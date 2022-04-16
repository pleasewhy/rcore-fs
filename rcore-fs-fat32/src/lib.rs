#[allow(dead_code)]
extern crate alloc;
extern crate log;

use alloc::{
    collections::BTreeMap,
    // boxed::Box,
    sync::{Arc, Weak},
};
use fat_struct::*;
use utils::DiskInodeIter;

use core::mem::MaybeUninit;
use core::slice;

use core::any::Any;
use core::cell::RefCell;
use core::fmt::{Debug, Error, Formatter};
use core::future::Future;
use core::mem::{size_of, size_of_val};
use core::pin::Pin;
use core::sync::atomic::{self, AtomicUsize};
use rcore_fs::dirty::Dirty;
use rcore_fs::util::*;
use rcore_fs::vfs::{self, FileSystem, FsError, FsInfo, INode, MMapArea, Metadata, Result};
use rcore_fs::{dev::Device, vfs::PollStatus};
use spin::RwLock;
use std::{cmp::Ordering, thread::current};

#[macro_use]
pub mod fat_struct;
pub mod utils;

/// Convert structs to [u8] slice
pub(crate) trait AsBuf {
    fn as_buf(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self as *const _ as *const u8, size_of_val(self)) }
    }
    fn as_buf_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self as *mut _ as *mut u8, size_of_val(self)) }
    }
}

trait DeviceExt: Device {
    /// read sector content to buf by given sector id.
    fn read_sector(&self, id: SectorId, buf: &mut [u8]) -> vfs::Result<()> {
        debug_assert!(buf.len() == SECTOR_SIZE);
        match self.read_at(id * SECTOR_SIZE, buf) {
            Ok(len) if len == buf.len() => Ok(()),
            _ => panic!("cannot read sector {} from device", id),
        }
    }

    fn write_sector(&self, id: SectorId, buf: &[u8]) -> vfs::Result<()> {
        debug_assert!(buf.len() == SECTOR_SIZE);
        match self.write_at(id * SECTOR_SIZE, buf) {
            Ok(len) if len == buf.len() => Ok(()),
            _ => panic!("cannot write sector {} to device", id),
        }
    }

    fn read_n_sector(&self, id: SectorId, buf: &mut [u8], n: usize) -> vfs::Result<()> {
        debug_assert!(buf.len() == SECTOR_SIZE * n);
        match self.read_at(id * SECTOR_SIZE, buf) {
            Ok(len) if len == buf.len() => Ok(()),
            _ => panic!("cannot read sector {} from device", id),
        }
    }

    fn write_n_sector(&self, id: SectorId, buf: &[u8], n: usize) -> vfs::Result<()> {
        debug_assert!(buf.len() == SECTOR_SIZE * 8);
        match self.write_at(id * SECTOR_SIZE, buf) {
            Ok(len) if len == buf.len() => Ok(()),
            _ => panic!("cannot write sector {} to device", id),
        }
    }

    /// Load struct `T` from given block in device
    fn load_struct<T: AsBuf>(&self, id: SectorId) -> vfs::Result<T> {
        let mut s: T = unsafe { MaybeUninit::uninit().assume_init() };
        self.read_sector(id, s.as_buf_mut())?;
        Ok(s)
    }
}

impl DeviceExt for dyn Device {}

pub struct Fat32FileSystem {
    /// on-disk Bios Parameter Block
    pub(crate) fat_bpb: Arc<FatBpb>,
    /// on-disk filesystem info
    pub(crate) fat_fs_info: Arc<FatFsInfo>,
    /// fat32 useful info.
    fat32_info: Fat32Info,
    /// inode list
    inodes: RwLock<BTreeMap<INodeId, Weak<Fat32INode>>>,
    /// device
    device: Arc<dyn Device>,
    /// Pointer to self, used by INodes
    self_ptr: Weak<Fat32FileSystem>,
    /// fat table
    fat_table: RwLock<Dirty<FatTable>>,
    /// inode num counter
    inode_num_counter: AtomicUsize,
}

impl Fat32FileSystem {
    /// Load Fat32FileSystem from device
    pub fn open(device: Arc<dyn Device>) -> vfs::Result<Arc<Self>> {
        let fat_bpb = Arc::new(device.load_struct::<FatBpb>(FAT_BPB_BLK_ID)?);
        let fs_info = Arc::new(device.load_struct::<FatFsInfo>(FAT_FS_INFO_BLK_ID)?);
        let fat32_info: Fat32Info = fat_bpb.clone().into();
        let mut fat_table = vec![0u8; fat32_info.total_fat_table_size];
        let readn = device.read_at(
            fat_bpb.reserved_sectors as usize * SECTOR_SIZE,
            fat_table.as_mut(),
        )?;
        let fs = Self {
            fat_bpb: fat_bpb,
            fat_fs_info: fs_info,
            inodes: RwLock::new(BTreeMap::new()),
            device: device,
            self_ptr: Weak::default(),
            fat_table: RwLock::new(Dirty::new(FatTable::new(fat_table))),
            fat32_info: fat32_info,
            inode_num_counter: AtomicUsize::new(2),
        };
        Ok(fs.wrap())
    }

    /// Wrap pure SimpleFileSystem with Arc
    /// Used in constructors
    fn wrap(self) -> Arc<Self> {
        // Create an Arc, make a Weak from it, then put it into the struct.
        // It's a little tricky.
        let fs = Arc::new(self);
        let weak = Arc::downgrade(&fs);
        let ptr = Arc::into_raw(fs) as *mut Self;
        unsafe {
            (*ptr).self_ptr = weak;
        }
        unsafe { Arc::from_raw(ptr) }
    }

    fn read_cluster(&self, id: ClusterId, offset: usize, buf: &mut [u8]) -> vfs::Result<()> {
        debug_assert!(offset + buf.len() <= self.fat32_info.cluster_size);
        match self
            .device
            .read_at(self.fat32_info.get_offset_of_cluster(id) + offset, buf)
        {
            Ok(len) if len == buf.len() => Ok(()),
            _ => panic!("cannot read cluster {} offset {} from device", id, offset),
        }
    }

    fn write_cluster(&self, id: ClusterId, offset: usize, buf: &[u8]) -> vfs::Result<()> {
        debug_assert!(offset + buf.len() <= self.fat32_info.cluster_size);
        match self
            .device
            .write_at(self.fat32_info.get_offset_of_cluster(id) + offset, buf)
        {
            Ok(len) if len == buf.len() => Ok(()),
            _ => panic!("cannot write cluster {} offset {} to device", id, offset),
        }
    }

    /// get next clusterid of given cluster_id in fat table.
    fn get_next_cluster_id(&self, cluster_id: ClusterId) -> vfs::Result<ClusterId> {
        let fat_table = self.fat_table.read();
        fat_table.get(cluster_id)
    }

    fn set_next_cluster_id(&self, cluster_id: ClusterId, value: ClusterId) -> vfs::Result<()> {
        let mut fat_table = self.fat_table.write();
        fat_table.set(cluster_id, value)
    }

    /// alloc disk cluster chain in fat table.
    fn alloc_disk_cluster_chain(&self, n: usize) -> vfs::Result<ClusterId> {
        let mut fat_table = self.fat_table.write();
        return fat_table.alloc_cluster_chain(n);
    }

    /// free cluster chain
    fn free_cluster_chain(&self, cluster_id: ClusterId) -> vfs::Result<()> {
        let mut fat_table = self.fat_table.write();
        let mut current_cluster_id = cluster_id;
        loop {
            let next_cluster_id = fat_table.get(current_cluster_id)?;
            if FREE_CLUSTER_MARK == next_cluster_id {
                return Err(FsError::WrongFs);
            }
            fat_table.set(current_cluster_id, FREE_CLUSTER_MARK)?;
            if END_OF_CLUSTER == next_cluster_id {
                return Ok(());
            }

            current_cluster_id = next_cluster_id;
        }
    }

    /// free file's data clusters
    fn free_disk_data_cluster(&self, disk_inode: &Fat32DiskINode) {
        let cluster_id = disk_inode.data_cluster_start;
        if cluster_id != 0 {
            self.free_cluster_chain(disk_inode.data_cluster_start);
        }
    }

    /// build fat32 inode by Fat32DiskINode.
    fn build_fat32_inode(
        &self,
        parent: Option<Arc<Fat32INode>>,
        disk_inode: Fat32DiskINode,
        inode_num: usize,
    ) -> Arc<Fat32INode> {
        let disk_entry_offset = disk_inode.disk_entry_offset as usize;
        let inode = Arc::new(Fat32INode {
            cluster_chain_context: RwLock::new(ClusterChainContext {
                current_file_cluster: 0,
                current_disk_cluster: disk_inode.data_cluster_start,
            }),
            fs: self.self_ptr.upgrade().unwrap(),
            disk_inode: RwLock::new(Dirty::new(disk_inode)),
            inode_num: inode_num,
            parent: parent,
        });
        self.inodes
            .write()
            .insert(disk_entry_offset, Arc::downgrade(&inode));
        inode.clone()
    }

    fn root_directory_size(&self) -> vfs::Result<u32> {
        let mut cluster_buf = vec![0u8; self.fat32_info.cluster_size];
        let mut size = 0u32;
        let mut cluster = self.fat_bpb.root_directory_cluster_start;
        loop {
            self.read_cluster(cluster, 0, &mut cluster_buf)?;
            for i in 0..cluster_buf.len() / size_of::<ShortFileEntry>() {
                let mark = cluster_buf[i * size_of::<ShortFileEntry>()];
                if mark == FREE_MARK {
                    return Ok(size);
                }
                size += size_of::<ShortFileEntry>() as u32;
            }
            cluster = self.get_next_cluster_id(cluster)?;
        }
    }

    /// sync fat table.
    fn sync_fat_table(&self) -> Result<()> {
        let mut fat_table = self.fat_table.write();
        let writen = self.device.write_at(
            self.fat_bpb.reserved_sectors as usize * SECTOR_SIZE,
            fat_table.as_ref(),
        )?;
        if writen != fat_table.as_ref().len() {
            return Err(FsError::DeviceError);
        }
        fat_table.sync();
        Ok(())
    }

    fn flush_weak_inodes(&self) {
        let mut inodes = self.inodes.write();
        let remove_ids: Vec<_> = inodes
            .iter()
            .filter(|(_, inode)| inode.upgrade().is_none())
            .map(|(&id, _)| id)
            .collect();
        for id in remove_ids.iter() {
            inodes.remove(id);
        }
    }

    fn write_disk_inode(&self, disk_inode: &Fat32DiskINode) -> vfs::Result<()> {
        let mut entry_offset = disk_inode.disk_entry_offset;
        println!(
            "write disk inode: name = {}",
            disk_inode.get_long_filename().as_ref()
        );
        for long_entry in &disk_inode.long_entries {
            self.device
                .write_at(entry_offset as usize, long_entry.as_buf())?;
            entry_offset += size_of::<LongFileEntry>() as u64;
        }
        self.device
            .write_at(entry_offset as usize, disk_inode.short_entry.as_buf())?;
        Ok(())
    }

    /// alloc a inode number
    fn alloc_inode_num(&self) -> usize {
        let ino = self
            .inode_num_counter
            .fetch_add(1, atomic::Ordering::Acquire);
        ino
    }

    /// sync all valid inode to disk.
    fn sync_inodes(&self) {
        let inodes = self.inodes.write();
        inodes.iter().for_each(|(_, inode)| {
            if let Some(inode) = inode.upgrade() {
                if let Err(err) = inode.sync_all() {
                    log::warn!("sync fat32inode {:?} failed. Err={:?}", inode, err);
                }
            }
        });
    }

    /// get inode by disk entry offset.
    fn get_fat32_inode(&self, disk_entry_offset: usize) -> Option<Arc<Fat32INode>> {
        if let Some(inode) = self.inodes.read().get(&disk_entry_offset) {
            return inode.upgrade();
        }
        return None;
    }
}

impl Drop for Fat32FileSystem {
    fn drop(&mut self) {
        if let Err(err) = self.sync() {
            log::warn!("Fat32FileSystem.sync failed. Err={:?}", err);
        }
    }
}

impl vfs::FileSystem for Fat32FileSystem {
    /// Sync all data to the storage
    fn sync(&self) -> Result<()> {
        self.flush_weak_inodes();
        self.sync_inodes();
        self.sync_fat_table()?;
        Ok(())
    }

    /// Get the root INode of the file system
    fn root_inode(&self) -> Arc<dyn INode> {
        // In the BTreeSet and not weak.
        if let Some(inode) = self.inodes.read().get(&FAT32_ROOT_DIR_INUM) {
            if let Some(inode) = inode.upgrade() {
                return inode;
            }
        }

        let mut root_short_entry = ShortFileEntry::default();
        root_short_entry.file_size = self.root_directory_size().unwrap();
        root_short_entry.attrs = Fat32FileAttr::DIRECTORY;
        let mut root_disk_inode = Fat32DiskINode {
            data_cluster_start: 0,
            disk_entry_offset: 0,
            short_entry: root_short_entry,
            long_entries: vec![],
        };
        root_disk_inode.set_data_cluster_start(self.fat_bpb.root_directory_cluster_start);

        return self.build_fat32_inode(None, root_disk_inode, FAT32_ROOT_DIR_INUM);
    }

    /// Get the file system information
    fn info(&self) -> FsInfo {
        vfs::FsInfo {
            bsize: self.fat32_info.cluster_size,
            frsize: self.fat32_info.cluster_size,
            blocks: self.fat_fs_info.free_clusters as usize,
            bfree: self.fat_fs_info.free_clusters as usize,
            bavail: self.fat_fs_info.allocated_clusters as usize,
            files: 100000, // inaccurate
            ffree: 100000, // inaccurate
            namemax: 256,
        }
    }
}

struct ClusterChainContext {
    /// 当前逻辑簇
    current_file_cluster: u32,
    /// 当前读取的物理簇
    current_disk_cluster: u32,
}
pub struct Fat32INode {
    cluster_chain_context: RwLock<ClusterChainContext>,
    fs: Arc<Fat32FileSystem>,
    disk_inode: RwLock<Dirty<Fat32DiskINode>>,
    inode_num: usize,
    parent: Option<Arc<Fat32INode>>,
}

impl Fat32INode {
    /// Map file cluster id to disk cluster id.
    fn get_disk_cluster_id(&self, file_cluster_id: ClusterId) -> vfs::Result<ClusterId> {
        let fat32_disk_inode = self.disk_inode.read();
        let mut cluster_chain_context = self.cluster_chain_context.write();

        let mut disk_cluster_id = fat32_disk_inode.data_cluster_start;
        if 0 == disk_cluster_id {
            return Err(FsError::InvalidParam);
        }

        let mut file_cluster_id_start = 0;
        if file_cluster_id >= cluster_chain_context.current_file_cluster {
            if cluster_chain_context.current_disk_cluster != 0 {
                disk_cluster_id = cluster_chain_context.current_disk_cluster;
            }
            file_cluster_id_start = cluster_chain_context.current_file_cluster;
        }

        for _ in file_cluster_id_start..file_cluster_id {
            let next_cluster_id = self.fs.get_next_cluster_id(disk_cluster_id)?;
            if (disk_cluster_id == 2 && (next_cluster_id & END_OF_CLUSTER2_MASK == END_OF_CLUSTER2))
                || next_cluster_id == END_OF_CLUSTER
            {
                return Err(FsError::InvalidParam);
            }
            disk_cluster_id = next_cluster_id;
        }

        cluster_chain_context.current_disk_cluster = disk_cluster_id;
        cluster_chain_context.current_file_cluster = file_cluster_id;
        Ok(disk_cluster_id)
    }

    /// Map file offset to disk offset.
    fn get_disk_offset(&self, file_offset: usize) -> vfs::Result<usize> {
        let file_cluster_id = file_offset / self.fs.fat32_info.cluster_size;
        let disk_cluster_id = self.get_disk_cluster_id(file_cluster_id as ClusterId)?;
        let disk_offset = self.fs.fat32_info.get_offset_of_cluster(disk_cluster_id);
        Ok(disk_offset + file_offset % self.fs.fat32_info.cluster_size)
    }

    // Note: the _\w*_at method always return begin>size?0:begin<end?0:(min(size,end)-begin) when success
    /// Read/Write content, no matter what type it is
    fn _io_at<F>(&self, begin: usize, end: usize, mut f: F) -> vfs::Result<usize>
    where
        F: FnMut(&Arc<Fat32FileSystem>, &BlockRange, usize) -> vfs::Result<()>,
    {
        let size = self.disk_inode.read().short_entry.file_size as usize;
        let iter = BlockIter {
            begin: size.min(begin),
            end: size.min(end),
            block_size_log2: self.fs.fat32_info.cluster_size_log2 as u8,
        };

        // For each block
        let mut buf_offset = 0usize;
        for mut range in iter {
            range.block = self.get_disk_cluster_id(range.block as u32)? as usize;
            f(&self.fs, &range, buf_offset)?;
            buf_offset += range.len();
        }
        Ok(buf_offset)
    }

    /// Read content, no matter what type it is
    fn _read_at(&self, offset: usize, buf: &mut [u8]) -> vfs::Result<usize> {
        self._io_at(offset, offset + buf.len(), |fs, range, offset| {
            fs.read_cluster(
                range.block as u32,
                range.begin,
                &mut buf[offset..offset + range.len()],
            )
        })
    }
    /// Write content, no matter what type it is
    fn _write_at(&self, offset: usize, buf: &[u8]) -> vfs::Result<usize> {
        self._io_at(offset, offset + buf.len(), |fs, range, offset| {
            fs.write_cluster(
                range.block as u32,
                range.begin,
                &buf[offset..offset + range.len()],
            )
        })
    }

    /// Clean content, no matter what type it is
    fn _clean_at(&self, begin: usize, end: usize) -> vfs::Result<usize> {
        static ZEROS: [u8; 4096] = [0; 4096];
        self._io_at(begin, end, |fs, range, _| {
            if range.len() <= ZEROS.len() {
                fs.write_cluster(range.block as u32, range.begin, &ZEROS[..range.len()])
            } else {
                let offset_iter = (range.begin..range.begin + range.len()).step_by(ZEROS.len());
                for offset in offset_iter {
                    let mut len = ZEROS.len();
                    if range.begin + range.len() - offset < len {
                        len = range.begin + range.len() - offset;
                    }
                    fs.write_cluster(range.block as u32, offset, &ZEROS[..len])?;
                }
                Ok(())
            }
        })
    }

    /// Load struct `T` from given file offset.
    fn load_struct_by_offset<T: AsBuf>(&self, file_offset: u64) -> vfs::Result<T> {
        let mut s: T = unsafe { MaybeUninit::uninit().assume_init() };
        let readn = self._read_at(file_offset as usize, s.as_buf_mut())?;
        if readn < size_of::<T>() {
            return Err(FsError::InvalidParam);
        }
        Ok(s)
    }

    /// Load Fat32DiskInode from given file offset.
    /// return this Fat32DiskInode  and its disk size.
    /// disk layout: [long_entry_2|long_entry_1|short_entry]
    fn load_fat32_disk_inode(&self, file_entry_offset: u64) -> vfs::Result<Fat32DiskINode> {
        let mut current_offset = file_entry_offset;
        let long_entry = self.load_struct_by_offset::<LongFileEntry>(current_offset)?;

        if long_entry.is_deleted() || long_entry.is_free() {
            return Err(FsError::EntryNotFound);
        }
        current_offset += FAT32_DIRECTORY_ENTRY_SIZE;
        let long_entry_num = (long_entry.sequence_number & LONG_ENTRY_SEQ_NUMBER_MASK) as u64;

        if long_entry_num == 0 {
            return Err(FsError::EntryNotFound);
        }

        let mut long_entry_vec = vec![long_entry];
        long_entry_vec.reserve((long_entry_num - 1) as usize);
        for _ in 1..long_entry_num {
            long_entry_vec.push(self.load_struct_by_offset::<LongFileEntry>(current_offset)?);
            current_offset += FAT32_DIRECTORY_ENTRY_SIZE;
        }
        let short_entry = self.load_struct_by_offset::<ShortFileEntry>(current_offset)?;

        let data_cluster_start =
            ((short_entry.cluster_high as u32) << 16) as u32 + short_entry.cluster_low as u32;
        let inode = Fat32DiskINode {
            data_cluster_start: data_cluster_start,
            disk_entry_offset: self.get_disk_offset(file_entry_offset as usize)? as u64,
            short_entry: short_entry,
            long_entries: long_entry_vec,
        };
        Ok(inode)
    }

    /// root dir need fake . and ... entry
    fn _root_dir_get_entry(&self, offset: usize) -> Result<(usize, String)> {
        match offset {
            0 => Ok((1, String::from("."))),
            1 => Ok((2, String::from(".."))),
            _ => {
                let disk_inode = self.load_fat32_disk_inode(offset as u64 - 2)?;
                Ok((
                    offset + disk_inode.get_indisk_size(),
                    String::from(disk_inode.get_long_filename().as_ref()),
                ))
            }
        }
    }

    /// Move the entries slot after offset to the left by `n` slots.
    fn _left_shift_entries(&self, shift_count: usize, offset: usize) -> vfs::Result<()> {
        let mut current_offset = offset;
        let mut buf: [u8; SECTOR_SIZE] = [0u8; SECTOR_SIZE];
        // move mutiple sectors at one time.
        loop {
            let readn_opt = self._read_at(current_offset, &mut buf);
            match readn_opt {
                Ok(readn) => {
                    if readn != buf.len() {
                        break;
                    }
                }
                Err(FsError::InvalidParam) => {
                    break;
                }
                Err(err) => {
                    return Err(err);
                }
            }

            self._write_at(current_offset - shift_count, &buf)?;
            current_offset += SECTOR_SIZE;
        }
        let new_len = self.disk_inode.read().short_entry.file_size as usize - shift_count;
        self._resize(new_len)?;
        Ok(())
    }

    fn _resize(&self, len: usize) -> Result<()> {
        let new_clusters =
            (len + self.fs.fat32_info.cluster_size - 1) / self.fs.fat32_info.cluster_size;
        let old_clusters = (self.disk_inode.read().short_entry.file_size as usize
            + self.fs.fat32_info.cluster_size
            - 1)
            / self.fs.fat32_info.cluster_size;
        if new_clusters > MAX_FILE_CLUSTER_NUM || old_clusters > MAX_FILE_CLUSTER_NUM {
            return Err(FsError::InvalidParam);
        }
        match new_clusters.cmp(&old_clusters) {
            Ordering::Equal => {
                self.disk_inode.write().short_entry.file_size = len as u32;
            }
            Ordering::Greater => {
                println!("expand");
                let mut current_cluster = self.disk_inode.read().data_cluster_start;
                if current_cluster == 0 && old_clusters != 0 {
                    return Err(FsError::WrongFs);
                }
                println!("expand1");
                for _ in 1..old_clusters {
                    current_cluster = self.fs.get_next_cluster_id(current_cluster)?;
                }
                println!("expand2");
                let cluster_chain = self
                    .fs
                    .alloc_disk_cluster_chain(new_clusters - old_clusters)?;
                println!("expand3");

                if current_cluster == 0 {
                    println!("expand4");
                    self.disk_inode
                        .write()
                        .set_data_cluster_start(cluster_chain);
                } else {
                    println!("expand5");
                    self.fs
                        .set_next_cluster_id(current_cluster, cluster_chain)?;
                }
            }
            Ordering::Less => {
                if new_clusters == 0 {
                    self.fs
                        .free_cluster_chain(self.disk_inode.read().data_cluster_start)?;
                    self.disk_inode.write().set_data_cluster_start(0);
                } else {
                    let mut current_cluster = self.disk_inode.read().data_cluster_start;
                    for _ in 1..new_clusters {
                        current_cluster = self.fs.get_next_cluster_id(current_cluster)?;
                    }
                    let next_cluster_id = self.fs.get_next_cluster_id(current_cluster)?;
                    self.fs
                        .set_next_cluster_id(current_cluster, END_OF_CLUSTER)?;
                    self.fs.free_cluster_chain(next_cluster_id)?;
                }
            }
        }
        self.disk_inode.write().short_entry.file_size = len as u32;
        Ok(())
    }

    /// There is no need to consider the repetition of short filenames.
    /// Fat32 implementation generates both long and short filenames for
    /// each file. With long filenames, short filenames are useless.
    fn get_short_filename(&self, long_filename: &str) -> [u8; 11] {
        let mut short_name: [u8; 11] = [0x20u8; 11];
        let dot_idx = long_filename.find('.');
        if let Some(idx) = dot_idx {
            let splited_filename = long_filename.split_at(idx);
            let name = splited_filename.0.as_bytes();
            let ext = &splited_filename.1.as_bytes();
            let base_len = if name.len() > 8 { 8 } else { name.len() };
            let ext_len = if ext.len() > 3 { 3 } else { ext.len() };
            short_name[0..base_len].copy_from_slice(&splited_filename.0.as_bytes()[0..base_len]);
            short_name[8..8 + ext_len].copy_from_slice(&splited_filename.1.as_bytes()[0..ext_len]);
        } else {
            let base_len = if long_filename.as_bytes().len() > 8 {
                8
            } else {
                long_filename.as_bytes().len()
            };
            short_name[0..base_len].copy_from_slice(&long_filename.as_bytes()[0..base_len]);
        }
        short_name
            .iter_mut()
            .for_each(|b| *b = (*b as char).to_ascii_uppercase() as u8);
        short_name
    }

    fn is_root_inode(&self) -> bool {
        self.inode_num == FAT32_ROOT_DIR_INUM
    }

    fn get_self_arc(&self) -> Arc<Fat32INode> {
        return self
            .fs
            .get_fat32_inode(self.disk_inode.read().disk_entry_offset as usize)
            .expect("Get Self Arc Failed.");
    }

    fn get_parent_inode(&self) -> Arc<Fat32INode> {
        if self.is_root_inode() {
            return self.get_self_arc();
        }
        return self.parent.as_ref().unwrap().clone();
    }
}

impl INode for Fat32INode {
    /// Read bytes at `offset` into `buf`, return the number of bytes read.
    fn read_at(&self, offset: usize, buf: &mut [u8]) -> vfs::Result<usize> {
        match self.metadata()?.type_ {
            vfs::FileType::File | vfs::FileType::SymLink => self._read_at(offset, buf),
            _ => Err(FsError::NotFile),
        }
    }

    /// Write bytes at `offset` from `buf`, return the number of bytes written.
    fn write_at(&self, offset: usize, buf: &[u8]) -> vfs::Result<usize> {
        let metadata = self.metadata()?;
        match metadata.type_ {
            vfs::FileType::File | vfs::FileType::SymLink => {
                let end_offset = offset + buf.len();
                if (metadata.size as usize) < end_offset {
                    self._resize(end_offset)?;
                }
                self._write_at(offset, buf)
            }
            _ => Err(FsError::NotFile),
        }
    }

    /// Poll the events, return a bitmap of events.
    fn poll(&self) -> vfs::Result<PollStatus> {
        vfs::Result::Err(FsError::DeviceError)
    }

    /// Poll the events, return a bitmap of events, async version.
    fn async_poll<'a>(
        &'a self,
    ) -> Pin<Box<dyn Future<Output = Result<PollStatus>> + Send + Sync + 'a>> {
        Box::pin(async move { self.poll() })
    }

    /// Get metadata of the INode
    fn metadata(&self) -> Result<Metadata> {
        let disk_inode = self.disk_inode.read();
        let mut clusters =
            disk_inode.short_entry.file_size as usize / self.fs.fat32_info.cluster_size;
        clusters +=
            if disk_inode.short_entry.file_size as usize % self.fs.fat32_info.cluster_size == 0 {
                0
            } else {
                1
            };
        let meta = Metadata {
            dev: 0,
            inode: self.inode_num,
            size: disk_inode.short_entry.file_size as usize,
            blk_size: self.fs.fat32_info.cluster_size,
            blocks: clusters,
            atime: disk_inode.get_access_timesepc(),
            mtime: disk_inode.get_modification_timesepc(),
            ctime: disk_inode.get_create_timesepc(),
            type_: vfs::FileType::from(disk_inode.short_entry.attrs),
            mode: 0o777,
            nlinks: 1,
            uid: 0,
            gid: 0,
            rdev: 0,
        };
        Ok(meta)
    }

    /// Set metadata of the INode
    fn set_metadata(&self, _metadata: &Metadata) -> Result<()> {
        Err(FsError::NotSupported)
    }

    /// Sync all data and metadata
    fn sync_all(&self) -> Result<()> {
        let mut disk_inode = self.disk_inode.write();

        if disk_inode.dirty() {
            if !self.is_root_inode() {
                let mut entry_offset = disk_inode.disk_entry_offset;
                for long_entry in &disk_inode.long_entries {
                    self.fs
                        .device
                        .write_at(entry_offset as usize, long_entry.as_buf())?;
                    entry_offset += size_of::<LongFileEntry>() as u64;
                }
                self.fs
                    .device
                    .write_at(entry_offset as usize, disk_inode.short_entry.as_buf())?;
            }
            disk_inode.sync();
        }
        Ok(())
    }

    /// Sync data (not include metadata)
    fn sync_data(&self) -> Result<()> {
        self.sync_all()
    }

    /// Resize the file
    fn resize(&self, len: usize) -> Result<()> {
        if self.metadata()?.type_ != vfs::FileType::File {
            return Err(FsError::NotFile);
        }
        self._resize(len)
    }

    /// Create a new INode in the directory
    fn create(&self, name: &str, type_: vfs::FileType, mode: u32) -> Result<Arc<dyn INode>> {
        println!(
            "file sz={}",
            self.disk_inode.read().short_entry.file_size as u64
        );
        if name.as_bytes().len() > MAX_FILEN_NAME_LEGTH {
            return Err(FsError::InvalidParam);
        }
        let mut iter = DiskInodeIter::new(&self);
        let name_existed = iter.find(|(_, disk_inode)| {
            disk_inode.get_long_filename().as_ref().cmp(name) == Ordering::Equal
        });
        if name_existed.is_some() {
            return Err(FsError::EntryExist);
        }
        let attr = Fat32FileAttr::from(type_);
        let short_name: [u8; 11] = self.get_short_filename(name);
        let mut create_disk_inode = Fat32DiskINode::create(short_name, name, attr, 0)?;

        let disk_inode = self.disk_inode.read();
        let file_offset = disk_inode.short_entry.file_size;
        let newsz = disk_inode.short_entry.file_size as usize + create_disk_inode.get_indisk_size();
        println!(
            "create_disk_inode.get_indisk_size()={}",
            create_disk_inode.get_indisk_size()
        );
        drop(disk_inode);
        self._resize(newsz)?;
        create_disk_inode.disk_entry_offset = self.get_disk_offset(file_offset as usize)? as u64;
        self.fs.write_disk_inode(&create_disk_inode)?;

        let created_inode = self.load_fat32_disk_inode(file_offset as u64).unwrap();
        println!(
            "offset={} name={}",
            file_offset,
            created_inode.get_long_filename().as_ref()
        );
        println!("create: find");
        self.find(name).unwrap();

        Ok(self.fs.build_fat32_inode(
            Some(self.get_self_arc()),
            create_disk_inode,
            self.fs.alloc_inode_num(),
        ))
    }

    /// Create a new INode in the directory, with a data field for usages like device file.
    fn create2(
        &self,
        name: &str,
        type_: vfs::FileType,
        mode: u32,
        _data: usize,
    ) -> Result<Arc<dyn INode>> {
        self.create(name, type_, mode)
    }

    /// Create a hard link `name` to `other`
    fn link(&self, _name: &str, _other: &Arc<dyn INode>) -> Result<()> {
        Err(FsError::NotSupported)
    }

    /// Delete entries and data corresponding to name.
    /// note: This function does not delete directory entries
    /// using `DELETED_MARK`, but overwrites them, because `get_entry`
    /// requires that directory entries be contigual.
    fn unlink(&self, name: &str) -> Result<()> {
        let info = self.metadata()?;
        if info.type_ != vfs::FileType::Dir {
            return Err(FsError::NotDir);
        }
        if name == "." {
            return Err(FsError::IsDir);
        }
        if name == ".." {
            return Err(FsError::IsDir);
        }

        let mut current_offset = 0u64;
        loop {
            let disk_inode = self.load_fat32_disk_inode(current_offset)?;
            if name.eq(disk_inode.get_long_filename().as_ref()) {
                self.fs.free_disk_data_cluster(&disk_inode);
                self._left_shift_entries(
                    disk_inode.get_indisk_size(),
                    current_offset as usize + disk_inode.get_indisk_size(),
                )?;
                break;
            }
            current_offset += disk_inode.get_indisk_size() as u64;
        }
        Ok(())
    }

    /// Move INode `self/old_name` to `target/new_name`.
    /// If `target` equals `self`, do rename.
    fn move_(&self, old_name: &str, target: &Arc<dyn INode>, new_name: &str) -> Result<()> {
        let info = self.metadata()?;
        if info.type_ != vfs::FileType::Dir {
            return Err(FsError::NotDir);
        }
        if info.nlinks == 0 {
            return Err(FsError::DirRemoved);
        }
        if old_name == "." {
            return Err(FsError::IsDir);
        }
        if old_name == ".." {
            return Err(FsError::IsDir);
        }

        let dest = target
            .downcast_ref::<Fat32INode>()
            .ok_or(FsError::NotSameFs)?;
        let dest_info = dest.metadata()?;
        if !Arc::ptr_eq(&self.fs, &dest.fs) {
            return Err(FsError::NotSameFs);
        }

        if dest_info.type_ != vfs::FileType::Dir {
            return Err(FsError::NotDir);
        }
        if dest_info.nlinks == 0 {
            return Err(FsError::DirRemoved);
        }

        let mut iter = DiskInodeIter::new(&self);
        let (removed_offset, mut removed_disk_inode) = iter
            .find(|(_, disk_inode)| disk_inode.get_long_filename().as_ref().eq(old_name))
            .ok_or(FsError::EntryNotFound)?;

        // Remove all entries corresponding to old files.
        self._left_shift_entries(
            removed_disk_inode.get_indisk_size(),
            removed_offset + removed_disk_inode.get_indisk_size(),
        )?;

        let short_name = self.get_short_filename(new_name);
        removed_disk_inode.rename(short_name, new_name);
        if info.inode == dest_info.inode {
            // rename
            let file_entry_offset = self.disk_inode.read().short_entry.file_size as usize;
            removed_disk_inode.disk_entry_offset = self.get_disk_offset(file_entry_offset)? as u64;
            self.fs.write_disk_inode(&removed_disk_inode)?;
        } else {
            // move
            let file_entry_offset = dest.disk_inode.read().short_entry.file_size as usize;
            removed_disk_inode.disk_entry_offset = dest.get_disk_offset(file_entry_offset)? as u64;
            dest.fs.write_disk_inode(&removed_disk_inode)?;
        }
        Ok(())
    }

    /// Find the INode `name` in the directory
    fn find(&self, name: &str) -> Result<Arc<dyn INode>> {
        if self.metadata()?.type_ != vfs::FileType::Dir {
            return Err(FsError::NotDir);
        }
        if ".".eq(name) {
            return Ok(self.get_self_arc());
        }
        if "..".eq(name) {
            return Ok(self.get_parent_inode());
        }
        let mut iter = DiskInodeIter::new(&self);
        let (_, disk_inode) = iter
            .find(|(_, disk_inode)| {
                let long_name = disk_inode.get_long_filename();
                println!("find name = {}", long_name.as_ref());
                return long_name.as_ref().eq(name);
            })
            .ok_or(FsError::EntryNotFound)?;

        let inode = self
            .fs
            .get_fat32_inode(disk_inode.disk_entry_offset as usize);
        if inode.is_some() {
            return Ok(inode.unwrap());
        }
        return Ok(self.fs.build_fat32_inode(
            Some(self.get_self_arc()),
            disk_inode,
            self.fs.alloc_inode_num(),
        ));
    }

    fn get_entry(&self, offset: usize) -> Result<(usize, String)> {
        if self.is_root_inode() {
            return self._root_dir_get_entry(offset);
        }
        let disk_inode = self.load_fat32_disk_inode(offset as u64)?;
        Ok((
            offset + disk_inode.get_indisk_size(),
            String::from(disk_inode.get_long_filename().as_ref()),
        ))
    }

    /// Get the name of directory entry with metadata
    /// return next entry offset, metadata and name.
    fn get_entry_with_metadata(&self, offset: usize) -> Result<(usize, Metadata, String)> {
        // a default and slow implementation
        let (next_offset, name) = self.get_entry(offset)?;
        let entry = self.find(&name)?;
        Ok((next_offset, entry.metadata()?, name))
    }

    /// Control device
    fn io_control(&self, _cmd: u32, _data: usize) -> Result<usize> {
        Err(FsError::NotSupported)
    }

    /// Map files or devices into memory
    fn mmap(&self, _area: MMapArea) -> Result<()> {
        Err(FsError::NotSupported)
    }

    /// Get the file system of the INode
    fn fs(&self) -> Arc<dyn FileSystem> {
        self.fs.clone()
    }

    fn as_any_ref(&self) -> &dyn Any {
        self
    }
}

impl Debug for Fat32INode {
    fn fmt(&self, f: &mut Formatter) -> core::result::Result<(), Error> {
        write!(f, "inode num={}", self.inode_num)?;
        Ok(())
    }
}

impl Drop for Fat32INode {
    fn drop(&mut self) {
        if let Err(err) = self.sync_all() {
            log::warn!("Fat32INode.sync_all failed. Err={:?}", err);
        }
    }
}

impl From<Fat32FileAttr> for vfs::FileType {
    fn from(t: Fat32FileAttr) -> Self {
        match t {
            Fat32FileAttr::DIRECTORY => vfs::FileType::Dir,
            _ => vfs::FileType::File,
        }
    }
}

impl From<vfs::FileType> for Fat32FileAttr {
    fn from(t: vfs::FileType) -> Self {
        match t {
            vfs::FileType::Dir => Fat32FileAttr::DIRECTORY,
            vfs::FileType::File => Fat32FileAttr::ARCHIVE,
            _ => Fat32FileAttr::empty(),
        }
    }
}
