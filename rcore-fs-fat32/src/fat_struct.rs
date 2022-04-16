extern crate alloc;

use super::utils::*;
use alloc::str;
use alloc::sync::Arc;
use core::fmt::{Debug, Error, Formatter};
use core::mem::size_of;
use core::option::Option;
use rcore_fs::vfs::{self, FileType, FsError};
use rcore_fs::vfs::{Metadata, Timespec};
use static_assertions::const_assert;

use crate::AsBuf;

pub type BlockId = usize;
pub type ClusterId = u32;
pub type SectorId = usize;
pub type INodeId = BlockId;

pub const FAT_BPB_BLK_ID: BlockId = 0;
pub const FAT_FS_INFO_BLK_ID: BlockId = 1;

/// sector size
pub const SECTOR_SIZE: usize = 512usize;

pub const SINGLE_SHIFT_ENTRIES_NUM: usize = (SECTOR_SIZE / 32) * 10;

// 短文件目录项属性
pub const FAT_ATTR_READ_ONLY: u8 = 0x01;
pub const FAT_ATTR_HIDDEN: u8 = 0x02;
pub const FAT_ATTR_SYSTEM: u8 = 0x04;
pub const FAT_ATTR_VOLUME_LABEL: u8 = 0x08;
pub const FAT_ATTR_DIRENTORY: u8 = 0x10;
pub const FAT_ATTR_ARCHIVE: u8 = 0x20;
pub const FAT_ATTR_DEVICE: u8 = 0x40;
pub const FAT_ATTR_UNUSED: u8 = 0x80;
pub const FAT_ATTR_LONG_ENTRY: u8 = 0xF; // 为此值时表示该目录项为长文件名目录项

pub const BAD_CLUSTER32: u32 = 0x0ffffff7;
pub const END_OF_CLUSTER: u32 = 0x0FFFFFFF; // 文件结束标志
pub const END_OF_CLUSTER2: u32 = 0x0FFFFF00; // 第二个簇的文件结束标志
pub const END_OF_CLUSTER2_MASK: u32 = 0xFFFFFF00; // 第二个簇的文件结束标志

pub const FREE_CLUSTER_MARK: u32 = 0;
pub const FAT_ENTRY_BYTES: u8 = 4; // fat表项为4个字节

pub const LONG_NAME_LENGTH: u8 = 13;
pub const SHORT_NAME_LENGH: u8 = 12; // 包括dot

pub const LONG_ENTRY_NAME_0_5_OFFSET: usize = 1;
pub const LONG_ENTRY_NAME_5_11_OFFSET: usize = 14;
pub const LONG_ENTRY_NAME_11_13_OFFSET: usize = 28;

pub const SHORT_NAME_FILL_STUFF: u8 = 0x20;
pub const MSDOS_ENTRY_SIZE: u8 = 32;
pub const DELETED_MARK: u8 = 0xe5;
pub const FREE_MARK: u8 = 0x0;
pub const LONG_ENTRY_SEQ_NUMBER_MASK: u8 = !0x40;

pub const FAT32_DIRECTORY_ENTRY_SIZE: u64 = 32;

pub const FAT32_ROOT_DIR_INUM: usize = 0;

pub const MAX_FILE_CLUSTER_NUM: usize = 0x0FFFFFF6;

pub const MAX_FILEN_NAME_LEGTH: usize = 256;

/// Bios Parameter Block
#[repr(C)]
#[repr(packed(1))]
#[derive(Debug, Copy, Clone)]
pub struct FatBpb {
    pub jump: [u8; 3],                     // 3
    pub oem_name: [u8; 8],                 // 11
    pub bytes_per_sector: u16,             // 扇区字节数;13
    pub sectors_per_cluster: u8,           // cluster 包含的扇区数;14
    pub reserved_sectors: u16,             // 保留的扇区数;16
    pub number_of_fat: u8,                 // fat表的数量;17
    pub root_directories_entries: u16,     // 根目录cluster;19
    pub total_sectors: u16,                // 总的扇区数(fat12/fat16);21
    pub media_descriptor: u8,              // 22
    pub sectors_per_fat: u16,              // fat包含扇区数(fat12/16);24
    pub sectors_per_track: u16,            // 磁道扇区数;26
    pub track_heads: u16,                  // 磁头数;28
    pub hidden_sectors: u32,               // 分区已使用扇区数;32
    pub total_sectors_long: u32,           // 文件系统总扇区数(fat32);36
    pub sectors_per_fat_v32: u32,          // fat表扇区数(fat32);40
    pub drive_description: u16,            // 介质描述符;42
    pub version: u16,                      // 版本;44
    pub root_directory_cluster_start: u32, // 根目录簇号(通常为2);48
    pub fs_information_sector: u16,        // 文件系统信息扇区;50
    pub boot_sectors_copy_sector: u16,     // 备份引导扇区;52
    pub filler: [u8; 12],                  // 未使用;64
    pub physical_drive_number: u8,         // 65
    pub reserved: u8,                      // 保留;66
    pub extended_boot_signature: u8,       // 扩展引导标志;67
    pub volume_id: u32,                    // 卷序列号,通常为随机值;71
    pub volume_label: [u8; 11],            // 卷标(ASCII码);82
    pub file_system_type: [u8; 8],         // 文件系统格式;90
    pub boot_code: [u8; 420],              // 未使用;510
    pub signature: u16,                    // 签名标志;512
}

impl FatBpb {
    // #[inline]
    // pub fn get_cluster_size(&self) -> usize {
    //     self.bytes_per_sector as usize * self.sectors_per_cluster as usize
    // }

    // #[inline]
    // pub fn get_total_fat_table_size(&self) -> usize {
    // self.number_of_fat as usize
    //     * self.sectors_per_fat_v32 as usize
    //     * self.bytes_per_sector as usize
    // }
}

/// Store frequently used data that needs to be computed via FatBpb
pub struct Fat32Info {
    pub cluster_size: usize,
    pub first_data_sector_offset: usize,
    pub cluster_size_log2: u8,
    pub total_fat_table_size: usize,
}

impl Fat32Info {
    #[inline]
    pub fn get_offset_of_cluster(&self, cluster_id: ClusterId) -> usize {
        assert!(cluster_id >= 2, "cluster id must be greater than 2");
        return self.first_data_sector_offset + (cluster_id - 2) as usize * self.cluster_size;
    }
}

impl From<Arc<FatBpb>> for Fat32Info {
    fn from(fat_bpb: Arc<FatBpb>) -> Self {
        let fisrt_data_sector_offset = (fat_bpb.reserved_sectors as usize
            + fat_bpb.number_of_fat as usize * fat_bpb.sectors_per_fat_v32 as usize)
            * fat_bpb.bytes_per_sector as usize;
        let total_fat_table_size = fat_bpb.number_of_fat as usize
            * fat_bpb.sectors_per_fat_v32 as usize
            * fat_bpb.bytes_per_sector as usize;

        let cluster_size = fat_bpb.bytes_per_sector as usize * fat_bpb.sectors_per_cluster as usize;
        let mut cluster_size_log2 = 0;
        let mut cluster_size_tmp = cluster_size >> 1;
        while cluster_size_tmp > 0 {
            cluster_size_tmp = cluster_size_tmp >> 1;
            cluster_size_log2 += 1;
        }
        Self {
            cluster_size: cluster_size,
            first_data_sector_offset: fisrt_data_sector_offset,
            cluster_size_log2: cluster_size_log2,
            total_fat_table_size: total_fat_table_size,
        }
    }
}

// FAT32 Information sector
#[repr(C)]
#[derive(Debug)]
pub struct FatFsInfo {
    pub signature_start: u32, // 签名
    pub reserved: [u8; 480],  // 保留
    pub signature_middle: u32,
    pub free_clusters: u32,      // 空闲簇数
    pub allocated_clusters: u32, // 已分配的簇数
    pub reserved_2: [u8; 12],    // 保留
    pub signature_end: u32,
}

// 短文件目录项
#[repr(C)]
#[repr(packed(1))]
#[derive(Debug, Copy, Clone, Default)]
pub struct ShortFileEntry {
    pub name: [u8; 11],
    pub attrs: Fat32FileAttr,
    pub reserved: u8,
    pub creation_time_seconds: u8,
    pub creation_time: u16,
    pub creation_date: u16,
    pub accessed_date: u16,
    pub cluster_high: u16,
    pub modification_time: u16,
    pub modification_date: u16,
    pub cluster_low: u16,
    pub file_size: u32,
}

impl ShortFileEntry {
    pub const fn const_default() -> Self {
        Self {
            name: [0; 11],
            attrs: Fat32FileAttr::empty(),
            reserved: 0,
            creation_time_seconds: 0,
            creation_time: 0,
            creation_date: 0,
            accessed_date: 0,
            cluster_high: 0,
            modification_time: 0,
            modification_date: 0,
            cluster_low: 0,
            file_size: 0,
        }
    }
}

// 长文件目录项
#[repr(C)]
#[repr(packed(1))]
#[derive(Debug, Copy, Clone, Default)]
pub struct LongFileEntry {
    pub sequence_number: u8,
    pub name0_5: [u16; 5],
    pub attrs: Fat32FileAttr,
    pub reserved0: u8,
    pub checksum: u8,
    pub name5_11: [u16; 6],
    pub reserved1: u16,
    pub name11_13: [u16; 2],
}

impl LongFileEntry {
    #[inline]
    pub fn is_deleted(&self) -> bool {
        self.sequence_number == DELETED_MARK
    }

    #[inline]
    pub fn is_free(&self) -> bool {
        self.sequence_number == FREE_MARK
    }
}

impl AsBuf for FatBpb {}
impl AsBuf for FatFsInfo {}
impl AsBuf for ShortFileEntry {}
impl AsBuf for LongFileEntry {}

#[repr(C)]
pub struct Str13(pub [u8; 13]);

#[repr(C)]
pub struct Str256(pub [u8; 256]);

impl AsRef<str> for Str256 {
    fn as_ref(&self) -> &str {
        let len = self.0.iter().enumerate().find(|(_, &b)| b == 0).unwrap().0;
        str::from_utf8(&self.0[0..len]).unwrap()
    }
}

impl AsRef<str> for Str13 {
    fn as_ref(&self) -> &str {
        let len = self.0.iter().enumerate().find(|(_, &b)| b == 0).unwrap().0;
        str::from_utf8(&self.0[0..len]).unwrap()
    }
}

impl Debug for Str256 {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{}", self.as_ref())
    }
}

impl Debug for Str13 {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{}", self.as_ref())
    }
}

impl<'a> From<&'a str> for Str256 {
    fn from(s: &'a str) -> Self {
        let mut ret = [0u8; 256];
        ret[0..s.len()].copy_from_slice(s.as_ref());
        Str256(ret)
    }
}

impl<'a> From<&'a str> for Str13 {
    fn from(s: &'a str) -> Self {
        let mut ret = [0u8; 13];
        ret[0..s.len()].copy_from_slice(s.as_ref());
        Str13(ret)
    }
}

pub struct Fat32DiskINode {
    /// 起始data cluster no
    pub data_cluster_start: u32,
    /// 起始目录项在磁盘上的位置
    pub disk_entry_offset: u64,
    /// short filename entry
    pub short_entry: ShortFileEntry,
    /// all long filename entry
    pub long_entries: Vec<LongFileEntry>,
}

impl Fat32DiskINode {
    pub fn create(
        short_name: [u8; 11],
        long_name: &str,
        attr: Fat32FileAttr,
        disk_entry_offset: u64,
    ) -> vfs::Result<Self> {
        if long_name.as_bytes().len() > MAX_FILEN_NAME_LEGTH {
            return Err(FsError::InvalidParam);
        }
        let short_entry = ShortFileEntry {
            name: short_name,
            attrs: attr,
            reserved: 0,
            creation_time_seconds: 0,
            creation_time: 0,
            creation_date: 0,
            accessed_date: 0,
            cluster_high: 0,
            modification_time: 0,
            modification_date: 0,
            cluster_low: 0,
            file_size: 0,
        };
        let long_entries =
            Fat32DiskINode::create_long_entries(long_name, fat32_check_sum(&short_name));
        Ok(Self {
            data_cluster_start: 0,
            disk_entry_offset: disk_entry_offset,
            short_entry,
            long_entries,
        })
    }

    fn create_long_entries(long_name: &str, checksum: u8) -> Vec<LongFileEntry> {
        let mut long_entries = vec![];

        let longname_len = long_name.as_bytes().len();
        let mut longname_bytes: [u8; MAX_FILEN_NAME_LEGTH + 2] = [0xffu8; MAX_FILEN_NAME_LEGTH + 2];
        longname_bytes[0..longname_len].copy_from_slice(&long_name.as_bytes()[..]);
        longname_bytes[longname_len] = 0;
        longname_bytes[longname_len + 1] = 0;
        for ino in 1..=((longname_len + 12) / 13) as u8 {
            let offset = (ino - 1) as usize * 13;
            let mut name0_5: [u8; 5] = [0u8; 5];
            let mut name5_11: [u8; 6] = [0u8; 6];
            let mut name11_13: [u8; 2] = [0u8; 2];
            name0_5.copy_from_slice(&longname_bytes[offset..offset + 5]);
            name5_11.copy_from_slice(&longname_bytes[offset + 5..offset + 11]);
            name11_13.copy_from_slice(&longname_bytes[offset + 11..offset + 13]);
            let long_entry = LongFileEntry {
                sequence_number: ino & LONG_ENTRY_SEQ_NUMBER_MASK,
                name0_5: name0_5.map(|ch| if ch == 0xff { 0xffu16 } else { ch as u16 }),
                attrs: Fat32FileAttr::LONG_FILE_ENTRY,
                reserved0: 0,
                checksum: checksum,
                name5_11: name5_11.map(|ch| if ch == 0xff { 0xffu16 } else { ch as u16 }),
                reserved1: 0,
                name11_13: name11_13.map(|ch| if ch == 0xff { 0xffu16 } else { ch as u16 }),
            };
            long_entries.push(long_entry);
        }
        long_entries.reverse();
        long_entries
    }

    /// get short filename
    /// note:   name = short_entry.name[0..8]
    ///         ext_name = short_entry.name[8..11]
    ///         short_name = name.ext_name
    pub fn get_short_filename(&self) -> Str13 {
        let short_entry = &self.short_entry;
        // 文件名长度
        let name_len = short_entry.name[0..8]
            .iter()
            .enumerate()
            .find(|(_, &b)| b == 0x20)
            .map_or(8, |(i, _)| i);
        // 扩展名长度
        let ext_name_len = short_entry.name[8..11]
            .iter()
            .enumerate()
            .find(|(_, &b)| b == 0x20)
            .map_or(3, |(i, _)| i - 8);

        let mut filename: [u8; 13] = [0; 13];
        filename[0..name_len].copy_from_slice(&short_entry.name[0..name_len]);
        filename[name_len] = '.' as u8;
        filename[name_len + 1..name_len + 1 + ext_name_len]
            .copy_from_slice(&short_entry.name[8..8 + ext_name_len]);
        Str13(filename)
    }

    /// get long filename
    /// note: 长文件名以两字节的0结束, 然后使用0xff填充
    pub fn get_long_filename(&self) -> Str256 {
        let long_entries = self.long_entries.clone();
        let mut filename: [u8; 256] = [0; 256];
        long_entries.iter().for_each(|long_entry| {
            let sno = long_entry.sequence_number & LONG_ENTRY_SEQ_NUMBER_MASK;
            let offset = (LONG_NAME_LENGTH * (sno - 1)) as usize;
            let name0_5 = long_entry.name0_5.map(|ch| ch.to_be_bytes()[1]);
            let name5_11 = long_entry.name5_11.map(|ch| ch.to_be_bytes()[1]);
            let name11_13 = long_entry.name11_13.map(|ch| ch.to_be_bytes()[1]);
            filename[offset..offset + 5].copy_from_slice(&name0_5);
            filename[offset + 5..offset + 11].copy_from_slice(&name5_11);
            filename[offset + 11..offset + 13].copy_from_slice(&name11_13);
        });
        Str256(filename)
    }

    /// get access timesepc.
    #[inline]
    pub fn get_access_timesepc(&self) -> Timespec {
        fat_time_2_unix(self.short_entry.accessed_date, 0)
    }

    /// get access timesepc.
    #[inline]
    pub fn get_modification_timesepc(&self) -> Timespec {
        fat_time_2_unix(
            self.short_entry.modification_date,
            self.short_entry.modification_time,
        )
    }

    /// get access timesepc.
    #[inline]
    pub fn get_create_timesepc(&self) -> Timespec {
        fat_time_2_unix(
            self.short_entry.creation_date,
            self.short_entry.creation_time,
        )
    }

    #[inline]
    /// get `self` Fat32DiskINode indisk size
    pub fn get_indisk_size(&self) -> usize {
        size_of::<LongFileEntry>() * (self.long_entries.len() + 1)
    }

    pub fn set_data_cluster_start(&mut self, data_cluster_id: ClusterId) {
        self.data_cluster_start = data_cluster_id;
        let hi = (data_cluster_id >> 16) as u16;
        let lo = data_cluster_id as u16;
        self.short_entry.cluster_high = hi;
        self.short_entry.cluster_low = lo;
    }

    pub fn rename(&mut self, new_short_name: [u8; 11], new_long_name: &str) {
        self.short_entry.name = new_short_name;
        let long_entries =
            Fat32DiskINode::create_long_entries(new_long_name, fat32_check_sum(&new_short_name));
        self.long_entries = long_entries;
    }
}

#[repr(C)]
pub struct FatTable {
    pub fat_table_vec: Vec<u8>,
    current: u32,
}

impl FatTable {
    pub fn new(fat_table_vec: Vec<u8>) -> Self {
        Self {
            fat_table_vec: fat_table_vec,
            current: 0,
        }
    }
    /// get the value correspond given cluster_id in fat table.
    pub fn get(&self, cluster_id: ClusterId) -> vfs::Result<ClusterId> {
        let range = (cluster_id << 2) as usize..(cluster_id << 2) as usize + 4;
        let bytes_option = self.fat_table_vec.get(range);

        match bytes_option {
            None => Err(FsError::InvalidParam),
            Some(bytes) => {
                let mut u32_bytes: [u8; 4] = [0u8; 4];
                u32_bytes.copy_from_slice(bytes);
                Ok(ClusterId::from_le_bytes(u32_bytes))
            }
        }
    }

    /// set the value correspond given cluster_id in fat table.
    pub fn set(&mut self, cluster_id: ClusterId, value: ClusterId) -> vfs::Result<()> {
        let bytes_option = self
            .fat_table_vec
            .get_mut((cluster_id << 2) as usize..(cluster_id << 2) as usize + 4);
        match bytes_option {
            None => Err(vfs::FsError::InvalidParam),
            Some(bytes) => {
                let u32_bytes: [u8; 4] = value.to_le_bytes();
                bytes.copy_from_slice(&u32_bytes);
                Ok(())
            }
        }
    }

    fn alloc_cluster(&mut self) -> vfs::Result<ClusterId> {
        let mut idx = self.current;
        for _ in 0..self.fat_table_vec.len() / size_of::<u32>() {
            let val = self.get(idx)?;
            if FREE_CLUSTER_MARK == val {
                self.set(idx, END_OF_CLUSTER)?;
                self.current = idx + 1;
                return Ok(idx);
            }
            idx += 1;
        }
        Err(FsError::NoDeviceSpace)
    }

    /// Alloc a cluster chain of length `n` and ending with `END_OF_CLUSTER`.
    pub fn alloc_cluster_chain(&mut self, n: usize) -> vfs::Result<ClusterId> {
        let head = self.alloc_cluster()?;
        let mut idx = head;
        for _ in 1..n {
            let next_idx = self.alloc_cluster()?;
            self.set(idx, next_idx)?;
            idx = next_idx;
        }
        return Ok(head);
    }
}

impl Debug for FatTable {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        for i in 0..20 {
            let val_result = self.get(i);
            match val_result {
                Ok(val) => write!(f, "0x{:x} ", val)?,
                Err(err) => write!(f, "{:?} ", err)?,
            }
        }
        Ok(())
    }
}

impl AsRef<[u8]> for FatTable {
    fn as_ref(&self) -> &[u8] {
        return self.fat_table_vec.as_ref();
    }
}

bitflags::bitflags! {
    #[derive(Default)]
    pub struct Fat32FileAttr: u8 {
        /// read only.
        const READ_ONLY = 1 << 0;
        /// hidden.
        const HIDDEN = 1 << 1;
        /// system file.
        const SYSTEM_FILE = 1 << 2;
        /// volume label.
        const VOLUME_LABEL  = 1 << 3;
        /// DIRECTORY
        const DIRECTORY = 1 << 4;
        /// archive
        const  ARCHIVE = 1 << 5;
        /// 0xf represent this entry is long file entry.
        const LONG_FILE_ENTRY = Self::READ_ONLY.bits | Self::HIDDEN.bits | Self::SYSTEM_FILE.bits | Self::VOLUME_LABEL.bits;
    }
}

const_assert!(size_of::<FatBpb>() == 512);
const_assert!(size_of::<ShortFileEntry>() == 32);
const_assert!(size_of::<LongFileEntry>() == 32);
