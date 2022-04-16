extern crate alloc;
use alloc::str;
use alloc::sync::Arc;
use rcore_fs::{dev, util::uninit_memory, vfs, vfs::*};
use rcore_fs_fat32::utils::*;
use rcore_fs_fat32::{fat_struct::FatBpb, Fat32FileSystem};
use std::sync::Mutex;
use std::{fs::File, fs::OpenOptions, os::unix::prelude::FileExt};
struct DeviceImpl {
    file: Mutex<File>,
}

impl DeviceImpl {
    pub fn new(path: &str) -> Self {
        let file = OpenOptions::new()
            .write(true)
            .read(true)
            .open(path)
            .unwrap();
        Self {
            file: Mutex::new(file),
        }
    }
}

impl dev::Device for DeviceImpl {
    fn read_at(&self, offset: usize, buf: &mut [u8]) -> dev::Result<usize> {
        Ok(self
            .file
            .lock()
            .unwrap()
            .read_at(buf, offset as u64)
            .unwrap() as usize)
    }

    fn write_at(&self, offset: usize, buf: &[u8]) -> dev::Result<usize> {
        if offset == 0 {
            panic!("\n\noffset={} buf.len={}\n\n", offset, buf.len());
        }
        Ok(self
            .file
            .lock()
            .unwrap()
            .write_at(buf, offset as u64)
            .unwrap() as usize)
    }

    fn sync(&self) -> dev::Result<()> {
        self.file.lock().unwrap().sync_all().unwrap();
        Ok(())
    }
}

fn open_fat_fs() -> Arc<Fat32FileSystem> {
    std::fs::copy("fat32fs.img", "test.img").expect("failed to open fat32fs.img");
    let device = Arc::new(DeviceImpl::new("test.img"));
    Fat32FileSystem::open(device).expect("failed to open Fat32FS")
}

// #[test]
// fn test_basic() {
//     let fat32fs = open_fat_fs();
//     let root_inode = fat32fs.root_inode();

//     let name = root_inode.list().unwrap();
//     println!("{:?}", name);
// }

// #[test]
// fn test_find() {
//     let fat32fs = open_fat_fs();
//     let root_inode = fat32fs.root_inode();
//     let inode = root_inode.find("a.txt").unwrap();
//     let mut buf: [u8; 64] = [0u8; 64];
//     let len = inode.read_at(0, buf.as_mut()).unwrap();
//     let content = str::from_utf8(&buf[0..len]).unwrap();
//     println!("{:?}", content);
// }

// #[test]
// fn test_unlink() {
//     let fat32fs = open_fat_fs();
//     let root_inode = fat32fs.root_inode();
//     root_inode.unlink("a.txt").unwrap();
// }

// #[test]
// fn test_find_after_unlink() {
//     let fat32fs = open_fat_fs();
//     let root_inode = fat32fs.root_inode();
//     root_inode.unlink("b.txt").unwrap();
//     let inode = root_inode.find("a.txt").unwrap();
//     let mut buf: [u8; 64] = [0u8; 64];
//     let len = inode.read_at(0, buf.as_mut()).unwrap();
//     let content = str::from_utf8(&buf[0..len]).unwrap();
//     println!("{:?}", content);
// }

// this case from linux
#[test]
fn test_checksum() {
    /* With no extension. */
    assert_eq!(
        fat32_check_sum("VMLINUX    ".as_bytes().try_into().unwrap()),
        44u8
    );
    assert_eq!(
        fat32_check_sum("README  TXT".as_bytes().try_into().unwrap()),
        115u8
    );
    assert_eq!(
        fat32_check_sum("ABCDEFGHA  ".as_bytes().try_into().unwrap()),
        98u8
    );
}

// this case from linux
#[test]
fn test_fattime_2_unixtime() {
    assert_eq!(
        fat_time_2_unix(0, 0),
        Timespec {
            sec: 315532800,
            nsec: 0
        }
    ); // Earliest possible UTC (1980-01-01 00:00:00)

    assert_eq!(
        fat_time_2_unix(65439, 49021),
        Timespec {
            sec: 4354819198,
            nsec: 0
        }
    ); // Latest possible UTC (2107-12-31 23:59:58)

    assert_eq!(
        fat_time_2_unix(8285, 0),
        Timespec {
            sec: 825552000,
            nsec: 0
        }
    ); //Leap Day / Year (1996-02-29 00:00:00)

    assert_eq!(
        fat_time_2_unix(10333, 0),
        Timespec {
            sec: 951782400,
            nsec: 0
        }
    ); //Year 2000 is leap year (2000-02-29 00:00:00)

    assert_eq!(
        fat_time_2_unix(61537, 0),
        Timespec {
            sec: 4107542400,
            nsec: 0
        }
    ); // Year 2100 not leap year (2100-03-01 00:00:00)
}

#[test]
fn create_file() -> vfs::Result<()> {
    let fs = open_fat_fs();
    let root = fs.root_inode();
    let file1 = root.create("file1", vfs::FileType::File, 0o777)?;

    assert_eq!(
        file1.metadata()?,
        Metadata {
            inode: 2,
            size: 0,
            type_: FileType::File,
            mode: 0o777,
            blocks: 0,
            atime: Timespec {
                sec: 315532800,
                nsec: 0
            },
            mtime: Timespec {
                sec: 315532800,
                nsec: 0
            },
            nlinks: 1,
            uid: 0,
            ctime: Timespec {
                sec: 315532800,
                nsec: 0
            },
            gid: 0,
            blk_size: 512,
            dev: 0,
            rdev: 0,
        }
    );

    fs.sync()?;
    Ok(())
}

#[test]
fn resize() -> Result<()> {
    let fs = open_fat_fs();
    let root = fs.root_inode();
    let file1 = root.create("file1", FileType::File, 0o777)?;
    assert_eq!(file1.metadata()?.size, 0, "empty file size != 0");

    const SIZE1: usize = 0x1234;
    const SIZE2: usize = 0x1250;
    println!("resize");
    file1.resize(SIZE1)?;
    assert_eq!(file1.metadata()?.size, SIZE1, "wrong size after resize");
    println!("resize ok");
    let mut data1: [u8; SIZE2] = unsafe { uninit_memory() };
    println!("read_at");
    let len = file1.read_at(0, data1.as_mut())?;
    println!("read_at ok");
    assert_eq!(len, SIZE1, "wrong size returned by read_at()");
    assert_eq!(
        &data1[..SIZE1],
        &[0u8; SIZE1][..],
        "expanded data should be 0"
    );
    fs.sync()?;
    Ok(())
}

#[test]
fn resize_on_dir_should_panic() -> Result<()> {
    let fs = open_fat_fs();
    let root = fs.root_inode();
    assert!(root.resize(4096).is_err());
    fs.sync()?;

    Ok(())
}

#[test]
fn resize_too_large_should_panic() -> Result<()> {
    let fs = open_fat_fs();
    let root = fs.root_inode();
    let file1 = root.create("file1", FileType::File, 0o777)?;
    assert!(file1.resize(1 << 40).is_err());
    fs.sync()?;

    Ok(())
}

#[test]
fn create_then_lookup() -> Result<()> {
    let fs = open_fat_fs();
    let root = fs.root_inode();
    println!("1");
    assert!(Arc::ptr_eq(&root.lookup(".")?, &root), "failed to find .");
    assert!(Arc::ptr_eq(&root.lookup("..")?, &root), "failed to find ..");
    println!("2");

    let file1 = root
        .create("file1", FileType::File, 0o777)
        .expect("failed to create file1");
    println!("3");

    assert!(
        Arc::ptr_eq(&root.lookup("file1")?, &file1),
        "failed to find file1"
    );
    println!("4");

    assert!(root.lookup("file2").is_err(), "found non-existent file");

    println!("lookup2");
    let dir1 = root
        .create("dir1", FileType::Dir, 0o777)
        .expect("failed to create dir1");
    let file2 = dir1
        .create("file2", FileType::File, 0o777)
        .expect("failed to create /dir1/file2");
    println!("look up dir1/file2");
    assert!(
        Arc::ptr_eq(&root.lookup("dir1/file2")?, &file2),
        "failed to find dir1/file2"
    );
    assert!(
        Arc::ptr_eq(&root.lookup("/")?.lookup("dir1/file2")?, &file2),
        "failed to find dir1/file2"
    );
    assert!(
        Arc::ptr_eq(&dir1.lookup("..")?, &root),
        "failed to find .. from dir1"
    );

    assert!(
        Arc::ptr_eq(&dir1.lookup("../dir1/file2")?, &file2),
        "failed to find dir1/file2 by relative"
    );
    assert!(
        Arc::ptr_eq(&dir1.lookup("/dir1/file2")?, &file2),
        "failed to find dir1/file2 by absolute"
    );
    assert!(
        Arc::ptr_eq(&dir1.lookup("/dir1/../dir1/file2")?, &file2),
        "failed to find dir1/file2 by absolute"
    );
    assert!(
        Arc::ptr_eq(&dir1.lookup("../../..//dir1/../dir1/file2")?, &file2),
        "failed to find dir1/file2 by more than one .."
    );
    assert!(
        Arc::ptr_eq(&dir1.lookup("..//dir1/file2")?, &file2),
        "failed to find dir1/file2 by weird relative"
    );

    assert!(
        root.lookup("./dir1/../file2").is_err(),
        "found non-existent file"
    );
    assert!(
        root.lookup("./dir1/../file3").is_err(),
        "found non-existent file"
    );
    assert!(
        root.lookup("/dir1/../dir1/../file3").is_err(),
        "found non-existent file"
    );
    assert!(
        root.lookup("/dir1/../../../dir1/../file3").is_err(),
        "found non-existent file"
    );
    assert!(
        root.lookup("/").unwrap().lookup("dir1/../file2").is_err(),
        "found non-existent file"
    );

    fs.sync()?;
    Ok(())
}

#[test]
#[ignore]
fn kernel_image_file_rename() -> Result<()> {
    let fs = open_fat_fs();
    let root = fs.root_inode();
    let files_count_before = root.list()?.len();
    root.move_("a.txt", &root, "rename_test_a.txt")?;
    let files_count_after = root.list()?.len();
    assert_eq!(files_count_before, files_count_after);
    assert!(root.lookup("a.txt").is_err());
    assert!(root.lookup("rename_test_a.txt").is_ok());

    fs.sync()?;
    Ok(())
}
