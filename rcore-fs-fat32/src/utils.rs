use crate::*;
use core::cmp::max;
use rcore_fs::vfs::Timespec;

/*
 * The epoch of FAT timestamp is 1980.
 *     :  bits :     value
 * date:  0 -  4: day	(1 -  31)
 * date:  5 -  8: month	(1 -  12)
 * date:  9 - 15: year	(0 - 127) from 1980
 * time:  0 -  4: sec	(0 -  29) 2sec counts
 * time:  5 - 10: min	(0 -  59)
 * time: 11 - 15: hour	(0 -  23)
 */
const SECS_PER_MIN: u8 = 60;
const SECS_PER_HOUR: u16 = 60 * 60;
const SECS_PER_DAY: u32 = SECS_PER_HOUR as u32 * 24;
const UNIX_SECS_1980: usize = 315532800;
const UNIX_SECS_2108: usize = 4354819200;

/* days between 1.1.70 and 1.1.80 (2 leap days) */
const DAYS_DELTA: u32 = 365 * 10 + 2;
/* 120 (2100 - 1980) 不是闰年 */
const YEAR_2100: u16 = 120;

// 前n月有多少天，不包含第n月
const DAYS_IN_YEAR: [u32; 16] = [
    /* Jan  Feb  Mar  Apr  May  Jun  Jul  Aug  Sep  Oct  Nov  Dec */
    0, 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334, 0, 0, 0,
];

pub(crate) fn is_leap_year(y: usize) -> bool {
    (y % 4 == 0) && (y != YEAR_2100 as usize)
}

/// 将FAT时间格式转换为UNIX时间(1970年1月1日之后的经过的秒)
/// ts 用于存放计算结果
/// date  FAT时间格式(年月日)
/// time  FAT时间格式(时分秒)
pub fn fat_time_2_unix(date: u16, time: u16) -> Timespec {
    let date = date as usize;
    let time = time as usize;
    let mut ts = Timespec { sec: 0, nsec: 0 };
    let year = date >> 9;
    let month = max(1, (date >> 5) & 0xf);
    let day = max(1, date & 0x1f) - 1;

    let mut leap_day = (year + 3) / 4;
    if year > YEAR_2100 as usize {
        // 2100 isn't leap year
        leap_day -= 1;
    }
    if is_leap_year(year) && month > 2 {
        leap_day += 1;
    }

    let mut second = ((time & 0x1f) << 1) as u64;
    second += (((time >> 5) & 0x3f) * SECS_PER_MIN as usize) as u64;
    second += ((time >> 11) * SECS_PER_HOUR as usize) as u64;
    second += (year as u32 * 365
        + leap_day as u32
        + DAYS_IN_YEAR[month as usize]
        + day as u32
        + DAYS_DELTA) as u64
        * SECS_PER_DAY as u64;

    ts.sec = second as i64;
    ts.nsec = 0;
    ts
}

pub struct DiskInodeIter<'a> {
    dir: &'a Fat32INode,
    offset: u32,
}

impl<'a> DiskInodeIter<'a> {
    pub fn new(dir: &'a Fat32INode) -> Self {
        Self {
            dir: dir,
            offset: 0,
        }
    }
}

impl<'a> Iterator for DiskInodeIter<'a> {
    type Item = (usize, Fat32DiskINode);

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.offset >= self.dir.disk_inode.read().short_entry.file_size {
            return None;
        }
        let disk_inode = self.dir.load_fat32_disk_inode(self.offset as u64).ok();
        let offset = self.offset as usize;
        if disk_inode.is_some() {
            self.offset += disk_inode.as_ref().unwrap().get_indisk_size() as u32;
        } else {
            println!("err offset={}", self.offset);
        }
        disk_inode.map(|disk_inode| (offset, disk_inode))
    }
}

pub fn fat32_check_sum(name: &[u8; 11]) -> u8 {
    let mut s = name[0];
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[1] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[2] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[3] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[4] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[5] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[6] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[7] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[8] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[9] as u16) as u8;
    s = ((s << 7) as u16 + (s >> 1) as u16 + name[10] as u16) as u8;
    return s;
}
