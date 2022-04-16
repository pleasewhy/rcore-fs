
DST=/mnt
FILES_DIR=./files
fat32fs.img:
	@if [ ! -f "fat32fs.img" ]; then \
		echo "making fs image..."; \
		dd if=/dev/zero of=fat32fs.img bs=512k count=512; \
		mkfs.vfat -s 1 -F 32 fat32fs.img; fi
	@sudo mount fat32fs.img $(DST)
	@for file in $$( ls $(FILES_DIR)/* ); do \
		sudo cp $$file $(DST)/`basename $$file`;\
		echo cp `basename $$file`; done
	ls /mnt
	@sudo umount $(DST)

clean:
	rm fat32fs.img

.PHONY: fat32fs.img
	
