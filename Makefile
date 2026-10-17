ifeq ($(strip $(DEVKITARM)),)
$(error "Define DEVKITARM (devkitPro con devkitARM + nds-dev)")
endif

include $(DEVKITARM)/ds_rules

TARGET  := granular
ARCH    := -march=armv5te -mtune=arm946e-s
CFLAGS  := -O2 -Wall $(ARCH) -DARM9 -I$(LIBNDS)/include
LDFLAGS := -specs=ds_arm9.specs -g $(ARCH) -L$(LIBNDS)/lib
LIBS    := -lfat -lnds9 -lm

all: $(TARGET).nds

$(TARGET).elf: $(TARGET).c
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS) $(LIBS)

$(TARGET).nds: $(TARGET).elf
	ndstool -c $@ -9 $< -b $(LIBNDS)/icon.bmp "Granular;DS sampler;"

clean:
	rm -f $(TARGET).elf $(TARGET).nds
