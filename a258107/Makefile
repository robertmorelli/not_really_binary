CC ?= cc
CFLAGS ?= -O3 -Wall -Wextra

.PHONY: all cpu gpu opencl test clean

all: cpu

cpu: scan4 scan5 scan6

scan4: scan.c consts.h
	$(CC) $(CFLAGS) -DTOPBASE=4 scan.c -o $@ -lpthread -lm

scan5: scan.c consts.h
	$(CC) $(CFLAGS) -DTOPBASE=5 scan.c -o $@ -lpthread -lm

scan6: scan.c consts.h
	$(CC) $(CFLAGS) -DTOPBASE=6 scan.c -o $@ -lpthread -lm

gpu: gpuscan

gpuscan: gpuscan.m scan.c consts.h
	/usr/bin/clang $(CFLAGS) -fobjc-arc -DTOPBASE=6 gpuscan.m -framework Metal -framework Foundation -lpthread -lm -o $@

opencl: gpuscan_cl

gpuscan_cl: gpuscan_cl.c scan.c consts.h
	$(CC) $(CFLAGS) -DTOPBASE=6 gpuscan_cl.c -o $@ -lOpenCL -lpthread -lm

test: cpu
	python3 test.py

clean:
	rm -f scan4 scan5 scan6 gpuscan gpuscan_cl
