CC ?= gcc
all: pqvs
pqvs: pqvs.c
	$(CC) -O2 -o pqvs pqvs.c -lm
test: pqvs
	./pqvs validate
bench: pqvs
	./pqvs bench 3 5 16 62 512 11
plan: pqvs
	./pqvs plan 3 5 40 80 2048
clean:
	rm -f pqvs
