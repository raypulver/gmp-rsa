CC=g++

all: rsa

rsa: rsa.cc
	$(CC) -o rsa rsa.cc -lgmp -std=c++0x -g

.PHONY: clean

clean:
	rm -f rsa
