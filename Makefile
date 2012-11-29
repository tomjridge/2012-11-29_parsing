SHELL=bash
.SUFFIXES=

all: FORCE
	(cd src && make)

FORCE: