SHELL=bash
HAPPY=~/.cabal/bin/happy
GHC=ghc

all: test

HappyMain: HappyMain.hs Happy.y
	$(HAPPY) --glr Happy.y
	$(GHC) --make -XFlexibleInstances -XOverlappingInstances -O2 HappyMain.hs

test: HappyMain FORCE
	time ./HappyMain 11111111111111111111

clean: FORCE
	rm -f *.o *.hi HappyData.hs Happy.hs HappyMain

FORCE: