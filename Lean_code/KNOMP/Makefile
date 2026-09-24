CXX ?= g++
# -O3 for the extra optimization headroom on real hardware; -march=native
# is deliberately NOT used by default since this package is meant to be
# copied to different (possibly heterogeneous, e.g. cloud) hardware -- an
# -march=native binary built on one machine can SIGILL on another with a
# different microarchitecture. Uncomment the line below (and comment the
# one after it) if you know the build and run machine are identical.
# CXXFLAGS = -O3 -march=native -std=c++17 -I include -I /usr/include/eigen3
CXXFLAGS = -O3 -std=c++17 -I include -I /usr/include/eigen3
LDFLAGS = -lpthread

HEADERS = include/json.hpp include/nk_kepler.hpp include/nk_optimize.hpp \
          include/nk_realdata.hpp include/nk_lskr.hpp include/nk_l1periodogram.hpp

all: bin/realdata_main

bin:
	mkdir -p bin

bin/realdata_main: src/realdata_main.cpp $(HEADERS) | bin
	$(CXX) $(CXXFLAGS) src/realdata_main.cpp -o bin/realdata_main $(LDFLAGS)

clean:
	rm -rf bin
