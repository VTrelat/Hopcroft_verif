default: do_benchmark

gcode=../../thys/examples/code
libs=../../src/lib_isabelle_llvm.cpp ../../src/lib_isabelle_llvm.c
cflags=-std=c++11 -stdlib=libstdc++ -Wall -Wno-unused-function -O3 -flto -I${HOME}/include -I$(gcode) ../../src/lib_isabelle_llvm.cpp
# cflags=-std=c++11 -stdlib=libstdc++ -march=native -w -Wall -fexceptions -O3 -I${HOME}/include -I$(gcode) -s
# -mllvm -inline-threshold=100000 -flto

compile=clang++ $(cflags)
compile_gcc=g++ -std=c++11 -Wall -Wno-unused-function -flto -O4 -I${HOME}/include

file_generator: file_generator.cpp Makefile
	$(compile) ./file_generator.cpp -o file_generator

do_benchmark: do_benchmark.cpp $(gcode)/introsort.ll $(libs) Makefile
	$(compile) ./do_benchmark.cpp $(gcode)/introsort.ll -o do_benchmark

.PHONY: run

input.bin: file_generator Makefile
	./file_generator input.bin 125000000

run: do_benchmark input.bin all_benchmarks.sh
	./all_benchmarks.sh
