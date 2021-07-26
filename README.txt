# FamilySketcher2 --- Program Sketcher based on Lifted Analysis 

This tool is a research prototype program sketcher designed for resolving numerical sketches using lifted static analyzis based on abstract interpretation


## Author

	Aleksandar Dimovski
	
	
# Installation

The tool requires the following applications and libraries:

* OCaml 

	```
	(sudo) apt-get install ocaml-interp
	```

* Findlib

	```
	(sudo) apt-get install ocaml-findlib
	```

* Menhir: LR(1) parser generator

	```
	(sudo) apt-get install menhir
	```
  
* Opam: https://opam.ocaml.org/doc/Install.html

	```
	(sudo) apt-get install opam
	```
  
* OUnit

	```
	opam install ounit
	```

* APRON: numerical abstract domain library

	```
	opam install apron
	```
	
* Set the Library Path variable in ~/.bashrc open with "gedit ~/.bashrc" 

	LD_LIBRARY_PATH=/home/aleks/.opam/system/share/apron/lib
	export LD_LIBRARY_PATH


* Zarith: arbitrary-precision integer operations

	```
	opam install zarith
	```

* Z3 solver: Micrsoft's Z3 SMT solver

	```
	sudo apt install z3
	```

# Compiling lifted_analyzer

Once all required libraries are installed, 'ocamlbuild' can be used to build lifted_analyzer with the following command:

```
eval $(opam config env)                 % It will setup environment variables, that are necessary for the toolchain to work properly

ocamlbuild Main.native -use-ocamlfind -use-menhir -pkgs 'apron,gmp,oUnit,zarith' -I utils -I domains -I frontend -I main -libs boxMPQ,octD,polkaMPQ,str,zarith
```

# Usage

The program sketcher performs a forward reachability analysis and a backward termination analysis of program families and resolves the holes (features) so that 
the found solutions are 'correct & optimal' with respect to the final assertions and the given quantitative objective. 

The following general command-line options are recognized
(showing their default value):

	 -tree					set to perform decision tree-based lifted analysis
	 -single 				set to perform brute force enumeration approach using single analysis for each variant
	 -main main                         set the analyzer entry point (defaults to main)
	 -domain boxes|octagons|polyhedra   set the abstract domain (defaults to boxes)
	 -joinfwd 2   			     set the widening delay in forward analysis

#################################################
# Examples from the paper are in 'bench' folder:

enter the folder that contains the tool, and write

$ ./Main.native -tree -domain polyhedra bench/loop1a-5.c
$ ./Main.native -tree -domain polyhedra bench/loop1b-5.c
$ ./Main.native -tree -domain polyhedra bench/loop2a-5.c
$ ./Main.native -tree -domain polyhedra bench/loop2b-5.c
$ ./Main.native -tree -domain polyhedra bench/loopcond-5.c
$ ./Main.native -tree -domain polyhedra bench/nestedloop-5.c
$ ./Main.native -tree -domain polyhedra bench/vmcai2004b-5.c


################################################################################
##Brute Force approach --- Single-Program Analysis of all variants one by one ##
################################################################################

We stay in the same folder ¨family_sketcher2¨ as for FamilySketcher2, we run the same example files, but now  
we use command-line option ¨-single¨ instead of ¨-tree¨. 

# Examples from the paper are in 'bench' folder:

$ ./Main.native -single -domain polyhedra bench/loop1a-5.c
$ ./Main.native -single -domain polyhedra bench/loop1b-5.c
$ ./Main.native -single -domain polyhedra bench/loop2a-5.c
$ ./Main.native -single -domain polyhedra bench/loop2b-5.c
$ ./Main.native -single -domain polyhedra bench/loopcond-5.c
$ ./Main.native -single -domain polyhedra bench/nestedloop-5.c
$ ./Main.native -single -domain polyhedra bench/vmcai2004b-5.c



###########################################################################################
## Sketch 1.7.6 --- Program Sketcher available from https://people.csail.mit.edu/asolar/ ##
###########################################################################################

The tool can be downloaded either from https://people.csail.mit.edu/asolar/ or can be found here. 

* unzip the file sketch-1.7.6.tar.gz
	```
	tar -xf sketch-1.7.6.tar.gz
	```
* copy ¨tests¨ folder to ¨sketch-1.7.6/sketch-frontend¨ 
	```
	cp -r ./tests ./sketch-1.7.6/sketch-frontend
	```
	
Follow the instructions either in README.txt of ¨sketch-1.7.6¨ folder or below.  

# the following tools need to be installed: 
* bison and flex

	```
	(sudo) apt-get install bison
	(sudo) apt-get install flex
	```

# under the sketch-1.7.6 directory, execute:

	```
	cd sketch-1.7.6
	cd sketch-backend
	chmod +x ./configure
	./configure
	make
	cd ..
	```
	
# Testing the sketch
	```
	cd sketch-frontend
	chmod +x ./sketch
	./sketch test/sk/seq/miniTest1.sk 
	```
	
# from sketch-frontend directory you can test all sketches. 
Note that we use the following ¨./sketch¨ options

option --bnd-cbits determines the size in bits of control holes [default is 5]
option --bnd-inbits determines the size in bits of inputs [default is 5]
option --bnd-unroll-amnt determines the unroll amount for loops [default is 8]

# Examples from the paper are in ¨tests¨ folder (copy 'tests' subfolder into 'sketch-1.7.6/sketch-frontend'): 	

./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 8 tests/loop1a.sk
./sketch --bnd-cbits 6 --bnd-inbits 6 --bnd-unroll-amnt 8 tests/loop1a.sk
./sketch --bnd-cbits 16 --bnd-inbits 16 --bnd-unroll-amnt 8 tests/loop1a.sk

./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 11 tests/loop1b.sk
./sketch --bnd-cbits 6 --bnd-inbits 6 --bnd-unroll-amnt 11 tests/loop1b.sk
./sketch --bnd-cbits 16 --bnd-inbits 16 --bnd-unroll-amnt 11 tests/loop1b.sk    - timeout

./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 11 tests/loop2a.sk   [empty solution]
./sketch --bnd-cbits 6 --bnd-inbits 6 --bnd-unroll-amnt 11 tests/loop2a.sk
./sketch --bnd-cbits 16 --bnd-inbits 16 --bnd-unroll-amnt 11 tests/loop2a.sk

./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 11 tests/loop2b.sk	[empty solution]
./sketch --bnd-cbits 6 --bnd-inbits 6 --bnd-unroll-amnt 11 tests/loop2b.sk
./sketch --bnd-cbits 16 --bnd-inbits 16 --bnd-unroll-amnt 11 tests/loop2b.sk

./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 32 tests/loopcond.sk
./sketch --bnd-cbits 6 --bnd-inbits 6 --bnd-unroll-amnt 64 tests/loopcond.sk
./sketch --bnd-cbits 16 --bnd-inbits 16 --bnd-unroll-amnt 65536 tests/loopcond.sk   - timeout

./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 8 tests/nestedloop.sk  [no solution]
./sketch --bnd-cbits 6 --bnd-inbits 6 --bnd-unroll-amnt 8 tests/nestedloop.sk
./sketch --bnd-cbits 16 --bnd-inbits 16 --bnd-unroll-amnt 8 tests/nestedloop.sk

./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 8 tests/vmcai2004.sk
./sketch --bnd-cbits 6 --bnd-inbits 6 --bnd-unroll-amnt 8 tests/vmcai2004.sk
./sketch --bnd-cbits 16 --bnd-inbits 16 --bnd-unroll-amnt 8 tests/vmcai2004.sk
