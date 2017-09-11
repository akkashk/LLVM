The file 'parallelisation_pass.cpp' contains the source code for the project. Parameters inside the source code are set by the user to indicate how many cores are 
present in the target processor and the pass accordingly spawns threads.

In order to run the pass, a shared object file must be created from the source code using LLVM. As an example I've compiled the source code into a shared object
that spawns two threads to parallelise loops called 'cores_2.so'

In order to run the pass, we must convert the input C program to LLVM's bitcode format:

clang -c -emit-llvm <source.c>

Then followed by running the list of required optimisation passes for dependency analysis:

opt -mem2reg -simplifycfg -loop-simplify -loop-rotate -simplifycfg -instcombine -indvars <source.bc> -o <optimisedSource.bc>

Then we use LLVM's opt command to run the parallelisation pass:

opt -load=./cores_2.so -paralleliseLoops <optimisedSource.bc> -o <destination.bc>

The <destination.bc> is then compiled with clang, linking the pthread library to produce an executable:

clang -pthread <destination.bc>