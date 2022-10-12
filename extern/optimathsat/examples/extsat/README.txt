Example code for using an external SAT solver with MathSAT
==========================================================

Quick compilation instructions
------------------------------

- Download Minisat (version 2.2.0) and Cleaneling (version 00g), and unpack
  them in this directory

- Apply the patches as follows:

  $ patch -p1 < minisat.patch
  $ patch -p1 < cleaneling.patch

- run "make"

If everything works, you should get an "extsolver" executable, which allows
you to run MathSAT with an external SAT solver as its DPLL engine. "extsolver"
takes as first argument the SAT solver to use ("minisat" or "cleaneling", all
lowercase) and reads an SMT-LIBv2 formula from standard input.
