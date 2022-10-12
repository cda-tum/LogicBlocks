README.txt file for MathSAT 5
-----------------------------

Contents of the tarball:
  README.txt            This file.
  LICENSE.txt           The MathSAT 5 License.
  CREDITS.txt           Credits for code used in MathSAT 5.
  bin/mathsat           The MathSAT 5 executable.
  include/mathsat.h     The MathSAT 5 API header file.
  lib/libmathsat.a      The MathSAT 5 library.
  examples/*            Various examples on using MathSAT 5, both via the
                        command-line and via the C API.
  configurations/*      Sample configurations files for MathSAT 5.
  

MathSAT 5 is linked with the Gnu Multiprecision Library (GMP) and the GNU C
library (glibc), both covered by the GNU LGPL license. A copy of the LGPL and
the GNU GPL license are included in this tarball (files lgpl-3.0.txt and
gpl-3.0.txt). For other credits, see the CREDITS.txt file.

NOTE: the provided MathSAT executable is statically linked against GMP and
glibc, so as to avoid potential issues with library versions. However, a
MathSAT executable linked against a different version of GMP and/or glibc can
be obtained easily, by creating a "main.c" C file with the following content:

  extern int msat_main(int argc, const char **argv);
  int main(int argc, const char **argv) { return msat_main(argc, argv); }

and linking it against libmathsat.a, GMP and glibc. For example, using GCC:

  $ gcc main.c -o mathsat lib/libmathsat.a -lgmpxx -lgmp
