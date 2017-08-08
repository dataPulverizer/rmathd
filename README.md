# rmathd is a D translation of the Rmath.h internal module from R 3.4.1

This code conversion is intended to convert R's `d`, `p`, `q`, and `r` type distribution functions to D. This library is distributed under GPL-3 as per the original R library but it contains a standalone module `(rmathd.rng.rng)` for random number generation built from D's `std.random` library that is distributed using the Boost Software License version 1.0.

The code conversion sticks very closely to the original version which is very much an internal module and not a user-friendly tool for immediate use in analysis. The main purpose of converting the library is to use it as an internal resource in other libraries.

For information on the converted functions, see the `package.d` file and [R's source code](https://cran.r-project.org/).

### Compiler dependency

**Please compile this library with dmd version >= v2.075.0**, manual compilation:

`dub build --compiler=dmd`

Thank you.
