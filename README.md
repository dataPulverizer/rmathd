# rmathd is a D translation of the Rmath.h internal module from R 3.4.1

This code conversion is intended to convert R's `d`, `p`, and `q` type distribution functions to D. The r-type functions for random sampling effectively have a placeholder RNG function from R's `Rmath.h` module rather than RNG from the `RNG.h` module. It is therefore not recommended to use the r-type functions until such time the RNG from the RNG module is added.

The code conversion sticks very closely to the original version which is very much an internal module and not a user-friendly tool for immediate use in analysis. The main purpose of converting the library is to use it as an internal resource in other libraries.

For information on the converted functions, see the `package.d` file and [R's source code](https://cran.r-project.org/).

Thank you.
