![OS](https://img.shields.io/badge/os-linux%20%7C%20macos%20%7C%20windows-blue?style=flat-square)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg?style=flat-square)](https://opensource.org/licenses/MIT)
[![CI](https://img.shields.io/github/actions/workflow/status/cda-tum/LogicBlocks/ci.yml?branch=main&style=flat-square&logo=github&label=c%2B%2B)](https://github.com/cda-tum/LogicBlocks/actions/workflows/ci.yml)
[![codecov](https://img.shields.io/codecov/c/github/cda-tum/LogicBlocks?style=flat-square&logo=codecov)](https://codecov.io/gh/cda-tum/LogicBlocks)

# LogicBlocks - A Interface Library for SAT/SMT Abstractions written in C++

A interface library for the abstraction of several methods of interaction with SAT/SMT Solvers developed by the [Chair for Design Automation](https://www.cda.cit.tum.de/) at the [Technical University of Munich](https://www.tum.de/).

LogicBlocks are built in the style of the z3 bindings for C++. The library is designed to offer a simpler way to encode SAT/SMT problems in C++ code and hand it off to several different solvers or text exports.
Note that at the moment the z3 integration is mostly working, as is export in DIMACs and the SMTLibv2 format.

If you have any questions, feel free to contact us via [quantum.cda@xcit.tum.de](mailto:quantum.cda@xcit.tum.de) or by creating an issue on [GitHub](https://github.com/cda-tum/LogicBlocks/issues).

## Usage

LogicBlocks are designed to be used as a submodule in conjunction with git and CMake.

- In order to start using LogicBlocks, first the submodule needs to be added:

```bash
git submodule add https://github.com/cda-tum/LogicBlocks.git
git submodule update --init --recursive
```

Then, to include the necessary files in your project the following lines need to be added to your CMakeLists.txt:

```cmake
add_subdirectory("${PROJECT_SOURCE_DIR}/LogicBlocks" "LogicBlocks")
```

As well as linking to the library:

```cmake
target_link_libraries(${PROJECT_NAME} PUBLIC logicblocks::Logic)
```

Finally, in all files where LogicBlocks are needed, the required files need to be included:

```cpp
#include "LogicBlocks/LogicBlock.hpp"
```

## Examples

A minimal working example needs at least some kind of LogicBlock and some LogicTerms:
The following example initializes a SMTLibv2 LogicBlock (supporting export to SMTLibv2 Format) and initializes two variables `a` and `b` with the respective LogicTerms, by creating variables from the LogicBlock.

```cpp
#include "LogicBlocks/LogicBlock.hpp"
#include "LogicTerm/LogicTerm.hpp"

using namespace logicbase;
int main() {
   SMTLogicBlock logicBlock();

    LogicTerm a = logicBlock.makeVariable("a", CType::BOOL);
    LogicTerm b = logicBlock.makeVariable("b", CType::BOOL);

    logicBlock.assertFormula(a && b);
    logicBlock.produceInstance();
}
```

Then, `assertFormula(LogicTerm)` asserts a formula to the LogicBlock.
Finally, `produceInstance()` produces an instance of all asserted formulas exported to SMTLibv2 format.

## Structure

- `LogicBlock` - Contains the various interfaces for interacting with SAT/SMT Solvers.
  - `LogicBlock.hpp` - Contains the base classes, `LogicBlock` for encoding general SAT/SMT problems and `LogicBlockOptimizer` for encoding optimization problems.
  - `Model.hpp` - Contains the base class for models, optionally returned by SAT/SMT Solvers.
- `LogicTerm/LogicTerm.hpp` - Contains the main way of interacting and writing encodings of problems, the LogicTerm.
- `Encodings/Encodings.hpp` - Contain some different encodings for common problems, especially `At most one` and `Exactly one` encodings.

As of now there are several Theories besides pure SAT that are supported:

- `Integer` - Integer arithmetic and comparison, including `+`, `-`, `/`, `*`, `<`, `>`, `<=` and `>=`.
- `Real` - Real arithmetic and comparison, including `+`, `-`, `/`, `*`, `<`, `>`, `<=` and `>=`.
- `Bitvector` - Bitvector arithmetic and comparison, including `+`, `-`, `/`, `*`, `<`, `>`, `<=` and `>=`, and using `BV_XOR`, `BV_AND` and `BV_OR` bit wise operations on bitvectors.
