-- Using Lake / creating projects

-- lake new greeting

-- Main.lean is the file in which the Lean compiler will look for the main action.

-- Greeting.lean and Greeting/Basic.lean are the scaffolding of a support library for the program.

-- lakefile.toml contains the configuration that lake needs to build the application.

-- lean-toolchain contains an identifier for the specific version of Lean that is used for the project.

-- lake init (for existing directory)

-- imports
import FpInLean.HelloWorld

-- building
-- lake build
-- binary is placed in .lake/build/bin
-- can be run standalone or using lake exe greeting

-- lakefile.toml describes package settings, library declaration, and executable name
-- contain exactly one package, but any number of dependencies, libraries, or executables.
-- By convention, package and executable names begin with a lowercase letter, while libraries begin with an uppercase letter
-- more here https://lean-lang.org/functional_programming_in_lean/Hello___-World___/Starting-a-Project/#libraries-and-imports
