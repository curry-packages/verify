# curry-verify - A Tool to Support the Verification of Curry Programs

This package contains the tool `curry-verify` that supports
the verification of Curry programs
with the help of other theorem provers or proof assistants.
Currently, only Agda is supported as
a target language for verification (but more target languages
may be supported in future releases).
The ideas implemented by this tool are described
in [this paper](http://dx.doi.org/10.4204/EPTCS.234.13):

S. Antoy, M. Hanus, and S. Libby:
_Proving non-deterministic computations in Agda_.
In Proc. of the 24th International Workshop on Functional and
(Constraint) Logic Programming (WFLP 2016),
volume 234 of Electronic Proceedings in Theoretical Computer Science,
pages 180--195. Open Publishing Association, 2017.


## Installing the tool

The tool can be directly installed by the command

    > cypm install verify

This installs the executable `curry-verify` in the bin directory of CPM.


## Using the tool

If the bin directory of CPM (default: `~/.cpm/bin`) is in your path,
execute the tool with the module containing properties to be verified, e.g.,

    > curry-verify -t agda -s choice Double

