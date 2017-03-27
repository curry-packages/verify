# curry-verify - A Tool to Support the Verification of Curry Programs

This package contains the tool `curry-verify` that supports
the verification of Curry programs
with the help of other theorem provers or proof assistants.
Currently, only Agda is supported as
a target language for verification (but more target languages
may be supported in future releases).


## Installing the tool

The tool can be directly installed by the command

    > cpm installbin verify

This installs the executable `curry-verify` in the bin directory of CPM.


## Using the tool

If the bin directory of CPM (default: `~/.cpm/bin`) is in your path,
execute the tool with the module containing properties to be verified, e.g.,

    > curry-verify -t agda -s choice Double

