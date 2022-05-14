# euf
EUF (Equivalent update filter) is an impact assessment tool for upgrading
open source C dependencies. The tool expects the following inputs:

1. A C project which uses an outdated version of a particular library
2. The commit hash for the current version of the library
3. The commit hash for the upgraded version of the library

By analyzing the differences between the two versions and their relationship to
the main project, EUF presents a set of locations in the main project which are
deemed impacted by the upgrade. The core procedure can be described as follows:

1. Determine what source files in the dependency have been modified or renamed
   since the current commit based on information from Git.
2. Walk the AST of the current and new version of each modified file and
   consider any functions with a difference in their AST composition as the base
   change set.
3. Inspect all calls in the dependency and the main project to each changed
   function and record if a parameter is always set to a constant value.
4. Generate stub C files which compare the output of the current and the
   upgraded version of each function in the change set.
5. Link each stub file against the current and the new version of the library
   and assess equivalence through instrumented execution in CBMC, all arguments
   except those identified as constant in step three are modeled as
   non-deterministic.
6. Remove the functions which based on the preceding analysis produce the same
   return value for the same input from the change set.
7. Enumerate indirectly changed functions, i.e. functions that call a directly
   changed function and add these to the change set.
8. Walk the AST of all source files in the main project and present the impact
   set, i.e. all locations were functions from the change set are called.

## Installation EUF has four core dependencies:
* Python >=3.10, required to support type hints and the `match` keyword
* Clang 13, required for the clang-plugins module and Python's libclang bindings
* Bear, used to generate compilation databases for libclang
* CBMC, the core tool for equivalence analysis

To setup the project, clone all submodules and refer to `./scripts/setup.sh` or
build the Docker image (recommended).

```bash
git clone --recursive https://github.com/Kafva/euf.git

# Semi-automatic setup for Arch or Ubuntu 20.04
./scripts/setup.sh

# Docker setup:
# Additional setup steps will likely be necessary
# to build the projects being analyzed and the Docker
# configuration is therefore split into two separate images

# Base image with all dependencies built
docker build --rm --tag=euf-base -f Dockerfile.base .

# Project specific image derived from Dockerfile.base
docker build --rm --tag=euf .

# Download and setup example projects
# (applies for both native and Docker installations)
./scripts/dl-examples.sh
```

Every invocation of EUF requires a JSON configuration file as an argument. The
format of the configuration file is described in `src/config.py` and there are
several examples present in the repository.

```bash
(venv) ./euf.py --config tests/configs/basic.json

# The dependency (oniguruma), the main project (jq) and
# any other resources like custom configs must be manually mounted
# when using Docker.
# Refer to ./scripts/docker-run.sh for development/debugging in Docker
docker run \
  -v $HOME/Repos/.docker/jq:/home/euf/Repos/jq \
  -v $HOME/Repos/.docker/oniguruma:/home/euf/Repos/oniguruma \
  euf --config tests/configs/onig_docker.json
```

Note that running EUF both within and outside Docker on the same repositories is
not supported, create separate directories if this is necessary.

## CBMC fork
To avoid duplicate symbols a fork of CBMC which adds a suffix to
all global symbols has been created. The symbol renaming is triggered by
starting `cbmc`, `goto-cc` or any of the other Cprover tools with `USE_SUFFIX`
set in the environment.

## Tests
```bash
# Miscellaneous function tests
pytest tests/test_misc.py

# Regression tests for each example project.
# Verifies the generated results against expected
# output under ./tests/expected
pytest tests/test_reg.py

# Regression test for Docker
VERIFY=true ./scripts/docker-run.sh

# Debug regressions with
./scripts/check_tests.sh
```

## Debugging harnesses
If a generated harness can not be compiled into a GB executable EUF will display
an error message akin to *'An error occurred during goto-cc compilation of
<...>'*. To sieve out the error messages from the compilation of a specific
function, the `test_harness.sh` script can be used. Specific configuration
settings (e.g. `USE_EXISTING_DRIVERS`) for debugging are meant to be set
inside of the script.


```bash
./scripts/test_harness.sh $euf_conf $func_name
```

## Implementation notes
EUF compiles the old and new version of the dependency _twice_, once using
`bear` to generate a compile commands database and once with
`goto-cc` to create a version of the library that CBMC can interact with.
Combining these steps would have been preferable but doing so seems unsupported,
(no commands are recorded in `compile_commands.json` if `CC` is overriden with
`goto-cc`).

## Interpreting the output
EUF can be invoked with a `VERBOSITY` value from 0-3, setting the verbosity to
zero will only print errors and a prettified version of the impact set. Higher
values will print information regarding each analysis stage.

With minimum verbosity, EUF will give each impact site its own header and print
a list of related changes beneath it. Listing dependency changes mapped to a
list of affected call sites can sometimes create output that is easer to oversee
and is possible by toggling the `ORDER_BY_CALL_SITE` option.

Changes are categorized as either *direct* or *indirect*. A direct change to a
function infers that the AST of the old and new version differs. An indirectly
changed function is a function which calls one or more functions with either a
direct or indirect change.

The impact set presented by EUF will only consider changed functions that are
reachable from the main project based on AST traversal. For example, in the
image below `util/nad.c:nad_parse()` has been affected by an indirect change to
`XML_Parse`. The indirect change originates from direct (or additional indirect)
changes in `XML_GetBuffer` and `XML_ParseBuffer`, neither of which are directly
called in the main project. Each change is prefixed with the line and column
number of the invocation within the current file.

![](.github/images/impact_set_example.png)
![](.github/images/impact_set_example_2.png)

A complete canonical representation of the impact set will always be written to
`./results/<dependency>_<new>_<old>/impact_set.json` for further analysis.

The change set given from AST diffing can be visualised by providing the
`--diff` flag. This will show the exact line and column where two functions
diverge followed by the textual git-diff for each modified file.
