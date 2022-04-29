# euf

## Installation
* EUF relies on certain features, e.g. the `match` keyword, which are only available in Python 3.10 onwards.
* The Python bindings for libclang utilise clang-13, if it is not installed, the `setup.sh` script will attempt to build it from source.

```sh
git clone --recursive https://github.com/Kafva/euf.git
./scripts/setup.sh
```

Every invocation of EUF requires a JSON config file as an argument. The format of the config file is described in `src/config.py` and there are several examples present in the repository.
```
(venv) ./euf.py --config tests/configs/basic.json
```

EUF can also be built and used with Docker
```sh
# Build the base image
docker build --rm --tag=euf-base -f Dockerfile.base .

# Build a derived image with any additional setup steps
docker build --rm --tag=euf -f Dockerfile .

# Mount the dependency (oniguruma) and the main project (jq)
# along with the results directory and execute a configuration
# available inside the container

```

## CBMC fork
To avoid duplicate symbols a fork of CBMC which adds a suffix to all global symbols has been created. The symbol renaming is triggered by starting `cbmc`, `goto-cc` or any of the other Cprover tools with `USE_SUFFIX` set in the environment.

## Tests
Unit tests for the functions of the actual script are ran with
```sh
pytest tests/test_*
```

## Implementation notes
EUF compiles the old and new version of the dependency _twice_, once using `bear` to generate a compile commands database and once with `goto-cc` to create a version of the library that CBMC can interact with. Combining these steps would have been preferable but doing so seems unsupported, (no commands are recorded in `compile_commands.json` if `CC` is overriden with `goto-cc`).

## Interpreting the output
EUF can be invoked with a `VERBOSITY` value from 0-3, setting the verbosity to zero will only print errors and a prettified version of the impact set. Higher values will print information regarding each analysis stage. 

With minimum verbosity, EUF will give each impact site its own header and print a list of related changes beneath it. Listing dependency changes mapped to a list of affected call sites can sometimes create output that is easer to oversee and is possible by toggling the `ORDER_BY_CALL_SITE` option.

Changes are categorized as either *direct* or *indirect*. A direct change to a function infers that the AST of the old and new version differs. An indirectly changed function is a function which calls one or more functions with either a direct or indirect change.

The impact set presented by EUF will only consider changed functions that are reachable from the main project based on AST traversal. For example, in the image below `util/nad.c:nad_parse()` has been affected by an indirect change to `XML_Parse`. The indirect change originates from direct (or additional indirect) changes in `XML_GetBuffer` and `XML_ParseBuffer`, neither of which are directly called in the main project. Each change is prefixed with the line and column number of the invocation within the current file.

![](.assets/impact_set_example.png)
![](.assets/impact_set_example_2.png)

A complete canonical representation of the impact set will always be written to `./results/<dependency>_<new>_<old>/impact_set.json` for further analysis.

The change set given from AST diffing can be visualised by providing the `--diff` flag. This will show the exact line and column where two functions diverge followed by the textual git-diff for each modified file.
