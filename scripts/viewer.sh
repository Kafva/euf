#!/usr/bin/env bash
# https://github.com/model-checking/cbmc-viewer
# This does not give any useful information
mkdir -p .viewer
cbmc runner --unwind 1 --trace --xml-ui > .viewer/result.xml
cbmc runner --unwind 1 --cover location --xml-ui > .viewer/coverage.xml
cbmc runner --unwind 1 --show-properties --xml-ui > .viewer/property.xml
cbmc-viewer --goto runner --result .viewer/result.xml --coverage .viewer/coverage.xml --property .viewer/property.xml
