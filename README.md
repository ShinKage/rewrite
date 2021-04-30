# Rewrite

NOTE: The second iteration of the tool is available in the `idris2` branch and is implemented with Idris2 instead of Idris.

A tool for directed graph rewriting, harnessing the power of dependent types for rule verification, with Idris.
It supports simple rewrite rules, negative properties, interfaces and typed graphs.

The motivation and the experiences behind this work are documented in my thesis: _Verified Graph Rewriting: Dependent types in general programming_.

## How-to-start
Two libraries are required by the implementation, if not already installed this two command can be used:
```
make lightyear
make graphviz
```

To build an executable: `make build`
To execute the test code: `make test`

(c) Giuseppe Lomurno 2019
