# Prototype implementation of CILC

Requires the following opam libraries to build
- `dune`
- `mparser`
- `bindlib`

To build the typechecker, use the following command.
```
$ dune build --profile release
```

After the typechecker has been built, example files can checked using the following command.
```
dune exe bin/main.exe file_to_typecheck
```

Example files can be found under the `test` directory.

If no type errors are immediately displayed, then typechecking is successful. A `log.clc` file will be produced detailing the results of syntactic desugaring and elaboration. The final core-term is subject to one last round of typechecking to make sure no ill-typed terms are synthesized during elaboration.