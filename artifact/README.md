# ITP 2026 submission #87 supplementary material

## Overview

This archive corresponds to the ITP 2026 submission #87:

> Tactics modulo associativity and cancellation for category theory

It contains:

- `graph-rewriting/`: The Graph Rewriting library
  + Most of the code was copied from (a slightly new version of) the companion Rocq development of the following paper, and thus, is not a contribution of the present paper.
    > S. Arsac, R. Harmer, and D. Pous. Adhesive category theory for graph rewriting in Rocq. In Proc. of CPP '26, 2026.
  + The contribution of the present paper are:
    * `theories/Arewrite.v`: Rocq code for the modulo AU/G tactics
    * `theories/*.elpi`: Elpi code for the modulo AU/G tactics
    * `tests/Arewrite_tests.v`: A demo of the tactics
  + NB: The instance of category for `Type`s and functions in this library requires a few axioms. Nevertheless, this is irrelevant to the present work (cf. `Print Assumptions all` at the end of `Arewrite_tests.v`). See also Section 5.1 of the CPP '26 paper for the details of the axioms.
- `monoid.v`: A complete implementation of the material presented in the paper
  + The monoid structure and the hierarchy of invertible elements (Section 2)
  + The simply-typed version of the modulo AU/G tactics (Sections 3 to 6)
  + A demo of the tactics, at the end of the file

## Prerequisites and their install instructions

- OPAM (>= 2.3 is recommended):
  You may use the package manager of your distribution.
  See [Opam installation instructions](https://opam.ocaml.org/doc/Install.html)

- OCaml (4.14 is recommended):
  ```bash
  opam update
  # create a fresh OPAM switch with OCaml 4.14.2 and the Flambda optimizer
  opam switch create itp26-submission-87 \
    --package=ocaml-variants.4.14.2+options,ocaml-option-flambda
  ```

- Rocq (>= 9.0), The Rocq Standard Library (>= 9.0), Rocq-Elpi, Hierarchy Builder (>= 1.10), MathComp boot (>= 2.5):
  ```bash
  # add the OPAM repository for Rocq packages
  opam repo --switch itp26-submission-87 \
    add rocq-released https://rocq-prover.org/opam/released
  # install the packages
  opam install --switch itp26-submission-87 \
      rocq-core.9.1.0 rocq-stdlib.9.1.0 \
      rocq-elpi.3.2.0 rocq-hierarchy-builder.1.10.2 rocq-mathcomp-boot.2.5.0
  ```

## Build instructions

To build the Graph Rewriting library:
```bash
eval $(opam env --switch itp26-submission-87)
make -C graph-rewriting
```

## Explore

You need a Rocq aware editor to browse our file with Rocq's feedback. You may use the one you prefer. We recommend either Emacs with Proof General or VS Code/Codium with the VsRocq extension.

NB: We use the `Restart` command in the demo to show a few alternative proofs, which is not supported by VsRocq. You may need to edit the proof script to see how these proofs work, e.g., removing the first proof to check the second proof.

### With VS Code/Codium

If you chose to use VS Code, and you picked OPAM as a way to install requirements, you need to install via OPAM the corresponding language server:
```bash
opam install --switch itp26-submission-87 vscoq-language-server
eval $(opam env --switch itp26-submission-87)
```
