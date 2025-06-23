# Formalization of Normalization by Evaluation of System T

This repo formalizes the normalization of evaluation of System T (STLC + Nat + Recursion) in Coq, including totality, soundness and completeness. The proof follows "Normalization by Evaluation: Dependent Typs and Impredicativity". The machanization is based on those in https://github.com/HuStmpHrrr/mech-type-theories which were written in Agda.

## Usage 

```
make
```

The proof of System T is in `./systemt/`. 

`./ptt/` contains unfinished work for a extending System T to a dependently typed system. Since its corresponding Agda formalization requires induction-recursion which is not currently supported by Coq, it may remain unfinished for a long time (there is a workaround to rely on the impredicativity of `Prop` in Coq, as shown in A "Coq Formalization of Normalization by Evaluation for Martin-Löf Type Theory")

`./stlc/` contains unfinished work for replacing explicit substitutions with substitution-as-operations.

### Dependency

(Recommended): use `opam switch` to create a new opam environment.

- `coq-8.19.2`

```bash
opam pin add coq 8.19.2
```

- [`CoqHammer`](https://github.com/lukaszcz/coqhammer) (tested on version 1.3.2)

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer-tactics
```

- [`TLC`](https://github.com/charguer/tlc)(tested on version 20240209)

```bash
opam repo add coq-released http://coq.inria.fr/opam/released
opam install coq-tlc
```

- [`autosubst-ocaml`](https://github.com/uds-psl/autosubst-ocaml) (tested on version 1.1)

```bash
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam install coq-autosubst-ocaml
```
