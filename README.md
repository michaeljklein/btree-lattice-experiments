
# btree-lattice-experiments

This repo contains proofs that `btree`

```coq
Cumulative Inductive btree {A : Type} : Type :=
  | bnil : A -> btree
  | bcons : btree -> btree -> btree.
```

Forms a `Lattice`:

```coq
Class Lattice (A : Type) := {
  lmeet : A -> A -> A where "x ⊓ y" := (lmeet x y);
  ljoin : A -> A -> A where "x ⊔ y" := (ljoin x y);

  lmeet_commutative : Commutative lmeet;
  lmeet_associative : Associative lmeet;
  lmeet_absorptive  : Absorptive lmeet ljoin;
  lmeet_idempotent  : Idempotent lmeet;

  ljoin_commutative : Commutative ljoin;
  ljoin_associative : Associative ljoin;
  ljoin_absorptive  : Absorptive ljoin lmeet;
  ljoin_idempotent  : Idempotent ljoin
}.
```

Where `lmeet` is:

```coq
Equations and_btree : magma btree! :=
and_btree (bnil _) (bnil _) := bnil () ;
and_btree (bnil _) (bcons _ _) := bnil () ;
and_btree (bcons _ _) (bnil x) := bnil () ;
and_btree (bcons x y) (bcons z w) := bcons (and_btree x z) (and_btree y w).
```

And `ljoin` is:

```coq
Equations or_btree : magma btree! :=
or_btree (bnil _) (bnil _) := bnil tt ;
or_btree (bcons x y) (bnil _) := bcons x y ;
or_btree (bnil _) (bcons x y) := bcons x y ;
or_btree (bcons x y) (bcons z w) := bcons (or_btree x z) (or_btree y w).
```

And `<=` is:

```coq
Definition ble {A : Type} (x : @btree 1) (y : @btree A) : Type :=
  { xy : @bforest A (num_leaves x) (num_leaves y)
  | run_bforest x xy = y
  }.
```



## Building

To build:

```bash
cd deps/coq-lattice && make
make
```

For OCaml:

```bash
❯❯❯ opam switch create . 4.05.0
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations
Respond: Y[es]
opam install coq-dpdgraph
Respond: Y[es]
```

```bash
~/C/c/s/s01 ❯❯❯ opam repo add coq-released https://coq.inria.fr/opam/released
[coq-released] no changes from https://coq.inria.fr/opam/released
[NOTE] Repository coq-released has been added to the selections of switch /Users/michaelklein/Coding/coq/scratch/s01 only.
       Run `opam repository add coq-released --all-switches|--set-default' to use it in all existing switches, or in newly created switches, respectively.

~/C/c/s/s01 ❯❯❯ opam install coq-equations
The following actions will be performed:
  ∗ install base-num       base       [required by num]
  ∗ install conf-findutils 1          [required by coq]
  ∗ install conf-m4        1          [required by ocamlfind]
  ∗ install num            0          [required by coq]
  ∗ install ocamlfind      1.8.1      [required by coq]
  ∗ install coq            8.10.2     [required by coq-equations]
  ∗ install coq-equations  1.2.1+8.10
===== ∗ 7 =====
Do you want to continue? [Y/n] y

<><> Gathering sources ><><><><><><><><><><><><><><><><><><><><><><><><><><>  🐫 
[coq.8.10.2] found in cache
[coq-equations.1.2.1+8.10] found in cache
[ocamlfind.1.8.1] found in cache

<><> Processing actions <><><><><><><><><><><><><><><><><><><><><><><><><><>  🐫 
∗ installed base-num.base
∗ installed num.0
∗ installed conf-m4.1
∗ installed conf-findutils.1
∗ installed ocamlfind.1.8.1
∗ installed coq.8.10.2
∗ installed coq-equations.1.2.1+8.10
Done.
```

```bash
❯❯❯ opam install coq-dpdgraph
The following actions will be performed:
  ∗ install ocamlgraph   1.8.8 [required by coq-dpdgraph]
  ∗ install coq-dpdgraph 0.6.6
===== ∗ 2 =====
Do you want to continue? [Y/n] y

<><> Gathering sources ><><><><><><><><><><><><><><><><><><><><><><><><><><>  🐫 
[ocamlgraph.1.8.8] found in cache
[coq-dpdgraph.0.6.6] downloaded from https://github.com/Karmaki/coq-dpdgraph/releases/download/v0.6.6/coq-dpdgraph-0.6.6.tgz

<><> Processing actions <><><><><><><><><><><><><><><><><><><><><><><><><><>  🐫 
∗ installed ocamlgraph.1.8.8
∗ installed coq-dpdgraph.0.6.6
Done.
```



## Dependency graph

- Generate a `.dot` file: `make depgraph_dot`
- Generate an image: `make depgraph_svg`
  - Requires [graphviz](http://www.graphviz.org)
- Visualize the graph: `make depgraph_show`
  - Requires [xdot](https://pypi.org/project/xdot/)

## Axioms

View axioms using:

```bash
make axiom_finder
```

The results are logged to: [`axioms_found.log`](axioms_found.log)

