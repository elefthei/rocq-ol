# Outcome Logic in Rocq

A mechanization in [Rocq](https://rocq-prover.org/) (formerly Coq) of Outcome Logic from:

> **Outcome Logic: A Unifying Foundation for Correctness and Incorrectness Reasoning**
> Noam Zilberstein, Derek Dreyer, Alexandra Silva
> *OOPSLA 2023*

Program logics for bug-finding (such as the recently introduced Incorrectness Logic) have framed correctness and incorrectness as dual concepts requiring different logical foundations. In this paper, we argue that a single unified theory can be used for both correctness and incorrectness reasoning. We present Outcome Logic (OL), a novel generalization of Hoare Logic that is both monadic (to capture computational effects) and monoidal (to reason about outcomes and reachability). OL expresses true positive bugs, while retaining correctness reasoning abilities as well. To formalize the applicability of OL to both correctness and incorrectness, we prove that any false OL specification can be disproven in OL itself. We also use our framework to reason about new types of incorrectness in nondeterministic and probabilistic programs. Given these advances, we advocate for OL as a new foundational theory of correctness and incorrectness.

## Architecture

The development is organized in 4 layers:

### 1. Powerset Monad & PCM (`theories/OL/Monad.v`)

Defines `PSet Sigma` (powersets of states), set union as the partial commutative monoid (PCM) operation, and the Kleisli lift for sequential composition.

### 2. Assertion Logic (`theories/OL/Assertion.v`, `Triple.v`)

Deep-embedded BI (Bunched Implications) formulas with:
- Outcome conjunction `⊕`
- Standard connectives: `∨`, `∧`, `¬`, `⊤`, `⊥`
- Satisfaction relation `m ⊨ φ` over `PSet Sigma`
- OL triple definition `⟨φ⟩ C ⟨ψ⟩`

### 3. Heap Separation Logic (`theories/OL/Heap/`)

Instantiation over a concrete heap model:
- **`Assertion.v`** — Heap model (partial map nat → nat), error tags (`ok`/`er`), SL assertions (`↦`, `emp`, `∗`), structural lemmas
- **`Lang.v`** — Atomic commands: assign, load, store, alloc, free, assume
- **`Error.v`** — Error-tagged state model
- **`Manifest.v`** — Manifest error characterization (Lemma 5.7)
- **`Rules.v`** — Separation logic proof rules for heap commands

### 4. Proof System (`theories/OL/Rules/`, `Hoare.v`, `Falsification.v`)

Sound inference rules and metatheory:
- **`Rules/Generic.v`** — Zero, One, Seq, Split, Consequence, Empty, True, False, For
- **`Rules/Nondeterministic.v`** — Plus, Induction (Kleene star)
- **`Rules/Expression.v`** — Assign, Assume, While rules
- **`Hoare.v`** — Embedding of Hoare Logic into OL
- **`Falsification.v`** — Semantic Falsification (Thm 4.1), Principle of Denial (Thm 4.5), ND Falsification (Thm 4.4), Hoare Logic Falsification (Cor 4.10)

### Examples (`examples/OL/`)

Bug-finding proofs demonstrating OL in action:
- **`Malloc.v`** — Nondeterministic malloc with null dereference
- **`DoubleFree.v`** — Double-free memory error
- **`LoadAfterFree.v`** — Use-after-free via load
- **`PushBack.v`** — Use-after-free in push_back (Fig 6 from paper)
- **`ManifestError.v`** — Manifest error example

## Properties

- **Single axiom**: `heap_ext` (functional extensionality for heaps) — standard and consistent
- **Zero `Admitted`**: All proofs are complete
- **~5000+ lines** of Rocq across 16 source files

## Building

Requires Rocq 9.x and Dune 3.21+.

```bash
# Build theories
cd theories/OL && dune build

# Build examples
cd examples/OL && dune build
```

## References

- [Paper (OOPSLA 2023)](https://doi.org/10.1145/3622830)
- [arXiv preprint](https://arxiv.org/abs/2303.03111)
