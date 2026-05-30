# Halving the Kalton--Roberts upper bound

This repository contains a Lean/mathlib formalization supplementing the
forthcoming paper:

[arXiv:2606.XXXX](https://arxiv.org/abs/2606.XXXX)

The Kalton--Roberts constant is the best universal constant in the following
stability problem for finitely additive measures. If `f` is a real-valued set
function on an algebra of sets, with `f(∅) = 0` and

$$
|f(A) + f(B) - f(A \cup B)| \leq \Delta
$$

whenever `A` and `B` are disjoint, then `f` should be uniformly close to a
finitely additive signed measure. The constant `K_KR` is the least `C` such
that one can always choose a finitely additive signed measure `μ` with

$$
\sup_A |f(A)-\mu(A)| \leq C\Delta.
$$

This repository formalizes the certified bound

$$
K_{\mathrm{KR}} \leq
\frac{694198146664396294486127753}{34994834677886019996000000}
=19.837160342\ldots < 19.838.
$$

The proof uses mixed neighbouring intersections: triple/fourfold intersections
in the one-sided case, and a fourfold plus mixed fourfold/fivefold construction
in the two-sided case. The four expander rows are formalized in Lean, with the
analytic endpoint bounds proved from rational logarithm estimates.

The formalization was carried out with GPT-5.5 Pro and Harmonic Aristotle.

## Contents

- `KaltonRoberts/` - Lean formalization modules.
- `KaltonRoberts.lean` - root import for the formalization.
- `kalton_api.py` - pure standard-library verification API.
- `scripts/verify_halving.py` - command-line verifier.
- `notebooks/kalton_api_demo.ipynb` - Jupyter notebook that imports `kalton_api.py` directly; no package installation is needed.
- `LICENSE` - MIT license for the repository.

## Toolchain

This formalization uses Lean `v4.28.0` and mathlib `v4.28.0`.

- Lean is pinned by `lean-toolchain`:
  `leanprover/lean4:v4.28.0`.
- mathlib is pinned in `lakefile.toml`:
  `rev = "v4.28.0"`.

## Main Lean Result

The headline theorem is in `KaltonRoberts/MainTheorem.lean`:

```lean
theorem KR_constant_lt : KR_constant < 9919 / 500
```

The exact rational bound proved just before it is:

```lean
theorem KR_constant_le_C₂ : KR_constant ≤ ↑C₂
```

where `C₂` is the rational number

$$
C_2 =
\frac{694198146664396294486127753}{34994834677886019996000000}.
$$

The same file also contains the paper-style set-algebra formulation:

```lean
theorem set_algebra_bound_C₂ {Ω : Type*} (F : BooleanSubalgebra (Set Ω))
    (f : F → ℝ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hf : IsApproxAdditiveBA f Δ) :
    ∃ μ : F → ℝ, IsFinitelyAdditiveBA μ ∧
      ∀ A : F, |f A - μ A| ≤ (C₂ : ℝ) * Δ
```

`KR_constant` itself is defined in `KaltonRoberts/Defs.lean` as the infimum of
all constants `C` satisfying the normalized Boolean-algebra version of this
approximation property.

```lean
noncomputable def KR_constant : ℝ :=
  sInf { C : ℝ | 0 ≤ C ∧
    ∀ (α : Type) [BooleanAlgebra α] (f : α → ℝ),
      IsApproxAdditiveBA f 1 →
        ∃ μ : α → ℝ, IsFinitelyAdditiveBA μ ∧ ∀ A : α, |f A - μ A| ≤ C }
```

## Formalization Notes

The Lean development follows the paper's mathematical route, but a few parts
are organized differently to make the proof robust in mathlib.

- The paper is phrased for algebras of sets. In Lean, most of the main proof is
  carried out for an abstract `BooleanAlgebra α`, then specialized back to set
  algebras via `BooleanSubalgebra (Set Ω)`. This avoids carrying set-membership
  encodings through arguments that only use Boolean-algebra operations.
- The paper's compactness reduction is formalized as a finite powerset theorem
  plus a compact product/FIP argument. This isolates the finite combinatorial
  core from the passage to arbitrary Boolean algebras.
- Recombination in the paper is naturally described with weighted collections.
  The Lean proof proves concrete finite-uniform recombination first, then uses
  epsilon approximation to pass to real-weighted `WeightedCollection`s. The
  final epsilon is removed by order closure. This avoids relying on an implicit
  denominator-clearing step for arbitrary real weights.
- The Pippenger expander rows are proved from exact rational logarithm
  certificates and convexity facts, rather than from floating-point numerics.
  The Python verifier is only an independent arithmetic check; the Lean proof
  contains the formal certificates used by the main theorem.

## Verify the Lean formalization

```bash
lake build
python scripts/check_active_sorries.py
```

The source scanner strips Lean comments and rejects active uses of `sorry`,
`admit`, `axiom`, `constant`, `opaque`, `unsafe`, `extern`,
`implemented_by`, and `native_decide`.

An axiom audit should report only the standard mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`:

```lean
import KaltonRoberts
#print axioms KR_constant_lt
```

## Verify the rational arithmetic

```bash
python3 scripts/verify_halving.py
```

The verifier runs the API checks and an independent rational rederivation of
the headline constant. The final line should be:

```text
All checks passed.
```

## Notebook API

Open `notebooks/kalton_api_demo.ipynb`. The first cell adds the repository
root to `sys.path` and imports `kalton_api`; it does not require `pip install`,
editable installs, or any non-standard Python packages for the verification
itself.

## License

This repository is released under the MIT license. See `LICENSE`.
