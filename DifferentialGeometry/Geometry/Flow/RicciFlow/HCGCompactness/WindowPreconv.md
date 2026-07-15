# WindowPreconv.lean — P3 Brick D (window-uniform C^∞ upgrade)

**Status: IMPLEMENTED, verified sorry-free + axiom-clean (2026-06-11).**
Focused check + targeted build green; `#print axioms` clean (only
`propext`/`Classical.choice`/`Quot.sound`) on every public theorem.

## Endpoint and where it sits

P3 = MSM135 Lemma 3.11 / Thm 3.10 input: convert the P2 `(B_r)` window bounds +
the q=1 evolution into a window-uniform `C^∞`-on-compacts convergent subsequence.
Brick D is the **time-uniformity upgrade**: it turns *per-time* spatial
preconvergence (Bricks A–C) into convergence **uniform over the whole window**,
matching `SourceMetricCPConvOnWindow`'s quantifier shape
(`ε → k0 → ∀ k ≥ k0 → ∀ t ∈ [β,ψ]`) so P4 consumes it directly.

This file does NOT touch `MetricPreconv.lean` (Brick B's area). The per-time
convergence is the abstract hypothesis `hconv`.

## What's proved (all sorry-free)

Pure-real helpers (no manifold context):
- `sqrt_sum_sq_add_le` — Euclidean ℓ² triangle inequality, via discrete
  Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` + squaring (NO `EuclideanSpace`
  needed — the squaring route avoids all `PiLp` friction).
- `sqrt_sum_sq_sub_le_of_hasDerivAt` — Euclidean ℓ² **vector mean value
  inequality**: componentwise `HasDerivAt` + `∑(c' i)² ≤ L²` ⇒
  `√(∑(c i s − c i t)²) ≤ L|s−t|`.  THIS one lifts to `EuclideanSpace ℝ ι` via
  `PiLp.continuousLinearEquiv` and applies
  `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.

Manifold layer (`ManifoldSection`, full HCG variable block):
- `sqrtNormSq0S_add_le` — triangle inequality for the `gRef`-fibre norm
  `√normSq0S`, via `normSq0S_identity_eq_sum_sq` (sum-of-squares in a
  `gRef`-orthonormal basis) + `sqrt_sum_sq_add_le`.
- `metricDerivNorm_triangle` — `metricDerivNorm a A C ≤ metricDerivNorm a A B +
  metricDerivNorm a B C`; the difference tower `metricDiffCovDerivAt` telescopes
  by pure `sub_add_sub_cancel` (NO field-linearity needed — it is the difference
  of the two `metricCovDeriv`s, an algebraic identity on the fibre).
- `metricDerivNormSupOn_le_of_forall` — pointwise `≤ c` ⇒ `metricDerivNormSupOn
  ≤ c` (`Real.sSup_le`, which handles empty/unbounded edge cases for `ℝ`).
- `timeLipschitz_of_hasDerivAt` — **the q=1 time-Lipschitz estimate**, stated
  abstractly over the `HasDerivAt` evolution family + a uniform `√normSq0S(Ev) ≤
  L` bound (exactly `hevComp_of_solutions`'s output shape + `ric_bound_field` +
  `(B_a)`); componentwise in a `gRef`-ON basis it feeds
  `sqrt_sum_sq_sub_le_of_hasDerivAt`.
- `windowPreconv` — **the Brick D endpoint, the `3ε` upgrade.**  Inputs: uniform
  time-Lipschitz of `gSeq k ·` and `gInf ·` (constant `L`); a dense set
  `S ⊆ [β,ψ]` (`hdense`); abstract per-time convergence `hconv` at the dense
  times (the Brick C boundary).  Output: window-uniform `metricDerivNormSupOn <
  ε`.  Finite δ-net via `IsCompact.elim_finite_subcover` on `isCompact_Icc`
  (centres in `S ∩ Icc`), `δ = ε/(3(L+1))`, three-term triangle split, constant
  bound `c = 2Lδ + ε/3 < ε`.

## Abstraction boundary (what Brick C / wiring supplies)

`windowPreconv` consumes:
1. `hconv` — per-time pointwise convergence of `gSeq k τ → gInf τ` at the dense
   times `τ ∈ S` (Brick C delivers this per time; the **dense-time diagonal**
   makes it a common subsequence, baked into the `gSeq`/`gInf` passed in).
2. `hgLip` / `hInfLip` — the uniform time-Lipschitz of the sequence and the limit.
   `timeLipschitz_of_hasDerivAt` produces `hgLip` from the P2 q=1 evolution
   (`hevComp_of_solutions`) once the uniform `√normSq0S(−2∇ᵖRc) ≤ L` bound is
   assembled from `ric_bound_field` + the `(B_a)` window bounds (a pointwise
   `≤`-composition).  `hInfLip` for the limit follows by passing the same Lipschitz
   bound to the limit (continuity of `gInf`, a Brick C output).

The full-window limit family `gInf : ℝ → SmoothRiemannianMetric I M` is a GIVEN
(it is `D.limitMetric` at the P4 layer / the Brick C limit), not constructed here.

## Route deviations from the plan

- The plan listed "componentwise scalar AA"-style steps; the actual triangle
  inequality is cleaner via **pure-real Cauchy–Schwarz** (`sqrt_sum_sq_add_le`),
  no `EuclideanSpace`.  `EuclideanSpace` is needed ONLY for the vector MVT
  (`sqrt_sum_sq_sub_le_of_hasDerivAt`), localized to one pure-real lemma.
- `metricDiffCovDerivAt` telescopes by `sub_add_sub_cancel` — it is the
  *difference of the two covariant derivatives*, so no `MetricCovDerivLinear`
  field-linearity is invoked (simpler than the plan anticipated).

## Lean gotchas hit

- `exists_gOrthonormalBasis` / `metricInverseInBasis_of_orthonormal` are in
  namespace `DifferentialGeometry.Integral.Connection` — needs that `open`
  (not `Tensor0SBundle`).
- `component0S_add` (and the `(u+w)`/sub component identities) are `rfl` —
  use `fun slots => rfl` / `congr 1`, not the named lemma (`Tensor0SBundle.
  component0S_add` does not resolve; the lemma lives in
  `DifferentialGeometry.Tensor.Coordinates`).
- `field_simp` CLOSES `2*(L+1)*(ε/(3*(L+1))) = 2*ε/3` outright — a trailing
  `ring` then errors with "No goals to be solved".  Drop the `ring`.
- The vector MVT `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` returns
  `‖f y − f x‖ ≤ C‖y − x‖` with `(xs : x ∈ s)(ys : y ∈ s)` LAST; for
  `‖f s − f t‖` pass `ht hs` (x:=t, y:=s), not `hs ht`.
- `EuclideanSpace ℝ ι` element construction: `(fun i => v i : EuclideanSpace ℝ ι)`
  type-ascription is REJECTED (`(ι → ℝ)` vs `EuclideanSpace`).  Build via
  `(PiLp.continuousLinearEquiv 2 ℝ (fun _ => ℝ)).symm v` and use
  `PiLp.continuousLinearEquiv_symm_apply` + `EuclideanSpace.norm_eq`.  HasDerivAt
  transfers through the CLE by `e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt`.

## Progress (honest, nested)

- This brick (`windowPreconv` + 6 supporting lemmas): the time-uniformity engine
  of P3, **complete and verified**.
- P3 (metric preconvergence → `SourceMetricCPConvOnWindow`): Bricks A1, A2 done;
  Brick D done; Bricks B (chart extraction + diagonal), C (limit reassembly +
  norm bridge) still open, plus the wiring (`hgLip`/`hInfLip` from P2, the
  dense-time diagonal feeding `hconv`).  P3 ≈ 40%.
- Lemma 3.11 / Thm 3.10 input: P1 ✅, P2 ✅, P3 in progress.  ≈ 70% of the
  3.11→3.10 chain when P3 lands.
- Whole HCG compactness project (MSM135 Ch3 + Ch4): ≈ 30–35%.
