# L23 fill log (bricks L2 + L3 of DESIGN_C3B)

## 2026-09-26 entry 1

Placement: DESIGN_C3B names no file for L2/L3. One new file next to the existing monotonicity and
restriction homes (`WindowedWitnessRestriction.lean`, `WindowedModelRestriction.lean`):
`Perelman/CanonicalNeighborhood/WindowedWitnessStrictRestriction.lean` (not registered in the root
aggregate; no other file edited).

Existing API found (not re-proved): `WindowedModelWitness.mono_of_regular`
(`WindowedWitnessRestriction.lean:48`) is already the plain L2 monotonicity `delta ≤ eps`;
`mono_strict_of_interior_regular` (`InteriorWitnessRestriction.lean:45`) only transports a strict
hypothesis. Missing piece was strictness *from* `delta < eps`, which needs no strict hypothesis.

Consumer shapes matched (quoted from DESIGN_C3B §4):
- L4 `hwindow : Icc (t - (eps * S₀.scalar t x)⁻¹) t ⊆ D.regular`
- L4 `hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
  ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
  tensor02CovDerivNormWith a (W.comparison.jet b s) (W.model.S.base.metric s)
  (W.model.S.base.metric s) y < eps`
- L6 "Q∞ has a strict witness at (z∞, T∞) (threshold at δ/4 plus L2). Restrict it to D' (L3)."

Declarations (L2): `WindowedModelWitness.mono_of_regular_strict_of_lt`,
`WindowedModelWitness.exists_strict_of_lt`, `WindowedModelWitness.window_subset_regular_of_lt`
(produces L4's `hwindow` at the larger tolerance from the smaller window's `hreg` plus
`t ∈ D.regular`), `orientedWitness_mono_of_regular`, `orientedWitness_exists_strict_of_lt`.

Declarations (L3): `WindowedModelWitness.toRestrictOpen` (hypothesis: `W.embedding ''
closedBall(modelRadius eps + 1) ⊆ U`, U any open set, no closedness), `toRestrictOpen_model`,
`toRestrictOpen_embedding`, `toRestrictOpen_source`, `toRestrictOpen_embedding_coe`,
`toRestrictOpen_strict` (L4's `hstrict` survives restriction verbatim),
`WindowedModelWitness.orientedWitness_toRestrictOpen` (orientation `o.restrictOpen U`).
Note: an `OrientedWitness`-to-`OrientedWitness` restriction cannot take a witness-free hypothesis:
the buffer annulus `modelRadius eps .. +1` is not metrically controlled by the witness, so the
image containment is stated for the explicit witness.

Dropped: `toRestrictOpen_comparison_jet := rfl` hit a whnf timeout; `toRestrictOpen_strict`
(proved by `hstrict` itself) covers the use.

## 2026-09-26 entry 2

Compile: `LEAN_NUM_THREADS=2 lake env lean` on the new file (read-only; one retry after a missing
mathlib `.olean.private` during a concurrent build): zero errors, zero warnings, zero info.
Axioms (scratch copy outside the repo, all 12 public declarations): `propext`, `Classical.choice`,
`Quot.sound` only. Lines ≤ 100 chars; no comments/docstrings; no sorry/nolint/overrides.
Public names grep-checked unique library-wide. Not built with `lake build`, not registered in the
root aggregate, no git writes.
