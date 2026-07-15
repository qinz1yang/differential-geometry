# StepBLocalizedAA.lean — B-loc localized map/isometry compactness (2026-06-13)

MSM135 Ch4 Step B, brick **B-loc** (STEPB_PLAN Planner Ruling Q2): localize the F7/F8
APIs from total `Set.univ` maps to maps on nested Euclidean balls.

## Status: COMPLETE (planner authorized the engine edit)

**Verification PASSED**: focused locked checks + targeted builds green for both
`MapConvergence.lean` and `StepBLocalizedAA.lean` (no warnings); axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) for `exists_cInf_subseq_on`,
`isometry_seq_cInf_on`, `isometry_seq_diffeo_on`, `comp_eq_id_of_cInf_on`.

### Delivered here (`StepBLocalizedAA.lean`)
- `IsometryDerivBoundsOn U Φ` — localized derivative-bounds predicate (bounds on
  compacts ⊆ open `U`), with `IsometryDerivBoundsOn.comp_subseq` and
  `IsometryDerivBounds.toOn` (global ⇒ localized restriction).
- `comp_eq_id_of_cInf_on` — localized **inverse-identity step**, a pure consumer of
  `MapCInfConvOnCompacts`: compact neighbourhood of `Ψ_∞ x` taken inside the open
  codomain `V` via `exists_compact_subset`.
- `isometry_seq_cInf_on` — localized convergence core (direct application of
  `exists_cInf_subseq_on`).
- `isometry_seq_diffeo_on` — localized diffeo compactness, mirroring the global
  `isometry_seq_diffeo` with `comp_eq_id_of_cInf_on`. **Inverse identities are
  conditional on domain membership** (`∀ x ∈ U, Φ_∞ x ∈ V → Ψ_∞ (Φ_∞ x) = x`, and
  symmetrically): the limits are only controlled on the open domains, so the membership
  is an explicit hypothesis, not a hidden frontier. Step B's nested-ball containment
  (`E^α ⊆ Ē^α ⊆ vec E^α`) discharges it in B-trans/B-glue. The second identity reuses
  the same lemma with `E`/`F` swapped (inferred from the arguments).

### The localized AA extraction (in `MapConvergence.lean`, planner-authorized)
`exists_cInf_subseq_on` + private `equicontOn_iteratedFDerivWithin`. The earlier
"blocked, stop-and-report" status is RESOLVED: the planner authorized the narrow engine
edit. The proof bundles the *within* derivatives `∇ᵤʳΦₖ` as continuous maps on the
metric subspace `↥U`, runs the existing vector Arzelà–Ascoli (↥U locally compact +
second-countable ⇒ sigma-compact), links the limits by differentiation on open balls
inside `U`, and assembles `HasFTaylorSeriesUpToOn ⊤` — **no smooth cutoff, no
ball-to-space diffeomorphism** (the two forbidden routes). Full route + gotchas in
`MapConvergence.md`.

## Lean notes
- `exists_compact_subset (hU : IsOpen U) (hx : x ∈ U) : ∃ K, IsCompact K ∧ x ∈ interior
  K ∧ K ⊆ U` is the locally-compact workhorse; `mem_interior_iff_mem_nhds.mp` turns
  `x ∈ interior K` into `K ∈ 𝓝 x`.
- `ContDiffOn.continuousOn` supplies the `ContinuousOn Φ_∞ V` that `comp_eq_id_of_cInf_on`
  needs, replacing the global `Continuous`.
- `omit [FiniteDimensional ℝ E] in` on `comp_eq_id_of_cInf_on` (only `F`'s local
  compactness is used).

## Conditional-cocycle generalization (2026-06-13, frontier-1 push)
`comp_eq_id_of_cInf_on` and `isometry_seq_diffeo_on` had **global** inverse hypotheses
(`hid : ∀ k x, Φ k (Ψ k x) = x`, `hLeft : ∀ k x, …`). Generalized to **domain-conditional**
(`∀ k, ∀ x ∈ U, …`) so the HCG `normalTransition` wrapper (junk off the chart overlap) can
satisfy them honestly — the conclusions were already conditional, so this just aligns the
hypotheses. Proof change is one line (`have hidx : ∀ k, Φ k (Ψ k x) = x := fun k => hid k x
hx` before the `simp`). Both re-verified axiom-clean. Backward compatible (the only caller,
`exists_transitionLimit_on`, threads the membership through).

## 2026-07-13 finite Pi bounds

Added `IsometryDerivBoundsOn.pi`. Componentwise localized derivative bounds,
together with componentwise smoothness on the open domain, now assemble into
the bound for a finite Pi-valued map. The proof uses the canonical
`Analysis/Calculus/PiDeriv.lean` tuple-derivative identity and a finite sum of
nonnegative component bounds.

Focused verification and the targeted refresh passed with no local warning.
This is reusable compactness machinery; it does not itself produce
`StepB1RawInput`.
