# BumpExtend.lean — hχgU smoothness obligation (RESOLVED, verified)

## The hard obligation
Prove the `χ • extZeroForm` frame coefficient is smooth, feeding
`bumpForm_coeff_contMDiffOn`. Originally had two `sorry`s in the `hχgU` block.

## KEY FINDING — route shape
The original skeleton tried a GLOBAL `contMDiff_of_tsupport` route (prove
`ContMDiff` everywhere, then `.contMDiffOn`). **That route is NOT provable** for
the frame coefficient: at a tsupport point `x ∈ U` that is OFF the trivialization
`baseSet`, `frameVec x₀ i` is itself not smooth (its smoothness `frameVec_cmdiffAt'`
only holds on `baseSet`). So the coefficient must be proved as
`ContMDiffOn ... baseSet` DIRECTLY, splitting on `x ∈ U` vs `x ∉ U`.
=> Restructure `bumpForm_coeff_contMDiffOn`'s `hχgU` to a `baseSet`-local
`ContMDiffOn` (lemma `hχgU_on` below); drop the global `contMDiff_of_tsupport`.
Then `(hχgU_on …).add hR` closes the coefficient (both summands on `baseSet`).

## ROUTE A compiled (contMDiffAt_subtype_iff). Route B not needed.
Verified green (read-only `lake env lean`, deliberate-error guarded — not
false-green), zero sorry.

### Three lemmas (all PRIVATE-able, put in BumpExtend `namespace Geometry`):

1. `frameVec_cmdiffAt'` — reprove of ConvexCombination's PRIVATE
   `frameVec_contMDiffAt` (NOT imported by BumpExtend; BumpExtend line 198 also
   references it and currently fails). Verbatim copy of the ConvexCombination
   proof (localFrame + `contMDiffAt_localFrame_of_mem` + `congr_of_eventuallyEq`).
   NOTE: BumpExtend line 198/199 `frameVec_contMDiffAt` must become
   `frameVec_cmdiffAt'` too.

2. `frameVec_sub_cmdiffAt` — the CRITICAL sub-problem: the U-tangent frame section
   `z:U ↦ frameVec x₀ i ↑z` is a smooth section of `TangentSpace I (·:U)` at
   `⟨x,_⟩` with `↑x ∈ baseSet`.
   - Mechanism: `ContMDiffAt.mpullback_vectorField_preimage` (Mathlib
     VectorField/Pullback.lean:602) with `f := Subtype.val`, `V := frameVec x₀ i`,
     `m=n=∞`, invertibility from `mfderiv_subtype_val = id`. This produces the
     section as `T% (mpullback I I Subtype.val (frameVec x₀ i))` — `T%` topologizes
     the U-tangent total space CORRECTLY (avoids the synthInstance failure below).
   - GOTCHA (synthInstance): writing the section directly as
     `fun z:U => TotalSpace.mk' E z (frameVec x₀ i ↑z)` makes Lean infer the fiber
     `fun z => TangentSpace I ↑z` (M-indexed-over-U) which has NO `TopologicalSpace`
     instance → `failed to synthesize TopologicalSpace (TotalSpace E fun z => TangentSpace I ↑z)`.
     FIX: pin `(E := fun z:U => TangentSpace I z)` (genuine U-tangent bundle); the
     `frameVec ↑z : TangentSpace I ↑z` value is accepted by defeq
     `TangentSpace I (z:U) ≡ TangentSpace I (z:M)`.
   - Final `congr_of_eventuallyEq` collapses `mpullback` to `frameVec ↑z` via
     `mpullback_apply` + `IsInvertible.inverse_apply_eq` (same as
     `restrictOpenTangentField_apply` in OpenSubtype.lean). NB `rw [inverse_id]`
     refused to fire (metavar/instance mismatch on the partially-applied
     `.inverse`); use `inverse_apply_eq` instead.

3. `target_hχgU_at` — `ContMDiffAt` of `fun y:M => χ y • extZeroForm U gU y (frameᵢ)(frameⱼ)`
   at `x ∈ baseSet ∩ U`:
   - `rw [← contMDiffAt_subtype_iff …]` flips the whole M-goal to a U-subtype goal.
   - `funext`+`extZeroForm_of_mem (… z.2)` rewrites `extZeroForm` → `gU.inner z`
     on U.
   - `(χ∘val smooth).smul (metric_inner_contMDiffAt gU (frameVec_sub_cmdiffAt …) …)`.
   - `metric_inner_contMDiffAt` is applied with `(M := U)` and the U-metric `gU`;
     its tangent-section inputs are exactly `frameVec_sub_cmdiffAt`.

`hχgU_on` (deliverable): `intro x hxb; by_cases x ∈ U` → `target_hχgU_at … |>.contMDiffWithinAt`;
else χ≡0 near x (`image_eq_zero_of_notMem_tsupport`, `contMDiffWithinAt_const`).

## Integration TODO for the file owner (BumpExtend.lean is lock-held by parent)
- Insert the 3 lemmas in `namespace Geometry`.
- Replace BumpExtend line 198/199 `frameVec_contMDiffAt` → `frameVec_cmdiffAt'`.
- Replace the `hχgU`/`sorry` block (lines ~163-191) by `hχgU_on …`; final line
  `exact (hχgU_on …).add hR` (drop `.contMDiffOn`, it's already `On baseSet`).
- Use the REAL `extZeroForm`/`extZeroForm_of_mem` (defeq to scratch `extZeroForm'`).
- Benign `unusedSectionVars` warnings on `[SigmaCompactSpace U]`/`[T2Space U]` in
  `frameVec_sub_cmdiffAt` (instances live in the `letI`, not the body) — keep them
  (downstream metric typeclasses need them) or `omit … in`.

Imports: the existing three BumpExtend imports SUFFICE (SmoothMetricFromCoeff +
OpenSubtype + Riemann/Basic/Field). No new import needed —
`mpullback_vectorField_preimage`, `contMDiffAt_subtype_iff`, `tsupport` lemmas all
arrive transitively.

Verification: read-only `lake env lean` GREEN, 0 sorry, deliberate-error guard
confirmed errors surface (not false-green).
