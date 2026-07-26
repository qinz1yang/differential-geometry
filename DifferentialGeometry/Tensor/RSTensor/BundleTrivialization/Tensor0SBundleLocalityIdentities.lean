import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SInnerSectionContinuity
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Locality identities for the `(0,s)`-tensor bundle trivialization

For a smooth manifold `M` modelled on `(E, H)` with model `I`, and a base point
`b₀ : M`, this file proves that on the locality neighbourhood of `b₀` — i.e.
where `chartAt H b = chartAt H b₀` — the inverse and forward continuous-linear
maps of the trivialization of the `(0, s)`-tensor bundle at `b₀`, evaluated at
`b`, are the identity.

These identities are the multilinear-bundle counterparts of the corresponding
tangent-bundle identities
(`Bundle.Trivialization.symmL_model_space`-style results lifted to the locality
neighbourhood via `TangentBundle.symmL_trivializationAt_eq_core` and the
`tangentBundleCore.coordChange_self` step). The reduction goes through the
explicit multilinear-bundle inverse-trivialization formula
`Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap` and its
forward analogue (proved here as
`triv_continuousLinearMapAt_eq_compContinuousLinearMap`), followed by the
tangent-bundle locality identities.

## Strategy

The trivialization of the `(0, s)`-tensor bundle at `b₀` is built from the
trivialization of the tangent bundle at `b₀` via Mathlib's
`Bundle.continuousMultilinearMap` construction. The inverse of the tensor-bundle
trivialization precomposes each input slot with the tangent-bundle's forward map
`(triv_E b₀).continuousLinearMapAt ℝ b`. The forward direction symmetrically
precomposes with `(triv_E b₀).symmL ℝ b`.

On the locality neighbourhood of `b₀`, both `(triv_E b₀).continuousLinearMapAt ℝ b`
and `(triv_E b₀).symmL ℝ b` are the identity. Precomposing a continuous
multilinear map slot-wise with the identity returns the map unchanged.

## Main results

* `triv_continuousLinearMapAt_eq_compContinuousLinearMap` — explicit forward
  formula for the multilinear-bundle trivialization, mirroring the project-internal
  `triv_symmL_eq_compContinuousLinearMap`.
* `tensor0S_trivAt_symmL_eq_one_on_locality` — `(triv_T₀ b₀).symmL ℝ b = 1` on
  the locality neighbourhood of `b₀`.
* `tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality` —
  `(triv_T₀ b₀).continuousLinearMapAt ℝ b = 1` on the locality neighbourhood of
  `b₀`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Tensor

open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Step 1: tangent-bundle locality identities (project-internal restatements) -/

/-- If `chartAt H b = chartAt H b₀`, the corresponding `achart` values agree
as subtypes. -/
private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ :=
  Subtype.ext h_chart

/-- On the locality neighbourhood of `b₀`, the inverse trivialization of the
tangent bundle centred at `b₀` evaluated at `b` is the identity. -/
private lemma tangent_trivb₀_symmL_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

/-- On the locality neighbourhood of `b₀`, the forward trivialization of the
tangent bundle centred at `b₀` evaluated at `b` is the identity. -/
private lemma tangent_trivb₀_clmAt_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

/-! ## Step 2: tangent-bundle trivialization base set identification -/

/-- The trivialization at `b₀` of the tangent bundle has base set equal to
`(chartAt H b₀).source`. -/
private lemma tangent_trivializationAt_baseSet (b₀ : M) :
    (trivializationAt E (TangentSpace I) b₀).baseSet = (chartAt H b₀).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀

/-! ## Step 3: forward-trivialization formula for the multilinear bundle

The project-internal lemma
`Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap`
provides the inverse-trivialization formula. Here we record the symmetric forward
formula, mirroring its proof structure. -/

/-- Forward formula for the multilinear-bundle trivialization. The forward
trivialization at `b₀` evaluated at `b ∈ baseSet`, applied to a fiber element `T`,
equals `T.compContinuousLinearMap (fun _ => (triv_E b₀).symmL ℝ b)`. -/
theorem triv_continuousLinearMapAt_eq_compContinuousLinearMap
    {s : ℕ} (b₀ b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet)
    (T : Bundle.continuousMultilinearMap ℝ s E (TangentSpace I) b) :
    ((trivializationAt
        (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
          ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      T.compContinuousLinearMap
        (fun _ : Fin s => (trivializationAt E (TangentSpace I) b₀).symmL ℝ b) := by
  set e := trivializationAt
    (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀ with he_def
  have hbase : b ∈ e.baseSet := hb

  have h_cLMA : (e.continuousLinearMapAt ℝ b T :
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (e ⟨b, T⟩).2 := by
    have h := congrFun (e.coe_linearMapAt_of_mem (R := ℝ) hbase) T
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply] using h
  rw [h_cLMA]

  apply ContinuousMultilinearMap.ext
  intro w

  change T (fun i : Fin s => (trivializationAt E (TangentSpace I) b₀).symmL ℝ b (w i)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-! ## Step 4: identity-on-locality for the `(0, s)`-tensor bundle trivialization -/

/-! ## Point-wise locality identities

The trivialization-level inverse and forward maps `symmL` and
`continuousLinearMapAt` go between the model fiber and the bundle fiber. Because
`Tensor0SSpace` (and even `Bundle.continuousMultilinearMap`) carries its own
registered topology, AddCommMonoid, and Module instances — distinct from
Mathlib's standard `ContinuousMultilinearMap.*` instances even though the
underlying types reduce — the maps are not endomorphisms in the syntactic type
system. We therefore state the locality identities in applied (point-wise) form,
which is the natural and most usable statement. -/

/-- On the locality neighbourhood of `b₀`, the inverse trivialization of the
underlying `(0, s)`-multilinear bundle centred at `b₀` evaluated at `b`, applied
to any model-fiber element `T`, recovers `T`. -/
theorem multilinear_trivAt_symmL_apply_eq_self_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    ((trivializationAt (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).symmL ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) = T := by

  have h_base : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [tangent_trivializationAt_baseSet (I := I) b₀]
    exact h_src

  have h_clmAt_id := tangent_trivb₀_clmAt_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart h_src

  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (s := s) b₀ b h_base T]

  rw [h_clmAt_id]

  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr

/-- On the locality neighbourhood of `b₀`, the forward trivialization of the
underlying `(0, s)`-multilinear bundle centred at `b₀` evaluated at `b`, applied
to any bundle-fiber element `T`, recovers `T` (viewed as a model-fiber element
through the reducible unfolding of `Bundle.continuousMultilinearMap`). -/
theorem multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : Bundle.continuousMultilinearMap ℝ s E (TangentSpace I) b) :
    ((trivializationAt (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
          ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by

  have h_base : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [tangent_trivializationAt_baseSet (I := I) b₀]
    exact h_src

  have h_symmL_id := tangent_trivb₀_symmL_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart h_src

  rw [triv_continuousLinearMapAt_eq_compContinuousLinearMap (I := I)
    (s := s) b₀ b h_base T]
  rw [h_symmL_id]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr

/-! ## `Tensor0SSpace`-level corollaries -/

/-- On the locality neighbourhood of `b₀`, the inverse trivialization of the
`(0, s)`-tensor bundle centred at `b₀` evaluated at `b`, applied to any
model-fiber element `T`, recovers `T`. -/
theorem tensor0S_trivAt_symmL_eq_one_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : Tensor0SModel s ℝ E) :
    ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) b₀).symmL ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) = T := by

  change (trivializationAt
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).symmL ℝ b T = T
  exact multilinear_trivAt_symmL_apply_eq_self_on_locality
    (s := s) (b₀ := b₀) (b := b) (h_chart := h_chart) (h_src := h_src) (T := T)

/-- On the locality neighbourhood of `b₀`, the forward trivialization of the
`(0, s)`-tensor bundle centred at `b₀` evaluated at `b`, applied to any fiber
element `T`, recovers `T`. -/
theorem tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : Tensor0SSpace s I b) :
    ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) b₀).continuousLinearMapAt ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by

  change (trivializationAt
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
        ℝ b T = T
  exact multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (s := s) (b₀ := b₀) (b := b) (h_chart := h_chart) (h_src := h_src) (T := T)

end Tensor
end DifferentialGeometry

end
