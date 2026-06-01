import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.Tensor0SBundleLocalityIdentities
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Hom

/-!
# Locality identities for the `(r, s)`-tensor Hom-bundle trivialization

For a smooth manifold `M` modelled on `(E, H)` with model `I`, and a base point
`b₀ : M`, this file lifts the `(0, s)`-tensor bundle locality identities (proved
in `Tensor0SBundleLocalityIdentities`) to the `(r, s)`-tensor Hom-bundle.

The Hom-bundle trivialization is built via `Bundle.ContinuousLinearMap.vectorBundle`
out of the `(0, r)`- and `(0, s)`-tensor bundle trivializations. The Mathlib
formula `Bundle.Pretrivialization.continuousLinearMap_symm_apply'` reduces the
Hom-bundle's `symm` map to a sandwich
`(e_s.symmL b).comp (D.comp (e_r.continuousLinearMapAt b))`,
and there is a symmetric formula for the forward direction
`continuousLinearMap_apply`. On the locality neighbourhood of `b₀` (where
`chartAt H b = chartAt H b₀` and `b ∈ (chartAt H b₀).source`), the `(0, r)` and
`(0, s)` bundle's `symmL` and `continuousLinearMapAt` act as the identity on
applied form (Sub-A). Composing two identity sandwiches recovers the input.

## Main results

* `tensorRS_trivAt_symmL_apply_eq_self_on_locality` — applied to a fibre input,
  the `symmL` of the Hom-bundle trivialization at `b₀` evaluated at `b` returns
  `D` (as a continuous linear map between the underlying model fibres).
* `tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality` — the
  symmetric forward identity.
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

/-! ## Inverse-trivialization locality identity for the `(r, s)`-Hom-bundle -/

/-- On the locality neighbourhood of `b₀`, the inverse trivialization of the
`(r, s)`-Hom-bundle centred at `b₀` evaluated at `b`, applied to a model-fibre
element `D : TensorRSModel r s ℝ E` and then to a `(0, r)` fibre input
`α_input : Tensor0SSpace r I b`, recovers `D α_input` — i.e. the trivialization's
`symmL` acts as the canonical identification `TensorRSModel ≃ TensorRSSpace b`
on the locality neighbourhood.

We state the result in the natural applied form
`(symmL ℝ b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) α_input = D α_input`
since the two sides have distinct ambient types (the Hom-bundle fibre uses the
bundle topology on `Tensor0SSpace`, while the model fibre `TensorRSModel` uses the
norm topology). They agree as functions on the underlying carrier by
`Tensor0SSpace`'s `tensor0SSpace_topology_eq` identification. -/
theorem tensorRS_trivAt_symmL_apply_eq_self_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (D : TensorRSModel r s ℝ E)
    (α_input : Tensor0SSpace r I b) :
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).symmL ℝ b D) α_input =
      (show Tensor0SSpace s I b from
        D ((show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input))) := by
  classical
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) b₀ with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) b₀ with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) b₀ with hes_def
  -- Tangent-bundle base set at `b₀` equals `(chartAt H b₀).source`.
  have hb_tan : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact h_src
  -- Base sets of the (0, r) and (0, s) bundle trivializations at b₀ both contain b.
  have hb_r : b ∈ er.baseSet := hb_tan
  have hb_s : b ∈ es.baseSet := hb_tan
  -- Base set of the Hom-bundle trivialization at b₀ contains b.
  have hb_RS : b ∈ eRS.baseSet := ⟨hb_r, hb_s⟩
  -- Reduce the Hom-bundle `symmL` to the sandwich of factor maps.
  have hHomSymm : (eRS.symmL ℝ b D :
      Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (es.symmL ℝ b).comp (D.comp (er.continuousLinearMapAt ℝ b)) := by
    have h := _root_.Bundle.Pretrivialization.continuousLinearMap_symm_apply'
      (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (F₂ := Tensor0SModel s ℝ E)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (e₁ := er) (e₂ := es) (b := b) hb_RS D
    -- `eRS.symmL b D = eRS.symm b D` (Trivialization-level `symmL` coerces to `symm`).
    change (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) = _
    -- The Hom-bundle trivialization at b₀ unfolds to the Pretrivialization-level
    -- `continuousLinearMap` formula at the (0, r), (0, s) factor trivializations.
    rw [show (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
          ((_root_.Bundle.Pretrivialization.continuousLinearMap (𝕜₁ := ℝ) (𝕜₂ := ℝ)
            (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
            (E₁ := fun y : M => Tensor0SSpace r I y)
            (F₂ := Tensor0SModel s ℝ E)
            (E₂ := fun y : M => Tensor0SSpace s I y)
            er es).symm b D) from rfl]
    exact h
  -- Now compute the application of the symmL on α_input via the sandwich.
  rw [hHomSymm]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- Apply Sub-A: the (0, r) forward map acts as the identity on locality.
  have h_r := tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality
    (I := I) (M := M) (s := r) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src) (T := α_input)
  -- Apply Sub-A: the (0, s) inverse map acts as the identity on locality.
  have h_s := tensor0S_trivAt_symmL_eq_one_on_locality
    (I := I) (M := M) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src)
    (T := D ((show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input)))
  -- Rewrite the inner `er.continuousLinearMapAt ℝ b α_input` to the model-fibre value.
  have h_r_id :
      (er.continuousLinearMapAt ℝ b α_input :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input) := h_r
  -- Rewrite the outer `es.symmL ℝ b (D (...))` to its bundle-fibre value.
  have h_s_id :
      (es.symmL ℝ b
          (D (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
        D (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input)) := h_s
  -- Conclude by combining the two identities. Both LHS and RHS, viewed as model-fibre
  -- elements, are equal by `h_s_id`; this propagates back to the bundle-fibre view.
  have h_inner :
      D (er.continuousLinearMapAt ℝ b α_input) =
      D (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input) := by
    exact congrArg D h_r_id
  rw [h_inner]
  -- Now the LHS is `es.symmL ℝ b (D (model α_input))` as an element of
  -- `Tensor0SSpace s I b`, and the RHS is `D (model α_input)` as an element of
  -- `Tensor0SSpace s I b`. Their underlying `ContinuousMultilinearMap`-views agree
  -- by `h_s_id`; this is propositional equality at the `Tensor0SSpace` level by
  -- the type-eq through `tensor0SSpace_topology_eq`.
  exact h_s_id

/-! ## Forward-trivialization locality identity for the `(r, s)`-Hom-bundle -/

/-- On the locality neighbourhood of `b₀`, the forward trivialization of the
`(r, s)`-Hom-bundle centred at `b₀` evaluated at `b`, applied to a fibre element
`T : TensorRSSpace r s I b` and then to a model `(0, r)` input
`D_α : Tensor0SModel r ℝ E`, recovers `T D_α` (as a `(0, s)` value). -/
theorem tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : TensorRSSpace r s I b)
    (D_α : Tensor0SModel r ℝ E) :
    (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E from
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T) D_α =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (show Tensor0SSpace r I b from D_α)) := by
  classical
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) b₀ with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) b₀ with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) b₀ with hes_def
  -- Tangent-bundle base set at `b₀` equals `(chartAt H b₀).source`.
  have hb_tan : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact h_src
  have hb_r : b ∈ er.baseSet := hb_tan
  have hb_s : b ∈ es.baseSet := hb_tan
  have hb_RS : b ∈ eRS.baseSet := ⟨hb_r, hb_s⟩
  -- Reduce `eRS.continuousLinearMapAt ℝ b T` to the sandwich
  -- `(es.continuousLinearMapAt ℝ b).comp(T.comp(er.symmL ℝ b))`.
  have hcoeRS := eRS.coe_linearMapAt_of_mem (R := ℝ) hb_RS
  -- `eRS.continuousLinearMapAt ℝ b T = (eRS ⟨b, T⟩).2` on the base set.
  have hForward : (eRS.continuousLinearMapAt ℝ b T :
      Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) =
      (es.continuousLinearMapAt ℝ b).comp
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T).comp
          (er.symmL ℝ b)) := by
    have h := congrFun hcoeRS T
    -- `linearMapAt = continuousLinearMapAt` as functions on the base set.
    have h_cLMA : (eRS.continuousLinearMapAt ℝ b T :
        Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) =
        (eRS ⟨b, T⟩).2 := by
      simpa [Bundle.Trivialization.continuousLinearMapAt_apply] using h
    rw [h_cLMA]
    -- The Hom-bundle pretrivialization formula reads off the sandwich.
    rfl
  rw [hForward]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- Apply Sub-A: the (0, r) inverse map acts as the identity on locality.
  have h_r := tensor0S_trivAt_symmL_eq_one_on_locality
    (I := I) (M := M) (s := r) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src) (T := D_α)
  -- Apply Sub-A: the (0, s) forward map acts as the identity on locality.
  have h_s := tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality
    (I := I) (M := M) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src)
    (T :=
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
        (show Tensor0SSpace r I b from D_α))
  -- Rewrite the inner `er.symmL ℝ b D_α` to the bundle-fibre value `D_α`.
  have h_r_id :
      (er.symmL ℝ b D_α :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from
        (show Tensor0SSpace r I b from D_α)) := h_r
  -- Rewrite the outer `es.continuousLinearMapAt ℝ b (T (...))` to the model value.
  have h_s_id :
      (es.continuousLinearMapAt ℝ b
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
            (show Tensor0SSpace r I b from D_α)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (show Tensor0SSpace r I b from D_α))) := h_s
  have h_inner :
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (er.symmL ℝ b D_α) =
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (show Tensor0SSpace r I b from D_α) :=
    congrArg (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T) h_r_id
  rw [h_inner]
  exact h_s_id

end Tensor
end DifferentialGeometry

end
