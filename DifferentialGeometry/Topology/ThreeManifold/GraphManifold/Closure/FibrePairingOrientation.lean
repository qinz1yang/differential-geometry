import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
Actual positive inclusions preserve the opposite boundary orientations of retained half collars.
-/

set_option autoImplicit false

noncomputable section

open Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem fibreOrientation_map_trans {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup H] [Module ℝ H] (L : E ≃ₗ[ℝ] F) (R : F ≃ₗ[ℝ] H)
    (o : Orientation ℝ E (Fin 3)) :
    Orientation.map (Fin 3) (L.trans R) o =
      Orientation.map (Fin 3) R (Orientation.map (Fin 3) L o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

set_option backward.isDefEq.respectTransparency false in
theorem reversesBoundaryOrientation_of_positiveInclusion
    {C K : CompactCarrier.{u}} (ι : K.Carrier → C.Carrier)
    (hsm : ContMDiff K.model C.model ∞ ι)
    (hbij : ∀ x, Bijective (mfderiv K.model C.model ι x))
    (ho : ∀ x, Orientation.map (Fin 3)
      (Manifold.differentialEquivOfBijective K.model C.model ι hbij x).toLinearEquiv
      (K.orientation.orientation x) = C.orientation.orientation (ι x))
    (l r : PartialDiffeomorph halfCollarModel K.model
      (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (h : ReversesBoundaryOrientation C (ι ∘ l) (ι ∘ r)) :
    ReversesBoundaryOrientation K l r := by
  intro t
  let p : Torus × EuclideanHalfSpace 1 := (t, halfZero)
  have hpl : p ∈ l.source := hl.symm ▸ zero_mem_halfCollarSource t
  have hpr : p ∈ r.source := hr.symm ▸ zero_mem_halfCollarSource t
  have hlD := l.isLocalDiffeomorphAt halfCollarModel K.model ∞ hpl
  have hrD := r.isLocalDiffeomorphAt halfCollarModel K.model ∞ hpr
  let L := (hlD.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let R := (hrD.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let D : (x : K.Carrier) → TangentSpace K.model x ≃ₗ[ℝ]
      TangentSpace C.model (ι x) := fun x =>
    (Manifold.differentialEquivOfBijective K.model C.model ι hbij x).toLinearEquiv
  obtain ⟨L', R', hL, hR, hLR⟩ := h t
  have heL : L.trans (D (l p)) = L' := by
    apply LinearEquiv.ext
    intro v
    change mfderiv K.model C.model ι (l p)
      (mfderiv halfCollarModel K.model l p v) = L' v
    exact (DFunLike.congr_fun (mfderiv_comp p (hsm.mdifferentiable (by simp) _)
      (l.mdifferentiableAt (by simp) hpl)) v).symm.trans (hL v).symm
  have heR : R.trans (D (r p)) = R' := by
    apply LinearEquiv.ext
    intro v
    change mfderiv K.model C.model ι (r p)
      (mfderiv halfCollarModel K.model r p v) = R' v
    exact (DFunLike.congr_fun (mfderiv_comp p (hsm.mdifferentiable (by simp) _)
      (r.mdifferentiableAt (by simp) hpr)) v).symm.trans (hR v).symm
  have hLo : Orientation.map (Fin 3) L'.symm
      (C.orientation.orientation (ι (l p))) =
      Orientation.map (Fin 3) L.symm (K.orientation.orientation (l p)) := by
    rw [← ho, ← heL, LinearEquiv.trans_symm, fibreOrientation_map_trans]
    exact congrArg (Orientation.map (Fin 3) L.symm)
      ((Orientation.map (Fin 3) (D (l p))).symm_apply_apply _)
  have hRo : Orientation.map (Fin 3) R'.symm
      (C.orientation.orientation (ι (r p))) =
      Orientation.map (Fin 3) R.symm (K.orientation.orientation (r p)) := by
    rw [← ho, ← heR, LinearEquiv.trans_symm, fibreOrientation_map_trans]
    exact congrArg (Orientation.map (Fin 3) R.symm)
      ((Orientation.map (Fin 3) (D (r p))).symm_apply_apply _)
  exact ⟨L, R, fun v => rfl, fun v => rfl, hLo.symm.trans (hLR.trans (congrArg Neg.neg hRo))⟩


set_option backward.isDefEq.respectTransparency false in
theorem reversesBoundaryOrientation_congrOn {C : CompactCarrier.{u}}
    {l r l' r' : Torus × EuclideanHalfSpace 1 → C.Carrier}
    (h : ReversesBoundaryOrientation C l r)
    (hl : Set.EqOn l l' halfCollarSource) (hr : Set.EqOn r r' halfCollarSource) :
    ReversesBoundaryOrientation C l' r' := by
  intro t
  obtain ⟨L, R, hL, hR, ho⟩ := h t
  have hp := zero_mem_halfCollarSource t
  have hopen : IsOpen halfCollarSource := by
    exact isOpen_lt ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  have heL : l =ᶠ[𝓝 (t, halfZero)] l' :=
    Filter.eventually_of_mem (hopen.mem_nhds hp) hl
  have heR : r =ᶠ[𝓝 (t, halfZero)] r' :=
    Filter.eventually_of_mem (hopen.mem_nhds hp) hr
  have hdL := Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel) (I' := C.model) heL
  have hdR := Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel) (I' := C.model) heR
  refine ⟨L, R, ?_, ?_, ?_⟩
  · intro v
    exact (hL v).trans (DFunLike.congr_fun hdL v)
  · intro v
    exact (hR v).trans (DFunLike.congr_fun hdR v)
  · rw [← hl hp, ← hr hp]
    exact ho

end GC.GraphManifold
