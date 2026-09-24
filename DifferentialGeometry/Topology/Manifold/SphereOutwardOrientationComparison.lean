import DifferentialGeometry.Topology.Manifold.SphereOutwardOrientation
import DifferentialGeometry.Topology.Manifold.SphereOutwardFrameDictionary

noncomputable section

open Metric Module
open scoped Manifold

namespace DifferentialGeometry.Topology

private instance sphere_euclidean_finrank (n : ℕ) :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private theorem sphere_outward_form_apply (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    ((((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation).volumeForm.curryLeft
      (x : EuclideanSpace ℝ (Fin (n + 1)))).compLinearMap
      (mvfderiv (𝓡 n) ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        EuclideanSpace ℝ (Fin (n + 1))) x).toLinearMap) b =
      DifferentialGeometry.sphereOutwardDeterminant n x b := by
  rw [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
    ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation).volumeForm_robust
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) rfl]
  rw [DifferentialGeometry.sphereOutwardDeterminant_eq_basisDet_frame]
  rfl

theorem sphereOutwardOrientation_euclidean (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereOutwardOrientation n (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation x =
      DifferentialGeometry.sphereOutwardOrientation n x := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let f := ((((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation).volumeForm.curryLeft
    (x : EuclideanSpace ℝ (Fin (n + 1)))).compLinearMap
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      EuclideanSpace ℝ (Fin (n + 1))) x).toLinearMap)
  have hf : f ≠ 0 := sphere_outward_volumeForm_ne_zero n _ x
  have hfb : f b = DifferentialGeometry.sphereOutwardDeterminant n x b :=
    sphere_outward_form_apply n x b
  have hfb0 : f b ≠ 0 := (AlternatingMap.map_basis_ne_zero_iff b f).mpr hf
  change rayOfNeZero ℝ f hf = _
  unfold DifferentialGeometry.sphereOutwardOrientation
  change rayOfNeZero ℝ f hf = if 0 < DifferentialGeometry.sphereOutwardDeterminant n x b then
    b.orientation else -b.orientation
  split_ifs with hpos
  · change rayOfNeZero ℝ f hf = rayOfNeZero ℝ b.det b.det_ne_zero
    apply (ray_eq_iff _ _).mpr
    rw [f.eq_smul_basis_det b]
    exact (sameRay_smul_left_iff_of_ne b.det_ne_zero hfb0).mpr (hfb.symm ▸ hpos)
  · rw [Basis.orientation, neg_rayOfNeZero]
    apply (ray_eq_iff _ _).mpr
    rw [f.eq_smul_basis_det b]
    apply (sameRay_neg_smul_left_iff_of_ne b.det_ne_zero hfb0).mpr
    have hnonpos : f b ≤ 0 := le_of_not_gt (hfb.symm ▸ hpos)
    exact lt_of_le_of_ne hnonpos hfb0

end DifferentialGeometry.Topology
