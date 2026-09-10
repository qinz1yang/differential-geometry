import DifferentialGeometry.Topology.Manifold.SphereCylinderAnnulus
import DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree
import DifferentialGeometry.Tensor.LinearAlgebra.BoundaryBlockDeterminant
import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.BoundaryNormalDerivative
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import DifferentialGeometry.Tensor.LinearAlgebra.CoordinateLinearSquare

noncomputable section
open Set Metric Filter Topology Manifold Module
open scoped ContDiff

namespace Poincare.Topology.Manifold

private instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem det_sphereCylinderAnnulusEquiv_pos_iff_boundary_degree_one
    (fallback : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval) ∞)
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (t : unitInterval) (ht : t = 0 ∨ t = 1)
    (hface : ∀ w, Ψ (w, t) = (f w, t))
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    0 < (fderivWithin ℝ (sphereCylinderAnnulusEquiv fallback Ψ)
      {x | ‖x‖ ∈ Icc (1 : ℝ) 2} (sphereCylinderInclusion (v, t))).toLinearMap.det ↔
      sphereDiffeomorphDegree f = 1 := by
  obtain ⟨e, hv, hfv, het, he, hei⟩ := exists_smooth_planar_chart_containing_pair v (f v)
  obtain ⟨c, hcs, hcfor, _, hcinv⟩ := exists_smooth_radial_chart e het he hei
  let r : ℝ := 1 + t.1
  let a : ℝ × ℂ := (r, e v)
  let b : ℝ × ℂ := (r, e (f v))
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {x | ‖x‖ ∈ Icc (1 : ℝ) 2}
  let T : Set (ℝ × ℂ) := Icc 1 2 ×ˢ univ
  let F := sphereCylinderAnnulusEquiv fallback Ψ
  let G : ℝ × ℂ → ℝ × ℂ := c.symm ∘ F ∘ c
  let g : ℂ → ℂ := fun z ↦ e (f (e.symm z))
  have hr : r ∈ Icc (1 : ℝ) 2 := by constructor <;> dsimp [r] <;> linarith [t.2.1, t.2.2]
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
  have ha : a ∈ c.source := hcs ▸ ⟨hrpos, mem_univ _⟩
  have hb : b ∈ c.source := hcs ▸ ⟨hrpos, mem_univ _⟩
  have hca : c a = sphereCylinderInclusion (v, t) := by
    rw [hcfor]
    change r • (e.symm (e v) : EuclideanSpace ℝ (Fin 3)) = _
    rw [e.left_inv hv]
    rfl
  have hcb : c b = sphereCylinderInclusion (f v, t) := by
    rw [hcfor]
    change r • (e.symm (e (f v)) : EuclideanSpace ℝ (Fin 3)) = _
    rw [e.left_inv hfv]
    rfl
  have hFinc (w : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      F (sphereCylinderInclusion (w, t)) = sphereCylinderInclusion (f w, t) := by
    change sphereCylinderInclusion
      (Ψ (sphereCylinderProjection fallback (sphereCylinderInclusion (w, t)))) = _
    rw [sphereCylinderProjection_inclusion, hface]
  have hab : F (c a) = c b := by rw [hca, hcb, hFinc]
  have hmaps : MapsTo c T S := by
    intro q hq
    change ‖c q‖ ∈ Icc (1 : ℝ) 2
    rw [hcfor]
    simpa only [norm_smul, norm_eq_of_mem_sphere, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le zero_lt_one hq.1.1), mul_one] using hq.1
  have hcaS : c a ∈ S := hmaps ⟨hr, mem_univ _⟩
  obtain ⟨hF, hFi⟩ := contDiffOn_sphereCylinderAnnulusEquiv fallback Ψ
  let A := fderivWithin ℝ F S (c a)
  let B := (fderiv ℝ c.symm (F (c a))).comp (A.comp (fderiv ℝ c a))
  have hA : HasFDerivWithinAt F A S (c a) :=
    (hF.differentiableOn (by simp) (c a) hcaS).hasFDerivWithinAt
  have hdc : HasFDerivAt c (fderiv ℝ c a) a :=
    ((c.contMDiffOn.contDiffOn.contDiffAt (c.open_source.mem_nhds ha)).differentiableAt
      (by simp)).hasFDerivAt
  have hFc : F (c a) ∈ c.target := hab ▸ c.map_source hb
  have hdci : HasFDerivAt c.symm (fderiv ℝ c.symm (F (c a))) (F (c a)) :=
    ((c.symm.contMDiffOn.contDiffOn.contDiffAt (c.open_target.mem_nhds hFc)).differentiableAt
      (by simp)).hasFDerivAt
  have hB : HasFDerivWithinAt G B T a :=
    hdci.comp_hasFDerivWithinAt a (hA.comp a hdc.hasFDerivWithinAt hmaps)
  have hBface : ∀ z, G (r, z) = (r, g z) := by
    intro z
    have hcz : c (r, z) = sphereCylinderInclusion (e.symm z, t) := hcfor (r, z)
    change c.symm (F (c (r, z))) = _
    rw [hcz, hFinc, hcinv, norm_sphereCylinderInclusion]
    change (r, e (sphereDirection (e.symm 0)
      (r • (f (e.symm z) : EuclideanSpace ℝ (Fin 3))))) = _
    rw [sphereDirection_pos_smul _ _ hrpos]
  have hbound : ∀ q ∈ T, (G q).1 ∈ Icc (1 : ℝ) 2 := by
    intro q hq
    change (c.symm (F (c q))).1 ∈ Icc (1 : ℝ) 2
    rw [hcinv]
    exact F.map_source (hmaps hq)
  have hnormal : 0 ≤ (B (1, 0)).1 := by
    rcases ht with ht | ht
    · have hrone : r = 1 := by simp [r, ht]
      have hB' : HasFDerivWithinAt G B T (1, e v) := by simpa only [a, hrone] using hB
      exact Poincare.Analysis.normal_coefficient_nonneg_at_lower (by norm_num)
        G B (e v) hB' hbound (by simpa only [hrone] using congrArg Prod.fst (hBface (e v)))
    · have hrtwo : r = 2 := by norm_num [r, ht]
      have hB' : HasFDerivWithinAt G B T (2, e v) := by simpa only [a, hrtwo] using hB
      exact Poincare.Analysis.normal_coefficient_nonneg_at_upper (by norm_num)
        G B (e v) hB' hbound (by simpa only [hrtwo] using congrArg Prod.fst (hBface (e v)))
  have hi : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm := contMDiffOn_univ.mp (het ▸ hei)
  let U : Set ℂ := (fun z ↦ f (e.symm z)) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (f.continuous.comp hi.continuous)
  have hevU : e v ∈ U := by
    change f (e.symm (e v)) ∈ e.source
    rwa [e.left_inv hv]
  have hg : ContDiffOn ℝ ∞ g U :=
    (he.comp (f.contMDiff.comp hi).contMDiffOn (fun _ hz ↦ hz)).contDiffOn
  have hga : HasFDerivAt g (fderiv ℝ g (e v)) (e v) :=
    ((hg.contDiffAt (hU.mem_nhds hevU)).differentiableAt (by simp)).hasFDerivAt
  have hhoriz := Poincare.Analysis.horizontal_derivative_of_face_eq
    hr G g B (fderiv ℝ g (e v)) (e v) hB hga hBface
  have hAnz : A.toLinearMap.det ≠ 0 :=
    Poincare.Analysis.det_fderivWithin_ne_zero_of_inverse
      (Poincare.Analysis.uniqueDiffOn_norm_band zero_lt_one (by norm_num))
      F F.symm hF hFi F.mapsTo (fun _ hx ↦ F.left_inv hx) hcaS
  have hAsurj : Function.Surjective A := by
    intro y
    obtain ⟨x, hx⟩ := (A.toContinuousLinearEquivOfDetNeZero hAnz).surjective y
    exact ⟨x, (A.toContinuousLinearEquivOfDetNeZero_apply hAnz x).symm.trans hx⟩
  have hBsurj : Function.Surjective B :=
    (Poincare.Analysis.bijective_fderiv_of_partialDiffeomorph c.symm hFc).2.comp
      (hAsurj.comp (Poincare.Analysis.bijective_fderiv_of_partialDiffeomorph c ha).2)
  have hBtangent := Poincare.Analysis.det_pos_iff_horizontal_of_surjective
    B.toLinearMap (fderiv ℝ g (e v)).toLinearMap hhoriz hBsurj hnormal
  have hinv : (fderiv ℝ c b).comp (fderiv ℝ c.symm (F (c a))) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
    have h := Poincare.Analysis.fderiv_symm_comp_fderiv_of_partialDiffeomorph
      c.symm (c.map_source hb)
    change (fderiv ℝ c (c.symm (c b))).comp (fderiv ℝ c.symm (c b)) = _ at h
    have hleft : c.symm (c b) = b := c.left_inv hb
    rw [hleft] at h
    rw [hab]
    exact h
  have hsquare : A.comp (fderiv ℝ c a) = (fderiv ℝ c b).comp B := by
    dsimp only [B]
    rw [← ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.id_comp]
  have hconn : IsPreconnected c.source := by
    rw [hcs]
    exact (convex_Ioi (0 : ℝ)).isPreconnected.prod convex_univ.isPreconnected
  let L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ℝ × ℂ :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  have hsign := Poincare.Analysis.det_pos_iff_of_coordinate_linear_square L c hconn ha hb A B hsquare
  have hchart := (sphereDiffeomorphDegree_eq_one_iff f v).trans
    (det_radial_pos_iff_det_chart_pos e het he hei f v hv hfv)
  have hresult := hsign.trans (hBtangent.trans hchart.symm)
  dsimp only [A] at hresult
  rwa [hca] at hresult

end Poincare.Topology.Manifold
