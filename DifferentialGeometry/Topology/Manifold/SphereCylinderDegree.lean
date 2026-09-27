import DifferentialGeometry.Topology.Manifold.SphereCylinderBoundarySign

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem sphereDiffeomorphDegree_eq_of_cylinder
    (Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval) ∞)
    (f₀ f₁ : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (h₀ : ∀ v, Ψ (v, 0) = (f₀ v, 0)) (h₁ : ∀ v, Ψ (v, 1) = (f₁ v, 1)) :
    sphereDiffeomorphDegree f₀ = sphereDiffeomorphDegree f₁ := by
  classical
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hlo := det_sphereCylinderAnnulusEquiv_pos_iff_boundary_degree_one v Ψ f₀ 0 (Or.inl rfl) h₀ v
  have hhi := det_sphereCylinderAnnulusEquiv_pos_iff_boundary_degree_one v Ψ f₁ 1 (Or.inr rfl) h₁ v
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    simp
  have hconn := det_sphereCylinderAnnulusEquiv_pos_iff hrank v Ψ
    (x := sphereCylinderInclusion (v, 0)) (y := sphereCylinderInclusion (v, 1))
    (by rw [norm_sphereCylinderInclusion]; norm_num)
    (by rw [norm_sphereCylinderInclusion]; norm_num)
  have hdegree := hlo.symm.trans (hconn.trans hhi)
  have hsign := (sphereDiffeomorphDegree_eq_one_iff f₀ v).symm.trans
    (hdegree.trans (sphereDiffeomorphDegree_eq_one_iff f₁ v))
  simp only [sphereDiffeomorphDegree_eq_sign _ v, hsign]

end DifferentialGeometry.Topology.Manifold
