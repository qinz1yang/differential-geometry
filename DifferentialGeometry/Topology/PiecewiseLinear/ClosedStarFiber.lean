import DifferentialGeometry.Topology.PiecewiseLinear.ConeFiber
import DifferentialGeometry.Topology.PiecewiseLinear.HeightLevelLink
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLBall_closedStar_inter_fiber {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
    (ℓ : E →ₗ[ℝ] ℝ) (hD : IsPLBall (n + 1) (K.space ∩ {x | ℓ x = ℓ p})) :
    IsPLBall (n + 1) (closedStar K p ∩ {x | ℓ x = ℓ p}) := by
  classical
  obtain ⟨F, f, hFfin, hFspace, hpF, hf⟩ := exists_isPLHomeomorphOn_geometricLink_fiber K hp ℓ
  let _ : Finite F.faces := hFfin.to_subtype
  have hF : IsPLBall (n + 1) F.space := hFspace.symm ▸ hD
  let B := SimplicialComplex.geometricLink K {p}
  let _ : Finite B.faces :=
    ((Set.toFinite K.faces).subset (SimplicialComplex.geometricLink_le K {p})).to_subtype
  have hB : IsPLSphere n (B.space ∩ {x | ℓ x = ℓ p}) ∨
      IsPLBall n (B.space ∩ {x | ℓ x = ℓ p}) :=
    (isPLSphere_or_isPLBall_geometricLink_of_isPLBall F hF hpF).imp
      (fun h => h.of_isPLHomeomorphOn hf) (fun h => h.of_isPLHomeomorphOn hf)
  have hpoly : IsPolyhedron (B.space ∩ {x | ℓ x = ℓ p}) :=
    hB.elim (fun h => h.isPolyhedron) (fun h => h.isPolyhedron)
  obtain ⟨L, hL, hLfin, hLspace, hcone⟩ :=
    (isConeBase_geometricLink K (p := p)).exists_coneComplex_inter_fiber ℓ hpoly
  let _ : Finite L.faces := hLfin.to_subtype
  rw [closedStar_eq_coneComplex_space K hp, ← hcone]
  rcases hB with hsphere | hball
  · exact hL.isPLBall_of_isPLSphere (hLspace.symm ▸ hsphere)
  · exact hL.isPLBall_of_isPLBall (hLspace.symm ▸ hball)

end DifferentialGeometry.Topology.PiecewiseLinear
