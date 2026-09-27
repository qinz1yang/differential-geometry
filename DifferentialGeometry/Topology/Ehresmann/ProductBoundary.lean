import DifferentialGeometry.Topology.Ehresmann.ProductHeight
import DifferentialGeometry.Geometry.Boundary.SmoothFactorization

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_boundaryLevel_diffeomorph_of_interval_product
    {E F H G W B : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace W] [ChartedSpace H W]
    [TopologicalSpace B] [ChartedSpace G B]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ W]
    [BoundarylessManifold J B]
    (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞)
    (u : W → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ w, I.IsBoundaryPoint w → u w = a ∨ u w = b)
    (hcoord : ∀ p : B × unitInterval, u (D p) = a + (b - a) * (p.2 : ℝ)) :
    ∃ η : B ≃ₘ⟮J, hI.boundaryI⟯ boundaryLevel u a b hab hu hboundary,
      ∀ p, (η p).1.1 = D (p, 0) := by
  let L := boundaryLevel u a b hab hu hboundary
  have hzero (p : B) : I.IsBoundaryPoint (D (p, 0)) := by
    apply ((D.isLocalDiffeomorph (p, 0)).isBoundaryPoint_iff (by decide)).mp
    change (p, (0 : unitInterval)) ∈ (J.prod (𝓡∂ 1)).boundary (B × unitInterval)
    rw [J.boundary_of_boundaryless_left, boundary_Icc]
    exact ⟨mem_univ _, Or.inl rfl⟩
  have hvalue (p : B) : u (D (p, 0)) = a := by simpa using hcoord (p, 0)
  let forward : B → L := fun p ↦ ⟨⟨D (p, 0), hzero p⟩, hvalue p⟩
  let back : L → B := fun x ↦ (D.symm x.1.1).1
  have hforward : ContMDiff J hI.boundaryI ∞ forward := by
    apply (contMDiff_boundaryLevelInclusion_comp_iff u a b hab hu hboundary).mp
    exact D.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hback : ContMDiff hI.boundaryI J ∞ back :=
    contMDiff_fst.comp (D.symm.contMDiff.comp
      (contMDiff_boundaryLevelInclusion u a b hab hu hboundary))
  have hleft (p : B) : back (forward p) = p := by
    change (D.symm (D (p, 0))).1 = p
    rw [D.symm_apply_apply]
  have hright (x : L) : forward (back x) = x := by
    have hx := hcoord (D.symm x.1.1)
    rw [D.apply_symm_apply, x.2] at hx
    have hsecond : (D.symm x.1.1).2 = 0 := by
      apply Subtype.ext
      change ((D.symm x.1.1).2 : ℝ) = 0
      rcases mul_eq_zero.mp (show (b - a) * ((D.symm x.1.1).2 : ℝ) = 0 by linarith) with h | h
      · exact False.elim (hab (sub_eq_zero.mp h).symm)
      · exact h
    apply Subtype.ext
    apply Subtype.ext
    change D ((D.symm x.1.1).1, 0) = x.1.1
    rw [← hsecond]
    exact D.apply_symm_apply x.1.1
  exact ⟨⟨⟨forward, back, hleft, hright⟩, hforward, hback⟩, fun _ ↦ rfl⟩

end DifferentialGeometry.Topology.Ehresmann
