import DifferentialGeometry.Topology.Manifold.CylinderCollar.Germ
import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialContraction
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SupportedExtension

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private def sphereProductLineDiffeomorph (d : ℝ ≃ₘ[ℝ] ℝ) :
    SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder :=
  (Diffeomorph.refl (𝓡 2) S2 ∞).prodCongr d

theorem exists_supported_cylinder_compression {r R ε : ℝ}
    (hr : 0 < r) (hrR : r < R) (hε : 0 < ε) :
    ∃ C : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ p : SphereCylinder, |p.2| ≤ r → |(C p).2| < ε) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioo (-R) R ∧
        EqOn C id Kᶜ ∧ EqOn C.symm id Kᶜ := by
  let R' := (r + R) / 2
  have hrR' : r < R' := by dsimp only [R']; linarith
  have hR'R : R' < R := by dsimp only [R']; linarith
  obtain ⟨D, _, _, _, _, hshrink, hfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_flow_contracting_closedBall (E := ℝ) hr hrR'
  let T := max 0 (Real.log (r / ε)) + 1
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hsmall : Real.exp (-T) * r < ε := by
    have hlog : Real.log (r / ε) < T := by dsimp only [T]; linarith [le_max_right 0 (Real.log (r / ε))]
    have hexp : r / ε < Real.exp T := by rwa [← Real.log_lt_iff_lt_exp (div_pos hr hε)]
    rw [Real.exp_neg]
    apply (inv_mul_lt_iff₀ (Real.exp_pos T)).mpr
    nlinarith [(div_lt_iff₀ hε).mp hexp]
  let C := sphereProductLineDiffeomorph (D T)
  refine ⟨C, ?_, univ ×ˢ Icc (-R') R', isCompact_univ.prod isCompact_Icc,
    ?_, ?_, ?_⟩
  · intro p hp
    change |D T p.2| < ε
    rw [hshrink T p.2 hT (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hp),
      smul_eq_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans_lt hsmall
  · rintro p ⟨_, hp⟩
    exact ⟨mem_univ _, by linarith [hp.1], by linarith [hp.2]⟩
  · intro p hp
    have hnot : p.2 ∉ closedBall (0 : ℝ) R' := by
      intro hx
      exact hp ⟨mem_univ _, (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).1,
        (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).2⟩
    exact Prod.ext rfl (hfix T p.2 hnot).1
  · intro p hp
    have hnot : p.2 ∉ closedBall (0 : ℝ) R' := by
      intro hx
      exact hp ⟨mem_univ _, (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).1,
        (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).2⟩
    exact Prod.ext rfl (hfix T p.2 hnot).2

end DifferentialGeometry.Topology.Manifold
