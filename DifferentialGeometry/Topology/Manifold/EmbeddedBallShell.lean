import DifferentialGeometry.Topology.Manifold.EmbeddedBallStraightening
import DifferentialGeometry.Topology.Manifold.EllipsoidShell

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem preimage_eq_of_equiv_fix_compl {X : Type*} (f : X ≃ X) {K S : Set X}
    (hKS : K ⊆ S) (hfix : ∀ x, x ∉ K → f x = x) : f ⁻¹' S = S := by
  ext x
  by_cases hxK : x ∈ K
  · have hfxK : f x ∈ K := by
      by_contra h
      have he : f x = x := f.injective (hfix _ h)
      exact h (he.symm ▸ hxK)
    exact iff_of_true (hKS hfxK) (hKS hxK)
  · simp only [mem_preimage, hfix x hxK]

theorem exists_smooth_embeddedBallShell_parametrization
    {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r R : ℝ} (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ φ.source)
    (hsub : φ '' closedBall 0 r ⊆ ball 0 R) (v : sphere (0 : E) 1) :
    ∃ e : PartialEquiv (sphere (0 : E) 1 × unitInterval) E,
      e.source = univ ∧ e.target = closedBall 0 R \ φ '' ball 0 r ∧
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ e ∧
      ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod (𝓡∂ 1)) ∞ e.symm e.target := by
  obtain ⟨A, ε, F, _, hε, _, hformula, K, hK, hKB, hfix⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ hr hrs isOpen_ball hsub
  let B : E ≃L[ℝ] E := (Units.mk0 ε hε.ne') • A
  have hBe (x : E) : B x = ε • A x := rfl
  have hpre (S : Set E) (hKS : K ⊆ S) : F ⁻¹' S = S :=
    preimage_eq_of_equiv_fix_compl F.toEquiv hKS (fun x hx ↦ (hfix x hx).1)
  have hpreB : F ⁻¹' ball 0 R = ball 0 R := hpre _ hKB
  have hpreC : F ⁻¹' closedBall 0 R = closedBall 0 R := hpre _ (hKB.trans ball_subset_closedBall)
  have hsubB : (fun x ↦ B x + φ 0) '' closedBall 0 r ⊆ ball 0 R := by
    rintro y ⟨x, hx, rfl⟩
    change B x + φ 0 ∈ ball 0 R
    rw [hBe, ← hformula x hx]
    exact (show F (φ x) ∈ ball 0 R ↔ φ x ∈ ball 0 R from Set.ext_iff.mp hpreB (φ x)).mpr
      (hsub ⟨x, hx, rfl⟩)
  have hp : ‖φ 0‖ < R := mem_ball_zero_iff.mp (hsub ⟨0, mem_closedBall_self hr.le, rfl⟩)
  obtain ⟨e, hes, het, he, hei⟩ :=
    exists_smooth_ellipsoidShell_parametrization (n := n) B (φ 0) hr hp hsubB v
  have hpreinner : F ⁻¹' ((fun x ↦ B x + φ 0) '' ball 0 r) = φ '' ball 0 r := by
    ext y
    constructor
    · rintro ⟨x, hx, heq⟩
      refine ⟨x, hx, F.injective ?_⟩
      exact (hformula x (ball_subset_closedBall hx)).trans ((hBe x ▸ heq))
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      exact (hBe x ▸ hformula x (ball_subset_closedBall hx)).symm
  let d := e.transEquiv F.symm.toEquiv
  have hdt : d.target = closedBall 0 R \ φ '' ball 0 r := by
    change F ⁻¹' e.target = _
    rw [het, preimage_sdiff, hpreC, hpreinner]
  refine ⟨d, hes, hdt, F.symm.contMDiff.comp he, ?_⟩
  exact hei.comp F.contMDiff.contMDiffOn (fun _ hx ↦ hx)

end Poincare.Topology.Manifold
