import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.EuclideanLocalCk

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry.Analysis.ODE

theorem exists_contDiffAt_integralCurve_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ∞} (hk : 1 ≤ k)
    {F : E → E} {a : E} {s : Set E}
    (hF : ContDiffOn ℝ k F s) (hs : s ∈ 𝓝 a) :
    ∃ Φ : E → ℝ → E,
      ContDiffAt ℝ k (fun p : E × ℝ => Φ p.1 p.2) (a, 0) ∧
      (∀ x, Φ x 0 = x) ∧
      ∀ᶠ p in 𝓝 ((a, 0) : E × ℝ),
        HasDerivAt (Φ p.1) (F (Φ p.1 p.2)) p.2 := by
  classical
  obtain ⟨U, hUs, hU, haU⟩ := _root_.mem_nhds_iff.mp hs
  obtain ⟨r, ε, hr, hε, Ψ, hΨflow, hΨ, _⟩ :=
    exists_confined_isLocalFlow_contDiffOn_of_contDiffOn hk hU (hF.mono hUs) haU
  let Φ : E → ℝ → E := fun x t =>
    if x ∈ closedBall a (r : ℝ) then Ψ (x, t) else x
  have hbox : ball a (r : ℝ) ×ˢ Ioo (-ε) ε ∈ 𝓝 ((a, 0) : E × ℝ) :=
    (isOpen_ball.prod isOpen_Ioo).mem_nhds
      ⟨mem_ball_self hr, neg_lt_zero.mpr hε, hε⟩
  have hclosed : closedBall a (r : ℝ) ×ˢ Icc (-ε) ε ∈ 𝓝 ((a, 0) : E × ℝ) :=
    mem_of_superset hbox (prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · apply (hΨ.contDiffAt hclosed).congr_of_eventuallyEq
    filter_upwards [hbox] with p hp
    simp only [Φ, ite_eq_left (ball_subset_closedBall hp.1)]
  · intro x
    by_cases hx : x ∈ closedBall a (r : ℝ)
    · simp only [Φ, ite_eq_left hx, hΨflow.apply_initial x hx]
    · simp only [Φ, ite_eq_right hx]
  · filter_upwards [hbox] with p hp
    have hx := ball_subset_closedBall hp.1
    have hd := (hΨflow.hasDerivWithinAt p.1 hx p.2
      (Ioo_subset_Icc_self hp.2)).hasDerivAt (Icc_mem_nhds hp.2.1 hp.2.2)
    simpa only [Φ, ite_eq_left hx] using hd

end DifferentialGeometry.Analysis.ODE
