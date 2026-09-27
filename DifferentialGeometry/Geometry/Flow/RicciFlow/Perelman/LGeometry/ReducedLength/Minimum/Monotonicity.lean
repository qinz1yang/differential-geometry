import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.WeakBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.TimeRegularity
import DifferentialGeometry.Analysis.Calculus.UpperSupport.Monotonicity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [TopologicalSpace.MetrizableSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem antitoneOn_scaled_action_sub_dim_mul_sq_of_compact_free_endpoint_minimizers
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {b₀ b₁ : ℝ} (hb₀ : 0 < b₀)
    (hreg : Icc (T - b₁ ^ 2) T ⊆ D.regular)
    (x : M) (η : ℝ → ℝ → M) (Q : Set M) (hQ : IsCompact Q)
    (hη : ∀ b ∈ Icc b₀ b₁, ContMDiff 𝓘(ℝ, ℝ) I 1 (η b))
    (hstart : ∀ b ∈ Icc b₀ b₁, η b 0 = x)
    (hconf : ∀ b ∈ Icc b₀ b₁, MapsTo (η b) (Icc 0 b) Q)
    (hmin : ∀ b ∈ Icc b₀ b₁, ∀ δ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
      lRegularizedAction S T (η b) 0 b ≤ lRegularizedAction S T δ 0 b) :
    AntitoneOn
      (fun b => 2 * b * lRegularizedAction S T (η b) 0 b -
        2 * (Module.finrank ℝ E : ℝ) * b ^ 2) (Icc b₀ b₁) := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  by_cases hband : b₀ ≤ b₁
  swap
  · intro a ha
    exact False.elim (hband (ha.1.trans ha.2))
  have hb₁ : 0 < b₁ := hb₀.trans_le hband
  have hclock : ∀ s ∈ Icc 0 b₁, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg
      ⟨sub_le_sub_left (pow_le_pow_left₀ hs.1 hs.2 2) T, sub_le_self _ (sq_nonneg s)⟩)
  obtain ⟨C, hC⟩ := exists_lipschitzOnWith_action_of_compact_free_endpoint_minimizers
    S hS T hb₀ hclock x η Q hQ hη hstart hconf hmin
  have hsqrt : MapsTo Real.sqrt (Icc (b₀ ^ 2) (b₁ ^ 2)) (Icc b₀ b₁) := by
    intro rho hrho
    exact ⟨Real.le_sqrt_of_sq_le hrho.1, (Real.sqrt_le_iff).mpr ⟨hb₁.le, hrho.2⟩⟩
  let q := fun rho =>
    2 * Real.sqrt rho * lRegularizedAction S T (η (Real.sqrt rho)) 0 (Real.sqrt rho) -
      2 * (Module.finrank ℝ E : ℝ) * rho
  have hq : ContinuousOn q (Icc (b₀ ^ 2) (b₁ ^ 2)) := by
    exact ((continuousOn_const.mul Real.continuous_sqrt.continuousOn).mul
      (hC.continuousOn.comp Real.continuous_sqrt.continuousOn hsqrt)).sub
        (continuousOn_const.mul continuousOn_id)
  have hanti : AntitoneOn q (Icc (b₀ ^ 2) (b₁ ^ 2)) := by
    apply DifferentialGeometry.antitoneOn_of_deriv_upper_support_le_pos hq
    intro tau htau eps heps
    have hVsub : Ioo (b₀ ^ 2) (b₁ ^ 2) ⊆ Ioo 0 (b₁ ^ 2) := by
      intro rho hrho
      exact ⟨(sq_pos_of_pos hb₀).trans hrho.1, hrho.2⟩
    obtain ⟨f, d, hupper, hcontact, hderiv, hd⟩ :=
      exists_time_upper_support_of_free_endpoint_minimizers_on S hS T (b₁ ^ 2) tau
        (Ioo (b₀ ^ 2) (b₁ ^ 2)) isOpen_Ioo htau hVsub hreg x
        (fun rho => η (Real.sqrt rho))
        (fun rho hrho => hη (Real.sqrt rho) (hsqrt (Ioo_subset_Icc_self hrho)))
        (fun rho hrho => hstart (Real.sqrt rho) (hsqrt (Ioo_subset_Icc_self hrho)))
        (fun rho hrho => hmin (Real.sqrt rho) (hsqrt (Ioo_subset_Icc_self hrho))) eps heps
    exact ⟨f, d, hcontact, hupper.filter_mono nhdsWithin_le_nhds,
      hderiv.hasDerivWithinAt, hd⟩
  intro a ha b hb hab
  have ha0 : 0 ≤ a := hb₀.le.trans ha.1
  have hb0 : 0 ≤ b := hb₀.le.trans hb.1
  have hasq : a ^ 2 ∈ Icc (b₀ ^ 2) (b₁ ^ 2) :=
    ⟨pow_le_pow_left₀ hb₀.le ha.1 2, pow_le_pow_left₀ ha0 ha.2 2⟩
  have hbsq : b ^ 2 ∈ Icc (b₀ ^ 2) (b₁ ^ 2) :=
    ⟨pow_le_pow_left₀ hb₀.le hb.1 2, pow_le_pow_left₀ hb0 hb.2 2⟩
  simpa only [q, Real.sqrt_sq ha0, Real.sqrt_sq hb0] using
    hanti hasq hbsq (pow_le_pow_left₀ ha0 hab 2)

theorem antitoneOn_scaled_action_sub_dim_mul_sq_on_Ioc_of_compact_free_endpoint_minimizers
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {b₀ b₁ : ℝ} (hb₀ : 0 ≤ b₀)
    (hreg : Icc (T - b₁ ^ 2) T ⊆ D.regular)
    (x : M) (η : ℝ → ℝ → M) (Q : Set M) (hQ : IsCompact Q)
    (hη : ∀ b ∈ Ioc b₀ b₁, ContMDiff 𝓘(ℝ, ℝ) I 1 (η b))
    (hstart : ∀ b ∈ Ioc b₀ b₁, η b 0 = x)
    (hconf : ∀ b ∈ Ioc b₀ b₁, MapsTo (η b) (Icc 0 b) Q)
    (hmin : ∀ b ∈ Ioc b₀ b₁, ∀ δ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
      lRegularizedAction S T (η b) 0 b ≤ lRegularizedAction S T δ 0 b) :
    AntitoneOn
      (fun b => 2 * b * lRegularizedAction S T (η b) 0 b -
        2 * (Module.finrank ℝ E : ℝ) * b ^ 2) (Ioc b₀ b₁) := by
  intro a ha b hb hab
  have ha0 : 0 < a := hb₀.trans_lt ha.1
  have hb0 : 0 ≤ b := hb₀.trans hb.1.le
  have hreg' : Icc (T - b ^ 2) T ⊆ D.regular := by
    intro t ht
    exact hreg ⟨(sub_le_sub_left (pow_le_pow_left₀ hb0 hb.2 2) T).trans ht.1, ht.2⟩
  have hsub : Icc a b ⊆ Ioc b₀ b₁ := by
    intro c hc
    exact ⟨ha.1.trans_le hc.1, hc.2.trans hb.2⟩
  have hanti := antitoneOn_scaled_action_sub_dim_mul_sq_of_compact_free_endpoint_minimizers
    S hS T ha0 hreg' x η Q hQ
    (fun c hc => hη c (hsub hc)) (fun c hc => hstart c (hsub hc))
    (fun c hc => hconf c (hsub hc)) (fun c hc => hmin c (hsub hc))
  exact hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
