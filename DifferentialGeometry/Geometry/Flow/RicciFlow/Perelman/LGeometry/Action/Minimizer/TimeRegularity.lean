import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Joining

noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [TopologicalSpace.MetrizableSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

private theorem action_minimum_le_join_of_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (x : M)
    (hclock : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.carrier)
    (hmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
      c ≤ lRegularizedAction S T δ 0 b)
    (α β : ℝ → M) (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Icc 0 a))
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 β (Icc a b))
    (hnode : α a = β a) (hstart : α 0 = x) :
    c ≤ lRegularizedAction S T α 0 a + lRegularizedAction S T β a b := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨γ, hγ, hγ0, _, hact⟩ := exists_lRegularizedAction_join_lt_on_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T 0 a b ha hab α β hα hβ hnode hclock hε
  exact (hmin γ hγ (hγ0.trans hstart)).trans hact.le


private theorem action_minimum_time_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b b₁ K : ℝ} (ha : 0 < a) (hab : a < b) (hbb : b ≤ b₁) (hK : 0 ≤ K)
    (hclock : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.carrier)
    (Q : Set M) (hscalar : ∀ s ∈ Icc a b, ∀ y ∈ Q, |S.scalar (T - s ^ 2) y| ≤ K)
    (x : M) (α β : ℝ → M)
    (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α) (hβ : ContMDiff 𝓘(ℝ, ℝ) I 1 β)
    (hα0 : α 0 = x) (hβ0 : β 0 = x)
    (hαQ : α a ∈ Q) (hβQ : MapsTo β (Icc a b) Q)
    (hminα : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
      lRegularizedAction S T α 0 a ≤ lRegularizedAction S T δ 0 a)
    (hminβ : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
      lRegularizedAction S T β 0 b ≤ lRegularizedAction S T δ 0 b) :
    |lRegularizedAction S T β 0 b - lRegularizedAction S T α 0 a| ≤
      (2 * b₁ ^ 2 * K) * (b-a) := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let P := 2 * b₁ ^ 2 * K
  have htailClock : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier :=
    fun s hs => hclock s ⟨ha.le.trans hs.1, hs.2⟩
  have hconstInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T a b hab.le (fun _ => α a)
      contMDiff_const.contMDiffOn htailClock
  have hconstBound : lRegularizedAction S T (fun _ => α a) a b ≤ P*(b-a) := by
    have hle : lRegularizedAction S T (fun _ => α a) a b ≤ ∫ _ in a..b, P := by
      apply intervalIntegral.integral_mono_on hab.le hconstInt intervalIntegrable_const
      intro s hs
      have hSc := (le_abs_self _).trans (hscalar s hs (α a) hαQ)
      have hs0 : 0 ≤ s := ha.le.trans hs.1
      have hsb : s ≤ b₁ := hs.2.trans hbb
      have hs2 := pow_le_pow_left₀ hs0 hsb 2
      have hv : lVelocity (I := I) (fun _ : ℝ => α a) s = 0 := by
        simp only [lVelocity, mfderiv_const]
        rfl
      simp only [lRegularizedLagrangian, hv, map_zero, mul_zero, zero_add]
      change 2*s^2*S.scalar (T - s ^ 2) (α a) ≤ _
      exact (mul_le_mul_of_nonneg_left hSc (by positivity)).trans
        (by dsimp [P]; nlinarith [mul_le_mul_of_nonneg_right hs2 hK])
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hle
  have hup := (action_minimum_le_join_of_carrier S hS T ha hab x hclock hminβ
    α (fun _ => α a) hα.contMDiffOn contMDiff_const.contMDiffOn rfl hα0).trans
      (add_le_add_right hconstBound _)
  have hβhead := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T 0 a ha.le β hβ.contMDiffOn
      (fun s hs => hclock s ⟨hs.1, hs.2.trans hab.le⟩)
  have hβtail := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T a b hab.le β hβ.contMDiffOn htailClock
  have htailBound : -P*(b-a) ≤ lRegularizedAction S T β a b := by
    have hle : (∫ _ in a..b, -P) ≤ lRegularizedAction S T β a b := by
      apply intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hβtail
      intro s hs
      have hSc := (abs_le.mp (hscalar s hs (β s) (hβQ hs))).1
      have hs0 : 0 ≤ s := ha.le.trans hs.1
      have hsb : s ≤ b₁ := hs.2.trans hbb
      have hs2 := pow_le_pow_left₀ hs0 hsb 2
      have hpot := mul_le_mul_of_nonneg_left hSc (by positivity : 0 ≤ 2*s^2)
      have hspeed := lRegularizedSpeedSq_nonneg S T β s
      dsimp only [lRegularizedSpeedSq] at hspeed
      dsimp only [lRegularizedLagrangian, P]
      nlinarith [mul_le_mul_of_nonneg_right hs2 hK]
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hle
  have hhead := hminα β hβ hβ0
  have hadd := lRegularizedAction_add S T β 0 a b hβhead hβtail
  rw [abs_le]
  constructor <;> dsimp only [P] at * <;> linarith


theorem exists_lipschitzOnWith_action_of_compact_free_endpoint_minimizers
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {b₀ b₁ : ℝ} (hb₀ : 0 < b₀)
    (hclock : ∀ s ∈ Icc 0 b₁, T - s ^ 2 ∈ D.carrier)
    (x : M) (η : ℝ → ℝ → M) (Q : Set M) (hQ : IsCompact Q)
    (hη : ∀ b ∈ Icc b₀ b₁, ContMDiff 𝓘(ℝ, ℝ) I 1 (η b))
    (hstart : ∀ b ∈ Icc b₀ b₁, η b 0 = x)
    (hconf : ∀ b ∈ Icc b₀ b₁, MapsTo (η b) (Icc 0 b) Q)
    (hmin : ∀ b ∈ Icc b₀ b₁, ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
      lRegularizedAction S T (η b) 0 b ≤ lRegularizedAction S T δ 0 b) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun b => lRegularizedAction S T (η b) 0 b) (Icc b₀ b₁) := by
  have hcont : ContinuousOn (fun z : ℝ × M => |S.scalar (T - z.1 ^ 2) z.2|) (Icc 0 b₁ ×ˢ Q) := by
    apply ContinuousOn.abs
    exact hS.scalarCont.comp (f := fun z : ℝ × M => (T-z.1^2,z.2))
      (by fun_prop) (fun z hz => ⟨hclock z.1 hz.1, mem_univ z.2⟩)
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc.prod hQ).bddAbove_image hcont
  let K := max 0 K₀
  have hK : 0 ≤ K := le_max_left _ _
  have hscalar : ∀ s ∈ Icc 0 b₁, ∀ y ∈ Q, |S.scalar (T - s ^ 2) y| ≤ K := by
    intro s hs y hy
    exact (hK₀ ⟨(s,y),⟨hs,hy⟩,rfl⟩).trans (le_max_right _ _)
  let C := 2 * b₁ ^ 2 * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨⟨C,hC⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro a ha b hb'
  have hord {a b : ℝ} (ha : a ∈ Icc b₀ b₁) (hb' : b ∈ Icc b₀ b₁) (hab : a < b) :
      |lRegularizedAction S T (η b) 0 b - lRegularizedAction S T (η a) 0 a| ≤ C * (b-a) := by
    exact action_minimum_time_bound S hS T (hb₀.trans_le ha.1) hab hb'.2 hK
      (fun s hs => hclock s ⟨hs.1,hs.2.trans hb'.2⟩) Q
      (fun s hs y hy => hscalar s ⟨(hb₀.trans_le ha.1).le.trans hs.1,hs.2.trans hb'.2⟩ y hy)
      x (η a) (η b) (hη a ha) (hη b hb') (hstart a ha) (hstart b hb')
      (hconf a ha ⟨(hb₀.trans_le ha.1).le,le_rfl⟩)
      (fun s hs => hconf b hb' ⟨(hb₀.trans_le ha.1).le.trans hs.1,hs.2⟩)
      (hmin a ha) (hmin b hb')
  change dist (lRegularizedAction S T (η a) 0 a) (lRegularizedAction S T (η b) 0 b) ≤ C * dist a b
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [Real.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hab), neg_sub, abs_sub_comm]
    exact hord ha hb' hab
  · simp only [dist_self, mul_zero, le_refl]
  · rw [Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr hba)]
    exact hord hb' ha hba

end DifferentialGeometry.PDE.RicciFlow.Perelman
