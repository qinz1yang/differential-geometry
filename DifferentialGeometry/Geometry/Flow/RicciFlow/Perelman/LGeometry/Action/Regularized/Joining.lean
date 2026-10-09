import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionJoin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.CarrierIntegrability

noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem exists_lRegularizedAction_join_lt_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a c b : ℝ) (hac : a < c) (hcb : c < b)
    (α β : ℝ → M)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Icc a c))
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 β (Icc c b))
    (hnode : α c = β c)
    (hback : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ a = α a ∧ γ b = β b ∧
      lRegularizedAction S T γ a b <
        lRegularizedAction S T α a c + lRegularizedAction S T β c b + ε := by
  obtain ⟨η, m, t, p, u, hhead, htail, htmono, hta, htb, _, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) a c b hac hcb α β hα hβ hnode
  obtain ⟨δ, hδ, hδa, hδb, hlimit⟩ :=
    exists_lRegAction_c1_approx_on_carrier S hMet hSc T a b t htmono hta htb
      p η u hsrc hrep hback
  have hηhead : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc a c) := hα.congr (fun _ ht => hhead ht)
  have hηtail : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc c b) := hβ.congr (fun _ ht => htail ht)
  have hihead := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hMet hSc T a c hac.le η hηhead (fun r hr => hback r ⟨hr.1, hr.2.trans hcb.le⟩)
  have hitail := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hMet hSc T c b hcb.le η hηtail (fun r hr => hback r ⟨hac.le.trans hr.1, hr.2⟩)
  have hheadAct : lRegularizedAction S T η a c = lRegularizedAction S T α a c := by
    apply lRegularizedAction_congr
    intro r hr
    rw [uIoo_of_le hac.le] at hr
    exact hhead (Ioo_subset_Icc_self hr)
  have htailAct : lRegularizedAction S T η c b = lRegularizedAction S T β c b := by
    apply lRegularizedAction_congr
    intro r hr
    rw [uIoo_of_le hcb.le] at hr
    exact htail (Ioo_subset_Icc_self hr)
  have haction : lRegularizedAction S T η a b =
      lRegularizedAction S T α a c + lRegularizedAction S T β c b := by
    rw [← lRegularizedAction_add S T η a c b hihead hitail, hheadAct, htailAct]
  have hev : ∀ᶠ n in atTop,
      lRegularizedAction S T (δ n) a b < lRegularizedAction S T η a b + ε :=
    hlimit.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨δ n, hδ n, (hδa n).trans (hhead ⟨le_rfl, hac.le⟩),
    (hδb n).trans (htail ⟨hcb.le, le_rfl⟩), ?_⟩
  simpa only [haction] using hn

theorem exists_lRegularizedAction_join_lt_on_carrier_of_contMDiff
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (α β : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α) (hβ : ContMDiff 𝓘(ℝ, ℝ) I 1 β)
    (hnode : α c = β c)
    (hback : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ a = α a ∧ γ b = β b ∧
      lRegularizedAction S T γ a b <
        lRegularizedAction S T α a c + lRegularizedAction S T β c b + ε := by
  rcases hac.eq_or_lt with rfl | hac
  · refine ⟨β, hβ, hnode.symm, rfl, ?_⟩
    have hzero : lRegularizedAction S T α a a = 0 := intervalIntegral.integral_same
    rw [hzero, zero_add]
    exact lt_add_of_pos_right _ hε
  rcases hcb.eq_or_lt with rfl | hcb
  · refine ⟨α, hα, rfl, hnode, ?_⟩
    have hzero : lRegularizedAction S T β c c = 0 := intervalIntegral.integral_same
    rw [hzero, add_zero]
    exact lt_add_of_pos_right _ hε
  exact exists_lRegularizedAction_join_lt_on_carrier S hMet hSc T a c b hac hcb
    α β hα.contMDiffOn hβ.contMDiffOn hnode hback hε

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem exists_lRegularizedAction_finite_join_lt_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S) (T : ℝ)
    (n : ℕ) (hn : 0 < n) (t : ℕ → ℝ) (β : ℕ → ℝ → M)
    (ht : ∀ k < n, t k ≤ t (k + 1))
    (hβ : ∀ k < n, ContMDiff 𝓘(ℝ, ℝ) I 1 (β k))
    (hnode : ∀ k, k + 1 < n → β k (t (k + 1)) = β (k + 1) (t (k + 1)))
    (hback : ∀ s ∈ Icc (t 0) (t n), T - s ^ 2 ∈ D.carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧
      γ (t 0) = β 0 (t 0) ∧ γ (t n) = β (n - 1) (t n) ∧
      lRegularizedAction S T γ (t 0) (t n) <
        (∑ k ∈ Finset.range n, lRegularizedAction S T (β k) (t k) (t (k + 1))) + ε := by
  induction n generalizing ε with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨β 0, hβ 0 (by omega), rfl, rfl, ?_⟩
      simpa only [Nat.zero_add, Finset.sum_range_one] using lt_add_of_pos_right
        (lRegularizedAction S T (β 0) (t 0) (t 1)) hε
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have ht0n : t 0 ≤ t n := by
      have haux : ∀ k ≤ n, t 0 ≤ t k := by
        intro k hk
        induction k with
        | zero => exact le_rfl
        | succ k ihk => exact (ihk (by omega)).trans (ht k (by omega))
      exact haux n le_rfl
    obtain ⟨γ₀, hγ₀, hstart, hend, hact⟩ := ih hnpos
      (fun k hk => ht k (Nat.lt_succ_of_lt hk))
      (fun k hk => hβ k (Nat.lt_succ_of_lt hk))
      (fun k hk => hnode k (Nat.lt_succ_of_lt hk))
      (fun s hs => hback s ⟨hs.1, hs.2.trans (ht n (Nat.lt_succ_self n))⟩) (half_pos hε)
    have hmatch : γ₀ (t n) = β n (t n) := by
      have hh := hnode (n - 1) (by omega)
      rw [Nat.sub_add_cancel hnpos] at hh
      exact hend.trans hh
    obtain ⟨γ, hγ, hγstart, hγend, hjoin⟩ :=
      exists_lRegularizedAction_join_lt_on_carrier_of_contMDiff S hMet hSc T (t 0) (t n) (t (n + 1))
        ht0n (ht n (Nat.lt_succ_self n)) γ₀ (β n) hγ₀ (hβ n (Nat.lt_succ_self n)) hmatch hback (half_pos hε)
    refine ⟨γ, hγ, hγstart.trans hstart, ?_, ?_⟩
    · simpa only [Nat.add_sub_cancel_right] using hγend
    · rw [Finset.sum_range_succ]
      linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
