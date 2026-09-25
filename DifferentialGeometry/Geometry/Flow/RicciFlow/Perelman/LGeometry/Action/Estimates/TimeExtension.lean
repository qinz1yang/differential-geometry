import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Joining
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman
variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {D : RealTimeInterval}

omit [I.Boundaryless] in
theorem continuousOn_lRegularizedAction_end_time_of_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T : ℝ) {a b : ℝ} (hab : a ≤ b) (η : ℝ → M)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc a b))
    (hclock : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier) :
    ContinuousOn (fun t => lRegularizedAction S T η a t) (Icc a b) := by
  have hint := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hMet hSc T a b hab η hη hclock
  simpa only [uIcc_of_le hab, lRegularizedAction] using intervalIntegral.continuousOn_primitive_interval' hint
    (show a ∈ uIcc a b from left_mem_uIcc)

omit [I.Boundaryless] in
theorem eventually_lRegularizedAction_lt_of_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T : ℝ) {a b : ℝ} (hab : a ≤ b) (η : ℝ → M)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc a b))
    (hclock : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier)
    (L : ℝ → ℝ) (hL : ContinuousOn L (Icc a b)) {v : ℝ} (hv : v ∈ Icc a b)
    (hact : lRegularizedAction S T η a v < L v) :
    ∀ᶠ t in 𝓝[Icc a b] v, lRegularizedAction S T η a t < L t :=
  ((continuousOn_lRegularizedAction_end_time_of_carrier S hMet hSc T hab η hη hclock v hv).sub
    (hL v hv)).eventually (Iio_mem_nhds (sub_neg.mpr hact)) |>.mono
      (fun _ ht => sub_neg.mp ht)

theorem exists_lRegularizedAction_extension_bound_on_compact
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T bmax : ℝ) (Q : Set M) (hQ : IsCompact Q)
    (hclock : ∀ t ∈ Icc 0 bmax, T - t ^ 2 ∈ D.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ bmax →
      ∀ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η → η a ∈ Q →
      ∀ ε : ℝ, 0 < ε → ∃ γ : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = η 0 ∧ γ b = η a ∧
        lRegularizedAction S T γ 0 b < lRegularizedAction S T η 0 a + C * (b - a) + ε := by
  have hcont : ContinuousOn (fun z : ℝ × M => 2 * z.1 ^ 2 * S.scalar (T - z.1 ^ 2) z.2)
      (Icc 0 bmax ×ˢ Q) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact hSc.scalar_continuousOn.comp (f := fun z : ℝ × M => (T - z.1 ^ 2, z.2))
        (by fun_prop) (fun z hz => ⟨hclock z.1 hz.1, mem_univ z.2⟩)
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod hQ).bddAbove_image hcont
  let C := max 0 K
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a b ha hab hb η hη hηQ ε hε
  have htime : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier :=
    fun t ht => hclock t ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hint := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hMet hSc T a b hab (fun _ => η a) contMDiff_const.contMDiffOn htime
  have hbound : lRegularizedAction S T (fun _ => η a) a b ≤ C * (b - a) := by
    have hh := intervalIntegral.integral_mono_on hab hint (intervalIntegrable_const (c := C))
      (fun t ht => by
        have hv : lVelocity (I := I) (fun _ : ℝ => η a) t = 0 := by
          simp only [lVelocity, mfderiv_const]
          rfl
        simp only [lRegularizedLagrangian, hv, map_zero, mul_zero, zero_add]
        exact (hK ⟨(t,η a), ⟨⟨ha.trans ht.1, ht.2.trans hb⟩,hηQ⟩, rfl⟩).trans (le_max_right _ _))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, lRegularizedAction] using hh
  obtain ⟨γ, hγ, hγ0, hγb, hact⟩ := exists_lRegularizedAction_join_lt_on_carrier_of_contMDiff
    S hMet hSc T 0 a b ha hab η (fun _ => η a) hη contMDiff_const rfl
      (fun t ht => hclock t ⟨ht.1, ht.2.trans hb⟩) hε
  exact ⟨γ, hγ, hγ0, hγb, hact.trans_le (by linarith)⟩


theorem exists_lRegularizedAction_lt_of_tendsto_time
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T b : ℝ) (Q : Set M) (hQ : IsCompact Q)
    (hclock : ∀ t ∈ Icc 0 b, T - t ^ 2 ∈ D.carrier)
    (time : ℕ → ℝ) (htime : ∀ n, time n ∈ Icc 0 b) (hlim : Tendsto time atTop (𝓝 b))
    (η : ℕ → ℝ → M) (hη : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (η n))
    (x : M) (hstart : ∀ n, η n 0 = x) (hend : ∀ n, η n (time n) ∈ Q)
    {A L : ℝ} (hAL : A < L)
    (hact : ∀ n, lRegularizedAction S T (η n) 0 (time n) ≤ A) :
    ∃ (n : ℕ) (γ : ℝ → M), ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧ γ b = η n (time n) ∧
      lRegularizedAction S T γ 0 b < L := by
  obtain ⟨C, _, hC⟩ := exists_lRegularizedAction_extension_bound_on_compact S hMet hSc T b Q hQ hclock
  have htail : Tendsto (fun n => C * (b - time n)) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).sub hlim).const_mul C
  have heps : 0 < (L - A) / 2 := half_pos (sub_pos.mpr hAL)
  obtain ⟨n, hn⟩ := (htail.eventually (Iio_mem_nhds heps)).exists
  obtain ⟨γ, hγ, hγ0, hγb, hγact⟩ := hC (time n) b (htime n).1 (htime n).2 le_rfl
    (η n) (hη n) (hend n) ((L - A) / 2) heps
  refine ⟨n, γ, hγ, hγ0.trans (hstart n), hγb, ?_⟩
  linarith [hact n]


theorem exists_lRegularizedAction_lt_linear_of_tendsto_time
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T b : ℝ) (Q : Set M) (hQ : IsCompact Q)
    (hclock : ∀ t ∈ Icc 0 b, T - t ^ 2 ∈ D.carrier)
    (time : ℕ → ℝ) (htime : ∀ n, time n ∈ Ioc 0 b) (hlim : Tendsto time atTop (𝓝 b))
    (η : ℕ → ℝ → M) (hη : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (η n))
    (x : M) (hstart : ∀ n, η n 0 = x) (hend : ∀ n, η n (time n) ∈ Q)
    {c κ : ℝ} (hc : 0 ≤ c) (hκ : κ < 0)
    (hact : ∀ n, 2 * time n * lRegularizedAction S T (η n) 0 (time n) -
      2 * c * (time n) ^ 2 ≤ κ) :
    ∃ (n : ℕ) (γ : ℝ → M), ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧ γ b = η n (time n) ∧
      lRegularizedAction S T γ 0 b < c * b := by
  have hb : 0 < b := (htime 0).1.trans_le (htime 0).2
  apply exists_lRegularizedAction_lt_of_tendsto_time S hMet hSc T b Q hQ hclock
    time (fun n => ⟨(htime n).1.le, (htime n).2⟩) hlim η hη x hstart hend
    (A := c * b + κ / (2 * b)) (by have := div_neg_of_neg_of_pos hκ (by positivity : 0 < 2 * b); linarith)
  intro n
  have ha : 0 < 2 * time n := mul_pos (by norm_num) (htime n).1
  have hlocal : lRegularizedAction S T (η n) 0 (time n) ≤ c * time n + κ / (2 * time n) := by
    have hh := hact n
    have heq : c * time n + κ / (2 * time n) = (2 * c * (time n) ^ 2 + κ) / (2 * time n) := by
      field_simp
    rw [heq]
    exact (le_div_iff₀ ha).mpr (by nlinarith)
  have hfrac : κ / (2 * time n) ≤ κ / (2 * b) := by
    have hh := div_le_div_of_nonneg_left (neg_nonneg.mpr hκ.le) ha
      (mul_le_mul_of_nonneg_left (htime n).2 (by norm_num : (0:ℝ) ≤ 2))
    simpa only [neg_div, neg_le_neg_iff] using hh
  exact hlocal.trans (add_le_add (mul_le_mul_of_nonneg_left (htime n).2 hc) hfrac)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
