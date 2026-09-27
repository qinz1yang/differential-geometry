import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeSliceConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.MovingShi
import DifferentialGeometry.Geometry.Metric.Convergence.Window.EventualBounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Tail

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable [I.Boundaryless]

private theorem initial_compact_metric_bounds
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hreg : Ioo 0 T ⊆ D.regular)
    (hgram : ∀ n (x : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n).base.metric p.1) x p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x).baseSet))
    (hinitial : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0) R R)
    (hcurv : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
        curvDerivNorm q ((S i).base.metric t) x ≤ C)
    (K : Set M) (hK : IsCompact K) (N : ℕ) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ i in atTop,
      (∀ q ≤ N, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
        metricCovDerivNorm q ((S i).base.metric t) R x ≤ C) ∧
      (∀ q ≤ N, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
        metricDerivNorm q ((S i).base.metric s) ((S i).base.metric t) R x ≤
          L * |s - t|) := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K', hK', hKK', _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let U := interior K'
  obtain ⟨_, _, hC0⟩ := hcurv K' hK' 0
  obtain ⟨B, hB, hequiv⟩ := exists_eventually_metric_uniform_equivalence_of_time_slice_convergence
    S hS R hT hslab hreg ⟨le_rfl, hT.le⟩ K' hK' (hinitial K' hK' 0) hC0
  choose Ccurv _ hcurvBound using hcurv K' hK'
  have hcurvTail : ∀ᶠ i in atTop, ∀ q ∈ Finset.range (N+1),
      ∀ t ∈ Icc 0 T, ∀ x ∈ K', curvDerivNorm q ((S i).base.metric t) x ≤ Ccurv q := by
    rw [eventually_all_finset]
    exact fun q _ => hcurvBound q
  have hini : ∀ᶠ i in atTop, ∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
      metricCovDerivNorm q ((S i).base.metric 0) R x ≤ (1 : ℝ) := by
    obtain ⟨n, hn⟩ := hinitial K' hK' N 1 zero_lt_one
    filter_upwards [eventually_ge_atTop n] with i hi
    intro q hq hqN x hx
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have hb := covNorm_le_add (r+1) ((S i).base.metric 0) R R x
    rw [covNorm_self_succ, zero_add] at hb
    exact hb.trans ((derivNorm_le_sup hK' hqN _ _ _ (interior_subset hx)).trans (hn i hi).le)
  obtain ⟨Kr, hKr, hRic⟩ := exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
    (I := I) (M := M) N Ccurv
  obtain ⟨L, hL, hlip⟩ := exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds
    U isOpen_interior R N T B Kr hB hKr (fun _ => 1) (by intros; norm_num)
  let C := B * Real.sqrt (Module.finrank ℝ E : ℝ) + 1 + L*T
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, L, hC, hL, ?_⟩
  filter_upwards [hequiv, hcurvTail, hini] with i he hc hi
  have heU : ∀ t ∈ Icc 0 T, MetricUniformEquivalentOn U R ((S i).base.metric t) B :=
    fun t ht => ⟨hB, fun x hx => (he t ht).2 x (interior_subset hx)⟩
  have hShi := hRic (fun _ t => (S i).base.metric t) U 0 T
    (fun q hq _ t ht x hx => hc q (Finset.mem_range.mpr (by omega)) t ht x (interior_subset hx))
  have htime := hlip D T hT.le le_rfl hreg (S i) (hS i) (hgram i) heU hi hShi K hKK'
  have hpoint : ∀ q ≤ N, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
      metricDerivNorm q ((S i).base.metric s) ((S i).base.metric t) R x ≤ L * |s-t| :=
    fun q hq s hs t ht x hx => (derivNorm_le_sup hK hq _ _ _ hx).trans (htime s hs t ht)
  refine ⟨?_, hpoint⟩
  intro q hq t ht x hx
  by_cases hz : q = 0
  · subst q
    have hb := covOrder_zero_le ((S i).base.metric t) R (he t ht) x (interior_subset (hKK' hx))
    have hp : 0 ≤ L*T := mul_nonneg hL hT.le
    exact hb.trans (by dsimp [C]; linarith)
  · have hb := covNorm_le_add q ((S i).base.metric t) ((S i).base.metric 0) R x
    have h0 := hi q (by omega) hq x (hKK' hx)
    have hd := hpoint q hq t ht 0 ⟨le_rfl,hT.le⟩ x hx
    rw [sub_zero, abs_of_nonneg ht.1] at hd
    have hlt := mul_le_mul_of_nonneg_left ht.2 hL
    have hB0 : 0 ≤ B * Real.sqrt (Module.finrank ℝ E : ℝ) := by positivity
    dsimp [C]
    linarith

private theorem initial_individual_time_bounds
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hreg : Ioo 0 T ⊆ D.regular)
    (hgram : ∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x).baseSet))
    (K : Set M) (hK : IsCompact K) (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ≤ N, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
      metricDerivNorm q (S.base.metric s) (S.base.metric t) R x ≤ L * |s-t| := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcurv : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ _i : ℕ in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
        curvDerivNorm q (S.base.metric t) x ≤ C := by
    intro K hK q
    have hc : ContinuousOn (fun p : ℝ × M => curvDerivNorm q (S.base.metric p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
      have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 T)
        (uniqueDiffOn_Icc hT) hgram q).continuousOn.sqrt
      simpa only [curvDerivNorm, curvDerivNormSq, curvCovDeriv_normSq_eq] using hh
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      (hc.mono (prod_mono subset_rfl (subset_univ K)))
    exact ⟨max B 0, le_max_right _ _, Eventually.of_forall fun _ t ht x hx =>
      (le_abs_self _).trans ((hB (t,x) ⟨ht,hx⟩).trans (le_max_left _ _))⟩
  have hini : MetricCInfConvergenceOnCompacts (fun _ : ℕ => S.base.metric 0)
      (S.base.metric 0) (S.base.metric 0) := by
    intro K _ p e he
    exact ⟨0, fun _ _ => by rw [metricDerivNormSupOn_self]; exact he⟩
  obtain ⟨_, L, _, hL, hb⟩ := initial_compact_metric_bounds (fun _ => S) (fun _ => hS)
    (S.base.metric 0) hT hslab hreg (fun _ => hgram) hini hcurv K hK N
  obtain ⟨i, hi⟩ := hb.exists
  obtain ⟨B, hB, href⟩ := exists_metric_deriv_norm_reference_bound hK (S.base.metric 0) R N
  refine ⟨B * ((N+1 : ℕ) : ℝ) * L, by positivity, ?_⟩
  intro q hq s hs t ht x hx
  calc
    _ ≤ B * ∑ j ∈ Finset.range (N+1),
        metricDerivNorm j (S.base.metric s) (S.base.metric t) (S.base.metric 0) x :=
      href _ _ q hq x hx
    _ ≤ B * ∑ _j ∈ Finset.range (N+1), L * |s-t| :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj =>
        hi.2 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) s hs t ht x hx) hB
    _ = (B * ((N+1 : ℕ) : ℝ) * L) * |s-t| := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

private theorem initial_solution_subsequence [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier)
    (hreg : Ioo 0 T ⊆ D.regular)
    (hgram : ∀ n (x : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n).base.metric p.1) x p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x).baseSet))
    (hinitial : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0) R R)
    (hcurv : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
        curvDerivNorm q ((S i).base.metric t) x ≤ C) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      g 0 = R ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.closed 0 T hT.le)) ∧
      (∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (g p.1) x p.2 i j)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) ∧
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc 0 T,
          metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t) R < epsilon := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hequiv : ∀ K : Set M, IsCompact K → ∃ B : ℝ, 1 ≤ B ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T, MetricUniformEquivalentOn K R ((S i).base.metric t) B := by
    intro K hK
    obtain ⟨C, _, hc⟩ := hcurv K hK 0
    exact exists_eventually_metric_uniform_equivalence_of_time_slice_convergence
      S hS R hT hslab hreg ⟨le_rfl,hT.le⟩ K hK (hinitial K hK 0) hc
  have hbounds := initial_compact_metric_bounds S hS R hT hslab hreg hgram hinitial hcurv
  obtain ⟨rho, hrho, g, hg⟩ :=
    exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_pointwise_lower
      hT.le R (fun i t => (S i).base.metric t)
      (fun i K hK p => by
        obtain ⟨L, hL, hb⟩ := initial_individual_time_bounds (S i) (hS i) R hT hslab hreg
          (hgram i) K hK p
        exact ⟨L,hL,fun s hs t ht q hq x hx => hb q hq s hs t ht x hx⟩)
      (fun K hK p => by
        obtain ⟨_, L, _, hL, hb⟩ := hbounds K hK p
        exact ⟨L, hL, hb.mono fun i hi s hs t ht q hq x hx => hi.2 q hq s hs t ht x hx⟩)
      (fun t ht q K hK => by
        obtain ⟨C, _, _, _, hb⟩ := hbounds K hK q
        exact ⟨C,hb.mono fun i hi x hx => hi.1 q le_rfl t ht x hx⟩)
      (fun t ht x => by
        obtain ⟨B, hB, hb⟩ := hequiv {x} isCompact_singleton
        exact ⟨B⁻¹, inv_pos.mpr (zero_lt_one.trans_le hB),
          hb.mono fun i hi v => ((hi t ht).2 x (mem_singleton x) v).1⟩)
  have hzero : g 0 = R := by
    apply metricCInf_unique (fun i => (S (rho i)).base.metric 0) (g 0) R R R
    · intro K hK p e he
      obtain ⟨N,hN⟩ := hg K hK p e he
      exact ⟨N,fun i hi => hN i hi 0 ⟨le_rfl,hT.le⟩⟩
    · intro K hK p e he
      obtain ⟨N,hN⟩ := hinitial K hK p e he
      exact ⟨N,fun i hi => hN (rho i) (hi.trans (hrho.id_le i))⟩
  refine ⟨rho,hrho,g,hzero,?_,?_,hg⟩
  · by_cases hM : Nonempty M
    · let _ : Nonempty M := hM
      let P : PointedRiemannianManifold (I := I) := {
        M := M
        topology := inferInstance
        charted := inferInstance
        smooth := inferInstance
        sigmaCompact := inferInstance
        t2 := inferInstance
        t2TangentBundle := inferInstance
        basepoint := Classical.choice hM
        metric := R }
      apply isSolutionOn_of_fixed_domain_metric_convergence P S hS hT hslab hreg rho hrho g hg
      intro K hK p
      obtain ⟨_, L, _, _, hb⟩ := hbounds K hK p
      exact hb.mono fun i hi => ⟨L,fun s hs t ht q hq x hx => hi.2 q hq s hs t ht x hx⟩
    · let _ : IsEmpty M := not_nonempty_iff.mp hM
      apply (isSolutionOn_timeRestrict (hS 0) hslab hreg).congr_metric
      intro t _
      exact SmoothRiemannianMetric.ext_inner fun x => isEmptyElim x
  · apply contMDiffOn_chartGramMatrix_of_fixed_domain_metric_convergence
      S hS R hT hslab hreg rho hrho g hg
    intro K hK p
    obtain ⟨_, L, _, _, hb⟩ := hbounds K hK p
    exact hb.mono fun i hi => ⟨L,fun s hs t ht q hq x hx => hi.2 q hq s hs t ht x hx⟩

theorem exists_solution_subsequence_on_closed_interval_of_initial_convergence [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular)
    (hgram : ∀ n (x : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n).base.metric p.1) x p.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x).baseSet))
    (hinitial : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric a) R R)
    (hcurv : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm q ((S i).base.metric t) x ≤ C) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      g a = R ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.closed a b hab.le)) ∧
      (∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (g p.1) x p.2 i j)
          (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) ∧
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t) R < epsilon := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let U := fun n => (S n).timeShift a
  have hU : ∀ n, IsSolutionOn (U n) := fun n => isSolutionOn_timeShift (hS n) a
  have hcarrier : Icc 0 (b-a) ⊆ (D.timeShift a).carrier := by
    intro t ht
    exact hslab ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hregular : Ioo 0 (b-a) ⊆ (D.timeShift a).regular := by
    intro t ht
    exact hreg ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hgramU : ∀ n (x : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((U n).base.metric p.1) x p.2 i j)
        (Icc 0 (b-a) ×ˢ (trivializationAt E (TangentSpace I) x).baseSet) := by
    intro n x i j
    exact (hgram n x i j).comp
      ((contMDiffOn_fst.add contMDiffOn_const).prodMk contMDiffOn_snd)
      (fun p hp => ⟨⟨by change a ≤ p.1 + a; linarith [hp.1.1],
        by change p.1 + a ≤ b; linarith [hp.1.2]⟩,hp.2⟩)
  have hinitialU : MetricCInfConvergenceOnCompacts (fun n => (U n).base.metric 0) R R := by
    simpa only [U,SolutionOn.timeShift_base_metric,zero_add] using hinitial
  have hcurvU : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc 0 (b-a), ∀ x ∈ K,
        curvDerivNorm q ((U i).base.metric t) x ≤ C := by
    intro K hK q
    obtain ⟨C,hC,hb⟩ := hcurv K hK q
    exact ⟨C,hC,hb.mono fun i hi t ht x hx =>
      hi (t+a) ⟨by linarith [ht.1],by linarith [ht.2]⟩ x hx⟩
  obtain ⟨rho,hrho,g,hzero,hg,hggram,hconv⟩ := initial_solution_subsequence U hU R
    (sub_pos.mpr hab) hcarrier hregular hgramU hinitialU hcurvU
  refine ⟨rho,hrho,fun t => g (t + -a),?_,?_,?_,?_⟩
  · simpa only [add_neg_cancel] using hzero
  · apply isSolutionOn_timeRestrict (isSolutionOn_timeShift hg (-a))
    · intro t ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
    · intro t ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  · intro x i j
    exact (hggram x i j).comp
      ((contMDiffOn_fst.add contMDiffOn_const).prodMk contMDiffOn_snd)
      (fun p hp => ⟨⟨by change 0 ≤ p.1 + -a; linarith [hp.1.1],
        by change p.1 + -a ≤ b-a; linarith [hp.1.2]⟩,hp.2⟩)
  · intro K hK p e he
    obtain ⟨N,hN⟩ := hconv K hK p e he
    refine ⟨N,fun i hi t ht => ?_⟩
    have hh := hN i hi (t + -a) ⟨by linarith [ht.1],by linarith [ht.2]⟩
    simpa only [U,SolutionOn.timeShift_base_metric,neg_add_cancel_right] using hh

end DifferentialGeometry.PDE.RicciFlow
