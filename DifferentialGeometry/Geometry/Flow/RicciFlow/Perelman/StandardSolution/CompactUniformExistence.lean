import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Scaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

private theorem extend_before_control_time (g₀ : SmoothRiemannianMetric I M)
    (τ : ℝ) (P : FlowTo g₀ τ) (hdim : Module.finrank ℝ E = 3) (K : ℝ)
    (hτ : τ ≤ compactCurvatureControlTime (Module.finrank ℝ E) K)
    (hinit : ∀ x : M, Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ Nonempty (FlowTo g₀ (τ + ε)) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hi (x : M) : Real.sqrt (normSq0S (P.S.base.metric 0) x 4
      (metricRm04 (P.S.base.metric 0) x)) ≤ K := by
    have he : P.S.base.metric 0 = g₀ := P.start
    rw [he]
    exact hinit x
  have hb : Rm04NormSqBoundedAt P.S P.S.base.rm04 := by
    refine ⟨2 * K ^ 2 + 1, ?_⟩
    intro t x ht0 htτ
    have hsub : Icc 0 t ⊆ Ico 0 τ := fun r hr => ⟨hr.1, hr.2.trans_lt htτ⟩
    have hh := curvature_bound_from_initial_compact t ht0 K (htτ.le.trans hτ) _ P.S P.isSolution
      hsub (fun r hr => ⟨hr.1, hr.2.trans htτ⟩)
      (fun x₀ i j => (P.joint x₀ i j).mono (prod_mono hsub subset_rfl)) hi t ⟨ht0, le_rfl⟩ x
    have hs := (Real.sqrt_le_iff.mp hh).2
    rw [Real.sq_sqrt (by nlinarith [sq_nonneg K] : 0 ≤ 2 * K ^ 2 + 1)] at hs
    exact hs
  exact flow_to_extend P (extends_of_rmBounded hdim P.isSolution (rm04Realizes_metric P.S) hb)

theorem exists_compact_flow_beyond_control_time (g₀ : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) (K : ℝ)
    (hinit : ∀ x : M, Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ K) :
    ∃ τ : ℝ, compactCurvatureControlTime (Module.finrank ℝ E) K < τ ∧ Nonempty (FlowTo g₀ τ) := by
  classical
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  by_contra hn
  let ends : Set ℝ := {τ | Nonempty (FlowTo g₀ τ)}
  have hbound (τ : ℝ) (hτ : τ ∈ ends) : τ ≤ compactCurvatureControlTime (Module.finrank ℝ E) K :=
    le_of_not_gt (fun ht => hn ⟨τ, ht, hτ⟩)
  have hbdd : BddAbove ends := ⟨compactCurvatureControlTime (Module.finrank ℝ E) K, hbound⟩
  obtain ⟨τ₀, hseed⟩ := flow_to_seed g₀
  let P₀ : FlowTo g₀ τ₀ := Classical.choice hseed
  have hτ₀ : τ₀ ∈ ends := hseed
  have hne : ends.Nonempty := ⟨τ₀, hτ₀⟩
  let Tsup := sSup ends
  have hTsup : 0 < Tsup := P₀.time_pos.trans_le (le_csSup hbdd hτ₀)
  have hTsupbound : Tsup ≤ compactCurvatureControlTime (Module.finrank ℝ E) K := csSup_le hne hbound
  have hcover (t : ℝ) (ht : t ∈ Ico 0 Tsup) : ∃ τ : ℝ, ∃ P : FlowTo g₀ τ, t < τ := by
    obtain ⟨τ, hτ, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact ⟨τ, Classical.choice hτ, htτ⟩
  choose endAt flowAt hltAt using hcover
  let g : ℝ → SmoothRiemannianMetric I M := fun t =>
    if ht : t ∈ Ico 0 Tsup then (flowAt t ht).S.base.metric t else g₀
  have hagree (t : ℝ) (ht : t ∈ Ico 0 Tsup) {τ : ℝ} (P : FlowTo g₀ τ) (htτ : t < τ) :
      g t = P.S.base.metric t := by
    simp only [g, dite_eq_left ht]
    exact flow_to_eq (flowAt t ht) P ht.1 (hltAt t ht) htτ
  have hzero : g 0 = g₀ := by
    have ht : (0 : ℝ) ∈ Ico 0 Tsup := ⟨le_rfl, hTsup⟩
    simp only [g, dite_eq_left ht]
    exact (flowAt 0 ht).start
  have hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Ico 0 Tsup ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    apply contMDiffOn_of_locally_contMDiffOn
    intro p hp
    let P := flowAt p.1 hp.1
    refine ⟨Iio (endAt p.1 hp.1) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet,
      isOpen_Iio.prod (trivializationAt E (TangentSpace I) x₀).open_baseSet,
      ⟨hltAt p.1 hp.1, hp.2⟩, ?_⟩
    refine ((P.joint x₀ i j).mono ?_).congr ?_
    · intro q hq
      exact ⟨⟨hq.1.1.1, hq.2.1⟩, hq.2.2⟩
    · intro q hq
      rw [hagree q.1 hq.1.1 P hq.2.1]
      rfl
  have hpde : ∀ t ∈ Ico 0 Tsup, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun r => (g r).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici 0) t := by
    intro t ht x v w
    let P := flowAt t ht
    have hb : t < min Tsup (endAt t ht) := lt_min ht.2 (hltAt t ht)
    have he : (fun r => (g r).inner x v w) =ᶠ[𝓝[Ici 0] t]
        (fun r => (P.S.base.metric r).inner x v w) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with r hr0 hr
      exact congrArg (fun m : SmoothRiemannianMetric I M => m.inner x v w)
        (hagree r ⟨hr0, hr.trans_le (min_le_left _ _)⟩ P (hr.trans_le (min_le_right _ _)))
    have het := hagree t ht P (hltAt t ht)
    have hh := (P.pde t ⟨ht.1, hltAt t ht⟩ x v w).congr_of_eventuallyEq he
      (congrArg (fun m : SmoothRiemannianMetric I M => m.inner x v w) het)
    simp only [SolutionOn.family_metric] at hh
    rw [← het] at hh
    exact hh
  let S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tsup hTsup) :=
    { base := { metric := g } }
  have hS : IsSolutionOn S := solutionOn_of_joint hTsup g hjoint hpde
  let P : FlowTo g₀ Tsup := ⟨hTsup, S, hS, hzero, hjoint, hpde⟩
  obtain ⟨ε, hε, hwide⟩ := extend_before_control_time g₀ Tsup P hdim K hTsupbound hinit
  have hle : Tsup + ε ≤ Tsup := le_csSup hbdd (show Tsup + ε ∈ ends from hwide)
  linarith

omit [I.Boundaryless] [CompactSpace M] [BoundarylessManifold I M] in
private theorem sqrt_normSq0S_metricRm04_scale (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (x : M) :
    Real.sqrt (normSq0S (scaleMetric c hc g) x 4 (metricRm04 (scaleMetric c hc g) x)) =
      Real.sqrt (normSq0S g x 4 (metricRm04 g x)) / c := by
  convert! CheegerGromovCompactness.curvDerivNorm_scaleMetric g c hc 0 x using 1
  simp only [pow_zero, mul_one]
  rfl

theorem exists_compact_flow_scaled_curvature_bound
    (g₀ : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (K : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (hinit : ∀ x : M, Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ K * Q) :
    ∃ T : ℝ, compactCurvatureControlTime 3 K / Q < T ∧
      ∃ F : FlowTo g₀ T,
        ∀ t ∈ Icc 0 (compactCurvatureControlTime 3 K / Q), ∀ x : M,
          Real.sqrt (normSq0S (F.S.base.metric t) x 4 (metricRm04 (F.S.base.metric t) x)) ≤
            Real.sqrt (2 * K ^ 2 + 1) * Q := by
  let gQ := scaleMetric Q hQ g₀
  have hnorm : ∀ x : M, Real.sqrt (normSq0S gQ x 4 (metricRm04 gQ x)) ≤ K := by
    intro x
    rw [sqrt_normSq0S_metricRm04_scale]
    exact (div_le_iff₀ hQ).mpr (hinit x)
  obtain ⟨U, hU, ⟨P⟩⟩ := exists_compact_flow_beyond_control_time gQ hdim K hnorm
  have hU' : compactCurvatureControlTime 3 K < U := by simpa only [hdim] using hU
  have heq : scaleMetric Q⁻¹ (inv_pos.mpr hQ) gQ = g₀ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [gQ, scaleMetric_inner, ← mul_assoc, inv_mul_cancel₀ hQ.ne', one_mul]
  let F' := P.scale Q⁻¹ (inv_pos.mpr hQ)
  let F : FlowTo g₀ (Q⁻¹ * U) := { F' with start := F'.start.trans heq }
  have hmetric (t : ℝ) : F.S.base.metric t =
      scaleMetric Q⁻¹ (inv_pos.mpr hQ) (P.S.base.metric (t * Q)) := by
    simp only [F, F', FlowTo.scale_metric, div_inv_eq_mul]
  refine ⟨Q⁻¹ * U, ?_, F, ?_⟩
  · simpa only [div_eq_mul_inv, mul_comm] using (div_lt_div_iff_of_pos_right hQ).mpr hU'
  · intro t ht x
    have htQ : t * Q ∈ Icc 0 (compactCurvatureControlTime 3 K) :=
      ⟨mul_nonneg ht.1 hQ.le, (le_div_iff₀ hQ).mp ht.2⟩
    have hsub : Icc 0 (compactCurvatureControlTime 3 K) ⊆
        (RealTimeInterval.closedOpen 0 U P.time_pos).carrier :=
      fun r hr => ⟨hr.1, hr.2.trans_lt hU'⟩
    let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
    have hb := curvature_bound_from_initial_compact (compactCurvatureControlTime 3 K)
      (compactCurvatureControlTime_pos 3 K).le K (by rw [hdim]) _ P.S P.isSolution hsub
      (fun r hr => ⟨hr.1, hr.2.trans hU'⟩)
      (fun x₀ i j => (P.joint x₀ i j).mono (prod_mono hsub subset_rfl))
      (fun x => by rw [show P.S.base.metric 0 = gQ from P.start]; exact hnorm x)
      (t * Q) htQ x
    rw [hmetric, sqrt_normSq0S_metricRm04_scale, div_inv_eq_mul]
    exact mul_le_mul_of_nonneg_right hb hQ.le

end DifferentialGeometry.PDE.RicciFlow
