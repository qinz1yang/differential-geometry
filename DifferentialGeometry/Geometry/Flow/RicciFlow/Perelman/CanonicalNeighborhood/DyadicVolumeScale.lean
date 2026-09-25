import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactSlabVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure MeasureTheory Set
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [I.Boundaryless]


theorem exists_scalar_doubling_scale [T2Space (TangentBundle I M)]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hdim : 2 ≤ Module.finrank ℝ E) {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsScalarControlled) :
    ∃ B' : FlowMetricBall S time,
      B'.center = B.center ∧ B'.radius ≤ B.radius ∧ B'.IsScalarControlled ∧
      B'.volume.toReal / B'.radius ^ Module.finrank ℝ E ≤
        B.volume.toReal / B.radius ^ Module.finrank ℝ E ∧
      B'.volume.toReal ≤ (3 : ℝ) ^ Module.finrank ℝ E *
        (riemannianVolumeMeasure I M (S.base.metric (time : ℝ))
          (riemannianBallOf (I := I) (S.base.metric (time : ℝ)) B'.center (B'.radius / 2))).toReal := by
  let n := Module.finrank ℝ E
  let V : ℕ → ℝ := fun j => (B.dyadic j).volume.toReal
  let W : ℕ → ℝ := fun j => V j / (B.dyadic j).radius ^ n
  have hrad : ∀ j : ℕ, (B.dyadic j).radius ≤ B.radius := by
    intro j
    rw [FlowMetricBall.dyadic_radius]
    exact mul_le_of_le_one_left B.radius_pos.le
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hK : ({(time : ℝ)} : Set ℝ) ⊆ D.carrier := by
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    exact time.2
  obtain ⟨ε, hε, hvol⟩ := family_compact_slab_volume S.family.metric hG
    isCompact_singleton hK B.radius_pos
  let μ := riemannianVolumeMeasure I M (S.base.metric (time : ℝ))
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hfinite (j : ℕ) : (B.dyadic j).volume ≠ ⊤ := by
    change volumeMeasureOn S.family time (B.dyadic j).set ≠ ⊤
    rw [volumeMeasureOn_eq_metric, SolutionOn.family_metric]
    exact measure_ne_top μ _
  have hlow : ∀ j : ℕ, ε ≤ W j := by
    intro j
    have hv : ENNReal.ofReal ε * ENNReal.ofReal (B.dyadic j).radius ^ n ≤
        (B.dyadic j).volume := by
      simpa only [n, FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
        FlowMetricBall.dyadic, FlowMetricBall.shrink,
        volumeMeasureOn_eq_metric, SolutionOn.family_metric] using
          hvol (time : ℝ) (Set.mem_singleton _) B.center (B.dyadic j).radius
            (B.dyadic j).radius_pos (hrad j)
    have hvreal := ENNReal.toReal_mono (hfinite j) hv
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le,
      ENNReal.toReal_ofReal (B.dyadic j).radius_pos.le] at hvreal
    exact (le_div_iff₀ (pow_pos (B.dyadic j).radius_pos n)).2 hvreal
  have hn : n ≠ 0 := by dsimp only [n]; omega
  have hq : (2 / 3 : ℝ) ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hn
  obtain ⟨j, hjdrop, hjbase⟩ := DifferentialGeometry.Analysis.Calculus.exists_drop_lower W
    (q := (2 / 3 : ℝ) ^ n) (by positivity) hq
    (fun k => div_nonneg ENNReal.toReal_nonneg (pow_nonneg (B.dyadic k).radius_pos.le n))
    hε (Filter.Eventually.of_forall hlow)
  refine ⟨B.dyadic j, rfl, hrad j,
    FlowMetricBall.scalarControlled_of_radius_le B (B.dyadic j) rfl (hrad j) hB,
    ?_, ?_⟩
  · simpa only [W, V, n, FlowMetricBall.dyadic, FlowMetricBall.shrink,
      pow_zero, one_mul] using hjbase
  · have hrn : 0 < (B.dyadic j).radius ^ n := pow_pos (B.dyadic j).radius_pos n
    have htwo : 0 < (2 : ℝ) ^ n := by positivity
    have hthree : 0 < (3 : ℝ) ^ n := by positivity
    have hsuc : (B.dyadic (j + 1)).radius ^ n = (B.dyadic j).radius ^ n / (2 : ℝ) ^ n := by
      rw [FlowMetricBall.dyadic_succ_radius, div_pow]
    have hdrop : ((2 : ℝ) ^ n / (3 : ℝ) ^ n) *
        (V j / (B.dyadic j).radius ^ n) <
          V (j + 1) / ((B.dyadic j).radius ^ n / (2 : ℝ) ^ n) := by
      simpa only [W, hsuc, div_pow] using hjdrop
    have hV : V j < (3 : ℝ) ^ n * V (j + 1) := by
      have hcross := (div_lt_div_iff₀ hthree (div_pos hrn htwo)).1
        (show (2 : ℝ) ^ n * (V j / (B.dyadic j).radius ^ n) / (3 : ℝ) ^ n <
          V (j + 1) / ((B.dyadic j).radius ^ n / (2 : ℝ) ^ n) from by
            simpa only [div_mul_eq_mul_div] using hdrop)
      have hcancel : ((2 : ℝ) ^ n * (V j / (B.dyadic j).radius ^ n)) *
          ((B.dyadic j).radius ^ n / (2 : ℝ) ^ n) = V j := by
        field_simp [hrn.ne', htwo.ne']
      rw [hcancel] at hcross
      simpa only [mul_comm] using hcross
    have hVsuc : V (j + 1) =
        (riemannianVolumeMeasure I M (S.base.metric (time : ℝ))
          (riemannianBallOf (I := I) (S.base.metric (time : ℝ))
            (B.dyadic j).center ((B.dyadic j).radius / 2))).toReal := by
      simp only [V, FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
        volumeMeasureOn_eq_metric, SolutionOn.family_metric,
        FlowMetricBall.dyadic_succ_radius, riemannianBallOf]
      rfl
    rw [hVsuc] at hV
    exact hV.le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
