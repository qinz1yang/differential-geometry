import DifferentialGeometry.Geometry.Metric.Coordinates.ChartFrameBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_chartGramMatrix_right_endpoint_bound
    (R : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hchart : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet)
    (B C : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
      ∀ {a b : ℝ}, a < b → Icc a b ⊆ D.carrier → Ioo a b ⊆ D.regular →
      (∀ t ∈ Icc a b, ∀ x ∈ K, ∀ v : TangentSpace I x,
        (S.family.metric t).inner x v v ≤ B * R.inner x v v) →
      MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0 C →
      ∀ t ∈ Icc a b, ∀ x ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        dist (chartGramMatrix (S.family.metric b) α x i j)
          (chartGramMatrix (S.family.metric t) α x i j) ≤ L * (b - t) := by
  obtain ⟨Rf, _, hframe⟩ := exists_pos_bound_chartBasisVec_on_compact R α hK hchart
  refine ⟨max 0 (2 * C * max 0 B * (Rf * Rf)), le_max_left _ _, ?_⟩
  intro D S hS a b hab hcarrier hregular hmetric hShi t ht x hx i j
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
  have hderiv (s : ℝ) (hs : s ∈ Icc t b) :
      HasDerivWithinAt (fun r => chartGramMatrix (S.family.metric r) α x i j)
        (-2 * S.ricciAt s x
          (vec2 (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)))
        (Icc t b) s :=
    (metric_inner_hasDerivWithinAt_on_closed_interval S hS hab hcarrier hregular
      (hsub hs) x (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)).mono hsub
  have hbound (s : ℝ) (hs : s ∈ Ico t b) :
      ‖-2 * S.ricciAt s x
        (vec2 (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x))‖ ≤
      max 0 (2 * C * max 0 B * (Rf * Rf)) := by
    have hs' : s ∈ Icc a b := ⟨ht.1.trans hs.1, hs.2.le⟩
    have hRic : Real.sqrt (normSq0S (S.family.metric s) x 2 (S.ricciAt s x)) ≤ C :=
      hShi 0 le_rfl 0 s hs' x hx
    exact (norm_ricci_pairing_le_of_metric_le S R (le_max_left 0 B) x
      (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)
      (fun v => (hmetric s hs' x hx v).trans
        (mul_le_mul_of_nonneg_right (le_max_right 0 B) (metric_inner_self_nonneg R x v))) hRic (hframe x hx i) (hframe x hx j)).trans
      (le_max_right _ _)
  simpa only [dist_eq_norm] using
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b (right_mem_Icc.mpr ht.2)

theorem tendstoUniformlyOn_chartGramOnE_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hchart : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet)
    {B C : ℝ}
    (hmetric : ∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0 C)
    {U : Set E} (hU : MapsTo (extChartAt I α).symm U K)
    (i j : Fin (Module.finrank ℝ E)) :
    TendstoUniformlyOn (fun t => chartGramOnE (S.family.metric t) α i j)
      (chartGramOnE (S.family.metric b) α i j) (𝓝[Ioo a b] b) U := by
  obtain ⟨L, _, hL⟩ := exists_chartGramMatrix_right_endpoint_bound R α hK hchart B C
  have hmod : Tendsto (fun t : ℝ => L * (b - t)) (𝓝[Ioo a b] b) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => L * (b - t)) b := by fun_prop
    simpa only [sub_self, mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_mem_nhdsWithin, hmod.eventually_lt_const hε]
    with t ht hsmall y hy
  exact (hL S hS hab hcarrier hregular
    (fun s hs x hx v => ((hmetric s hs).2 x hx v).2) hShi t (Ioo_subset_Icc_self ht)
    ((extChartAt I α).symm y) (hU hy) i j).trans_lt hsmall

end DifferentialGeometry.PDE.RicciFlow
