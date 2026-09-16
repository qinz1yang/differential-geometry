import DifferentialGeometry.Analysis.Calculus.Derivative.EndpointSpatialDerivative
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.ConnectionLimits
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.CoordinateBounds
import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.Frame
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.CoordinateConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology Manifold ContDiff BigOperators

private theorem abs_sub_sum_three_le
    {J : Type*} [Fintype J] (c f g : J → J → J → ℝ) {A : ℝ}
    (h : ∀ i j k, |f i j k - g i j k| ≤ A) :
    |(∑ i, ∑ j, ∑ k, c i j k * f i j k) -
      (∑ i, ∑ j, ∑ k, c i j k * g i j k)| ≤
      (∑ i, ∑ j, ∑ k, |c i j k|) * A := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    |∑ i, ∑ j, ∑ k, c i j k * (f i j k - g i j k)|
        ≤ ∑ i, ∑ j, ∑ k, |c i j k * (f i j k - g i j k)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, ∑ k, |c i j k| * A := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h i j k) (abs_nonneg _)
    _ = _ := by simp_rw [Finset.sum_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_tendstoUniformlyOn_chartChristoffel_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (α : M)
    {a b B KShi : ℝ} (hab : a < b) (hregular : Ioo a b ⊆ D.regular)
    {K : Set M} (hK : IsCompact K) (hchart : K ⊆ coordinateFrameSet (I := I) α)
    {U : Set E} (hU : U ⊆ (extChartAt I α).target)
    (hUK : MapsTo (extChartAt I α).symm U K)
    (hmetric : ∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 1 KShi)
    (i j k : Fin (Module.finrank ℝ E)) :
    ∃ Γ : E → ℝ, TendstoUniformlyOn
      (fun t => chartChristoffel (I := I) (S.family.metric t) α i j k)
      Γ (𝓝[Ioo a b] b) U := by
  classical
  obtain ⟨C, _, hC⟩ := exists_bound_christoffel_evolution_rhs_on_compact
    R α hK hchart a b B KShi
  let γ := fun t x p q r => christoffelSymbolInFrame (S.family.connection t)
    (coordinateFrameAt (I := I) α) (coordinateFrameAt_isLocalFrame_one α) x p q r
  have hLip : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x ∈ K, ∀ p q r,
      |γ s x p q r - γ t x p q r| ≤ C * |s - t| := by
    intro s hs t ht x hx p q r
    have hdiff : ∀ u ∈ Ioo a b, DifferentiableAt ℝ (fun v => γ v x p q r) u := by
      intro u hu
      exact (christoffel_hasDerivAt_of_solution S hS α ⟨u, hregular hu⟩
        (hchart hx) p q r).differentiableAt
    have hbound : ∀ u ∈ Ioo a b, ‖deriv (fun v => γ v x p q r) u‖ ≤ C := by
      intro u hu
      rw [(christoffel_hasDerivAt_of_solution S hS α ⟨u, hregular hu⟩
        (hchart hx) p q r).deriv]
      exact hC S hmetric hShi u ⟨hu.1.le, hu.2.le⟩ x hx p q r
    simpa only [Real.norm_eq_abs] using
      (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le hdiff hbound ht hs
  let c := fun p q r =>
    (Module.finBasis ℝ E).repr (chartModelBasis E j) p *
      (Module.finBasis ℝ E).repr (chartModelBasis E i) q *
        (chartModelBasis E).repr (Module.finBasis ℝ E r) k
  have hbridge : ∀ t y, y ∈ U →
      chartChristoffel (I := I) (S.family.metric t) α i j k y =
        ∑ p, ∑ q, ∑ r, c p q r * γ t ((extChartAt I α).symm y) q p r := by
    intro t y hy
    have h := chartChristoffel_eq_sum_coordinateFrame (S.family.metric t) α
      (hchart (hUK hy)) i j k
    rw [(extChartAt I α).right_inv (hU hy)] at h
    exact h
  apply exists_tendstoUniformlyOn_right_endpoint_of_time_lipschitz
    (C := (∑ p, ∑ q, ∑ r, |c p q r|) * C) hab
  intro s hs t ht y hy
  rw [Real.dist_eq, hbridge s y hy, hbridge t y hy]
  exact (abs_sub_sum_three_le c
    (fun p q r => γ s ((extChartAt I α).symm y) q p r)
    (fun p q r => γ t ((extChartAt I α).symm y) q p r)
    (fun p q r => hLip s hs t ht _ (hUK hy) q p r)).trans_eq (mul_assoc _ _ _).symm

private theorem tendstoUniformlyOn_chartChristoffel_right_endpoint_of_metric_convergence
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (α : M)
    {a b B KShi : ℝ} (hab : a < b) (hregular : Ioo a b ⊆ D.regular)
    {K : Set M} (hK : IsCompact K) (hchart : K ⊆ coordinateFrameSet (I := I) α)
    {U : Set E} (hU : IsOpen U) (hUchart : U ⊆ interior (extChartAt I α).target)
    (hUK : MapsTo (extChartAt I α).symm U K)
    (hmetric : ∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 1 KShi)
    (hgram : ∀ i j, TendstoLocallyUniformlyOn
      (fun t => chartGramOnE (I := I) (S.family.metric t) α i j)
      (chartGramOnE (I := I) (S.family.metric b) α i j)
      (𝓝[Ioo a b] b) U)
    (i j k : Fin (Module.finrank ℝ E)) :
    TendstoUniformlyOn
      (fun t => chartChristoffel (I := I) (S.family.metric t) α i j k)
      (chartChristoffel (I := I) (S.family.metric b) α i j k) (𝓝[Ioo a b] b) U := by
  classical
  let : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  have hex := fun p q r => exists_tendstoUniformlyOn_chartChristoffel_right_endpoint
    S hS R α hab hregular hK hchart (hUchart.trans interior_subset) hUK hmetric hShi p q r
  choose Γ hΓ using hex
  have heq := DifferentialGeometry.Geometry.Connection.chartChristoffel_limit_eq
    (fun t => S.family.metric t) (S.family.metric b) α hU hUchart Γ hgram
      (fun p q r => (hΓ p q r).tendstoLocallyUniformlyOn)
  exact (hΓ i j k).congr_right fun x hx => heq x hx i j k

theorem tendstoUniformlyOn_chartChristoffel_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (α : M)
    {a b B KShi : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    {K : Set M} (hK : IsCompact K) (hchart : K ⊆ coordinateFrameSet (I := I) α)
    {U : Set E} (hU : IsOpen U) (hUchart : U ⊆ interior (extChartAt I α).target)
    (hUK : MapsTo (extChartAt I α).symm U K)
    (hmetric : ∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 1 KShi)
    (i j k : Fin (Module.finrank ℝ E)) :
    TendstoUniformlyOn
      (fun t => chartChristoffel (I := I) (S.family.metric t) α i j k)
      (chartChristoffel (I := I) (S.family.metric b) α i j k) (𝓝[Ioo a b] b) U := by
  apply tendstoUniformlyOn_chartChristoffel_right_endpoint_of_metric_convergence
    S hS R α hab hregular hK hchart hU hUchart hUK hmetric hShi
  intro p q
  have hShi₀ : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0 KShi :=
    fun n hn => hShi n (hn.trans (by decide))
  exact (tendstoUniformlyOn_chartGramOnE_right_endpoint S hS hab hcarrier hregular R α
    hK hchart hmetric hShi₀ hUK p q).tendstoLocallyUniformlyOn

end DifferentialGeometry.PDE.RicciFlow
