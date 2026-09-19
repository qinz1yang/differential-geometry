import DifferentialGeometry.Analysis.Calculus.Derivative.EndpointSpatialDerivative
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.ConnectionLimits
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.CoordinateBounds
import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.Frame
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.CoordinateConvergence
import DifferentialGeometry.Analysis.Calculus.Derivative.EndpointIntegrableLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialIntegrability
import DifferentialGeometry.Topology.Manifold.ChartNeighborhood
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceNorm
import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceContinuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Topology Manifold ContDiff BigOperators

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

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology Manifold ContDiff BigOperators


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_tendstoUniformlyOn_chartChristoffel_left_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (α : M)
    {a b B : ℝ} (hab : a < b) (hregular : Ioo a b ⊆ D.regular)
    {K : Set M} (hK : IsCompact K) (hchart : K ⊆ coordinateFrameSet (I := I) α)
    {U : Set E} (hU : U ⊆ (extChartAt I α).target)
    (hUK : MapsTo (extChartAt I α).symm U K)
    (hmetric : ∀ t ∈ Ioo a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (F : ℝ → ℝ) (hF : IntervalIntegrable F volume a b)
    (hRic : ∀ t ∈ Ioo a b, ∀ x ∈ K,
      Real.sqrt (normSq0S (S.family.metric t) x 3
        (ricCovTower (S.family.metric t) (S.family.metric t) 1 x)) ≤ F t)
    (i j k : Fin (Module.finrank ℝ E)) :
    ∃ Γ : E → ℝ, TendstoUniformlyOn
      (fun t => chartChristoffel (I := I) (S.family.metric t) α i j k)
      Γ (𝓝[Ioo a b] a) U := by
  classical
  obtain ⟨C, hCnonneg, hC⟩ :=
    exists_bound_christoffel_evolution_rhs_by_nablaRic_on_compact R α hK hchart B
  let γ := fun t x p q r => christoffelSymbolInFrame (S.family.connection t)
    (coordinateFrameAt (I := I) α) (coordinateFrameAt_isLocalFrame_one α) x p q r
  let d := fun t x p q r => deriv (fun s => γ s x p q r) t
  have hd : ∀ t ∈ Ioo a b, ∀ x ∈ K, ∀ p q r,
      HasDerivAt (fun s => γ s x p q r) (d t x p q r) t := by
    intro t ht x hx p q r
    exact (christoffel_hasDerivAt_of_solution S hS α ⟨t, hregular ht⟩
      (hchart hx) p q r).differentiableAt.hasDerivAt
  have hb : ∀ t ∈ Ioo a b, ∀ x ∈ K, ∀ p q r,
      |d t x p q r| ≤ C * F t := by
    intro t ht x hx p q r
    have hder := christoffel_hasDerivAt_of_solution S hS α ⟨t, hregular ht⟩
      (hchart hx) p q r
    change |deriv (fun s => γ s x p q r) t| ≤ C * F t
    rw [hder.deriv]
    have hc := hC S t (hmetric t ht) x hx p q r
    rw [Real.norm_eq_abs] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left (hRic t ht x hx) hCnonneg)
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
  let D := fun t y => ∑ p, ∑ q, ∑ r,
    c p q r * d t ((extChartAt I α).symm y) q p r
  let L := ∑ p, ∑ q, ∑ r, |c p q r|
  apply exists_tendstoUniformlyOn_left_endpoint_of_integrable_deriv_bound hab
    (fun t => chartChristoffel (I := I) (S.family.metric t) α i j k) D
    (fun t => (L * C) * F t)
  · intro t ht y hy
    rw [show (fun s => chartChristoffel (I := I) (S.family.metric s) α i j k y) =
      (fun s => ∑ p, ∑ q, ∑ r, c p q r * γ s ((extChartAt I α).symm y) q p r) by
        funext s; exact hbridge s y hy]
    exact HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ =>
      HasDerivAt.fun_sum fun r _ => (hd t ht _ (hUK hy) q p r).const_mul (c p q r)
  · intro t ht y hy
    have h := abs_sub_sum_three_le c
      (fun p q r => d t ((extChartAt I α).symm y) q p r) (fun _ _ _ => 0)
      (fun p q r => by simpa only [sub_zero] using hb t ht _ (hUK hy) q p r)
    simpa only [D, L, mul_zero, Finset.sum_const_zero, sub_zero, Real.norm_eq_abs,
      mul_assoc] using h
  · exact hF.const_mul (L * C)

theorem tendstoUniformlyOn_chartChristoffel_left_endpoint_of_integrable_nablaRic_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (α : M)
    {a b B C : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    {K : Set M} (hK : IsCompact K) (hchart : K ⊆ coordinateFrameSet (I := I) α)
    {U : Set E} (hU : IsOpen U) (hUchart : U ⊆ interior (extChartAt I α).target)
    (hUK : MapsTo (extChartAt I α).symm U K)
    (hmetric : ∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0 C)
    (F : ℝ → ℝ) (hF : IntervalIntegrable F volume a b)
    (hRic : ∀ t ∈ Ioo a b, ∀ x ∈ K,
      Real.sqrt (normSq0S (S.family.metric t) x 3
        (ricCovTower (S.family.metric t) (S.family.metric t) 1 x)) ≤ F t)
    (i j k : Fin (Module.finrank ℝ E)) :
    TendstoUniformlyOn
      (fun t => chartChristoffel (I := I) (S.family.metric t) α i j k)
      (chartChristoffel (I := I) (S.family.metric a) α i j k) (𝓝[Ioo a b] a) U := by
  classical
  let : NeBot (𝓝[Ioo a b] a) := left_nhdsWithin_Ioo_neBot hab
  have hex := fun p q r => exists_tendstoUniformlyOn_chartChristoffel_left_endpoint
    S hS R α hab hregular hK hchart (hUchart.trans interior_subset) hUK
    (fun t ht => hmetric t (Ioo_subset_Icc_self ht)) F hF hRic p q r
  choose Γ hΓ using hex
  have hgram : ∀ p q, TendstoLocallyUniformlyOn
      (fun t => chartGramOnE (S.family.metric t) α p q)
      (chartGramOnE (S.family.metric a) α p q) (𝓝[Ioo a b] a) U := by
    intro p q
    exact (tendstoUniformlyOn_chartGramOnE_left_endpoint S hS hcarrier hregular R α
      hK hchart hmetric hShi hUK p q).tendstoLocallyUniformlyOn
  have heq := DifferentialGeometry.Geometry.Connection.chartChristoffel_limit_eq
    (fun t => S.family.metric t) (S.family.metric a) α hU hUchart Γ hgram
    (fun p q r => (hΓ p q r).tendstoLocallyUniformlyOn)
  exact (hΓ i j k).congr_right fun x hx => heq x hx i j k

end DifferentialGeometry.PDE.RicciFlow

end


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem tendsto_chartChristoffel_left_endpoint_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b C : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (x : M) (i j k : Fin (Module.finrank ℝ E)) :
    Tendsto (fun t => chartChristoffel (I := I) (S.family.metric t) x i j k
      (extChartAt I x x)) (𝓝[Ioo a b] a)
      (𝓝 (chartChristoffel (I := I) (S.family.metric a) x i j k (extChartAt I x x))) := by
  classical
  obtain ⟨F, hF, hFbound⟩ := exists_integrable_nablaRic_bound_on_initial_interval
    S hS hcarrier hregular hcomplete hC hcurv
  obtain ⟨K, U, hK, hU, _hxK, hxU, hKchart, hUchart, hUK⟩ :=
    DifferentialGeometry.Topology.exists_compact_extChartAt_neighborhood (I := I) x
  have hreg : Ioo a b ⊆ D.regular := fun t ht => hregular ⟨ht.1, ht.2.le⟩
  let A := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hquad : ∀ t ∈ Icc a b, ∀ y ∈ K, ∀ v : TangentSpace I y,
      |S.ricciAt t y (vec2 v v)| ≤ A * (S.base.metric t).inner y v v := by
    intro t ht y _ v
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor, A] using
      ricci_quadratic_form_bound_of_solution_curvature_bound S y v (hcurv t ht y)
  have heq := metric_uniform_equivalent_on_closed_interval_of_solution
    S hS hab hcarrier hreg (left_mem_Icc.mpr hab.le) hA hquad
  let B := Real.exp (2 * A * (b - a))
  have hmetric : ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn K (S.family.metric a) (S.family.metric t) B := by
    intro t ht
    apply metricUniformEquivalentOn_of_le (heq 0 t ht)
    simp only [metricEquivalenceFactor, one_mul, B]
    apply Real.exp_le_exp.mpr
    have hdist : |t - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact sub_le_sub_right ht.2 a
    exact mul_le_mul_of_nonneg_left hdist (mul_nonneg (by norm_num) hA)
  have hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 0
      (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4 * C)) := by
    intro n hn q t ht y _
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    apply Real.sqrt_le_sqrt
    have htrace := ricTower_normSq_le S t 0 y
    simpa [nablaKRm04Field_zero] using htrace.trans
      (mul_le_mul_of_nonneg_left (hcurv t ht y) (by positivity))
  have hchart : K ⊆ coordinateFrameSet (I := I) x := by
    simpa only [coordinateFrameSet, coordinateTrivializationAt,
      trivializationAt_baseSet_eq_chartAt_source, extChartAt_source] using hKchart
  exact (tendstoUniformlyOn_chartChristoffel_left_endpoint_of_integrable_nablaRic_bound
    S hS (S.family.metric a) x hab hcarrier hreg hK hchart hU hUchart hUK hmetric hShi
      F hF (fun t ht y _ => hFbound t ⟨ht.1, ht.2.le⟩ y) i j k).tendsto_at hxU

end DifferentialGeometry.PDE.RicciFlow

end


set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open scoped Manifold _root_.Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem continuousWithinAt_initial_connection_pairing_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b C : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (x : M) (u w v : TangentSpace I x) :
    ContinuousWithinAt
      (fun r => (S.base.metric a).inner x (CovariantDerivative.difference
        (LeviCivita (I := I) (S.base.metric r))
        (LeviCivita (I := I) (S.base.metric a)) x u w) v) (Icc a b) a := by
  have hconn : ∀ i j k : Fin (Module.finrank ℝ E),
      Tendsto (fun t => chartChristoffel (I := I) (S.base.metric t) x i j k
        (extChartAt I x x)) (𝓝[Ioo a b] a)
        (𝓝 (chartChristoffel (I := I) (S.base.metric a) x i j k (extChartAt I x x))) := by
    intro i j k
    simpa only [SolutionOn.family_metric] using
      tendsto_chartChristoffel_left_endpoint_of_complete_bounded_curvature
        S hS hab hcarrier hregular hcomplete hC hcurv x i j k
  have hlim := tendsto_leviCivita_difference_pairing_zero_of_chartChristoffel
    S.base.metric (S.base.metric a) (S.base.metric a) x hconn u w v
  have hz := connectionDifferenceLowAt_self (I := I) (S.base.metric a) x
  have hz' := congrArg (fun A : Tensor0SSpace 3 I x =>
      Tensor0SSpace.eval A (vec3 (I := I) w u v)) hz
  rw [connectionDifferenceLowAt_apply] at hz'
  have hzero : (S.base.metric a).inner x (CovariantDerivative.difference
      (LeviCivita (I := I) (S.base.metric a))
      (LeviCivita (I := I) (S.base.metric a)) x u w) v = 0 := by
    simpa [vec3, Tensor0SSpace.eval, metricCov, LeviCivita] using hz'
  have hi : ContinuousWithinAt
      (fun r => (S.base.metric a).inner x (CovariantDerivative.difference
        (LeviCivita (I := I) (S.base.metric r))
        (LeviCivita (I := I) (S.base.metric a)) x u w) v) (Ioi a) a :=
    (continuousWithinAt_Ioo_iff_Ioi hab).mp (by
      change Tendsto _ _ _
      dsimp only
      rw [hzero]
      exact hlim)
  exact (continuousWithinAt_Icc_iff_Ici hab).mpr (by
    simpa only [Ioi_insert] using hi.insert)

end DifferentialGeometry.PDE.RicciFlow

end
