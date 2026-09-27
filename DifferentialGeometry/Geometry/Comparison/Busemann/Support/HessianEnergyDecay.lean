import DifferentialGeometry.Geometry.Comparison.Busemann.Support.HorosphereHessianLimit
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.LineSupportRiccati

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set MeasureTheory
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem laplacian_eq_sum_hessian (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ∑ i, hessFun (I := I) g f x (b i) (b i) := by
  classical
  rw [lap_eq_hess_on (I := I) g hU hf hx,
    metricTracePair0SAt_eq_sum_basis (I := I) g b
      (fun i j => if i = j then 1 else 0)
      (metricInverseInBasis_of_orthonormal (I := I) g b hON)]
  simp only [hessTensorAt_apply, ite_mul, one_mul, zero_mul]
  simp

theorem lineDistanceSupport_laplacian_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s R : ℝ) (hsR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    laplacian (I := I) (LeviCivita (I := I) g) g (lineDistanceSupport eta R) (eta s) ≤ 0 := by
  classical
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨L, _, hL, _, htrace⟩ :=
    exists_lineDistanceSupport_opposite_hessian_limits (I := I) g hEnorm hRic p u hu hiso s
  have hb : ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (eta s)),
      ∀ i j, g.inner (eta s) (b i) (b j) = if i = j then 1 else 0 :=
    exists_orthonormal_basis (I := I) g (eta s)
  obtain ⟨b, hON⟩ := hb
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => hL (b i) (b i))
  rw [htrace b hON] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop R] with S hS
  obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
    g hEnorm p u hu hiso s R hsR
  rw [laplacian_eq_sum_hessian g hU hf hx b hON]
  exact Finset.sum_le_sum fun i _ =>
    lineDistanceSupport_hessian_mono (I := I) g hEnorm p u hu hiso s R S hsR hS (b i)

theorem tendsto_lineDistanceSupport_laplacian_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    Tendsto (fun R => laplacian (I := I) (LeviCivita (I := I) g) g
      (lineDistanceSupport eta R) (eta s)) atTop (𝓝 0) := by
  have hden : Tendsto (fun R : ℝ => R - s) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (b + s)] with R hR
    linarith
  have hlow : Tendsto (fun R : ℝ => -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (R - s)))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using (hden.const_div_atTop ((Module.finrank ℝ E - 1 : ℕ) : ℝ)).neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop s] with R hR
    exact lineDistanceSupport_laplacian_ge (I := I) g hEnorm hRic p u hu hiso s R hR
  · filter_upwards [eventually_gt_atTop s] with R hR
    exact lineDistanceSupport_laplacian_nonpos (I := I) g hEnorm hRic p u hu hiso s R hR

theorem lineDistanceSupport_hessian_energy_bounds
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (a b R : ℝ) (hab : a ≤ b) (hbR : b < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    0 ≤ (∫ s in a..b, chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s)) ∧
    (∫ s in a..b, chartHessFrobeniusSq (I := I) g (lineDistanceSupport eta R) (eta s)) ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (R - b) := by
  constructor
  · exact intervalIntegral.integral_nonneg hab fun s hs =>
      lineDistanceSupport_hessianNorm_nonneg (I := I) g hEnorm p u hu hiso s R (hs.2.trans_lt hbR)
  · have henergy := integral_lineDistanceSupport_hessianNorm_le (I := I)
      g hEnorm hRic p u hu hiso a b R hab hbR
    have ha := lineDistanceSupport_laplacian_nonpos (I := I)
      g hEnorm hRic p u hu hiso a R (hab.trans_lt hbR)
    have hb := lineDistanceSupport_laplacian_ge (I := I)
      g hEnorm hRic p u hu hiso b R hbR
    dsimp only at henergy ha hb
    linarith

theorem tendsto_lineDistanceSupport_hessian_energy_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (a b : ℝ) (hab : a ≤ b) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    Tendsto (fun R => ∫ s in a..b, chartHessFrobeniusSq (I := I) g
      (lineDistanceSupport eta R) (eta s)) atTop (𝓝 0) := by
  have hden : Tendsto (fun R : ℝ => R - b) atTop atTop := by
    refine tendsto_atTop.mpr fun c => ?_
    filter_upwards [eventually_ge_atTop (c + b)] with R hR
    linarith
  apply squeeze_zero' ?_ ?_ (hden.const_div_atTop ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  · filter_upwards [eventually_gt_atTop b] with R hR
    exact (lineDistanceSupport_hessian_energy_bounds (I := I)
      g hEnorm hRic p u hu hiso a b R hab hR).1
  · filter_upwards [eventually_gt_atTop b] with R hR
    exact (lineDistanceSupport_hessian_energy_bounds (I := I)
      g hEnorm hRic p u hu hiso a b R hab hR).2

end DifferentialGeometry.Geometry.Topology

end
