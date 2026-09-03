import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.Basic

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MetricSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [PseudoMetricSpace N]

section Constructors

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [T2Space M'] [T2Space (TangentBundle I M')] [SigmaCompactSpace M']
  [ConnectedSpace M'] [T3Space M']


def MapMetricApproximationOn.ofBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    (K : Set M') (eps : ℝ) (p : ℕ) (F : M' → N')
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hpb : SmoothPullbackMetricTensor (I := I) F h)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpb.tensor g x ≤ eps)
    (hcov : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a hpb.tensor g g x ≤ eps) :
    MapMetricApproximationOn (I := I) K eps p F g h where
  eps_pos := heps
  eps_lt_one := heps1
  smoothOn := hsmooth
  pullback := hpb.tensor
  pullback_apply := fun x _ v => hpb.tensor_apply x v
  c0_small := hc0
  cov_deriv_small := hcov

def MapMetricApproximationOn.ofZeroOrderBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    (K : Set M') (eps : ℝ) (F : M' → N')
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hpb : SmoothPullbackMetricTensor (I := I) F h)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpb.tensor g x ≤ eps) :
    MapMetricApproximationOn (I := I) K eps 0 F g h :=
  MapMetricApproximationOn.ofBounds K eps 0 F g h hpb heps heps1 hsmooth hc0
    (by intro a ha ha0 x hx; omega)

def PartialDiffeomorphMetricApproximation.ofBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] (K : Set M') (eps : ℝ) (p : ℕ)
    (Φ : PartialDiffeomorph I I M' N' (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hsub : K ⊆ Φ.source)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hpbF : SmoothPullbackMetricTensor (I := I) (Φ : M' → N') h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M' → N') K)
    (hc0F : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpbF.tensor g x ≤ eps)
    (hcovF : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a hpbF.tensor g g x ≤ eps)
    (hpbR : SmoothPullbackMetricTensor (I := I) (Φ.symm : N' → M') g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ.symm : N' → M') ((Φ : M' → N') '' K))
    (hc0R : ∀ y ∈ (Φ : M' → N') '' K,
      metricTensorErrorNorm (I := I) hpbR.tensor h y ≤ eps)
    (hcovR : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ (Φ : M' → N') '' K,
      tensor02CovDerivNormWith (I := I) a hpbR.tensor h h y ≤ eps) :
    PartialDiffeomorphMetricApproximation (I := I) K eps p Φ g h where
  source_sub := hsub
  forward := MapMetricApproximationOn.ofBounds K eps p (Φ : M' → N') g h hpbF heps heps1
    hsmoothF hc0F hcovF
  reverse := MapMetricApproximationOn.ofBounds ((Φ : M' → N') '' K) eps p
    (Φ.symm : N' → M') h g hpbR heps heps1 hsmoothR hc0R hcovR

def PartialDiffeomorphMetricApproximation.ofZeroOrderBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] (K : Set M') (eps : ℝ)
    (Φ : PartialDiffeomorph I I M' N' (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hsub : K ⊆ Φ.source)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hpbF : SmoothPullbackMetricTensor (I := I) (Φ : M' → N') h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M' → N') K)
    (hc0F : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpbF.tensor g x ≤ eps)
    (hpbR : SmoothPullbackMetricTensor (I := I) (Φ.symm : N' → M') g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ.symm : N' → M') ((Φ : M' → N') '' K))
    (hc0R : ∀ y ∈ (Φ : M' → N') '' K,
      metricTensorErrorNorm (I := I) hpbR.tensor h y ≤ eps) :
    PartialDiffeomorphMetricApproximation (I := I) K eps 0 Φ g h where
  source_sub := hsub
  forward := MapMetricApproximationOn.ofZeroOrderBounds K eps (Φ : M' → N') g h
    hpbF heps heps1 hsmoothF hc0F
  reverse := MapMetricApproximationOn.ofZeroOrderBounds ((Φ : M' → N') '' K) eps
    (Φ.symm : N' → M') h g hpbR heps heps1 hsmoothR hc0R

end Constructors

section

open Set Manifold

variable {M'' : Type u} [TopologicalSpace M''] [ChartedSpace H M''] [IsManifold I ∞ M'']
  [T2Space M''] [T2Space (TangentBundle I M'')] [SigmaCompactSpace M'']
  [ConnectedSpace M''] [T3Space M'']
  [MetricSpace M''] [Nonempty M'']
variable {N'' : Type u} [TopologicalSpace N''] [ChartedSpace H N'']
  [nManifold : IsManifold I ∞ N'']
  [T2Space N''] [T2Space (TangentBundle I N'')] [SigmaCompactSpace N'']
  [ConnectedSpace N''] [T3Space N'']

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M'')] [SigmaCompactSpace M''] [ConnectedSpace M''] [T3Space M'']
  [T2Space (TangentBundle I N'')] [SigmaCompactSpace N''] [ConnectedSpace N''] [T3Space N''] in
theorem exists_partial_diffeomorph_metric_approximation_of_bounds
    (g : SmoothRiemannianMetric I M'') (h : SmoothRiemannianMetric I N'')
    (Ok : M'') (Oℓ : N'') (r ε : ℝ) (p : ℕ) (U : Set M'')
    (hU : IsOpen U) (hOkU : Ok ∈ U) (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M'' → N'')
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U) (hbase : F Ok = Oℓ)
    (heps : 0 < ε) (heps1 : ε < 1)
    (hpbF : SmoothPullbackMetricTensor (I := I) F h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) F (Metric.closedBall Ok r))
    (hc0F : ∀ x ∈ Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbF.tensor g x ≤ ε)
    (hcovF : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ Metric.closedBall Ok r,
      tensor02CovDerivNormWith (I := I) a hpbF.tensor g g x ≤ ε)
    (hpbR : SmoothPullbackMetricTensor (I := I) (Function.invFunOn F U) g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Function.invFunOn F U)
      (F '' Metric.closedBall Ok r))
    (hc0R : ∀ y ∈ F '' Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbR.tensor h y ≤ ε)
    (hcovR : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ F '' Metric.closedBall Ok r,
      tensor02CovDerivNormWith (I := I) a hpbR.tensor h h y ≤ ε) :
    ∃ Phi : PartialDiffeomorph I I M'' N'' (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) (Metric.closedBall Ok r) ε p Phi g h) := by
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) N'' := by
    change IsManifold I ∞ N''
    exact nManifold
  exact
    exists_partial_diffeomorph_metric_approximation g h Ok Oℓ r ε p U hU hOkU hKU F hloc
      hinj hbase
      (MapMetricApproximationOn.ofBounds (Metric.closedBall Ok r) ε p F g h hpbF heps heps1
        hsmoothF hc0F hcovF)
      (MapMetricApproximationOn.ofBounds (F '' Metric.closedBall Ok r) ε p
        (Function.invFunOn F U) h g hpbR heps heps1 hsmoothR hc0R hcovR)

omit [Module.Finite ℝ E] in
omit [T2Space (TangentBundle I M'')] [ConnectedSpace M''] [T3Space M'']
    [T2Space (TangentBundle I N'')] [ConnectedSpace N''] [T3Space N''] in
omit [FiniteDimensional ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M'')] [SigmaCompactSpace M''] [ConnectedSpace M''] [T3Space M''] [T2Space (TangentBundle I N'')] [SigmaCompactSpace N''] [ConnectedSpace N''] [T3Space N''] in
theorem exists_partial_diffeomorph_metric_approximation_of_zero_order_bounds
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M'') (h : SmoothRiemannianMetric I N'')
    (Ok : M'') (Oℓ : N'') (r ε : ℝ) (U : Set M'')
    (hU : IsOpen U) (hOkU : Ok ∈ U) (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M'' → N'')
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U) (hbase : F Ok = Oℓ)
    (heps : 0 < ε) (heps1 : ε < 1)
    (hpbF : SmoothPullbackMetricTensor (I := I) F h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) F (Metric.closedBall Ok r))
    (hc0F : ∀ x ∈ Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbF.tensor g x ≤ ε)
    (hpbR : SmoothPullbackMetricTensor (I := I) (Function.invFunOn F U) g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Function.invFunOn F U)
      (F '' Metric.closedBall Ok r))
    (hc0R : ∀ y ∈ F '' Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbR.tensor h y ≤ ε) :
    ∃ Phi : PartialDiffeomorph I I M'' N'' (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) (Metric.closedBall Ok r) ε 0 Phi g h) :=
  exists_partial_diffeomorph_metric_approximation_of_bounds g h Ok Oℓ r ε 0 U hU hOkU hKU F hloc hinj hbase heps heps1
    hpbF hsmoothF hc0F (by intro a ha ha0 x hx; omega)
    hpbR hsmoothR hc0R (by intro a ha ha0 y hy; omega)

end

end HCGCompactness
end DifferentialGeometry
