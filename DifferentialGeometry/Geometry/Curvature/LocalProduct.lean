import DifferentialGeometry.Geometry.Metric.LocalProduct
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

open Set TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [I.Boundaryless] [J.Boundaryless] [T2Space M] [T2Space N]
variable [SigmaCompactSpace N]

theorem exists_metric_scalar_eq_of_local_product_partialDiffeomorph
    (g : SmoothRiemannianMetric I M) (K : Opens N) (O : Opens ℝ) (hO : 0 ∈ O)
    (phi : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (N × ℝ) M ∞)
    (hsource : (K : Set N) ×ˢ (O : Set ℝ) ⊆ phi.source)
    (hproduct : ∀ k ∈ K, ∀ t ∈ O, ∀ (u v : TangentSpace J k) (r q : ℝ),
      g.inner (phi (k, t))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (k, t) (u, r))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (k, t) (v, q)) =
      g.inner (phi (k, 0))
        (mfderiv J I (fun y : N => phi (y, 0)) k u)
        (mfderiv J I (fun y : N => phi (y, 0)) k v) + r * q) :
    ∃ (hPhi : IsLocalDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I ∞
        (fun x : K × O => phi (x.1.1, x.2.1)))
      (h : SmoothRiemannianMetric J K),
      (∀ (k : K) (u v : TangentSpace J k), h.inner k u v =
        g.inner (phi (k.1, 0))
          (mfderiv J I (fun y : N => phi (y, 0)) k.1 u)
          (mfderiv J I (fun y : N => phi (y, 0)) k.1 v)) ∧
      (localPullMetric g (fun x : K × O => phi (x.1.1, x.2.1)) hPhi =
        h.prod ((euclideanMetric (E := ℝ)).restrictOpen O)) ∧
      ∀ (k : K) (t : O), metricScalarAt (I := J) h k =
        metricScalarAt (I := I) g (phi (k.1, t.1)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : SigmaCompactSpace K :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen J K.isOpen)
  let _ : SigmaCompactSpace O :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen 𝓘(ℝ, ℝ) O.isOpen)
  obtain ⟨hPhi, h, hinner, hmetric⟩ :=
    exists_metric_prod_eq_localPullMetric_of_partialDiffeomorph g K O hO phi hsource hproduct
  refine ⟨hPhi, h, hinner, hmetric, ?_⟩
  intro k t
  have hn := metricScalarAt_localPull g
    (fun x : K × O => phi (x.1.1, x.2.1)) hPhi (k, t)
  rw [hmetric] at hn
  rw [metricScalarAt_productMetric,
    metricScalarAt_eq_zero_of_finrank_le_one (I := 𝓘(ℝ, ℝ)) _ (by norm_num)] at hn
  simpa using hn

end DifferentialGeometry.Geometry.Curvature
