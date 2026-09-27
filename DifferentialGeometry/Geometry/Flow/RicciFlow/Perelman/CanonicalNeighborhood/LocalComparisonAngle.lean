import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalSquaredDistanceConvexity

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

private theorem comparisonAngle_shorten_first_local
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (o : M) (u v : TangentSpace I o) (a1 a2 b : ℝ)
    (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (hb : 0 < b) (hu : g.inner o u u = 1)
    (hminB : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal = b)
    (hsec : ∀ s ∈ interior (Icc (0 : ℝ) a2), ∀ y : M,
      riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o v b) y +
        riemannianEDist I y (intrinsicGeodesic (I := I) g hEnorm o u s) =
        riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o v b)
          (intrinsicGeodesic (I := I) g hEnorm o u s) →
      metricRm04At (I := I) g y ∈ tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    comparisonAngle a2 b
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a2)
        (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal ≤
    comparisonAngle a1 b
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a1)
        (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal := by
  let F : ℝ → ℝ := fun s => s ^ 2 + b ^ 2 -
    (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u s)
      (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal ^ 2
  have hbase := convexOn_sq_sub_sq_of_sectional_nonnegative_on_minimizing_lenses (I := I)
    g hEnorm (intrinsicGeodesic (I := I) g hEnorm o v b) o u hu
    (convex_Icc 0 a2) hsec
  have hF : ConvexOn ℝ (Icc 0 a2) F := by
    convert! hbase.add_const (b ^ 2) using 1
    funext s
    dsimp only [F, Pi.add_apply]
    rw [riemannianEDist_comm]
    ring
  have hzero : F 0 = 0 := by
    dsimp only [F]
    rw [intrinsicGeodesic_zero, hminB]
    ring
  have hratio := convex_quotient_mono hF hzero ha1 ha12 le_rfl
  have hdiv := div_le_div_of_nonneg_right hratio (by positivity : 0 ≤ 2 * b)
  dsimp only [comparisonAngle]
  apply Real.arccos_le_arccos
  convert! hdiv using 1 <;> dsimp only [F] <;> ring

theorem comparisonAngle_shortening_of_sectional_nonnegative_on_minimizing_lenses
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (o : M) (u v : TangentSpace I o) (a1 a2 b1 b2 : ℝ)
    (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (hb1 : 0 < b1) (hb12 : b1 ≤ b2)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a2)).toReal = a2)
    (hminB : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b2)).toReal = b2)
    (hsec : ∀ s ∈ Icc (0 : ℝ) a2, ∀ t ∈ Icc (0 : ℝ) b2, ∀ y : M,
      riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u s) y +
        riemannianEDist I y (intrinsicGeodesic (I := I) g hEnorm o v t) =
        riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u s)
          (intrinsicGeodesic (I := I) g hEnorm o v t) →
      metricRm04At (I := I) g y ∈ tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    comparisonAngle a2 b2
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a2)
        (intrinsicGeodesic (I := I) g hEnorm o v b2)).toReal ≤
    comparisonAngle a1 b1
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a1)
        (intrinsicGeodesic (I := I) g hEnorm o v b1)).toReal := by
  have hminA1 := unit_intrinsic_subsegment_dist (I := I) g hEnorm o u hu a2 a1
    (ha1.trans_le ha12) ha1.le ha12 hminA
  have hfirst := comparisonAngle_shorten_first_local (I := I) g hEnorm o u v
    a1 a2 b2 ha1 ha12 (hb1.trans_le hb12) hu hminB (by
      intro s hs y hy
      apply hsec s (interior_subset hs) b2 ⟨(hb1.trans_le hb12).le, le_rfl⟩ y
      simpa only [riemannianEDist_comm, add_comm] using hy)
  have hsecond := comparisonAngle_shorten_first_local (I := I) g hEnorm o v u
    b1 b2 a1 hb1 hb12 ha1 hv hminA1 (by
      intro t ht y hy
      exact hsec a1 ⟨ha1.le, ha12⟩ t (interior_subset ht) y hy)
  rw [comparisonAngle_comm b2 a1, comparisonAngle_comm b1 a1,
    riemannianEDist_comm (I := I)
      (x := intrinsicGeodesic (I := I) g hEnorm o v b2),
    riemannianEDist_comm (I := I)
      (x := intrinsicGeodesic (I := I) g hEnorm o v b1)] at hsecond
  exact hfirst.trans hsecond

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
