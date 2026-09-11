import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteHinge

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem unit_intrinsic_subsegment_dist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (a L : ℝ) (ha : 0 < a) (hL : 0 ≤ L) (hLa : L ≤ a)
    (hmin : (riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p u a)).toReal = a) :
    (riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p u L)).toReal = L := by
  let v : TangentSpace I p := a • u
  have hexp : expMapIntrinsic (I := I) g hEnorm p v =
      intrinsicGeodesic (I := I) g hEnorm p u a :=
    intrinsicGeodesic_smul (I := I) g hEnorm p u a
  have hlen : Real.sqrt (g.inner p v v) = a := by
    dsimp only [v]
    rw [sqrt_gInner_smul_self (I := I) g p ha.le, hu, Real.sqrt_one, mul_one]
  have hfin : riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p u a) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hmin
    linarith
  have hratio : L / a ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hL ha.le, (div_le_one ha).2 hLa⟩
  have h := minSegment_edist (I := I) g hEnorm v hexp hlen hmin.symm hfin hratio
  have hparam : intrinsicGeodesic (I := I) g hEnorm p v (L / a) =
      intrinsicGeodesic (I := I) g hEnorm p u L := by
    calc
      _ = intrinsicGeodesic (I := I) g hEnorm p u (a * (L / a)) :=
        intrinsicGeo_smul_apply (I := I) g hEnorm p u a (L / a)
      _ = _ := by rw [mul_div_cancel₀ L ha.ne']
  rw [hparam, div_mul_cancel₀ L ha.ne'] at h
  rw [h, ENNReal.toReal_ofReal hL]

variable [ConnectedSpace M]

theorem complete_triangle_angle
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : M) (u v : TangentSpace I o) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a)).toReal = a)
    (hminB : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal = b) :
    comparisonAngle
      (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a)).toReal
      (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a)
        (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal ≤
      Real.arccos (g.inner o u v) := by
  rw [hminA, hminB, comparisonAngle]
  apply Real.arccos_le_arccos
  have h := complete_hinge_sq (I := I) g hEnorm hsec o u v a b ha hb hu hv hminA
  apply (le_div_iff₀ (by positivity : 0 < 2 * a * b)).2
  nlinarith

private theorem comparisonAngle_shorten_first
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : M) (u v : TangentSpace I o) (a1 a2 b : ℝ)
    (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (hb : 0 < b) (hu : g.inner o u u = 1)
    (hminB : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal = b) :
    comparisonAngle a2 b
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a2)
        (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal ≤
    comparisonAngle a1 b
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a1)
        (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal := by
  let F : ℝ → ℝ := fun s => s ^ 2 + b ^ 2 -
    (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u s)
      (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal ^ 2
  have hbase := convexOn_sq_sub_sq_riemannianEDist_intrinsicGeodesic (I := I)
    g hEnorm hsec (intrinsicGeodesic (I := I) g hEnorm o v b) o u hu
    (convex_Icc 0 a2)
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

theorem complete_comparisonAngle_shortening
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : M) (u v : TangentSpace I o) (a1 a2 b1 b2 : ℝ)
    (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (hb1 : 0 < b1) (hb12 : b1 ≤ b2)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a2)).toReal = a2)
    (hminB : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b2)).toReal = b2) :
    comparisonAngle a2 b2
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a2)
        (intrinsicGeodesic (I := I) g hEnorm o v b2)).toReal ≤
    comparisonAngle a1 b1
      (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a1)
        (intrinsicGeodesic (I := I) g hEnorm o v b1)).toReal := by
  have hminA1 := unit_intrinsic_subsegment_dist (I := I) g hEnorm o u hu a2 a1
    (ha1.trans_le ha12) ha1.le ha12 hminA
  have hfirst := comparisonAngle_shorten_first (I := I) g hEnorm hsec o u v
    a1 a2 b2 ha1 ha12 (hb1.trans_le hb12) hu hminB
  have hsecond := comparisonAngle_shorten_first (I := I) g hEnorm hsec o v u
    b1 b2 a1 hb1 hb12 ha1 hv hminA1
  rw [comparisonAngle_comm b2 a1, comparisonAngle_comm b1 a1,
    riemannianEDist_comm (I := I)
      (x := intrinsicGeodesic (I := I) g hEnorm o v b2),
    riemannianEDist_comm (I := I)
      (x := intrinsicGeodesic (I := I) g hEnorm o v b1)] at hsecond
  exact hfirst.trans hsecond

end DifferentialGeometry.Geometry.Comparison.Toponogov
