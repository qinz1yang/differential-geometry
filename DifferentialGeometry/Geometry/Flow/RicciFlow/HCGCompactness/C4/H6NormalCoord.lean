import DifferentialGeometry.Geometry.Comparison.Volume.RadialRadius
import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PointedEmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# H6 normal-coordinate metric bridges

This file connects the radial Jacobi estimates from the comparison-geometry
layer to the normal-coordinate metric package consumed by Chapter 4.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- The framed model-space radius corresponding to the canonical clamped
Jacobi launch radius. -/
def framedJacobiRadius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Real := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact expRadiusGp (I := I) Y.metric x / 26

/-- The framed Jacobi radius is positive at every center. -/
lemma framedJacobiRadius_pos
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    0 < framedJacobiRadius (I := I) Y x := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [framedJacobiRadius]
  exact div_pos (expRadiusGp_pos (I := I) Y.metric x) (by norm_num)

/-- Framed model smallness at `expRadiusGp / 26` is exactly the raw tangent
smallness required by the explicit radial Rm04 package. -/
lemma normalFrame_lt_jac
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {z : E} :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ‖z‖ < framedJacobiRadius (I := I) Y x →
      ‖normalFrame (I := I) Y.metric x z‖ <
        jacobiVarRadius (I := I) Y.metric x := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hz
  rw [framedJacobiRadius] at hz
  rw [jacobiVarRadius]
  apply norm_lt_exp_div (I := I) Y.metric x (by norm_num)
  simpa only [normalFrame_sqrt] using hz

/-- A radial Riemann-tensor norm bound along the geodesic launched by one
framed normal-coordinate point. -/
def FramedRm04Bound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E) (R : Real) : Prop :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ∀ t ∈ Set.Ioo (0 : Real) 1,
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) Y.metric
      (radialCurve (I := I) Y.metric x
        (normalFrame (I := I) Y.metric x z) t) 4
      (DifferentialGeometry.Integral.Connection.metricRm04At
        (I := I) (M := Y.M) Y.metric
        (radialCurve (I := I) Y.metric x
          (normalFrame (I := I) Y.metric x z) t))) ≤ R

/-- Uniform bounded geometry supplies the radial Rm04 bound along every
framed normal-coordinate ray in every sequence member. -/
theorem framed_rm04_of_seq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (k : Nat)
    (x : (X.obj k).M) (z : E) :
    FramedRm04Bound (I := I) (X.obj k) x z (hX.C 0) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  intro t ht
  exact rm04Bound_of_seq (I := I) hX k
    (radialCurve (I := I) (X.obj k).metric x
      (normalFrame (I := I) (X.obj k).metric x z) t)

/-- The public normal-coordinate metric is the endpoint Gram form of radial
Jacobi fields launched through its orthonormal frame. -/
theorem framed_metric_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ‖z‖ < expRadiusGp (I := I) Y.metric x →
    normalCoordMetric (I := I) Y x z v w =
      Y.metric.inner
        (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
        (radialJacobiField (I := I) Y.metric x
          (normalFrame (I := I) Y.metric x z)
          (normalFrame (I := I) Y.metric x v) 1)
        (radialJacobiField (I := I) Y.metric x
          (normalFrame (I := I) Y.metric x z)
          (normalFrame (I := I) Y.metric x w) 1) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hz
  have hzC2 : ‖normalFrame (I := I) Y.metric x z‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    simpa only [normalFrame_sqrt] using hz
  have hsrc : z ∈ (framedExpDiffeo (I := I) Y.metric x).source := by
    rw [framedExp_source]
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hzC2
  have hraw : normalFrame (I := I) Y.metric x z ∈
      (expMapDiffeo (I := I) Y.metric x).source := by
    simpa only [framedExp_source] using hsrc
  rw [normalCoordMetric_apply (I := I), framedExp_apply,
    mfderiv_framedExp (I := I) Y.metric x hsrc]
  rw [expMapDiffeo_apply_eq (I := I) Y.metric x hraw,
    expDiffeo_mfderiv (I := I) Y.metric x hraw]
  change Y.metric.inner _
      (mfderiv (modelWithCornersSelf Real E) I
        (fun b : E => (expMap (I := I) Y.metric x
          (show TangentSpace I x from b) : Y.M))
        (normalFrame (I := I) Y.metric x z)
        (normalFrame (I := I) Y.metric x v))
      (mfderiv (modelWithCornersSelf Real E) I
        (fun b : E => (expMap (I := I) Y.metric x
          (show TangentSpace I x from b) : Y.M))
        (normalFrame (I := I) Y.metric x z)
        (normalFrame (I := I) Y.metric x w)) = _
  rw [← radialJacobi_one (I := I) Y.metric x
      (normalFrame (I := I) Y.metric x z)
      (normalFrame (I := I) Y.metric x v) hzC2,
    ← radialJacobi_one (I := I) Y.metric x
      (normalFrame (I := I) Y.metric x z)
      (normalFrame (I := I) Y.metric x w) hzC2]

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The explicit radial Rm04 package, together with the existing smooth radial
extension frame, gives two-sided endpoint bounds directly in framed normal
coordinates. -/
theorem framed_rm04_bounds
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (z v : E) {a K R Vb A Blo Bhi : Real}
    (ha : 0 < a) (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hz : ‖z‖ < framedJacobiRadius (I := I) Y x)
    (hav : ‖a • v‖ < framedJacobiRadius (I := I) Y x)
    (hlaunch : ‖z‖ ≤ Vb) (hinit : ‖a • v‖ ≤ A)
    (hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
          R * Vb ^ 2 ≤ K)
    (hRm : FramedRm04Bound (I := I) Y x z R)
    (hmodelLe :
      A + gronwallBound 0 (max K 1) (K * A) 1 ≤ a * Bhi)
    (hmodelGe :
      a * Blo ≤ ‖a • v‖ -
        gronwallBound 0 (max K 1) (K * ‖a • v‖) 1) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Blo ≤ Real.sqrt (normalCoordMetric (I := I) Y x z v v) ∧
      Real.sqrt (normalCoordMetric (I := I) Y x z v v) ≤ Bhi := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let xRaw : E := show E from normalFrame (I := I) Y.metric x z
  let vRaw : E := show E from normalFrame (I := I) Y.metric x v
  have hsmul : a • vRaw =
      (show E from normalFrame (I := I) Y.metric x (a • v)) := by
    dsimp only [vRaw]
    exact ((normalFrame (I := I) Y.metric x).map_smul a v).symm
  have hzRaw : ‖xRaw‖ < jacobiVarRadius (I := I) Y.metric x := by
    dsimp only [xRaw]
    rw [jacobiVarRadius]
    apply norm_lt_exp_div (I := I) Y.metric x (by norm_num)
    simpa only [normalFrame_sqrt] using hz
  have havRaw : ‖a • vRaw‖ <
      jacobiVarRadius (I := I) Y.metric x := by
    rw [jacobiVarRadius]
    apply norm_lt_exp_div (I := I) Y.metric x (by norm_num)
    rw [hsmul, normalFrame_sqrt]
    exact hav
  have hzMem : xRaw ∈
      Metric.ball (0 : E) (jacobiVarRadius (I := I) Y.metric x) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hzRaw
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w)) := by
    intro y w
    simpa using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric y w)
  obtain ⟨D, hcard, hpar, hON, hFdiff⟩ :=
    exists_rm04FrameData_radius.{_, _, _, 0} (I := I) Y.metric x
      (R := jacobiVarRadius (I := I) Y.metric x) (b := 1)
      (by norm_num) le_rfl (jacobi_radius_le_c2 (I := I) Y.metric x)
  have hzC2 :
      ‖xRaw‖ < expMapC2Radius (I := I) Y.metric x :=
    hzRaw.trans_le (jacobi_radius_le_c2 (I := I) Y.metric x)
  have hgamma : ∀ t ∈ Set.Icc (0 : Real) 1,
      ContMDiffAt 𝓘(Real, Real) I 1
        (radialCurve (I := I) Y.metric x xRaw) t := by
    intro t ht
    exact (radialCurve_contMDiffAt_Icc (I := I) Y.metric x
      xRaw le_rfl hzC2 t ht).of_le (by norm_num)
  have hlaunchRaw :
      Real.sqrt (Y.metric.inner x xRaw xRaw) ≤ Vb := by
    dsimp only [xRaw]
    simpa only [normalFrame_sqrt] using hlaunch
  have hscaled :
      Real.sqrt (Y.metric.inner x (a • vRaw) (a • vRaw)) = ‖a • v‖ := by
    rw [hsmul, normalFrame_sqrt]
  have hinitRaw :
      Real.sqrt (Y.metric.inner x (a • vRaw) (a • vRaw)) ≤ A := by
    rw [hscaled]
    exact hinit
  have hRmRaw : ∀ t ∈ Set.Ioo (0 : Real) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) Y.metric
        (radialCurve (I := I) Y.metric x xRaw t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := Y.M) Y.metric
          (radialCurve (I := I) Y.metric x xRaw t))) ≤ R := by
    simpa only [FramedRm04Bound, xRaw] using hRm
  have hupper := rm04_one_le (I := I) Y.metric hEnorm x
    xRaw vRaw
    ha hK hVb (by norm_num) le_rfl le_rfl hzRaw havRaw hlaunchRaw
    hKbound hRmRaw hgamma (hcard _ hzMem) (D.F _)
    (hpar _ hzMem) (hON _ hzMem) (hFdiff _ hzMem) hinitRaw
    (by simpa only [one_mul] using hmodelLe)
  have hlower := rm04_one_ge (I := I) Y.metric hEnorm x
    xRaw vRaw
    ha hK hVb (by norm_num) le_rfl le_rfl hzRaw havRaw hlaunchRaw
    hKbound hRmRaw hgamma (hcard _ hzMem) (D.F _)
    (hpar _ hzMem) (hON _ hzMem) (hFdiff _ hzMem)
    (by simpa only [one_mul, hscaled] using hmodelGe)
  have hzGp : ‖z‖ < expRadiusGp (I := I) Y.metric x := by
    rw [framedJacobiRadius] at hz
    have hpos := expRadiusGp_pos (I := I) Y.metric x
    linarith
  rw [framed_metric_jacobi (I := I) Y x z v v hzGp]
  exact ⟨hlower, hupper⟩

private lemma exists_pos_mul_sq_le {S κ : Real} (hκ : 0 < κ) :
    ∃ r : Real, 0 < r ∧ S * r ^ 2 ≤ κ := by
  let T : Real := max S 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right S 1)
  have hdiv : 0 < κ / T := div_pos hκ hT
  refine ⟨Real.sqrt (κ / T), Real.sqrt_pos.mpr hdiv, ?_⟩
  calc
    S * Real.sqrt (κ / T) ^ 2 ≤
        T * Real.sqrt (κ / T) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left S 1) (sq_nonneg _)
    _ = T * (κ / T) := by rw [Real.sq_sqrt hdiv.le]
    _ = κ := by field_simp [hT.ne']

private lemma exists_smul_lt (v : E) {r : Real} (hr : 0 < r) :
    ∃ a : Real, 0 < a ∧ ‖a • v‖ < r := by
  let d : Real := ‖v‖ + 1
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  let a : Real := r / d
  have ha : 0 < a := div_pos hr hd
  refine ⟨a, ha, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hv : ‖v‖ < d := by
    dsimp only [d]
    linarith
  calc
    a * ‖v‖ < a * d := mul_lt_mul_of_pos_left hv ha
    _ = r := by
      dsimp only [a]
      field_simp [hd.ne']

private lemma quarter_models {K s : Real} (hs : 0 ≤ s)
    (herr : gronwallBound 0 (max K 1) K 1 ≤ 1 / 4) :
    s + gronwallBound 0 (max K 1) (K * s) 1 ≤ (5 / 4) * s ∧
      (3 / 4) * s ≤ s - gronwallBound 0 (max K 1) (K * s) 1 := by
  have hscale :
      gronwallBound 0 (max K 1) (K * s) 1 =
        s * gronwallBound 0 (max K 1) K 1 := by
    have heps : K * s = s * K := by ring
    rw [heps, gronwallBound_zero_mul_eps]
  have hmul := mul_le_mul_of_nonneg_left herr hs
  rw [hscale]
  constructor <;> nlinarith

/-- A uniform zeroth-order curvature bound gives one model-space radius on
which every framed normal-coordinate metric in the sequence satisfies the
book's half/two quadratic-form estimate.  The usable radius is still clamped
by the pointwise Jacobi source radius. -/
theorem exists_rm04_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    ∃ r₀ : Real, 0 < r₀ ∧ ∀ (k : Nat) (x : (X.obj k).M),
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      NormalCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E)
          (min (framedJacobiRadius (I := I) (X.obj k) x) r₀)) := by
  obtain ⟨κ, buffer, hκ, hbuffer, hsmall⟩ :=
    exists_gron_smallK (B₀ := (1 / 4 : Real)) (D := 1)
      (by norm_num) (by norm_num)
  let S : Real :=
    Real.sqrt ((Fintype.card
      (Fin 1 -> Fin (Module.finrank Real E)) : Real)) * hgeom.C 0
  have hS : 0 ≤ S := by
    exact mul_nonneg (Real.sqrt_nonneg _) (hgeom.nonneg 0)
  obtain ⟨r₀, hr₀, hcap⟩ := exists_pos_mul_sq_le (S := S) hκ
  refine ⟨r₀, hr₀, ?_⟩
  intro k x
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : ConnectedSpace (X.obj k).M := hconn k
  let K : Real := S * r₀ ^ 2
  have hK : 0 ≤ K := mul_nonneg hS (sq_nonneg r₀)
  have hKle : K ≤ κ := by simpa only [K] using hcap
  have herr : gronwallBound 0 (max K 1) K 1 ≤ 1 / 4 := by
    have hsmallK := hsmall hK hKle
    have hsmallK' :
        buffer ≤ (1 / 4 : Real) - gronwallBound 0 (max K 1) K 1 := by
      simpa only [mul_one] using hsmallK
    linarith
  intro z hz v
  have hzMin :
      ‖z‖ < min (framedJacobiRadius (I := I) (X.obj k) x) r₀ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzJac : ‖z‖ < framedJacobiRadius (I := I) (X.obj k) x :=
    hzMin.trans_le (min_le_left _ _)
  have hzRadius : ‖z‖ < r₀ := hzMin.trans_le (min_le_right _ _)
  obtain ⟨a, ha, hav⟩ := exists_smul_lt (v := v)
    (framedJacobiRadius_pos (I := I) (X.obj k) x)
  have hnormScale : ‖a • v‖ = a * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  obtain ⟨hmodelLe₀, hmodelGe₀⟩ :=
    quarter_models (K := K) (s := ‖a • v‖) (norm_nonneg _) herr
  have hmodelLe :
      ‖a • v‖ + gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 ≤
        a * ((5 / 4 : Real) * ‖v‖) := by
    calc
      ‖a • v‖ + gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 ≤
          (5 / 4 : Real) * ‖a • v‖ := hmodelLe₀
      _ = a * ((5 / 4 : Real) * ‖v‖) := by rw [hnormScale]; ring
  have hmodelGe :
      a * ((3 / 4 : Real) * ‖v‖) ≤
        ‖a • v‖ - gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 := by
    calc
      a * ((3 / 4 : Real) * ‖v‖) =
          (3 / 4 : Real) * ‖a • v‖ := by rw [hnormScale]; ring
      _ ≤ ‖a • v‖ - gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 :=
        hmodelGe₀
  have hKbound :
      Real.sqrt ((Fintype.card
        (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
          hgeom.C 0 * r₀ ^ 2 ≤ K := by
    simp only [K, S]
    exact le_rfl
  have hbounds := framed_rm04_bounds (I := I) (X.obj k)
    (hcomplete.complete k) (hconn k) x z v
    (a := a) (K := K) (R := hgeom.C 0) (Vb := r₀)
    (A := ‖a • v‖) (Blo := (3 / 4 : Real) * ‖v‖)
    (Bhi := (5 / 4 : Real) * ‖v‖)
    ha hK hr₀.le hzJac hav hzRadius.le le_rfl hKbound
    (framed_rm04_of_seq (I := I) hgeom k x z) hmodelLe hmodelGe
  have hzGp : ‖z‖ < expRadiusGp (I := I) (X.obj k).metric x := by
    rw [framedJacobiRadius] at hzJac
    have hpos := expRadiusGp_pos (I := I) (X.obj k).metric x
    linarith
  have hmetricNonneg :
      0 ≤ normalCoordMetric (I := I) (X.obj k) x z v v := by
    rw [framed_metric_jacobi (I := I) (X.obj k) x z v v hzGp]
    let q : (X.obj k).M :=
      expMap (I := I) (X.obj k).metric x
        (normalFrame (I := I) (X.obj k).metric x z)
    let J : TangentSpace I q :=
      radialJacobiField (I := I) (X.obj k).metric x
        (normalFrame (I := I) (X.obj k).metric x z)
        (normalFrame (I := I) (X.obj k).metric x v) 1
    change 0 ≤ (X.obj k).metric.inner q J J
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      simp
    · exact ((X.obj k).metric.pos q J hJ).le
  have hlowerSq :
      ((3 / 4 : Real) * ‖v‖) ^ 2 ≤
        (Real.sqrt (normalCoordMetric (I := I) (X.obj k) x z v v)) ^ 2 :=
    (sq_le_sq₀
      (mul_nonneg (by norm_num) (norm_nonneg v))
      (Real.sqrt_nonneg _)).2 hbounds.1
  have hupperSq :
      (Real.sqrt (normalCoordMetric (I := I) (X.obj k) x z v v)) ^ 2 ≤
        ((5 / 4 : Real) * ‖v‖) ^ 2 :=
    (sq_le_sq₀
      (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg v))).2 hbounds.2
  rw [Real.sq_sqrt hmetricNonneg] at hlowerSq hupperSq
  constructor <;> nlinarith [sq_nonneg ‖v‖]

/-- Jacobi endpoint comparison in a `g_x`-orthonormal frame gives the genuine
Euclidean half/two estimate for the framed normal-coordinate metric. -/
theorem framed_equiv_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (∀ z ∈ U, ‖z‖ < expRadiusGp (I := I) Y.metric x) →
    (∀ z ∈ U, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
        Y.metric.inner
          (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1)
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1) ∧
        Y.metric.inner
          (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1)
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1) ≤
              2 * ‖v‖ ^ 2) →
    NormalCoordMetricEquivOn (I := I) Y x U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hsmall hJ z hz v
  rw [framed_metric_jacobi (I := I) Y x z v v (hsmall z hz)]
  exact hJ z hz v

private lemma half_two_of_close
    (G G₀ : E →L[Real] E →L[Real] Real)
    (hG : ‖G - G₀‖ ≤ 1 / 2)
    (hG₀ : ∀ v : E, G₀ v v = ‖v‖ ^ 2)
    (v : E) :
    (1 / 2 : Real) * ‖v‖ ^ 2 ≤ G v v ∧ G v v ≤ 2 * ‖v‖ ^ 2 := by
  have hdiff :
      (G - G₀) v v = G v v - ‖v‖ ^ 2 := by
    simp only [ContinuousLinearMap.sub_apply, hG₀]
  have heval := ContinuousLinearMap.le_opNorm₂
    (G - G₀) v v
  have habs : |G v v - ‖v‖ ^ 2| ≤ (1 / 2 : Real) * ‖v‖ ^ 2 := by
    calc
      |G v v - ‖v‖ ^ 2| =
          ‖(G - G₀) v v‖ := by
            rw [hdiff, Real.norm_eq_abs]
      _ ≤ ‖G - G₀‖ * ‖v‖ * ‖v‖ := heval
      _ = ‖G - G₀‖ * ‖v‖ ^ 2 := by ring
      _ ≤ (1 / 2 : Real) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hG (sq_nonneg ‖v‖)
  obtain ⟨hlower, hupper⟩ := abs_le.mp habs
  constructor <;> nlinarith [sq_nonneg ‖v‖]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma exists_close_ball
    (f : E → E →L[Real] E →L[Real] Real)
    (hf : ContinuousAt f 0) :
    ∃ r : Real, 0 < r ∧ ∀ z ∈ Metric.ball (0 : E) r,
      ‖f z - f 0‖ ≤ 1 / 2 := by
  letI : SeminormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  obtain ⟨r, hr, hclose⟩ :=
    (Metric.continuousAt_iff (f := f) (a := (0 : E))).mp hf
      (1 / 2 : Real) (by norm_num)
  refine ⟨r, hr, fun z hz => ?_⟩
  have hnear := hclose (x := z) (Metric.mem_ball.mp hz)
  rw [dist_eq_norm] at hnear
  exact hnear.le

/-- Every framed normal chart has a positive ball, contained in its intrinsic
source-radius ball, on which the public normal-coordinate metric is uniformly
equivalent to the fixed model inner product. -/
theorem exists_equiv_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ r : Real, 0 < r ∧ r ≤ expRadiusGp (I := I) Y.metric x ∧
      NormalCoordMetricEquivOn (I := I) Y x (Metric.ball (0 : E) r) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let f := normalCoordMetric (I := I) Y x
  have hzero : (0 : E) ∈
      Metric.ball (0 : E) (expRadiusGp (I := I) Y.metric x) := by
    simp only [Metric.mem_ball, dist_self]
    exact expRadiusGp_pos (I := I) Y.metric x
  have hcont : ContinuousAt f 0 :=
    ((normalCoordMetric_contDiffOn_expBall (I := I) Y x).contDiffAt
      (Metric.isOpen_ball.mem_nhds hzero)).continuousAt
  obtain ⟨r₀, hr₀, hclose⟩ := exists_close_ball (E := E) f hcont
  let r := min r₀ (expRadiusGp (I := I) Y.metric x)
  refine ⟨r, lt_min hr₀ (expRadiusGp_pos (I := I) Y.metric x),
    min_le_right _ _, ?_⟩
  intro z hz v
  have hz₀ : z ∈ Metric.ball (0 : E) r₀ := by
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    exact lt_of_lt_of_le hz (min_le_left _ _)
  have hzero_eval : ∀ w : E, f 0 w w = ‖w‖ ^ 2 := by
    intro w
    calc
      f 0 w w =
          (innerSL Real : E →L[Real] E →L[Real] Real) w w :=
        congrArg (fun G => G w w) (normalMetric_zero (I := I) Y x)
      _ = Inner.inner Real w w := rfl
      _ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  exact half_two_of_close (E := E) (f z) (f 0) (hclose z hz₀) hzero_eval v

/-- The pointwise framed equivalence balls can be chosen simultaneously for a
pointed sequence.  This is pointwise radius data, not a uniform H6 profile. -/
theorem exists_equiv_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    ∃ radius : (k : Nat) → (X.obj k).M → Real,
      ∀ (k : Nat) (x : (X.obj k).M),
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : T2Space (TangentBundle I (X.obj k).M) :=
          (X.obj k).t2TangentBundle
        0 < radius k x ∧
          radius k x ≤ expRadiusGp (I := I) (X.obj k).metric x ∧
          NormalCoordMetricEquivOn (I := I) (X.obj k) x
            (Metric.ball (0 : E) (radius k x)) := by
  choose radius hpos hle hequiv using fun k x =>
    exists_equiv_ball (I := I) (X.obj k) x
  exact ⟨radius, fun k x => ⟨hpos k x, hle k x, hequiv k x⟩⟩

end HCGCompactness
end DifferentialGeometry
