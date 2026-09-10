import DifferentialGeometry.Geometry.Comparison.Volume.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Comparison.Volume.CompactAVR
import DifferentialGeometry.Geometry.Comparison.Volume.DiffeomorphVolume
import DifferentialGeometry.Geometry.Comparison.Volume.PointedConvergence
import DifferentialGeometry.Geometry.Comparison.Volume.VolumeNaturality
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciFromJets
import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem arcLength_le_sqrt_mul_arcLength_of_inner_le_along
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g h : SmoothRiemannianMetric I M)
    {c a b : ℝ} (hc : 0 ≤ c) (hab : a ≤ b)
    {γ : ℝ → M}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
    (hinner : ∀ t ∈ Set.Icc a b, ∀ v : TangentSpace I (γ t),
      h.inner (γ t) v v ≤ c * g.inner (γ t) v v) :
    Variation.arcLength (I := I) h γ a b ≤
      Real.sqrt c * Variation.arcLength (I := I) g γ a b := by
  let F : ℝ → ℝ := fun t ↦ Real.sqrt
    (h.inner (γ t)
      (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t (1 : ℝ))
      (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t (1 : ℝ)))
  let G : ℝ → ℝ := fun t ↦ Real.sqrt
    (g.inner (γ t)
      (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t (1 : ℝ))
      (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t (1 : ℝ)))
  have hFint : IntegrableOn F (Set.Icc a b) :=
    Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) h hab hγ
  have hGint : IntegrableOn G (Set.Icc a b) :=
    Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hγ
  have hFint' : IntegrableOn F (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hFint
  have hGint' : IntegrableOn G (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hGint
  have hmono : ∫ t in a..b, F t ≤
      ∫ t in a..b, Real.sqrt c * G t := by
    refine intervalIntegral.integral_mono_on hab hFint'.intervalIntegrable
      (IntervalIntegrable.const_mul hGint'.intervalIntegrable (Real.sqrt c)) ?_
    intro t ht
    dsimp only [F, G]
    rw [← Real.sqrt_mul hc]
    exact Real.sqrt_le_sqrt (hinner t ht _)
  simpa only [Variation.arcLength, F, G,
    intervalIntegral.integral_const_mul] using hmono

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem arcLength_localPullMetric_eq
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (g : SmoothRiemannianMetric I N) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b)) :
    Variation.arcLength (I := I) (localPullMetric (I := I) (J := I) g f hf) γ a b =
      Variation.arcLength (I := I) g (f ∘ γ) a b := by
  let gp : SmoothRiemannianMetric I M :=
    localPullMetric (I := I) (J := I) g f hf
  let rbN : RiemannianBundle (fun y : N ↦ TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun y : N ↦ TangentSpace I y) := rbN
  let rbM : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gp.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := rbM
  have hnormN : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y w
  have hnormM : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gp.inner x v v)) := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) gp x v
  have hcomp : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      (f ∘ γ) (Set.Icc a b) :=
    (hf.contMDiff.of_le (by decide)).comp_contMDiffOn hγ
  have hpath := localPull_pathLen (I := I) (J := I) g hnormN f hf hγ
  have hpull := Geodesic.pathELength_eq_arcLength_riemannianBundle
    (I := I) gp hab
    (Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) gp hab hγ)
    (fun t _ ↦ hnormM _ _)
  have htgt := Geodesic.pathELength_eq_arcLength_riemannianBundle
    (I := I) g hab
    (Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hcomp)
    (fun t _ ↦ hnormN _ _)
  change Manifold.pathELength I (f ∘ γ) a b =
      Manifold.pathELength I γ a b at hpath
  rw [hpull, htgt] at hpath
  apply (ENNReal.ofReal_eq_ofReal_iff
    (arcLength_nonneg (I := I) (localPullMetric (I := I) (J := I) g f hf) hab)
    (arcLength_nonneg (I := I) g hab)).mp
  exact hpath.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem arcLength_restrictOpen_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U]
    {γ : ℝ → U} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b)) :
    Variation.arcLength (I := I) (g.restrictOpen (I := I) U) γ a b =
      Variation.arcLength (I := I) g
        ((Subtype.val : U → M) ∘ γ) a b := by
  unfold Variation.arcLength
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.ae_iff.mpr (by simp :
      volume {t : ℝ | ¬ t ≠ b} = 0)] with t htb
  intro ht
  rw [Set.uIoc_of_le hab] at ht
  have ht' : t ∈ Set.Ioo a b := ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  have hγt : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht'.1.le, ht'.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht'.1 ht'.2)
  have hval : MDifferentiableAt I I (Subtype.val : U → M) (γ t) :=
    (contMDiff_subtype_val (I := I) (U := U) (n := (∞ : WithTop ℕ∞))).mdifferentiableAt
      (by decide)
  have hchain :
      mfderiv (modelWithCornersSelf ℝ ℝ) I
          ((Subtype.val : U → M) ∘ γ) t =
        (mfderiv I I (Subtype.val : U → M) (γ t)).comp
          (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t) :=
    mfderiv_comp t hval hγt
  congr 1
  let v : TangentSpace I (γ t) :=
    mfderiv (modelWithCornersSelf ℝ ℝ) I γ t (1 : ℝ)
  change g.inner (γ t : M) v v =
    g.inner (γ t : M)
      (mfderiv (modelWithCornersSelf ℝ ℝ) I
        ((Subtype.val : U → M) ∘ γ) t (1 : ℝ))
      (mfderiv (modelWithCornersSelf ℝ ℝ) I
        ((Subtype.val : U → M) ∘ γ) t (1 : ℝ))
  rw [hchain]
  change g.inner (γ t : M) v v =
    g.inner (γ t : M)
      (mfderiv I I (Subtype.val : U → M) (γ t) v)
      (mfderiv I I (Subtype.val : U → M) (γ t) v)
  have hv : mfderiv I I (Subtype.val : U → M) (γ t) v = v := by
    simpa only using mfderiv_subtype_val_apply (I := I) U (γ t) v
  rw [hv]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem arcLength_congr_of_eqOn
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    {γ η : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
    (hη : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 η (Set.Icc a b))
    (hγη : Set.EqOn γ η (Set.Icc a b)) :
    Variation.arcLength (I := I) g γ a b =
      Variation.arcLength (I := I) g η a b := by
  let rb : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := rb
  have hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hp := Manifold.pathELength_congr (I := I) hγη
  have hγbridge := Geodesic.pathELength_eq_arcLength_riemannianBundle
    (I := I) g hab
    (Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hγ)
    (fun t _ ↦ hnorm _ _)
  have hηbridge := Geodesic.pathELength_eq_arcLength_riemannianBundle
    (I := I) g hab
    (Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hη)
    (fun t _ ↦ hnorm _ _)
  rw [hγbridge, hηbridge] at hp
  exact (ENNReal.ofReal_eq_ofReal_iff
    (arcLength_nonneg (I := I) g hab)
    (arcLength_nonneg (I := I) g hab)).mp hp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem minJoin_mapsTo_pointedClosedBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (hEnorm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
        Y.riemBundle (I := I)
      IsMetricNorm (I := I) (M := Y.M) Y.metric)
    {s : ℝ} (_hs : 0 < s) {y : Y.M}
    (hy : y ∈ pointedOpenBall (I := I) Y s) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace ℝ (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : IsRiemannianManifold I Y.M := inferInstance
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    Set.MapsTo
      (minJoin (I := I) Y.metric hEnorm Y.basepoint y)
      (Set.Icc (0 : ℝ) 1) (pointedClosedBall (I := I) Y s) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    Y.riemBundle (I := I)
  let : (z : Y.M) → InnerProductSpace ℝ (TangentSpace I z) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : IsRiemannianManifold I Y.M := inferInstance
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro t ht
  have hmin := minJoin_edist_le (I := I) Y.metric hEnorm
    Y.basepoint y ht.1
  have hdist_ne : riemannianEDist I Y.basepoint y ≠ (∞ : ℝ≥0∞) :=
    Exponential.riemannianEDist_ne_top (I := I) Y.basepoint y
  have hscale : ENNReal.ofReal
      ((riemannianEDist I Y.basepoint y).toReal * t) ≤
      riemannianEDist I Y.basepoint y := by
    calc
      ENNReal.ofReal ((riemannianEDist I Y.basepoint y).toReal * t) ≤
          ENNReal.ofReal ((riemannianEDist I Y.basepoint y).toReal) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_of_le_one_right ENNReal.toReal_nonneg ht.2
      _ = riemannianEDist I Y.basepoint y := ENNReal.ofReal_toReal hdist_ne
  change riemannianEDistOf (I := I) Y.metric Y.basepoint
      (minJoin (I := I) Y.metric hEnorm Y.basepoint y t) ≤ ENNReal.ofReal s
  rw [riemannianEDistOf_eq_riemannianEDist (I := I) Y.metric hEnorm]
  exact (hmin.trans hscale).trans hy.le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem pointedOpenBall_isOpen
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (R : ℝ) :
    letI : TopologicalSpace Y.M := Y.topology
    IsOpen (pointedOpenBall (I := I) Y R) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let rb : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.toRiemannianMetric⟩
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) := rb
  let rbCont : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.inner, Y.metric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) := rbCont
  let hEnorm : IsMetricNorm (I := I) (M := Y.M) Y.metric := fun z v ↦
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) Y.metric z v
  have hdist : Continuous (fun z : Y.M ↦
      riemannianEDistOf (I := I) Y.metric Y.basepoint z) := by
    have h := continuous_riemannianEDist (I := I) Y.metric Y.basepoint
    convert h using 1
    funext z
    exact (riemannianEDistOf_eq_riemannianEDist
      (I := I) Y.metric hEnorm Y.basepoint z).symm
  change IsOpen {z : Y.M |
    riemannianEDistOf (I := I) Y.metric Y.basepoint z < ENNReal.ofReal R}
  exact isOpen_lt hdist continuous_const

def pointedBallVolume
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (R : ℝ) : ℝ≥0∞ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.toRiemannianMetric⟩
  exact ballVolume (I := I) Y.metric Y.basepoint R

def pointedAsymptoticVolumeRatio
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ℝ≥0∞ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.toRiemannianMetric⟩
  exact asymptoticVolumeRatio (I := I) Y.metric Y.basepoint

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem riemannianVolumeMeasure_pointedOpenBall_eq_pointedBallVolume
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (R : ℝ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
        (pointedOpenBall (I := I) Y R) = pointedBallVolume (I := I) Y R := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let rb : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.toRiemannianMetric⟩
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) := rb
  unfold pointedBallVolume ballVolume
  congr 1

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem pointedAsymptoticVolumeRatio_mul_euclidean_le_pointedBallVolume
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {R : ℝ} (hR : 0 < R) :
    pointedAsymptoticVolumeRatio (I := I) Y *
        ENNReal.ofReal (euclideanUnitBallVolume (Module.finrank ℝ E) *
          R ^ Module.finrank ℝ E) ≤
      pointedBallVolume (I := I) Y R := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.toRiemannianMetric⟩
  exact asymptoticVolumeRatio_mul_euclidean_le_ballVolume
    (I := I) Y.metric Y.basepoint hR

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem riemannianVolumeMeasure_restrictOpen_le_of_image_subset
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] [SigmaCompactSpace U]
    {A : Set U} {B : Set M}
    (hB : letI : MeasurableSpace M := borel M; MeasurableSet B)
    (hAB : ∀ x ∈ A, (x : M) ∈ B) :
    riemannianVolumeMeasure (I := I) (M := U)
        (g.restrictOpen (I := I) U) A ≤
      riemannianVolumeMeasure (I := I) (M := M) g B := by
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μU : Measure U := riemannianVolumeMeasure (I := I) (M := U)
    (g.restrictOpen (I := I) U)
  let μM : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have hmap := congrArg (fun μ : Measure M ↦ μ B)
    (riemannianVolumeMeasure_map_restrictOpen (I := I) g U)
  rw [Measure.map_apply continuous_subtype_val.measurable hB,
    Measure.restrict_apply hB] at hmap
  calc
    μU A ≤ μU ((Subtype.val : U → M) ⁻¹' B) :=
      measure_mono (fun x hx ↦ hAB x hx)
    _ = μM (B ∩ (U : Set M)) := hmap
    _ ≤ μM B := measure_mono inter_subset_left

def metricSourceSet
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ)
    (A : Set L.M) : Set (MetricSourceDomain (I := I) Φ k) :=
  (Subtype.val : MetricSourceDomain (I := I) Φ k → L.M) ⁻¹' A

def pointedEmbeddingPreimage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ)
    (A : Set (X.obj (subseq k)).M) :
    Set (MetricSourceDomain (I := I) Φ k) :=
  {x | Φ.map k (x : L.M) ∈ A}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metricSourceSet_mono
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ)
    {A B : Set L.M} (hAB : A ⊆ B) :
    metricSourceSet (I := I) Φ k A ⊆ metricSourceSet (I := I) Φ k B :=
  preimage_mono hAB

omit [I.Boundaryless] in
theorem eventually_pullback_inner_le_on_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    {K : Set L.M}
    (hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    {Q : ℝ} (hQ : 1 < Q) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      K ⊆ Φ.source k ∧
      let D := canonicalMetricSourceData (I := I) Φ k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
      ∀ (x : MetricSourceDomain (I := I) Φ k),
        x ∈ metricSourceSet (I := I) Φ k K →
        ∀ v : TangentSpace I x,
          D.pullbackMetric.inner x v v ≤ Q * D.limitMetric.inner x v v := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 < n := by
    change (0 : ℝ) < (Module.finrank ℝ E : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  let ε : ℝ := (Q - 1) / n
  have hε : 0 < ε := div_pos (sub_pos.mpr hQ) hn
  obtain ⟨ksrc, hksrc⟩ := C.eventually_source_contains hK
  obtain ⟨kconv, hkconv⟩ := C.converges K hK 0 ε hε
  refine ⟨max ksrc kconv, fun k hk ↦ ?_⟩
  have hsrc : K ⊆ Φ.source k :=
    hksrc k (le_trans (Nat.le_max_left _ _) hk)
  refine ⟨hsrc, ?_⟩
  dsimp only
  let D := canonicalMetricSourceData (I := I) Φ k
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  have hsup : D.derivNormSupOn (I := I) K 0 < ε :=
    hkconv k (le_trans (Nat.le_max_right _ _) hk)
  have hKsrcCompact :
      IsCompact (metricSourceCompactSet (I := I) Φ k K) :=
    D.compact_preimage K hK hsrc
  intro x hx v
  have hx' : x ∈ metricSourceCompactSet (I := I) Φ k K := hx
  have hdn : metricDerivNorm (I := I) 0 D.pullbackMetric
      D.limitMetric D.limitMetric x ≤ D.derivNormSupOn (I := I) K 0 := by
    have hdn' :=
      derivNorm_le_sup (I := I) hKsrcCompact (a := 0) (p := 0)
        (le_refl 0) D.pullbackMetric D.limitMetric D.referenceMetric hx'
    rw [canonicalMetricSourceData_reference_eq_limit (I := I) Φ k] at hdn'
    change metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric
        D.limitMetric x ≤
      metricDerivNormSupOn (I := I)
        (metricSourceCompactSet (I := I) Φ k K) 0
        D.pullbackMetric D.limitMetric D.limitMetric
    exact hdn'
  have hquad := metricQuadFormDiff_le_metricDerivNorm
    (I := I) D.pullbackMetric D.limitMetric D.limitMetric x v
  have hnonneg : 0 ≤ D.limitMetric.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (D.limitMetric.pos x v hv).le
  have hcoeff : (Module.finrank ℝ (TangentSpace I x) : ℝ) *
      metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric D.limitMetric x <
      Q - 1 := by
    have hfinrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [hfinrank]
    calc
      n * metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric
          D.limitMetric x ≤ n * D.derivNormSupOn (I := I) K 0 :=
        mul_le_mul_of_nonneg_left hdn hn.le
      _ < n * ε := mul_lt_mul_of_pos_left hsup hn
      _ = Q - 1 := by
        have hn0 : (Module.finrank ℝ E : ℝ) ≠ 0 := by positivity
        dsimp only [ε, n]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hn0]
  have hdiff : D.pullbackMetric.inner x v v - D.limitMetric.inner x v v ≤
      (Q - 1) * D.limitMetric.inner x v v := by
    calc
      D.pullbackMetric.inner x v v - D.limitMetric.inner x v v ≤
          |D.pullbackMetric.inner x v v - D.limitMetric.inner x v v| :=
        le_abs_self _
      _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) *
            metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric
              D.limitMetric x * D.limitMetric.inner x v v := hquad
      _ ≤ (Q - 1) * D.limitMetric.inner x v v :=
        mul_le_mul_of_nonneg_right hcoeff.le hnonneg
  linarith

omit [I.Boundaryless] in
theorem eventually_limit_inner_le_pullback_on_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    {K : Set L.M}
    (hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    {Q : ℝ} (hQ : 1 < Q) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      K ⊆ Φ.source k ∧
      let D := canonicalMetricSourceData (I := I) Φ k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
      ∀ (x : MetricSourceDomain (I := I) Φ k),
        x ∈ metricSourceSet (I := I) Φ k K →
        ∀ v : TangentSpace I x,
          D.limitMetric.inner x v v ≤ Q * D.pullbackMetric.inner x v v := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 < n := by
    change (0 : ℝ) < (Module.finrank ℝ E : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  let δ : ℝ := 1 - Q⁻¹
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hδ : 0 < δ := sub_pos.mpr ((inv_lt_one₀ hQpos).2 hQ)
  let ε : ℝ := δ / n
  have hε : 0 < ε := div_pos hδ hn
  obtain ⟨ksrc, hksrc⟩ := C.eventually_source_contains hK
  obtain ⟨kconv, hkconv⟩ := C.converges K hK 0 ε hε
  refine ⟨max ksrc kconv, fun k hk ↦ ?_⟩
  have hsrc : K ⊆ Φ.source k :=
    hksrc k (le_trans (Nat.le_max_left _ _) hk)
  refine ⟨hsrc, ?_⟩
  dsimp only
  let D := canonicalMetricSourceData (I := I) Φ k
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  have hsup : D.derivNormSupOn (I := I) K 0 < ε :=
    hkconv k (le_trans (Nat.le_max_right _ _) hk)
  have hKsrcCompact :
      IsCompact (metricSourceCompactSet (I := I) Φ k K) :=
    D.compact_preimage K hK hsrc
  intro x hx v
  have hx' : x ∈ metricSourceCompactSet (I := I) Φ k K := hx
  have hdn : metricDerivNorm (I := I) 0 D.pullbackMetric
      D.limitMetric D.limitMetric x ≤ D.derivNormSupOn (I := I) K 0 := by
    have hdn' :=
      derivNorm_le_sup (I := I) hKsrcCompact (a := 0) (p := 0)
        (le_refl 0) D.pullbackMetric D.limitMetric D.referenceMetric hx'
    rw [canonicalMetricSourceData_reference_eq_limit (I := I) Φ k] at hdn'
    change metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric
        D.limitMetric x ≤
      metricDerivNormSupOn (I := I)
        (metricSourceCompactSet (I := I) Φ k K) 0
        D.pullbackMetric D.limitMetric D.limitMetric
    exact hdn'
  have hquad := metricQuadFormDiff_le_metricDerivNorm
    (I := I) D.pullbackMetric D.limitMetric D.limitMetric x v
  have hnonneg : 0 ≤ D.limitMetric.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (D.limitMetric.pos x v hv).le
  have hcoeff : (Module.finrank ℝ (TangentSpace I x) : ℝ) *
      metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric D.limitMetric x < δ := by
    have hfinrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [hfinrank]
    calc
      n * metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric
          D.limitMetric x ≤ n * D.derivNormSupOn (I := I) K 0 :=
        mul_le_mul_of_nonneg_left hdn hn.le
      _ < n * ε := mul_lt_mul_of_pos_left hsup hn
      _ = δ := by
        have hn0 : (Module.finrank ℝ E : ℝ) ≠ 0 := by positivity
        dsimp only [ε, n]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hn0]
  have hlower : -δ * D.limitMetric.inner x v v ≤
      D.pullbackMetric.inner x v v - D.limitMetric.inner x v v := by
    calc
      -δ * D.limitMetric.inner x v v ≤
          -((Module.finrank ℝ (TangentSpace I x) : ℝ) *
            metricDerivNorm (I := I) 0 D.pullbackMetric D.limitMetric
              D.limitMetric x) * D.limitMetric.inner x v v := by
        gcongr
      _ ≤ D.pullbackMetric.inner x v v - D.limitMetric.inner x v v :=
        by simpa [mul_assoc] using (neg_le_of_abs_le hquad)
  have hinv : Q⁻¹ * D.limitMetric.inner x v v ≤
      D.pullbackMetric.inner x v v := by
    dsimp only [δ] at hlower
    linarith
  calc
    D.limitMetric.inner x v v = Q * (Q⁻¹ * D.limitMetric.inner x v v) := by
      rw [← mul_assoc, mul_inv_cancel₀ hQpos.ne', one_mul]
    _ ≤ Q * D.pullbackMetric.inner x v v :=
      mul_le_mul_of_nonneg_left hinv hQpos.le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem pointedEmbeddingPreimage_openBall_subset_limitOpenBall_of_capture
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ)
    (hcomplete : MetricComplete (I := I) (X.obj (subseq k)))
    (hconn :
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      ConnectedSpace (X.obj (subseq k)).M)
    {K : Set L.M} (hKsrc : K ⊆ Φ.source k)
    {s r Q : ℝ} (hs : 0 < s) (hQ : 1 < Q)
    (hbuffer : Real.sqrt Q * s < r)
    (hcapture : pointedClosedBall (I := I) (X.obj (subseq k)) s ⊆ Φ.map k '' K)
    (hinner :
      let D := canonicalMetricSourceData (I := I) Φ k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
      ∀ (x : MetricSourceDomain (I := I) Φ k),
        x ∈ metricSourceSet (I := I) Φ k K →
        ∀ v : TangentSpace I x,
          D.limitMetric.inner x v v ≤ Q * D.pullbackMetric.inner x v v) :
    pointedEmbeddingPreimage (I := I) Φ k
        (pointedOpenBall (I := I) (X.obj (subseq k)) s) ⊆
      metricSourceSet (I := I) Φ k (pointedOpenBall (I := I) L r) := by
  let Y := X.obj (subseq k)
  let D := canonicalMetricSourceData (I := I) Φ k
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    Y.riemBundle (I := I)
  let : (z : Y.M) → InnerProductSpace ℝ (TangentSpace I z) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : IsRiemannianManifold I Y.M := inferInstance
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  let : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_t2 (I := I) Φ k
  let : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  let hEnorm : IsMetricNorm (I := I) (M := Y.M) Y.metric := fun z v ↦
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) Y.metric z v
  let F : MetricSourceDomain (I := I) Φ k ≃ₘ⟮I, I⟯
      MetricTargetDomain (I := I) Φ k := metricSourceTargetDiffeomorph (I := I) Φ k
  intro x hx
  let y : Y.M := Φ.map k (x : L.M)
  let join : ℝ → Y.M := minJoin (I := I) Y.metric hEnorm Y.basepoint y
  have hjoinBall : Set.MapsTo join (Set.Icc (0 : ℝ) 1)
      (pointedClosedBall (I := I) Y s) := by
    exact minJoin_mapsTo_pointedClosedBall (I := I) Y hcomplete hconn hEnorm hs hx
  have hjoinTarget : ∀ t : Set.Icc (0 : ℝ) 1, join t ∈ Φ.target k := by
    intro t
    obtain ⟨z, hzK, hmap⟩ := hcapture (hjoinBall t.property)
    rw [← hmap]
    exact (Φ.partialDiffeomorph k).map_source (hKsrc hzK)
  let joinT : Set.Icc (0 : ℝ) 1 → MetricTargetDomain (I := I) Φ k :=
    fun t ↦ ⟨join t, hjoinTarget t⟩
  have hjoinSmooth : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ join := by
    exact Exponential.intrinsicGeodesic_contMDiff
      (I := I) Y.metric hEnorm Y.basepoint
        (minimizingVec (I := I) Y.metric hEnorm Y.basepoint y)
  have hjoinISmooth : ContMDiff (𝓡∂ 1) I ∞
      (fun t : Set.Icc (0 : ℝ) 1 ↦ join t) :=
    hjoinSmooth.comp
      (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  have hjoinTSmooth : ContMDiff (𝓡∂ 1) I ∞ joinT := by
    rw [← ContMDiff.subtypeVal_comp_iff
      (metricTargetOpenSubset (I := I) Φ k) joinT]
    exact hjoinISmooth
  let γI : Set.Icc (0 : ℝ) 1 → MetricSourceDomain (I := I) Φ k :=
    fun t ↦ F.symm (joinT t)
  have hγISmooth : ContMDiff (𝓡∂ 1) I ∞ γI :=
    F.symm.contMDiff_toFun.comp hjoinTSmooth
  let γ : ℝ → MetricSourceDomain (I := I) Φ k :=
    γI ∘ Set.projIcc 0 1 zero_le_one
  have hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc 0 1) := by
    exact ((contMDiffOn_comp_projIcc_iff (x := (0 : ℝ)) (y := 1)).2
      (hγISmooth.of_le (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))))
  have hγmap (t : ℝ) : (F (γ t) : Y.M) =
      join (Set.projIcc 0 1 zero_le_one t) := by
    change (F (F.symm (joinT (Set.projIcc 0 1 zero_le_one t))) : Y.M) = _
    simp only [Diffeomorph.apply_symm_apply]
    rfl
  have hγK : ∀ t : ℝ, γ t ∈ metricSourceSet (I := I) Φ k K := by
    intro t
    let u : Set.Icc (0 : ℝ) 1 := Set.projIcc 0 1 zero_le_one t
    obtain ⟨z, hzK, hmap⟩ := hcapture (hjoinBall u.property)
    change (γ t : L.M) ∈ K
    have hzsrc : z ∈ Φ.source k := hKsrc hzK
    let z' : MetricSourceDomain (I := I) Φ k := ⟨z, hzsrc⟩
    have hF : F (γ t) = F z' := by
      apply Subtype.ext
      rw [hγmap]
      exact hmap.symm
    have : γ t = z' := F.injective hF
    rw [this]
    exact hzK
  let baseS : MetricSourceDomain (I := I) Φ k :=
    ⟨L.basepoint, show L.basepoint ∈ Φ.source k from Φ.base_mem k⟩
  have hγ0 : γ 0 = baseS := by
    apply F.injective
    apply Subtype.ext
    change (F (γ 0) : Y.M) = (F baseS : Y.M)
    rw [hγmap]
    have hbaseMap : (F baseS : Y.M) = Φ.map k L.basepoint := by
      have hbaseCoe : (baseS : L.M) = L.basepoint := rfl
      rw [← hbaseCoe]
      change ((metricSourceTargetDiffeomorph (I := I) Φ k baseS :
        MetricTargetDomain (I := I) Φ k) : Y.M) = Φ.map k (baseS : L.M)
      exact metric_source_target_diffeomorph_apply (I := I) Φ k baseS
    rw [hbaseMap]
    simp only [Set.projIcc_left, join, minJoin_zero]
    exact (Φ.basepoint_map k).symm
  have hγ1 : γ 1 = x := by
    apply F.injective
    apply Subtype.ext
    change (F (γ 1) : Y.M) = (F x : Y.M)
    rw [hγmap]
    have hxMap : (F x : Y.M) = Φ.map k (x : L.M) := by
      change ((metricSourceTargetDiffeomorph (I := I) Φ k x :
        MetricTargetDomain (I := I) Φ k) : Y.M) = Φ.map k (x : L.M)
      exact metric_source_target_diffeomorph_apply (I := I) Φ k x
    rw [hxMap]
    simp only [Set.projIcc_right, join, minJoin_one, y]
  have harcComp : Variation.arcLength (I := I) D.limitMetric γ 0 1 ≤
      Real.sqrt Q * Variation.arcLength (I := I) D.pullbackMetric γ 0 1 :=
    arcLength_le_sqrt_mul_arcLength_of_inner_le_along
      (I := I) D.pullbackMetric D.limitMetric
        (le_trans zero_le_one hQ.le) zero_le_one hγ
        (fun t _ v ↦ hinner (γ t) (hγK t) v)
  let gT : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) :=
    Y.metric.restrictOpen (I := I) (metricTargetOpenSubset (I := I) Φ k)
  have hpullTarget : Variation.arcLength (I := I) D.pullbackMetric γ 0 1 =
      Variation.arcLength (I := I) gT (F ∘ γ) 0 1 := by
    change Variation.arcLength (I := I)
        (Diffeomorph.pullbackMetric (I := I) gT F) γ 0 1 = _
    exact arcLength_localPullMetric_eq (I := I) gT F
      F.isLocalDiffeomorph zero_le_one hγ
  have hFγ : F ∘ γ = joinT ∘ Set.projIcc 0 1 zero_le_one := by
    funext t
    apply Subtype.ext
    exact hγmap t
  have hjoinTγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      (joinT ∘ Set.projIcc 0 1 zero_le_one) (Set.Icc 0 1) :=
    ((contMDiffOn_comp_projIcc_iff (x := (0 : ℝ)) (y := 1)).2
      (hjoinTSmooth.of_le (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))))
  have htargetAmbient : Variation.arcLength (I := I) gT
      (joinT ∘ Set.projIcc 0 1 zero_le_one) 0 1 =
      Variation.arcLength (I := I) Y.metric
        ((Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M) ∘
          (joinT ∘ Set.projIcc 0 1 zero_le_one)) 0 1 :=
    arcLength_restrictOpen_eq (I := I) Y.metric
      (metricTargetOpenSubset (I := I) Φ k) zero_le_one hjoinTγ
  let joinClamp : ℝ → Y.M :=
    (Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M) ∘
      (joinT ∘ Set.projIcc 0 1 zero_le_one)
  have hjoinClamp : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 joinClamp
      (Set.Icc 0 1) := by
    exact ((contMDiff_subtype_val (I := I)
      (U := metricTargetOpenSubset (I := I) Φ k) (n := (∞ : WithTop ℕ∞))).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).comp_contMDiffOn hjoinTγ
  have hclampEq : Set.EqOn joinClamp join (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    change join (Set.projIcc 0 1 zero_le_one t) = join t
    rw [Set.projIcc_of_mem zero_le_one ht]
  have hjoinC1 : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 join
      (Set.Icc 0 1) :=
    (hjoinSmooth.of_le (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).contMDiffOn
  have htargetJoin : Variation.arcLength (I := I) Y.metric joinClamp 0 1 =
      Variation.arcLength (I := I) Y.metric join 0 1 :=
    arcLength_congr_of_eqOn (I := I) Y.metric zero_le_one
      hjoinClamp hjoinC1 hclampEq
  have hpull : Variation.arcLength (I := I) D.pullbackMetric γ 0 1 =
      (riemannianEDist I Y.basepoint y).toReal := by
    rw [hpullTarget, hFγ, htargetAmbient, htargetJoin]
    exact minJoin_arcLength (I := I) Y.metric hEnorm Y.basepoint y
  have hpull_lt : Variation.arcLength (I := I) D.pullbackMetric γ 0 1 < s := by
    rw [hpull]
    have htop : riemannianEDist I Y.basepoint y ≠ (∞ : ℝ≥0∞) :=
      Exponential.riemannianEDist_ne_top (I := I) Y.basepoint y
    have hy : riemannianEDist I Y.basepoint y < ENNReal.ofReal s := hx
    exact ENNReal.toReal_lt_of_lt_ofReal hy
  have harcLimit : Variation.arcLength (I := I) D.limitMetric γ 0 1 < r := by
    refine lt_of_le_of_lt harcComp ?_
    exact (mul_lt_mul_of_pos_left hpull_lt (Real.sqrt_pos.2 (zero_lt_one.trans hQ))).trans
      hbuffer
  let valγ : ℝ → L.M := (Subtype.val : MetricSourceDomain (I := I) Φ k → L.M) ∘ γ
  have hvalγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 valγ (Set.Icc 0 1) :=
    ((contMDiff_subtype_val (I := I) (U := metricSourceOpenSubset (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞))).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).comp_contMDiffOn hγ
  have hlimitAmbient : Variation.arcLength (I := I) D.limitMetric γ 0 1 =
      Variation.arcLength (I := I) L.metric valγ 0 1 :=
    arcLength_restrictOpen_eq (I := I) L.metric
      (metricSourceOpenSubset (I := I) Φ k) zero_le_one hγ
  have hed := edistOf_le_arcLength (I := I) L.metric zero_le_one hvalγ
  change riemannianEDistOf (I := I) L.metric L.basepoint (x : L.M) < ENNReal.ofReal r
  have hval0 : valγ 0 = L.basepoint := by
    simp only [valγ, Function.comp_apply, hγ0, baseS]
  have hval1 : valγ 1 = (x : L.M) := by simp only [valγ, Function.comp_apply, hγ1]
  rw [hval0, hval1] at hed
  rw [← hlimitAmbient] at hed
  exact hed.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
    exact lt_of_le_of_lt (mul_nonneg (Real.sqrt_nonneg _) hs.le) hbuffer)).2 harcLimit)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem pointedEmbeddingPreimage_openBall_subset_metricSourceSet_of_capture
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ)
    {K : Set L.M} (hKsrc : K ⊆ Φ.source k)
    {s : ℝ}
    (hcapture : pointedClosedBall (I := I) (X.obj (subseq k)) s ⊆ Φ.map k '' K) :
    pointedEmbeddingPreimage (I := I) Φ k
        (pointedOpenBall (I := I) (X.obj (subseq k)) s) ⊆
      metricSourceSet (I := I) Φ k K := by
  let Y := X.obj (subseq k)
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  intro x hx
  have hxclosed : Φ.map k (x : L.M) ∈
      pointedClosedBall (I := I) Y s := by
    change riemannianEDistOf (I := I) Y.metric Y.basepoint (Φ.map k (x : L.M)) ≤
      ENNReal.ofReal s
    change riemannianEDistOf (I := I) Y.metric Y.basepoint (Φ.map k (x : L.M)) <
      ENNReal.ofReal s at hx
    exact hx.le
  obtain ⟨z, hzK, hzx⟩ := hcapture hxclosed
  change (x : L.M) ∈ K
  have hzsrc : z ∈ Φ.source k := hKsrc hzK
  have heq : z = (x : L.M) :=
    (Φ.partialDiffeomorph k).toPartialEquiv.injOn hzsrc x.property hzx
  rwa [← heq]

theorem eventually_captured_openBall_preimage_subset_limitOpenBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    (capture : CapturesSourceBalls (I := I) X L subseq Φ)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {s r Q : ℝ} (hs : 0 < s) (hQ : 1 < Q)
    (hbuffer : Real.sqrt Q * s < r) :
    ∃ K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) ∧
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        K ⊆ Φ.source k ∧
        pointedEmbeddingPreimage (I := I) Φ k
            (pointedOpenBall (I := I) (X.obj (subseq k)) s) ⊆
          metricSourceSet (I := I) Φ k K ∧
        pointedEmbeddingPreimage (I := I) Φ k
            (pointedOpenBall (I := I) (X.obj (subseq k)) s) ⊆
          metricSourceSet (I := I) Φ k (pointedOpenBall (I := I) L r) := by
  obtain ⟨K, hK, kcap, hkcap⟩ := capture.exists_compact_capture hs
  obtain ⟨kmetric, hkmetric⟩ :=
    eventually_limit_inner_le_pullback_on_compact (I := I) C hK hQ
  refine ⟨K, hK, max kcap kmetric, fun k hk ↦ ?_⟩
  have hkcap' := hkcap k (le_trans (Nat.le_max_left _ _) hk)
  have hkmetric' := hkmetric k (le_trans (Nat.le_max_right _ _) hk)
  refine ⟨hkcap'.1,
    pointedEmbeddingPreimage_openBall_subset_metricSourceSet_of_capture
      (I := I) Φ k hkcap'.1 hkcap'.2, ?_⟩
  exact pointedEmbeddingPreimage_openBall_subset_limitOpenBall_of_capture
    (I := I) Φ k (hcomplete.complete (subseq k)) (hconn (subseq k))
      hkcap'.1 hs hQ hbuffer hkcap'.2 hkmetric'.2

omit [I.Boundaryless] in
theorem eventually_pullback_volume_le_on_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    {K : Set L.M}
    (hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    {Q : ℝ} (hQ : 1 < Q) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      K ⊆ Φ.source k ∧
      let D := canonicalMetricSourceData (I := I) Φ k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
      letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
      letI : MeasurableSpace (MetricSourceDomain (I := I) Φ k) :=
        borel (MetricSourceDomain (I := I) Φ k)
      letI : BorelSpace (MetricSourceDomain (I := I) Φ k) := ⟨rfl⟩
      ∀ A : Set (MetricSourceDomain (I := I) Φ k), MeasurableSet A →
        A ⊆ metricSourceSet (I := I) Φ k K →
        riemannianVolumeMeasure (I := I) (M := MetricSourceDomain (I := I) Φ k)
            D.pullbackMetric A ≤
          ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
            riemannianVolumeMeasure (I := I)
              (M := MetricSourceDomain (I := I) Φ k) D.limitMetric A := by
  obtain ⟨k0, hk0⟩ :=
    eventually_pullback_inner_le_on_compact (I := I) C hK hQ
  refine ⟨k0, fun k hk ↦ ?_⟩
  obtain ⟨hsrc, hinner⟩ := hk0 k hk
  refine ⟨hsrc, ?_⟩
  dsimp only
  let D := canonicalMetricSourceData (I := I) Φ k
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  let : MeasurableSpace (MetricSourceDomain (I := I) Φ k) :=
    borel (MetricSourceDomain (I := I) Φ k)
  let : BorelSpace (MetricSourceDomain (I := I) Φ k) := ⟨rfl⟩
  intro A hA hAK
  apply riemannianVolumeMeasure_apply_le_of_inner_le_on
    (I := I) D.limitMetric D.pullbackMetric hA (zero_lt_one.trans hQ)
  intro x hx v
  exact hinner x (hAK hx) v

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem riemannianVolumeMeasure_map_pointedEmbedding
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ) :
    let D := canonicalMetricSourceData (I := I) Φ k
    let Y := X.obj (subseq k)
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : T2Space Y.M := Y.t2
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
    letI : MeasurableSpace (MetricSourceDomain (I := I) Φ k) :=
      borel (MetricSourceDomain (I := I) Φ k)
    letI : BorelSpace (MetricSourceDomain (I := I) Φ k) := ⟨rfl⟩
    letI : MeasurableSpace Y.M := borel Y.M
    letI : BorelSpace Y.M := ⟨rfl⟩
    Measure.map (fun x : MetricSourceDomain (I := I) Φ k ↦ Φ.map k (x : L.M))
        (riemannianVolumeMeasure (I := I)
          (M := MetricSourceDomain (I := I) Φ k) D.pullbackMetric) =
      (riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric).restrict
        (Φ.target k) := by
  dsimp only
  let D := canonicalMetricSourceData (I := I) Φ k
  let Y := X.obj (subseq k)
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : T2Space Y.M := Y.t2
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  let : MeasurableSpace (MetricSourceDomain (I := I) Φ k) :=
    borel (MetricSourceDomain (I := I) Φ k)
  let : BorelSpace (MetricSourceDomain (I := I) Φ k) := ⟨rfl⟩
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  let : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_t2 (I := I) Φ k
  let : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  let : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) := by
    exact isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (Φ.target_open k))
  let : MeasurableSpace (MetricTargetDomain (I := I) Φ k) :=
    borel (MetricTargetDomain (I := I) Φ k)
  let : BorelSpace (MetricTargetDomain (I := I) Φ k) := ⟨rfl⟩
  let : MeasurableSpace Y.M := borel Y.M
  let : BorelSpace Y.M := ⟨rfl⟩
  let F : MetricSourceDomain (I := I) Φ k ≃ₘ⟮I, I⟯
      MetricTargetDomain (I := I) Φ k := metricSourceTargetDiffeomorph (I := I) Φ k
  let gT : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) :=
    Y.metric.restrictOpen (I := I) (metricTargetOpenSubset (I := I) Φ k)
  have hFmeas : Measurable (F : MetricSourceDomain (I := I) Φ k →
      MetricTargetDomain (I := I) Φ k) := F.continuous.measurable
  have hvalmeas : Measurable
      (Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M) :=
    continuous_subtype_val.measurable
  have hpull : Measure.map F
      (riemannianVolumeMeasure (I := I)
        (M := MetricSourceDomain (I := I) Φ k) D.pullbackMetric) =
      riemannianVolumeMeasure (I := I)
        (M := MetricTargetDomain (I := I) Φ k) gT := by
    have hmetric : D.pullbackMetric = Diffeomorph.pullbackMetric gT F := by
      rfl
    rw [hmetric]
    simpa only using
      (riemannianVolumeMeasure_map_pullback (I := I) gT F)
  have hopen : Measure.map
      (Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M)
      (riemannianVolumeMeasure (I := I)
        (M := MetricTargetDomain (I := I) Φ k) gT) =
      (riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric).restrict
        (Φ.target k) := by
    convert riemannianVolumeMeasure_map_restrictOpen
      (I := I) Y.metric (metricTargetOpenSubset (I := I) Φ k) using 1
    all_goals rfl
  calc
    Measure.map (fun x : MetricSourceDomain (I := I) Φ k ↦ Φ.map k (x : L.M))
        (riemannianVolumeMeasure (I := I)
          (M := MetricSourceDomain (I := I) Φ k) D.pullbackMetric) =
      Measure.map (Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M)
        (Measure.map F
          (riemannianVolumeMeasure (I := I)
            (M := MetricSourceDomain (I := I) Φ k) D.pullbackMetric)) := by
        rw [Measure.map_map hvalmeas hFmeas]
        congr 1
    _ = Measure.map (Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M)
        (riemannianVolumeMeasure (I := I)
          (M := MetricTargetDomain (I := I) Φ k) gT) := by rw [hpull]
    _ = (riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric).restrict
        (Φ.target k) := hopen

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem riemannianVolumeMeasure_pointedEmbedding_preimage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ)
    {A : Set (X.obj (subseq k)).M}
    (hA : letI : TopologicalSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).topology
      letI : MeasurableSpace (X.obj (subseq k)).M :=
        borel (X.obj (subseq k)).M
      MeasurableSet A)
    (hAtarget : A ⊆ Φ.target k) :
    let D := canonicalMetricSourceData (I := I) Φ k
    let Y := X.obj (subseq k)
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : T2Space Y.M := Y.t2
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
    letI : MeasurableSpace (MetricSourceDomain (I := I) Φ k) :=
      borel (MetricSourceDomain (I := I) Φ k)
    letI : BorelSpace (MetricSourceDomain (I := I) Φ k) := ⟨rfl⟩
    letI : MeasurableSpace Y.M := borel Y.M
    letI : BorelSpace Y.M := ⟨rfl⟩
    riemannianVolumeMeasure (I := I)
        (M := MetricSourceDomain (I := I) Φ k) D.pullbackMetric
        (pointedEmbeddingPreimage (I := I) Φ k A) =
      riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric A := by
  dsimp only
  let D := canonicalMetricSourceData (I := I) Φ k
  let Y := X.obj (subseq k)
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : T2Space Y.M := Y.t2
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  let : MeasurableSpace (MetricSourceDomain (I := I) Φ k) :=
    borel (MetricSourceDomain (I := I) Φ k)
  let : BorelSpace (MetricSourceDomain (I := I) Φ k) := ⟨rfl⟩
  let : MeasurableSpace Y.M := borel Y.M
  let : BorelSpace Y.M := ⟨rfl⟩
  let f : MetricSourceDomain (I := I) Φ k → Y.M :=
    fun x ↦ Φ.map k (x : L.M)
  have hf : Measurable f := by
    let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    let F : MetricSourceDomain (I := I) Φ k ≃ₘ⟮I, I⟯
        MetricTargetDomain (I := I) Φ k := metricSourceTargetDiffeomorph (I := I) Φ k
    have hcomp : f = (Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M) ∘ F := by
      funext x
      exact (metric_source_target_diffeomorph_apply (I := I) Φ k x).symm
    rw [hcomp]
    exact continuous_subtype_val.measurable.comp F.continuous.measurable
  have hmeasure := congrArg (fun μ : Measure Y.M ↦ μ A)
    (riemannianVolumeMeasure_map_pointedEmbedding (I := I) Φ k)
  rw [Measure.map_apply hf hA, Measure.restrict_apply hA] at hmeasure
  have hinter : A ∩ Φ.target k = A := inter_eq_self_of_subset_left hAtarget
  rw [hinter] at hmeasure
  exact hmeasure

theorem eventually_captured_ball_volume_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    (capture : CapturesSourceBalls (I := I) X L subseq Φ)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {s r Q : ℝ} (hs : 0 < s) (hQ : 1 < Q)
    (hbuffer : Real.sqrt Q * s < r) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      let Y := X.obj (subseq k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : T2Space Y.M := Y.t2
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : MeasurableSpace Y.M := borel Y.M
      letI : BorelSpace Y.M := ⟨rfl⟩
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : MeasurableSpace L.M := borel L.M
      letI : BorelSpace L.M := ⟨rfl⟩
      riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
          (pointedOpenBall (I := I) Y s) ≤
        ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
          riemannianVolumeMeasure (I := I) (M := L.M) L.metric
            (pointedOpenBall (I := I) L r) := by
  obtain ⟨K, hK, kbuffer, hkbuffer⟩ :=
    eventually_captured_openBall_preimage_subset_limitOpenBall
      (I := I) C capture hcomplete hconn hs hQ hbuffer
  obtain ⟨kvolume, hkvolume⟩ :=
    eventually_pullback_volume_le_on_compact (I := I) C hK hQ
  obtain ⟨ktarget, hktarget⟩ := capture.eventually_closedBall_subset_target hs
  refine ⟨max kbuffer (max kvolume ktarget), fun k hk ↦ ?_⟩
  have hkbuf := hkbuffer k (le_trans (Nat.le_max_left _ _) hk)
  have hkvol := hkvolume k
    (le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hk))
  have hktgt := hktarget k
    (le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hk))
  dsimp only
  let Y := X.obj (subseq k)
  let D := canonicalMetricSourceData (I := I) Φ k
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : T2Space Y.M := Y.t2
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : MeasurableSpace Y.M := borel Y.M
  let : BorelSpace Y.M := ⟨rfl⟩
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : MeasurableSpace L.M := borel L.M
  let : BorelSpace L.M := ⟨rfl⟩
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  let : MeasurableSpace (MetricSourceDomain (I := I) Φ k) :=
    borel (MetricSourceDomain (I := I) Φ k)
  let : BorelSpace (MetricSourceDomain (I := I) Φ k) := ⟨rfl⟩
  let A : Set (MetricSourceDomain (I := I) Φ k) :=
    pointedEmbeddingPreimage (I := I) Φ k (pointedOpenBall (I := I) Y s)
  have hsourceOpen : IsOpen (pointedOpenBall (I := I) Y s) :=
    pointedOpenBall_isOpen (I := I) Y s
  have hsourceMeas : MeasurableSet (pointedOpenBall (I := I) Y s) :=
    hsourceOpen.measurableSet
  let f : MetricSourceDomain (I := I) Φ k → Y.M :=
    fun x ↦ Φ.map k (x : L.M)
  have hf : Measurable f := by
    let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    let F : MetricSourceDomain (I := I) Φ k ≃ₘ⟮I, I⟯
        MetricTargetDomain (I := I) Φ k := metricSourceTargetDiffeomorph (I := I) Φ k
    have hcomp : f =
        (Subtype.val : MetricTargetDomain (I := I) Φ k → Y.M) ∘ F := by
      funext x
      exact (metric_source_target_diffeomorph_apply (I := I) Φ k x).symm
    rw [hcomp]
    exact continuous_subtype_val.measurable.comp F.continuous.measurable
  have hAmeas : MeasurableSet A := by
    change MeasurableSet (f ⁻¹' pointedOpenBall (I := I) Y s)
    exact hsourceMeas.preimage hf
  have hAtarget : pointedOpenBall (I := I) Y s ⊆ Φ.target k := by
    intro y hy
    apply hktgt
    change riemannianEDistOf (I := I) Y.metric Y.basepoint y ≤ ENNReal.ofReal s
    change riemannianEDistOf (I := I) Y.metric Y.basepoint y < ENNReal.ofReal s at hy
    exact hy.le
  have heq := riemannianVolumeMeasure_pointedEmbedding_preimage
    (I := I) Φ k hsourceMeas hAtarget
  have hpullLe := hkvol.2 A hAmeas hkbuf.2.1
  have hlimitOpen : IsOpen (pointedOpenBall (I := I) L r) :=
    pointedOpenBall_isOpen (I := I) L r
  let sourceOpenSigma : SigmaCompactSpace (metricSourceOpenSubset (I := I) Φ k) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k))
  let : SigmaCompactSpace (metricSourceOpenSubset (I := I) Φ k) := sourceOpenSigma
  have hlimitLe :
      riemannianVolumeMeasure (I := I)
          (M := MetricSourceDomain (I := I) Φ k) D.limitMetric A ≤
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (pointedOpenBall (I := I) L r) := by
    exact @riemannianVolumeMeasure_restrictOpen_le_of_image_subset
      E _ _ _ H _ I _ L.M _ _ _ _ _ L.metric
      (metricSourceOpenSubset (I := I) Φ k) D.t2 sourceOpenSigma A
      (pointedOpenBall (I := I) L r) hlimitOpen.measurableSet
      (fun x hx ↦ hkbuf.2.2 hx)
  calc
    riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
        (pointedOpenBall (I := I) Y s) =
      riemannianVolumeMeasure (I := I)
        (M := MetricSourceDomain (I := I) Φ k) D.pullbackMetric A := heq.symm
    _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I)
          (M := MetricSourceDomain (I := I) Φ k) D.limitMetric A := hpullLe
    _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (pointedOpenBall (I := I) L r) := by
      simpa only [mul_comm] using
        (mul_le_mul_right hlimitLe
          (ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E))))

theorem buffered_pointedBallVolume_lower_of_source_AVR
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    (capture : CapturesSourceBalls (I := I) X L subseq Φ)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {v : ℝ≥0∞}
    (hAVR : ∀ i : ℕ, v ≤ pointedAsymptoticVolumeRatio (I := I) (X.obj i))
    {s r Q : ℝ} (hs : 0 < s) (hQ : 1 < Q)
    (hbuffer : Real.sqrt Q * s < r) :
    v * ENNReal.ofReal
        (euclideanUnitBallVolume (Module.finrank ℝ E) *
          s ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        pointedBallVolume (I := I) L r := by
  obtain ⟨k0, hk0⟩ := eventually_captured_ball_volume_le
    (I := I) C capture hcomplete hconn hs hQ hbuffer
  let Y := X.obj (subseq k0)
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : T2Space Y.M := Y.t2
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : MeasurableSpace Y.M := borel Y.M
  let : BorelSpace Y.M := ⟨rfl⟩
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : MeasurableSpace L.M := borel L.M
  let : BorelSpace L.M := ⟨rfl⟩
  let den : ℝ≥0∞ := ENNReal.ofReal
    (euclideanUnitBallVolume (Module.finrank ℝ E) *
      s ^ Module.finrank ℝ E)
  have hsourceLower : v * den ≤ pointedBallVolume (I := I) Y s := by
    calc
      v * den ≤ pointedAsymptoticVolumeRatio (I := I) Y * den :=
        by simpa only [mul_comm] using
          (mul_le_mul_right (hAVR (subseq k0)) den)
      _ ≤ pointedBallVolume (I := I) Y s :=
        pointedAsymptoticVolumeRatio_mul_euclidean_le_pointedBallVolume
          (I := I) Y hs
  have hvol := hk0 k0 le_rfl
  have hsourceEq :=
    riemannianVolumeMeasure_pointedOpenBall_eq_pointedBallVolume
      (I := I) Y s
  have hlimitEq :=
    riemannianVolumeMeasure_pointedOpenBall_eq_pointedBallVolume
      (I := I) L r
  dsimp only at hvol
  change v * den ≤ _
  calc
    v * den ≤ pointedBallVolume (I := I) Y s := hsourceLower
    _ = riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
        (pointedOpenBall (I := I) Y s) := hsourceEq.symm
    _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (pointedOpenBall (I := I) L r) := hvol
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        pointedBallVolume (I := I) L r := congrArg _ hlimitEq

theorem pointedBallVolume_lower_of_source_AVR
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    (capture : CapturesSourceBalls (I := I) X L subseq Φ)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {v : ℝ≥0∞}
    (hAVR : ∀ i : ℕ, v ≤ pointedAsymptoticVolumeRatio (I := I) (X.obj i))
    {r : ℝ} (hr : 0 < r) :
    v * ENNReal.ofReal
        (euclideanUnitBallVolume (Module.finrank ℝ E) *
          r ^ Module.finrank ℝ E) ≤
      pointedBallVolume (I := I) L r := by
  let n : ℕ := Module.finrank ℝ E
  let q : ℕ → ℝ := fun m ↦ 1 + 1 / ((m : ℝ) + 1)
  let Q : ℕ → ℝ := fun m ↦ (q m) ^ 2
  let s : ℕ → ℝ := fun m ↦ r / Q m
  have hq_one (m : ℕ) : 1 < q m := by
    dsimp only [q]
    have : 0 < (m : ℝ) + 1 := by positivity
    linarith [one_div_pos.mpr this]
  have hq_pos (m : ℕ) : 0 < q m := zero_lt_one.trans (hq_one m)
  have hQ_one (m : ℕ) : 1 < Q m := by
    dsimp only [Q]
    nlinarith [hq_one m, sq_nonneg (q m - 1)]
  have hs_pos (m : ℕ) : 0 < s m :=
    div_pos hr (sq_pos_of_pos (hq_pos m))
  have hbuffer (m : ℕ) : Real.sqrt (Q m) * s m < r := by
    rw [show Real.sqrt (Q m) = q m by
      dsimp only [Q]
      exact Real.sqrt_sq (hq_pos m).le]
    have hq_ne : q m ≠ 0 := (hq_pos m).ne'
    calc
      q m * s m = r / q m := by
        dsimp only [s, Q]
        field_simp
      _ < r := div_lt_self hr (hq_one m)
  have hq_lim : Tendsto q atTop (𝓝 (1 : ℝ)) := by
    simpa only [q, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hQ_lim : Tendsto Q atTop (𝓝 (1 : ℝ)) := by
    simpa only [Q, one_pow] using hq_lim.pow 2
  have hs_lim : Tendsto s atTop (𝓝 r) := by
    change Tendsto ((fun _ : ℕ ↦ r) / Q) atTop (𝓝 r)
    simpa only [div_one] using
      tendsto_const_nhds.div hQ_lim (by norm_num : (1 : ℝ) ≠ 0)
  have hcoeffReal : Tendsto
      (fun m ↦ Real.sqrt ((Q m) ^ n)) atTop (𝓝 (1 : ℝ)) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp (hQ_lim.pow n)
    change Tendsto ((fun x : ℝ ↦ Real.sqrt x) ∘
      (fun m ↦ (Q m) ^ n)) atTop (𝓝 (1 : ℝ))
    simpa only [one_pow, Real.sqrt_one] using hsqrt
  have hcoeff : Tendsto
      (fun m ↦ ENNReal.ofReal (Real.sqrt ((Q m) ^ n))) atTop
      (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hcoeffReal
  have hright : Tendsto
      (fun m ↦ ENNReal.ofReal (Real.sqrt ((Q m) ^ n)) *
        pointedBallVolume (I := I) L r) atTop
      (𝓝 (pointedBallVolume (I := I) L r)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoeff (Or.inl one_ne_zero)
  have hdenReal : Tendsto
      (fun m ↦ euclideanUnitBallVolume n * (s m) ^ n) atTop
      (𝓝 (euclideanUnitBallVolume n * r ^ n)) :=
    tendsto_const_nhds.mul (hs_lim.pow n)
  have hden : Tendsto
      (fun m ↦ ENNReal.ofReal
        (euclideanUnitBallVolume n * (s m) ^ n)) atTop
      (𝓝 (ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n))) :=
    ENNReal.tendsto_ofReal hdenReal
  have hden_pos : 0 < ENNReal.ofReal
      (euclideanUnitBallVolume n * r ^ n) := by
    exact ENNReal.ofReal_pos.mpr
      (mul_pos (euclideanUnitBallVolume_pos n) (pow_pos hr n))
  have hleft : Tendsto
      (fun m ↦ v * ENNReal.ofReal
        (euclideanUnitBallVolume n * (s m) ^ n)) atTop
      (𝓝 (v * ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n))) :=
    ENNReal.Tendsto.const_mul hden (Or.inl hden_pos.ne')
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [] with m
  exact buffered_pointedBallVolume_lower_of_source_AVR
    (I := I) C capture hcomplete hconn hAVR (hs_pos m) (hQ_one m) (hbuffer m)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem le_pointedAsymptoticVolumeRatio_of_ballVolume_lower
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {v : ℝ≥0∞}
    (hvolume : ∀ {r : ℝ}, 0 < r →
      v * ENNReal.ofReal
          (euclideanUnitBallVolume (Module.finrank ℝ E) *
            r ^ Module.finrank ℝ E) ≤
        pointedBallVolume (I := I) Y r) :
    v ≤ pointedAsymptoticVolumeRatio (I := I) Y := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.toRiemannianMetric⟩
  unfold pointedAsymptoticVolumeRatio asymptoticVolumeRatio
  apply le_iInf
  intro R
  let den : ℝ≥0∞ := ENNReal.ofReal
    (euclideanUnitBallVolume (Module.finrank ℝ E) *
      R.1 ^ Module.finrank ℝ E)
  have hden_pos : 0 < den := by
    exact ENNReal.ofReal_pos.mpr
      (mul_pos (euclideanUnitBallVolume_pos (Module.finrank ℝ E))
        (pow_pos R.2 (Module.finrank ℝ E)))
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden_pos.ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  simpa only [normalizedBallVolume, den, pointedBallVolume] using hvolume R.2

theorem pointedAsymptoticVolumeRatio_lower_of_source_AVR
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    (capture : CapturesSourceBalls (I := I) X L subseq Φ)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {v : ℝ≥0∞}
    (hAVR : ∀ i : ℕ, v ≤ pointedAsymptoticVolumeRatio (I := I) (X.obj i)) :
    v ≤ pointedAsymptoticVolumeRatio (I := I) L := by
  apply le_pointedAsymptoticVolumeRatio_of_ballVolume_lower (I := I) L
  intro r hr
  exact pointedBallVolume_lower_of_source_AVR
    (I := I) C capture hcomplete hconn hAVR hr

omit [CompleteSpace E] [I.Boundaryless] in
theorem not_compactSpace_of_pos_le_pointedAsymptoticVolumeRatio
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {v : ℝ≥0∞} (hv : 0 < v)
    (hAVR : v ≤ pointedAsymptoticVolumeRatio (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    ¬ CompactSpace Y.M := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    ⟨Y.metric.toRiemannianMetric⟩
  apply not_compactSpace_of_pos_le_asymptoticVolumeRatio
    (I := I) Y.metric Y.basepoint hv
  simpa only [pointedAsymptoticVolumeRatio] using hAVR

theorem pointedAsymptoticVolumeRatio_lower_and_noncompact_of_source_AVR
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    (capture : CapturesSourceBalls (I := I) X L subseq Φ)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {v : ℝ≥0∞} (hv : 0 < v)
    (hAVR : ∀ i : ℕ, v ≤ pointedAsymptoticVolumeRatio (I := I) (X.obj i)) :
    (letI : TopologicalSpace L.M := L.topology; NoncompactSpace L.M) ∧
      v ≤ pointedAsymptoticVolumeRatio (I := I) L := by
  have hlimitAVR := pointedAsymptoticVolumeRatio_lower_of_source_AVR
    (I := I) C capture hcomplete hconn hAVR
  refine ⟨?_, hlimitAVR⟩
  let : TopologicalSpace L.M := L.topology
  exact not_compactSpace_iff.mp
    (not_compactSpace_of_pos_le_pointedAsymptoticVolumeRatio
      (I := I) L hv hlimitAVR)

theorem pointedAsymptoticVolumeRatio_lower_and_noncompact_of_source_AVR_real
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    (capture : CapturesSourceBalls (I := I) X L subseq Φ)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {v : ℝ} (hv : 0 < v)
    (hAVR : ∀ i : ℕ, ENNReal.ofReal v ≤
      pointedAsymptoticVolumeRatio (I := I) (X.obj i)) :
    (letI : TopologicalSpace L.M := L.topology; NoncompactSpace L.M) ∧
      ENNReal.ofReal v ≤ pointedAsymptoticVolumeRatio (I := I) L := by
  exact pointedAsymptoticVolumeRatio_lower_and_noncompact_of_source_AVR
    (I := I) C capture hcomplete hconn (ENNReal.ofReal_pos.mpr hv) hAVR

end Poincare.Geometry.Riemannian.VolumeComparison
