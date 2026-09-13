import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Framed
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalJetBounds

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

local instance centeredJetBoundsFormNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance centeredJetBoundsFormNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.NormalCoordinates

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem HasLocalCurvDerivBound.mono_radius
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p : P.M) {A B : Real} (hBA : B ≤ A) {k : Nat} {C : Real}
    (h : HasLocalCurvDerivBound (I := I) P p A k C) :
    HasLocalCurvDerivBound (I := I) P p B k C := by
  intro y hy
  exact h y (hy.trans (ENNReal.ofReal_le_ofReal hBA))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem HasLocalCurvDerivBound.of_edist_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p x : P.M) {A r : Real} {k : Nat} {C : Real}
    (hr : 0 ≤ r) (hrA : 2 * r ≤ A)
    (h : HasLocalCurvDerivBound (I := I) P p A k C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    riemannianEDistOf (I := I) P.metric p x ≤ ENNReal.ofReal r →
      HasLocalCurvDerivBound (I := I) P x r k C := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  intro hx y hy
  exact h y (by
    calc riemannianEDistOf (I := I) P.metric p y
        ≤ riemannianEDistOf (I := I) P.metric p x +
          riemannianEDistOf (I := I) P.metric x y :=
          riemannianEDistOf_triangle (I := I) P.metric p x y
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add hx hy
      _ = ENNReal.ofReal (r + r) := (ENNReal.ofReal_add hr hr).symm
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (by linarith))

theorem intrinsic_frame_metric_iterated_fderiv_norm_le_of_edist_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p x : P.M) {A r : Real} (hr : 0 ≤ r) (hrA : 2 * r ≤ A)
    (N : Nat) (C : Nat → Real) (hC : ∀ k : Nat, 0 ≤ C k)
    (hN : ∀ k : Nat, k ≤ N →
      HasLocalCurvDerivBound (I := I) P p A k (C k))
    (z : E) (n : Nat) {U : Real} (hU : U ≤ r) (hzU : ‖z‖ ≤ U)
    (hx : letI : TopologicalSpace P.M := P.topology
          letI : ChartedSpace H P.M := P.charted
          letI : IsManifold I ∞ P.M := P.smooth
          letI : SigmaCompactSpace P.M := P.sigmaCompact
          letI : T2Space P.M := P.t2
          riemannianEDistOf (I := I) P.metric p x ≤ ENNReal.ofReal r) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun y : P.M => TangentSpace I y) :=
      P.riemBundle (I := I)
    letI : (y : P.M) → InnerProductSpace Real (TangentSpace I y) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : P.M => TangentSpace I y) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (y : P.M) (v : TangentSpace I y),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner y v v)) := by
      intro y v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric y v
    n + 1 ≤ N →
      ContDiffAt Real ∞
        (intrinsicFrameMetric (I := I) P.metric hEnorm x) z →
      ‖iteratedFDeriv Real n
          (intrinsicFrameMetric (I := I) P.metric hEnorm x) z‖ ≤
        ContinuousMultilinearMap.polarConst n *
          (2 * (2 ^ n * jacobiJetBound C U 1 n ^ 2)) := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun y : P.M => TangentSpace I y) :=
    P.riemBundle (I := I)
  let _ : (y : P.M) → InnerProductSpace Real (TangentSpace I y) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun y : P.M => TangentSpace I y) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (y : P.M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner y v v)) := by
    intro y v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric y v
  dsimp only
  intro hnN hsmooth
  exact intrinsic_frame_metric_iterated_fderiv_norm_le_local_order (I := I)
    P hcomplete hconn x N C hC
    (fun k hk => HasLocalCurvDerivBound.of_edist_le (I := I) P p x hr hrA
      (hN k hk) hx)
    z n (U := U) hU hzU hnN hsmooth

theorem exists_eventually_intrinsicFrameMetric_iteratedFDeriv_norm_le_of_edist_le_of_curvDerivNorm_eventually
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : Nat,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hjets : ∀ A : Real, 0 < A → ∀ p : Nat, ∃ C : Real, 0 ≤ C ∧
      ∀ᶠ i in Filter.atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (A : Real) (hA : 0 < A) (n : Nat) {U : Real} (hUA : U ≤ A / 2) :
    ∃ Cb : Real, 0 ≤ Cb ∧
      ∀ᶠ i in Filter.atTop,
        letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
        letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
        letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        letI : IsManifold I 1 (X.obj i).M :=
          IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)
        letI : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        letI : T2Space (X.obj i).M := (X.obj i).t2
        letI : T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle
        letI : RiemannianBundle (fun x : (X.obj i).M => TangentSpace I x) :=
          (X.obj i).riemBundle (I := I)
        letI : (x : (X.obj i).M) → InnerProductSpace Real (TangentSpace I x) :=
          (X.obj i).riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun x : (X.obj i).M => TangentSpace I x) :=
          (X.obj i).riemBundle_cont (I := I)
        letI : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
        letI : CompleteSpace (X.obj i).M :=
          MetricComplete.complete (I := I) (X.obj i) (hcomplete.complete i)
        letI : ConnectedSpace (X.obj i).M := hconn i
        let hEnorm : ∀ (x : (X.obj i).M) (v : TangentSpace I x),
            ‖v‖ₑ = ENNReal.ofReal
              (Real.sqrt ((X.obj i).metric.inner x v v)) := by
          intro x v
          with_unfolding_all
            exact
              Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (X.obj i).metric x v
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal (A / 2) →
          ∀ z : E, ‖z‖ ≤ U →
            ContDiffAt Real ∞
              (intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x) z →
            ‖iteratedFDeriv Real n
              (intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x) z‖ ≤ Cb := by
  classical
  obtain ⟨C, hC, hsta⟩ :=
    exists_forall_le_hasLocalCurvDerivBound_of_curvDerivNorm_eventually
      (I := I) X hjets A hA (n + 1)
  refine ⟨ContinuousMultilinearMap.polarConst n *
      (2 * (2 ^ n * jacobiJetBound C U 1 n ^ 2)), ?_, ?_⟩
  · exact mul_nonneg (ContinuousMultilinearMap.polarConst_nonneg n)
      (mul_nonneg (by norm_num)
        (mul_nonneg (pow_nonneg (by norm_num) n) (sq_nonneg _)))
  · refine hsta.mono fun i hi => ?_
    let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
    let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
    let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
    let _ : IsManifold I 1 (X.obj i).M :=
      IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)
    let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
    let _ : T2Space (X.obj i).M := (X.obj i).t2
    let _ : T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle
    let _ : RiemannianBundle (fun x : (X.obj i).M => TangentSpace I x) :=
      (X.obj i).riemBundle (I := I)
    let _ : (x : (X.obj i).M) → InnerProductSpace Real (TangentSpace I x) :=
      (X.obj i).riemInner (I := I)
    let _ : IsContinuousRiemannianBundle E
        (fun x : (X.obj i).M => TangentSpace I x) :=
      (X.obj i).riemBundle_cont (I := I)
    let _ : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
    let _ : CompleteSpace (X.obj i).M :=
      MetricComplete.complete (I := I) (X.obj i) (hcomplete.complete i)
    let _ : ConnectedSpace (X.obj i).M := hconn i
    intro hEnorm x hx z hz hcd
    exact intrinsic_frame_metric_iterated_fderiv_norm_le_of_edist_le (I := I)
      (X.obj i) (hcomplete.complete i) (hconn i) (X.obj i).basepoint x
      (A := A) (r := A / 2) (by linarith) (by linarith)
      (n + 1) C hC (fun k hk => hi k hk) z n (U := U) hUA hz hx
      (le_refl (n + 1)) hcd

theorem framedCoordMetric_eq_intrinsicFrameMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M :=
      MetricComplete.complete (I := I) Y hcomplete
    (hEnorm : ∀ (y : Y.M) (v : TangentSpace I y),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v))) →
    ∀ z : E, z ∈ (intrinsicFrameDiffeo (I := I) Y.metric hEnorm x).source →
      framedCoordMetric (I := I) Y x z =
        intrinsicFrameMetric (I := I) Y.metric hEnorm x z := by
  let _ : TopologicalSpace Y.M := Y.topology
  let _ : ChartedSpace H Y.M := Y.charted
  let _ : IsManifold I ∞ Y.M := Y.smooth
  let _ : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace Y.M := Y.sigmaCompact
  let _ : T2Space Y.M := Y.t2
  let _ : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let _ : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let _ : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle_cont (I := I)
  let _ : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let _ : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y hcomplete
  intro hEnorm z hz
  exact (intrinsicFrameMetric_eq (I := I) Y.metric hEnorm x hz).symm

end CheegerGromovCompactness
end DifferentialGeometry
