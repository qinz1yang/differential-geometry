import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.IntrinsicSmoothness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Framed
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalJetBounds

section

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

local instance localMetricFormNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance localMetricFormNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.NormalCoordinates

theorem exists_eventually_intrinsicFrameMetric_iteratedFDeriv_norm_le_on_ball
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : Nat,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    {R r U : Real} (hr : 0 ≤ r) (hrR : r < R) (hUR : U ≤ R - r)
    (hjets : ∀ p : Nat, ∃ C : Real, 0 ≤ C ∧
      ∀ᶠ i in Filter.atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal R → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (n : Nat) :
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
            ENNReal.ofReal r →
          ∀ z : E, ‖z‖ ≤ U →
            ‖iteratedFDeriv Real n
              (intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x) z‖ ≤ Cb := by
  classical
  choose C hC hCb using hjets
  have hsta : ∀ᶠ i in Filter.atTop, ∀ k ∈ Finset.range (n + 2),
      HasLocalCurvDerivBound (I := I) (X.obj i) (X.obj i).basepoint R k (C k) := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact hCb k
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
    intro hEnorm x hx z hz
    apply intrinsic_frame_metric_iterated_fderiv_norm_le_local_order (I := I)
      (X.obj i) (hcomplete.complete i) (hconn i) x (A := R - r)
      (n + 1) C hC ?_ z n U hUR hz (le_refl (n + 1))
    · exact (contDiff_intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x).contDiffAt
    · intro k hk y hy
      exact hi k (Finset.mem_range.mpr (by omega)) y (by
        calc riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint y
            ≤ riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x +
              riemannianEDistOf (I := I) (X.obj i).metric x y :=
              riemannianEDistOf_triangle (I := I) (X.obj i).metric _ _ _
          _ ≤ ENNReal.ofReal r + ENNReal.ofReal (R - r) := add_le_add hx hy
          _ = ENNReal.ofReal (r + (R - r)) :=
            (ENNReal.ofReal_add hr (sub_nonneg.mpr hrR.le)).symm
          _ = ENNReal.ofReal R := by congr 1; ring)

end CheegerGromovCompactness
end DifferentialGeometry

end

end
