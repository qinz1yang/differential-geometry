import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FiniteHistorySeedBoundCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ObservationTower

/-!
# CX-SPINE: the bounded-time part of the prepared-chain scalar estimate

The fixed observation N supplies every geometric input of the finite-history
low-base theorem. Each query in any observation is compared at its actual time
using the same tower's atIndex_independent theorem. Only the two scalar values
and their distance are transported; the parabolic seed stays in its source.
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

private theorem early_metric_points_transport_CXSP
    {P Q : OrientedThreeStage.{u}} (hP : P = Q)
    {gP : P.Metric} {gQ : Q.Metric} (hg : HEq gP gQ)
    (p x : P.Carrier) :
    ∃ p' x' : Q.Carrier,
      metricScalarAt gQ p' = metricScalarAt gP p ∧
      metricScalarAt gQ x' = metricScalarAt gP x ∧
      riemannianEDistOf gQ p' x' = riemannianEDistOf gP p x := by
  cases hP
  cases eq_of_heq hg
  exact ⟨p, x, rfl, rfl, rfl⟩

private theorem early_tower_slice_transport_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (n N : ℕ)
    (t : Icc (0 : ℝ) (T.history n).horizon) (htN : (t : ℝ) ≤ (N : ℝ))
    (p x : ((T.history n).stageAt t).Carrier) :
    let tN : Icc (0 : ℝ) (T.history N).horizon :=
      ⟨t, t.2.1, htN.trans_eq (T.horizon_eq N).symm⟩
    ∃ pN xN : ((T.history N).stageAt tN).Carrier,
      metricScalarAt ((T.history N).stageMetric ((T.history N).activeStage tN) tN) pN =
        metricScalarAt ((T.history n).stageMetric ((T.history n).activeStage t) t) p ∧
      metricScalarAt ((T.history N).stageMetric ((T.history N).activeStage tN) tN) xN =
        metricScalarAt ((T.history n).stageMetric ((T.history n).activeStage t) t) x ∧
      riemannianEDistOf ((T.history N).stageMetric ((T.history N).activeStage tN) tN) pN xN =
        riemannianEDistOf ((T.history n).stageMetric ((T.history n).activeStage t) t) p x := by
  let tN : Icc (0 : ℝ) (T.history N).horizon :=
    ⟨t, t.2.1, htN.trans_eq (T.horizon_eq N).symm⟩
  let K := (T.history n).restrict t
  let L := (T.history N).restrict tN
  let uK : Icc (0 : ℝ) K.horizon := ⟨t, t.2.1, le_rfl⟩
  let uL : Icc (0 : ℝ) L.horizon := ⟨t, t.2.1, le_rfl⟩
  have htn : (t : ℝ) ≤ (n : ℝ) := t.2.2.trans_eq (T.horizon_eq n)
  have R : K.SamePresentation L := T.atIndex_independent n N t t.2.1 htn htN
  have eK : K.stageAt uK = (T.history n).stageAt t :=
    (T.history n).restrict_stageAt t uK
  have eL : L.stageAt uL = (T.history N).stageAt tN :=
    (T.history N).restrict_stageAt tN uL
  have eR : K.stageAt uK = L.stageAt uL := R.stageAt_eq uK
  have e : (T.history n).stageAt t = (T.history N).stageAt tN :=
    eK.symm.trans (eR.trans eL)
  have hm : HEq ((T.history n).stageMetric ((T.history n).activeStage t) t)
      ((T.history N).stageMetric ((T.history N).activeStage tN) tN) :=
    ((T.history n).restrict_sliceMetric t uK).symm.trans
      ((R.sliceMetric_heq uK).trans ((T.history N).restrict_sliceMetric tN uL))
  exact early_metric_points_transport_CXSP e hm p x

/-- All observations of an arbitrary prepared chain satisfy the same small-seed
scalar estimate below any fixed positive integer time. -/
theorem exists_prepared_early_scalar_bound_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (N : ℕ) (hN : 1 ≤ N) (A : ℝ) (hA : 0 < A) :
    ∃ rbar K : ℝ, 0 < rbar ∧ 0 < K ∧
      ∀ n, let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          (t : ℝ) ≤ (N : ℝ) → r ≤ rbar * Real.sqrt t →
          hasSmallParabolicCurvature H t p r →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
            metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ K * (r ^ 2)⁻¹ := by
  rw [hTower]
  let V := (S.observation N).history
  obtain ⟨r0, K, hr0, hK, hfinite⟩ := exists_finite_history_low_base_scalar_bound_CXSP
    V (S.observation N).initial (S.observation N).parameters (S.observation N).records
    (S.observation N).kappa C.epsilon (S.observation N).kappa_pos C.epsilon_pos
    (S.observation N).noncollapsed A hA
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hN)
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  let rbar : ℝ := r0 / Real.sqrt (N : ℝ)
  have hrbar : 0 < rbar := div_pos hr0 hsqrtN
  refine ⟨rbar, K, hrbar, hK, ?_⟩
  intro n H t p r htN hrr hsmall x hx
  have hr : 0 < r := hsmall.1
  have hrr0 : r ≤ r0 := calc
    r ≤ rbar * Real.sqrt t := hrr
    _ ≤ rbar * Real.sqrt (N : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htN) hrbar.le
    _ = r0 := div_mul_cancel₀ r0 hsqrtN.ne'
  have hpmem : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hseed := (le_abs_self _).trans
    (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hpmem)
  let T := S.tower.toObservationTower
  let tN : Icc (0 : ℝ) V.horizon :=
    ⟨t, t.2.1, by change (t : ℝ) ≤ (N : ℝ); exact htN⟩
  obtain ⟨pN, xN, hpN, hxN, hdN⟩ := early_tower_slice_transport_CXSP T n N t htN p x
  have hseedN : metricScalarAt
      (V.toHistory.stageMetric (V.toHistory.activeStage tN) tN) pN ≤ 3 * (r ^ 2)⁻¹ := by
    exact hpN.le.trans hseed
  have hballN : xN ∈ riemannianBallOf
      (V.toHistory.stageMetric (V.toHistory.activeStage tN) tN) pN (A * r) := by
    exact hdN.trans_lt hx
  have hbound := hfinite tN pN r hr hrr0 hseedN xN hballN
  exact hxN.symm.trans_le hbound

end GC.LongTime.Ch11
