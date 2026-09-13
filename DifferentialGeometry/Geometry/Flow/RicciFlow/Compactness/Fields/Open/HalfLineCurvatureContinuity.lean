import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.SourceDomain
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem chartRiemannTensor_eq_sum_metricRm04At_mul_chartInvGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b c m : Fin (Module.finrank Real E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartRiemannTensor (I := I) g α c a b m (extChartAt I α x) =
      ∑ d : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) g α x m d *
          metricRm04At (I := I) g x
            (fun k : Fin 4 =>
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α
                (![a, b, c, d] k) x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hterm : ∀ d : Fin (Module.finrank Real E),
      metricRm04At (I := I) g x
          (fun k : Fin 4 =>
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α
              (![a, b, c, d] k) x) =
        ∑ l : Fin (Module.finrank Real E),
          chartRiemannTensor (I := I) g α c a b l (extChartAt I α x) *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x d l := by
    intro d
    have h := rm04_coord_eq (I := I) g α ![a, b, c, d] hx
    simpa only [Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_eq] using h
  have hGram : ∀ l : Fin (Module.finrank Real E),
      (∑ d : Fin (Module.finrank Real E),
          chartInvGramMatrix (I := I) g α x m d *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x d l) =
        if l = m then 1 else 0 := by
    intro l
    have hmul := congrFun (congrFun
      (chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hbase) m) l
    rw [Matrix.mul_apply, Matrix.one_apply] at hmul
    simpa only [eq_comm] using hmul
  calc chartRiemannTensor (I := I) g α c a b m (extChartAt I α x)
      = ∑ l : Fin (Module.finrank Real E),
          chartRiemannTensor (I := I) g α c a b l (extChartAt I α x) *
            (if l = m then 1 else 0) := by
        rw [Finset.sum_eq_single m]
        · simp
        · intro l _ hl
          simp only [hl, if_false, mul_zero]
        · intro hm
          exact absurd (Finset.mem_univ m) hm
    _ = ∑ l : Fin (Module.finrank Real E),
          chartRiemannTensor (I := I) g α c a b l (extChartAt I α x) *
            (∑ d : Fin (Module.finrank Real E),
              chartInvGramMatrix (I := I) g α x m d *
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x d l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hGram l]
    _ = ∑ l : Fin (Module.finrank Real E),
          ∑ d : Fin (Module.finrank Real E),
            chartRiemannTensor (I := I) g α c a b l (extChartAt I α x) *
              (chartInvGramMatrix (I := I) g α x m d *
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x d l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ d : Fin (Module.finrank Real E),
          ∑ l : Fin (Module.finrank Real E),
            chartRiemannTensor (I := I) g α c a b l (extChartAt I α x) *
              (chartInvGramMatrix (I := I) g α x m d *
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x d l) :=
        Finset.sum_comm
    _ = ∑ d : Fin (Module.finrank Real E),
          chartInvGramMatrix (I := I) g α x m d *
            (∑ l : Fin (Module.finrank Real E),
              chartRiemannTensor (I := I) g α c a b l (extChartAt I α x) *
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x d l) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ d : Fin (Module.finrank Real E),
          chartInvGramMatrix (I := I) g α x m d *
            metricRm04At (I := I) g x
              (fun k : Fin 4 =>
                DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α
                  (![a, b, c, d] k) x) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hterm d]

end Curvature
end Geometry

namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat -> Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
private theorem chartBasisVecFiber_subtype_contMDiffAt
    (hsrc : SourceIsSigmaCompact Φ)
    (k : Nat) (x₀ : P.M) (a : Fin (Module.finrank Real E)) {x : P.M}
    (hxb : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      x ∈ chartLeviCivitaGoodSet (I := I) x₀)
    (hxU : letI : TopologicalSpace P.M := P.topology; x ∈ Φ.source k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k (hsrc k)
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun z : SourceDomain (I := I) Φ k =>
        TotalSpace.mk' E
          (E := fun z : SourceDomain (I := I) Φ k => TangentSpace I z) z
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ a (z : P.M)))
      ⟨x, hxU⟩ := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  have hxb' : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hxb
  have hf' :
      (mfderiv I I
        (Subtype.val : SourceDomain (I := I) Φ k -> P.M) ⟨x, hxU⟩).IsInvertible := by
    have hmf :
        mfderiv I I
            (Subtype.val : SourceDomain (I := I) Φ k -> P.M) ⟨x, hxU⟩ =
          ContinuousLinearMap.id Real E := by
      simpa only using
        mfderiv_subtype_val (I := I) (sourceOpen (I := I) Φ k) ⟨x, hxU⟩
    rw [hmf]
    change (ContinuousLinearMap.id Real E).IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
      (f := ContinuousLinearEquiv.refl Real E)
  have hpull :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% (VectorField.mpullback I I
          (Subtype.val : SourceDomain (I := I) Φ k -> P.M)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ a)))
        (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) :=
    ContMDiffAt.mpullback_vectorField_preimage
      (I := I) (I' := I)
      (f := (Subtype.val : SourceDomain (I := I) Φ k -> P.M))
      (V := DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ a)
      (x₀ := ⟨x, hxU⟩) (m := ∞) (n := ∞)
      ((DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn
          (I := I) x₀ a).contMDiffAt
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hxb'))
      (contMDiff_subtype_val (I := I)
        (U := sourceOpen (I := I) Φ k)).contMDiffAt
      hf' (by simp)
  refine hpull.congr_of_eventuallyEq ?_
  filter_upwards with z
  change TotalSpace.mk' E
      (E := fun z : SourceDomain (I := I) Φ k => TangentSpace I z) z _ =
    TotalSpace.mk' E
      (E := fun z : SourceDomain (I := I) Φ k => TangentSpace I z) z _
  congr 1
  have hfz :
      (mfderiv I I
        (Subtype.val : SourceDomain (I := I) Φ k -> P.M) z).IsInvertible := by
    have hmf :
        mfderiv I I
            (Subtype.val : SourceDomain (I := I) Φ k -> P.M) z =
          ContinuousLinearMap.id Real E := by
      simpa only using
        mfderiv_subtype_val (I := I) (sourceOpen (I := I) Φ k) z
    rw [hmf]
    change (ContinuousLinearMap.id Real E).IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
      (f := ContinuousLinearEquiv.refl Real E)
  rw [VectorField.mpullback_apply]
  refine ((ContinuousLinearMap.IsInvertible.inverse_apply_eq hfz).mpr ?_).symm
  simpa only using
    (mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Φ k) z
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ a
        (z : P.M))).symm

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem gSeqExt_rm04At
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : Nat) (t : Real) (x : P.M)
    (hx : letI : TopologicalSpace P.M := P.topology; x ∈ bf.grow k)
    (slots : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      Fin 4 -> TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k (hsrc k)
    metricRm04At (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x slots =
      metricRm04At (I := I) (sourceMetric (I := I) Φ hsrc htgt k t)
        ⟨x, bf.grow_subset k hx⟩ slots := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one k
  let O : TopologicalSpace.Opens (SourceDomain (I := I) Φ k) :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩
  let : ChartedSpace H ↥O :=
    TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := SourceDomain (I := I) Φ k) (s := O)
  let : IsManifold I ∞ ↥O := { O.instHasGroupoid (contDiffGroupoid ∞ I) with }
  let : SigmaCompactSpace ↥O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I O.isOpen)
  let : T2Space ↥O := inferInstance
  let : IsManifold I 1 ↥O :=
    IsManifold.of_le (I := I) (M := ↥O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 ↥O :=
    IsManifold.of_le (I := I) (M := ↥O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥O := by
    change IsManifold I ∞ ↥O
    infer_instance
  let xsrc : SourceDomain (I := I) Φ k := ⟨x, bf.grow_subset k hx⟩
  let slotsSrc : Fin 4 -> TangentSpace I xsrc := fun q => show E from slots q
  have hxO : xsrc ∈ O := hgrowW hx
  have hres :
      (sourceMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O =
        (sourceMetricRestriction (I := I) Φ (k := k)
          (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O := by
    apply smoothRiemannianMetric_eq_of_inner (I := I)
    funext y
    ext a b
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (sourceMetricRestriction (I := I) Φ (k := k)
        (gSeqExt (I := I) Φ R bf hsrc htgt k t)).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b)
    rw [resSource_inner (I := I) Φ k]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner
        (((y : SourceDomain (I := I) Φ k) : P.M))
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t
      ((y : SourceDomain (I := I) Φ k) : P.M)
      (y : SourceDomain (I := I) Φ k).2
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)]
    rw [hW1 _ y.2]
    simp
  have hrmSource :
      metricRm04 (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc slotsSrc =
        metricRm04 (I := I)
          (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t))
          xsrc slotsSrc := by
    let xO : O := ⟨xsrc, hxO⟩
    let slotsO : Fin 4 -> TangentSpace I xO := fun q => show E from slotsSrc q
    have hderivO :
        (fun q : Fin 4 =>
            mfderiv I I (Subtype.val : O -> SourceDomain (I := I) Φ k) xO (slotsO q)) =
          slotsSrc := by
      funext q
      rw [mfderiv_subtype_val_apply]
    calc metricRm04 (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc slotsSrc
        = metricRm04 (I := I)
            ((sourceMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O)
            xO slotsO := by
          rw [metricRm04_restrictOpen_eval (I := I) (sourceMetric (I := I) Φ hsrc htgt k t)
            O xO slotsO, hderivO]
      _ = metricRm04 (I := I)
            ((sourceMetricRestriction (I := I) Φ (k := k)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O)
            xO slotsO := by
          rw [hres]
      _ = metricRm04 (I := I)
            (sourceMetricRestriction (I := I) Φ (k := k)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t)) xsrc slotsSrc := by
          rw [metricRm04_restrictOpen_eval (I := I)
            (sourceMetricRestriction (I := I) Φ (k := k)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t)) O xO slotsO, hderivO]
  have hrmAmbient :
      metricRm04 (I := I)
          (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t))
          xsrc slotsSrc =
        metricRm04 (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x slots := by
    have h := metricRm04_restrictOpen_eval (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t)
      (sourceOpen (I := I) Φ k) xsrc slotsSrc
    simp only [mfderiv_subtype_val_apply] at h
    exact h
  rw [← metricRm04_apply (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x,
    ← metricRm04_apply (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc]
  exact hrmAmbient.symm.trans hrmSource.symm

omit [NeZero (Module.finrank Real E)] in
theorem gSeqExt_chartRicci_contOn
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ) (k : Nat) (x₀ : P.M)
    (i j : Fin (Module.finrank Real E)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn
      (fun p : Real × P.M =>
        chartRicciTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j
          (extChartAt I x₀ p.2))
      (X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  let S : Set (Real × P.M) :=
    X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)
  rw [continuousOn_iff_continuous_domRestrict]
  let b : ↥S -> SourceDomain (I := I) Φ k := fun q => ⟨q.1.2, bf.grow_subset k q.2.2.2⟩
  have hb : Continuous b :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hτ : Continuous (fun q : ↥S => q.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hτK : ∀ q : ↥S, q.1.1 ∈ X.D.carrier := fun q => q.2.1
  let v : Fin 2 -> (q : ↥S) -> TangentSpace I (b q) :=
    fun a q =>
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
        (if a = 0 then i else j) q.1.2
  have hv : ∀ a : Fin 2, Continuous (fun q : ↥S =>
      TotalSpace.mk' E
        (E := fun z : SourceDomain (I := I) Φ k => TangentSpace I z) (b q) (v a q)) := by
    intro a
    rw [continuous_iff_continuousAt]
    intro q
    have ha :=
      (chartBasisVecFiber_subtype_contMDiffAt (I := I) Φ hsrc k x₀
        (if a = 0 then i else j) q.2.2.1 (bf.grow_subset k q.2.2.2)).continuousAt
    exact ContinuousAt.comp
      (g := fun z : SourceDomain (I := I) Φ k =>
        TotalSpace.mk' E
          (E := fun z : SourceDomain (I := I) Φ k => TangentSpace I z) z
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
            (if a = 0 then i else j) (z : P.M)))
      ha hb.continuousAt
  have hS := isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k)
  have heval :=
    hS.ricciCont.eval_continuous
      (P := ↥S) (τ := fun q => q.1.1) (b := b) hτ hτK hb hv
  refine heval.congr (fun q => ?_)
  have hvec : (fun a : Fin 2 => v a q) =
      vec2
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i q.1.2)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j q.1.2) := by
    funext a
    fin_cases a <;> rfl
  have hricciMetric :
      (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).ricci q.1.1 (b q) =
        metricRicciAt (I := I) (sourceMetric (I := I) Φ hsrc htgt k q.1.1) (b q) := by
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt,
      sourceMetric, SolutionOn.family_metric]
  calc (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).ricci q.1.1 (b q)
        (fun a : Fin 2 => v a q)
      = (metricRicciAt (I := I) (sourceMetric (I := I) Φ hsrc htgt k q.1.1) (b q))
          (fun a : Fin 2 => v a q) := by simp only [hricciMetric]
    _ = metricRicciAt (I := I) (sourceMetric (I := I) Φ hsrc htgt k q.1.1) (b q)
          (vec2
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i q.1.2)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j q.1.2)) := by
          rw [hvec]
          rfl
    _ = ricciTensor (I := I) (sourceMetric (I := I) Φ hsrc htgt k q.1.1) (b q)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i q.1.2)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j q.1.2) :=
          metricRicciAt_apply_eq_ricciTensor (I := I) _ _ _ _
    _ = ricciTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k q.1.1) q.1.2
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i q.1.2)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j q.1.2) :=
          (gSeqExt_ricci (I := I) Φ R bf hsrc htgt k q.1.1 q.1.2 q.2.2.2
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i q.1.2)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j q.1.2)).symm
    _ = chartRicciTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k q.1.1) x₀ i j
          (extChartAt I x₀ q.1.2) :=
          ricciTensor_chartBasisVec_alpha_eq (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt k q.1.1) x₀ i j q.2.2.1

omit [NeZero (Module.finrank Real E)] in
theorem gSeqExt_metricRm04At_contOn
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ) (k : Nat) (x₀ : P.M)
    (idx : Fin 4 -> Fin (Module.finrank Real E)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn
      (fun p : Real × P.M =>
        metricRm04At (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) p.2
          (fun a : Fin 4 =>
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
              (idx a) p.2))
      (X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  let S : Set (Real × P.M) :=
    X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)
  rw [continuousOn_iff_continuous_domRestrict]
  let b : ↥S -> SourceDomain (I := I) Φ k := fun q => ⟨q.1.2, bf.grow_subset k q.2.2.2⟩
  have hb : Continuous b :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hτ : Continuous (fun q : ↥S => q.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hτK : ∀ q : ↥S, q.1.1 ∈ X.D.carrier := fun q => q.2.1
  let v : Fin 4 -> (q : ↥S) -> TangentSpace I (b q) :=
    fun a q =>
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
        (idx a) q.1.2
  have hv : ∀ a : Fin 4, Continuous (fun q : ↥S =>
      TotalSpace.mk' E
        (E := fun z : SourceDomain (I := I) Φ k => TangentSpace I z) (b q) (v a q)) := by
    intro a
    rw [continuous_iff_continuousAt]
    intro q
    have ha :=
      (chartBasisVecFiber_subtype_contMDiffAt (I := I) Φ hsrc k x₀ (idx a)
        q.2.2.1 (bf.grow_subset k q.2.2.2)).continuousAt
    exact ContinuousAt.comp
      (g := fun z : SourceDomain (I := I) Φ k =>
        TotalSpace.mk' E
          (E := fun z : SourceDomain (I := I) Φ k => TangentSpace I z) z
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
            (idx a) (z : P.M)))
      ha hb.continuousAt
  have hS := isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k)
  have heval :=
    hS.rm04Cont.eval_continuous
      (P := ↥S) (τ := fun q => q.1.1) (b := b) hτ hτK hb hv
  refine heval.congr (fun q => ?_)
  have hrmMetric :
      (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).base.rm04 q.1.1 (b q) =
        metricRm04At (I := I) (sourceMetric (I := I) Φ hsrc htgt k q.1.1) (b q) := by
    simp only [SolutionFamily.rm04, SolutionOn.family_metric, sourceMetric, metricRm04_apply]
  calc (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).base.rm04 q.1.1 (b q)
        (fun a : Fin 4 => v a q)
      = (metricRm04At (I := I) (sourceMetric (I := I) Φ hsrc htgt k q.1.1) (b q))
          (fun a : Fin 4 => v a q) := by simp only [hrmMetric]
    _ = metricRm04At (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k q.1.1) q.1.2
          (fun a : Fin 4 => v a q) := by
          exact (gSeqExt_rm04At (I := I) Φ R bf hsrc htgt k q.1.1 q.1.2 q.2.2.2
            (fun a : Fin 4 => v a q)).symm
    _ = metricRm04At (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k q.1.1) q.1.2
          (fun a : Fin 4 =>
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
              (idx a) q.1.2) := by
          simp only [v]

omit [NeZero (Module.finrank Real E)] in
theorem gSeqExt_chartInvGramMatrix_contOn
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ) (k : Nat) (x₀ : P.M)
    (d m : Fin (Module.finrank Real E)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn
      (fun p : Real × P.M =>
        chartInvGramMatrix (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ p.2 d m)
      (X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let S : Set (Real × P.M) :=
    X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)
  let A : Real × P.M -> Matrix (Fin (Module.finrank Real E))
      (Fin (Module.finrank Real E)) Real :=
    fun p => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
      (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ p.2
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      ContinuousOn (fun p : Real × P.M => A p i j) S := by
    intro i j
    exact (gSeqExt_gram_cont (I := I) Φ R bf hsrc htgt k x₀ i j).mono
      (Set.prod_mono Subset.rfl
        (fun y hy => chartLeviCivitaGoodSet_mem_baseSet (I := I) hy.1))
  have hA : Continuous (fun q : ↥S => A q.1) :=
    continuous_matrix (fun i j =>
      continuousOn_iff_continuous_domRestrict.mp (hentry i j))
  have hdet : Continuous (fun q : ↥S => (A q.1).det) := hA.matrix_det
  have hdetne : ∀ q : ↥S, (A q.1).det ≠ 0 := by
    intro q
    exact ne_of_gt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I)
      (gSeqExt (I := I) Φ R bf hsrc htgt k q.1.1) x₀
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) q.2.2.1))
  have hinv : Continuous (fun q : ↥S => ((A q.1).det)⁻¹) := hdet.inv₀ hdetne
  have hadj : Continuous (fun q : ↥S => (A q.1).adjugate d m) :=
    (continuous_apply m).comp ((continuous_apply d).comp hA.matrix_adjugate)
  have hchart : Continuous (fun q : ↥S =>
      chartInvGramMatrix (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k q.1.1) x₀ q.1.2 d m) := by
    refine (hinv.mul hadj).congr (fun q => ?_)
    simp only [Pi.mul_apply, A, chartInvGramMatrix, Matrix.inv_def, Matrix.smul_apply,
      smul_eq_mul, Ring.inverse_eq_inv]
  exact continuousOn_iff_continuous_domRestrict.mpr hchart

omit [NeZero (Module.finrank Real E)] in
theorem gSeqExt_chartRiemann_contOn
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ) (k : Nat) (x₀ : P.M)
    (i j k' l : Fin (Module.finrank Real E)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn
      (fun p : Real × P.M =>
        chartRiemannTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j k' l
          (extChartAt I x₀ p.2))
      (X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let S : Set (Real × P.M) :=
    X.D.carrier ×ˢ (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow k)
  have hsum : ContinuousOn
      (fun p : Real × P.M =>
        ∑ d : Fin (Module.finrank Real E),
          chartInvGramMatrix (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ p.2 l d *
            metricRm04At (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) p.2
              (fun a : Fin 4 =>
                DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
                  (![j, k', i, d] a) p.2)) S := by
    refine continuousOn_finsetSum _ (fun d _ => ?_)
    exact (gSeqExt_chartInvGramMatrix_contOn (I := I) Φ R bf hsrc htgt k x₀ l d).mul
      (gSeqExt_metricRm04At_contOn (I := I) Φ R bf hsrc htgt k x₀ ![j, k', i, d])
  refine hsum.congr (fun p hp => ?_)
  exact chartRiemannTensor_eq_sum_metricRm04At_mul_chartInvGramMatrix (I := I)
    (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ j k' i l hp.2.1

omit [NeZero (Module.finrank Real E)] in
theorem FlowMetricConvergenceData.ricciCont_window_of_carrier
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.carrier)
    (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2 (Set.Icc β ψ)
      (fun t x => metricRicciAt (I := I) (co.gInf t) x) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  exact FlowMetricConvergenceData.ricciCont_window (I := I) Φ cLow hcLow hbound hcovTail co
    (fun k x₀ i j =>
      (gSeqExt_chartRicci_contOn (I := I) Φ R bf hsrc htgt (co.φ k) x₀ i j).mono
        (Set.prod_mono hwin Subset.rfl))

omit [NeZero (Module.finrank Real E)] in
theorem FlowMetricConvergenceData.rm04Cont_window_of_carrier
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.carrier)
    (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 4 (Set.Icc β ψ)
      (fun t x => metricRm04At (I := I) (co.gInf t) x) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  exact FlowMetricConvergenceData.rm04Cont_window (I := I) Φ hwin cLow hcLow hbound hcovTail co
    (fun k x₀ i j k' l =>
      (gSeqExt_chartRiemann_contOn (I := I) Φ R bf hsrc htgt (co.φ k) x₀ i j k' l).mono
        (Set.prod_mono hwin Subset.rfl))

end CheegerGromovCompactness
end DifferentialGeometry
