import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceRestriction_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

variable (H : ObservedHistory.{u}) (cut : Icc (0 : ℝ) H.horizon)

/-- Prefix lifting reflects the incoming-terminal bounds as well as the
ordinary-time bounds. -/
theorem traceAtOfRestriction_bounded_iff_CX2
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace (H.restrict cut) ((H.restrict cut).activeStage a)
      ((H.restrict cut).activeStage t) ((H.restrict cut).activeStage_mono hat) x) {K : ℝ} :
    (traceAtOfRestriction_CX2 H cut (hat := hat) A).isRmBoundedBy
      (hat := show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat) K ↔
        A.isRmBoundedBy (hat := hat) K := by
  refine ⟨?_, traceAtOfRestriction_bounded_CX2 H cut A⟩
  intro hA
  constructor
  · intro v hav hvt
    have hp := traceAtOfRestriction_point_heq_CX2 H cut (hat := hat) A v hav hvt
    have heq := rmNormSq_heq_CX2 (H.restrict_stageAt cut v)
      (H.restrict_sliceMetric cut v) hp.symm
    exact heq.trans_le (hA.1 (restrictTime_CX2 H cut v) hav hvt)
  · intro i hf hl
    let i' : Fin H.eventCount := Fin.castLE (Nat.le_of_lt_succ (H.activeStage cut).isLt) i
    have hf' : H.activeStage (restrictTime_CX2 H cut a) ≤ i'.castSucc := by
      rw [← restrict_active_CX2]
      exact hf
    have hl' : i'.succ ≤ H.activeStage (restrictTime_CX2 H cut t) := by
      rw [← restrict_active_CX2]
      exact hl
    have hp := traceReindex_point_CX2 H
      (hle' := H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrict_active_CX2 H cut a) (restrict_active_CX2 H cut t)
      (restrictPoint_heq_CX2 H cut t x).symm (traceOfRestriction_CX2 H cut A)
      i'.castSucc hf (i.castSucc_lt_succ.le.trans hl) hf' (i'.castSucc_lt_succ.le.trans hl')
    change (traceAtOfRestriction_CX2 H cut (hat := hat) A).point i'.castSucc hf'
      (i'.castSucc_lt_succ.le.trans hl') = A.point i.castSucc hf
      (i.castSucc_lt_succ.le.trans hl) at hp
    exact (terminalRmNormSq_congr_CX2 H i' _ _ hp.symm).trans_le (hA.2 i' hf' hl')

/-- The inverse transport for a trace at two prefix observation times. -/
def traceAtToRestriction_CX2
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage (restrictTime_CX2 H cut a))
      (H.activeStage (restrictTime_CX2 H cut t))
      (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrictPoint_CX2 H cut t x)) :
    BackwardPointTrace (H.restrict cut) ((H.restrict cut).activeStage a)
      ((H.restrict cut).activeStage t) ((H.restrict cut).activeStage_mono hat) x :=
  traceToRestriction_CX2 H cut (traceReindex_CX2 H (restrict_active_CX2 H cut a).symm
    (restrict_active_CX2 H cut t).symm (restrictPoint_heq_CX2 H cut t x) A)

theorem traceAtToRestriction_bounded_CX2
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage (restrictTime_CX2 H cut a))
      (H.activeStage (restrictTime_CX2 H cut t))
      (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrictPoint_CX2 H cut t x)) {K : ℝ}
    (hA : A.isRmBoundedBy
      (hat := show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat) K) :
    (traceAtToRestriction_CX2 H cut (hat := hat) A).isRmBoundedBy (hat := hat) K := by
  apply (traceAtOfRestriction_bounded_iff_CX2 H cut _).mp
  have h : traceAtOfRestriction_CX2 H cut (hat := hat)
      (traceAtToRestriction_CX2 H cut (hat := hat) A) = A := Subsingleton.elim _ _
  rw [h]
  exact hA

/-- The carrier identification is onto, so ball quantifiers transport in both directions. -/
theorem restrictPoint_surjective_CX2 (t : Icc (0 : ℝ) (H.restrict cut).horizon) :
    Function.Surjective (restrictPoint_CX2 H cut t) := by
  intro x
  refine ⟨cast (congrArg OrientedThreeStage.Carrier (H.restrict_stageAt cut t)).symm x, ?_⟩
  exact eq_of_heq ((restrictPoint_heq_CX2 H cut t _).trans (cast_heq _ _))

theorem metricBall_heq_CX2 {P Q : OrientedThreeStage.{u}} {g : P.Metric} {h : Q.Metric}
    (hPQ : P = Q) (hgh : HEq g h) {p x : P.Carrier} {q y : Q.Carrier}
    (hpq : HEq p q) (hxy : HEq x y) (r : ℝ) :
    x ∈ riemannianBallOf g p r ↔ y ∈ riemannianBallOf h q r := by
  subst Q
  cases hgh
  cases hpq
  cases hxy
  rfl

theorem ballVolume_heq_CX2 {P Q : OrientedThreeStage.{u}} {g : P.Metric} {h : Q.Metric}
    (hPQ : P = Q) (hgh : HEq g h) {p : P.Carrier} {q : Q.Carrier}
    (hpq : HEq p q) (r : ℝ) : ballVolume g p r = ballVolume h q r := by
  subst Q
  cases hgh
  cases hpq
  rfl

/-- Buffered traced regions are unchanged by restricting after their top time. -/
theorem isTracedRegion_restrict_iff_CX2
    (t : Icc (0 : ℝ) (H.restrict cut).horizon) (p : ((H.restrict cut).stageAt t).Carrier)
    (ρ τ K : ℝ) :
    (H.restrict cut).isTracedRegion t p ρ τ K ↔
      H.isTracedRegion (restrictTime_CX2 H cut t) (restrictPoint_CX2 H cut t p) ρ τ K := by
  constructor
  · rintro ⟨hρ, hτ, a, hat, ha, htrace⟩
    refine ⟨hρ, hτ, restrictTime_CX2 H cut a, hat, ha, ?_⟩
    intro x hx
    obtain ⟨x', rfl⟩ := restrictPoint_surjective_CX2 H cut t x
    have hx' := (metricBall_heq_CX2 (H.restrict_stageAt cut t) (H.restrict_sliceMetric cut t)
      (restrictPoint_heq_CX2 H cut t p).symm (restrictPoint_heq_CX2 H cut t x').symm ρ).mpr hx
    obtain ⟨A, hA⟩ := htrace x' hx'
    exact ⟨traceAtOfRestriction_CX2 H cut (hat := hat) A,
      traceAtOfRestriction_bounded_CX2 H cut A hA⟩
  · rintro ⟨hρ, hτ, a, hat, ha, htrace⟩
    let a' : Icc (0 : ℝ) (H.restrict cut).horizon :=
      ⟨a.val, a.property.1, (show a.val ≤ t.val from hat).trans t.property.2⟩
    have hat' : a' ≤ t := hat
    refine ⟨hρ, hτ, a', hat', ha, ?_⟩
    intro x hx
    have hx' := (metricBall_heq_CX2 (H.restrict_stageAt cut t) (H.restrict_sliceMetric cut t)
      (restrictPoint_heq_CX2 H cut t p).symm (restrictPoint_heq_CX2 H cut t x).symm ρ).mp hx
    obtain ⟨A, hA⟩ := htrace (restrictPoint_CX2 H cut t x) hx'
    exact ⟨traceAtToRestriction_CX2 H cut (a := a') (hat := hat') A,
      traceAtToRestriction_bounded_CX2 H cut (a := a') (t := t) (hat := hat') A hA⟩

end GC.LongTime.Ch12
