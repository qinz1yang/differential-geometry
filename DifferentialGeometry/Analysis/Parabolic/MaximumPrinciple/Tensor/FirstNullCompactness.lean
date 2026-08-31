import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

structure TensorFirstNullCompactnessOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop where
  firstNull_of_failure :
    (∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x) ->
    (¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) ->
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)

namespace TensorFirstNullCompactnessOn

omit [IsManifold I 2 M] in
theorem of_section
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + delta))))
    (hunit_cont :
      Continuous
        (barrierUnitQuad (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 t0 (t0 + delta)))
    (hfixed_cont :
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))) :
    TensorFirstNullCompactnessOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 := by
  classical
  let Sraw : TwoTensorFamily (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) S
  have hSraw : Sraw = twoTensorSecToFamily (I := I) (M := M) S := rfl
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G Sraw epsilon delta t0
  let slab := MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + delta)
  let φ : slab -> Real :=
    barrierUnitQuad (I := I) (M := M) G Sraw epsilon delta t0 t0 (t0 + delta)
  let Z : Set slab := {p | φ p ≤ 0}
  refine ⟨?_⟩
  intro hinit_pos hfail
  have hZclosed : IsClosed Z := by
    have hclosed : IsClosed ((Set.Iic (0 : Real)) : Set Real) := isClosed_Iic
    change IsClosed (φ ⁻¹' Set.Iic 0)
    change IsClosed
      (barrierUnitQuad (I := I) (M := M) G Sraw epsilon delta t0 t0
        (t0 + delta) ⁻¹' Set.Iic 0)
    rw [hSraw]
    exact hclosed.preimage hunit_cont
  have hZcompact : IsCompact Z := by
    simpa [Z] using hcompact.inter_right hZclosed
  obtain ⟨pbad, hpbad_neg⟩ :=
    failure_unitSlab (I := I) (M := M) G S epsilon delta t0 t0
      (t0 + delta) hfail
  have hZne : Z.Nonempty := ⟨pbad, le_of_lt hpbad_neg⟩
  obtain ⟨p1, hp1Z, hmin⟩ :=
    hZcompact.exists_isMinOn hZne
      (metricUnitSlab_timeVal_cont (I := I) (M := M) G t0 (t0 + delta)).continuousOn
  let t1 : Real := p1.1.1
  let x1 : M := MetricUnitTangent.base (I := I) (M := M) p1.2
  let v1 : TangentSpace I x1 := MetricUnitTangent.vec (I := I) (M := M) p1.2
  have hp1_time : t1 ∈ Set.Icc t0 (t0 + delta) := by
    simp [t1]
  have hp1_nonpos : φ p1 ≤ 0 := hp1Z
  have hv1_ne : v1 ≠ 0 := by
    intro hv
    have hbad : (0 : Real) = 1 := by
      simpa [v1, hv] using
        (MetricUnitTangent.unit (I := I) (M := M) p1.2)
    norm_num at hbad
  have ht1_ne_t0 : t1 ≠ t0 := by
    intro ht1eq
    have hpos : 0 < φ p1 := by
      have hpos_raw := hinit_pos x1 v1 hv1_ne
      simpa [φ, barrierUnitQuad, Sraw, B, t1, x1, v1, ht1eq] using hpos_raw
    linarith
  have ht1_gt : t0 < t1 := lt_of_le_of_ne hp1_time.1 (Ne.symm ht1_ne_t0)
  have hnonneg_until :
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (B t) x := by
    intro t ht x v
    by_contra hnot
    have hneg : B t x v v < 0 := lt_of_not_ge hnot
    have ht_full : t ∈ Set.Icc t0 (t0 + delta) :=
      ⟨ht.1, le_trans ht.2 hp1_time.2⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0
          t0 (t0 + delta) t ht_full x v (by simpa [B, Sraw] using hneg)
      have hqZ : q ∈ Z := by
        change barrierUnitQuad (I := I) (M := M) G Sraw epsilon delta t0 t0
          (t0 + delta) q ≤ 0
        rw [hSraw]
        exact le_of_lt hqneg
      have hmin_q := hmin hqZ
      have hqtime : q.1.1 = t := hq_time
      have ht1_le_t : t1 ≤ t := by
        have ht1_le_q : (p1.1.1 : Real) ≤ q.1.1 := by
          exact (Subtype.coe_le_coe).2 hmin_q
        simpa [t1, hqtime] using ht1_le_q
      linarith
    · have hneg_t1 :
          B t1 x v v < 0 := by
        simpa [heq] using hneg
      obtain ⟨s, hs_full, hs_lt, hsneg⟩ :=
        exists_left_neg_of_continuousOn (a := t0) (b := t1)
          (c := t0 + delta) ht1_gt hp1_time.2
          (by simpa [B, Sraw] using hfixed_cont x v)
          hneg_t1
      obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0
          t0 (t0 + delta) s hs_full x v (by simpa [B, Sraw] using hsneg)
      have hqZ : q ∈ Z := by
        change barrierUnitQuad (I := I) (M := M) G Sraw epsilon delta t0 t0
          (t0 + delta) q ≤ 0
        rw [hSraw]
        exact le_of_lt hqneg
      have hmin_q := hmin hqZ
      have hqtime : q.1.1 = s := hq_time
      have ht1_le_s : t1 ≤ s := by
        have ht1_le_q : (p1.1.1 : Real) ≤ q.1.1 := by
          exact (Subtype.coe_le_coe).2 hmin_q
        simpa [t1, hqtime] using ht1_le_q
      linarith
  have hnonneg_p1 : 0 ≤ φ p1 := by
    have hquad :=
      hnonneg_until t1 ⟨le_of_lt ht1_gt, le_rfl⟩ x1 v1
    simpa [φ, barrierUnitQuad, B, Sraw, t1, x1, v1] using hquad
  have hnullφ : φ p1 = 0 := le_antisymm hp1_nonpos hnonneg_p1
  refine Nonempty.intro
    { t1 := t1
      x1 := x1
      v := v1
      t1_mem := ⟨ht1_gt, hp1_time.2⟩
      v_ne_zero := hv1_ne
      unit := by
        exact MetricUnitTangent.unit (I := I) (M := M) p1.2
      nonnegative_until := ?_
      null := ?_ }
  · intro t ht x
    simpa [B, Sraw] using hnonneg_until t ht x
  · simpa [φ, barrierUnitQuad, B, Sraw, t1, x1, v1] using hnullφ

end TensorFirstNullCompactnessOn

namespace TensorFirstNullCompactnessOn

omit [IsManifold I 2 M] in
theorem of_section_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta)))))
    (hunit_cont :
      Continuous
        (barrierTimeSlabQuad (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 (Set.Icc t0 (t0 + delta))))
    (hfixed_cont :
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))) :
    TensorFirstNullCompactnessOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 := by
  classical
  let Sraw : TwoTensorFamily (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) S
  have hSraw : Sraw = twoTensorSecToFamily (I := I) (M := M) S := rfl
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G Sraw epsilon delta t0
  let slab := MetricUnitTangentTimeSlab (I := I) (M := M) G
    (Set.Icc t0 (t0 + delta))
  let φ : slab -> Real :=
    barrierTimeSlabQuad (I := I) (M := M) G Sraw epsilon delta t0
      (Set.Icc t0 (t0 + delta))
  let Z : Set slab := {p | φ p ≤ 0}
  refine ⟨?_⟩
  intro hinit_pos hfail
  have hZclosed : IsClosed Z := by
    have hclosed : IsClosed ((Set.Iic (0 : Real)) : Set Real) := isClosed_Iic
    change IsClosed (φ ⁻¹' Set.Iic 0)
    change IsClosed
      (barrierTimeSlabQuad (I := I) (M := M) G Sraw epsilon delta t0
        (Set.Icc t0 (t0 + delta)) ⁻¹' Set.Iic 0)
    rw [hSraw]
    exact hclosed.preimage hunit_cont
  have hZcompact : IsCompact Z := by
    simpa [Z] using hcompact.inter_right hZclosed
  obtain ⟨pbad, hpbad_neg⟩ :=
    failure_timeSlab (I := I) (M := M) G S epsilon delta t0
      (K := Set.Icc t0 (t0 + delta)) hfail
  have hZne : Z.Nonempty := ⟨pbad, le_of_lt hpbad_neg⟩
  obtain ⟨p1, hp1Z, hmin⟩ :=
    hZcompact.exists_isMinOn hZne
      (metricUnitTimeSlab_timeVal_cont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))).continuousOn
  let t1 : Real := MetricUnitTangentTimeSlab.time (I := I) (M := M) p1
  let x1 : M := MetricUnitTangentTimeSlab.base (I := I) (M := M) p1
  let v1 : TangentSpace I x1 :=
    MetricUnitTangentTimeSlab.vec (I := I) (M := M) p1
  have hp1_time : t1 ∈ Set.Icc t0 (t0 + delta) := by
    simpa [t1] using
      (MetricUnitTangentTimeSlab.time_mem (I := I) (M := M) p1)
  have hp1_nonpos : φ p1 ≤ 0 := hp1Z
  have hv1_ne : v1 ≠ 0 := by
    intro hv
    have hbad : (0 : Real) = 1 := by
      simpa [v1, hv] using
        (MetricUnitTangentTimeSlab.unit (I := I) (M := M) p1)
    norm_num at hbad
  have ht1_ne_t0 : t1 ≠ t0 := by
    intro ht1eq
    have hpos : 0 < φ p1 := by
      have hpos_raw := hinit_pos x1 v1 hv1_ne
      simpa [φ, barrierTimeSlabQuad, Sraw, B, t1, x1, v1, ht1eq] using hpos_raw
    linarith
  have ht1_gt : t0 < t1 := lt_of_le_of_ne hp1_time.1 (Ne.symm ht1_ne_t0)
  have hnonneg_until :
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (B t) x := by
    intro t ht x v
    by_contra hnot
    have hneg : B t x v v < 0 := lt_of_not_ge hnot
    have ht_full : t ∈ Set.Icc t0 (t0 + delta) :=
      ⟨ht.1, le_trans ht.2 hp1_time.2⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 t
          (K := Set.Icc t0 (t0 + delta)) ht_full x v
          (by simpa [B, Sraw] using hneg)
      have hqZ : q ∈ Z := by
        change barrierTimeSlabQuad (I := I) (M := M) G Sraw epsilon delta t0
          (Set.Icc t0 (t0 + delta)) q ≤ 0
        rw [hSraw]
        exact le_of_lt hqneg
      have hmin_q := hmin hqZ
      have ht1_le_t : t1 ≤ t := by
        simpa [t1, hq_time] using hmin_q
      linarith
    · have hneg_t1 :
          B t1 x v v < 0 := by
        simpa [heq] using hneg
      obtain ⟨s, hs_full, hs_lt, hsneg⟩ :=
        exists_left_neg_of_continuousOn (a := t0) (b := t1)
          (c := t0 + delta) ht1_gt hp1_time.2
          (by simpa [B, Sraw] using hfixed_cont x v)
          hneg_t1
      obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 s
          (K := Set.Icc t0 (t0 + delta)) hs_full x v
          (by simpa [B, Sraw] using hsneg)
      have hqZ : q ∈ Z := by
        change barrierTimeSlabQuad (I := I) (M := M) G Sraw epsilon delta t0
          (Set.Icc t0 (t0 + delta)) q ≤ 0
        rw [hSraw]
        exact le_of_lt hqneg
      have hmin_q := hmin hqZ
      have ht1_le_s : t1 ≤ s := by
        simpa [t1, hq_time] using hmin_q
      linarith
  have hnonneg_p1 : 0 ≤ φ p1 := by
    have hquad :=
      hnonneg_until t1 ⟨le_of_lt ht1_gt, le_rfl⟩ x1 v1
    simpa [φ, barrierTimeSlabQuad, B, Sraw, t1, x1, v1] using hquad
  have hnullφ : φ p1 = 0 := le_antisymm hp1_nonpos hnonneg_p1
  refine Nonempty.intro
    { t1 := t1
      x1 := x1
      v := v1
      t1_mem := ⟨ht1_gt, hp1_time.2⟩
      v_ne_zero := hv1_ne
      unit := by
        exact MetricUnitTangentTimeSlab.unit (I := I) (M := M) p1
      nonnegative_until := ?_
      null := ?_ }
  · intro t ht x
    simpa [B, Sraw] using hnonneg_until t ht x
  · simpa [φ, barrierTimeSlabQuad, B, Sraw, t1, x1, v1] using hnullφ

end TensorFirstNullCompactnessOn


end

end DifferentialGeometry.PDE.RicciFlow
