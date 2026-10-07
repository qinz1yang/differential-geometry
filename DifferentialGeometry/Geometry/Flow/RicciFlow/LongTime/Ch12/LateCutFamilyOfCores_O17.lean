import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateThinSide_O17
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedRestartWiring_S32

set_option autoImplicit false

/-!
# CH12-O17 (G2): A09 from buffered cores and base truncations

`exists_late_cut_family_of_cores_O17`: conclusion verbatim `exists_late_cut_family` (A09).  Inputs:
`B : BufferedPersistentCores F (K + 4)`, `base`, and the two analytic leaves of
`exists_late_cut_family_thin_O17` (nearly cuspidal boundary `hNCB`, ambient collapse `hAmbS`),
quantified over the restart data (restart time, levels with `n_j / 2 ≤ level j`, the S24 ball
inputs and the inner containment `closedBall(x_i, n_j/2) ⊆ int range`).  The restart is S32 G3;
`lateCutBallInputs_level_O17` is `lateCutBallInputs_pointwise_S32` (same proof) with the level
lower bound `n_j / 2 ≤ level j` exported.
-/

noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.Geometry
  DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Curvature GC.GraphManifold GC.Topology
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- `lateCutBallInputs_pointwise_S32` with the level lower bound `n_j / 2 ≤ level j` exported
(proof copied from S32). -/
theorem lateCutBallInputs_level_O17 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {B : BufferedPersistentCores F K}
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (slices : ℕ → RegularSlice F.observation) :
    ∃ (N₀ : ℝ) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j),
      (∀ j, (B.accuracy (slices j).time)⁻¹ / 2 ≤ level j) ∧ ∀ j,
      N₀ ≤ (B.accuracy (slices j).time)⁻¹ →
      (∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
        p.2.val 0 ≤ level j + 200 →
          (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
            (2 * (B.accuracy (slices j).time)⁻¹)) ∧
      (∀ i : Fin B.count,
        Set.range (trunc_S24 B base level two_le j i).inclusion ⊆
          riemannianBallOf (B.model i).metric (B.model i).basepoint
            (B.accuracy (slices j).time)⁻¹) ∧
      (∀ i : Fin B.count,
        riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
            ((B.accuracy (slices j).time)⁻¹ / 2) ⊆
          interior (Set.range (trunc_S24 B base level two_le j i).inclusion)) := by
  choose A hA0 hxA hcore hcusp using fun i : Fin B.count =>
    exists_distance_constant_S29 (base i) (B.model i).basepoint
  set As : ℝ := ∑ i, A i with hAs
  have hAs0 : 0 ≤ As := Finset.sum_nonneg fun i _ => hA0 i
  have hle : ∀ i, A i ≤ As := fun i =>
    Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ i)
  let level : ℕ → ℝ := fun j => max 2 (levelOf_S29 As (B.accuracy (slices j).time)⁻¹)
  have two_le : ∀ j, 2 ≤ level j := fun j => le_max_left _ _
  refine ⟨4 * As + 404, level, two_le, fun j => le_max_of_le_right (by unfold levelOf_S29; linarith),
    fun j hn => ?_⟩
  have key : ∀ i : Fin B.count,
      (riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
          ((B.accuracy (slices j).time)⁻¹ / 2) ⊆
        interior (Set.range (trunc_S24 B base level two_le j i).inclusion)) ∧
      (Set.range (trunc_S24 B base level two_le j i).inclusion ⊆
        riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
          ((B.accuracy (slices j).time)⁻¹ - 1)) ∧
      (∀ (q : Fin (base i).count) (p : CuspHalfSpace), p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
          ((B.accuracy (slices j).time)⁻¹ - 1)) := by
    intro i
    set n := (B.accuracy (slices j).time)⁻¹ with hnd
    have hlev : level j = levelOf_S29 As n := by
      refine max_eq_right ?_
      unfold levelOf_S29; linarith
    obtain ⟨h1, h2, h3⟩ := distance_constant_mono_S29 (base i) (B.model i).basepoint (hle i)
      (hxA i) (hcore i) (hcusp i)
    have := truncation_ball_sandwich_level_S29 (base i) (B.model i).basepoint hAs0 h1 h2 h3
      (n := n) (S := level j) (two_le j) (by rw [hlev]; unfold levelOf_S29; linarith)
      (by rw [hlev]; unfold levelOf_S29; linarith)
    exact ⟨this.1, this.2.1, fun q p hp => this.2.2 q p (by linarith [hp])⟩
  refine ⟨fun i q p hp => ?_, fun i => ?_, fun i => (key i).1⟩
  · have hm := (key i).2.2 q p hp
    change riemannianEDistOf _ _ _ < _
    refine lt_of_le_of_lt hm ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith [hAs0])]
    linarith
  · intro p hp
    have hm := (key i).2.1 hp
    change riemannianEDistOf _ _ _ < _
    refine lt_of_le_of_lt hm ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith [hAs0])]
    linarith

/-- **Restart (S32 G3) with the level lower bound.**  As `exists_restart_ball_inputs_S32`, plus
`n_j / 2 ≤ level j`. -/
theorem exists_restart_ball_inputs_O17 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time) :
    ∃ (T : ℝ) (hT : B.start ≤ T) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j),
      (∀ j, (B.accuracy (slices j).time)⁻¹ / 2 ≤ level j) ∧
      (∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
        p.2.val 0 ≤ level j + 200 →
          (base i).cuspMap q p ∈ riemannianBallOf ((B.restart_S30 T hT).model i).metric
            ((B.restart_S30 T hT).model i).basepoint
            (2 * ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹)) ∧
      (∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion ⊆
          riemannianBallOf ((B.restart_S30 T hT).model i).metric
            ((B.restart_S30 T hT).model i).basepoint
            ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹) ∧
      (∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        riemannianClosedBallOf ((B.restart_S30 T hT).model i).metric
            ((B.restart_S30 T hT).model i).basepoint
            (((B.restart_S30 T hT).accuracy (slices j).time)⁻¹ / 2) ⊆
          interior (Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion)) := by
  obtain ⟨N₀, level, two_le, hlev, hpt⟩ := lateCutBallInputs_level_O17 base slices
  obtain ⟨T, hT, hlarge⟩ := accuracy_inv_large_S29 B N₀
  have hlate : ∀ j : ℕ, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j →
      N₀ ≤ (B.accuracy (slices j).time)⁻¹ := fun j hj =>
    hlarge _ (((Nat.le_ceil T).trans (by exact_mod_cast hj)).trans (htimes j).le)
  exact ⟨T, hT, level, two_le, hlev, fun j hj => (hpt j (hlate j hj)).1,
    fun j hj => (hpt j (hlate j hj)).2.1, fun j hj => (hpt j (hlate j hj)).2.2⟩

/-- **A09 from cores (O17 G2).**  Conclusion verbatim `exists_late_cut_family`.  Inputs besides
the A09 binders: the buffered cores `B`, the base truncations `base`, and the two analytic leaves
(`hNCB`: S34 R3 / S39; `hAmbS`: slice form of `outerThin_ambient_v2_S35`, whose `hTrans` is
S40 / S41), each for every restart datum produced by `exists_restart_ball_inputs_O17`. -/
theorem exists_late_cut_family_of_cores_O17 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    -- proved as `collarNegativePlane_S16` / `exists_negative_plane_of_nearlyCuspidal_S27`; inline only
    -- because BoundaryWiringG2_S16 cannot be imported together with S29 (duplicate
    -- `CuspEmbedding.isOpen_image`)
    (hG2 : CollarNegativePlane.{u} K)
    (hNP : ∀ (W : CompactCarrier.{u}) (h : SmoothRiemannianMetric W.model W.Carrier),
      NearlyCuspidalBoundary W h (K + 4) (1 / 10000) → ∃ q, ¬ SectionalBoundedBelowAt h q (-(1 / 81 : ℝ)))
    (hNCB : ∀ (T : ℝ) (hT : B.start ≤ T) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j)
      (hball : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
        p.2.val 0 ≤ level j + 200 →
          (base i).cuspMap q p ∈ riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            (2 * ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹))
      (_hcore : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion ⊆
          riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹)
      ,
      (∀ j, (B.accuracy (slices j).time)⁻¹ / 2 ≤ level j) →
      (∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        riemannianClosedBallOf ((B.restart_S30 T hT).model i).metric
            ((B.restart_S30 T hT).model i).basepoint
            (((B.restart_S30 T hT).accuracy (slices j).time)⁻¹ / 2) ⊆
          interior (Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion)) →
      ∀ w : ℝ, 0 < w → ∃ N : ℕ, ∀ j (hj : ⌈(B.restart_S30 T hT).start⌉₊ ≤ j), N ≤ j →
      ∀ C (i : Fin (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin (B.restart_S30 T hT).count,
          Disjoint
            ((fun x => (((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                ((B.restart_S30 T hT).toCores.map c (slices j).time (ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj)
                  ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).inclusion x))) ''
              ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).core.interior : Set _))) →
        ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i).model.boundary
            ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i).Carrier ≠ ∅ →
        Nonempty (NearlyCuspidalBoundary
          ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i)
          (cutMetric_S25 ((slices j).componentMetric C)
            (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i) (K + 4) w))
    (hAmbS : ∀ (T : ℝ) (hT : B.start ≤ T) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j)
      (hball : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
        p.2.val 0 ≤ level j + 200 →
          (base i).cuspMap q p ∈ riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            (2 * ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹))
      (_hcore : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion ⊆
          riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹)
      ,
      (∀ j, (B.accuracy (slices j).time)⁻¹ / 2 ≤ level j) →
      (∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        riemannianClosedBallOf ((B.restart_S30 T hT).model i).metric
            ((B.restart_S30 T hT).model i).basepoint
            (((B.restart_S30 T hT).accuracy (slices j).time)⁻¹ / 2) ⊆
          interior (Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion)) →
      ∀ w : ℝ, 0 < w → ∃ N : ℕ, ∀ j (hj : ⌈(B.restart_S30 T hT).start⌉₊ ≤ j), N ≤ j →
      ∀ C (i : Fin (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin (B.restart_S30 T hT).count,
          Disjoint
            ((fun x => (((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                ((B.restart_S30 T hT).toCores.map c (slices j).time (ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj)
                  ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).inclusion x))) ''
              ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).core.interior : Set _))) →
        ∀ p : ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i)
              (cutMetric_S25 ((slices j).componentMetric C)
                (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i) p →
          volumeCollapsedAtCurvatureScale ((slices j).componentMetric C) w
            (cutPieceMap (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i p)) :
    Nonempty (LateCutFamily F K slices) := by
  obtain ⟨T, hT, level, two_le, hlev, hball, hcore, hinner⟩ :=
    exists_restart_ball_inputs_O17 B base slices htimes
  exact exists_late_cut_family_thin_O17 F K hK δ hadm hdec slices htimes hnonempty
    (B.restart_S30 T hT) base level two_le hball hcore hG2 hNP
    (hNCB T hT level two_le hball hcore hlev hinner)
    (hAmbS T hT level two_le hball hcore hlev hinner)

end GC.LongTime.Ch12
