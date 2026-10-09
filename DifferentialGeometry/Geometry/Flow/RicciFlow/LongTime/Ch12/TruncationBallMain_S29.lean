import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationBallGeom_S29

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.Geometry
  DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

/-- Uniform distance constant: core and all cusp points are within `A + height` of `x`, and `x`
lies below height `A` in every cusp. -/
theorem exists_distance_constant_S29 (x : H.Carrier) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ i, x ∉ T.cuspMap i '' {q : CuspHalfSpace | A < q.2.val 0}) ∧
      (∀ p ∈ range T.inclusion, riemannianEDistOf H.metric x p ≤ ENNReal.ofReal A) ∧
      (∀ i q, riemannianEDistOf H.metric x (T.cuspMap i q) ≤ ENNReal.ofReal (A + q.2.val 0)) := by
  obtain ⟨a0, ha0, hx0⟩ := exists_basepoint_height_S29 T x
  obtain ⟨Dc, hDc⟩ := exists_edist_core_le_S26 T x
  choose Di hDi0 hDi using fun i => exists_edist_cusp_le_S26 T x i
  set A : ℝ := max 0 (max a0 (max Dc (∑ i, Di i))) with hA
  have hA0 : 0 ≤ A := le_max_left _ _
  have hAa : a0 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hADc : Dc ≤ A := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hADi : ∀ i, Di i ≤ A := fun i =>
    (Finset.single_le_sum (fun j _ => hDi0 j) (Finset.mem_univ i)).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right le_rfl)))
  refine ⟨A, hA0, fun i ⟨q, hq, hqx⟩ => hx0 i ⟨q, lt_of_le_of_lt hAa hq, hqx⟩, fun p hp => ?_,
    fun i q => ?_⟩
  · exact (hDc p hp).trans (ENNReal.ofReal_le_ofReal hADc)
  · exact (hDi i q).trans (ENNReal.ofReal_le_ofReal (by linarith [hADi i]))

/-- The distance-constant facts are monotone in `A`. -/
theorem distance_constant_mono_S29 (x : H.Carrier) {A A' : ℝ} (hle : A ≤ A')
    (hxA : ∀ i, x ∉ T.cuspMap i '' {q : CuspHalfSpace | A < q.2.val 0})
    (hcore : ∀ p ∈ range T.inclusion, riemannianEDistOf H.metric x p ≤ ENNReal.ofReal A)
    (hcusp : ∀ i q, riemannianEDistOf H.metric x (T.cuspMap i q) ≤ ENNReal.ofReal (A + q.2.val 0)) :
    (∀ i, x ∉ T.cuspMap i '' {q : CuspHalfSpace | A' < q.2.val 0}) ∧
      (∀ p ∈ range T.inclusion, riemannianEDistOf H.metric x p ≤ ENNReal.ofReal A') ∧
      (∀ i q, riemannianEDistOf H.metric x (T.cuspMap i q) ≤ ENNReal.ofReal (A' + q.2.val 0)) :=
  ⟨fun i ⟨q, hq, e⟩ => hxA i ⟨q, lt_of_le_of_lt hle hq, e⟩,
    fun p hp => (hcore p hp).trans (ENNReal.ofReal_le_ofReal hle),
    fun i q => (hcusp i q).trans (ENNReal.ofReal_le_ofReal (by linarith))⟩

/-- **G1 (level form).** For any level `S ≥ 2` with `n/2 + A + 1 ≤ S` and `S + A + 201 ≤ n`:
`closedBall (x, n/2) ⊆ int C(S)`, `C(S) ⊆ closedBall (x, n-1)`, and the base cusp up to height
`S + 200` (the depth-200 collar of the level-`S` truncation) lies in `closedBall (x, n-1)`. -/
theorem truncation_ball_sandwich_level_S29 (x : H.Carrier) {A : ℝ} (hA0 : 0 ≤ A)
    (hxA : ∀ i, x ∉ T.cuspMap i '' {q : CuspHalfSpace | A < q.2.val 0})
    (hcore : ∀ p ∈ range T.inclusion, riemannianEDistOf H.metric x p ≤ ENNReal.ofReal A)
    (hcusp : ∀ i q, riemannianEDistOf H.metric x (T.cuspMap i q) ≤ ENNReal.ofReal (A + q.2.val 0))
    {n S : ℝ} (hS : 2 ≤ S) (hlo : n / 2 + A + 1 ≤ S) (hhi : S + A + 201 ≤ n) :
    riemannianClosedBallOf H.metric x (n / 2) ⊆
        interior (range (truncationAtLevel_C1 T hS).inclusion) ∧
      range (truncationAtLevel_C1 T hS).inclusion ⊆ riemannianClosedBallOf H.metric x (n - 1) ∧
      (∀ i (q : CuspHalfSpace), q.2.val 0 ≤ S + 200 →
        T.cuspMap i q ∈ riemannianClosedBallOf H.metric x (n - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine fun y hy => ?_
    have hopen := isOpen_riemannianBallOf H.metric x (n / 2 + 1)
    have hsub : riemannianBallOf H.metric x (n / 2 + 1) ⊆
        range (truncationAtLevel_C1 T hS).inclusion := by
      intro y hy'
      rw [truncationAtLevel_core_image_C1 T hS]
      rcases (T.exhausts ▸ mem_univ y : y ∈ range T.inclusion ∪ ⋃ i, range (T.cuspMap i)) with h | h
      · exact Or.inl h
      · obtain ⟨i, q, rfl⟩ := mem_iUnion.mp h
        by_cases hq : q.2.val 0 ≤ S
        · exact Or.inr (mem_iUnion.mpr ⟨i, q, ⟨mem_univ _, hq⟩, rfl⟩)
        · exfalso
          have hq' : S < q.2.val 0 := not_le.mp hq
          have hAq : A < q.2.val 0 := by linarith
          have h1 := ofReal_height_sub_le_edist_S26 T i q hA0 hAq (y := x) (hxA i)
          have h2 : riemannianEDistOf H.metric x (T.cuspMap i q) < ENNReal.ofReal (n / 2 + 1) := hy'
          rw [riemannianEDistOf_comm] at h1
          have h3 := lt_of_le_of_lt h1 h2
          rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)] at h3
          linarith
    refine interior_maximal hsub hopen ?_
    change riemannianEDistOf H.metric x y < ENNReal.ofReal (n / 2 + 1)
    exact lt_of_le_of_lt hy (by rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]; linarith)
  · intro p hp
    rw [truncationAtLevel_core_image_C1 T hS] at hp
    change riemannianEDistOf H.metric x p ≤ ENNReal.ofReal (n - 1)
    rcases hp with h | h
    · obtain ⟨y, rfl⟩ := h
      exact (hcore _ (mem_range_self y)).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · obtain ⟨i, q, ⟨-, hq⟩, rfl⟩ := mem_iUnion.mp h
      refine (hcusp i q).trans (ENNReal.ofReal_le_ofReal ?_)
      change q.2.val 0 ≤ S at hq
      linarith
  · intro i q hq
    change riemannianEDistOf H.metric x (T.cuspMap i q) ≤ ENNReal.ofReal (n - 1)
    exact (hcusp i q).trans (ENNReal.ofReal_le_ofReal (by linarith))

/-- **G1.** Explicit choice `S_n = n/2 + A + 1` for `n ≥ 4A + 404`. -/
theorem truncation_ball_sandwich_S29 (x : H.Carrier) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℝ, 4 * A + 404 ≤ n → ∃ hS : 2 ≤ levelOf_S29 A n,
      riemannianClosedBallOf H.metric x (n / 2) ⊆
        interior (range (truncationAtLevel_C1 T hS).inclusion) ∧
      range (truncationAtLevel_C1 T hS).inclusion ⊆ riemannianClosedBallOf H.metric x (n - 1) ∧
      (∀ i (q : CuspHalfSpace), q.2.val 0 ≤ levelOf_S29 A n + 200 →
        T.cuspMap i q ∈ riemannianClosedBallOf H.metric x (n - 1)) := by
  obtain ⟨A, hA0, hxA, hcore, hcusp⟩ := exists_distance_constant_S29 T x
  refine ⟨A, hA0, fun n hn => ?_⟩
  have hS : 2 ≤ levelOf_S29 A n := by unfold levelOf_S29; linarith
  exact ⟨hS, truncation_ball_sandwich_level_S29 T x hA0 hxA hcore hcusp hS
    (by unfold levelOf_S29; linarith) (by unfold levelOf_S29; linarith)⟩

end GC.LongTime.Ch12
