import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationBallMain_S29
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutAssembly_S24

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.Geometry
  DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **G2.** Supplies `level`, `two_le`, `hball`, `hcore` of `exists_late_cut_family_assembly_S24`
(shapes verbatim), plus the inner containment `closedBall(x, n/2) ⊆ int C(S_n)`, from the single
largeness hypothesis `N₀ ≤ n_j := (B.accuracy (slices j).time)⁻¹` for `j ≥ ⌈B.start⌉₊`
(`B.buffer_domain`, accuracy `= 1/n`, is consumed by S19's `ofBuffered_S19`, not here). -/
theorem lateCutBallInputs_S29 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (slices : ℕ → RegularSlice F.observation) :
    ∃ (N₀ : ℝ) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j),
      (∀ j, ⌈B.start⌉₊ ≤ j → N₀ ≤ (B.accuracy (slices j).time)⁻¹) →
      (∀ j, ⌈B.start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
        p.2.val 0 ≤ level j + 200 →
          (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
            (2 * (B.accuracy (slices j).time)⁻¹)) ∧
      (∀ j, ⌈B.start⌉₊ ≤ j → ∀ i : Fin B.count,
        Set.range (trunc_S24 B base level two_le j i).inclusion ⊆
          riemannianBallOf (B.model i).metric (B.model i).basepoint
            (B.accuracy (slices j).time)⁻¹) ∧
      (∀ j, ⌈B.start⌉₊ ≤ j → ∀ i : Fin B.count,
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
  refine ⟨4 * As + 404, level, two_le, fun hlarge => ?_⟩
  have key : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i : Fin B.count,
      (riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
          ((B.accuracy (slices j).time)⁻¹ / 2) ⊆
        interior (Set.range (trunc_S24 B base level two_le j i).inclusion)) ∧
      (Set.range (trunc_S24 B base level two_le j i).inclusion ⊆
        riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
          ((B.accuracy (slices j).time)⁻¹ - 1)) ∧
      (∀ (q : Fin (base i).count) (p : CuspHalfSpace), p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
          ((B.accuracy (slices j).time)⁻¹ - 1)) := by
    intro j hj i
    have hn := hlarge j hj
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
  refine ⟨fun j hj i q p hp => ?_, fun j hj i => ?_, fun j hj i => (key j hj i).1⟩
  · have hn := hlarge j hj
    have hm := (key j hj i).2.2 q p hp
    change riemannianEDistOf _ _ _ < _
    refine lt_of_le_of_lt hm ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith [hAs0])]
    linarith
  · have hn := hlarge j hj
    intro p hp
    have hm := (key j hj i).2.1 hp
    change riemannianEDistOf _ _ _ < _
    refine lt_of_le_of_lt hm ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith [hAs0])]
    linarith


/-- Largeness of `n_t = accuracy(t)⁻¹` for late times (from `accuracy_decay`). -/
theorem accuracy_inv_large_S29 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K) (N : ℝ) :
    ∃ T₀ : ℝ, B.start ≤ T₀ ∧ ∀ t, T₀ ≤ t → N ≤ (B.accuracy t)⁻¹ := by
  obtain ⟨T, hT⟩ := B.accuracy_decay (1 / (max N 1)) (by positivity)
  refine ⟨max B.start T, le_max_left _ _, fun t ht => ?_⟩
  have h1 := hT t ((le_max_right _ _).trans ht)
  have hp := B.accuracy_pos t ((le_max_left _ _).trans ht)
  have hm : 0 < max N 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have : max N 1 < (B.accuracy t)⁻¹ := by
    rw [lt_inv_comm₀ hm hp]
    simpa [one_div] using h1
  exact (le_max_left _ _).trans this.le

end GC.LongTime.Ch12
