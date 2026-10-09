import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationBallInputs_S29
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedRestart_S30

set_option autoImplicit false

/-!
# CH12-S32 (G3): restarting buffered cores at a late time, and the S24 ball inputs for the restart

Finishes CH12-S30.  `lateCutBallInputs_S29` returns its largeness threshold `N₀` existentially for
the cores it is applied to, while the restart time `T` has to be chosen after `N₀`.  Since the
restart `B.restart_S30 T hT` has the same models, accuracy and base truncations as `B`, and the
S29 proof is pointwise in `j`, we re-derive the S29 statement with the threshold exposed and
quantified pointwise (`lateCutBallInputs_pointwise_S32`: the same proof as S29, `N₀ = 4·ΣA + 404`
depends only on `base` and the models), then choose `T` with `accuracy_inv_large_S29`.

`exists_restart_ball_inputs_S32` produces `T`, `level`, `two_le`, `hball`, `hcore` (and the inner
containment) in exactly the shapes `exists_late_cut_family_assembly_S24` wants for
`B' := B.restart_S30 T hT`, whose `start` is `T` by `rfl`.
-/

noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.Geometry
  DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- The S29 ball inputs with the threshold `N₀` exposed and the largeness hypothesis pointwise in
`j` (no reference to `B.start`). -/
theorem lateCutBallInputs_pointwise_S32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {B : BufferedPersistentCores F K}
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (slices : ℕ → RegularSlice F.observation) :
    ∃ (N₀ : ℝ) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j), ∀ j,
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
  refine ⟨4 * As + 404, level, two_le, fun j hn => ?_⟩
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

/-- **S30 → S29 → S24.**  A restart time `T ≥ B.start` and truncation levels such that, for
`B' := B.restart_S30 T hT` (so `B'.start = T` by `rfl`, and `B'` has the models, accuracy and base
truncations of `B`), the data `level`, `two_le`, `hball`, `hcore` of
`exists_late_cut_family_assembly_S24` hold with `B := B'` (shapes verbatim), together with the inner
containment `closedBall(x, n/2) ⊆ int C(S_n)` of `lateCutBallInputs_S29`. -/
theorem exists_restart_ball_inputs_S32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time) :
    ∃ (T : ℝ) (hT : B.start ≤ T) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j),
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
  obtain ⟨N₀, level, two_le, hpt⟩ := lateCutBallInputs_pointwise_S32 base slices
  obtain ⟨T, hT, hlarge⟩ := accuracy_inv_large_S29 B N₀
  have hlate : ∀ j : ℕ, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j →
      N₀ ≤ (B.accuracy (slices j).time)⁻¹ := fun j hj =>
    hlarge _ (((Nat.le_ceil T).trans (by exact_mod_cast hj)).trans (htimes j).le)
  refine ⟨T, hT, level, two_le, fun j hj => (hpt j (hlate j hj)).1,
    fun j hj => (hpt j (hlate j hj)).2.1, fun j hj => (hpt j (hlate j hj)).2.2⟩

end GC.LongTime.Ch12
