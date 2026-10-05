import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1StandardFacts

/-!
# Chapter-14 assembly, item L1, group G3c: coincidences in a cycle normal form and the transfer map

For a cycle normal form `N` (`CycleNormalForm`), two pieces' parametrizations meet exactly as the
standard local forms say (`ball_eq_ball_iff`, `handle_eq_handle_iff`, `neck_eq_neck_iff`,
`ball_eq_neck_iff`, `handle_eq_neck_iff`, `ball_eq_handle_iff`); the right-hand sides involve only
the indices and the standard maps `capMap`, `handleEnd`, so they are the same for any two normal
forms with the same `len` and `ε`. Hence the transfer `transfer N₀ N : U₀ → X`, sending a point
described by a model piece to the same description in `N`, is well defined
(`transfer_ball`, `transfer_handle`, `transfer_neck`); `transfer N N₀` is a left inverse
(`transfer_transfer`), and every point of `U` is a transfer (`exists_transfer_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1G : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance ballCharts_ASML1G : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

namespace CycleNormalForm

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U : Set X}
  (N : CycleNormalForm I X len ε U)

theorem ball_eq_ball_iff {k k' : Fin len} {x x' : ClosedCell 3} :
    N.ball k x = N.ball k' x' ↔ k = k' ∧ x = x' := by
  constructor
  · intro h
    have hk : k = k' := by
      by_contra hne
      exact Set.disjoint_left.mp (N.ball_disjoint hne) ⟨x, rfl⟩ ⟨x', h.symm⟩
    subst hk
    exact ⟨rfl, N.ball_injective k h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem handle_eq_handle_iff {k k' : Fin len} {q q' : ClosedCell 2 × Icc (0 : ℝ) 1} :
    N.handle k q = N.handle k' q' ↔ k = k' ∧ q = q' := by
  constructor
  · intro h
    have hk : k = k' := by
      by_contra hne
      exact Set.disjoint_left.mp (N.handle_disjoint hne) ⟨q, rfl⟩ ⟨q', h.symm⟩
    subst hk
    exact ⟨rfl, N.handle_injective k h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem neck_mem_target {k : Fin len} {b : Bool} {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ neckDomain ε) : N.neck k b q ∈ (N.neck k b).target :=
  (N.neck k b).map_source (by rw [N.neck_source]; exact hq)

theorem neck_eq_neck_iff {k k' : Fin len} {b b' : Bool} {q q' : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ neckDomain ε) (hq' : q' ∈ neckDomain ε) :
    N.neck k b q = N.neck k' b' q' ↔ k = k' ∧ b = b' ∧ q = q' := by
  constructor
  · intro h
    have hkb : (k, b) = (k', b') := by
      by_contra hne
      exact Set.disjoint_left.mp (N.neck_disjoint k b k' b' hne) (N.neck_mem_target hq)
        (h ▸ N.neck_mem_target hq')
    simp only [Prod.mk.injEq] at hkb
    obtain ⟨rfl, rfl⟩ := hkb
    refine ⟨rfl, rfl, ?_⟩
    exact (N.neck k b).toPartialEquiv.injOn (by rw [N.neck_source]; exact hq)
      (by rw [N.neck_source]; exact hq') h
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem iccEnd_val (b : Bool) : ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) = if b then 1 else 0 := by
  cases b <;> rfl

/-- A handle point that is also a ball point lies on an end face. -/
theorem handle_mem_ball_end {k j : Fin len} {q : ClosedCell 2 × Icc (0 : ℝ) 1}
    (h : N.handle k q ∈ range (N.ball j)) : (q.2 : ℝ) = 0 ∨ (q.2 : ℝ) = 1 := by
  have hmem : N.handle k q ∈ range (N.handle k) ∩ range (N.ball j) := ⟨⟨q, rfl⟩, h⟩
  rw [N.handle_ball_inter k j] at hmem
  rcases hmem with hm | hm
  · split_ifs at hm
    · obtain ⟨q', hq', hqq'⟩ := hm
      rw [N.handle_injective k hqq'] at hq'
      left
      rw [hq', iccEnd_val]
      rfl
    · exact hm.elim
  · split_ifs at hm
    · obtain ⟨q', hq', hqq'⟩ := hm
      rw [N.handle_injective k hqq'] at hq'
      right
      rw [hq', iccEnd_val]
      rfl
    · exact hm.elim

/-- A ball point inside a neck belongs to the labelled ball. -/
theorem eq_rimBall_of_neck_mem_ball {k j : Fin len} {b : Bool} {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ neckDomain ε) (h : N.neck k b q ∈ range (N.ball j)) : j = rimBall len k b := by
  have hT := N.neck_mem_target (k := k) (b := b) hq
  have hpieces := N.neck_pieces k b ⟨hT, Or.inl (Set.mem_iUnion.mpr ⟨j, h⟩)⟩
  have hball_or : N.neck k b q ∈ range (N.ball (rimBall len k b)) → j = rimBall len k b := by
    intro hr
    by_contra hne
    exact Set.disjoint_left.mp (N.ball_disjoint hne) h hr
  rcases hpieces with hr | hH
  · exact hball_or hr
  · obtain ⟨hq0, hq1⟩ := (N.neck_handle k b hq).mp hH
    rcases eq_or_lt_of_le hq0 with h0 | hpos
    · exact hball_or ((N.neck_ball k b hq).mpr h0.symm.le)
    · obtain ⟨q'', hq''end, hq''⟩ := exists_handleEnd_eq N.ε_le b hq hq0 hq1
      have hhq : N.handle k q'' = N.neck k b q := by rw [N.handle_end k b q'' hq''end, hq'']
      have hend := N.handle_mem_ball_end (hhq ▸ h)
      have hcoord : endCoord b (q''.2 : ℝ) = q.2 := congrArg Prod.snd hq''
      exfalso
      cases b
      · change (q''.2 : ℝ) = q.2 at hcoord
        have hlt : q.2 < 2 * ε := (abs_lt.mp hq.2).2
        have h18 := N.ε_le
        rcases hend with he | he <;> linarith
      · change 1 - (q''.2 : ℝ) = q.2 at hcoord
        have hlt : q.2 < 2 * ε := (abs_lt.mp hq.2).2
        have h18 := N.ε_le
        rcases hend with he | he <;> linarith

theorem ball_eq_neck_iff {j k : Fin len} {b : Bool} {x : ClosedCell 3}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ neckDomain ε) :
    N.ball j x = N.neck k b q ↔
      j = rimBall len k b ∧ x ∈ neckCapRegion ε b ∧
        capMap b (x : EuclideanSpace ℝ (Fin 3)) = q := by
  constructor
  · intro h
    have hj := N.eq_rimBall_of_neck_mem_ball hq ⟨x, h⟩
    subst hj
    have hq0 : q.2 ≤ 0 := (N.neck_ball k b hq).mp ⟨x, h⟩
    obtain ⟨x', hx', hx'q⟩ := exists_capRegion_capMap_eq N.ε_pos N.ε_le b hq hq0
    have hball := N.ball_cap k b x' hx'
    rw [hx'q, ← h] at hball
    have hxx := N.ball_injective _ hball
    subst hxx
    exact ⟨rfl, hx', hx'q⟩
  · rintro ⟨rfl, hx, rfl⟩
    exact N.ball_cap k b x hx

/-- A handle point inside a neck belongs to the labelled handle. -/
theorem eq_of_neck_mem_handle {k j : Fin len} {b : Bool} {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ neckDomain ε) (h : N.neck k b q ∈ range (N.handle j)) : j = k := by
  by_contra hne
  have hT := N.neck_mem_target (k := k) (b := b) hq
  obtain ⟨q₁, hq₁⟩ := h
  -- an open set of handle parameters around `q₁` mapped into the neck target
  let O : Set (ClosedCell 2 × Icc (0 : ℝ) 1) := N.handle j ⁻¹' (N.neck k b).target
  have hO : IsOpen O := (N.neck k b).open_target.preimage (N.handle_smooth j).continuous
  have hq₁O : (q₁.1, q₁.2) ∈ O := by
    change N.handle j q₁ ∈ (N.neck k b).target
    rw [hq₁]
    exact hT
  obtain ⟨s, hsO, hs0, hs1⟩ := BallHandleCycle.exists_mem_Ioo_of_isOpen hO hq₁O
  have hpieces := N.neck_pieces k b ⟨hsO, Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨_, rfl⟩⟩)⟩
  rcases hpieces with hr | hH
  · rcases N.handle_mem_ball_end hr with he | he
    · change (s : ℝ) = 0 at he
      linarith
    · change (s : ℝ) = 1 at he
      linarith
  · exact Set.disjoint_left.mp (N.handle_disjoint hne) ⟨_, rfl⟩ hH

theorem handle_eq_neck_iff {j k : Fin len} {b : Bool} {q' : ClosedCell 2 × Icc (0 : ℝ) 1}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ neckDomain ε) :
    N.handle j q' = N.neck k b q ↔
      j = k ∧ |(q'.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε ∧ handleEnd b q' = q := by
  constructor
  · intro h
    have hj := N.eq_of_neck_mem_handle hq ⟨q', h⟩
    subst hj
    obtain ⟨hq0, hq1⟩ := (N.neck_handle j b hq).mp ⟨q', h⟩
    obtain ⟨q'', hq''end, hq''⟩ := exists_handleEnd_eq N.ε_le b hq hq0 hq1
    have hh := N.handle_end j b q'' hq''end
    rw [hq'', ← h] at hh
    have hqq := N.handle_injective j hh
    subst hqq
    exact ⟨rfl, hq''end, hq''⟩
  · rintro ⟨rfl, hend, rfl⟩
    exact N.handle_end j b q' hend

theorem ball_eq_handle_iff {j k : Fin len} {x : ClosedCell 3} {q : ClosedCell 2 × Icc (0 : ℝ) 1} :
    N.ball j x = N.handle k q ↔ ∃ b : Bool, j = rimBall len k b ∧
      (q.2 : ℝ) = (iccEnd b : ℝ) ∧ x ∈ neckCapRegion ε b ∧
        capMap b (x : EuclideanSpace ℝ (Fin 3)) = handleEnd b q := by
  constructor
  · intro h
    have hmem : N.handle k q ∈ range (N.handle k) ∩ range (N.ball j) := ⟨⟨q, rfl⟩, ⟨x, h⟩⟩
    rw [N.handle_ball_inter k j] at hmem
    have hend : ∃ b : Bool, (q.2 : ℝ) = (iccEnd b : ℝ) := by
      rcases hmem with hm | hm
      · split_ifs at hm
        · obtain ⟨q₃, hq₃, hq₃q⟩ := hm
          rw [N.handle_injective k hq₃q] at hq₃
          exact ⟨false, by rw [hq₃]⟩
        · exact hm.elim
      · split_ifs at hm
        · obtain ⟨q₃, hq₃, hq₃q⟩ := hm
          rw [N.handle_injective k hq₃q] at hq₃
          exact ⟨true, by rw [hq₃]⟩
        · exact hm.elim
    obtain ⟨b, hb⟩ := hend
    have hendb : |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε := by
      rw [hb, sub_self, abs_zero]
      linarith [N.ε_pos]
    have hneck := (handleEnd_mem_neckDomain b hendb).1
    have hh := N.handle_end k b q hendb
    rw [hh] at h
    obtain ⟨hj, hx, hcap⟩ := (N.ball_eq_neck_iff hneck).mp h
    exact ⟨b, hj, hb, hx, hcap⟩
  · rintro ⟨b, rfl, hb, hx, hcap⟩
    have hendb : |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε := by
      rw [hb, sub_self, abs_zero]
      linarith [N.ε_pos]
    rw [N.ball_cap k b x hx, hcap, N.handle_end k b q hendb]

theorem ball_mem (k : Fin len) (x : ClosedCell 3) : N.ball k x ∈ U := by
  refine (Set.ext_iff.mp N.union_eq _).mpr ?_
  exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨k, x, rfl⟩))

theorem handle_mem (k : Fin len) (q : ClosedCell 2 × Icc (0 : ℝ) 1) : N.handle k q ∈ U := by
  refine (Set.ext_iff.mp N.union_eq _).mpr ?_
  exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨k, q, rfl⟩))

theorem neck_mem (k : Fin len) (b : Bool) {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ neckDomain ε) (hψ : neckRounding ε q ≤ 0) : N.neck k b q ∈ U := by
  refine (Set.ext_iff.mp N.union_eq _).mpr ?_
  exact Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨b, q, ⟨hq, hψ⟩, rfl⟩⟩)

/-- Every point of `U` has a description by a ball, a handle or a rounded neck point. -/
theorem mem_union_cases {p : X} (hp : p ∈ U) :
    (∃ k x, N.ball k x = p) ∨ (∃ k q, N.handle k q = p) ∨
      ∃ k b q, (q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0) ∧ N.neck k b q = p := by
  rw [N.union_eq] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨k, x, hx⟩ := Set.mem_iUnion.mp hp
    exact Or.inl ⟨k, x, hx⟩
  · obtain ⟨k, q, hq⟩ := Set.mem_iUnion.mp hp
    exact Or.inr (Or.inl ⟨k, q, hq⟩)
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    obtain ⟨b, q, hq, hqp⟩ := Set.mem_iUnion.mp hk
    exact Or.inr (Or.inr ⟨k, b, q, hq, hqp⟩)

end CycleNormalForm

section Transfer

variable {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₀}
  {X₀ : Type*} [TopologicalSpace X₀] [ChartedSpace H₀ X₀]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U₀ : Set X₀} {U : Set X}
  (N₀ : CycleNormalForm I₀ X₀ len ε U₀) (N : CycleNormalForm I X len ε U)

/-- The transfer of a point of `U₀` along its description. -/
def transfer (p : X₀) (hp : p ∈ U₀) : X := by
  classical
  exact if h1 : ∃ k x, N₀.ball k x = p then N.ball h1.choose h1.choose_spec.choose
    else if h2 : ∃ k q, N₀.handle k q = p then N.handle h2.choose h2.choose_spec.choose
    else
      have h3 : ∃ k b q, (q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0) ∧ N₀.neck k b q = p :=
        ((N₀.mem_union_cases hp).resolve_left h1).resolve_left h2
      N.neck h3.choose h3.choose_spec.choose h3.choose_spec.choose_spec.choose

theorem transfer_ball (k : Fin len) (x : ClosedCell 3) (hp : N₀.ball k x ∈ U₀) :
    transfer N₀ N (N₀.ball k x) hp = N.ball k x := by
  classical
  have h1 : ∃ k' x', N₀.ball k' x' = N₀.ball k x := ⟨k, x, rfl⟩
  rw [transfer, dite_eq_left h1]
  obtain ⟨hk, hx⟩ := (N₀.ball_eq_ball_iff).mp h1.choose_spec.choose_spec
  rw [N.ball_eq_ball_iff]
  exact ⟨hk, hx⟩

theorem transfer_handle (k : Fin len) (q : ClosedCell 2 × Icc (0 : ℝ) 1)
    (hp : N₀.handle k q ∈ U₀) : transfer N₀ N (N₀.handle k q) hp = N.handle k q := by
  classical
  rw [transfer]
  by_cases h1 : ∃ k' x', N₀.ball k' x' = N₀.handle k q
  · rw [dite_eq_left h1]
    exact (N.ball_eq_handle_iff).mpr ((N₀.ball_eq_handle_iff).mp h1.choose_spec.choose_spec)
  · have h2 : ∃ k' q', N₀.handle k' q' = N₀.handle k q := ⟨k, q, rfl⟩
    rw [dite_eq_right h1, dite_eq_left h2]
    exact (N.handle_eq_handle_iff).mpr ((N₀.handle_eq_handle_iff).mp h2.choose_spec.choose_spec)

theorem transfer_neck (k : Fin len) (b : Bool) {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ neckDomain ε) (hp : N₀.neck k b q ∈ U₀) :
    transfer N₀ N (N₀.neck k b q) hp = N.neck k b q := by
  classical
  rw [transfer]
  by_cases h1 : ∃ k' x', N₀.ball k' x' = N₀.neck k b q
  · rw [dite_eq_left h1]
    exact (N.ball_eq_neck_iff hq).mpr ((N₀.ball_eq_neck_iff hq).mp h1.choose_spec.choose_spec)
  · rw [dite_eq_right h1]
    by_cases h2 : ∃ k' q', N₀.handle k' q' = N₀.neck k b q
    · rw [dite_eq_left h2]
      exact (N.handle_eq_neck_iff hq).mpr
        ((N₀.handle_eq_neck_iff hq).mp h2.choose_spec.choose_spec)
    · rw [dite_eq_right h2]
      set h3 : ∃ k' b' q', (q' ∈ neckDomain ε ∧ neckRounding ε q' ≤ 0) ∧ N₀.neck k' b' q' =
          N₀.neck k b q := ((N₀.mem_union_cases hp).resolve_left h1).resolve_left h2
      have hspec := h3.choose_spec.choose_spec.choose_spec
      exact (N.neck_eq_neck_iff hspec.1.1 hq).mpr
        ((N₀.neck_eq_neck_iff hspec.1.1 hq).mp hspec.2)

theorem transfer_mem (p : X₀) (hp : p ∈ U₀) : transfer N₀ N p hp ∈ U := by
  rcases N₀.mem_union_cases hp with ⟨k, x, rfl⟩ | ⟨k, q, rfl⟩ | ⟨k, b, q, hq, rfl⟩
  · rw [transfer_ball]
    exact N.ball_mem k x
  · rw [transfer_handle]
    exact N.handle_mem k q
  · rw [transfer_neck N₀ N k b hq.1]
    exact N.neck_mem k b hq.1 hq.2

theorem transfer_transfer (p : X₀) (hp : p ∈ U₀) :
    transfer N N₀ (transfer N₀ N p hp) (transfer_mem N₀ N p hp) = p := by
  rcases N₀.mem_union_cases hp with ⟨k, x, rfl⟩ | ⟨k, q, rfl⟩ | ⟨k, b, q, hq, rfl⟩
  · simp only [transfer_ball]
  · simp only [transfer_handle]
  · simp only [transfer_neck N₀ N k b hq.1, transfer_neck N N₀ k b hq.1]

theorem transfer_injective {p p' : X₀} (hp : p ∈ U₀) (hp' : p' ∈ U₀)
    (h : transfer N₀ N p hp = transfer N₀ N p' hp') : p = p' := by
  rw [← transfer_transfer N₀ N p hp, ← transfer_transfer N₀ N p' hp']
  simp only [h]

theorem exists_transfer_eq {y : X} (hy : y ∈ U) : ∃ p, ∃ hp : p ∈ U₀, transfer N₀ N p hp = y :=
  ⟨transfer N N₀ y hy, transfer_mem N N₀ y hy, transfer_transfer N N₀ y hy⟩

end Transfer

end GC.GraphManifold.Assembly
