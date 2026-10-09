import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimRounding
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

/-!
# Chapter-14 assembly, item L1: the ball–handle cycle

`BallHandleCycle W` is the input of L1 (`exists_solidTorus_of_ballHandleCycle`): `len` balls and
`len` product disk handles, handle `k` from ball `k` to ball `k + 1 mod len` (loops and parallel
edges allowed), the half-space / quadrant product charts at every rim, and the actual rounded union
as one connected piece.

The structure is the frozen V2 text (`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:767–802`,
review item 2, disposition D3) with ONE NEW FIELD and two linter-forced binder changes:

* **`rim_quadrant` (erratum E-L1, V3).** V2 constrains a rim chart target only against its OWN ball
  (`rim_ball`) and handle (`rim_handle`); the L1 conclusion is then FALSE for `len ≥ 2`. Counterexample
  (`build-logs/resume/sheet-ASM-L1.md`, E-L1): the target of rim chart `(0, false)` carries an arm,
  inside the chart region `{x > 1, y > 1}` (where `standardRimRounding > 0`), engulfing the middle of
  handle `1`, whose frontier inside that handle is two smooth capsule tips tangent to the handle's side
  to infinite order. Every V2 field holds, and `union_rim` / `union_away` force the union to be
  `B₀ ∪ H₀ ∪ B₁` plus two capsule stubs of `H₁` plus fillets: a smooth 3-ball, not a solid torus.
  The new field says that the open quadrant `{0 < x, 0 < y}` of every rim chart meets no ball and no
  handle. The certificate producer derives it (`AssemblyRimQuadrantProducer.lean`).
* `rim_source`, `rim_ball`, `rim_handle`, `union_rim` take the chart point `{p}` implicitly (the
  `explicitVarsOfIff` linter; same change as ASM-CERT's certificate rim fields).

Consequences proved here (they are what the rest of L1 uses):
* `disjoint_ball_target`, `disjoint_handle_target`: a rim chart target meets no other ball and no
  other handle;
* `range_union_eq`: the union is exactly the balls, the handles and the fillets
  `rimChart k b '' {0 < x, 0 < y, (x, y) ∈ rimBox 1, standardRimRounding (x, y) ≤ 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASML1 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- One cycle of FC42 step 6 (route A): `len` balls and `len` product disk handles, handle `k`
from ball `k` to ball `k + 1 mod len`, the half-space / quadrant product charts at every rim, the
common-rounding pullback equalities and the actual rounded union as one connected piece. V2 text
(review item 2, D3) plus the field `rim_quadrant` (erratum E-L1): the open quadrant of every rim
chart meets no ball and no handle. -/
structure BallHandleCycle (W : CompactCarrier.{u}) where
  len : ℕ
  len_pos : 0 < len
  ball : Fin len → PieceEmbedding W
  ballModel : ∀ k, (ball k).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3
  handle : Fin len → EdgeHandle W
  start_face : ∀ k, (handle k).endDisk false ⊆ (ball k).map '' (𝓡∂ 3).boundary (ball k).Piece
  end_face : ∀ k, (handle k).endDisk true ⊆
    (ball (finRotate len k)).map '' (𝓡∂ 3).boundary (ball (finRotate len k)).Piece
  handle_ball_inter : ∀ k j, range (handle k).map ∩ range (ball j).map =
    (if j = k then (handle k).endDisk false else ∅) ∪
      (if j = finRotate len k then (handle k).endDisk true else ∅)
  ball_disjoint : Pairwise fun k k' => Disjoint (range (ball k).map) (range (ball k').map)
  handle_disjoint : Pairwise fun k k' => Disjoint (range (handle k).map) (range (handle k').map)
  rimChart : Fin len → Bool →
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞
  rim_source : ∀ k b {p}, p ∈ (rimChart k b).source ↔ p.2 ∈ rimBox 2
  rim_ball : ∀ k b {p}, p ∈ (rimChart k b).source →
    (rimChart k b p ∈ range (ball (rimBall len k b)).map ↔ p.2.2 ≤ 0)
  rim_handle : ∀ k b {p}, p ∈ (rimChart k b).source →
    (rimChart k b p ∈ range (handle k).map ↔ (0 ≤ p.2.2 ∧ p.2.1 ≤ 0))
  /-- NEW (erratum E-L1): the open quadrant of a rim chart meets no ball and no handle. -/
  rim_quadrant : ∀ k b p, p ∈ (rimChart k b).source → 0 < p.2.1 → 0 < p.2.2 →
    rimChart k b p ∉ (⋃ j, range (ball j).map) ∪ ⋃ j, range (handle j).map
  rim_label : ∀ k b, rimChart k b '' {p | p.2 = (0, 0)} =
    (fun x : ClosedCell 2 => (handle k).map (x, iccEnd b)) '' diskRim
  rim_disjoint : ∀ k b k' b', (k, b) ≠ (k', b') →
    Disjoint (rimChart k b).target (rimChart k' b').target
  roundingFn : W.Carrier → ℝ
  rimScale : Fin len → Bool → ℝ
  rimScale_pos : ∀ k b, 0 < rimScale k b
  rim_pullback : ∀ k b p, p ∈ (rimChart k b).source →
    roundingFn (rimChart k b p) = rimScale k b * standardRimRounding p.2
  union : PieceEmbedding W
  union_rim : ∀ k b {p}, p ∈ (rimChart k b).source →
    (rimChart k b p ∈ range union.map ↔ standardRimRounding p.2 ≤ 0)
  union_away : range union.map \ (⋃ k, ⋃ b, (rimChart k b).target) =
    ((⋃ k, range (ball k).map) ∪ ⋃ k, range (handle k).map) \
      (⋃ k, ⋃ b, (rimChart k b).target)

namespace BallHandleCycle

variable {W : CompactCarrier.{u}} (C : BallHandleCycle W)

/-- The fillet of rim `(k, b)`: the points that the rounding adds in the open quadrant. -/
def fillet (k : Fin C.len) (b : Bool) : Set W.Carrier :=
  C.rimChart k b '' {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2 ∈ rimBox 1 ∧ standardRimRounding p.2 ≤ 0}

theorem mem_target_of_mem_source {k : Fin C.len} {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (C.rimChart k b).source) : C.rimChart k b p ∈ (C.rimChart k b).target :=
  (C.rimChart k b).map_source hp

theorem exists_source_of_mem_target {k : Fin C.len} {b : Bool} {z : W.Carrier}
    (hz : z ∈ (C.rimChart k b).target) :
    ∃ p, p ∈ (C.rimChart k b).source ∧ C.rimChart k b p = z :=
  ⟨(C.rimChart k b).symm z, (C.rimChart k b).map_target hz, (C.rimChart k b).right_inv hz⟩

theorem isOpen_target (k : Fin C.len) (b : Bool) : IsOpen (C.rimChart k b).target :=
  (C.rimChart k b).open_target

/-- The end disks of a handle lie in the model-boundary images of the balls they touch. -/
theorem handle_inter_ball_subset (k j : Fin C.len) :
    range (C.handle k).map ∩ range (C.ball j).map ⊆
      (C.ball j).map '' (𝓡∂ 3).boundary (C.ball j).Piece := by
  rw [C.handle_ball_inter k j]
  rintro z (hz | hz)
  · split_ifs at hz with hj
    · subst hj
      exact C.start_face j hz
    · exact hz.elim
  · split_ifs at hz with hj
    · subst hj
      exact C.end_face k hz
    · exact hz.elim

/-- A nonempty open subset of a piece contains an interior point. -/
theorem exists_interior_mem_of_isOpen {P : PieceEmbedding W} {U : Set P.Piece} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ q ∈ U, (𝓡∂ 3).IsInteriorPoint q := by
  obtain ⟨q, hq⟩ := (ModelWithCorners.dense_interior (𝓡∂ 3) (M := P.Piece)).inter_open_nonempty
    U hU hne
  exact ⟨q, hq.1, hq.2⟩

/-- A rim chart target meets no ball other than its labelled one. -/
theorem disjoint_ball_target (k : Fin C.len) (b : Bool) (j : Fin C.len)
    (hj : j ≠ rimBall C.len k b) :
    Disjoint (range (C.ball j).map) (C.rimChart k b).target := by
  rw [Set.disjoint_left]
  rintro z ⟨q₀, rfl⟩ hz₀
  -- the open set of piece points mapped into the target
  let U : Set (C.ball j).Piece := (C.ball j).map ⁻¹' (C.rimChart k b).target
  have hU : IsOpen U := (C.isOpen_target k b).preimage (C.ball j).continuous_map
  obtain ⟨q, hqU, hqint⟩ := exists_interior_mem_of_isOpen hU ⟨q₀, hz₀⟩
  obtain ⟨p, hp, hpq⟩ := C.exists_source_of_mem_target hqU
  -- `(C.ball j).map q` is not in the labelled ball, hence `y > 0`
  have hnot : (C.ball j).map q ∉ range (C.ball (rimBall C.len k b)).map :=
    fun hmem => Set.disjoint_left.mp (C.ball_disjoint hj) ⟨q, rfl⟩ hmem
  have hy : 0 < p.2.2 := by
    by_contra hy
    exact hnot (hpq ▸ (C.rim_ball k b hp).mpr (not_lt.mp hy))
  have hx : p.2.1 ≤ 0 := by
    by_contra hx
    exact C.rim_quadrant k b p hp (not_le.mp hx) hy
      (Or.inl (Set.mem_iUnion.mpr ⟨j, hpq ▸ ⟨q, rfl⟩⟩))
  have hH : (C.ball j).map q ∈ range (C.handle k).map :=
    hpq ▸ (C.rim_handle k b hp).mpr ⟨hy.le, hx⟩
  obtain ⟨q', hq', hqq'⟩ := C.handle_inter_ball_subset k j ⟨hH, ⟨q, rfl⟩⟩
  have hqb : q' = q := (C.ball j).injective hqq'
  subst hqb
  exact ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint q').mp hqint hq'

/-- The interior times-slices of a handle: an open set of the handle source containing a point of
an end face contains a point with time strictly between `0` and `1`. -/
theorem exists_mem_Ioo_of_isOpen {U : Set (ClosedCell 2 × Icc (0 : ℝ) 1)} (hU : IsOpen U)
    {x : ClosedCell 2} {t : Icc (0 : ℝ) 1} (hxt : (x, t) ∈ U) :
    ∃ s : Icc (0 : ℝ) 1, (x, s) ∈ U ∧ 0 < (s : ℝ) ∧ (s : ℝ) < 1 := by
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hc0 : ∀ n, 0 < c n := fun n => by positivity
  have hc1 : ∀ n, c n ≤ 1 / 2 := fun n => by
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  let s : ℕ → Icc (0 : ℝ) 1 := fun n =>
    ⟨(t : ℝ) * (1 - c n) + c n / 2, by
      have := hc0 n
      have := hc1 n
      constructor <;> nlinarith⟩
  have hs : ∀ n, 0 < (s n : ℝ) ∧ (s n : ℝ) < 1 := fun n => by
    have := hc0 n
    have := hc1 n
    change 0 < (t : ℝ) * (1 - c n) + c n / 2 ∧ (t : ℝ) * (1 - c n) + c n / 2 < 1
    constructor <;> nlinarith
  have hc : Filter.Tendsto c Filter.atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
    refine h.congr (fun n => ?_)
    simp only [Function.comp_apply, c]
    push_cast
    ring
  have hsT : Filter.Tendsto s Filter.atTop (𝓝 t) := by
    rw [tendsto_subtype_rng]
    have h : Filter.Tendsto (fun n => (t : ℝ) * (1 - c n) + c n / 2) Filter.atTop
        (𝓝 ((t : ℝ) * (1 - 0) + 0 / 2)) :=
      ((tendsto_const_nhds.sub hc).const_mul (t : ℝ)).add (hc.div_const (2 : ℝ))
    simpa using h
  have hev : ∀ᶠ n in Filter.atTop, (x, s n) ∈ U :=
    ((continuous_const.prodMk continuous_id).tendsto t |>.comp hsT) (hU.mem_nhds hxt)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨s n, hn, hs n⟩

/-- A rim chart target meets no handle other than its own. -/
theorem disjoint_handle_target (k : Fin C.len) (b : Bool) (k' : Fin C.len) (hk : k' ≠ k) :
    Disjoint (range (C.handle k').map) (C.rimChart k b).target := by
  rw [Set.disjoint_left]
  rintro z ⟨q₀, rfl⟩ hz₀
  let U : Set (ClosedCell 2 × Icc (0 : ℝ) 1) := (C.handle k').map ⁻¹' (C.rimChart k b).target
  have hU : IsOpen U := (C.isOpen_target k b).preimage (C.handle k').smooth.continuous
  obtain ⟨s, hsU, hs0, hs1⟩ := exists_mem_Ioo_of_isOpen hU (x := q₀.1) (t := q₀.2) hz₀
  obtain ⟨p, hp, hpq⟩ := C.exists_source_of_mem_target hsU
  have hnot : (C.handle k').map (q₀.1, s) ∉ range (C.handle k).map :=
    fun hmem => Set.disjoint_left.mp (C.handle_disjoint hk) ⟨_, rfl⟩ hmem
  have hy : p.2.2 ≤ 0 := by
    by_contra hy
    have hy' : 0 < p.2.2 := not_le.mp hy
    by_cases hx : p.2.1 ≤ 0
    · exact hnot (hpq ▸ (C.rim_handle k b hp).mpr ⟨hy'.le, hx⟩)
    · exact C.rim_quadrant k b p hp (not_le.mp hx) hy'
        (Or.inr (Set.mem_iUnion.mpr ⟨k', hpq ▸ ⟨_, rfl⟩⟩))
  have hB : (C.handle k').map (q₀.1, s) ∈ range (C.ball (rimBall C.len k b)).map :=
    hpq ▸ (C.rim_ball k b hp).mpr hy
  have hmem := (C.handle_ball_inter k' (rimBall C.len k b)).subset ⟨⟨_, rfl⟩, hB⟩
  have hend : ∀ e : Bool, (C.handle k').map (q₀.1, s) ∉ (C.handle k').endDisk e := by
    rintro e ⟨x', hx'⟩
    have h := congrArg (fun q : ClosedCell 2 × Icc (0 : ℝ) 1 => (q.2 : ℝ))
      ((C.handle k').injective hx')
    simp only at h
    cases e <;> simp [iccEnd] at h <;> linarith
  rcases hmem with h | h
  · split_ifs at h
    · exact hend false h
    · exact h
  · split_ifs at h
    · exact hend true h
    · exact h

/-- A rim chart target meets the balls and handles only in its own ball and handle. -/
theorem target_inter_pieces (k : Fin C.len) (b : Bool) :
    (C.rimChart k b).target ∩ ((⋃ j, range (C.ball j).map) ∪ ⋃ j, range (C.handle j).map) =
      (C.rimChart k b).target ∩
        (range (C.ball (rimBall C.len k b)).map ∪ range (C.handle k).map) := by
  apply Subset.antisymm
  · rintro z ⟨hzT, hz | hz⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      by_cases hjk : j = rimBall C.len k b
      · exact ⟨hzT, Or.inl (hjk ▸ hj)⟩
      · exact (Set.disjoint_left.mp (C.disjoint_ball_target k b j hjk) hj hzT).elim
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      by_cases hjk : j = k
      · exact ⟨hzT, Or.inr (hjk ▸ hj)⟩
      · exact (Set.disjoint_left.mp (C.disjoint_handle_target k b j hjk) hj hzT).elim
  · rintro z ⟨hzT, hz | hz⟩
    · exact ⟨hzT, Or.inl (Set.mem_iUnion.mpr ⟨_, hz⟩)⟩
    · exact ⟨hzT, Or.inr (Set.mem_iUnion.mpr ⟨_, hz⟩)⟩

theorem fillet_subset_target (k : Fin C.len) (b : Bool) :
    C.fillet k b ⊆ (C.rimChart k b).target := by
  rintro z ⟨p, hp, rfl⟩
  exact C.mem_target_of_mem_source ((C.rim_source k b).mpr (rimBox_mono (by norm_num) hp.2.2.1))

/-- **The union is the balls, the handles and the fillets.** -/
theorem range_union_eq :
    range C.union.map = ((⋃ k, range (C.ball k).map) ∪ ⋃ k, range (C.handle k).map) ∪
      ⋃ k, ⋃ b, C.fillet k b := by
  apply Subset.antisymm
  · intro z hz
    by_cases hT : z ∈ ⋃ k, ⋃ b, (C.rimChart k b).target
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hT
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hk
      obtain ⟨p, hp, rfl⟩ := C.exists_source_of_mem_target hb
      have hψ : standardRimRounding p.2 ≤ 0 := (C.union_rim k b hp).mp hz
      rcases standardRimRounding_nonpos_iff_or_fillet.mp hψ with hy | hx | hf
      · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨_, (C.rim_ball k b hp).mpr hy⟩))
      · by_cases hy : 0 ≤ p.2.2
        · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨k, (C.rim_handle k b hp).mpr ⟨hy, hx⟩⟩))
        · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨_, (C.rim_ball k b hp).mpr (le_of_not_ge hy)⟩))
      · exact Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨b, ⟨p, hf, rfl⟩⟩⟩)
    · have h : z ∈ range C.union.map \ (⋃ k, ⋃ b, (C.rimChart k b).target) := ⟨hz, hT⟩
      rw [C.union_away] at h
      exact Or.inl h.1
  · intro z hz
    rcases hz with hz | hz
    · by_cases hT : z ∈ ⋃ k, ⋃ b, (C.rimChart k b).target
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hT
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hk
        have hz' := (C.target_inter_pieces k b).subset ⟨hb, hz⟩
        obtain ⟨p, hp, rfl⟩ := C.exists_source_of_mem_target hb
        apply (C.union_rim k b hp).mpr
        rcases hz'.2 with h | h
        · exact standardRimRounding_nonpos_of p.2 (Or.inl ((C.rim_ball k b hp).mp h))
        · exact standardRimRounding_nonpos_of p.2 (Or.inr ((C.rim_handle k b hp).mp h).2)
      · have h : z ∈ ((⋃ k, range (C.ball k).map) ∪ ⋃ k, range (C.handle k).map) \
            (⋃ k, ⋃ b, (C.rimChart k b).target) := ⟨hz, hT⟩
        rw [← C.union_away] at h
        exact h.1
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      obtain ⟨b, ⟨p, hp, rfl⟩⟩ := Set.mem_iUnion.mp hk
      exact (C.union_rim k b ((C.rim_source k b).mpr (rimBox_mono (by norm_num) hp.2.2.1))).mpr
        hp.2.2.2

theorem ball_subset_union (k : Fin C.len) : range (C.ball k).map ⊆ range C.union.map := by
  rw [C.range_union_eq]
  exact fun z hz => Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨k, hz⟩))

theorem handle_subset_union (k : Fin C.len) : range (C.handle k).map ⊆ range C.union.map := by
  rw [C.range_union_eq]
  exact fun z hz => Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨k, hz⟩))

end BallHandleCycle

end GC.GraphManifold.Assembly
