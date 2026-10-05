import DifferentialGeometry.Topology.Manifold.OneManifold.CompactOneManifoldChoiceBCFApplications
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The shared `K₃` kernel KEEPS circle components: the unit circle (lane B-BCF134; D74-9, D74-19)

Review 74 D74-9: the shared kernel `exists_compact_oneManifold_choice74` must output circle components
(the closed route keeps the surface mapping torus over a circle component of `K₃`). This file is the
circle-component check of the acceptance plan (D74-19) for the kernel itself:

* `unitCircle_BCF`: the unit circle in `ℝ × ℝ`; `isCompact_unitCircle_BCF`;
* `unitCircleAtlas_BCF`: a graph atlas of the circle by the four half-circle graphs
  `t ↦ (±√(1 - t²), t)`, `t ↦ (t, ±√(1 - t²))` on `(-1, 1)`;
* `exists_compactOneDomain_circle_BCF`: K0 applied to `Kset = S¹` gives a domain whose carrier is the
  whole circle, with NO arc and at least one loop.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

/-- The unit circle in `ℝ × ℝ`. -/
def unitCircle_BCF : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- The circle is compact (closed and bounded). -/
theorem isCompact_unitCircle_BCF : IsCompact unitCircle_BCF := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).subset fun p hp => ?_
    have h : p.1 ^ 2 + p.2 ^ 2 = 1 := hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_le, abs_le]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]

/-- The sign attached to a boolean. -/
def boolSign_BCF (b : Bool) : ℝ := if b then 1 else -1

theorem boolSign_sq_BCF (b : Bool) : boolSign_BCF b * boolSign_BCF b = 1 := by
  cases b <;> simp [boolSign_BCF]

/-- The half-circle graph `t ↦ (s √(1 - t²), t)` on `(-1, 1)` is the part of the circle with
`s x > 0`. -/
theorem image_halfCircle_BCF (b : Bool) :
    (fun t : ℝ => (boolSign_BCF b * √(1 - t ^ 2), t)) '' Ioo (-1) 1 =
      unitCircle_BCF ∩ {p | 0 < boolSign_BCF b * p.1} := by
  have hs := boolSign_sq_BCF b
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    refine ⟨?_, ?_⟩
    · change (boolSign_BCF b * √(1 - t ^ 2)) ^ 2 + t ^ 2 = 1
      rw [mul_pow, Real.sq_sqrt h1.le, sq, hs]
      ring
    · change 0 < boolSign_BCF b * (boolSign_BCF b * √(1 - t ^ 2))
      rw [← mul_assoc, hs, one_mul]
      exact Real.sqrt_pos.mpr h1
  · rintro ⟨hp, hpos⟩
    have hc : p.1 ^ 2 + p.2 ^ 2 = 1 := hp
    have hp1 : 0 < p.1 ^ 2 := by
      have : p.1 ≠ 0 := fun h => by simp [h] at hpos
      positivity
    refine ⟨p.2, ⟨by nlinarith, by nlinarith⟩, Prod.ext ?_ rfl⟩
    change boolSign_BCF b * √(1 - p.2 ^ 2) = p.1
    rw [show 1 - p.2 ^ 2 = p.1 ^ 2 by linarith, Real.sqrt_sq_eq_abs]
    have hpos' : 0 < boolSign_BCF b * p.1 := hpos
    cases b
    · have : p.1 < 0 := by simpa [boolSign_BCF] using hpos'
      simp [boolSign_BCF, abs_of_neg this]
    · have : 0 < p.1 := by simpa [boolSign_BCF] using hpos'
      simp [boolSign_BCF, abs_of_pos this]

/-- The swapped half-circle graph `t ↦ (t, s √(1 - t²))` is the part of the circle with `s y > 0`. -/
theorem image_halfCircle_swap_BCF (b : Bool) :
    (fun t : ℝ => (t, boolSign_BCF b * √(1 - t ^ 2))) '' Ioo (-1) 1 =
      unitCircle_BCF ∩ {p | 0 < boolSign_BCF b * p.2} := by
  have h := congrArg (Prod.swap '' ·) (image_halfCircle_BCF b)
  simp only [image_image, Prod.swap_prod_mk] at h
  rw [h]
  ext p
  constructor
  · rintro ⟨q, ⟨hq, hqpos⟩, rfl⟩
    refine ⟨?_, hqpos⟩
    change q.2 ^ 2 + q.1 ^ 2 = 1
    have : q.1 ^ 2 + q.2 ^ 2 = 1 := hq
    linarith
  · rintro ⟨hp, hpos⟩
    refine ⟨p.swap, ⟨?_, hpos⟩, Prod.swap_swap p⟩
    change p.2 ^ 2 + p.1 ^ 2 = 1
    have : p.1 ^ 2 + p.2 ^ 2 = 1 := hp
    linarith

/-- `t ↦ √(1 - t²)` is smooth on `(-1, 1)`. -/
theorem contDiffOn_sqrt_one_sub_sq_BCF : ContDiffOn ℝ ∞ (fun t : ℝ => √(1 - t ^ 2)) (Ioo (-1) 1) :=
  fun t ht => (Real.contDiffAt_sqrt (by
    intro h
    simp only [id] at h
    nlinarith [ht.1, ht.2])).comp t
    (contDiffAt_const.sub (contDiffAt_id.pow 2)) |>.contDiffWithinAt

/-- **The graph atlas of the unit circle** by four half-circle graphs. -/
def unitCircleAtlas_BCF : GraphAtlas1_BCF (Bool × Bool) unitCircle_BCF where
  coord j := if j.1 then ContinuousLinearMap.fst ℝ ℝ ℝ else ContinuousLinearMap.snd ℝ ℝ ℝ
  param j := if j.1 then fun t => (t, boolSign_BCF j.2 * √(1 - t ^ 2))
    else fun t => (boolSign_BCF j.2 * √(1 - t ^ 2), t)
  dom _ := Ioo (-1) 1
  isOpen_dom _ := isOpen_Ioo
  param_smooth j := by
    rcases j with ⟨a, b⟩
    cases a
    · exact (contDiffOn_const.mul contDiffOn_sqrt_one_sub_sq_BCF).prodMk contDiffOn_id
    · exact contDiffOn_id.prodMk (contDiffOn_const.mul contDiffOn_sqrt_one_sub_sq_BCF)
  coord_param j t _ := by
    rcases j with ⟨a, b⟩
    cases a <;> rfl
  piece_relOpen j := by
    rcases j with ⟨a, b⟩
    cases a
    · refine ⟨{p | 0 < boolSign_BCF b * p.1},
        isOpen_lt continuous_const (continuous_const.mul continuous_fst), ?_⟩
      rw [inter_comm]
      exact (image_halfCircle_BCF b).symm
    · refine ⟨{p | 0 < boolSign_BCF b * p.2},
        isOpen_lt continuous_const (continuous_const.mul continuous_snd), ?_⟩
      rw [inter_comm]
      exact (image_halfCircle_swap_BCF b).symm
  cover := by
    ext p
    constructor
    · intro hp
      have hc : p.1 ^ 2 + p.2 ^ 2 = 1 := hp
      rw [mem_iUnion]
      rcases lt_trichotomy p.1 0 with h1 | h1 | h1
      · refine ⟨(false, false), ?_⟩
        change p ∈ (fun t : ℝ => (boolSign_BCF false * √(1 - t ^ 2), t)) '' Ioo (-1) 1
        rw [image_halfCircle_BCF]
        exact ⟨hp, by simp [boolSign_BCF, h1]⟩
      · rcases lt_or_gt_of_ne (show p.2 ≠ 0 by
            intro h2
            rw [h1, h2] at hc
            norm_num at hc) with h2 | h2
        · refine ⟨(true, false), ?_⟩
          change p ∈ (fun t : ℝ => (t, boolSign_BCF false * √(1 - t ^ 2))) '' Ioo (-1) 1
          rw [image_halfCircle_swap_BCF]
          exact ⟨hp, by simp [boolSign_BCF, h2]⟩
        · refine ⟨(true, true), ?_⟩
          change p ∈ (fun t : ℝ => (t, boolSign_BCF true * √(1 - t ^ 2))) '' Ioo (-1) 1
          rw [image_halfCircle_swap_BCF]
          exact ⟨hp, by simp [boolSign_BCF, h2]⟩
      · refine ⟨(false, true), ?_⟩
        change p ∈ (fun t : ℝ => (boolSign_BCF true * √(1 - t ^ 2), t)) '' Ioo (-1) 1
        rw [image_halfCircle_BCF]
        exact ⟨hp, by simp [boolSign_BCF, h1]⟩
    · intro hp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      rcases j with ⟨a, b⟩
      cases a
      · have h : p ∈ (fun t : ℝ => (boolSign_BCF b * √(1 - t ^ 2), t)) '' Ioo (-1) 1 := hj
        rw [image_halfCircle_BCF] at h
        exact h.1
      · have h : p ∈ (fun t : ℝ => (t, boolSign_BCF b * √(1 - t ^ 2))) '' Ioo (-1) 1 := hj
        rw [image_halfCircle_swap_BCF] at h
        exact h.1

/-- **Circle components are kept** (D74-9 / D74-19): the shared kernel K0 applied to the whole unit
circle returns a compact smooth one-dimensional domain whose carrier is the circle, with no arc and at
least one loop. -/
theorem exists_compactOneDomain_circle_BCF :
    ∃ D : SmoothCompactOneDomain_BCF unitCircle_BCF, D.carrier = unitCircle_BCF ∧ D.m = 0 ∧
      0 < D.l := by
  obtain ⟨D, hD, -⟩ := unitCircleAtlas_BCF.exists_compact_oneManifold_choice74_BCF
    (Q := unitCircle_BCF) (F := ∅) isCompact_unitCircle_BCF subset_rfl finite_empty
  have hsub : unitCircle_BCF ⊆ D.carrier := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hD hx
    exact (interior_subset hy : y ∈ Subtype.val ⁻¹' D.carrier)
  have hcar : D.carrier = unitCircle_BCF := Subset.antisymm D.subset_base hsub
  have hfr : D.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set unitCircle_BCF) =
      ∅ := by
    rw [hcar]
    exact sdiff_eq_empty.mpr (fun x hx => by
      have := hD hx
      rwa [hcar] at this)
  have hm : D.m = 0 := by
    by_contra hm
    obtain ⟨k⟩ : Nonempty (Fin D.m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    have h0 : D.arc k 0 ∈ ⋃ k, ({D.arc k 0, D.arc k 1} : Set (ℝ × ℝ)) :=
      mem_iUnion.mpr ⟨k, Or.inl rfl⟩
    rw [← D.relFrontier_eq, hfr] at h0
    exact h0
  refine ⟨D, hcar, hm, Nat.pos_of_ne_zero fun hl => ?_⟩
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ D.carrier := by
    rw [hcar]
    change (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1
    norm_num
  rw [D.carrier_eq] at h1
  rcases h1 with h1 | h1
  · obtain ⟨k, -⟩ := mem_iUnion.mp h1
    exact (hm ▸ k).elim0
  · obtain ⟨j, -⟩ := mem_iUnion.mp h1
    exact (hl ▸ j).elim0

end DifferentialGeometry.Topology
