import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def standardBarycentricSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

omit [DecidableEq ι] in
theorem isClosed_standardBarycentricSimplex : IsClosed (standardBarycentricSimplex ι) := by
  have heq : standardBarycentricSimplex ι = (⋂ i, {x : ι → ℝ | 0 ≤ x i}) ∩
      {x | ∑ i, x i = 1} := by ext x; simp [standardBarycentricSimplex]
  rw [heq]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_eq (by fun_prop) continuous_const)

omit [DecidableEq ι] in
theorem isCompact_standardBarycentricSimplex : IsCompact (standardBarycentricSimplex ι) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : ι → ℝ) 1)).of_isClosed_subset
    isClosed_standardBarycentricSimplex
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  have hi : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  rwa [hx.2] at hi

def barycentricHyperplane (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {x | ∑ i, x i = 1}

structure SimplexSplit (ι : Type*) [Fintype ι] [DecidableEq ι] where
  left : Finset ι
  left_nonempty : left.Nonempty
  right_nonempty : leftᶜ.Nonempty

namespace SimplexSplit

variable (s : SimplexSplit ι)

abbrev right : Finset ι := s.leftᶜ

theorem left_card_pos : 0 < (s.left.card : ℝ) := by
  exact_mod_cast s.left_nonempty.card_pos

theorem right_card_pos : 0 < (s.right.card : ℝ) := by
  exact_mod_cast s.right_nonempty.card_pos

def direction (i : ι) : ℝ := if i ∈ s.left then -1 / s.left.card else 1 / s.right.card

theorem direction_of_mem_left {i : ι} (hi : i ∈ s.left) :
    s.direction i = -1 / s.left.card := ite_eq_left hi

theorem direction_of_mem_right {i : ι} (hi : i ∈ s.right) :
    s.direction i = 1 / s.right.card := ite_eq_right (Finset.mem_compl.mp hi)

theorem sum_left_direction : ∑ i ∈ s.left, s.direction i = -1 := by
  calc
    _ = ∑ _i ∈ s.left, (-1 : ℝ) / s.left.card :=
      Finset.sum_congr rfl (fun i hi => s.direction_of_mem_left hi)
    _ = -1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp [s.left_card_pos.ne']

theorem sum_right_direction : ∑ i ∈ s.right, s.direction i = 1 := by
  calc
    _ = ∑ _i ∈ s.right, (1 : ℝ) / s.right.card :=
      Finset.sum_congr rfl (fun i hi => s.direction_of_mem_right hi)
    _ = 1 := by simp [nsmul_eq_mul, s.right_card_pos.ne']

theorem sum_direction : ∑ i, s.direction i = 0 := by
  rw [← Finset.sum_add_sum_compl s.left (s.direction)]
  change (∑ i ∈ s.left, s.direction i) + (∑ i ∈ s.right, s.direction i) = 0
  rw [s.sum_left_direction, s.sum_right_direction]
  norm_num

def fiberPoint (z : ι → ℝ) (t : ℝ) : ι → ℝ := fun i => z i + t * s.direction i

theorem sum_fiberPoint (z : ι → ℝ) (t : ℝ) : ∑ i, s.fiberPoint z t i = ∑ i, z i := by
  simp only [fiberPoint, Finset.sum_add_distrib, ← Finset.mul_sum,
    s.sum_direction, mul_zero, add_zero]

theorem sum_left_fiberPoint (z : ι → ℝ) (t : ℝ) :
    ∑ i ∈ s.left, s.fiberPoint z t i = (∑ i ∈ s.left, z i) - t := by
  simp only [fiberPoint, Finset.sum_add_distrib, ← Finset.mul_sum,
    s.sum_left_direction, mul_neg_one, sub_eq_add_neg]

noncomputable def lower (z : ι → ℝ) : ℝ :=
  s.right.sup' s.right_nonempty (fun i => -(s.right.card : ℝ) * z i)

noncomputable def upper (z : ι → ℝ) : ℝ :=
  s.left.inf' s.left_nonempty (fun i => (s.left.card : ℝ) * z i)

theorem nonneg_fiberPoint_iff_of_mem_left {i : ι} (hi : i ∈ s.left) (z : ι → ℝ) (t : ℝ) :
    0 ≤ s.fiberPoint z t i ↔ t ≤ (s.left.card : ℝ) * z i := by
  rw [fiberPoint, s.direction_of_mem_left hi]
  have heq : z i + t * (-1 / (s.left.card : ℝ)) = z i - t / s.left.card := by ring
  rw [heq, sub_nonneg, div_le_iff₀ s.left_card_pos, mul_comm]

theorem nonneg_fiberPoint_iff_of_mem_right {i : ι} (hi : i ∈ s.right) (z : ι → ℝ) (t : ℝ) :
    0 ≤ s.fiberPoint z t i ↔ -(s.right.card : ℝ) * z i ≤ t := by
  rw [fiberPoint, s.direction_of_mem_right hi]
  have heq : z i + t * (1 / (s.right.card : ℝ)) = z i + t / s.right.card := by ring
  rw [heq]
  calc
    0 ≤ z i + t / s.right.card ↔ -z i ≤ t / s.right.card := by
      constructor <;> intro h <;> linarith
    _ ↔ -z i * s.right.card ≤ t := le_div_iff₀ s.right_card_pos
    _ ↔ -(s.right.card : ℝ) * z i ≤ t := by ring_nf

theorem nonneg_fiberPoint_iff (z : ι → ℝ) (t : ℝ) :
    (∀ i, 0 ≤ s.fiberPoint z t i) ↔ t ∈ Icc (s.lower z) (s.upper z) := by
  change _ ↔ s.lower z ≤ t ∧ t ≤ s.upper z
  rw [lower, upper, Finset.sup'_le_iff, Finset.le_inf'_iff]
  constructor
  · intro h
    exact ⟨fun i hi => (s.nonneg_fiberPoint_iff_of_mem_right hi z t).mp (h i),
      fun i hi => (s.nonneg_fiberPoint_iff_of_mem_left hi z t).mp (h i)⟩
  · rintro ⟨hB, hA⟩ i
    by_cases hi : i ∈ s.left
    · exact (s.nonneg_fiberPoint_iff_of_mem_left hi z t).mpr (hA i hi)
    · have hiB : i ∈ s.right := Finset.mem_compl.mpr hi
      exact (s.nonneg_fiberPoint_iff_of_mem_right hiB z t).mpr (hB i hiB)

theorem fiberPoint_mem_simplex_iff (z : ι → ℝ) (t : ℝ) :
    s.fiberPoint z t ∈ standardBarycentricSimplex ι ↔
      (∑ i, z i = 1) ∧ t ∈ Icc (s.lower z) (s.upper z) := by
  change (∀ i, 0 ≤ s.fiberPoint z t i) ∧ (∑ i, s.fiberPoint z t i) = 1 ↔ _
  rw [s.nonneg_fiberPoint_iff, s.sum_fiberPoint, and_comm]

theorem continuous_lower : Continuous s.lower :=
  Continuous.finset_sup'_apply s.right_nonempty
    (fun i _ => continuous_const.mul (continuous_apply i))

theorem continuous_upper : Continuous s.upper :=
  Continuous.finset_inf'_apply s.left_nonempty
    (fun i _ => continuous_const.mul (continuous_apply i))

def horizontal : Set (ι → ℝ) := {z | (∑ i, z i = 1) ∧ ∑ i ∈ s.left, z i = 1 / 2}

def height (x : ι → ℝ) : ℝ := 1 / 2 - ∑ i ∈ s.left, x i

def project (x : ι → ℝ) : ι → ℝ := s.fiberPoint x (-s.height x)

theorem project_mem_horizontal {x : ι → ℝ} (hx : ∑ i, x i = 1) :
    s.project x ∈ s.horizontal := by
  refine ⟨(s.sum_fiberPoint x (-s.height x)).trans hx, ?_⟩
  rw [project, s.sum_left_fiberPoint, height]
  ring

theorem fiberPoint_project_height (x : ι → ℝ) : s.fiberPoint (s.project x) (s.height x) = x := by
  ext i
  simp only [project, fiberPoint]
  ring

theorem height_fiberPoint {z : ι → ℝ} (hz : z ∈ s.horizontal) (t : ℝ) :
    s.height (s.fiberPoint z t) = t := by
  rw [height, s.sum_left_fiberPoint, hz.2]
  ring

theorem project_fiberPoint {z : ι → ℝ} (hz : z ∈ s.horizontal) (t : ℝ) :
    s.project (s.fiberPoint z t) = z := by
  rw [project, s.height_fiberPoint hz]
  ext i
  simp only [fiberPoint]
  ring

theorem continuous_height : Continuous s.height := by unfold height; fun_prop

theorem continuous_project : Continuous s.project := by
  unfold project fiberPoint
  exact continuous_pi (fun i => (continuous_apply i).add (s.continuous_height.neg.mul continuous_const))

def prismCoordinates : barycentricHyperplane ι ≃ₜ (s.horizontal × ℝ) where
  toFun x := (⟨s.project x, s.project_mem_horizontal x.2⟩, s.height x)
  invFun p := ⟨s.fiberPoint p.1 p.2, (s.sum_fiberPoint p.1 p.2).trans p.1.2.1⟩
  left_inv x := Subtype.ext (s.fiberPoint_project_height x)
  right_inv p := Prod.ext (Subtype.ext (s.project_fiberPoint p.1.2 p.2))
    (s.height_fiberPoint p.1.2 p.2)
  continuous_toFun := ((s.continuous_project.comp continuous_subtype_val).subtype_mk _).prodMk
    (s.continuous_height.comp continuous_subtype_val)
  continuous_invFun := (continuous_pi (fun i =>
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).add
      (continuous_snd.mul continuous_const))).subtype_mk _

def base : Set s.horizontal := {z | s.lower z ≤ s.upper z}

theorem isClosed_base : IsClosed s.base :=
  isClosed_le (s.continuous_lower.comp continuous_subtype_val)
    (s.continuous_upper.comp continuous_subtype_val)

theorem base_eq_range_project : s.base =
    range (fun x : standardBarycentricSimplex ι =>
      (⟨s.project x, s.project_mem_horizontal x.2.2⟩ : s.horizontal)) := by
  ext z
  constructor
  · intro hz
    have hx : s.fiberPoint z (s.lower z) ∈ standardBarycentricSimplex ι :=
      (s.fiberPoint_mem_simplex_iff z (s.lower z)).mpr ⟨z.2.1, le_rfl, hz⟩
    exact ⟨⟨s.fiberPoint z (s.lower z), hx⟩, Subtype.ext (s.project_fiberPoint z.2 _)⟩
  · rintro ⟨x, rfl⟩
    have hx : s.fiberPoint (s.project x) (s.height x) ∈ standardBarycentricSimplex ι := by
      rw [s.fiberPoint_project_height]
      exact x.2
    have hb := ((s.fiberPoint_mem_simplex_iff _ _).mp hx).2
    exact hb.1.trans hb.2

theorem isCompact_base : IsCompact s.base := by
  have : CompactSpace (standardBarycentricSimplex ι) :=
    isCompact_iff_compactSpace.mp isCompact_standardBarycentricSimplex
  rw [s.base_eq_range_project]
  exact isCompact_range ((s.continuous_project.comp continuous_subtype_val).subtype_mk _)

theorem lower_eq_upper_of_mem_frontier {z : s.horizontal} (hz : z ∈ frontier s.base) :
    s.lower z = s.upper z := by
  have hle : s.lower z ≤ s.upper z := by
    change z ∈ s.base
    exact s.isClosed_base.closure_eq ▸ hz.1
  apply le_antisymm hle
  by_contra hnot
  have hlt : s.lower z < s.upper z := lt_of_not_ge hnot
  apply hz.2
  exact interior_maximal
    (show {z : s.horizontal | s.lower z < s.upper z} ⊆ s.base from
      fun z hz => show s.lower z ≤ s.upper z from hz.le)
    (isOpen_lt (s.continuous_lower.comp continuous_subtype_val)
      (s.continuous_upper.comp continuous_subtype_val)) hlt

theorem prismCoordinates_simplex_iff (x : barycentricHyperplane ι) :
    x.val ∈ standardBarycentricSimplex ι ↔
      (s.prismCoordinates x).2 ∈ Icc (s.lower (s.prismCoordinates x).1)
        (s.upper (s.prismCoordinates x).1) := by
  have h := s.fiberPoint_mem_simplex_iff (s.project x) (s.height x)
  rw [s.fiberPoint_project_height] at h
  exact h.trans (and_iff_right (s.project_mem_horizontal x.2).1)

theorem fiberPoint_eq_zero_iff_of_mem_left {i : ι} (hi : i ∈ s.left)
    (z : ι → ℝ) (t : ℝ) :
    s.fiberPoint z t i = 0 ↔ t = (s.left.card : ℝ) * z i := by
  have heq : (s.left.card : ℝ) * s.fiberPoint z t i = s.left.card * z i - t := by
    rw [fiberPoint, s.direction_of_mem_left hi]
    field_simp [s.left_card_pos.ne']
    ring
  constructor
  · intro h
    rw [h, mul_zero] at heq
    linarith
  · intro h
    apply mul_left_cancel₀ s.left_card_pos.ne'
    rw [heq, h, sub_self, mul_zero]

theorem fiberPoint_eq_zero_iff_of_mem_right {i : ι} (hi : i ∈ s.right)
    (z : ι → ℝ) (t : ℝ) :
    s.fiberPoint z t i = 0 ↔ t = -(s.right.card : ℝ) * z i := by
  have heq : (s.right.card : ℝ) * s.fiberPoint z t i = s.right.card * z i + t := by
    rw [fiberPoint, s.direction_of_mem_right hi]
    field_simp [s.right_card_pos.ne']
  constructor
  · intro h
    rw [h, mul_zero] at heq
    linarith
  · intro h
    apply mul_left_cancel₀ s.right_card_pos.ne'
    rw [heq, h, mul_zero]
    ring

theorem eq_lower_iff_coordinate_zero {z : ι → ℝ} {t : ℝ}
    (ht : t ∈ Icc (s.lower z) (s.upper z)) :
    t = s.lower z ↔ ∃ i ∈ s.right, s.fiberPoint z t i = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' s.right_nonempty
      (fun i => -(s.right.card : ℝ) * z i)
    exact ⟨i, hi, (s.fiberPoint_eq_zero_iff_of_mem_right hi z t).mpr (h.trans heq)⟩
  · rintro ⟨i, hi, hzero⟩
    have heq := (s.fiberPoint_eq_zero_iff_of_mem_right hi z t).mp hzero
    apply le_antisymm _ ht.1
    rw [heq]
    exact Finset.le_sup' (fun j => -(s.right.card : ℝ) * z j) hi

theorem eq_upper_iff_coordinate_zero {z : ι → ℝ} {t : ℝ}
    (ht : t ∈ Icc (s.lower z) (s.upper z)) :
    t = s.upper z ↔ ∃ i ∈ s.left, s.fiberPoint z t i = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' s.left_nonempty
      (fun i => (s.left.card : ℝ) * z i)
    exact ⟨i, hi, (s.fiberPoint_eq_zero_iff_of_mem_left hi z t).mpr (h.trans heq)⟩
  · rintro ⟨i, hi, hzero⟩
    have heq := (s.fiberPoint_eq_zero_iff_of_mem_left hi z t).mp hzero
    apply le_antisymm ht.2
    rw [heq]
    exact Finset.inf'_le (fun j => (s.left.card : ℝ) * z j) hi

def prism : Set (s.horizontal × ℝ) :=
  {p | p.2 ∈ Icc (s.lower p.1) (s.upper p.1)}

def simplexPrismHomeomorph : standardBarycentricSimplex ι ≃ₜ s.prism where
  toFun x := ⟨s.prismCoordinates ⟨x.val, x.2.2⟩,
    (s.prismCoordinates_simplex_iff ⟨x.val, x.2.2⟩).mp x.2⟩
  invFun p := ⟨s.fiberPoint p.1.1 p.1.2,
    (s.fiberPoint_mem_simplex_iff p.1.1 p.1.2).mpr ⟨p.1.1.2.1, p.2⟩⟩
  left_inv x := Subtype.ext (s.fiberPoint_project_height x)
  right_inv p := Subtype.ext (Prod.ext (Subtype.ext (s.project_fiberPoint p.1.1.2 p.1.2))
    (s.height_fiberPoint p.1.1.2 p.1.2))
  continuous_toFun := (s.prismCoordinates.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _
  continuous_invFun := (continuous_pi (fun i =>
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val.fst)).add
      (continuous_subtype_val.snd.mul continuous_const))).subtype_mk _

end SimplexSplit

end

end DifferentialGeometry.Topology.Engulfing
