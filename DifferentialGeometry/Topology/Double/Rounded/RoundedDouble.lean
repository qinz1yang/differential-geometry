import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Order.Compact

namespace DifferentialGeometry.Topology

set_option linter.unusedSectionVars false

open Set _root_.Topology unitInterval
open scoped ContinuousMap

namespace RoundedDouble

variable {X : Type*} [TopologicalSpace X]

def base (g : X → ℝ) : Set X := {x | g x ≤ 0}

def filling (g : X → ℝ) : Set (X × ℝ) := {p | g p.1 + p.2 ^ 2 ≤ 0}

def boundary (g : X → ℝ) : Set (X × ℝ) := {p | g p.1 + p.2 ^ 2 = 0}

theorem fst_mem_base {g : X → ℝ} {p : X × ℝ} (hp : p ∈ filling g) :
    p.1 ∈ base g := by
  have := sq_nonneg p.2
  dsimp [filling] at hp
  dsimp [base]
  linarith

theorem boundary_subset_filling (g : X → ℝ) : boundary g ⊆ filling g :=
  fun _ hp => le_of_eq hp

theorem scale_mem_filling {g : X → ℝ} (p : filling g) (s : I) :
    (p.1.1, (s : ℝ) * p.1.2) ∈ filling g := by
  have hs : (s : ℝ) ^ 2 ≤ 1 := by nlinarith [s.2.1, s.2.2]
  have hmul := mul_le_mul_of_nonneg_right hs (sq_nonneg p.1.2)
  have hp := p.2
  dsimp [filling] at hp ⊢
  rw [mul_pow]
  nlinarith

def homotopyEquivBase (g : X → ℝ) : filling g ≃ₕ base g where
  toFun := ⟨fun p => ⟨p.1.1, fst_mem_base p.2⟩, by fun_prop⟩
  invFun := ⟨fun x => ⟨(x.1, 0), by simpa only [filling, mem_ofPred, zero_pow (by decide : 2 ≠ 0),
    add_zero] using (show g x ≤ 0 from x.2)⟩, by fun_prop⟩
  left_inv := by
    refine ⟨{
      toFun := fun p => ⟨(p.2.1.1, (p.1 : ℝ) * p.2.1.2), scale_mem_filling p.2 p.1⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x => by apply Subtype.ext; simp
      map_one_left := fun x => by apply Subtype.ext; simp }⟩
  right_inv := by
    have h : (⟨fun p : filling g => ⟨p.1.1, fst_mem_base p.2⟩, by fun_prop⟩ :
        C(filling g, base g)).comp
        ⟨fun x => ⟨(x.1, 0), by simpa only [filling, mem_ofPred, zero_pow (by decide : 2 ≠ 0),
          add_zero] using (show g x ≤ 0 from x.2)⟩, by fun_prop⟩ =
        ContinuousMap.id (base g) := rfl
    rw [h]

noncomputable def upper (g : X → ℝ) (x : base g) : boundary g :=
  ⟨(x.1, Real.sqrt (-g x)), by
    dsimp [boundary]
    rw [Real.sq_sqrt (neg_nonneg.mpr x.2)]
    ring⟩

noncomputable def lower (g : X → ℝ) (x : base g) : boundary g :=
  ⟨(x.1, -Real.sqrt (-g x)), by
    dsimp [boundary]
    rw [neg_sq, Real.sq_sqrt (neg_nonneg.mpr x.2)]
    ring⟩

theorem continuous_upper {g : X → ℝ} (hg : Continuous g) : Continuous (upper g) := by
  unfold upper
  exact (continuous_subtype_val.prodMk
    (Real.continuous_sqrt.comp (hg.comp continuous_subtype_val).neg)).subtype_mk _

theorem continuous_lower {g : X → ℝ} (hg : Continuous g) : Continuous (lower g) := by
  unfold lower
  exact (continuous_subtype_val.prodMk
    (Real.continuous_sqrt.comp (hg.comp continuous_subtype_val).neg).neg).subtype_mk _

theorem upper_injective (g : X → ℝ) : Function.Injective (upper g) := by
  intro x y h
  exact Subtype.ext (congrArg (fun p : boundary g => p.1.1) h)

theorem lower_injective (g : X → ℝ) : Function.Injective (lower g) := by
  intro x y h
  exact Subtype.ext (congrArg (fun p : boundary g => p.1.1) h)

theorem mem_range_upper {g : X → ℝ} (p : boundary g) :
    p ∈ range (upper g) ↔ 0 ≤ p.1.2 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact Real.sqrt_nonneg _
  · intro hp
    refine ⟨⟨p.1.1, fst_mem_base (boundary_subset_filling g p.2)⟩, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change Real.sqrt (-g p.1.1) = p.1.2
    have heq : -g p.1.1 = p.1.2 ^ 2 := by have := p.2; dsimp [boundary] at this; linarith
    rw [heq, Real.sqrt_sq hp]

theorem mem_range_lower {g : X → ℝ} (p : boundary g) :
    p ∈ range (lower g) ↔ p.1.2 ≤ 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  · intro hp
    refine ⟨⟨p.1.1, fst_mem_base (boundary_subset_filling g p.2)⟩, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change -Real.sqrt (-g p.1.1) = p.1.2
    have heq : -g p.1.1 = (-p.1.2) ^ 2 := by
      have := p.2
      dsimp [boundary] at this
      nlinarith
    rw [heq, Real.sqrt_sq (neg_nonneg.mpr hp), neg_neg]

theorem range_upper_union_range_lower (g : X → ℝ) :
    range (upper g) ∪ range (lower g) = univ := by
  ext p
  simp only [mem_union, mem_range_upper, mem_range_lower, mem_univ, iff_true]
  exact le_total _ _

theorem range_upper_inter_range_lower (g : X → ℝ) :
    range (upper g) ∩ range (lower g) = {p : boundary g | p.1.2 = 0} := by
  ext p
  simp only [mem_inter_iff, mem_range_upper, mem_range_lower, mem_ofPred]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

theorem upper_eq_lower_iff {g : X → ℝ} (x y : base g) :
    upper g x = lower g y ↔ x = y ∧ g x = 0 := by
  constructor
  · intro h
    have hxy : x = y := Subtype.ext (congrArg (fun p : boundary g => p.1.1) h)
    subst y
    refine ⟨rfl, ?_⟩
    have ht := congrArg (fun p : boundary g => p.1.2) h
    change Real.sqrt (-g x) = -Real.sqrt (-g x) at ht
    have hz : Real.sqrt (-g x) = 0 := by linarith
    have hs := Real.sq_sqrt (neg_nonneg.mpr x.2)
    rw [hz] at hs
    simpa using hs
  · rintro ⟨rfl, hx⟩
    apply Subtype.ext
    simp [upper, lower, hx]

theorem isClosedEmbedding_upper {g : X → ℝ} (hg : Continuous g) :
    IsClosedEmbedding (upper g) := by
  let r : boundary g → base g := fun p =>
    ⟨p.1.1, fst_mem_base (boundary_subset_filling g p.2)⟩
  have hr : Function.LeftInverse r (upper g) := fun _ => rfl
  refine ⟨hr.isEmbedding (by fun_prop) (continuous_upper hg), ?_⟩
  have heq : range (upper g) = {p : boundary g | 0 ≤ p.1.2} := Set.ext mem_range_upper
  rw [heq]
  exact isClosed_le continuous_const continuous_subtype_val.snd

theorem isClosedEmbedding_lower {g : X → ℝ} (hg : Continuous g) :
    IsClosedEmbedding (lower g) := by
  let r : boundary g → base g := fun p =>
    ⟨p.1.1, fst_mem_base (boundary_subset_filling g p.2)⟩
  have hr : Function.LeftInverse r (lower g) := fun _ => rfl
  refine ⟨hr.isEmbedding (by fun_prop) (continuous_lower hg), ?_⟩
  have heq : range (lower g) = {p : boundary g | p.1.2 ≤ 0} := Set.ext mem_range_lower
  rw [heq]
  exact isClosed_le continuous_subtype_val.snd continuous_const

theorem isCompact_filling [CompactSpace X] {g : X → ℝ} (hg : Continuous g) :
    IsCompact (filling g) := by
  obtain ⟨b, hb⟩ := (isCompact_univ.image hg).bddBelow
  have hbound (x : X) : b ≤ g x := hb ⟨x, mem_univ _, rfl⟩
  have hclosed : IsClosed (filling g) :=
    isClosed_le ((hg.comp continuous_fst).add (continuous_snd.pow 2)) continuous_const
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-(|b| + 1)) (|b| + 1)))).of_isClosed_subset
    hclosed
  intro p hp
  refine ⟨mem_univ _, ?_, ?_⟩ <;>
    have hp' : g p.1 + p.2 ^ 2 ≤ 0 := hp
  · nlinarith [hbound p.1, neg_le_abs b, abs_nonneg b,
      sq_nonneg (p.2 + (|b| + 1)), sq_nonneg (|b|)]
  · nlinarith [hbound p.1, neg_le_abs b, abs_nonneg b,
      sq_nonneg (p.2 - (|b| + 1)), sq_nonneg (|b|)]

theorem isCompact_boundary [CompactSpace X] {g : X → ℝ} (hg : Continuous g) :
    IsCompact (boundary g) := by
  have hclosed : IsClosed (boundary g) :=
    isClosed_eq ((hg.comp continuous_fst).add (continuous_snd.pow 2)) continuous_const
  exact (isCompact_filling hg).of_isClosed_subset hclosed (boundary_subset_filling g)

end RoundedDouble

end DifferentialGeometry.Topology
