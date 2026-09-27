/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def spliceSquare : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

theorem mem_spliceSquare {p : ℝ × ℝ} :
    p ∈ spliceSquare ↔ (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (-1 ≤ p.2 ∧ p.2 ≤ 1) := by
  simp only [spliceSquare, Set.mem_prod, Set.mem_Icc]

def spliceCylinder : Set ((ℝ × ℝ) × ℝ) := spliceSquare ×ˢ Icc (0 : ℝ) 1

theorem mem_spliceCylinder {p : (ℝ × ℝ) × ℝ} :
    p ∈ spliceCylinder ↔ p.1 ∈ spliceSquare ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

theorem isHPolytope_spliceSquare : IsHPolytope spliceSquare :=
  isHPolytope_Icc.prod isHPolytope_Icc

theorem isHPolytope_spliceCylinder : IsHPolytope spliceCylinder :=
  isHPolytope_spliceSquare.prod isHPolytope_Icc

theorem interior_spliceSquare_nonempty : (interior spliceSquare).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  rw [spliceSquare]
  simp only [interior_prod_eq, interior_Icc, Set.mem_prod, Set.mem_Ioo]
  norm_num

theorem interior_spliceCylinder_nonempty : (interior spliceCylinder).Nonempty := by
  refine ⟨((0, 0), 1 / 2), ?_⟩
  rw [spliceCylinder, spliceSquare]
  simp only [interior_prod_eq, interior_Icc, Set.mem_prod, Set.mem_Ioo]
  norm_num

theorem isPLBall_spliceSquare : IsPLBall 2 spliceSquare := by
  have h := isHPolytope_spliceSquare.isPLBall interior_spliceSquare_nonempty
  rwa [show Module.finrank ℝ (ℝ × ℝ) = 2 by simp] at h

theorem isPLBall_spliceCylinder : IsPLBall 3 spliceCylinder := by
  have h := isHPolytope_spliceCylinder.isPLBall interior_spliceCylinder_nonempty
  rwa [show Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 by simp] at h

def spliceSquareBoundary : Set (ℝ × ℝ) :=
  {p ∈ spliceSquare | p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -1 ∨ p.2 = 1}

theorem mem_spliceSquareBoundary {p : ℝ × ℝ} :
    p ∈ spliceSquareBoundary ↔
      p ∈ spliceSquare ∧ (p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -1 ∨ p.2 = 1) := Iff.rfl

theorem spliceSquareBoundary_eq_frontier : spliceSquareBoundary = frontier spliceSquare := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  rw [spliceSquare, frontier_prod_eq, closure_Icc, frontier_Icc hle]
  ext p
  simp only [spliceSquareBoundary, spliceSquare, Set.mem_prod, Set.mem_Icc,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h⟩
    rcases h with h | h | h | h
    · exact Or.inr ⟨Or.inl h, h3, h4⟩
    · exact Or.inr ⟨Or.inr h, h3, h4⟩
    · exact Or.inl ⟨⟨h1, h2⟩, Or.inl h⟩
    · exact Or.inl ⟨⟨h1, h2⟩, Or.inr h⟩
  · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨h, h3, h4⟩)
    · rcases h with h | h
      · exact ⟨⟨⟨h1, h2⟩, by norm_num [h], by norm_num [h]⟩, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨⟨⟨h1, h2⟩, by norm_num [h], by norm_num [h]⟩, Or.inr (Or.inr (Or.inr h))⟩
    · rcases h with h | h
      · exact ⟨⟨⟨by norm_num [h], by norm_num [h]⟩, h3, h4⟩, Or.inl h⟩
      · exact ⟨⟨⟨by norm_num [h], by norm_num [h]⟩, h3, h4⟩, Or.inr (Or.inl h)⟩

def SpliceRel (p q : (ℝ × ℝ) × ℝ) : Prop :=
  p = q ∨ (p.2 = 0 ∧ q.2 = 1 ∧ q.1 = p.1.swap) ∨ (p.2 = 1 ∧ q.2 = 0 ∧ p.1 = q.1.swap)

theorem spliceRel_equivalence : Equivalence SpliceRel := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
  · rintro p q (rfl | ⟨h0, h1, hq⟩ | ⟨h1, h0, hp⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨h1, h0, hq⟩)
    · exact Or.inr (Or.inl ⟨h0, h1, hp⟩)
  · rintro p q r (rfl | ⟨hp0, hq1, hq⟩ | ⟨hp1, hq0, hp⟩) hqr
    · exact hqr
    · rcases hqr with rfl | ⟨hq0, -, -⟩ | ⟨-, hr0, hq'⟩
      · exact Or.inr (Or.inl ⟨hp0, hq1, hq⟩)
      · exact absurd (hq0.symm.trans hq1) (by norm_num)
      · refine Or.inl (Prod.ext ?_ (hp0.trans hr0.symm))
        have hswap : p.1.swap = r.1.swap := hq.symm.trans hq'
        have := congrArg Prod.swap hswap
        simpa using this
    · rcases hqr with rfl | ⟨-, hr1, hr⟩ | ⟨hq1, -, -⟩
      · exact Or.inr (Or.inr ⟨hp1, hq0, hp⟩)
      · refine Or.inl (Prod.ext ?_ (hp1.trans hr1.symm))
        have hswap : p.1 = r.1 := hp.trans hr.symm
        exact hswap
      · exact absurd (hq0.symm.trans hq1) (by norm_num)

def spliceSetoid : Setoid ((ℝ × ℝ) × ℝ) := ⟨SpliceRel, spliceRel_equivalence⟩

def spliceMk (p : (ℝ × ℝ) × ℝ) : Quotient spliceSetoid := Quotient.mk spliceSetoid p

theorem spliceMk_eq_iff {p q : (ℝ × ℝ) × ℝ} : spliceMk p = spliceMk q ↔ SpliceRel p q := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem eq_of_spliceRel_of_snd_ne {p q : (ℝ × ℝ) × ℝ} (h0 : p.2 ≠ 0) (h1 : p.2 ≠ 1)
    (h : SpliceRel p q) : p = q := by
  rcases h with h | ⟨hp0, -, -⟩ | ⟨hp1, -, -⟩
  · exact h
  · exact absurd hp0 h0
  · exact absurd hp1 h1

def crossingArcX : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 = 0}

def crossingArcY : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.2 = 0}

def spliceArcPos : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 - p.2 = 1}

def spliceArcNeg : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 - p.2 = -1}

def crossingSheetX : Set ((ℝ × ℝ) × ℝ) := crossingArcX ×ˢ Icc (0 : ℝ) 1

def crossingSheetY : Set ((ℝ × ℝ) × ℝ) := crossingArcY ×ˢ Icc (0 : ℝ) 1

def crossingFigure : Set ((ℝ × ℝ) × ℝ) := (crossingArcX ∪ crossingArcY) ×ˢ Icc (0 : ℝ) 1

def spliceSheetPos : Set ((ℝ × ℝ) × ℝ) := spliceArcPos ×ˢ Icc (0 : ℝ) 1

def spliceSheetNeg : Set ((ℝ × ℝ) × ℝ) := spliceArcNeg ×ˢ Icc (0 : ℝ) 1

def spliceFigure : Set ((ℝ × ℝ) × ℝ) := (spliceArcPos ∪ spliceArcNeg) ×ˢ Icc (0 : ℝ) 1

def spliceCore : Set ((ℝ × ℝ) × ℝ) := ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1

def spliceEnds : Set (ℝ × ℝ) := {(0, 1), (0, -1), (1, 0), (-1, 0)}

theorem mem_crossingSheetX {p : (ℝ × ℝ) × ℝ} :
    p ∈ crossingSheetX ↔ p.1 ∈ crossingArcX ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

theorem mem_crossingSheetY {p : (ℝ × ℝ) × ℝ} :
    p ∈ crossingSheetY ↔ p.1 ∈ crossingArcY ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

theorem mem_spliceSheetPos {p : (ℝ × ℝ) × ℝ} :
    p ∈ spliceSheetPos ↔ p.1 ∈ spliceArcPos ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

theorem mem_spliceSheetNeg {p : (ℝ × ℝ) × ℝ} :
    p ∈ spliceSheetNeg ↔ p.1 ∈ spliceArcNeg ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

theorem crossingArcX_eq : crossingArcX = ({0} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1 := by
  ext p
  simp only [crossingArcX, mem_spliceSquare, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, h⟩
    exact ⟨h, h2⟩
  · rintro ⟨h, h2⟩
    exact ⟨⟨by norm_num [h], h2⟩, h⟩

theorem crossingArcY_eq : crossingArcY = Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ) := by
  ext p
  simp only [crossingArcY, mem_spliceSquare, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h⟩
    exact ⟨h1, h⟩
  · rintro ⟨h1, h⟩
    exact ⟨⟨h1, by norm_num [h], by norm_num [h]⟩, h⟩

theorem spliceArcPos_eq : spliceArcPos = (fun t : ℝ => (t, t - 1)) '' Icc (0 : ℝ) 1 := by
  ext p
  simp only [spliceArcPos, mem_spliceSquare, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h⟩
    exact ⟨p.1, ⟨by linarith, h2⟩, Prod.ext rfl (by simp; linarith)⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨⟨⟨by linarith, ht1⟩, by simp; linarith, by simp; linarith⟩, by simp⟩

theorem spliceArcNeg_eq : spliceArcNeg = (fun t : ℝ => (t - 1, t)) '' Icc (0 : ℝ) 1 := by
  ext p
  simp only [spliceArcNeg, mem_spliceSquare, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h⟩
    exact ⟨p.2, ⟨by linarith, h4⟩, Prod.ext (by simp; linarith) rfl⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨⟨⟨by simp; linarith, by simp; linarith⟩, by linarith, ht1⟩, by simp⟩

theorem crossingArcX_inter_crossingArcY :
    crossingArcX ∩ crossingArcY = {((0 : ℝ), (0 : ℝ))} := by
  ext p
  simp only [crossingArcX, crossingArcY, Set.mem_inter_iff, Set.mem_sep_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨-, h1⟩, -, h2⟩
    exact Prod.ext h1 h2
  · rintro rfl
    refine ⟨⟨?_, rfl⟩, ⟨?_, rfl⟩⟩ <;> simp only [mem_spliceSquare] <;> norm_num

theorem crossingSheetX_inter_crossingSheetY :
    crossingSheetX ∩ crossingSheetY = spliceCore := by
  rw [crossingSheetX, crossingSheetY, Set.prod_inter_prod, Set.inter_self,
    crossingArcX_inter_crossingArcY, spliceCore]

theorem mem_crossingSheet_inter {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (((0 : ℝ), (0 : ℝ)), t) ∈ crossingSheetX ∩ crossingSheetY := by
  rw [crossingSheetX_inter_crossingSheetY]
  exact ⟨rfl, ht⟩

theorem spliceCore_nonempty : spliceCore.Nonempty :=
  ⟨(((0 : ℝ), (0 : ℝ)), 0), rfl, by norm_num⟩

theorem disjoint_spliceArcPos_spliceArcNeg : Disjoint spliceArcPos spliceArcNeg := by
  rw [Set.disjoint_left]
  rintro p ⟨-, hp⟩ ⟨-, hq⟩
  rw [hp] at hq
  norm_num at hq

theorem disjoint_spliceSheetPos_spliceSheetNeg : Disjoint spliceSheetPos spliceSheetNeg := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact Set.disjoint_left.mp disjoint_spliceArcPos_spliceArcNeg
    (mem_spliceSheetPos.mp hp).1 (mem_spliceSheetNeg.mp hq).1

theorem swap_mem_spliceSquare {p : ℝ × ℝ} (hp : p ∈ spliceSquare) : p.swap ∈ spliceSquare := by
  rw [mem_spliceSquare] at hp ⊢
  exact ⟨hp.2, hp.1⟩

theorem swap_mem_crossingArcY_of_mem_crossingArcX {p : ℝ × ℝ} (hp : p ∈ crossingArcX) :
    p.swap ∈ crossingArcY :=
  ⟨swap_mem_spliceSquare hp.1, hp.2⟩

theorem swap_mem_crossingArcX_of_mem_crossingArcY {p : ℝ × ℝ} (hp : p ∈ crossingArcY) :
    p.swap ∈ crossingArcX :=
  ⟨swap_mem_spliceSquare hp.1, hp.2⟩

theorem swap_mem_spliceArcNeg_of_mem_spliceArcPos {p : ℝ × ℝ} (hp : p ∈ spliceArcPos) :
    p.swap ∈ spliceArcNeg :=
  ⟨swap_mem_spliceSquare hp.1, by
    have h := hp.2
    change p.2 - p.1 = -1
    linarith⟩

theorem swap_mem_spliceArcPos_of_mem_spliceArcNeg {p : ℝ × ℝ} (hp : p ∈ spliceArcNeg) :
    p.swap ∈ spliceArcPos :=
  ⟨swap_mem_spliceSquare hp.1, by
    have h := hp.2
    change p.2 - p.1 = 1
    linarith⟩

theorem swap_image_crossingArcX : Prod.swap '' crossingArcX = crossingArcY := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact swap_mem_crossingArcY_of_mem_crossingArcX hq
  · intro p hp
    exact ⟨p.swap, swap_mem_crossingArcX_of_mem_crossingArcY hp, Prod.swap_swap p⟩

theorem swap_image_spliceArcPos : Prod.swap '' spliceArcPos = spliceArcNeg := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact swap_mem_spliceArcNeg_of_mem_spliceArcPos hq
  · intro p hp
    exact ⟨p.swap, swap_mem_spliceArcPos_of_mem_spliceArcNeg hp, Prod.swap_swap p⟩

theorem crossingArcX_ne_crossingArcY : crossingArcX ≠ crossingArcY := by
  intro h
  have hmem : ((0 : ℝ), (1 : ℝ)) ∈ crossingArcX := ⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩
  rw [h] at hmem
  exact absurd hmem.2 (by norm_num)

theorem spliceArcPos_ne_spliceArcNeg : spliceArcPos ≠ spliceArcNeg := by
  intro h
  exact Set.disjoint_left.mp disjoint_spliceArcPos_spliceArcNeg
    (show ((1 : ℝ), (0 : ℝ)) ∈ spliceArcPos from
      ⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩)
    (h ▸ (show ((1 : ℝ), (0 : ℝ)) ∈ spliceArcPos from
      ⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩))

theorem spliceMk_crossing_bottom_eq_top {a : ℝ × ℝ} (ha : a ∈ crossingArcX) :
    spliceMk (a, 0) = spliceMk (a.swap, 1) ∧ a.swap ∈ crossingArcY :=
  ⟨spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
    swap_mem_crossingArcY_of_mem_crossingArcX ha⟩

theorem spliceMk_splice_bottom_eq_top {a : ℝ × ℝ} (ha : a ∈ spliceArcPos) :
    spliceMk (a, 0) = spliceMk (a.swap, 1) ∧ a.swap ∈ spliceArcNeg :=
  ⟨spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
    swap_mem_spliceArcNeg_of_mem_spliceArcPos ha⟩

theorem snd_eq_ends_of_spliceMk_eq {p q : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceSheetPos)
    (hq : q ∈ spliceSheetNeg) (h : spliceMk p = spliceMk q) :
    (p.2 = 0 ∧ q.2 = 1) ∨ (p.2 = 1 ∧ q.2 = 0) := by
  rcases spliceMk_eq_iff.mp h with rfl | ⟨h0, h1, -⟩ | ⟨h1, h0, -⟩
  · exact absurd hq (Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg hp)
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h1, h0⟩

theorem image_spliceSheetPos_inter_image_spliceSheetNeg :
    spliceMk '' spliceSheetPos ∩ spliceMk '' spliceSheetNeg
      = spliceMk '' (spliceArcPos ×ˢ ({0, 1} : Set ℝ)) := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨p, hp, rfl⟩, q, hq, hqz⟩
    have hrel : SpliceRel p q := spliceMk_eq_iff.mp hqz.symm
    rcases hrel with rfl | ⟨h0, -, -⟩ | ⟨h1, -, -⟩
    · exact absurd hq (Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg hp)
    · exact ⟨p, ⟨(mem_spliceSheetPos.mp hp).1, Or.inl h0⟩, rfl⟩
    · exact ⟨p, ⟨(mem_spliceSheetPos.mp hp).1, Or.inr h1⟩, rfl⟩
  · rintro z ⟨p, ⟨hpa, hp2⟩, rfl⟩
    have hcases : p.2 = 0 ∨ p.2 = 1 := hp2
    have hp2' : p.2 ∈ Icc (0 : ℝ) 1 := by
      rcases hcases with h | h <;> rw [Set.mem_Icc, h] <;> norm_num
    refine ⟨⟨p, mem_spliceSheetPos.mpr ⟨hpa, hp2'⟩, rfl⟩, ?_⟩
    rcases hcases with h | h
    · refine ⟨(p.1.swap, 1), mem_spliceSheetNeg.mpr
        ⟨swap_mem_spliceArcNeg_of_mem_spliceArcPos hpa, by rw [Set.mem_Icc]; norm_num⟩, ?_⟩
      exact (spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨h, rfl, rfl⟩))).symm
    · refine ⟨(p.1.swap, 0), mem_spliceSheetNeg.mpr
        ⟨swap_mem_spliceArcNeg_of_mem_spliceArcPos hpa, by rw [Set.mem_Icc]; norm_num⟩, ?_⟩
      refine (spliceMk_eq_iff.mpr (Or.inr (Or.inr ⟨h, rfl, ?_⟩))).symm
      exact (Prod.swap_swap p.1).symm

theorem crossingArcX_inter_spliceSquareBoundary :
    crossingArcX ∩ spliceSquareBoundary = {((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨-, hx⟩, -, hb⟩
    rcases hb with h | h | h | h
    · rw [hx] at h; norm_num at h
    · rw [hx] at h; norm_num at h
    · exact Or.inr (Prod.ext hx h)
    · exact Or.inl (Prod.ext hx h)
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

theorem crossingArcY_inter_spliceSquareBoundary :
    crossingArcY ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((-1 : ℝ), (0 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨-, hy⟩, -, hb⟩
    rcases hb with h | h | h | h
    · exact Or.inr (Prod.ext h hy)
    · exact Or.inl (Prod.ext h hy)
    · rw [hy] at h; norm_num at h
    · rw [hy] at h; norm_num at h
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩

theorem spliceArcPos_inter_spliceSquareBoundary :
    spliceArcPos ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨hsq, hd⟩, -, hb⟩
    rw [mem_spliceSquare] at hsq
    rcases hb with h | h | h | h
    · exfalso; rw [h] at hd; linarith [hsq.2.1]
    · exact Or.inl (Prod.ext h (by linarith [hd, h]))
    · exact Or.inr (Prod.ext (by linarith [hd, h]) h)
    · exfalso; rw [h] at hd; linarith [hsq.1.2]
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

theorem spliceArcNeg_inter_spliceSquareBoundary :
    spliceArcNeg ∩ spliceSquareBoundary = {((-1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨hsq, hd⟩, -, hb⟩
    rw [mem_spliceSquare] at hsq
    rcases hb with h | h | h | h
    · exact Or.inl (Prod.ext h (by linarith [hd, h]))
    · exfalso; rw [h] at hd; linarith [hsq.2.2]
    · exfalso; rw [h] at hd; linarith [hsq.1.1]
    · exact Or.inr (Prod.ext (by linarith [hd, h]) h)
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩

theorem crossingArc_inter_spliceSquareBoundary :
    (crossingArcX ∪ crossingArcY) ∩ spliceSquareBoundary = spliceEnds := by
  rw [Set.union_inter_distrib_right, crossingArcX_inter_spliceSquareBoundary,
    crossingArcY_inter_spliceSquareBoundary]
  ext p
  simp only [spliceEnds, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem spliceArc_inter_spliceSquareBoundary :
    (spliceArcPos ∪ spliceArcNeg) ∩ spliceSquareBoundary = spliceEnds := by
  rw [Set.union_inter_distrib_right, spliceArcPos_inter_spliceSquareBoundary,
    spliceArcNeg_inter_spliceSquareBoundary]
  ext p
  simp only [spliceEnds, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem crossingFigure_inter_lateral :
    crossingFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) = spliceEnds ×ˢ Icc (0 : ℝ) 1 := by
  rw [crossingFigure, Set.prod_inter_prod, Set.inter_self,
    crossingArc_inter_spliceSquareBoundary]

theorem spliceFigure_inter_lateral :
    spliceFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) = spliceEnds ×ˢ Icc (0 : ℝ) 1 := by
  rw [spliceFigure, Set.prod_inter_prod, Set.inter_self, spliceArc_inter_spliceSquareBoundary]

theorem crossingFigure_inter_lateral_eq_spliceFigure_inter_lateral :
    crossingFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      = spliceFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
  rw [crossingFigure_inter_lateral, spliceFigure_inter_lateral]

theorem swap_ne_self_of_mem_spliceEnds {a : ℝ × ℝ} (ha : a ∈ spliceEnds) : a.swap ≠ a := by
  simp only [spliceEnds, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num

theorem spliceMk_core_zero_eq_one :
    spliceMk (((0 : ℝ), (0 : ℝ)), 0) = spliceMk (((0 : ℝ), (0 : ℝ)), 1) :=
  spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

theorem spliceMk_end_zero_ne_one {a : ℝ × ℝ} (ha : a ∈ spliceEnds) :
    spliceMk (a, (0 : ℝ)) ≠ spliceMk (a, (1 : ℝ)) := by
  intro h
  rcases spliceMk_eq_iff.mp h with h' | ⟨-, -, h'⟩ | ⟨h', -, -⟩
  · exact absurd (congrArg Prod.snd h') (by norm_num)
  · exact swap_ne_self_of_mem_spliceEnds ha h'.symm
  · exact absurd h' (by norm_num)

theorem spliceMk_end_bottom_eq_swap_top (a : ℝ × ℝ) :
    spliceMk (a, (0 : ℝ)) = spliceMk (a.swap, (1 : ℝ)) :=
  spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

theorem spliceMk_upper_ne_lower {a b : ℝ × ℝ} {s t : ℝ}
    (ha : a ∈ ({((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)))
    (hb : b ∈ ({((0 : ℝ), (-1 : ℝ)), ((-1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))) :
    spliceMk (a, s) ≠ spliceMk (b, t) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  intro h
  rcases spliceMk_eq_iff.mp h with h' | ⟨-, -, h'⟩ | ⟨-, -, h'⟩
  · have h'' : a = b := congrArg Prod.fst h'
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Prod.mk.injEq] at h'' <;> norm_num at h''
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h' <;> norm_num at h'
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h' <;> norm_num at h'

theorem spliceRel_iff_of_isCylindricalDiagram {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (ℝ × ℝ) × ℝ → F} {S : Set F}
    (hf : IsCylindricalDiagram f spliceSquare S)
    (hend : ∀ a ∈ spliceSquare, f (a, 0) = f (a.swap, 1))
    {p q : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) (hq : q ∈ spliceCylinder) :
    f p = f q ↔ SpliceRel p q := by
  have hp1 : p.1 ∈ spliceSquare := (mem_spliceCylinder.mp hp).1
  have hq1 : q.1 ∈ spliceSquare := (mem_spliceCylinder.mp hq).1
  have hpc : p ∈ spliceSquare ×ˢ Icc (0 : ℝ) 1 := hp
  have hqc : q ∈ spliceSquare ×ˢ Icc (0 : ℝ) 1 := hq
  constructor
  · intro h
    rcases hf.eq_or_endpoints p hpc q hqc h with heq | ⟨h0, h1⟩ | ⟨h1, h0⟩
    · exact Or.inl heq
    · refine Or.inr (Or.inl ⟨h0, h1, ?_⟩)
      have hpa : p = (p.1, (0 : ℝ)) := Prod.ext rfl h0
      have hqa : q = (q.1, (1 : ℝ)) := Prod.ext rfl h1
      have e1 : f (p.1.swap, (1 : ℝ)) = f p := by rw [← hend p.1 hp1, ← hpa]
      have e2 : f q = f (q.1, (1 : ℝ)) := by rw [← hqa]
      exact (hf.eq_of_eq_top (swap_mem_spliceSquare hp1) hq1 (e1.trans (h.trans e2))).symm
    · refine Or.inr (Or.inr ⟨h1, h0, ?_⟩)
      have hpa : p = (p.1, (1 : ℝ)) := Prod.ext rfl h1
      have hqa : q = (q.1, (0 : ℝ)) := Prod.ext rfl h0
      have e1 : f (q.1.swap, (1 : ℝ)) = f q := by rw [← hend q.1 hq1, ← hqa]
      have e2 : f p = f (p.1, (1 : ℝ)) := by rw [← hpa]
      exact hf.eq_of_eq_top hp1 (swap_mem_spliceSquare hq1) (e2.symm.trans (h.trans e1.symm))
  · rintro (rfl | ⟨h0, h1, hs⟩ | ⟨h1, h0, hs⟩)
    · rfl
    · have hpa : p = (p.1, (0 : ℝ)) := Prod.ext rfl h0
      have hqa : q = (q.1, (1 : ℝ)) := Prod.ext rfl h1
      have e1 : f p = f (p.1, (0 : ℝ)) := by rw [← hpa]
      have e2 : f q = f (q.1, (1 : ℝ)) := by rw [← hqa]
      rw [e1, e2, hs, hend p.1 hp1]
    · have hpa : p = (p.1, (1 : ℝ)) := Prod.ext rfl h1
      have hqa : q = (q.1, (0 : ℝ)) := Prod.ext rfl h0
      have e1 : f p = f (p.1, (1 : ℝ)) := by rw [← hpa]
      have e2 : f q = f (q.1, (0 : ℝ)) := by rw [← hqa]
      rw [e1, e2, hs, hend q.1 hq1]

end DifferentialGeometry.Topology.PiecewiseLinear
