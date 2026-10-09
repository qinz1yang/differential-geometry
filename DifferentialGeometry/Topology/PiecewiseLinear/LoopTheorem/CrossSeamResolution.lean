/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isHPolytope_singleton_real (a : ℝ) : IsHPolytope ({a} : Set ℝ) := by
  rw [← Set.Icc_self a]
  exact isHPolytope_Icc

def crossRayPosX : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)

def crossRayNegX : Set (ℝ × ℝ) := Icc (-1 : ℝ) 0 ×ˢ ({0} : Set ℝ)

def crossRayPosY : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1

def crossRayNegY : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc (-1 : ℝ) 0

theorem mem_crossRayPosX {p : ℝ × ℝ} :
    p ∈ crossRayPosX ↔ (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ p.2 = 0 := by
  simp only [crossRayPosX, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

theorem mem_crossRayNegX {p : ℝ × ℝ} :
    p ∈ crossRayNegX ↔ (-1 ≤ p.1 ∧ p.1 ≤ 0) ∧ p.2 = 0 := by
  simp only [crossRayNegX, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

theorem mem_crossRayPosY {p : ℝ × ℝ} :
    p ∈ crossRayPosY ↔ p.1 = 0 ∧ (0 ≤ p.2 ∧ p.2 ≤ 1) := by
  simp only [crossRayPosY, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

theorem mem_crossRayNegY {p : ℝ × ℝ} :
    p ∈ crossRayNegY ↔ p.1 = 0 ∧ (-1 ≤ p.2 ∧ p.2 ≤ 0) := by
  simp only [crossRayNegY, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

theorem crossingArcY_eq_union : crossingArcY = crossRayNegX ∪ crossRayPosX := by
  rw [crossingArcY_eq, crossRayNegX, crossRayPosX, ← Set.union_prod,
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

theorem crossingArcX_eq_union : crossingArcX = crossRayNegY ∪ crossRayPosY := by
  rw [crossingArcX_eq, crossRayNegY, crossRayPosY, ← Set.prod_union,
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

def bentArcPos : Set (ℝ × ℝ) := crossRayPosX ∪ crossRayNegY

def bentArcNeg : Set (ℝ × ℝ) := crossRayNegX ∪ crossRayPosY

def bentSheetPos : Set ((ℝ × ℝ) × ℝ) := bentArcPos ×ˢ Icc (0 : ℝ) 1

def bentSheetNeg : Set ((ℝ × ℝ) × ℝ) := bentArcNeg ×ˢ Icc (0 : ℝ) 1

def bentFigure : Set ((ℝ × ℝ) × ℝ) := (bentArcPos ∪ bentArcNeg) ×ˢ Icc (0 : ℝ) 1

theorem mem_bentArcPos {p : ℝ × ℝ} :
    p ∈ bentArcPos ↔ ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ p.2 = 0) ∨ (p.1 = 0 ∧ (-1 ≤ p.2 ∧ p.2 ≤ 0)) := by
  rw [bentArcPos, Set.mem_union, mem_crossRayPosX, mem_crossRayNegY]

theorem mem_bentArcNeg {p : ℝ × ℝ} :
    p ∈ bentArcNeg ↔ ((-1 ≤ p.1 ∧ p.1 ≤ 0) ∧ p.2 = 0) ∨ (p.1 = 0 ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)) := by
  rw [bentArcNeg, Set.mem_union, mem_crossRayNegX, mem_crossRayPosY]

theorem bentArcPos_subset_spliceSquare : bentArcPos ⊆ spliceSquare := by
  intro p hp
  rw [mem_bentArcPos] at hp
  rw [mem_spliceSquare]
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
  · exact ⟨⟨by linarith, h1⟩, by rw [h2]; norm_num⟩
  · exact ⟨by rw [h1]; norm_num, h0, by linarith⟩

theorem bentArcNeg_subset_spliceSquare : bentArcNeg ⊆ spliceSquare := by
  intro p hp
  rw [mem_bentArcNeg] at hp
  rw [mem_spliceSquare]
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
  · exact ⟨⟨h0, by linarith⟩, by rw [h2]; norm_num⟩
  · exact ⟨by rw [h1]; norm_num, by linarith, h2⟩

theorem bentArcPos_union_bentArcNeg :
    bentArcPos ∪ bentArcNeg = crossingArcX ∪ crossingArcY := by
  rw [bentArcPos, bentArcNeg, crossingArcX_eq_union, crossingArcY_eq_union]
  ext p
  simp only [Set.mem_union]
  tauto

theorem bentArcPos_inter_bentArcNeg : bentArcPos ∩ bentArcNeg = {((0 : ℝ), (0 : ℝ))} := by
  apply Set.Subset.antisymm
  · rintro p ⟨hpos, hneg⟩
    rw [mem_bentArcPos] at hpos
    rw [mem_bentArcNeg] at hneg
    have h1 : p.1 = 0 := by
      rcases hpos with ⟨hp, -⟩ | ⟨hp, -⟩
      · rcases hneg with ⟨hq, -⟩ | ⟨hq, -⟩
        · linarith [hp.1, hq.2]
        · exact hq
      · exact hp
    have h2 : p.2 = 0 := by
      rcases hpos with ⟨-, hp⟩ | ⟨-, hp⟩
      · exact hp
      · rcases hneg with ⟨-, hq⟩ | ⟨-, hq⟩
        · exact hq
        · linarith [hp.2, hq.1]
    exact Prod.ext h1 h2
  · rintro p rfl
    refine ⟨mem_bentArcPos.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
      mem_bentArcNeg.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩)⟩

theorem bentFigure_eq_crossingFigure : bentFigure = crossingFigure := by
  rw [bentFigure, crossingFigure, bentArcPos_union_bentArcNeg]

theorem bentSheetPos_inter_bentSheetNeg : bentSheetPos ∩ bentSheetNeg = spliceCore := by
  rw [bentSheetPos, bentSheetNeg, Set.prod_inter_prod, Set.inter_self,
    bentArcPos_inter_bentArcNeg, spliceCore]

theorem bentArcPos_inter_spliceSquareBoundary :
    bentArcPos ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨harc, -, hb⟩
    rw [mem_bentArcPos] at harc
    rcases harc with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [hx] at h0; linarith)
      · exact Or.inl (Prod.ext h h2)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact Or.inr (Prod.ext h1 h)
      · exact absurd h (by intro hx; rw [hx] at h2; linarith)
  · rintro (rfl | rfl)
    · exact ⟨mem_bentArcPos.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨mem_bentArcPos.mpr (Or.inr ⟨rfl, le_rfl, by norm_num⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

theorem bentArcNeg_inter_spliceSquareBoundary :
    bentArcNeg ∩ spliceSquareBoundary = {((-1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨harc, -, hb⟩
    rw [mem_bentArcNeg] at harc
    rcases harc with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · rcases hb with h | h | h | h
      · exact Or.inl (Prod.ext h h2)
      · exact absurd h (by intro hx; rw [hx] at h1; linarith)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [hx] at h0; linarith)
      · exact Or.inr (Prod.ext h1 h)
  · rintro (rfl | rfl)
    · exact ⟨mem_bentArcNeg.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩
    · exact ⟨mem_bentArcNeg.mpr (Or.inr ⟨rfl, by norm_num, le_rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩

theorem bentArcPos_inter_lateral_eq :
    bentArcPos ∩ spliceSquareBoundary = spliceArcPos ∩ spliceSquareBoundary := by
  rw [bentArcPos_inter_spliceSquareBoundary, spliceArcPos_inter_spliceSquareBoundary]

theorem bentArcNeg_inter_lateral_eq :
    bentArcNeg ∩ spliceSquareBoundary = spliceArcNeg ∩ spliceSquareBoundary := by
  rw [bentArcNeg_inter_spliceSquareBoundary, spliceArcNeg_inter_spliceSquareBoundary]

theorem bentFigure_inter_lateral :
    bentFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) = spliceEnds ×ˢ Icc (0 : ℝ) 1 := by
  rw [bentFigure_eq_crossingFigure]
  exact crossingFigure_inter_lateral

theorem isPolyhedron_bentArcPos : IsPolyhedron bentArcPos :=
  (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).isPolyhedron.union
    ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).isPolyhedron

theorem isPolyhedron_bentArcNeg : IsPolyhedron bentArcNeg :=
  (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).isPolyhedron.union
    ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).isPolyhedron

noncomputable def crossSeamChordPos (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 + 1) / 2, (p.1 + p.2 - 1) / 2)

noncomputable def crossSeamChordNeg (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 - 1) / 2, (p.1 + p.2 + 1) / 2)

theorem crossSeamChordPos_fst (p : ℝ × ℝ) :
    (crossSeamChordPos p).1 = (p.1 + p.2 + 1) / 2 := rfl

theorem crossSeamChordPos_snd (p : ℝ × ℝ) :
    (crossSeamChordPos p).2 = (p.1 + p.2 - 1) / 2 := rfl

theorem crossSeamChordNeg_fst (p : ℝ × ℝ) :
    (crossSeamChordNeg p).1 = (p.1 + p.2 - 1) / 2 := rfl

theorem crossSeamChordNeg_snd (p : ℝ × ℝ) :
    (crossSeamChordNeg p).2 = (p.1 + p.2 + 1) / 2 := rfl

noncomputable def crossSeamChordMapPos : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ where
  toFun := crossSeamChordPos
  linear := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).smulRight ((1 / 2 : ℝ), (1 / 2 : ℝ))
  map_vadd' p v := by
    refine Prod.ext ?_ ?_ <;> simp [crossSeamChordPos] <;> ring

noncomputable def crossSeamChordMapNeg : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ where
  toFun := crossSeamChordNeg
  linear := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).smulRight ((1 / 2 : ℝ), (1 / 2 : ℝ))
  map_vadd' p v := by
    refine Prod.ext ?_ ?_ <;> simp [crossSeamChordNeg] <;> ring

theorem crossSeamChordMapPos_apply (p : ℝ × ℝ) :
    crossSeamChordMapPos p = crossSeamChordPos p := rfl

theorem crossSeamChordMapNeg_apply (p : ℝ × ℝ) :
    crossSeamChordMapNeg p = crossSeamChordNeg p := rfl

theorem crossSeamChordPos_apply_posX : crossSeamChordPos ((1 : ℝ), (0 : ℝ)) = (1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> norm_num

theorem crossSeamChordPos_apply_negY : crossSeamChordPos ((0 : ℝ), (-1 : ℝ)) = (0, -1) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> norm_num

theorem crossSeamChordNeg_apply_negX : crossSeamChordNeg ((-1 : ℝ), (0 : ℝ)) = (-1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> norm_num

theorem crossSeamChordNeg_apply_posY : crossSeamChordNeg ((0 : ℝ), (1 : ℝ)) = (0, 1) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> norm_num

theorem sum_mem_Icc_of_mem_bentArcPos {p : ℝ × ℝ} (hp : p ∈ bentArcPos) :
    -1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [mem_bentArcPos] at hp
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩ <;> constructor <;> linarith

theorem sum_mem_Icc_of_mem_bentArcNeg {p : ℝ × ℝ} (hp : p ∈ bentArcNeg) :
    -1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [mem_bentArcNeg] at hp
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩ <;> constructor <;> linarith

theorem mapsTo_crossSeamChordPos : MapsTo crossSeamChordPos bentArcPos spliceArcPos := by
  intro p hp
  obtain ⟨hlow, hhigh⟩ := sum_mem_Icc_of_mem_bentArcPos hp
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [crossSeamChordPos_fst]; linarith
  · rw [crossSeamChordPos_fst]; linarith
  · rw [crossSeamChordPos_snd]; linarith
  · rw [crossSeamChordPos_snd]; linarith
  · rw [crossSeamChordPos_fst, crossSeamChordPos_snd]; ring

theorem mapsTo_crossSeamChordNeg : MapsTo crossSeamChordNeg bentArcNeg spliceArcNeg := by
  intro p hp
  obtain ⟨hlow, hhigh⟩ := sum_mem_Icc_of_mem_bentArcNeg hp
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [crossSeamChordNeg_fst]; linarith
  · rw [crossSeamChordNeg_fst]; linarith
  · rw [crossSeamChordNeg_snd]; linarith
  · rw [crossSeamChordNeg_snd]; linarith
  · rw [crossSeamChordNeg_fst, crossSeamChordNeg_snd]; ring

theorem injOn_crossSeamChordPos : InjOn crossSeamChordPos bentArcPos := by
  intro p hp q hq hpq
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    have h := congrArg Prod.fst hpq
    rw [crossSeamChordPos_fst, crossSeamChordPos_fst] at h
    linarith
  rw [mem_bentArcPos] at hp hq
  rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩ | ⟨hp1, hp0, hp2⟩ <;>
    rcases hq with ⟨⟨hq0, hq1⟩, hq2⟩ | ⟨hq1, hq0, hq2⟩ <;>
      exact Prod.ext (by linarith) (by linarith)

theorem injOn_crossSeamChordNeg : InjOn crossSeamChordNeg bentArcNeg := by
  intro p hp q hq hpq
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    have h := congrArg Prod.fst hpq
    rw [crossSeamChordNeg_fst, crossSeamChordNeg_fst] at h
    linarith
  rw [mem_bentArcNeg] at hp hq
  rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩ | ⟨hp1, hp0, hp2⟩ <;>
    rcases hq with ⟨⟨hq0, hq1⟩, hq2⟩ | ⟨hq1, hq0, hq2⟩ <;>
      exact Prod.ext (by linarith) (by linarith)

theorem surjOn_crossSeamChordPos : SurjOn crossSeamChordPos bentArcPos spliceArcPos := by
  rintro q ⟨hsq, hd⟩
  rw [mem_spliceSquare] at hsq
  by_cases hs : 0 ≤ q.1 + q.2
  · refine ⟨(q.1 + q.2, 0), mem_bentArcPos.mpr (Or.inl ⟨⟨hs, ?_⟩, rfl⟩), ?_⟩
    · linarith [hsq.1.2, hsq.2.2]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> linarith
  · replace hs : q.1 + q.2 < 0 := not_le.mp hs
    refine ⟨(0, q.1 + q.2), mem_bentArcPos.mpr (Or.inr ⟨rfl, ?_, le_of_lt hs⟩), ?_⟩
    · linarith [hsq.1.1, hsq.2.1]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> linarith

theorem surjOn_crossSeamChordNeg : SurjOn crossSeamChordNeg bentArcNeg spliceArcNeg := by
  rintro q ⟨hsq, hd⟩
  rw [mem_spliceSquare] at hsq
  by_cases hs : 0 ≤ q.1 + q.2
  · refine ⟨(0, q.1 + q.2), mem_bentArcNeg.mpr (Or.inr ⟨rfl, hs, ?_⟩), ?_⟩
    · linarith [hsq.1.2, hsq.2.2]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> linarith
  · replace hs : q.1 + q.2 < 0 := not_le.mp hs
    refine ⟨(q.1 + q.2, 0), mem_bentArcNeg.mpr (Or.inl ⟨⟨?_, le_of_lt hs⟩, rfl⟩), ?_⟩
    · linarith [hsq.1.1, hsq.2.1]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> linarith

theorem bijOn_crossSeamChordPos : BijOn crossSeamChordPos bentArcPos spliceArcPos :=
  ⟨mapsTo_crossSeamChordPos, injOn_crossSeamChordPos, surjOn_crossSeamChordPos⟩

theorem bijOn_crossSeamChordNeg : BijOn crossSeamChordNeg bentArcNeg spliceArcNeg :=
  ⟨mapsTo_crossSeamChordNeg, injOn_crossSeamChordNeg, surjOn_crossSeamChordNeg⟩

theorem isPiecewiseAffineOn_crossSeamChordPos :
    IsPiecewiseAffineOn crossSeamChordPos bentArcPos :=
  ((isPiecewiseAffineOn_of_affine_of_isHPolytope crossSeamChordMapPos
    isHPolytope_spliceSquare).mono_of_isPolyhedron isPolyhedron_bentArcPos
      bentArcPos_subset_spliceSquare).congr fun p _ => (crossSeamChordMapPos_apply p).symm

theorem isPiecewiseAffineOn_crossSeamChordNeg :
    IsPiecewiseAffineOn crossSeamChordNeg bentArcNeg :=
  ((isPiecewiseAffineOn_of_affine_of_isHPolytope crossSeamChordMapNeg
    isHPolytope_spliceSquare).mono_of_isPolyhedron isPolyhedron_bentArcNeg
      bentArcNeg_subset_spliceSquare).congr fun p _ => (crossSeamChordMapNeg_apply p).symm

theorem isPLHomeomorphOn_crossSeamChordPos :
    IsPLHomeomorphOn crossSeamChordPos bentArcPos spliceArcPos :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPolyhedron_bentArcPos
    isPiecewiseAffineOn_crossSeamChordPos bijOn_crossSeamChordPos

theorem isPLHomeomorphOn_crossSeamChordNeg :
    IsPLHomeomorphOn crossSeamChordNeg bentArcNeg spliceArcNeg :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPolyhedron_bentArcNeg
    isPiecewiseAffineOn_crossSeamChordNeg bijOn_crossSeamChordNeg

theorem spliceArcPos_eq_segment :
    spliceArcPos = segment ℝ ((0 : ℝ), (-1 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
  rw [spliceArcPos_eq, segment_eq_image]
  refine Set.image_congr fun t _ => ?_
  have h : (1 - t) • ((0 : ℝ), (-1 : ℝ)) + t • ((1 : ℝ), (0 : ℝ))
      = ((1 - t) * 0 + t * 1, (1 - t) * (-1) + t * 0) := rfl
  rw [h]
  exact Prod.ext (by ring) (by ring)

theorem spliceArcNeg_eq_segment :
    spliceArcNeg = segment ℝ ((-1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) := by
  rw [spliceArcNeg_eq, segment_eq_image]
  refine Set.image_congr fun t _ => ?_
  have h : (1 - t) • ((-1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ))
      = ((1 - t) * (-1) + t * 0, (1 - t) * 0 + t * 1) := rfl
  rw [h]
  exact Prod.ext (by ring) (by ring)

theorem isPLBall_spliceArcPos : IsPLBall 1 spliceArcPos := by
  rw [spliceArcPos_eq_segment]
  refine isPLBall_segment fun h => ?_
  exact absurd (congrArg Prod.fst h) (by norm_num)

theorem isPLBall_spliceArcNeg : IsPLBall 1 spliceArcNeg := by
  rw [spliceArcNeg_eq_segment]
  refine isPLBall_segment fun h => ?_
  exact absurd (congrArg Prod.fst h) (by norm_num)

theorem isPLBall_bentArcPos : IsPLBall 1 bentArcPos :=
  isPLBall_spliceArcPos.of_isPLHomeomorphOn isPLHomeomorphOn_crossSeamChordPos.symm

theorem isPLBall_bentArcNeg : IsPLBall 1 bentArcNeg :=
  isPLBall_spliceArcNeg.of_isPLHomeomorphOn isPLHomeomorphOn_crossSeamChordNeg.symm

theorem isPLBall_bentSheetPos : IsPLBall 2 bentSheetPos :=
  isPLBall_two_prod isPLBall_bentArcPos (isPLBall_Icc zero_lt_one)

theorem isPLBall_bentSheetNeg : IsPLBall 2 bentSheetNeg :=
  isPLBall_two_prod isPLBall_bentArcNeg (isPLBall_Icc zero_lt_one)

theorem isPLBall_spliceSheetPos : IsPLBall 2 spliceSheetPos :=
  isPLBall_two_prod isPLBall_spliceArcPos (isPLBall_Icc zero_lt_one)

theorem isPLBall_spliceSheetNeg : IsPLBall 2 spliceSheetNeg :=
  isPLBall_two_prod isPLBall_spliceArcNeg (isPLBall_Icc zero_lt_one)

noncomputable def crossSeamResolvePos : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  Prod.map crossSeamChordPos id

noncomputable def crossSeamResolveNeg : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  Prod.map crossSeamChordNeg id

theorem crossSeamResolvePos_fst (p : (ℝ × ℝ) × ℝ) :
    (crossSeamResolvePos p).1 = crossSeamChordPos p.1 := rfl

theorem crossSeamResolvePos_snd (p : (ℝ × ℝ) × ℝ) : (crossSeamResolvePos p).2 = p.2 := rfl

theorem crossSeamResolveNeg_fst (p : (ℝ × ℝ) × ℝ) :
    (crossSeamResolveNeg p).1 = crossSeamChordNeg p.1 := rfl

theorem crossSeamResolveNeg_snd (p : (ℝ × ℝ) × ℝ) : (crossSeamResolveNeg p).2 = p.2 := rfl

theorem isPLHomeomorphOn_crossSeamResolvePos :
    IsPLHomeomorphOn crossSeamResolvePos bentSheetPos spliceSheetPos :=
  isPLHomeomorphOn_crossSeamChordPos.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

theorem isPLHomeomorphOn_crossSeamResolveNeg :
    IsPLHomeomorphOn crossSeamResolveNeg bentSheetNeg spliceSheetNeg :=
  isPLHomeomorphOn_crossSeamChordNeg.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

theorem disjoint_image_crossSeamResolve :
    Disjoint (crossSeamResolvePos '' bentSheetPos) (crossSeamResolveNeg '' bentSheetNeg) := by
  rw [isPLHomeomorphOn_crossSeamResolvePos.bijOn.image_eq,
    isPLHomeomorphOn_crossSeamResolveNeg.bijOn.image_eq]
  exact disjoint_spliceSheetPos_spliceSheetNeg

theorem crossSeamResolvePos_eqOn_lateral :
    EqOn crossSeamResolvePos id (bentSheetPos ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)) := by
  rintro p ⟨⟨harc, -⟩, hb, -⟩
  have hp : p.1 ∈ bentArcPos ∩ spliceSquareBoundary := ⟨harc, hb⟩
  rw [bentArcPos_inter_spliceSquareBoundary] at hp
  refine Prod.ext ?_ (crossSeamResolvePos_snd p)
  rw [crossSeamResolvePos_fst]
  change crossSeamChordPos p.1 = p.1
  rcases hp with h | h
  · rw [h]; exact crossSeamChordPos_apply_posX
  · rw [Set.mem_singleton_iff.mp h]; exact crossSeamChordPos_apply_negY

theorem crossSeamResolveNeg_eqOn_lateral :
    EqOn crossSeamResolveNeg id (bentSheetNeg ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)) := by
  rintro p ⟨⟨harc, -⟩, hb, -⟩
  have hp : p.1 ∈ bentArcNeg ∩ spliceSquareBoundary := ⟨harc, hb⟩
  rw [bentArcNeg_inter_spliceSquareBoundary] at hp
  refine Prod.ext ?_ (crossSeamResolveNeg_snd p)
  rw [crossSeamResolveNeg_fst]
  change crossSeamChordNeg p.1 = p.1
  rcases hp with h | h
  · rw [h]; exact crossSeamChordNeg_apply_negX
  · rw [Set.mem_singleton_iff.mp h]; exact crossSeamChordNeg_apply_posY

theorem convex_spliceSquare : Convex ℝ spliceSquare :=
  (convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)

theorem segment_crossSeamResolvePos_subset {p : (ℝ × ℝ) × ℝ} (hp : p ∈ bentSheetPos) :
    segment ℝ p (crossSeamResolvePos p) ⊆ spliceSquare ×ˢ ({p.2} : Set ℝ) := by
  refine (convex_spliceSquare.prod (convex_singleton p.2)).segment_subset ?_ ?_
  · exact ⟨bentArcPos_subset_spliceSquare hp.1, rfl⟩
  · refine ⟨?_, crossSeamResolvePos_snd p⟩
    rw [crossSeamResolvePos_fst]
    exact Set.sep_subset _ _ (mapsTo_crossSeamChordPos hp.1)

theorem segment_crossSeamResolveNeg_subset {p : (ℝ × ℝ) × ℝ} (hp : p ∈ bentSheetNeg) :
    segment ℝ p (crossSeamResolveNeg p) ⊆ spliceSquare ×ˢ ({p.2} : Set ℝ) := by
  refine (convex_spliceSquare.prod (convex_singleton p.2)).segment_subset ?_ ?_
  · exact ⟨bentArcNeg_subset_spliceSquare hp.1, rfl⟩
  · refine ⟨?_, crossSeamResolveNeg_snd p⟩
    rw [crossSeamResolveNeg_fst]
    exact Set.sep_subset _ _ (mapsTo_crossSeamChordNeg hp.1)

theorem bentFigure_eq_union : bentFigure = bentSheetPos ∪ bentSheetNeg := by
  rw [bentFigure, bentSheetPos, bentSheetNeg, Set.union_prod]

theorem spliceFigure_eq_union : spliceFigure = spliceSheetPos ∪ spliceSheetNeg := by
  rw [spliceFigure, spliceSheetPos, spliceSheetNeg, Set.union_prod]

def bentSource : Set (Bool × ((ℝ × ℝ) × ℝ)) :=
  {true} ×ˢ bentSheetPos ∪ {false} ×ˢ bentSheetNeg

theorem mem_bentSource {q : Bool × ((ℝ × ℝ) × ℝ)} :
    q ∈ bentSource ↔
      (q.1 = true ∧ q.2 ∈ bentSheetPos) ∨ (q.1 = false ∧ q.2 ∈ bentSheetNeg) := by
  simp only [bentSource, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff]

def crossSeamInclude (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ := q.2

noncomputable def crossSeamResolve (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ :=
  if q.1 then crossSeamResolvePos q.2 else crossSeamResolveNeg q.2

theorem crossSeamResolve_true (x : (ℝ × ℝ) × ℝ) :
    crossSeamResolve (true, x) = crossSeamResolvePos x := rfl

theorem crossSeamResolve_false (x : (ℝ × ℝ) × ℝ) :
    crossSeamResolve (false, x) = crossSeamResolveNeg x := rfl

theorem injOn_crossSeamResolve : InjOn crossSeamResolve bentSource := by
  rintro ⟨b, x⟩ hq ⟨b', x'⟩ hr hqr
  rcases mem_bentSource.mp hq with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;>
    rcases mem_bentSource.mp hr with ⟨hb', hx'⟩ | ⟨hb', hx'⟩ <;>
      subst hb <;> subst hb'
  · rw [crossSeamResolve_true, crossSeamResolve_true] at hqr
    exact Prod.ext rfl (isPLHomeomorphOn_crossSeamResolvePos.bijOn.injOn hx hx' hqr)
  · exfalso
    rw [crossSeamResolve_true, crossSeamResolve_false] at hqr
    have h1 : crossSeamResolvePos x ∈ spliceSheetPos :=
      isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo hx
    rw [hqr] at h1
    exact Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg h1
      (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo hx')
  · exfalso
    rw [crossSeamResolve_false, crossSeamResolve_true] at hqr
    have h1 : crossSeamResolveNeg x ∈ spliceSheetNeg :=
      isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo hx
    rw [hqr] at h1
    exact Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg
      (isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo hx') h1
  · rw [crossSeamResolve_false, crossSeamResolve_false] at hqr
    exact Prod.ext rfl (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.injOn hx hx' hqr)

theorem doublePointSet_crossSeamInclude :
    doublePointSet crossSeamInclude bentSource = spliceCore := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨b, x⟩, hq, ⟨b', x'⟩, hr, hne, hy1, hy2⟩
    have hx : x = y := hy1
    have hx' : x' = y := hy2
    have hbb : b ≠ b' := fun h => hne (Prod.ext h (hx.trans hx'.symm))
    rw [← bentSheetPos_inter_bentSheetNeg]
    rcases mem_bentSource.mp hq with ⟨hb, hs⟩ | ⟨hb, hs⟩ <;>
      rcases mem_bentSource.mp hr with ⟨hb', hs'⟩ | ⟨hb', hs'⟩
    · exact absurd (hb.trans hb'.symm) hbb
    · exact ⟨hx ▸ hs, hx' ▸ hs'⟩
    · exact ⟨hx' ▸ hs', hx ▸ hs⟩
    · exact absurd (hb.trans hb'.symm) hbb
  · intro y hy
    rw [← bentSheetPos_inter_bentSheetNeg] at hy
    exact ⟨(true, y), mem_bentSource.mpr (Or.inl ⟨rfl, hy.1⟩), (false, y),
      mem_bentSource.mpr (Or.inr ⟨rfl, hy.2⟩),
      fun h => Bool.noConfusion (congrArg Prod.fst h), rfl, rfl⟩

theorem doublePointSet_crossSeamResolve :
    doublePointSet crossSeamResolve bentSource = ∅ :=
  (doublePointSet_eq_empty_iff_injOn crossSeamResolve bentSource).mpr injOn_crossSeamResolve

theorem image_crossSeamInclude : crossSeamInclude '' bentSource = bentFigure := by
  rw [bentFigure_eq_union]
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    rcases mem_bentSource.mp hq with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro x (hx | hx)
    · exact ⟨(true, x), mem_bentSource.mpr (Or.inl ⟨rfl, hx⟩), rfl⟩
    · exact ⟨(false, x), mem_bentSource.mpr (Or.inr ⟨rfl, hx⟩), rfl⟩

theorem image_crossSeamResolve : crossSeamResolve '' bentSource = spliceFigure := by
  rw [spliceFigure_eq_union]
  apply Set.Subset.antisymm
  · rintro x ⟨⟨b, z⟩, hq, rfl⟩
    rcases mem_bentSource.mp hq with ⟨hb, h⟩ | ⟨hb, h⟩ <;> subst hb
    · exact Or.inl (isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo h)
    · exact Or.inr (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo h)
  · rintro x (hx | hx)
    · obtain ⟨z, hz, rfl⟩ := isPLHomeomorphOn_crossSeamResolvePos.bijOn.surjOn hx
      exact ⟨(true, z), mem_bentSource.mpr (Or.inl ⟨rfl, hz⟩), rfl⟩
    · obtain ⟨z, hz, rfl⟩ := isPLHomeomorphOn_crossSeamResolveNeg.bijOn.surjOn hx
      exact ⟨(false, z), mem_bentSource.mpr (Or.inr ⟨rfl, hz⟩), rfl⟩

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

theorem complexity_lt_of_branchEquiv_compl (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') {c : T.Branch}
    (e : T'.Branch ≃ {b : T.Branch // b ≠ c}) :
    T'.complexity < T.complexity :=
  T.complexity_lt_of_injective_origin T' c (fun b => (e b).1)
    (fun _ _ h => e.injective (Subtype.ext h)) fun b => (e b).2

end NormalSingularSetTriangulation

structure CrossSeamResolutionData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) (U : Set M) where
  cell : SingularTwoCell M
  normal : NormalSingularCellData cell BdM B
  doublePointSet_eq : doublePointSet cell cell.domain =
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c
  branchEquiv : normal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}
  branchCarrier_eq : ∀ b, normal.singularSet.branchCarrier b =
    hD.singularSet.branchCarrier (branchEquiv b).1
  image_subset : cell '' cell.domain ⊆ D '' D.domain ∪ U

namespace CrossSeamResolutionData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

theorem complexity_lt (R : CrossSeamResolutionData hD c U) :
    R.normal.singularSet.complexity < hD.singularSet.complexity :=
  hD.singularSet.complexity_lt_of_branchEquiv_compl R.normal.singularSet R.branchEquiv

theorem doublePointSet_subset (R : CrossSeamResolutionData hD c U) :
    doublePointSet R.cell R.cell.domain ⊆ doublePointSet D D.domain := by
  rw [R.doublePointSet_eq]
  exact Set.sdiff_subset

theorem disjoint_branchCarrier (R : CrossSeamResolutionData hD c U) :
    Disjoint (doublePointSet R.cell R.cell.domain) (hD.singularSet.branchCarrier c) := by
  rw [R.doublePointSet_eq]
  exact Set.disjoint_sdiff_left

theorem branchCarrier_mem_range (R : CrossSeamResolutionData hD c U)
    (b : R.normal.singularSet.Branch) :
    R.normal.singularSet.branchCarrier b ∈
      Set.range (hD.singularSet.branchCarrier ∘ fun b' : {b' // b' ≠ c} => b'.1) :=
  ⟨R.branchEquiv b, (R.branchCarrier_eq b).symm⟩

end CrossSeamResolutionData

end DifferentialGeometry.Topology.PiecewiseLinear
