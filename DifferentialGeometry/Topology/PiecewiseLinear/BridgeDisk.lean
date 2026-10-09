/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedIntervalLink
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskArcGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "V2" => (Fin 3 → ℝ)
local notation "Δ" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "v0" => (![1, 0, 0] : V2)
local notation "v1" => (![0, 1, 0] : V2)

def standardTriangleBase : Set V2 := {x | x ∈ Δ ∧ x 2 = 0}

def standardTriangleSides : Set V2 := {x | x ∈ Δ ∧ (x 0 = 0 ∨ x 1 = 0)}

theorem standardTriangleBase_eq_segment : standardTriangleBase = segment ℝ v0 v1 := by
  have hline (t : ℝ) : AffineMap.lineMap v0 v1 t = ![1 - t, t, 0] := by
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply]
    ring
  rw [segment_eq_image_lineMap]
  ext x
  constructor
  · rintro ⟨hx, hx2⟩
    have hsum : x 0 + x 1 + x 2 = 1 := by simpa only [Fin.sum_univ_three] using hx.2
    refine ⟨x 1, ⟨hx.1 1, by linarith [hx.1 0]⟩, ?_⟩
    rw [hline]
    ext i
    fin_cases i <;> simp <;> linarith
  · rintro ⟨t, ht, rfl⟩
    rw [hline]
    refine ⟨⟨?_, ?_⟩, by simp⟩
    · intro i
      fin_cases i <;> simp <;> linarith [ht.1, ht.2]
    · simp [Fin.sum_univ_three]

theorem standardTriangleBase_union_sides :
    standardTriangleBase ∪ standardTriangleSides = stdSimplexBoundary 2 := by
  ext x
  constructor
  · rintro (⟨hx, hx2⟩ | ⟨hx, hx0 | hx1⟩)
    · exact ⟨hx, 2, hx2⟩
    · exact ⟨hx, 0, hx0⟩
    · exact ⟨hx, 1, hx1⟩
  · rintro ⟨hx, i, hi⟩
    fin_cases i
    · exact Or.inr ⟨hx, Or.inl hi⟩
    · exact Or.inr ⟨hx, Or.inr hi⟩
    · exact Or.inl ⟨hx, hi⟩

theorem standardTriangleBase_inter_sides :
    standardTriangleBase ∩ standardTriangleSides = {v0, v1} := by
  ext x
  constructor
  · rintro ⟨⟨hx, hx2⟩, _, hx0 | hx1⟩
    · right
      apply mem_singleton_iff.mpr
      have hsum : x 0 + x 1 + x 2 = 1 := by simpa only [Fin.sum_univ_three] using hx.2
      ext i
      fin_cases i <;> simp <;> linarith
    · left
      have hsum : x 0 + x 1 + x 2 = 1 := by simpa only [Fin.sum_univ_three] using hx.2
      ext i
      fin_cases i <;> simp <;> linarith
  · rintro (rfl | hx)
    · constructor
      · refine ⟨⟨?_, by norm_num [Fin.sum_univ_succ]⟩, by rfl⟩
        intro i
        fin_cases i <;> norm_num
      · refine ⟨⟨?_, by norm_num [Fin.sum_univ_succ]⟩, Or.inr (by norm_num)⟩
        intro i
        fin_cases i <;> norm_num
    · rcases mem_singleton_iff.mp hx with rfl
      constructor
      · refine ⟨⟨?_, by norm_num [Fin.sum_univ_succ]⟩, by rfl⟩
        intro i
        fin_cases i <;> norm_num
      · refine ⟨⟨?_, by norm_num [Fin.sum_univ_succ]⟩, Or.inl (by norm_num)⟩
        intro i
        fin_cases i <;> norm_num

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsBridgeDisk (C A B : Set E) (a b : E) : Prop :=
  ∃ q : V2 → E,
    IsPLHomeomorphOn q Δ B ∧ B ⊆ C ∧
    q '' standardTriangleBase = A ∧ B ∩ frontier C = q '' standardTriangleSides ∧
    q v0 = a ∧ q v1 = b

variable [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_Icc_with_boundary_endpoints
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : IsPLBall 1 A.space)
    {a b : E} (hbd : (boundaryComplex 1 A).space = {a, b}) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) A.space ∧ γ 0 = a ∧ γ 1 = b := by
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hA
  have hpair : {γ 0, γ 1} = ({a, b} : Set E) :=
    (boundaryComplex_space_of_parametrized_Icc A zero_lt_one hγ).symm.trans hbd
  have h0 : γ 0 = a ∨ γ 0 = b := hpair.subset (Or.inl rfl)
  have h1 : γ 1 = a ∨ γ 1 = b := hpair.subset (Or.inr rfl)
  have hne : γ 0 ≠ γ 1 := fun h => zero_ne_one
    (hγ.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact (hne (h0.trans h1.symm)).elim
  · exact ⟨γ, hγ, h0, h1⟩
  · exact ⟨fun t => γ (1 - t), isPLHomeomorphOn_comp_one_sub hγ, by simpa using h1,
      by simpa using h0⟩
  · exact (hne (h0.trans h1.symm)).elim

open Classical in
theorem exists_isBridgeDisk_of_boundary_cover
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces] (hB : IsPLBall 2 B.space)
    {C A : Set E} (hBC : B.space ⊆ C) {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hAB : A ⊆ (boundaryComplex 2 B).space)
    (hfront : B.space ∩ frontier C ⊆ (boundaryComplex 2 B).space)
    (hcover : (boundaryComplex 2 B).space ⊆ A ∪ frontier C)
    (hends : A ∩ frontier C = {γ 0, γ 1}) :
    IsBridgeDisk C A B.space (γ 0) (γ 1) := by
  let : DecidableEq V2 := Classical.decEq V2
  let α := AffineMap.lineMap (k := ℝ) v0 v1
  have hne : v0 ≠ v1 := by intro h; have hh := congrFun h 0; norm_num at hh
  have hα : IsPLHomeomorphOn α (Icc 0 1) standardTriangleBase := by
    rw [standardTriangleBase_eq_segment]
    exact isPLHomeomorphOn_lineMap_Icc_segment hne
  have hα0 : α 0 = v0 := AffineMap.lineMap_apply_zero _ _
  have hα1 : α 1 = v1 := AffineMap.lineMap_apply_one _ _
  have hv0 : v0 ∈ standardTriangleBase := hα0 ▸ hα.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hv1 : v1 ∈ standardTriangleBase := hα1 ▸ hα.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hv0s : v0 ∈ standardTriangleSides :=
    (standardTriangleBase_inter_sides.symm.subset (Or.inl rfl)).2
  have hv1s : v1 ∈ standardTriangleSides :=
    (standardTriangleBase_inter_sides.symm.subset (Or.inr rfl)).2
  let g := γ ∘ Function.invFunOn α (Icc 0 1)
  have hg : IsPLHomeomorphOn g standardTriangleBase A := hα.symm.trans hγ
  have hg0 : g v0 = γ 0 := by
    change γ (Function.invFunOn α (Icc 0 1) v0) = γ 0
    rw [← hα0, hα.bijOn.invOn_invFunOn.1 ⟨le_rfl, zero_le_one⟩]
  have hg1 : g v1 = γ 1 := by
    change γ (Function.invFunOn α (Icc 0 1) v1) = γ 1
    rw [← hα1, hα.bijOn.invOn_invFunOn.1 ⟨zero_le_one, le_rfl⟩]
  obtain ⟨Q, hQfin, hQspace⟩ := (isPLBall_stdSimplex 2).isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 2 Q.space := hQspace.symm ▸ isPLBall_stdSimplex 2
  have hQB : (boundaryComplex 2 Q).space = stdSimplexBoundary 2 := by
    have hid := (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
    simpa only [image_id] using (hid.image_stdSimplexBoundary_eq_boundaryComplex Q hQspace).symm
  have hbase : standardTriangleBase ⊆ (boundaryComplex 2 Q).space := by
    rw [hQB, ← standardTriangleBase_union_sides]
    exact subset_union_left
  have hBaseBall : IsPLBall 1 standardTriangleBase :=
    (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hα
  obtain ⟨q, hq, hqg⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient
    Q B hQ hB hBaseBall hbase hg hAB
  rw [hQspace] at hq
  have hq0 : q v0 = γ 0 := (hqg hv0).trans hg0
  have hq1 : q v1 = γ 1 := (hqg hv1).trans hg1
  have hqbase : q '' standardTriangleBase = A := hqg.image_eq.trans hg.image_eq
  have hqbdy : q '' stdSimplexBoundary 2 = (boundaryComplex 2 B).space :=
    hq.image_stdSimplexBoundary_eq_boundaryComplex B rfl
  refine ⟨q, hq, hBC, hqbase, ?_, hq0, hq1⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hqbdy.symm.subset (hfront hx)
    rcases standardTriangleBase_union_sides.symm.subset hz with hzb | hzs
    · have hxA : q z ∈ A := hqbase.subset ⟨z, hzb, rfl⟩
      rcases hends.subset ⟨hxA, hx.2⟩ with h0 | h1
      · exact ⟨v0, hv0s, hq0.trans h0.symm⟩
      · exact ⟨v1, hv1s, hq1.trans (mem_singleton_iff.mp h1).symm⟩
    · exact ⟨z, hzs, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨hq.bijOn.mapsTo hz.1, ?_⟩
    by_cases hzA : q z ∈ A
    · obtain ⟨y, hy, heq⟩ := hqbase.symm.subset hzA
      have hzy : y = z := hq.bijOn.injOn hy.1 hz.1 heq
      have hzbase : z ∈ standardTriangleBase := hzy ▸ hy
      rcases standardTriangleBase_inter_sides.subset ⟨hzbase, hz⟩ with h0 | h1
      · rw [h0, hq0]
        exact (hends.symm.subset (Or.inl rfl)).2
      · rw [mem_singleton_iff.mp h1, hq1]
        exact (hends.symm.subset (Or.inr rfl)).2
    · exact (hcover (hqbdy.subset ⟨z,
        standardTriangleBase_union_sides.subset (Or.inr hz), rfl⟩)).resolve_left hzA

end DifferentialGeometry.Topology.PiecewiseLinear
