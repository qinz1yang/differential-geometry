/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskArc
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingDoubleCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Q" => (ℝ × ℝ) × ℝ
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "C₀" => (J ×ˢ J) ×ˢ I
local notation "A₀" => ({((0 : ℝ), (0 : ℝ))} ×ˢ I)
local notation "B₀" => (I ×ˢ {(0 : ℝ)}) ×ˢ I

private theorem mem_frontier_standard_box_on_disk {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    ((x, 0), t) ∈ frontier C₀ ↔ x = 1 ∨ t = 0 ∨ t = 1 := by
  have hxJ : x ∈ J := ⟨by linarith [hx.1], hx.2⟩
  have hxneg : x ≠ -1 := by linarith [hx.1]
  simp only [frontier_prod_eq, closure_prod_eq, isClosed_Icc.closure_eq,
    frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1), frontier_Icc (zero_le_one : (0 : ℝ) ≤ 1),
    mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
  norm_num [hxJ, ht, hxneg]
  tauto

theorem isPLBall_standardBox : IsPLBall 3 C₀ :=
  isPLBall_three_prod
    (isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num)))
    (isPLBall_Icc zero_lt_one)

theorem standardBoxBridgeDisk_inter_frontier :
    B₀ ∩ frontier C₀ =
      ({(1 : ℝ)} ×ˢ {(0 : ℝ)}) ×ˢ I ∪ (I ×ˢ {(0 : ℝ)}) ×ˢ ({0, 1} : Set ℝ) := by
  ext ⟨⟨x, y⟩, t⟩
  constructor
  · rintro ⟨⟨⟨hx, hy⟩, ht⟩, hfront⟩
    have hy0 : y = 0 := hy
    subst y
    rcases (mem_frontier_standard_box_on_disk hx ht).mp hfront with hx1 | ht0 | ht1
    · exact Or.inl ⟨⟨hx1, rfl⟩, ht⟩
    · exact Or.inr ⟨⟨hx, rfl⟩, Or.inl ht0⟩
    · exact Or.inr ⟨⟨hx, rfl⟩, Or.inr ht1⟩
  · rintro (⟨⟨hx, hy⟩, ht⟩ | ⟨⟨hx, hy⟩, ht⟩)
    · have hx1 : x = 1 := hx
      have hy0 : y = 0 := hy
      subst x y
      exact ⟨⟨⟨by norm_num, rfl⟩, ht⟩,
        (mem_frontier_standard_box_on_disk (by norm_num) ht).mpr (Or.inl rfl)⟩
    · have hy0 : y = 0 := hy
      subst y
      have htI : t ∈ I := by rcases ht with rfl | rfl <;> norm_num
      exact ⟨⟨⟨hx, rfl⟩, htI⟩,
        (mem_frontier_standard_box_on_disk hx htI).mpr (Or.inr ht)⟩

theorem isBridgeDisk_standardBox_axis :
    IsBridgeDisk C₀ A₀ B₀ (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ((0, 0), 1) := by
  classical
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  let _ : DecidableEq Q := Classical.decEq _
  have hI : IsPLBall 1 I := isPLBall_Icc zero_lt_one
  have hR : IsPLBall 2 (I ×ˢ I) := isPLBall_two_prod hI hI
  let j : ℝ × ℝ → Q := fun z => ((z.1, 0), z.2)
  have hj : IsPLHomeomorphOn j (I ×ˢ I) B₀ :=
    (hI.isPolyhedron.isPLHomeomorphOn_prod_const 0).prodMap hI.isPolyhedron.isPLHomeomorphOn_id
  have hB : IsPLBall 2 B₀ := hR.of_isPLHomeomorphOn hj
  obtain ⟨R, hRfin, hRsp⟩ := hR.isPolyhedron.exists_simplicialComplex
  obtain ⟨B, hBfin, hBsp⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hRball : IsPLBall 2 R.space := hRsp.symm ▸ hR
  have hBball : IsPLBall 2 B.space := hBsp.symm ▸ hB
  have hjRB : IsPLHomeomorphOn j R.space B.space := by rw [hRsp, hBsp]; exact hj
  have hRbd : (boundaryComplex 2 R).space = frontier (I ×ˢ I) := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) R hRball.isCombinatorialManifoldWithBoundary, hRsp]
  have hBbd : (boundaryComplex 2 B).space = j '' frontier (I ×ˢ I) := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn R B
      hRball.isCombinatorialManifoldWithBoundary hjRB, hRbd]
  have hRb : frontier (I ×ˢ I) = I ×ˢ ({0, 1} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ I := by
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc zero_le_one]
  have hBC : B.space ⊆ C₀ := by
    rw [hBsp]
    rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩, ht⟩
    have hy0 : y = 0 := hy
    subst y
    exact ⟨⟨⟨by linarith [hx.1], hx.2⟩, by norm_num⟩, ht⟩
  let γ : ℝ → Q := fun t => ((0, 0), t)
  have hγ : IsPLHomeomorphOn γ I A₀ := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hI.isPolyhedron
    · exact isPiecewiseAffineOn_of_affine_of_isHPolytope
        ((AffineMap.const ℝ ℝ ((0 : ℝ), (0 : ℝ))).prod (AffineMap.id ℝ ℝ))
        isHPolytope_Icc
    · refine ⟨fun t ht => ⟨rfl, ht⟩, fun s _ t _ h => congrArg Prod.snd h, ?_⟩
      rintro ⟨⟨x, y⟩, t⟩ ⟨hxy, ht⟩
      exact ⟨t, ht, Prod.ext hxy.symm rfl⟩
  have hAB : A₀ ⊆ (boundaryComplex 2 B).space := by
    rw [hBbd, hRb]
    rintro ⟨⟨x, y⟩, t⟩ ⟨hxy, ht⟩
    refine ⟨(0, t), Or.inr ⟨Or.inl rfl, ht⟩, ?_⟩
    exact Prod.ext hxy.symm rfl
  have hfront : B.space ∩ frontier C₀ ⊆ (boundaryComplex 2 B).space := by
    rw [hBsp, hBbd, hRb]
    rintro ⟨⟨x, y⟩, t⟩ ⟨⟨⟨hx, hy⟩, ht⟩, hfr⟩
    have hy0 : y = 0 := hy
    subst y
    refine ⟨(x, t), ?_, rfl⟩
    rcases (mem_frontier_standard_box_on_disk hx ht).mp hfr with hx1 | ht0 | ht1
    · exact Or.inr ⟨Or.inr hx1, ht⟩
    · exact Or.inl ⟨hx, Or.inl ht0⟩
    · exact Or.inl ⟨hx, Or.inr ht1⟩
  have hcover : (boundaryComplex 2 B).space ⊆ A₀ ∪ frontier C₀ := by
    rw [hBbd, hRb]
    rintro _ ⟨⟨x, t⟩, hxt, rfl⟩
    rcases hxt with ⟨hx, ht⟩ | ⟨hx, ht⟩
    · have htI : t ∈ I := by rcases ht with rfl | rfl <;> norm_num
      exact Or.inr ((mem_frontier_standard_box_on_disk hx htI).mpr (Or.inr ht))
    · rcases hx with rfl | rfl
      · exact Or.inl ⟨rfl, ht⟩
      · exact Or.inr ((mem_frontier_standard_box_on_disk (by norm_num) ht).mpr (Or.inl rfl))
  have hends : A₀ ∩ frontier C₀ = {γ 0, γ 1} := by
    ext ⟨⟨x, y⟩, t⟩
    constructor
    · rintro ⟨⟨hxy, ht⟩, hfr⟩
      have hxy0 : (x, y) = ((0 : ℝ), (0 : ℝ)) := hxy
      have hx0 : x = 0 := congrArg Prod.fst hxy0
      have hy0 : y = 0 := congrArg Prod.snd hxy0
      subst x y
      rcases (mem_frontier_standard_box_on_disk (by norm_num) ht).mp hfr with h | h | h
      · norm_num at h
      · exact Or.inl (Prod.ext rfl h)
      · exact Or.inr (Prod.ext rfl h)
    · rintro (h | h)
      · have h0 : ((x, y), t) = γ 0 := h
        rw [h0]
        exact ⟨⟨rfl, by norm_num⟩,
          (mem_frontier_standard_box_on_disk (by norm_num) (by norm_num)).mpr (Or.inr (Or.inl rfl))⟩
      · have h1 : ((x, y), t) = γ 1 := h
        rw [h1]
        exact ⟨⟨rfl, by norm_num⟩,
          (mem_frontier_standard_box_on_disk (by norm_num) (by norm_num)).mpr (Or.inr (Or.inr rfl))⟩
  have hbridge := exists_isBridgeDisk_of_boundary_cover B hBball hBC hγ hAB hfront hcover hends
  rwa [hBsp] at hbridge

def standardBoxBridgeLeftChart : Q ≃ᵃ[ℝ] Q :=
  (AffineEquiv.prodComm ℝ (ℝ × ℝ) ℝ).trans (AffineEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm

def standardBoxBridgeRightChart : Q ≃ᵃ[ℝ] Q :=
  standardBoxBridgeLeftChart.trans
    (((AffineEquiv.constVSub ℝ (0 : ℝ)).prodCongr (AffineEquiv.refl ℝ ℝ)).prodCongr
      (AffineEquiv.constVSub ℝ (1 : ℝ)))

noncomputable def standardBoxBridgeMiddleChart : Q ≃ᵃ[ℝ] Q :=
  standardBoxBridgeLeftChart.trans (AffineEquiv.vaddConst ℝ (((1 / 2 : ℝ), 0), 0))

@[simp] theorem standardBoxBridgeLeftChart_apply (p : Q) :
    standardBoxBridgeLeftChart p = ((p.2, p.1.1), p.1.2) := rfl

@[simp] theorem standardBoxBridgeRightChart_apply (p : Q) :
    standardBoxBridgeRightChart p = ((-p.2, p.1.1), 1 - p.1.2) := by
  simp [standardBoxBridgeRightChart, AffineEquiv.constVSub]

@[simp] theorem standardBoxBridgeMiddleChart_apply (p : Q) :
    standardBoxBridgeMiddleChart p = ((p.2 + 1 / 2, p.1.1), p.1.2) := by
  simp [standardBoxBridgeMiddleChart]

local notation "U₀" =>
  Set.prod (Set.prod (Ioo (-1 / 4 : ℝ) (1 / 4)) (Ioo (-1 / 4 : ℝ) (1 / 4)))
    (Ioo (-1 / 4 : ℝ) (1 / 4))

private theorem standardBoxBridge_chart_openBox (e : Q ≃ᵃ[ℝ] Q) :
    IsOpen U₀ ∧ (0 : Q) ∈ U₀ ∧ IsOpen (e '' U₀) ∧
      IsPLHomeomorphOn e U₀ (e '' U₀) := by
  have hU : IsOpen U₀ := (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo
  have he := isPLHomeomorphOn_univ_of_affineEquiv e
  have heU := he.isOpen_image_of_isOpen isOpen_univ hU (subset_univ _)
  have hzero : (0 : ℝ) ∈ Ioo (-1 / 4 : ℝ) (1 / 4) := by norm_num
  exact ⟨hU, ⟨⟨hzero, hzero⟩, hzero⟩, heU,
    he.restrict_isOpen hU (subset_univ _) heU⟩

private theorem standardBoxBridge_coordinate_memberships {x y t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    (((x, y), t) ∈ C₀ ↔ 0 ≤ t ∧ t ≤ 1) ∧
      (((x, y), t) ∈ frontier C₀ ↔ t = 0 ∨ t = 1) ∧
      (((x, y), t) ∈ B₀ ↔ y = 0 ∧ 0 ≤ x ∧ 0 ≤ t ∧ t ≤ 1) ∧
      (((x, y), t) ∈ A₀ ↔ x = 0 ∧ y = 0 ∧ 0 ≤ t ∧ t ≤ 1) := by
  have hxJ : x ∈ J := ⟨hx.1.le, hx.2.le⟩
  have hyJ : y ∈ J := ⟨hy.1.le, hy.2.le⟩
  refine ⟨by simp only [mem_prod, hxJ, hyJ, true_and, mem_Icc], ?_, ?_, ?_⟩
  · simp only [frontier_prod_eq, closure_prod_eq, isClosed_Icc.closure_eq,
      frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1), frontier_Icc (zero_le_one : (0 : ℝ) ≤ 1),
      mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    simp [hxJ, hyJ, hx.1.ne', hx.2.ne, hy.1.ne', hy.2.ne]
  · simp only [mem_prod, mem_Icc, mem_singleton_iff, hx.2.le, and_true]
    tauto
  · simp only [mem_prod, mem_singleton_iff, Prod.mk.injEq, mem_Icc]
    tauto

theorem standardBoxBridgeLeftChart_on_openBox :
    IsOpen U₀ ∧ (0 : Q) ∈ U₀ ∧ IsOpen (standardBoxBridgeLeftChart '' U₀) ∧
      IsPLHomeomorphOn standardBoxBridgeLeftChart U₀ (standardBoxBridgeLeftChart '' U₀) ∧
      standardBoxBridgeLeftChart 0 = (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ∧
      ∀ p ∈ U₀,
        (standardBoxBridgeLeftChart p ∈ C₀ ↔ 0 ≤ p.1.2) ∧
        (standardBoxBridgeLeftChart p ∈ frontier C₀ ↔ p.1.2 = 0) ∧
        (standardBoxBridgeLeftChart p ∈ B₀ ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ 0 ≤ p.2) ∧
        (standardBoxBridgeLeftChart p ∈ B₀ ∩ frontier C₀ ↔
          p.1.1 = 0 ∧ p.1.2 = 0 ∧ 0 ≤ p.2) ∧
        (standardBoxBridgeLeftChart p ∈ A₀ ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 = 0) := by
  obtain ⟨hU, h0, hV, he⟩ := standardBoxBridge_chart_openBox standardBoxBridgeLeftChart
  refine ⟨hU, h0, hV, he, rfl, ?_⟩
  rintro ⟨⟨u, v⟩, z⟩ ⟨⟨hu, hv⟩, hz⟩
  obtain ⟨hC, hfr, hB, hA⟩ := standardBoxBridge_coordinate_memberships
    (x := z) (y := u) (t := v)
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hv1 : v ≤ 1 := by linarith [hv.2]
  have hvne : v ≠ 1 := by linarith [hv.2]
  have hvzero : v = 0 → 0 ≤ v := fun h => h.symm ▸ le_rfl
  simp only [standardBoxBridgeLeftChart_apply, hC, hfr, hB, hA, mem_inter_iff,
    hv1, hvne, or_false, and_true]
  clear hU h0 hV he hu hv hz hC hfr hB hA hv1 hvne
  tauto

theorem standardBoxBridgeRightChart_on_openBox :
    IsOpen U₀ ∧ (0 : Q) ∈ U₀ ∧ IsOpen (standardBoxBridgeRightChart '' U₀) ∧
      IsPLHomeomorphOn standardBoxBridgeRightChart U₀ (standardBoxBridgeRightChart '' U₀) ∧
      standardBoxBridgeRightChart 0 = (((0 : ℝ), (0 : ℝ)), (1 : ℝ)) ∧
      ∀ p ∈ U₀,
        (standardBoxBridgeRightChart p ∈ C₀ ↔ 0 ≤ p.1.2) ∧
        (standardBoxBridgeRightChart p ∈ frontier C₀ ↔ p.1.2 = 0) ∧
        (standardBoxBridgeRightChart p ∈ B₀ ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 ≤ 0) ∧
        (standardBoxBridgeRightChart p ∈ B₀ ∩ frontier C₀ ↔
          p.1.1 = 0 ∧ p.1.2 = 0 ∧ p.2 ≤ 0) ∧
        (standardBoxBridgeRightChart p ∈ A₀ ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.2 = 0) := by
  obtain ⟨hU, h0, hV, he⟩ := standardBoxBridge_chart_openBox standardBoxBridgeRightChart
  refine ⟨hU, h0, hV, he, by simp, ?_⟩
  rintro ⟨⟨u, v⟩, z⟩ ⟨⟨hu, hv⟩, hz⟩
  obtain ⟨hC, hfr, hB, hA⟩ := standardBoxBridge_coordinate_memberships
    (x := -z) (y := u) (t := 1 - v)
    ⟨by linarith [hz.2], by linarith [hz.1]⟩
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hv0 : 0 ≤ 1 - v := by linarith [hv.2]
  have hvne : 1 - v ≠ 0 := by linarith [hv.2]
  have hvle : 1 - v ≤ 1 ↔ 0 ≤ v := by constructor <;> intro h <;> linarith only [h]
  have hveq : 1 - v = 1 ↔ v = 0 := by constructor <;> intro h <;> linarith only [h]
  have hvzero : v = 0 → 0 ≤ v := fun h => h.symm ▸ le_rfl
  simp only [standardBoxBridgeRightChart_apply, hC, hfr, hB, hA, mem_inter_iff,
    hv0, hvne, hvle, hveq, false_or, true_and, neg_nonneg, neg_eq_zero]
  clear hU h0 hV he hu hv hz hC hfr hB hA hv0 hvne hvle hveq
  tauto

theorem standardBoxBridgeMiddleChart_on_openBox :
    IsOpen U₀ ∧ (0 : Q) ∈ U₀ ∧ IsOpen (standardBoxBridgeMiddleChart '' U₀) ∧
      IsPLHomeomorphOn standardBoxBridgeMiddleChart U₀ (standardBoxBridgeMiddleChart '' U₀) ∧
      standardBoxBridgeMiddleChart 0 = (((1 / 2 : ℝ), (0 : ℝ)), (0 : ℝ)) ∧
      ∀ p ∈ U₀,
        (standardBoxBridgeMiddleChart p ∈ C₀ ↔ 0 ≤ p.1.2) ∧
        (standardBoxBridgeMiddleChart p ∈ frontier C₀ ↔ p.1.2 = 0) ∧
        (standardBoxBridgeMiddleChart p ∈ B₀ ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2) ∧
        (standardBoxBridgeMiddleChart p ∈ B₀ ∩ frontier C₀ ↔
          p.1.1 = 0 ∧ p.1.2 = 0) ∧ standardBoxBridgeMiddleChart p ∉ A₀ := by
  obtain ⟨hU, h0, hV, he⟩ := standardBoxBridge_chart_openBox standardBoxBridgeMiddleChart
  refine ⟨hU, h0, hV, he, by simp, ?_⟩
  rintro ⟨⟨u, v⟩, z⟩ ⟨⟨hu, hv⟩, hz⟩
  obtain ⟨hC, hfr, hB, hA⟩ := standardBoxBridge_coordinate_memberships
    (x := z + 1 / 2) (y := u) (t := v)
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hv1 : v ≤ 1 := by linarith [hv.2]
  have hvne : v ≠ 1 := by linarith [hv.2]
  have hz0 : 0 ≤ z + 1 / 2 := by linarith [hz.1]
  have hzne : z + 1 / 2 ≠ 0 := by linarith [hz.1]
  have hvzero : v = 0 → 0 ≤ v := fun h => h.symm ▸ le_rfl
  simp only [standardBoxBridgeMiddleChart_apply, hC, hfr, hB, hA, mem_inter_iff,
    hv1, hvne, hz0, hzne, or_false, and_true, true_and, false_and, not_false_eq_true]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hvzero h.2⟩, h.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
