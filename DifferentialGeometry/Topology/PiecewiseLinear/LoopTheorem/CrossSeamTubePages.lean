/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossQuarterTurn
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def crossRayOf : Fin 4 → Set (ℝ × ℝ) :=
  ![crossRayPosX, crossRayPosY, crossRayNegX, crossRayNegY]

def crossDirOf : Fin 4 → ℝ × ℝ := ![(1, 0), (0, 1), (-1, 0), (0, -1)]

def crossSheetOf (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) := crossRayOf i ×ˢ Icc (0 : ℝ) 1

def crossOpenSheetOf (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  (crossRayOf i \ {((0 : ℝ), (0 : ℝ))}) ×ˢ Icc (0 : ℝ) 1

theorem crossRayOf_sdiff_eq (i : Fin 4) :
    crossRayOf i \ {((0 : ℝ), (0 : ℝ))} = (fun s : ℝ => s • crossDirOf i) '' Ioc 0 1 := by
  ext ⟨x, y⟩
  fin_cases i <;>
    simp only [crossRayOf, crossDirOf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, mem_sdiff,
      mem_crossRayPosX, mem_crossRayPosY, mem_crossRayNegX, mem_crossRayNegY,
      mem_singleton_iff, Prod.mk.injEq, mem_image, mem_Ioc, Prod.smul_mk, smul_eq_mul,
      mul_one, mul_zero, mul_neg] <;>
    constructor
  · rintro ⟨⟨⟨hx0, hx1⟩, rfl⟩, hne⟩
    exact ⟨x, ⟨lt_of_le_of_ne hx0 fun h => hne ⟨h.symm, rfl⟩, hx1⟩, rfl, rfl⟩
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl, rfl⟩
    exact ⟨⟨⟨hs0.le, hs1⟩, rfl⟩, fun h => hs0.ne' h.1⟩
  · rintro ⟨⟨rfl, hy0, hy1⟩, hne⟩
    exact ⟨y, ⟨lt_of_le_of_ne hy0 fun h => hne ⟨rfl, h.symm⟩, hy1⟩, rfl, rfl⟩
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl, rfl⟩
    exact ⟨⟨rfl, hs0.le, hs1⟩, fun h => hs0.ne' h.2⟩
  · rintro ⟨⟨⟨hx0, hx1⟩, rfl⟩, hne⟩
    refine ⟨-x, ⟨?_, by linarith⟩, neg_neg x, rfl⟩
    exact neg_pos.mpr (lt_of_le_of_ne hx1 fun h => hne ⟨h, rfl⟩)
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl, rfl⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, rfl⟩, fun h => hs0.ne' (neg_eq_zero.mp h.1)⟩
  · rintro ⟨⟨rfl, hy0, hy1⟩, hne⟩
    refine ⟨-y, ⟨?_, by linarith⟩, rfl, neg_neg y⟩
    exact neg_pos.mpr (lt_of_le_of_ne hy1 fun h => hne ⟨rfl, h⟩)
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl, rfl⟩
    exact ⟨⟨rfl, by linarith, by linarith⟩, fun h => hs0.ne' (neg_eq_zero.mp h.2)⟩

theorem crossRayOf_subset_crossingArc (i : Fin 4) :
    crossRayOf i ⊆ crossingArcX ∪ crossingArcY := by
  intro p hp
  rw [crossingArcX_eq_union, crossingArcY_eq_union]
  fin_cases i
  exacts [Or.inr (Or.inr hp), Or.inl (Or.inr hp), Or.inr (Or.inl hp), Or.inl (Or.inl hp)]

theorem crossRayOf_subset_spliceSquare (i : Fin 4) : crossRayOf i ⊆ spliceSquare := fun _ hp =>
  (crossRayOf_subset_crossingArc i hp).elim (fun h => h.1) fun h => h.1

theorem zero_mem_crossRayOf (i : Fin 4) : ((0 : ℝ), (0 : ℝ)) ∈ crossRayOf i := by
  fin_cases i
  · exact mem_crossRayPosX.mpr ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  · exact mem_crossRayPosY.mpr ⟨rfl, le_rfl, zero_le_one⟩
  · exact mem_crossRayNegX.mpr ⟨⟨by norm_num, le_rfl⟩, rfl⟩
  · exact mem_crossRayNegY.mpr ⟨rfl, by norm_num, le_rfl⟩

theorem crossOpenSheetOf_subset_crossSheetOf (i : Fin 4) :
    crossOpenSheetOf i ⊆ crossSheetOf i :=
  prod_mono sdiff_subset subset_rfl

theorem crossSheetOf_subset_spliceCylinder (i : Fin 4) : crossSheetOf i ⊆ spliceCylinder :=
  prod_mono (crossRayOf_subset_spliceSquare i) subset_rfl

theorem crossOpenSheetOf_subset_spliceCylinder (i : Fin 4) :
    crossOpenSheetOf i ⊆ spliceCylinder :=
  (crossOpenSheetOf_subset_crossSheetOf i).trans (crossSheetOf_subset_spliceCylinder i)

theorem crossSheetOf_subset_crossingFigure (i : Fin 4) : crossSheetOf i ⊆ crossingFigure :=
  prod_mono (crossRayOf_subset_crossingArc i) subset_rfl

theorem crossSheetOf_eq_union (i : Fin 4) :
    crossSheetOf i = crossOpenSheetOf i ∪ spliceCore := by
  rw [crossSheetOf, crossOpenSheetOf, spliceCore, ← union_prod, sdiff_union_self,
    union_eq_left.mpr (singleton_subset_iff.mpr (zero_mem_crossRayOf i))]

theorem disjoint_crossOpenSheetOf_spliceCore (i : Fin 4) :
    Disjoint (crossOpenSheetOf i) spliceCore := by
  rw [crossOpenSheetOf, spliceCore]
  exact disjoint_prod.mpr (Or.inl disjoint_sdiff_left)

theorem spliceCore_subset_crossSheetOf (i : Fin 4) : spliceCore ⊆ crossSheetOf i := by
  rw [crossSheetOf_eq_union]
  exact subset_union_right

theorem convex_crossOpenSheetOf (i : Fin 4) : Convex ℝ (crossOpenSheetOf i) := by
  have hmap : (fun s : ℝ => s • crossDirOf i) =
      ⇑((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (crossDirOf i)) := by
    funext s
    simp only [LinearMap.smulRight_apply, LinearMap.id_apply]
  rw [crossOpenSheetOf, crossRayOf_sdiff_eq, hmap]
  exact ((convex_Ioc 0 1).linear_image _).prod (convex_Icc 0 1)

theorem smul_crossDirOf_mem_crossOpenSheetOf (i : Fin 4) {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : (s • crossDirOf i, t) ∈ crossOpenSheetOf i := by
  refine ⟨?_, ht⟩
  rw [crossRayOf_sdiff_eq]
  exact ⟨s, ⟨hs, hs1⟩, rfl⟩

theorem mem_closure_crossOpenSheetOf {i : Fin 4} {w : (ℝ × ℝ) × ℝ} (hw : w ∈ crossSheetOf i) :
    w ∈ closure (crossOpenSheetOf i) := by
  rw [crossSheetOf_eq_union] at hw
  rcases hw with hw | hw
  · exact subset_closure hw
  · obtain ⟨hw1, hw2⟩ := hw
    rw [crossOpenSheetOf, closure_prod_eq]
    refine ⟨?_, subset_closure hw2⟩
    rw [mem_singleton_iff.mp hw1, crossRayOf_sdiff_eq]
    have hcont : Continuous fun s : ℝ => s • crossDirOf i := continuous_id.smul continuous_const
    have h0 : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
      rw [closure_Ioc zero_ne_one]
      exact ⟨le_rfl, zero_le_one⟩
    have h := map_mem_closure hcont h0 (mapsTo_image _ _)
    simpa only [zero_smul, Prod.zero_eq_mk] using h

theorem exists_mem_crossOpenSheetOf {w : (ℝ × ℝ) × ℝ} (hw : w ∈ crossingFigure)
    (hwc : w ∉ spliceCore) : ∃ i, w ∈ crossOpenSheetOf i := by
  obtain ⟨hw1, hw2⟩ := hw
  have hne : w.1 ∉ ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := fun h => hwc ⟨h, hw2⟩
  rw [crossingArcX_eq_union, crossingArcY_eq_union] at hw1
  rcases hw1 with (h | h) | (h | h)
  exacts [⟨3, ⟨h, hne⟩, hw2⟩, ⟨1, ⟨h, hne⟩, hw2⟩, ⟨2, ⟨h, hne⟩, hw2⟩, ⟨0, ⟨h, hne⟩, hw2⟩]

theorem crossRayOf_inter_subset {i j : Fin 4} (hij : i ≠ j) :
    crossRayOf i ∩ crossRayOf j ⊆ {((0 : ℝ), (0 : ℝ))} := by
  rintro ⟨x, y⟩ ⟨hi, hj⟩
  rw [mem_singleton_iff, Prod.mk.injEq]
  fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
    simp only [crossRayOf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, mem_crossRayPosX, mem_crossRayPosY,
      mem_crossRayNegX, mem_crossRayNegY] at hi hj <;>
    obtain ⟨hi1, hi2⟩ := hi <;> obtain ⟨hj1, hj2⟩ := hj <;>
    constructor <;> linarith [hi1, hi2, hj1, hj2]

theorem crossSheetOf_inter_subset {i j : Fin 4} (hij : i ≠ j) :
    crossSheetOf i ∩ crossSheetOf j ⊆ spliceCore := by
  rintro w ⟨⟨hi, ht⟩, hj, -⟩
  exact ⟨crossRayOf_inter_subset hij ⟨hi, hj⟩, ht⟩

theorem isHPolytope_crossSheetOf (i : Fin 4) : IsHPolytope (crossSheetOf i) := by
  fin_cases i
  · exact (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).prod isHPolytope_Icc
  · exact ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).prod isHPolytope_Icc
  · exact (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).prod isHPolytope_Icc
  · exact ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).prod isHPolytope_Icc

theorem isHPolytope_spliceCore : IsHPolytope spliceCore := by
  rw [spliceCore, ← singleton_prod_singleton]
  exact ((isHPolytope_singleton_real 0).prod (isHPolytope_singleton_real 0)).prod isHPolytope_Icc

theorem crossQuarterTurn_smul_crossDirOf (i : Fin 4) (s t : ℝ) :
    crossQuarterTurn (s • crossDirOf i, t) = (s • crossDirOf (i + 1), t) := by
  fin_cases i <;>
    simp only [crossQuarterTurn, crossDirOf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Fin.reduceAdd, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, mul_neg, neg_zero,
      neg_neg]

theorem crossOpenSheetOf_eq_image (i : Fin 4) :
    crossOpenSheetOf i =
      (fun p : ℝ × ℝ => (p.1 • crossDirOf i, p.2)) '' (Ioc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  rw [crossOpenSheetOf, crossRayOf_sdiff_eq, ← image_id (Icc (0 : ℝ) 1), prod_image_image_eq,
    image_id]
  rfl

theorem image_crossQuarterTurn_crossOpenSheetOf (i : Fin 4) :
    crossQuarterTurn '' crossOpenSheetOf i = crossOpenSheetOf (i + 1) := by
  rw [crossOpenSheetOf_eq_image, crossOpenSheetOf_eq_image, image_image]
  refine image_congr fun p _ => ?_
  exact crossQuarterTurn_smul_crossDirOf i p.1 p.2

theorem image_crossQuarterTurn_crossSheetOf (i : Fin 4) :
    crossQuarterTurn '' crossSheetOf i = crossSheetOf (i + 1) := by
  rw [crossSheetOf_eq_union, crossSheetOf_eq_union, image_union,
    image_crossQuarterTurn_crossOpenSheetOf, image_crossQuarterTurn_spliceCore]

theorem continuousOn_invFunOn_of_isCompact_of_forall_eq {α β : Type*} [TopologicalSpace α]
    [Nonempty α] [TopologicalSpace β] [T2Space β] {f : α → β} {K : Set α} {W : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hW : W ⊆ f '' K)
    (huniq : ∀ x ∈ K, ∀ y ∈ K, f x = f y → f x ∈ W → x = y) :
    ContinuousOn (Function.invFunOn f K) W := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  refine ⟨f '' (C ∩ K),
    ((hK.inter_left hC).image_of_continuousOn (hf.mono inter_subset_right)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyW⟩
    have hex : ∃ a ∈ K, f a = y := hW hyW
    exact ⟨⟨_, ⟨hy, Function.invFunOn_mem hex⟩, Function.invFunOn_eq hex⟩, hyW⟩
  · rintro ⟨⟨x, ⟨hxC, hxK⟩, rfl⟩, hyW⟩
    have hex : ∃ a ∈ K, f a = f x := ⟨x, hxK, rfl⟩
    have heq : Function.invFunOn f K (f x) = x :=
      huniq _ (Function.invFunOn_mem hex) x hxK (Function.invFunOn_eq hex)
        (by rw [Function.invFunOn_eq hex]; exact hyW)
    refine ⟨?_, hyW⟩
    rw [mem_preimage, heq]
    exact hxC

theorem exists_mem_nhds_inter_image_subset_image_inter {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T2Space β] {f : α → β} {K : Set α} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hinj : InjOn f K) {q : α} (hq : q ∈ K) {B : Set α}
    (hB : B ∈ 𝓝 q) : ∃ N ∈ 𝓝 (f q), N ∩ f '' K ⊆ f '' (K ∩ B) := by
  refine ⟨(f '' (K \ interior B))ᶜ, IsOpen.mem_nhds ((hK.diff isOpen_interior).image_of_continuousOn
    (hf.mono sdiff_subset)).isClosed.isOpen_compl ?_, ?_⟩
  · rintro ⟨x, ⟨hxK, hxB⟩, hfx⟩
    apply hxB
    rw [hinj hxK hq hfx]
    exact mem_interior_iff_mem_nhds.mpr hB
  · rintro y ⟨hyN, x, hxK, rfl⟩
    refine ⟨x, ⟨hxK, ?_⟩, rfl⟩
    by_contra hxB
    exact hyN ⟨x, ⟨hxK, fun h => hxB (interior_subset h)⟩, rfl⟩

theorem exists_mem_nhds_forall_mem_of_isCompact {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T2Space β] {f : α → β} {K O : Set α} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hO : IsOpen O) {y : β} (hy : ∀ x ∈ K, f x = y → x ∈ O) :
    ∃ N ∈ 𝓝 y, ∀ x ∈ K, f x ∈ N → x ∈ O := by
  refine ⟨(f '' (K \ O))ᶜ, IsOpen.mem_nhds
    ((hK.diff hO).image_of_continuousOn (hf.mono sdiff_subset)).isClosed.isOpen_compl ?_, ?_⟩
  · rintro ⟨x, ⟨hxK, hxO⟩, hfx⟩
    exact hxO (hy x hxK hfx)
  · intro x hxK hxN
    by_contra hxO
    exact hxN ⟨x, ⟨hxK, hxO⟩, rfl⟩

def crossSeamPage {X : Type*} (chart : (ℝ × ℝ) × ℝ → X) (f : EuclideanSpace ℝ (Fin 2) → X)
    (Dom : Set (EuclideanSpace ℝ (Fin 2))) (i : Fin 4) : Set (EuclideanSpace ℝ (Fin 2)) :=
  closure (Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i))

section Pages

variable {X : Type*} [TopologicalSpace X] [T2Space X] {chart : (ℝ × ℝ) × ℝ → X}
  {f : EuclideanSpace ℝ (Fin 2) → X} {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}

omit [TopologicalSpace X] [T2Space X] in
theorem crossSeamPage_subset (hDom : IsClosed Dom) (i : Fin 4) :
    crossSeamPage chart f Dom i ⊆ Dom :=
  closure_minimal inter_subset_left hDom

theorem crossSeamPage_subset_preimage (hchart : ContinuousOn chart spliceCylinder)
    (hDom : IsClosed Dom) (hf : ContinuousOn f Dom) (i : Fin 4) :
    crossSeamPage chart f Dom i ⊆ Dom ∩ f ⁻¹' (chart '' crossSheetOf i) :=
  closure_minimal
    (inter_subset_inter_right _ (preimage_mono (image_mono
      (crossOpenSheetOf_subset_crossSheetOf i))))
    (hf.preimage_isClosed_of_isClosed hDom ((isHPolytope_crossSheetOf i).1.image_of_continuousOn
      (hchart.mono (crossSheetOf_subset_spliceCylinder i))).isClosed)

theorem exists_mem_crossSeamPage_apply_eq (hchart : ContinuousOn chart spliceCylinder)
    (hDom : IsCompact Dom) (hf : ContinuousOn f Dom) {i : Fin 4}
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom) {w : (ℝ × ℝ) × ℝ}
    (hw : w ∈ crossSheetOf i) : ∃ x ∈ crossSeamPage chart f Dom i, f x = chart w := by
  have hZDom : crossSeamPage chart f Dom i ⊆ Dom := crossSeamPage_subset hDom.isClosed i
  have hZc : IsCompact (crossSeamPage chart f Dom i) :=
    hDom.of_isClosed_subset isClosed_closure hZDom
  have hfZ : IsClosed (f '' crossSeamPage chart f Dom i) :=
    (hZc.image_of_continuousOn (hf.mono hZDom)).isClosed
  have hWZ : chart '' crossOpenSheetOf i ⊆ f '' crossSeamPage chart f Dom i := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj hy
    exact ⟨x, subset_closure ⟨hx, hy⟩, rfl⟩
  have hcl : closure (crossOpenSheetOf i) ⊆ spliceCylinder :=
    closure_minimal (crossOpenSheetOf_subset_spliceCylinder i)
      isHPolytope_spliceCylinder.1.isClosed
  have h1 : chart w ∈ closure (chart '' crossOpenSheetOf i) :=
    (hchart.mono hcl).image_closure ⟨w, mem_closure_crossOpenSheetOf hw, rfl⟩
  exact closure_minimal hWZ hfZ h1

theorem notMem_crossSeamPage_of_forall_mem (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hf : ContinuousOn f Dom) {i : Fin 4}
    {B : Set ((ℝ × ℝ) × ℝ)} (hB : IsOpen B) {O₁ O₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (hO₂ : IsOpen O₂) (hO : Disjoint O₁ O₂)
    (hown : ∀ x ∈ Dom, f x ∈ chart '' (crossOpenSheetOf i ∩ B) → x ∈ O₁)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Dom) (hxO₂ : x ∈ O₂) {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ spliceCylinder) (hpB : p ∈ B) (hfx : f x = chart p) :
    x ∉ crossSeamPage chart f Dom i := by
  intro hmem
  obtain ⟨N, hN, hNsub⟩ := exists_mem_nhds_inter_image_subset_image_inter
    isHPolytope_spliceCylinder.1 hchart hinjc hp (hB.mem_nhds hpB)
  have hpre : f ⁻¹' N ∈ 𝓝[Dom] x := hf x hx (by rw [hfx]; exact hN)
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨z, ⟨hzV, hzO₂⟩, hzDom, hzW⟩ :=
    mem_closure_iff_nhds.mp hmem (V ∩ O₂) (Filter.inter_mem hV (hO₂.mem_nhds hxO₂))
  obtain ⟨q, hq, hqz⟩ := hzW
  have hqcyl : q ∈ spliceCylinder := crossOpenSheetOf_subset_spliceCylinder i hq
  have hzN : f z ∈ N := hVsub ⟨hzV, hzDom⟩
  obtain ⟨q', ⟨hq'cyl, hq'B⟩, hq'z⟩ := hNsub ⟨hzN, q, hqcyl, hqz⟩
  have hqq : q = q' := hinjc hqcyl hq'cyl (hqz.trans hq'z.symm)
  have hqB : q ∈ B := by rw [hqq]; exact hq'B
  exact disjoint_left.mp hO (hown z hzDom ⟨q, ⟨hq, hqB⟩, hqz⟩) hzO₂

theorem exists_forall_mem_or_forall_mem_of_crossOpenSheetOf
    (hchart : ContinuousOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom) {p₀ : (ℝ × ℝ) × ℝ}
    (hp₀ : p₀ ∈ spliceCylinder) {O₁ O₂ : Set (EuclideanSpace ℝ (Fin 2))} (hO₁ : IsOpen O₁)
    (hO₂ : IsOpen O₂) (hO : Disjoint O₁ O₂) (hpre : ∀ x ∈ Dom, f x = chart p₀ → x ∈ O₁ ∪ O₂) :
    ∃ δ > 0, (∀ x ∈ Dom, f x ∈ chart '' (crossOpenSheetOf i ∩ Metric.ball p₀ δ) → x ∈ O₁) ∨
      (∀ x ∈ Dom, f x ∈ chart '' (crossOpenSheetOf i ∩ Metric.ball p₀ δ) → x ∈ O₂) := by
  obtain ⟨N, hN, hNsub⟩ := exists_mem_nhds_forall_mem_of_isCompact hDom hf (hO₁.union hO₂) hpre
  have hcw : chart ⁻¹' N ∈ 𝓝[spliceCylinder] p₀ := hchart p₀ hp₀ hN
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hcw
  refine ⟨δ, hδ, ?_⟩
  have hRcyl : crossOpenSheetOf i ∩ Metric.ball p₀ δ ⊆ spliceCylinder :=
    inter_subset_left.trans (crossOpenSheetOf_subset_spliceCylinder i)
  have hRconn : IsPreconnected (crossOpenSheetOf i ∩ Metric.ball p₀ δ) :=
    ((convex_crossOpenSheetOf i).inter (convex_ball p₀ δ)).isPreconnected
  have hcont : ContinuousOn (Function.invFunOn f Dom ∘ chart)
      (crossOpenSheetOf i ∩ Metric.ball p₀ δ) :=
    (continuousOn_invFunOn_of_isCompact_of_forall_eq hDom hf hsurj huniq).comp
      (hchart.mono hRcyl) fun q hq => ⟨q, hq.1, rfl⟩
  have hXeq : Dom ∩ f ⁻¹' (chart '' (crossOpenSheetOf i ∩ Metric.ball p₀ δ)) =
      (Function.invFunOn f Dom ∘ chart) '' (crossOpenSheetOf i ∩ Metric.ball p₀ δ) := by
    ext x
    constructor
    · rintro ⟨hx, q, hq, hqx⟩
      refine ⟨q, hq, ?_⟩
      have hex : ∃ a ∈ Dom, f a = chart q := ⟨x, hx, hqx.symm⟩
      exact huniq _ (Function.invFunOn_mem hex) x hx ((Function.invFunOn_eq hex).trans hqx)
        (by rw [Function.invFunOn_eq hex]; exact ⟨q, hq.1, rfl⟩)
    · rintro ⟨q, hq, rfl⟩
      have hex : ∃ a ∈ Dom, f a = chart q := hsurj ⟨q, hq.1, rfl⟩
      exact ⟨Function.invFunOn_mem hex, q, hq, (Function.invFunOn_eq hex).symm⟩
  have hXconn : IsPreconnected
      (Dom ∩ f ⁻¹' (chart '' (crossOpenSheetOf i ∩ Metric.ball p₀ δ))) := by
    rw [hXeq]
    exact hRconn.image _ hcont
  have hXsub : Dom ∩ f ⁻¹' (chart '' (crossOpenSheetOf i ∩ Metric.ball p₀ δ)) ⊆ O₁ ∪ O₂ := by
    rintro x ⟨hx, q, hq, hqx⟩
    refine hNsub x hx ?_
    rw [← hqx]
    exact hδsub ⟨hq.2, hRcyl hq⟩
  rcases hXconn.subset_or_subset hO₁ hO₂ hO hXsub with h | h
  · exact Or.inl fun x hx hfx => h ⟨hx, hfx⟩
  · exact Or.inr fun x hx hfx => h ⟨hx, hfx⟩

end Pages

section Class

variable {X : Type*} [TopologicalSpace X] [T2Space X] {chart : (ℝ × ℝ) × ℝ → X}
  {f : EuclideanSpace ℝ (Fin 2) → X} {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}

omit [TopologicalSpace X] [T2Space X] in
theorem exists_eq_invFunOn_of_mem_of_crossSeam
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ J₁) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      x = Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) := by
  have hxJ : x ∈ J₁ ∪ J₂ := Or.inl hx
  rw [← hJ] at hxJ
  obtain ⟨w, ⟨hw1, hw2⟩, hwx⟩ := hxJ.2
  have hw : w = (((0 : ℝ), (0 : ℝ)), w.2) := Prod.ext (mem_singleton_iff.mp hw1) rfl
  have hex : ∃ a ∈ J₁, f a = chart (((0 : ℝ), (0 : ℝ)), w.2) :=
    hsurj₁ ⟨(((0 : ℝ), (0 : ℝ)), w.2), ⟨mem_singleton _, hw2⟩, rfl⟩
  refine ⟨w.2, hw2, hinj₁ hx (Function.invFunOn_mem hex) ?_⟩
  rw [Function.invFunOn_eq hex, ← hw, hwx]

theorem crossSeamPage_class (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hJ₁ : IsClosed J₁) (hJ₂ : IsClosed J₂)
    (hJJ : Disjoint J₁ J₂) (hinj₁ : InjOn f J₁) (hinj₂ : InjOn f J₂)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) (hsurj₂ : chart '' spliceCore ⊆ f '' J₂)
    {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom) :
    (J₁ ⊆ crossSeamPage chart f Dom i ∧ Disjoint J₂ (crossSeamPage chart f Dom i)) ∨
      (J₂ ⊆ crossSeamPage chart f Dom i ∧ Disjoint J₁ (crossSeamPage chart f Dom i)) := by
  have hJ₁Dom : J₁ ⊆ Dom := (subset_union_left.trans hJ.symm.subset).trans inter_subset_left
  have hJ₂Dom : J₂ ⊆ Dom := (subset_union_right.trans hJ.symm.subset).trans inter_subset_left
  have hcore : ∀ t ∈ Icc (0 : ℝ) 1, (((0 : ℝ), (0 : ℝ)), t) ∈ spliceCore :=
    fun t ht => ⟨rfl, ht⟩
  have hj₁ : ∀ t ∈ Icc (0 : ℝ) 1,
      Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ J₁ ∧
        f (Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t))) =
          chart (((0 : ℝ), (0 : ℝ)), t) :=
    fun t ht => Function.invFunOn_pos (hsurj₁ ⟨_, hcore t ht, rfl⟩)
  have hj₂ : ∀ t ∈ Icc (0 : ℝ) 1,
      Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ J₂ ∧
        f (Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t))) =
          chart (((0 : ℝ), (0 : ℝ)), t) :=
    fun t ht => Function.invFunOn_pos (hsurj₂ ⟨_, hcore t ht, rfl⟩)
  have hcurve : ContinuousOn (fun t : ℝ => chart (((0 : ℝ), (0 : ℝ)), t)) (Icc 0 1) :=
    hchart.comp (continuous_const.prodMk continuous_id).continuousOn
      fun t ht => spliceCore_subset_spliceCylinder (hcore t ht)
  have hj₁c : ContinuousOn
      (fun t : ℝ => Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t))) (Icc 0 1) :=
    (continuousOn_invFunOn_image_of_isCompact (hDom.of_isClosed_subset hJ₁ hJ₁Dom)
      (hf.mono hJ₁Dom) hinj₁).comp hcurve fun t ht => hsurj₁ ⟨_, hcore t ht, rfl⟩
  have hj₂c : ContinuousOn
      (fun t : ℝ => Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t))) (Icc 0 1) :=
    (continuousOn_invFunOn_image_of_isCompact (hDom.of_isClosed_subset hJ₂ hJ₂Dom)
      (hf.mono hJ₂Dom) hinj₂).comp hcurve fun t ht => hsurj₂ ⟨_, hcore t ht, rfl⟩
  have hpre : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Dom, f x = chart (((0 : ℝ), (0 : ℝ)), t) →
      x = Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∨
        x = Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) := by
    intro t ht x hx hfx
    have hxJ : x ∈ Dom ∩ f ⁻¹' (chart '' spliceCore) := ⟨hx, _, hcore t ht, hfx.symm⟩
    rw [hJ] at hxJ
    rcases hxJ with h | h
    · exact Or.inl (hinj₁ h (hj₁ t ht).1 (hfx.trans (hj₁ t ht).2.symm))
    · exact Or.inr (hinj₂ h (hj₂ t ht).1 (hfx.trans (hj₂ t ht).2.symm))
  have hstep1 : ∀ t ∈ Icc (0 : ℝ) 1,
      Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ crossSeamPage chart f Dom i ∨
        Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈
          crossSeamPage chart f Dom i := by
    intro t ht
    obtain ⟨x, hxZ, hfx⟩ := exists_mem_crossSeamPage_apply_eq hchart hDom hf hsurj
      (spliceCore_subset_crossSheetOf i (hcore t ht))
    rcases hpre t ht x (crossSeamPage_subset hDom.isClosed i hxZ) hfx with h | h
    · rw [h] at hxZ
      exact Or.inl hxZ
    · rw [h] at hxZ
      exact Or.inr hxZ
  have hstep2 : ∀ t₀ ∈ Icc (0 : ℝ) 1, ∃ δ > 0,
      (∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ →
        Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈
            crossSeamPage chart f Dom i ∧
          Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∉
            crossSeamPage chart f Dom i) ∨
      (∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ →
        Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈
            crossSeamPage chart f Dom i ∧
          Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∉
            crossSeamPage chart f Dom i) := by
    intro t₀ ht₀
    have hne : Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t₀)) ≠
        Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t₀)) := fun h =>
      disjoint_left.mp hJJ (hj₁ t₀ ht₀).1 (h ▸ (hj₂ t₀ ht₀).1)
    obtain ⟨O₁, O₂, hO₁, hO₂, hx₁, hx₂, hO⟩ := t2_separation hne
    obtain ⟨δ₁, hδ₁, halt⟩ := exists_forall_mem_or_forall_mem_of_crossOpenSheetOf hchart hDom hf
      huniq hsurj (spliceCore_subset_spliceCylinder (hcore t₀ ht₀)) hO₁ hO₂ hO
      fun x hx hfx => (hpre t₀ ht₀ x hx hfx).elim (fun h => Or.inl (h ▸ hx₁))
        fun h => Or.inr (h ▸ hx₂)
    have hev₁ : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] t₀,
        Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ O₁ :=
      hj₁c t₀ ht₀ (hO₁.mem_nhds hx₁)
    have hev₂ : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] t₀,
        Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ O₂ :=
      hj₂c t₀ ht₀ (hO₂.mem_nhds hx₂)
    obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.mem_nhdsWithin_iff.mp (hev₁.and hev₂)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    have hball : ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < min δ₁ δ₂ →
        (((0 : ℝ), (0 : ℝ)), t) ∈ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) δ₁ ∧
          Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ O₁ ∧
            Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ O₂ := by
      intro t ht htt
      refine ⟨?_, hδ₂sub ⟨?_, ht⟩⟩
      · rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
        exact max_lt hδ₁ (htt.trans_le (min_le_left _ _))
      · rw [Metric.mem_ball, Real.dist_eq]
        exact htt.trans_le (min_le_right _ _)
    rcases halt with hown | hown
    · left
      intro t ht htt
      obtain ⟨hb, -, h₂⟩ := hball t ht htt
      have hnot := notMem_crossSeamPage_of_forall_mem hchart hinjc hf Metric.isOpen_ball hO₂ hO
        hown (hJ₂Dom (hj₂ t ht).1) h₂ (spliceCore_subset_spliceCylinder (hcore t ht)) hb
        (hj₂ t ht).2
      exact ⟨(hstep1 t ht).resolve_right hnot, hnot⟩
    · right
      intro t ht htt
      obtain ⟨hb, h₁, -⟩ := hball t ht htt
      have hnot := notMem_crossSeamPage_of_forall_mem hchart hinjc hf Metric.isOpen_ball hO₁
        hO.symm hown (hJ₁Dom (hj₁ t ht).1) h₁ (spliceCore_subset_spliceCylinder (hcore t ht))
        hb (hj₁ t ht).2
      exact ⟨(hstep1 t ht).resolve_left hnot, hnot⟩
  have hopen : ∀ P : ℝ → Prop,
      IsOpen {t : ℝ | ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, |s - t| < δ → P s} := by
    intro P
    rw [Metric.isOpen_iff]
    rintro t ⟨δ, hδ, hP⟩
    refine ⟨δ, hδ, fun t' ht' => ⟨δ - dist t' t, sub_pos.mpr ht', fun s hs hst => hP s hs ?_⟩⟩
    linarith [abs_sub_le s t' t, Real.dist_eq t' t]
  obtain hu | hv := isPreconnected_iff_subset_of_disjoint.mp isPreconnected_Icc
    {t : ℝ | ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, |s - t| < δ →
      Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), s)) ∈ crossSeamPage chart f Dom i ∧
        Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), s)) ∉ crossSeamPage chart f Dom i}
    {t : ℝ | ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, |s - t| < δ →
      Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), s)) ∈ crossSeamPage chart f Dom i ∧
        Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), s)) ∉ crossSeamPage chart f Dom i}
    (hopen _) (hopen _)
    (fun t ht => by
      obtain ⟨δ, hδ, h | h⟩ := hstep2 t ht
      exacts [Or.inl ⟨δ, hδ, h⟩, Or.inr ⟨δ, hδ, h⟩])
    (by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨ht, ⟨δ, hδ, hu⟩, ⟨δ', hδ', hv⟩⟩
      exact (hu t ht (by simpa using hδ)).2 (hv t ht (by simpa using hδ')).1)
  · left
    have hall : ∀ t ∈ Icc (0 : ℝ) 1,
        Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ crossSeamPage chart f Dom i ∧
          Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∉
            crossSeamPage chart f Dom i := fun t ht => by
      obtain ⟨δ, hδ, h⟩ := hu ht
      exact h t ht (by simpa using hδ)
    refine ⟨fun x hx => ?_, disjoint_left.mpr fun x hx hxZ => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := exists_eq_invFunOn_of_mem_of_crossSeam hJ hinj₁ hsurj₁ hx
      exact (hall t ht).1
    · have hJ' : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₂ ∪ J₁ := by rw [hJ, union_comm]
      obtain ⟨t, ht, rfl⟩ := exists_eq_invFunOn_of_mem_of_crossSeam hJ' hinj₂ hsurj₂ hx
      exact (hall t ht).2 hxZ
  · right
    have hall : ∀ t ∈ Icc (0 : ℝ) 1,
        Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) ∈ crossSeamPage chart f Dom i ∧
          Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∉
            crossSeamPage chart f Dom i := fun t ht => by
      obtain ⟨δ, hδ, h⟩ := hv ht
      exact h t ht (by simpa using hδ)
    refine ⟨fun x hx => ?_, disjoint_left.mpr fun x hx hxZ => ?_⟩
    · have hJ' : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₂ ∪ J₁ := by rw [hJ, union_comm]
      obtain ⟨t, ht, rfl⟩ := exists_eq_invFunOn_of_mem_of_crossSeam hJ' hinj₂ hsurj₂ hx
      exact (hall t ht).1
    · obtain ⟨t, ht, rfl⟩ := exists_eq_invFunOn_of_mem_of_crossSeam hJ hinj₁ hsurj₁ hx
      exact (hall t ht).2 hxZ

end Class

theorem crossOpenSheetOf_eq_sdiff (i : Fin 4) :
    crossOpenSheetOf i = crossSheetOf i \ spliceCore := by
  rw [crossSheetOf_eq_union, union_sdiff_right,
    (disjoint_crossOpenSheetOf_spliceCore i).sdiff_eq_left]

theorem zero_mem_closure_crossRayOf_sdiff (i : Fin 4) :
    ((0 : ℝ), (0 : ℝ)) ∈ closure (crossRayOf i \ {((0 : ℝ), (0 : ℝ))}) := by
  rw [crossRayOf_sdiff_eq]
  have hcont : Continuous fun s : ℝ => s • crossDirOf i := continuous_id.smul continuous_const
  have h0 : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have h := map_mem_closure hcont h0 (mapsTo_image _ _)
  simpa only [zero_smul, Prod.zero_eq_mk] using h

theorem IsPLBall.exists_isOpen_isPreconnected_inter_interior
    {Dom : Set (EuclideanSpace ℝ (Fin 2))} (hDom : IsPLBall 2 Dom) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ Dom) {V₀ : Set (EuclideanSpace ℝ (Fin 2))} (hV₀ : V₀ ∈ 𝓝 x) :
    ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧ x ∈ V ∧ V ⊆ V₀ ∧
      IsPreconnected (V ∩ interior Dom) := by
  obtain ⟨φ, hφ⟩ := hDom
  have hφc : ContinuousOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hφ.isPiecewiseAffineOn.continuousOn
  have hinv : ContinuousOn (Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) Dom := by
    have h := continuousOn_invFunOn_image_of_isCompact (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)) hφc
      hφ.bijOn.injOn
    rwa [hφ.bijOn.image_eq] at h
  have hxex : ∃ a ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), φ a = x := hφ.bijOn.surjOn hx
  obtain ⟨hy, hφy⟩ := Function.invFunOn_pos hxex
  have hcw : φ ⁻¹' interior V₀ ∈
      𝓝[Convexity.StdSimplex.coordinateSet ℝ (Fin 3)] Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x :=
    hφc _ hy (by rw [hφy]; exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hV₀))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hcw
  obtain ⟨V₁, hV₁, hV₁eq⟩ := continuousOn_iff'.mp hinv
    (Metric.ball (Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x) r) Metric.isOpen_ball
  refine ⟨V₁ ∩ interior V₀, hV₁.inter isOpen_interior, ⟨?_, ?_⟩,
    inter_subset_right.trans interior_subset, ?_⟩
  · have hxmem : x ∈ Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ⁻¹'
        Metric.ball (Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x) r ∩ Dom :=
      ⟨Metric.mem_ball_self hr, hx⟩
    rw [hV₁eq] at hxmem
    exact hxmem.1
  · exact mem_interior_iff_mem_nhds.mpr hV₀
  · have hint : φ '' openSimplex (stdVertices 1) = interior Dom :=
      hφ.image_openSimplex_eq_interior
    have heq : (V₁ ∩ interior V₀) ∩ interior Dom =
        φ '' (openSimplex (stdVertices 1) ∩
          Metric.ball (Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x) r) := by
      ext z
      constructor
      · rintro ⟨⟨hzV₁, -⟩, hzint⟩
        have hzDom : z ∈ Dom := interior_subset hzint
        rw [← hint] at hzint
        obtain ⟨w, hw, rfl⟩ := hzint
        have hwS : w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := openSimplex_stdVertices_subset_stdSimplex hw
        have hball : φ w ∈ Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ⁻¹'
            Metric.ball (Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x) r ∩ Dom := by
          rw [hV₁eq]
          exact ⟨hzV₁, hzDom⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        have := hball.1
        rwa [mem_preimage, hφ.bijOn.injOn.leftInvOn_invFunOn hwS] at this
      · rintro ⟨w, ⟨hw, hwr⟩, rfl⟩
        have hwS : w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := openSimplex_stdVertices_subset_stdSimplex hw
        have hφwDom : φ w ∈ Dom := hφ.bijOn.mapsTo hwS
        refine ⟨⟨?_, ?_⟩, hint ▸ ⟨w, hw, rfl⟩⟩
        · have hmem : φ w ∈ Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ⁻¹'
              Metric.ball (Function.invFunOn φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x) r ∩ Dom := by
            refine ⟨?_, hφwDom⟩
            rw [mem_preimage, hφ.bijOn.injOn.leftInvOn_invFunOn hwS]
            exact hwr
          rw [hV₁eq] at hmem
          exact hmem.1
        · exact hrsub ⟨hwr, hwS⟩
    rw [heq]
    exact ((convex_openSimplex _).inter (convex_ball _ _)).isPreconnected.image _
      (hφc.mono (inter_subset_left.trans openSimplex_stdVertices_subset_stdSimplex))

section Structure

variable {X : Type*} [TopologicalSpace X] [T2Space X] {chart : (ℝ × ℝ) × ℝ → X}
  {f : EuclideanSpace ℝ (Fin 2) → X} {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}

omit [TopologicalSpace X] [T2Space X] in
theorem mem_of_apply_mem_image_of_injOn (hinjc : InjOn chart spliceCylinder)
    {S : Set ((ℝ × ℝ) × ℝ)} (hS : S ⊆ spliceCylinder) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ spliceCylinder) (h : chart q ∈ chart '' S) : q ∈ S := by
  obtain ⟨q', hq', heq⟩ := h
  rwa [← hinjc (hS hq') hq heq]

omit [TopologicalSpace X] [T2Space X] in
theorem eq_invFunOn_or_eq_invFunOn_of_crossSeam
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁) (hinj₂ : InjOn f J₂)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) (hsurj₂ : chart '' spliceCore ⊆ f '' J₂)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Dom)
    (hfx : f x = chart (((0 : ℝ), (0 : ℝ)), t)) :
    x = Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t)) ∨
      x = Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t)) := by
  have hcore : (((0 : ℝ), (0 : ℝ)), t) ∈ spliceCore := ⟨mem_singleton _, ht⟩
  have hxJ : x ∈ Dom ∩ f ⁻¹' (chart '' spliceCore) := ⟨hx, _, hcore, hfx.symm⟩
  rw [hJ] at hxJ
  rcases hxJ with h | h
  · have hex := hsurj₁ ⟨_, hcore, rfl⟩
    exact Or.inl (hinj₁ h (Function.invFunOn_mem hex) (hfx.trans (Function.invFunOn_eq hex).symm))
  · have hex := hsurj₂ ⟨_, hcore, rfl⟩
    exact Or.inr (hinj₂ h (Function.invFunOn_mem hex) (hfx.trans (Function.invFunOn_eq hex).symm))

theorem forall_mem_of_subset_crossSeamPage (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁) (hinj₂ : InjOn f J₂)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) (hsurj₂ : chart '' spliceCore ⊆ f '' J₂)
    {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom)
    (hclass : J₁ ⊆ crossSeamPage chart f Dom i) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    {O₁ O₂ : Set (EuclideanSpace ℝ (Fin 2))} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hO : Disjoint O₁ O₂)
    (hx₁ : Function.invFunOn f J₁ (chart (((0 : ℝ), (0 : ℝ)), t₀)) ∈ O₁)
    (hx₂ : Function.invFunOn f J₂ (chart (((0 : ℝ), (0 : ℝ)), t₀)) ∈ O₂) :
    ∃ δ > 0, ∀ x ∈ Dom, f x ∈ chart '' (crossOpenSheetOf i ∩
      Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) δ) → x ∈ O₁ := by
  have hcore : (((0 : ℝ), (0 : ℝ)), t₀) ∈ spliceCore := ⟨mem_singleton _, ht₀⟩
  obtain ⟨δ, hδ, halt⟩ := exists_forall_mem_or_forall_mem_of_crossOpenSheetOf hchart hDom hf
    huniq hsurj (spliceCore_subset_spliceCylinder hcore) hO₁ hO₂ hO
    fun x hx hfx => (eq_invFunOn_or_eq_invFunOn_of_crossSeam hJ hinj₁ hinj₂ hsurj₁ hsurj₂ ht₀ hx
      hfx).elim (fun h => Or.inl (h ▸ hx₁)) fun h => Or.inr (h ▸ hx₂)
  refine ⟨δ, hδ, ?_⟩
  rcases halt with hown | hown
  · exact hown
  · exfalso
    have hex := hsurj₁ ⟨_, hcore, rfl⟩
    have hJ₁Dom : J₁ ⊆ Dom := (subset_union_left.trans hJ.symm.subset).trans inter_subset_left
    exact notMem_crossSeamPage_of_forall_mem hchart hinjc hf Metric.isOpen_ball hO₁ hO.symm hown
      (hJ₁Dom (Function.invFunOn_mem hex)) hx₁ (spliceCore_subset_spliceCylinder hcore)
      (Metric.mem_ball_self hδ) (Function.invFunOn_eq hex) (hclass (Function.invFunOn_mem hex))

theorem crossSeamPage_eq_union (hchart : ContinuousOn chart spliceCylinder)
    (hDom : IsClosed Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) {i : Fin 4}
    (hZ₁ : J₁ ⊆ crossSeamPage chart f Dom i) (hZ₂ : Disjoint J₂ (crossSeamPage chart f Dom i)) :
    crossSeamPage chart f Dom i = (Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i)) ∪ J₁ := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨hxDom, hxS⟩ := crossSeamPage_subset_preimage hchart hDom hf i hx
    rw [crossSheetOf_eq_union, image_union] at hxS
    rcases hxS with h | h
    · exact Or.inl ⟨hxDom, h⟩
    · have hxJ : x ∈ Dom ∩ f ⁻¹' (chart '' spliceCore) := ⟨hxDom, h⟩
      rw [hJ] at hxJ
      rcases hxJ with h' | h'
      · exact Or.inr h'
      · exact absurd hx (disjoint_left.mp hZ₂ h')
  · exact union_subset subset_closure hZ₁

theorem injOn_crossSeamPage (hchart : ContinuousOn chart spliceCylinder) (hDom : IsClosed Dom)
    (hf : ContinuousOn f Dom) (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂)
    (hinj₁ : InjOn f J₁) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hZ₂ : Disjoint J₂ (crossSeamPage chart f Dom i)) :
    InjOn f (crossSeamPage chart f Dom i) := by
  have hJ₁ : ∀ x ∈ crossSeamPage chart f Dom i, f x ∈ chart '' spliceCore → x ∈ J₁ := by
    intro x hx hfx
    have hxJ : x ∈ Dom ∩ f ⁻¹' (chart '' spliceCore) := ⟨crossSeamPage_subset hDom i hx, hfx⟩
    rw [hJ] at hxJ
    exact hxJ.resolve_right fun h => disjoint_left.mp hZ₂ h hx
  intro x hx y hy hxy
  have hxS := (crossSeamPage_subset_preimage hchart hDom hf i hx).2
  rw [crossSheetOf_eq_union, image_union] at hxS
  rcases hxS with h | h
  · exact huniq x (crossSeamPage_subset hDom i hx) y (crossSeamPage_subset hDom i hy) hxy h
  · exact hinj₁ (hJ₁ x hx h) (hJ₁ y hy (hxy ▸ h)) hxy

theorem image_crossSeamPage (hchart : ContinuousOn chart spliceCylinder) (hDom : IsClosed Dom)
    (hf : ContinuousOn f Dom) {i : Fin 4} (hsurj₁ : chart '' spliceCore ⊆ f '' J₁)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom) (hZ₁ : J₁ ⊆ crossSeamPage chart f Dom i) :
    f '' crossSeamPage chart f Dom i = chart '' crossSheetOf i := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (crossSeamPage_subset_preimage hchart hDom hf i hx).2
  · rw [crossSheetOf_eq_union, image_union]
    rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hsurj hy
      exact ⟨x, subset_closure ⟨hx, hy⟩, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hsurj₁ hy
      exact ⟨x, hZ₁ hx, rfl⟩

theorem bijOn_crossSeamPage (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsClosed Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom)
    (hZ₁ : J₁ ⊆ crossSeamPage chart f Dom i) (hZ₂ : Disjoint J₂ (crossSeamPage chart f Dom i)) :
    BijOn (Function.invFunOn chart spliceCylinder ∘ f) (crossSeamPage chart f Dom i)
      (crossSheetOf i) := by
  have himage := image_crossSeamPage hchart hDom hf hsurj₁ hsurj hZ₁
  have hinj := injOn_crossSeamPage hchart hDom hf hJ hinj₁ huniq hZ₂
  have hval : ∀ x ∈ crossSeamPage chart f Dom i,
      (Function.invFunOn chart spliceCylinder ∘ f) x ∈ crossSheetOf i ∧
        chart ((Function.invFunOn chart spliceCylinder ∘ f) x) = f x := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ : f x ∈ chart '' crossSheetOf i := himage ▸ mem_image_of_mem f hx
    have hqc : q ∈ spliceCylinder := crossSheetOf_subset_spliceCylinder i hq
    have heq : Function.invFunOn chart spliceCylinder (f x) = q := by
      rw [← hqx]
      exact hinjc.leftInvOn_invFunOn hqc
    refine ⟨?_, ?_⟩
    · change Function.invFunOn chart spliceCylinder (f x) ∈ crossSheetOf i
      rw [heq]
      exact hq
    · change chart (Function.invFunOn chart spliceCylinder (f x)) = f x
      rw [heq, hqx]
  refine ⟨fun x hx => (hval x hx).1, fun x hx y hy hxy => ?_, fun q hq => ?_⟩
  · apply hinj hx hy
    rw [← (hval x hx).2, ← (hval y hy).2, hxy]
  · obtain ⟨x, hx, hxq⟩ : chart q ∈ f '' crossSeamPage chart f Dom i :=
      himage ▸ mem_image_of_mem chart hq
    refine ⟨x, hx, ?_⟩
    change Function.invFunOn chart spliceCylinder (f x) = q
    rw [hxq]
    exact hinjc.leftInvOn_invFunOn (crossSheetOf_subset_spliceCylinder i hq)

omit [TopologicalSpace X] [T2Space X] in
theorem inter_preimage_invFunOn_eq (hinjc : InjOn chart spliceCylinder)
    {S : Set ((ℝ × ℝ) × ℝ)} (hS : S ⊆ spliceCylinder) :
    (Dom ∩ f ⁻¹' (chart '' spliceCylinder)) ∩ (Function.invFunOn chart spliceCylinder ∘ f) ⁻¹' S =
      Dom ∩ f ⁻¹' (chart '' S) := by
  ext x
  constructor
  · rintro ⟨⟨hx, hfx⟩, hS'⟩
    refine ⟨hx, _, hS', ?_⟩
    exact Function.invFunOn_eq hfx
  · rintro ⟨hx, q, hq, hqx⟩
    have heq : Function.invFunOn chart spliceCylinder (f x) = q := by
      rw [← hqx]
      exact hinjc.leftInvOn_invFunOn (hS hq)
    refine ⟨⟨hx, q, hS hq, hqx⟩, ?_⟩
    change Function.invFunOn chart spliceCylinder (f x) ∈ S
    rw [heq]
    exact hq

theorem isPolyhedron_crossSeamPage (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hψ : IsPiecewiseAffineOn (Function.invFunOn chart spliceCylinder ∘ f)
      (Dom ∩ f ⁻¹' (chart '' spliceCylinder))) (i : Fin 4) :
    IsPolyhedron (crossSeamPage chart f Dom i) := by
  have hcomp : ∀ S : Set ((ℝ × ℝ) × ℝ), S ⊆ spliceCylinder → IsCompact S →
      IsCompact (Dom ∩ f ⁻¹' (chart '' S)) := fun S hS hSc =>
    hDom.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hDom.isClosed
      (hSc.image_of_continuousOn (hchart.mono hS)).isClosed) inter_subset_left
  have hsheet : IsPolyhedron ((Dom ∩ f ⁻¹' (chart '' spliceCylinder)) ∩
      (Function.invFunOn chart spliceCylinder ∘ f) ⁻¹' crossSheetOf i) := by
    refine isPolyhedron_inter_preimage_of_isCompact hψ (isHPolytope_crossSheetOf i) ?_
    rw [inter_preimage_invFunOn_eq hinjc (crossSheetOf_subset_spliceCylinder i)]
    exact hcomp _ (crossSheetOf_subset_spliceCylinder i) (isHPolytope_crossSheetOf i).1
  have hcore : IsPolyhedron ((Dom ∩ f ⁻¹' (chart '' spliceCylinder)) ∩
      (Function.invFunOn chart spliceCylinder ∘ f) ⁻¹' spliceCore) := by
    refine isPolyhedron_inter_preimage_of_isCompact hψ isHPolytope_spliceCore ?_
    rw [inter_preimage_invFunOn_eq hinjc spliceCore_subset_spliceCylinder]
    exact hcomp _ spliceCore_subset_spliceCylinder isHPolytope_spliceCore.1
  have heq : Dom ∩ f ⁻¹' (chart '' crossOpenSheetOf i) =
      ((Dom ∩ f ⁻¹' (chart '' spliceCylinder)) ∩
          (Function.invFunOn chart spliceCylinder ∘ f) ⁻¹' crossSheetOf i) \
        ((Dom ∩ f ⁻¹' (chart '' spliceCylinder)) ∩
          (Function.invFunOn chart spliceCylinder ∘ f) ⁻¹' spliceCore) := by
    rw [← inter_preimage_invFunOn_eq hinjc (crossOpenSheetOf_subset_spliceCylinder i),
      crossOpenSheetOf_eq_sdiff, preimage_sdiff, inter_sdiff_distrib_left]
  rw [crossSeamPage, heq]
  exact hsheet.closure_sdiff hcore

end Structure

section Reading

variable {X : Type*} [TopologicalSpace X] [T2Space X] {chart : (ℝ × ℝ) × ℝ → X}
  {f : EuclideanSpace ℝ (Fin 2) → X} {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}

theorem isPLHomeomorphOn_crossSeamPage (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom)
    (hψ : IsPiecewiseAffineOn (Function.invFunOn chart spliceCylinder ∘ f)
      (Dom ∩ f ⁻¹' (chart '' spliceCylinder)))
    (hZ₁ : J₁ ⊆ crossSeamPage chart f Dom i) (hZ₂ : Disjoint J₂ (crossSeamPage chart f Dom i)) :
    IsPLHomeomorphOn (Function.invFunOn chart spliceCylinder ∘ f) (crossSeamPage chart f Dom i)
      (crossSheetOf i) := by
  have hpoly := isPolyhedron_crossSeamPage hchart hinjc hDom hf hψ i
  have hZS : crossSeamPage chart f Dom i ⊆ Dom ∩ f ⁻¹' (chart '' spliceCylinder) :=
    (crossSeamPage_subset_preimage hchart hDom.isClosed hf i).trans
      (inter_subset_inter_right _ (preimage_mono (image_mono
        (crossSheetOf_subset_spliceCylinder i))))
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    (hψ.mono_of_isPolyhedron hpoly hZS)
    (bijOn_crossSeamPage hchart hinjc hDom.isClosed hf hJ hinj₁ hsurj₁ huniq hsurj hZ₁ hZ₂)

theorem continuousOn_invFunOn_crossSeamPage (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom)
    (hZ₁ : J₁ ⊆ crossSeamPage chart f Dom i) (hZ₂ : Disjoint J₂ (crossSeamPage chart f Dom i)) :
    ContinuousOn (Function.invFunOn (Function.invFunOn chart spliceCylinder ∘ f)
      (crossSeamPage chart f Dom i)) (crossSheetOf i) := by
  have hbij := bijOn_crossSeamPage hchart hinjc hDom.isClosed hf hJ hinj₁ hsurj₁ huniq hsurj hZ₁
    hZ₂
  have hZDom := crossSeamPage_subset (chart := chart) (f := f) hDom.isClosed i
  have hψc : ContinuousOn (Function.invFunOn chart spliceCylinder ∘ f)
      (crossSeamPage chart f Dom i) :=
    (continuousOn_invFunOn_image_of_isCompact isHPolytope_spliceCylinder.1 hchart hinjc).comp
      (hf.mono hZDom) fun x hx => image_mono (crossSheetOf_subset_spliceCylinder i)
        (crossSeamPage_subset_preimage hchart hDom.isClosed hf i hx).2
  have hZc : IsCompact (crossSeamPage chart f Dom i) :=
    hDom.of_isClosed_subset isClosed_closure hZDom
  have h : ContinuousOn (Function.invFunOn (Function.invFunOn chart spliceCylinder ∘ f)
      (crossSeamPage chart f Dom i))
      ((Function.invFunOn chart spliceCylinder ∘ f) '' crossSeamPage chart f Dom i) :=
    continuousOn_invFunOn_image_of_isCompact hZc hψc hbij.injOn
  rwa [hbij.image_eq] at h

theorem mem_frontier_iff_of_mem_crossSeamPage (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom)
    (hZ₁ : J₁ ⊆ crossSeamPage chart f Dom i) (hZ₂ : Disjoint J₂ (crossSeamPage chart f Dom i))
    {BdM : Set X} (htube : chart '' spliceCylinder ∩ BdM = chart '' spliceEndDisks)
    (hfront : ∀ x ∈ frontier Dom, f x ∈ BdM)
    (hbd : ∀ x ∈ Dom, f x ∈ BdM → f x ∈ chart '' (crossingFigure \ spliceCore) →
      x ∈ frontier Dom)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ crossSeamPage chart f Dom i) :
    x ∈ frontier Dom ↔ ((Function.invFunOn chart spliceCylinder ∘ f) x).2 = 0 ∨
      ((Function.invFunOn chart spliceCylinder ∘ f) x).2 = 1 := by
  have hbij := bijOn_crossSeamPage hchart hinjc hDom.isClosed hf hJ hinj₁ hsurj₁ huniq hsurj hZ₁
    hZ₂
  have hZDom := crossSeamPage_subset (chart := chart) (f := f) hDom.isClosed i
  have hval : ∀ z ∈ crossSeamPage chart f Dom i,
      (Function.invFunOn chart spliceCylinder ∘ f) z ∈ crossSheetOf i ∧
        chart ((Function.invFunOn chart spliceCylinder ∘ f) z) = f z := fun z hz =>
    ⟨hbij.mapsTo hz, Function.invFunOn_eq (image_mono (crossSheetOf_subset_spliceCylinder i)
      (crossSeamPage_subset_preimage hchart hDom.isClosed hf i hz).2)⟩
  have hBd : ∀ q ∈ spliceCylinder, chart q ∈ BdM ↔ q.2 = 0 ∨ q.2 = 1 := by
    intro q hq
    constructor
    · intro h
      have hmem : chart q ∈ chart '' spliceEndDisks := by
        rw [← htube]
        exact ⟨⟨q, hq, rfl⟩, h⟩
      exact (mem_of_apply_mem_image_of_injOn hinjc spliceEndDisks_subset_spliceCylinder hq
        hmem).2
    · intro h
      have hmem : chart q ∈ chart '' spliceEndDisks := ⟨q, ⟨hq.1, h⟩, rfl⟩
      rw [← htube] at hmem
      exact hmem.2
  have hnoncore : ∀ z ∈ crossSeamPage chart f Dom i,
      (Function.invFunOn chart spliceCylinder ∘ f) z ∉ spliceCore →
        ((Function.invFunOn chart spliceCylinder ∘ f) z).2 = 0 ∨
          ((Function.invFunOn chart spliceCylinder ∘ f) z).2 = 1 → z ∈ frontier Dom := by
    intro z hz hzc hzt
    have hzq := hval z hz
    have hzcyl := crossSheetOf_subset_spliceCylinder i hzq.1
    refine hbd z (hZDom hz) ?_ ?_
    · rw [← hzq.2]
      exact (hBd _ hzcyl).mpr hzt
    · rw [← hzq.2]
      exact ⟨_, ⟨crossSheetOf_subset_crossingFigure i hzq.1, hzc⟩, rfl⟩
  constructor
  · intro hxf
    have h := hfront x hxf
    rw [← (hval x hx).2] at h
    exact (hBd _ (crossSheetOf_subset_spliceCylinder i (hval x hx).1)).mp h
  · intro ht
    by_cases hxc : (Function.invFunOn chart spliceCylinder ∘ f) x ∈ spliceCore
    · obtain ⟨hx1, hx2⟩ := hxc
      have hYsheet : (crossRayOf i \ {((0 : ℝ), (0 : ℝ))}) ×ˢ
          ({((Function.invFunOn chart spliceCylinder ∘ f) x).2} : Set ℝ) ⊆
            crossOpenSheetOf i :=
        prod_mono subset_rfl (singleton_subset_iff.mpr hx2)
      have hψx : (Function.invFunOn chart spliceCylinder ∘ f) x ∈
          closure ((crossRayOf i \ {((0 : ℝ), (0 : ℝ))}) ×ˢ
            ({((Function.invFunOn chart spliceCylinder ∘ f) x).2} : Set ℝ)) := by
        rw [closure_prod_eq, closure_singleton]
        refine ⟨?_, rfl⟩
        rw [mem_singleton_iff.mp hx1]
        exact zero_mem_closure_crossRayOf_sdiff i
      have hclY : closure ((crossRayOf i \ {((0 : ℝ), (0 : ℝ))}) ×ˢ
          ({((Function.invFunOn chart spliceCylinder ∘ f) x).2} : Set ℝ)) ⊆ crossSheetOf i :=
        closure_minimal (hYsheet.trans (crossOpenSheetOf_subset_crossSheetOf i))
          (isHPolytope_crossSheetOf i).1.isClosed
      have hcont := continuousOn_invFunOn_crossSeamPage hchart hinjc hDom hf hJ hinj₁ hsurj₁
        huniq hsurj hZ₁ hZ₂
      have himg : Function.invFunOn (Function.invFunOn chart spliceCylinder ∘ f)
          (crossSeamPage chart f Dom i) '' ((crossRayOf i \ {((0 : ℝ), (0 : ℝ))}) ×ˢ
            ({((Function.invFunOn chart spliceCylinder ∘ f) x).2} : Set ℝ)) ⊆
              frontier Dom := by
        rintro _ ⟨q, hq, rfl⟩
        have hqS : q ∈ crossSheetOf i :=
          crossOpenSheetOf_subset_crossSheetOf i (hYsheet hq)
        obtain ⟨hmem, heq⟩ := Function.invFunOn_pos (hbij.surjOn hqS)
        refine hnoncore _ hmem ?_ ?_
        · rw [heq]
          exact disjoint_left.mp (disjoint_crossOpenSheetOf_spliceCore i) (hYsheet hq)
        · rw [heq, mem_singleton_iff.mp hq.2]
          exact ht
      have hmem := (hcont.mono hclY).image_closure ⟨_, hψx, rfl⟩
      rw [hbij.injOn.leftInvOn_invFunOn hx] at hmem
      exact closure_minimal himg isClosed_frontier hmem
    · exact hnoncore x hx hxc ht

omit [TopologicalSpace X] [T2Space X] in
theorem exists_mem_crossSeamPage_of_mem
    (himage : ∀ x ∈ Dom, f x ∈ chart '' spliceCylinder → f x ∈ chart '' crossingFigure)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂)
    (hJ₁page : ∃ i, J₁ ⊆ crossSeamPage chart f Dom i)
    (hJ₂page : ∃ i, J₂ ⊆ crossSeamPage chart f Dom i) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ Dom) (hfx : f x ∈ chart '' spliceCylinder) :
    ∃ i, x ∈ crossSeamPage chart f Dom i := by
  obtain ⟨q, hq, hqx⟩ := himage x hx hfx
  by_cases hqc : q ∈ spliceCore
  · have hxJ : x ∈ Dom ∩ f ⁻¹' (chart '' spliceCore) := ⟨hx, q, hqc, hqx⟩
    rw [hJ] at hxJ
    rcases hxJ with h | h
    · obtain ⟨i, hi⟩ := hJ₁page
      exact ⟨i, hi h⟩
    · obtain ⟨i, hi⟩ := hJ₂page
      exact ⟨i, hi h⟩
  · obtain ⟨i, hi⟩ := exists_mem_crossOpenSheetOf hq hqc
    exact ⟨i, subset_closure ⟨hx, q, hi, hqx⟩⟩

theorem crossSeamPage_wall (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDomB : IsPLBall 2 Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hinj₁ : InjOn f J₁)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) {i : Fin 4}
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y)
    (hsurj : chart '' crossOpenSheetOf i ⊆ f '' Dom)
    (hZ₁ : J₁ ⊆ crossSeamPage chart f Dom i) (hZ₂ : Disjoint J₂ (crossSeamPage chart f Dom i))
    (hopen : IsOpen (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)))
    (hfrontier : ∀ z ∈ Dom, f z ∈ chart '' spliceCylinder →
      (z ∈ frontier Dom ↔ ((Function.invFunOn chart spliceCylinder ∘ f) z).2 = 0 ∨
        ((Function.invFunOn chart spliceCylinder ∘ f) z).2 = 1))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ crossSeamPage chart f Dom i)
    (hxw : x ∈ closure (Dom \ (Dom ∩ f ⁻¹' (chart '' spliceCylinder)))) :
    (Function.invFunOn chart spliceCylinder ∘ f) x ∈ spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 := by
  have hDom : IsCompact Dom := hDomB.isPolyhedron.isCompact
  have hbij := bijOn_crossSeamPage hchart hinjc hDom.isClosed hf hJ hinj₁ hsurj₁ huniq hsurj hZ₁
    hZ₂
  have hZDom := crossSeamPage_subset (chart := chart) (f := f) hDom.isClosed i
  have hcont := continuousOn_invFunOn_crossSeamPage hchart hinjc hDom hf hJ hinj₁ hsurj₁ huniq
    hsurj hZ₁ hZ₂
  have hfcyl : ∀ z ∈ crossSeamPage chart f Dom i, f z ∈ chart '' spliceCylinder := fun z hz =>
    image_mono (crossSheetOf_subset_spliceCylinder i)
      (crossSeamPage_subset_preimage hchart hDom.isClosed hf i hz).2
  have hψS : (Function.invFunOn chart spliceCylinder ∘ f) x ∈ crossSheetOf i := hbij.mapsTo hx
  have hψx : chart ((Function.invFunOn chart spliceCylinder ∘ f) x) = f x :=
    Function.invFunOn_eq (hfcyl x hx)
  have hψcyl := crossSheetOf_subset_spliceCylinder i hψS
  refine ⟨?_, hψcyl.2⟩
  by_contra hlat
  have hsq := mem_spliceSquare.mp hψcyl.1
  have hnb : ¬(((Function.invFunOn chart spliceCylinder ∘ f) x).1.1 = -1 ∨
      ((Function.invFunOn chart spliceCylinder ∘ f) x).1.1 = 1 ∨
      ((Function.invFunOn chart spliceCylinder ∘ f) x).1.2 = -1 ∨
      ((Function.invFunOn chart spliceCylinder ∘ f) x).1.2 = 1) := fun h => hlat ⟨hψcyl.1, h⟩
  simp only [not_or] at hnb
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hnb
  have ha1 : -1 < ((Function.invFunOn chart spliceCylinder ∘ f) x).1.1 :=
    lt_of_le_of_ne hsq.1.1 (Ne.symm hn1)
  have ha2 : ((Function.invFunOn chart spliceCylinder ∘ f) x).1.1 < 1 := lt_of_le_of_ne hsq.1.2 hn2
  have hb1 : -1 < ((Function.invFunOn chart spliceCylinder ∘ f) x).1.2 :=
    lt_of_le_of_ne hsq.2.1 (Ne.symm hn3)
  have hb2 : ((Function.invFunOn chart spliceCylinder ∘ f) x).1.2 < 1 := lt_of_le_of_ne hsq.2.2 hn4
  obtain ⟨ρ, hρ, hρ1, hρ2, hρ3, hρ4⟩ : ∃ ρ : ℝ, 0 < ρ ∧
      ρ ≤ ((Function.invFunOn chart spliceCylinder ∘ f) x).1.1 + 1 ∧
      ρ ≤ 1 - ((Function.invFunOn chart spliceCylinder ∘ f) x).1.1 ∧
      ρ ≤ ((Function.invFunOn chart spliceCylinder ∘ f) x).1.2 + 1 ∧
      ρ ≤ 1 - ((Function.invFunOn chart spliceCylinder ∘ f) x).1.2 :=
    ⟨min (min (((Function.invFunOn chart spliceCylinder ∘ f) x).1.1 + 1)
        (1 - ((Function.invFunOn chart spliceCylinder ∘ f) x).1.1))
      (min (((Function.invFunOn chart spliceCylinder ∘ f) x).1.2 + 1)
        (1 - ((Function.invFunOn chart spliceCylinder ∘ f) x).1.2)),
      lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hball : ∀ q ∈ Metric.ball ((Function.invFunOn chart spliceCylinder ∘ f) x) ρ,
      q.1.1 ∈ Ioo (-1 : ℝ) 1 ∧ q.1.2 ∈ Ioo (-1 : ℝ) 1 := by
    intro q hq
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hq
    have h1 := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hq)
    have h2 := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hq)
    rw [abs_lt] at h1 h2
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  obtain ⟨N, hN, hNsub⟩ := exists_mem_nhds_inter_image_subset_image_inter
    isHPolytope_spliceCylinder.1 hchart hinjc hψcyl (Metric.ball_mem_nhds _ hρ)
  have hpre : f ⁻¹' N ∈ 𝓝[Dom] x := hf x (hZDom hx) (by rw [← hψx]; exact hN)
  obtain ⟨V₀, hV₀, hV₀sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨V, hVo, hxV, hVV₀, hVconn⟩ :=
    hDomB.exists_isOpen_isPreconnected_inter_interior (hZDom hx) hV₀
  have hBcyl : (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1 ⊆ spliceCylinder :=
    prod_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) Ioo_subset_Icc_self
  have hcylc : IsClosed (chart '' spliceCylinder) :=
    (isHPolytope_spliceCylinder.1.image_of_continuousOn hchart).isClosed
  have hu₁ : IsOpen (interior Dom ∩
      f ⁻¹' (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1))) :=
    (hf.mono interior_subset).isOpen_inter_preimage isOpen_interior hopen
  have hu₂ : IsOpen (interior Dom ∩ f ⁻¹' (chart '' spliceCylinder)ᶜ) :=
    (hf.mono interior_subset).isOpen_inter_preimage isOpen_interior hcylc.isOpen_compl
  have hdisj : Disjoint (interior Dom ∩
      f ⁻¹' (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)))
      (interior Dom ∩ f ⁻¹' (chart '' spliceCylinder)ᶜ) :=
    disjoint_left.mpr fun z hz hz' => hz'.2 (image_mono hBcyl hz.2)
  have hcover : V ∩ interior Dom ⊆ (interior Dom ∩
      f ⁻¹' (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1))) ∪
        (interior Dom ∩ f ⁻¹' (chart '' spliceCylinder)ᶜ) := by
    rintro z ⟨hzV, hzint⟩
    by_cases hzc : f z ∈ chart '' spliceCylinder
    · left
      refine ⟨hzint, ?_⟩
      have hzN : f z ∈ N := hV₀sub ⟨hVV₀ hzV, interior_subset hzint⟩
      obtain ⟨q, ⟨hqc, hqb⟩, hqz⟩ := hNsub ⟨hzN, hzc⟩
      have hzfront := hfrontier z (interior_subset hzint) hzc
      have hψz : (Function.invFunOn chart spliceCylinder ∘ f) z = q := by
        change Function.invFunOn chart spliceCylinder (f z) = q
        rw [← hqz]
        exact hinjc.leftInvOn_invFunOn hqc
      have hnf : z ∉ frontier Dom := fun h => h.2 hzint
      rw [hψz] at hzfront
      obtain ⟨hq1, hq2⟩ := hball q hqb
      exact ⟨q, ⟨⟨hq1, hq2⟩, lt_of_le_of_ne hqc.2.1 fun h => hnf (hzfront.mpr (Or.inl h.symm)),
        lt_of_le_of_ne hqc.2.2 fun h => hnf (hzfront.mpr (Or.inr h))⟩, hqz⟩
    · exact Or.inr ⟨hzint, hzc⟩
  have hne : (V ∩ interior Dom ∩ (interior Dom ∩
      f ⁻¹' (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)))).Nonempty := by
    have hY'S : ({((Function.invFunOn chart spliceCylinder ∘ f) x).1} : Set (ℝ × ℝ)) ×ˢ
        Ioo (0 : ℝ) 1 ⊆ crossSheetOf i :=
      prod_mono (singleton_subset_iff.mpr hψS.1) Ioo_subset_Icc_self
    have hψY : (Function.invFunOn chart spliceCylinder ∘ f) x ∈
        closure (({((Function.invFunOn chart spliceCylinder ∘ f) x).1} : Set (ℝ × ℝ)) ×ˢ
          Ioo (0 : ℝ) 1) := by
      rw [closure_prod_eq, closure_singleton, closure_Ioo zero_ne_one]
      exact ⟨rfl, hψS.2⟩
    have hclY : closure (({((Function.invFunOn chart spliceCylinder ∘ f) x).1} :
        Set (ℝ × ℝ)) ×ˢ Ioo (0 : ℝ) 1) ⊆ crossSheetOf i :=
      closure_minimal hY'S (isHPolytope_crossSheetOf i).1.isClosed
    have hmem := (hcont.mono hclY).image_closure ⟨_, hψY, rfl⟩
    rw [hbij.injOn.leftInvOn_invFunOn hx] at hmem
    obtain ⟨_, hzV, q, hq, rfl⟩ := mem_closure_iff_nhds.mp hmem V (hVo.mem_nhds hxV)
    obtain ⟨hzZ, hψzq⟩ := Function.invFunOn_pos (hbij.surjOn (hY'S hq))
    have hzDom := hZDom hzZ
    have hfz := hfcyl _ hzZ
    have hzint : Function.invFunOn (Function.invFunOn chart spliceCylinder ∘ f)
        (crossSeamPage chart f Dom i) q ∈ interior Dom := by
      by_contra hzi
      have hzf : Function.invFunOn (Function.invFunOn chart spliceCylinder ∘ f)
          (crossSeamPage chart f Dom i) q ∈ frontier Dom := ⟨subset_closure hzDom, hzi⟩
      rw [hfrontier _ hzDom hfz, hψzq] at hzf
      rcases hzf with h | h
      · exact hq.2.1.ne' h
      · exact hq.2.2.ne h
    refine ⟨_, ⟨hzV, hzint⟩, hzint, q, ⟨⟨?_, ?_⟩, hq.2⟩, ?_⟩
    · rw [mem_singleton_iff.mp hq.1]
      exact ⟨ha1, ha2⟩
    · rw [mem_singleton_iff.mp hq.1]
      exact ⟨hb1, hb2⟩
    · exact (congrArg chart hψzq).symm.trans (Function.invFunOn_eq hfz)
  rcases hVconn.subset_or_subset hu₁ hu₂ hdisj hcover with hsub | hsub
  · have hSclosed : IsClosed (Dom ∩ f ⁻¹' (chart '' spliceCylinder)) :=
      hf.preimage_isClosed_of_isClosed hDom.isClosed hcylc
    have hVS : V ∩ Dom ⊆ Dom ∩ f ⁻¹' (chart '' spliceCylinder) := by
      rintro y ⟨hyV, hyDom⟩
      have hycl : y ∈ closure (V ∩ interior Dom) := by
        rw [mem_closure_iff_nhds]
        intro W hW
        have hy' : y ∈ closure (interior Dom) := by
          rw [IsPLBall.closure_interior (n := 1) hDomB]
          exact hyDom
        obtain ⟨z, ⟨hzW, hzV⟩, hzint⟩ :=
          mem_closure_iff_nhds.mp hy' (W ∩ V) (Filter.inter_mem hW (hVo.mem_nhds hyV))
        exact ⟨z, hzW, hzV, hzint⟩
      refine closure_minimal (fun z hz => ?_) hSclosed hycl
      exact ⟨interior_subset hz.2, image_mono hBcyl (hsub hz).2⟩
    obtain ⟨y, hyV, hyDom, hyS⟩ := mem_closure_iff_nhds.mp hxw V (hVo.mem_nhds hxV)
    exact hyS (hVS ⟨hyV, hyDom⟩)
  · obtain ⟨z, hzV, hzu₁⟩ := hne
    exact disjoint_left.mp hdisj hzu₁ (hsub hzV)

end Reading

end DifferentialGeometry.Topology.PiecewiseLinear
