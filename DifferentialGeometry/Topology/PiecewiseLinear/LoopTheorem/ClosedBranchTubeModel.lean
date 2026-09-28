/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexCone
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSquareWitness

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def tubeCellSphere : Set ((ℝ × ℝ) × ℝ) :=
  spliceSquare ×ˢ ({0, 1} : Set ℝ) ∪ spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1

theorem frontier_spliceCylinder : frontier spliceCylinder = tubeCellSphere := by
  have hsq : IsClosed spliceSquare := isHPolytope_spliceSquare.1.isClosed
  rw [spliceCylinder, frontier_prod_eq, closure_Icc, frontier_Icc (by norm_num : (0 : ℝ) ≤ 1),
    hsq.closure_eq, ← spliceSquareBoundary_eq_frontier, tubeCellSphere]

theorem isPLSphere_tubeCellSphere : IsPLSphere 2 tubeCellSphere := by
  rw [← frontier_spliceCylinder]
  exact isHPolytope_spliceCylinder.isPLSphere_frontier (by simp) interior_spliceCylinder_nonempty

theorem tubeCellCentre_mem_interior :
    ((0 : ℝ × ℝ), (1 / 2 : ℝ)) ∈ interior spliceCylinder := by
  rw [spliceCylinder, spliceSquare]
  simp only [interior_prod_eq, interior_Icc, Set.mem_prod, Set.mem_Ioo]
  norm_num

theorem exists_tubeCellSphere_coneBase [DecidableEq ((ℝ × ℝ) × ℝ)] :
    ∃ K : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ), K.faces.Finite ∧
      K.space = tubeCellSphere ∧ ∃ hK : IsConeBase ((0 : ℝ × ℝ), (1 / 2 : ℝ)) K,
        (coneComplex hK).space = spliceCylinder := by
  obtain ⟨K, hfin, hK⟩ := isPLSphere_tubeCellSphere.isPolyhedron.exists_simplicialComplex
  have hcone : IsConeBase ((0 : ℝ × ℝ), (1 / 2 : ℝ)) K :=
    isConeBase_of_space_subset_frontier_convex isHPolytope_spliceCylinder.convex
      isHPolytope_spliceCylinder.1.isClosed tubeCellCentre_mem_interior K
      (by rw [hK, frontier_spliceCylinder])
  refine ⟨K, hfin, hK, hcone, ?_⟩
  exact coneComplex_space_eq_of_convex isHPolytope_spliceCylinder.convex
    isHPolytope_spliceCylinder.1 (interior_subset tubeCellCentre_mem_interior) hcone
    (by rw [hK, frontier_spliceCylinder])

noncomputable def tubeMeridianCoeff (t : ℝ) : ℝ :=
  if t ≤ 1 / 4 then 4 * t else if t ≤ 3 / 4 then 1 else 4 - 4 * t

noncomputable def tubeMeridianHeight (t : ℝ) : ℝ :=
  if t ≤ 1 / 4 then 0 else if t ≤ 3 / 4 then 2 * t - 1 / 2 else 1

noncomputable def tubeMeridianParam (v : ℝ × ℝ) (t : ℝ) : (ℝ × ℝ) × ℝ :=
  (tubeMeridianCoeff t • v, tubeMeridianHeight t)

def tubeMeridian (v : ℝ × ℝ) : Set ((ℝ × ℝ) × ℝ) := tubeMeridianParam v '' Icc 0 1

def tubeCellArc (k : Fin 4) : Set ((ℝ × ℝ) × ℝ) := tubeMeridian (fourSpokeModelLeaf k)

theorem tubeMeridianCoeff_of_le {t : ℝ} (h : t ≤ 1 / 4) : tubeMeridianCoeff t = 4 * t :=
  ite_eq_left h

theorem tubeMeridianHeight_of_le {t : ℝ} (h : t ≤ 1 / 4) : tubeMeridianHeight t = 0 :=
  ite_eq_left h

theorem tubeMeridianCoeff_of_mem {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 3 / 4) :
    tubeMeridianCoeff t = 1 := by
  unfold tubeMeridianCoeff
  split_ifs with h
  · linarith
  · rfl

theorem tubeMeridianHeight_of_mem {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 3 / 4) :
    tubeMeridianHeight t = 2 * t - 1 / 2 := by
  unfold tubeMeridianHeight
  split_ifs with h
  · linarith
  · rfl

theorem tubeMeridianCoeff_of_ge {t : ℝ} (h : 3 / 4 ≤ t) : tubeMeridianCoeff t = 4 - 4 * t := by
  unfold tubeMeridianCoeff
  split_ifs with h1 h2
  · linarith
  · linarith
  · rfl

theorem tubeMeridianHeight_of_ge {t : ℝ} (h : 3 / 4 ≤ t) : tubeMeridianHeight t = 1 := by
  unfold tubeMeridianHeight
  split_ifs with h1 h2
  · linarith
  · linarith
  · rfl

theorem tubeMeridianParam_zero (v : ℝ × ℝ) : tubeMeridianParam v 0 = (0, 0) := by
  simp [tubeMeridianParam, tubeMeridianCoeff_of_le, tubeMeridianHeight_of_le]

theorem tubeMeridianParam_one (v : ℝ × ℝ) : tubeMeridianParam v 1 = (0, 1) := by
  rw [tubeMeridianParam, tubeMeridianCoeff_of_ge (by norm_num),
    tubeMeridianHeight_of_ge (by norm_num)]
  simp

theorem tubeMeridianParam_quarter (v : ℝ × ℝ) : tubeMeridianParam v (1 / 4) = (v, 0) := by
  rw [tubeMeridianParam, tubeMeridianCoeff_of_le le_rfl, tubeMeridianHeight_of_le le_rfl]
  norm_num

theorem tubeMeridianParam_half (v : ℝ × ℝ) : tubeMeridianParam v (1 / 2) = (v, 1 / 2) := by
  rw [tubeMeridianParam, tubeMeridianCoeff_of_mem (by norm_num) (by norm_num),
    tubeMeridianHeight_of_mem (by norm_num) (by norm_num)]
  norm_num

theorem tubeMeridianParam_threeQuarter (v : ℝ × ℝ) :
    tubeMeridianParam v (3 / 4) = (v, 1) := by
  rw [tubeMeridianParam, tubeMeridianCoeff_of_ge le_rfl, tubeMeridianHeight_of_ge le_rfl]
  norm_num

theorem tubeMeridianCoeff_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tubeMeridianCoeff t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := ht
  rcases le_or_gt t (1 / 4) with ha | ha
  · rw [tubeMeridianCoeff_of_le ha]
    constructor <;> linarith
  rcases le_or_gt t (3 / 4) with hb | hb
  · rw [tubeMeridianCoeff_of_mem ha.le hb]
    norm_num
  · rw [tubeMeridianCoeff_of_ge hb.le]
    constructor <;> linarith

theorem tubeMeridianHeight_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tubeMeridianHeight t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := ht
  rcases le_or_gt t (1 / 4) with ha | ha
  · rw [tubeMeridianHeight_of_le ha]
    norm_num
  rcases le_or_gt t (3 / 4) with hb | hb
  · rw [tubeMeridianHeight_of_mem ha.le hb]
    constructor <;> linarith
  · rw [tubeMeridianHeight_of_ge hb.le]
    norm_num

theorem tubeMeridianCoeff_eq_one_or {t : ℝ} :
    tubeMeridianCoeff t = 1 ∨ tubeMeridianHeight t = 0 ∨ tubeMeridianHeight t = 1 := by
  rcases le_or_gt t (1 / 4) with ha | ha
  · exact Or.inr (Or.inl (tubeMeridianHeight_of_le ha))
  rcases le_or_gt t (3 / 4) with hb | hb
  · exact Or.inl (tubeMeridianCoeff_of_mem ha.le hb)
  · exact Or.inr (Or.inr (tubeMeridianHeight_of_ge hb.le))

theorem eq_of_tubeMeridianCoeff_eq {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hc : tubeMeridianCoeff t = tubeMeridianCoeff s)
    (hz : tubeMeridianHeight t = tubeMeridianHeight s) : t = s := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hs0, hs1⟩ := hs
  rcases le_or_gt t (1 / 4) with hta | hta <;> rcases le_or_gt s (1 / 4) with hsa | hsa
  · rw [tubeMeridianCoeff_of_le hta, tubeMeridianCoeff_of_le hsa] at hc
    linarith
  · rcases le_or_gt s (3 / 4) with hsb | hsb
    · rw [tubeMeridianCoeff_of_le hta, tubeMeridianCoeff_of_mem hsa.le hsb] at hc
      rw [tubeMeridianHeight_of_le hta, tubeMeridianHeight_of_mem hsa.le hsb] at hz
      linarith
    · rw [tubeMeridianHeight_of_le hta, tubeMeridianHeight_of_ge hsb.le] at hz
      norm_num at hz
  · rcases le_or_gt t (3 / 4) with htb | htb
    · rw [tubeMeridianCoeff_of_le hsa, tubeMeridianCoeff_of_mem hta.le htb] at hc
      rw [tubeMeridianHeight_of_le hsa, tubeMeridianHeight_of_mem hta.le htb] at hz
      linarith
    · rw [tubeMeridianHeight_of_le hsa, tubeMeridianHeight_of_ge htb.le] at hz
      norm_num at hz
  · rcases le_or_gt t (3 / 4) with htb | htb <;> rcases le_or_gt s (3 / 4) with hsb | hsb
    · rw [tubeMeridianHeight_of_mem hta.le htb, tubeMeridianHeight_of_mem hsa.le hsb] at hz
      linarith
    · rw [tubeMeridianCoeff_of_mem hta.le htb, tubeMeridianCoeff_of_ge hsb.le] at hc
      rw [tubeMeridianHeight_of_mem hta.le htb, tubeMeridianHeight_of_ge hsb.le] at hz
      linarith
    · rw [tubeMeridianCoeff_of_mem hsa.le hsb, tubeMeridianCoeff_of_ge htb.le] at hc
      rw [tubeMeridianHeight_of_mem hsa.le hsb, tubeMeridianHeight_of_ge htb.le] at hz
      linarith
    · rw [tubeMeridianCoeff_of_ge htb.le, tubeMeridianCoeff_of_ge hsb.le] at hc
      linarith

theorem injOn_tubeMeridianParam {v : ℝ × ℝ} (hv : v ≠ 0) :
    InjOn (tubeMeridianParam v) (Icc 0 1) := by
  intro t ht s hs h
  have hc : tubeMeridianCoeff t • v = tubeMeridianCoeff s • v := congrArg Prod.fst h
  have hz : tubeMeridianHeight t = tubeMeridianHeight s := congrArg Prod.snd h
  exact eq_of_tubeMeridianCoeff_eq ht hs (smul_left_injective ℝ hv hc) hz

theorem isPiecewiseAffineOn_tubeMeridianParam (v : ℝ × ℝ) :
    IsPiecewiseAffineOn (tubeMeridianParam v) (Icc 0 1) := by
  let A₁ : ℝ →ᵃ[ℝ] (ℝ × ℝ) × ℝ := AffineMap.lineMap (0 : (ℝ × ℝ) × ℝ) ((4 : ℝ) • v, (0 : ℝ))
  let A₂ : ℝ →ᵃ[ℝ] (ℝ × ℝ) × ℝ := AffineMap.lineMap (v, (-1 / 2 : ℝ)) (v, (3 / 2 : ℝ))
  let A₃ : ℝ →ᵃ[ℝ] (ℝ × ℝ) × ℝ := AffineMap.lineMap ((4 : ℝ) • v, (1 : ℝ)) (0, (1 : ℝ))
  have h₁ : IsPiecewiseAffineOn (tubeMeridianParam v) (Icc 0 (1 / 4)) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope A₁ isHPolytope_Icc).congr ?_
    intro t ht
    rw [tubeMeridianParam, tubeMeridianCoeff_of_le ht.2, tubeMeridianHeight_of_le ht.2]
    simp only [A₁, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, sub_zero, add_zero,
      Prod.smul_mk, smul_smul, smul_zero, mul_comm]
  have h₂ : IsPiecewiseAffineOn (tubeMeridianParam v) (Icc (1 / 4) (3 / 4)) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope A₂ isHPolytope_Icc).congr ?_
    intro t ht
    rw [tubeMeridianParam, tubeMeridianCoeff_of_mem ht.1 ht.2,
      tubeMeridianHeight_of_mem ht.1 ht.2]
    simp only [A₂, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Prod.mk_sub_mk, sub_self,
      Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add, one_smul, smul_eq_mul]
    congr 1
    ring
  have h₃ : IsPiecewiseAffineOn (tubeMeridianParam v) (Icc (3 / 4) 1) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope A₃ isHPolytope_Icc).congr ?_
    intro t ht
    rw [tubeMeridianParam, tubeMeridianCoeff_of_ge ht.1, tubeMeridianHeight_of_ge ht.1]
    simp only [A₃, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Prod.mk_sub_mk, sub_self,
      Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add, zero_sub, smul_neg, smul_smul]
    congr 1
    rw [sub_smul, neg_add_eq_sub]
    congr 1
    rw [mul_comm]
  have h12 := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h12
  have h123 := h12.union_of_isClosed h₃ isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h123

theorem isPLHomeomorphOn_tubeMeridianParam {v : ℝ × ℝ} (hv : v ≠ 0) :
    IsPLHomeomorphOn (tubeMeridianParam v) (Icc 0 1) (tubeMeridian v) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_tubeMeridianParam v) (injOn_tubeMeridianParam hv).bijOn_image

theorem mem_tubeMeridian_iff {v : ℝ × ℝ} {p : (ℝ × ℝ) × ℝ} :
    p ∈ tubeMeridian v ↔ ∃ c z : ℝ, c ∈ Icc (0 : ℝ) 1 ∧ z ∈ Icc (0 : ℝ) 1 ∧
      (c = 1 ∨ z = 0 ∨ z = 1) ∧ p = (c • v, z) := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, _, tubeMeridianCoeff_mem ht, tubeMeridianHeight_mem ht,
      tubeMeridianCoeff_eq_one_or, rfl⟩
  · rintro ⟨c, z, hc, hz, hcase, rfl⟩
    rcases hcase with rfl | rfl | rfl
    · refine ⟨z / 2 + 1 / 4, ⟨by linarith [hz.1], by linarith [hz.2]⟩, ?_⟩
      rw [tubeMeridianParam, tubeMeridianCoeff_of_mem (by linarith [hz.1]) (by linarith [hz.2]),
        tubeMeridianHeight_of_mem (by linarith [hz.1]) (by linarith [hz.2])]
      congr 1
      ring
    · refine ⟨c / 4, ⟨by linarith [hc.1], by linarith [hc.2]⟩, ?_⟩
      rw [tubeMeridianParam, tubeMeridianCoeff_of_le (by linarith [hc.2]),
        tubeMeridianHeight_of_le (by linarith [hc.2])]
      congr 2
      ring
    · refine ⟨1 - c / 4, ⟨by linarith [hc.2], by linarith [hc.1]⟩, ?_⟩
      rw [tubeMeridianParam, tubeMeridianCoeff_of_ge (by linarith [hc.2]),
        tubeMeridianHeight_of_ge (by linarith [hc.2])]
      congr 2
      ring

theorem image_tubeMeridianParam_Icc_zero_quarter (v : ℝ × ℝ) :
    tubeMeridianParam v '' Icc 0 (1 / 4) = (fun c : ℝ => (c • v, (0 : ℝ))) '' Icc 0 1 := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨4 * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [tubeMeridianParam, tubeMeridianCoeff_of_le ht.2, tubeMeridianHeight_of_le ht.2]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c / 4, ⟨by linarith [hc.1], by linarith [hc.2]⟩, ?_⟩
    rw [tubeMeridianParam, tubeMeridianCoeff_of_le (by linarith [hc.2]),
      tubeMeridianHeight_of_le (by linarith [hc.2])]
    congr 2
    ring

theorem image_tubeMeridianParam_Icc_threeQuarter_one (v : ℝ × ℝ) :
    tubeMeridianParam v '' Icc (3 / 4) 1 = (fun c : ℝ => (c • v, (1 : ℝ))) '' Icc 0 1 := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨4 - 4 * t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [tubeMeridianParam, tubeMeridianCoeff_of_ge ht.1, tubeMeridianHeight_of_ge ht.1]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨1 - c / 4, ⟨by linarith [hc.2], by linarith [hc.1]⟩, ?_⟩
    rw [tubeMeridianParam, tubeMeridianCoeff_of_ge (by linarith [hc.2]),
      tubeMeridianHeight_of_ge (by linarith [hc.2])]
    congr 2
    ring

theorem smul_mem_spliceSquare {v : ℝ × ℝ} (hv : v ∈ spliceSquare) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) : c • v ∈ spliceSquare := by
  rw [mem_spliceSquare] at hv ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv
  obtain ⟨hc0, hc1⟩ := hc
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

theorem tubeMeridian_subset_tubeCellSphere {v : ℝ × ℝ} (hv : v ∈ spliceSquareBoundary) :
    tubeMeridian v ⊆ tubeCellSphere := by
  intro p hp
  obtain ⟨c, z, hc, hz, hcase, rfl⟩ := mem_tubeMeridian_iff.mp hp
  rcases hcase with rfl | rfl | rfl
  · exact Or.inr ⟨by rwa [one_smul], hz⟩
  · exact Or.inl ⟨smul_mem_spliceSquare hv.1 hc, Or.inl rfl⟩
  · exact Or.inl ⟨smul_mem_spliceSquare hv.1 hc, Or.inr rfl⟩

theorem fourSpokeModelLeaf_mem_spliceSquareBoundary (k : Fin 4) :
    fourSpokeModelLeaf k ∈ spliceSquareBoundary := by
  rw [mem_spliceSquareBoundary, mem_spliceSquare]
  rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl <;> norm_num [fourSpokeModelLeaf]

theorem tubeCellArc_subset_tubeCellSphere (k : Fin 4) : tubeCellArc k ⊆ tubeCellSphere :=
  tubeMeridian_subset_tubeCellSphere (fourSpokeModelLeaf_mem_spliceSquareBoundary k)

theorem isPLHomeomorphOn_tubeCellArc (k : Fin 4) :
    IsPLHomeomorphOn (tubeMeridianParam (fourSpokeModelLeaf k)) (Icc 0 1) (tubeCellArc k) :=
  isPLHomeomorphOn_tubeMeridianParam (fourSpokeModelLeaf_ne_zero k)

theorem eq_zero_of_smul_fourSpokeModelLeaf_eq {i j : Fin 4} (hij : i ≠ j) {c c' : ℝ}
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (h : c • fourSpokeModelLeaf i = c' • fourSpokeModelLeaf j) :
    c = 0 ∧ c' = 0 := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hij
    | (simp only [fourSpokeModelLeaf, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h
       constructor <;> linarith [h.1, h.2])

theorem tubeCellArc_inter {i j : Fin 4} (hij : i ≠ j) :
    tubeCellArc i ∩ tubeCellArc j =
      {((0 : ℝ × ℝ), (0 : ℝ)), ((0 : ℝ × ℝ), (1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨hpi, hpj⟩
    obtain ⟨c, z, hc, hz, hcase, rfl⟩ := mem_tubeMeridian_iff.mp hpi
    obtain ⟨c', z', hc', hz', -, hpeq⟩ := mem_tubeMeridian_iff.mp hpj
    have h1 : c • fourSpokeModelLeaf i = c' • fourSpokeModelLeaf j := congrArg Prod.fst hpeq
    obtain ⟨rfl, -⟩ := eq_zero_of_smul_fourSpokeModelLeaf_eq hij hc.1 hc'.1 h1
    rcases hcase with h | rfl | rfl
    · norm_num at h
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, tubeMeridianParam_zero _⟩,
        ⟨0, ⟨le_rfl, zero_le_one⟩, tubeMeridianParam_zero _⟩⟩
    · exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, tubeMeridianParam_one _⟩,
        ⟨1, ⟨zero_le_one, le_rfl⟩, tubeMeridianParam_one _⟩⟩

theorem tubeMeridianParam_mem_tubeCellArc (k : Fin 4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tubeMeridianParam (fourSpokeModelLeaf k) t ∈ tubeCellArc k := ⟨t, ht, rfl⟩

theorem not_isPreconnected_of_sign {X A B U : Set ((ℝ × ℝ) × ℝ)} {ℓ : (ℝ × ℝ) × ℝ → ℝ}
    (hℓ : Continuous ℓ) (hzero : ∀ p ∈ tubeCellSphere, ℓ p = 0 → p ∈ X)
    (hA : ∀ p ∈ A, p ∉ X → 0 < ℓ p) (hB : ∀ p ∈ B, p ∉ X → ℓ p < 0)
    (hU : U ⊆ tubeCellSphere \ X) (hconn : IsPreconnected U) (hUA : (U ∩ A).Nonempty)
    (hUB : (U ∩ B).Nonempty) : False := by
  obtain ⟨a, haU, haA⟩ := hUA
  obtain ⟨b, hbU, hbB⟩ := hUB
  have ha := hA a haA (hU haU).2
  have hb := hB b hbB (hU hbU).2
  obtain ⟨c, hcU, hc⟩ := hconn.intermediate_value hbU haU hℓ.continuousOn
    (show (0 : ℝ) ∈ Icc (ℓ b) (ℓ a) from ⟨hb.le, ha.le⟩)
  exact (hU hcU).2 (hzero c (hU hcU).1 hc)

theorem mem_tubeCellArc_union_of_snd_eq_zero {p : (ℝ × ℝ) × ℝ} (hp : p ∈ tubeCellSphere)
    (h : p.1.2 = 0) : p ∈ tubeCellArc 0 ∪ tubeCellArc 2 := by
  obtain ⟨⟨x, y⟩, z⟩ := p
  simp only at h
  subst h
  have hmem : ∀ c : ℝ, c ∈ Icc (0 : ℝ) 1 → (c = 1 ∨ z = 0 ∨ z = 1) → z ∈ Icc (0 : ℝ) 1 →
      (((c, (0 : ℝ)), z) : (ℝ × ℝ) × ℝ) ∈ tubeCellArc 0 ∧
        (((-c, (0 : ℝ)), z) : (ℝ × ℝ) × ℝ) ∈ tubeCellArc 2 := by
    intro c hc hcase hz
    refine ⟨mem_tubeMeridian_iff.mpr ⟨c, z, hc, hz, hcase, ?_⟩,
      mem_tubeMeridian_iff.mpr ⟨c, z, hc, hz, hcase, ?_⟩⟩ <;>
      simp [fourSpokeModelLeaf]
  rcases hp with ⟨hxy, hz⟩ | ⟨hxy, hz⟩
  · rw [mem_spliceSquare] at hxy
    have hz' : z ∈ Icc (0 : ℝ) 1 := by
      rcases hz with h | h <;> simp only [mem_singleton_iff] at h <;> rw [h] <;> norm_num
    have hcase : ∀ c : ℝ, c = 1 ∨ z = 0 ∨ z = 1 := by
      intro c
      rcases hz with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rcases le_total 0 x with hx | hx
    · exact Or.inl (hmem x ⟨hx, hxy.1.2⟩ (hcase x) hz').1
    · have h := (hmem (-x) ⟨by linarith, by linarith [hxy.1.1]⟩ (hcase (-x)) hz').2
      rw [neg_neg] at h
      exact Or.inr h
  · rw [mem_spliceSquareBoundary, mem_spliceSquare] at hxy
    obtain ⟨⟨⟨h1, h2⟩, -⟩, hb⟩ := hxy
    rcases hb with hb | hb | hb | hb
    · have h := (hmem 1 ⟨zero_le_one, le_rfl⟩ (Or.inl rfl) hz).2
      simp only at hb
      rw [hb]
      exact Or.inr h
    · simp only at hb
      rw [hb]
      exact Or.inl (hmem 1 ⟨zero_le_one, le_rfl⟩ (Or.inl rfl) hz).1
    · norm_num at hb
    · norm_num at hb

theorem mem_tubeCellArc_union_of_fst_eq_zero {p : (ℝ × ℝ) × ℝ} (hp : p ∈ tubeCellSphere)
    (h : p.1.1 = 0) : p ∈ tubeCellArc 1 ∪ tubeCellArc 3 := by
  obtain ⟨⟨x, y⟩, z⟩ := p
  simp only at h
  subst h
  have hmem : ∀ c : ℝ, c ∈ Icc (0 : ℝ) 1 → (c = 1 ∨ z = 0 ∨ z = 1) → z ∈ Icc (0 : ℝ) 1 →
      ((((0 : ℝ), c), z) : (ℝ × ℝ) × ℝ) ∈ tubeCellArc 1 ∧
        ((((0 : ℝ), -c), z) : (ℝ × ℝ) × ℝ) ∈ tubeCellArc 3 := by
    intro c hc hcase hz
    refine ⟨mem_tubeMeridian_iff.mpr ⟨c, z, hc, hz, hcase, ?_⟩,
      mem_tubeMeridian_iff.mpr ⟨c, z, hc, hz, hcase, ?_⟩⟩ <;>
      simp [fourSpokeModelLeaf]
  rcases hp with ⟨hxy, hz⟩ | ⟨hxy, hz⟩
  · rw [mem_spliceSquare] at hxy
    have hz' : z ∈ Icc (0 : ℝ) 1 := by
      rcases hz with h | h <;> simp only [mem_singleton_iff] at h <;> rw [h] <;> norm_num
    have hcase : ∀ c : ℝ, c = 1 ∨ z = 0 ∨ z = 1 := by
      intro c
      rcases hz with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rcases le_total 0 y with hy | hy
    · exact Or.inl (hmem y ⟨hy, hxy.2.2⟩ (hcase y) hz').1
    · have h := (hmem (-y) ⟨by linarith, by linarith [hxy.2.1]⟩ (hcase (-y)) hz').2
      rw [neg_neg] at h
      exact Or.inr h
  · rw [mem_spliceSquareBoundary, mem_spliceSquare] at hxy
    obtain ⟨⟨-, ⟨h1, h2⟩⟩, hb⟩ := hxy
    rcases hb with hb | hb | hb | hb
    · norm_num at hb
    · norm_num at hb
    · have h := (hmem 1 ⟨zero_le_one, le_rfl⟩ (Or.inl rfl) hz).2
      simp only at hb
      rw [hb]
      exact Or.inr h
    · simp only at hb
      rw [hb]
      exact Or.inl (hmem 1 ⟨zero_le_one, le_rfl⟩ (Or.inl rfl) hz).1

theorem coord_pos_of_mem_tubeCellArc {k : Fin 4} {p : (ℝ × ℝ) × ℝ} (hp : p ∈ tubeCellArc k)
    (hpole : p ∉ ({((0 : ℝ × ℝ), (0 : ℝ)), ((0 : ℝ × ℝ), (1 : ℝ))} : Set ((ℝ × ℝ) × ℝ))) :
    ∃ c : ℝ, 0 < c ∧ p.1 = c • fourSpokeModelLeaf k := by
  obtain ⟨c, z, hc, -, hcase, rfl⟩ := mem_tubeMeridian_iff.mp hp
  refine ⟨c, lt_of_le_of_ne hc.1 fun h0 => hpole ?_, rfl⟩
  subst h0
  rcases hcase with h | rfl | rfl
  · norm_num at h
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

theorem tubeCellArc_sep (i : Fin 4) :
    ∀ U ⊆ tubeCellSphere \ (tubeCellArc i ∪ tubeCellArc (i + 2)), IsPreconnected U →
      (U ∩ tubeCellArc (i + 1)).Nonempty → (U ∩ tubeCellArc (i + 3)).Nonempty → False := by
  intro U hU hconn hA hB
  have hpoles : ∀ q ∈ ({((0 : ℝ × ℝ), (0 : ℝ)), ((0 : ℝ × ℝ), (1 : ℝ))} :
      Set ((ℝ × ℝ) × ℝ)), q ∈ tubeCellArc i ∪ tubeCellArc (i + 2) := by
    rintro q (rfl | rfl)
    · exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, tubeMeridianParam_zero _⟩
    · exact Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, tubeMeridianParam_one _⟩
  have hc2 : Continuous fun p : (ℝ × ℝ) × ℝ => p.1.2 := continuous_snd.comp continuous_fst
  have hc1 : Continuous fun p : (ℝ × ℝ) × ℝ => p.1.1 := continuous_fst.comp continuous_fst
  have hsign : ∀ (k : Fin 4) (ℓ : (ℝ × ℝ) × ℝ → ℝ),
      (∀ c : ℝ, ℓ (c • fourSpokeModelLeaf k, (0 : ℝ)) = c * ℓ (fourSpokeModelLeaf k, 0)) →
      (∀ p q : (ℝ × ℝ) × ℝ, p.1 = q.1 → ℓ p = ℓ q) → ∀ p ∈ tubeCellArc k,
        p ∉ tubeCellArc i ∪ tubeCellArc (i + 2) →
          ∃ c : ℝ, 0 < c ∧ ℓ p = c * ℓ (fourSpokeModelLeaf k, 0) := by
    intro k ℓ hlin hfst p hp hpX
    obtain ⟨c, hc, hpc⟩ := coord_pos_of_mem_tubeCellArc hp (fun h => hpX (hpoles p h))
    exact ⟨c, hc, (hfst p (c • fourSpokeModelLeaf k, 0) hpc).trans (hlin c)⟩
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
  · refine not_isPreconnected_of_sign hc2
      (fun p hp h => mem_tubeCellArc_union_of_snd_eq_zero hp h)
      (fun p hpA hpX => ?_) (fun p hpB hpX => ?_) hU hconn hA hB
    · obtain ⟨c, hc, h⟩ := hsign 1 (fun p => p.1.2) (fun c => by simp)
        (fun p q h => by rw [h]) p hpA hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc
    · obtain ⟨c, hc, h⟩ := hsign 3 (fun p => p.1.2) (fun c => by simp)
        (fun p q h => by rw [h]) p hpB hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc
  · refine not_isPreconnected_of_sign (ℓ := fun p => -p.1.1) hc1.neg
      (fun p hp h => mem_tubeCellArc_union_of_fst_eq_zero hp (neg_eq_zero.mp h))
      (fun p hpA hpX => ?_) (fun p hpB hpX => ?_) hU hconn hA hB
    · obtain ⟨c, hc, h⟩ := hsign 2 (fun p => -p.1.1) (fun c => by simp)
        (fun p q h => by rw [h]) p hpA hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc
    · obtain ⟨c, hc, h⟩ := hsign 0 (fun p => -p.1.1) (fun c => by simp)
        (fun p q h => by rw [h]) p hpB hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc
  · refine not_isPreconnected_of_sign (ℓ := fun p => -p.1.2) hc2.neg
      (fun p hp h => (mem_tubeCellArc_union_of_snd_eq_zero hp (neg_eq_zero.mp h)).symm)
      (fun p hpA hpX => ?_) (fun p hpB hpX => ?_) hU hconn hA hB
    · obtain ⟨c, hc, h⟩ := hsign 3 (fun p => -p.1.2) (fun c => by simp)
        (fun p q h => by rw [h]) p hpA hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc
    · obtain ⟨c, hc, h⟩ := hsign 1 (fun p => -p.1.2) (fun c => by simp)
        (fun p q h => by rw [h]) p hpB hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc
  · refine not_isPreconnected_of_sign hc1
      (fun p hp h => (mem_tubeCellArc_union_of_fst_eq_zero hp h).symm)
      (fun p hpA hpX => ?_) (fun p hpB hpX => ?_) hU hconn hA hB
    · obtain ⟨c, hc, h⟩ := hsign 0 (fun p => p.1.1) (fun c => by simp)
        (fun p q h => by rw [h]) p hpA hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc
    · obtain ⟨c, hc, h⟩ := hsign 2 (fun p => p.1.1) (fun c => by simp)
        (fun p q h => by rw [h]) p hpB hpX
      rw [h]
      norm_num [fourSpokeModelLeaf]
      exact hc

theorem mem_segment_zero_iff_smul {v p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) v ↔ ∃ c ∈ Icc (0 : ℝ) 1, p = c • v := by
  rw [segment_eq_image']
  simp only [sub_zero, zero_add, mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem centre_add_smul_sub_fst (x : ℝ × ℝ) (z s : ℝ) :
    (((0 : ℝ × ℝ), (1 / 2 : ℝ)) + s • ((x, z) - ((0 : ℝ × ℝ), (1 / 2 : ℝ)))).1 = s • x := by
  simp

theorem centre_add_smul_sub_snd (x : ℝ × ℝ) (z s : ℝ) :
    (((0 : ℝ × ℝ), (1 / 2 : ℝ)) + s • ((x, z) - ((0 : ℝ × ℝ), (1 / 2 : ℝ)))).2 =
      1 / 2 + s * (z - 1 / 2) := by
  simp

theorem coneSet_tubeMeridian (v : ℝ × ℝ) :
    coneSet ((0 : ℝ × ℝ), (1 / 2 : ℝ)) (tubeMeridian v) =
      segment ℝ (0 : ℝ × ℝ) v ×ˢ Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro p (rfl | ⟨q, hq, s, hs0, hs1, rfl⟩)
    · exact ⟨mem_segment_zero_iff_smul.mpr ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩, by norm_num⟩
    · obtain ⟨c, w, hc, hw, -, rfl⟩ := mem_tubeMeridian_iff.mp hq
      refine ⟨mem_segment_zero_iff_smul.mpr ⟨s * c, ⟨by nlinarith [hc.1], by nlinarith [hc.2]⟩,
        ?_⟩, ?_⟩
      · rw [centre_add_smul_sub_fst, smul_smul]
      · rw [mem_Icc, centre_add_smul_sub_snd]
        constructor <;> nlinarith [hw.1, hw.2]
  · rintro ⟨x, z⟩ ⟨hx, hz⟩
    obtain ⟨c, hc, rfl⟩ := mem_segment_zero_iff_smul.mp hx
    by_cases ho : c = 0 ∧ z = 1 / 2
    · obtain ⟨rfl, rfl⟩ := ho
      exact Or.inl (by simp)
    right
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = z - 1 / 2 := ⟨_, rfl⟩
    have hdabs : |d| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max c (2 * |d|) := ⟨_, rfl⟩
    have hcm : c ≤ m := hm ▸ le_max_left _ _
    have hdm : 2 * |d| ≤ m := hm ▸ le_max_right _ _
    have hmpos : 0 < m := by
      by_contra hle
      rw [not_lt] at hle
      have hc0 : c = 0 := le_antisymm (hcm.trans hle) hc.1
      have hd0 : |d| = 0 := le_antisymm (by linarith) (abs_nonneg d)
      exact ho ⟨hc0, by rw [abs_eq_zero] at hd0; linarith⟩
    have hm1 : m ≤ 1 := by rw [hm]; exact max_le hc.2 (by linarith)
    refine ⟨((c / m) • v, 1 / 2 + d / m), mem_tubeMeridian_iff.mpr ⟨c / m, 1 / 2 + d / m,
      ⟨div_nonneg hc.1 hmpos.le, (div_le_one hmpos).mpr hcm⟩, ?_, ?_, rfl⟩, m, hmpos, hm1, ?_⟩
    · have h1 : |d / m| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
        linarith
      rw [abs_le] at h1
      constructor <;> linarith [h1.1, h1.2]
    · rcases le_total c (2 * |d|) with hle | hle
      · have hmd : m = 2 * |d| := hm.trans (max_eq_right hle)
        right
        have hdne : d ≠ 0 := by
          intro h0
          rw [h0, abs_zero, mul_zero] at hmd
          exact hmpos.ne' hmd
        rcases abs_cases d with ⟨habs, -⟩ | ⟨habs, -⟩
        · right
          rw [hmd, habs]
          field_simp
          ring
        · left
          rw [hmd, habs]
          field_simp
          ring
      · left
        have hmc : m = c := hm.trans (max_eq_left hle)
        rw [hmc] at hmpos ⊢
        exact div_self hmpos.ne'
    · refine Prod.ext ?_ ?_
      · rw [centre_add_smul_sub_fst, smul_smul, mul_div_cancel₀ c hmpos.ne']
      · rw [centre_add_smul_sub_snd, hd]
        field_simp
        ring

theorem coneSet_tubeCellPoles :
    coneSet ((0 : ℝ × ℝ), (1 / 2 : ℝ))
        ({((0 : ℝ × ℝ), (0 : ℝ)), ((0 : ℝ × ℝ), (1 : ℝ))} : Set ((ℝ × ℝ) × ℝ)) =
      ({(0 : ℝ × ℝ)} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro p (rfl | ⟨q, hq, s, hs0, hs1, rfl⟩)
    · exact ⟨rfl, by norm_num⟩
    · rcases hq with rfl | rfl
      · refine ⟨by rw [mem_singleton_iff, centre_add_smul_sub_fst, smul_zero], ?_⟩
        rw [mem_Icc, centre_add_smul_sub_snd]
        constructor <;> nlinarith
      · refine ⟨by rw [mem_singleton_iff, centre_add_smul_sub_fst, smul_zero], ?_⟩
        rw [mem_Icc, centre_add_smul_sub_snd]
        constructor <;> nlinarith
  · rintro ⟨x, z⟩ ⟨hx, hz⟩
    rw [mem_singleton_iff] at hx
    subst hx
    by_cases hzz : z = 1 / 2
    · subst hzz
      exact Or.inl rfl
    right
    rcases lt_or_gt_of_ne hzz with hlt | hgt
    · refine ⟨((0 : ℝ × ℝ), (0 : ℝ)), Or.inl rfl, 1 - 2 * z, by linarith, by linarith [hz.1],
        Prod.ext ?_ ?_⟩
      · rw [centre_add_smul_sub_fst, smul_zero]
      · rw [centre_add_smul_sub_snd]
        ring
    · refine ⟨((0 : ℝ × ℝ), (1 : ℝ)), Or.inr rfl, 2 * z - 1, by linarith, by linarith [hz.2],
        Prod.ext ?_ ?_⟩
      · rw [centre_add_smul_sub_fst, smul_zero]
      · rw [centre_add_smul_sub_snd]
        ring

end DifferentialGeometry.Topology.PiecewiseLinear
