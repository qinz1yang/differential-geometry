/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IsSpineRevolutionOfOfMemCellInterior
import DifferentialGeometry.Topology.PiecewiseLinear.RevolutionOfCellInteriorSubsetInterior

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def unitSolidCylinder : Set E3 := {x | x 0 ^ 2 + x 2 ^ 2 ≤ 1 ∧ |x 1| ≤ 1}

def unitMeridianDisk : Set E3 := {x | x 0 ^ 2 + x 2 ^ 2 ≤ 1 ∧ x 1 = 0}

def unitMeridianCircle : Set E3 := {x | x 0 ^ 2 + x 2 ^ 2 = 1 ∧ x 1 = 0}

section Cylinder

private theorem continuous_radiusSq : Continuous fun p : E3 => p 0 ^ 2 + p 2 ^ 2 := by
  fun_prop

private theorem norm_sq_eq_coords (p : E3) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

private theorem norm_le_of_coords {p : E3} {R : ℝ} (hR : 0 ≤ R)
    (h : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 ≤ R ^ 2) : ‖p‖ ≤ R := by
  have h' : ‖p‖ ^ 2 ≤ R ^ 2 := by rw [norm_sq_eq_coords]; exact h
  nlinarith [norm_nonneg p]

private theorem norm_lt_of_coords {p : E3} {R : ℝ} (hR : 0 < R)
    (h : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 < R ^ 2) : ‖p‖ < R := by
  have h' : ‖p‖ ^ 2 < R ^ 2 := by rw [norm_sq_eq_coords]; exact h
  nlinarith [norm_nonneg p]

private theorem isClosed_setOf_band (a b c d : ℝ) :
    IsClosed {p : E3 | a ≤ p 0 ^ 2 + p 2 ^ 2 ∧ p 0 ^ 2 + p 2 ^ 2 ≤ b ∧ c ≤ p 1 ∧ p 1 ≤ d} :=
  (isClosed_le continuous_const continuous_radiusSq).inter
    ((isClosed_le continuous_radiusSq continuous_const).inter
      ((isClosed_le continuous_const (continuous_euclideanApply 1)).inter
        (isClosed_le (continuous_euclideanApply 1) continuous_const)))

theorem isCompact_unitSolidCylinder : IsCompact unitSolidCylinder := by
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le continuous_radiusSq continuous_const).inter
      (isClosed_le (continuous_euclideanApply 1).abs continuous_const)) ?_
  refine (isBounded_closedBall (x := (0 : E3)) (r := 2)).subset fun p hp => ?_
  obtain ⟨h1, h2⟩ := hp
  have h3 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
  rw [mem_closedBall_zero_iff]
  exact norm_le_of_coords (by norm_num) (by nlinarith)

theorem unitMeridianDisk_subset_unitSolidCylinder : unitMeridianDisk ⊆ unitSolidCylinder :=
  fun _ hx => ⟨hx.1, by rw [hx.2, abs_zero]; exact zero_le_one⟩

theorem unitMeridianCircle_subset_unitMeridianDisk : unitMeridianCircle ⊆ unitMeridianDisk :=
  fun _ hx => ⟨hx.1.le, hx.2⟩

private theorem openCore_subset_interior :
    {x : E3 | x 0 ^ 2 + x 2 ^ 2 < 1 ∧ |x 1| < 1} ⊆ interior unitSolidCylinder :=
  interior_maximal (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
    ((isOpen_lt continuous_radiusSq continuous_const).inter
      (isOpen_lt (continuous_euclideanApply 1).abs continuous_const))

theorem zero_mem_interior_unitSolidCylinder : (0 : E3) ∈ interior unitSolidCylinder :=
  openCore_subset_interior (by simp)

private theorem mem_puncturedDisk_iff {p : E3} :
    p ∈ unitMeridianDisk \ (unitMeridianCircle ∪ {0}) ↔
      p 1 = 0 ∧ 0 < p 0 ^ 2 + p 2 ^ 2 ∧ p 0 ^ 2 + p 2 ^ 2 < 1 := by
  constructor
  · rintro ⟨⟨hρ, h1⟩, hn⟩
    refine ⟨h1, lt_of_le_of_ne (by positivity) fun h0 => hn (Or.inr ?_),
      lt_of_le_of_ne hρ fun h => hn (Or.inl ⟨h, h1⟩)⟩
    have hp0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 2)]
    have hp2 : p 2 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 2)]
    refine PiLp.ext fun i => ?_
    fin_cases i
    · exact hp0
    · exact h1
    · exact hp2
  · rintro ⟨h1, hpos, hlt⟩
    refine ⟨⟨hlt.le, h1⟩, ?_⟩
    rintro (h | h)
    · exact hlt.ne h.1
    · have h0 : p = 0 := h
      rw [h0] at hpos
      simp at hpos

theorem unitMeridianDisk_sdiff_subset_interior :
    unitMeridianDisk \ (unitMeridianCircle ∪ {0}) ⊆ interior unitSolidCylinder := by
  intro p hp
  obtain ⟨h1, -, hlt⟩ := mem_puncturedDisk_iff.mp hp
  exact openCore_subset_interior ⟨hlt, by rw [h1, abs_zero]; exact zero_lt_one⟩

end Cylinder

section Profile

private theorem exists_radialProfile :
    ∃ r : ℤ → ℝ, StrictMono r ∧ (∀ i, 0 < r i) ∧ (∀ i, r i < 1) ∧
      (∀ δ : ℝ, 0 < δ → ∃ k, r k < δ) ∧ ∀ δ : ℝ, 0 < δ → ∃ k, 1 - r k < δ := by
  refine ⟨fun i => (2 : ℝ) ^ i / (1 + (2 : ℝ) ^ i), ?_, fun i => by positivity, ?_, ?_, ?_⟩
  · intro a b hab
    have h := zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) hab
    have ha : (0 : ℝ) < 2 ^ a := by positivity
    change (2 : ℝ) ^ a / (1 + 2 ^ a) < 2 ^ b / (1 + 2 ^ b)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · intro i
    have : (0 : ℝ) < 2 ^ i := by positivity
    change (2 : ℝ) ^ i / (1 + 2 ^ i) < 1
    rw [div_lt_one (by positivity)]
    linarith
  · intro δ hδ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨-(n : ℤ), ?_⟩
    have h2 : (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ)⁻¹ ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
    have hpos : (0 : ℝ) < 2 ^ (-(n : ℤ)) := by positivity
    change (2 : ℝ) ^ (-(n : ℤ)) / (1 + 2 ^ (-(n : ℤ))) < δ
    calc (2 : ℝ) ^ (-(n : ℤ)) / (1 + 2 ^ (-(n : ℤ))) ≤ 2 ^ (-(n : ℤ)) :=
          div_le_self hpos.le (by linarith)
      _ < δ := by rw [h2]; exact hn
  · intro δ hδ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨(n : ℤ), ?_⟩
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    have hne : (1 + (2 : ℝ) ^ n) ≠ 0 := by positivity
    change 1 - (2 : ℝ) ^ (n : ℤ) / (1 + 2 ^ (n : ℤ)) < δ
    rw [zpow_natCast]
    have heq : 1 - (2 : ℝ) ^ n / (1 + 2 ^ n) = 1 / (1 + 2 ^ n) := by
      rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
      ring
    rw [heq]
    calc 1 / (1 + (2 : ℝ) ^ n) < 1 / 2 ^ n := one_div_lt_one_div_of_lt hpos (by linarith)
      _ = (2 : ℝ)⁻¹ ^ n := by rw [one_div, inv_pow]
      _ < δ := hn

end Profile

section Planar

private theorem revolutionOf_planarPoint_rectTwo {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    revolutionOf (planarPoint '' rectTwo a b c d) =
      {p : E3 | a ^ 2 ≤ p 0 ^ 2 + p 2 ^ 2 ∧ p 0 ^ 2 + p 2 ^ 2 ≤ b ^ 2 ∧ c ≤ p 1 ∧ p 1 ≤ d} := by
  ext p
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, -, hq0, hq1, hsq⟩
    rw [planarPoint_apply_zero] at hq0 hsq
    rw [planarPoint_apply_one] at hq1
    obtain ⟨⟨hx0, hx0'⟩, hx1, hx1'⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hsq]
      nlinarith
    · rw [← hsq]
      nlinarith
    · rw [← hq1]
      exact hx1
    · rw [← hq1]
      exact hx1'
  · rintro ⟨h1, h2, h3, h4⟩
    have hρ : 0 ≤ p 0 ^ 2 + p 2 ^ 2 := by positivity
    have hsa : a ≤ Real.sqrt (p 0 ^ 2 + p 2 ^ 2) := by
      calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
        _ ≤ _ := Real.sqrt_le_sqrt h1
    have hsb : Real.sqrt (p 0 ^ 2 + p 2 ^ 2) ≤ b := by
      calc Real.sqrt (p 0 ^ 2 + p 2 ^ 2) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h2
        _ = b := Real.sqrt_sq (ha.trans hab)
    obtain ⟨y, hy0, hy1⟩ : ∃ y : EuclideanSpace ℝ (Fin 2),
        y 0 = Real.sqrt (p 0 ^ 2 + p 2 ^ 2) ∧ y 1 = p 1 :=
      ⟨EuclideanSpace.single 0 (Real.sqrt (p 0 ^ 2 + p 2 ^ 2)) + EuclideanSpace.single 1 (p 1),
        by simp, by simp⟩
    refine ⟨planarPoint y, ⟨y, ⟨?_, ?_⟩, rfl⟩, planarPoint_apply_two _, ?_, ?_, ?_⟩
    · rw [hy0]
      exact ⟨hsa, hsb⟩
    · rw [hy1]
      exact ⟨h3, h4⟩
    · rw [planarPoint_apply_zero, hy0]
      exact Real.sqrt_nonneg _
    · rw [planarPoint_apply_one, hy1]
    · rw [planarPoint_apply_zero, hy0, Real.sq_sqrt hρ]

private theorem segment_planarPoint_single {a b : ℝ} (hab : a < b) :
    segment ℝ (planarPoint (EuclideanSpace.single 0 a)) (planarPoint (EuclideanSpace.single 0 b)) =
      planarPoint '' rectTwo a b 0 0 := by
  ext p
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    obtain ⟨y, hy, hy0, hy1⟩ : ∃ y : EuclideanSpace ℝ (Fin 2),
        y = s • EuclideanSpace.single 0 a + t • EuclideanSpace.single 0 b ∧
          y 0 = s * a + t * b ∧ y 1 = 0 :=
      ⟨_, rfl, by simp, by simp⟩
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · rw [hy0]
      have hs' : s = 1 - t := by linarith
      subst hs'
      constructor <;> nlinarith [mul_nonneg ht (sub_nonneg.mpr hab.le),
        mul_nonneg hs (sub_nonneg.mpr hab.le)]
    · rw [hy1]
      exact left_mem_Icc.mpr le_rfl
    · rw [hy]
      exact planarPoint_smul_add_smul _ _ _ _
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    have hx1' : x 1 = 0 := le_antisymm hx1.2 hx1.1
    have hba : b - a ≠ 0 := by linarith
    refine ⟨(b - x 0) / (b - a), (x 0 - a) / (b - a), div_nonneg (by linarith [hx0.2])
      (by linarith), div_nonneg (by linarith [hx0.1]) (by linarith), ?_, ?_⟩
    · rw [← add_div, div_eq_one_iff_eq hba]
      ring
    · obtain ⟨y, hy, hy0, hy1⟩ : ∃ y : EuclideanSpace ℝ (Fin 2),
          y = ((b - x 0) / (b - a)) • EuclideanSpace.single 0 a +
            ((x 0 - a) / (b - a)) • EuclideanSpace.single 0 b ∧
          y 0 = (b - x 0) / (b - a) * a + (x 0 - a) / (b - a) * b ∧ y 1 = 0 :=
        ⟨_, rfl, by simp, by simp⟩
      rw [← planarPoint_smul_add_smul, ← hy]
      congr 1
      refine PiLp.ext fun i => ?_
      fin_cases i
      · change y 0 = x 0
        rw [hy0, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hba]
        ring
      · change y 1 = x 1
        rw [hy1, hx1']

end Planar

section Tower

private noncomputable def towerRect (r w : ℤ → ℝ) (k : ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectTwo (r k - w k) (r (k + 1) + w k) (-w k) (w k)

private noncomputable def towerPoint (r : ℤ → ℝ) (k : ℤ) : E3 :=
  planarPoint (EuclideanSpace.single 0 (r k))

private noncomputable def towerSolid (r w : ℤ → ℝ) (k : ℤ) : Set E3 :=
  revolutionOf (planarPoint '' towerRect r w k)

private noncomputable def towerAnnulus (r : ℤ → ℝ) (k : ℤ) : Set E3 :=
  revolutionOf (segment ℝ (towerPoint r k) (towerPoint r (k + 1)))

private theorem towerPoint_apply_zero (r : ℤ → ℝ) (k : ℤ) : towerPoint r k 0 = r k := by
  simp [towerPoint]

private theorem towerPoint_apply_one (r : ℤ → ℝ) (k : ℤ) : towerPoint r k 1 = 0 := by
  simp [towerPoint]

private theorem towerPoint_apply_two (r : ℤ → ℝ) (k : ℤ) : towerPoint r k 2 = 0 := by
  simp [towerPoint]

variable {r w : ℤ → ℝ}

private theorem single_mem_interior_towerRect {k : ℤ} {s : ℝ} (hw : 0 < w k)
    (h1 : r k - w k < s) (h2 : s < r (k + 1) + w k) :
    EuclideanSpace.single 0 s ∈ interior (towerRect r w k) :=
  single_mem_interior_rectTwo h1 h2 (by linarith) hw

private theorem towerRect_halfPlane {k : ℤ} (hwr : w k < r k) :
    ∀ p ∈ planarPoint '' towerRect r w k, p 2 = 0 ∧ 0 < p 0 := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨planarPoint_apply_two x, ?_⟩
  rw [planarPoint_apply_zero]
  have := hx.1.1
  linarith

private theorem towerRect_cell {k : ℤ} (hw : 0 < w k) (hrs : r k < r (k + 1)) :
    IsTopologicalCellWithInterior 2 (planarPoint '' towerRect r w k)
      (planarPoint '' interior (towerRect r w k)) :=
  isTopologicalCellWithInterior_planarImage (convex_rectTwo _ _ _ _) (isClosed_rectTwo _ _ _ _)
    (isBounded_rectTwo _ _ _ _) ⟨_, single_mem_interior_towerRect (s := r k) hw
      (by linarith) (by linarith)⟩

private theorem segment_subset_towerRect {k : ℤ} (hw : 0 < w k) (hrs : r k < r (k + 1)) :
    segment ℝ (towerPoint r k) (towerPoint r (k + 1)) ⊆
      planarPoint '' interior (towerRect r w k) := by
  rintro _ ⟨s, t, hs, ht, hst, rfl⟩
  have hu := single_mem_interior_towerRect (s := r k) hw (by linarith) (by linarith)
  have hv := single_mem_interior_towerRect (s := r (k + 1)) hw (by linarith) (by linarith)
  exact ⟨_, (convex_rectTwo _ _ _ _).interior hu hv hs ht hst,
    planarPoint_smul_add_smul _ _ _ _⟩

private theorem towerPoint_ne {k : ℤ} (hrs : r k < r (k + 1)) :
    towerPoint r k ≠ towerPoint r (k + 1) := by
  intro h
  have h0 := congrArg (fun p : E3 => p 0) h
  simp only [towerPoint_apply_zero] at h0
  exact hrs.ne h0

private theorem towerRect_overlap {k : ℤ} (hw : 0 < w k) (hw' : 0 < w (k + 1))
    (hrs : r k < r (k + 1)) (hrs' : r (k + 1) < r (k + 1 + 1)) :
    IsTopologicalCell 2
      (planarPoint '' towerRect r w k ∩ planarPoint '' towerRect r w (k + 1)) := by
  rw [← image_inter planarPoint_injective, towerRect, towerRect, rectTwo_inter]
  exact isTopologicalCell_planarImage (convex_rectTwo _ _ _ _) (isClosed_rectTwo _ _ _ _)
    (isBounded_rectTwo _ _ _ _) ⟨EuclideanSpace.single 0 (r (k + 1)),
      single_mem_interior_rectTwo (max_lt (by linarith) (by linarith))
        (lt_min (by linarith) (by linarith)) (max_lt (by linarith) (by linarith))
        (lt_min hw hw')⟩

private theorem towerRect_apart {k : ℤ} (hgap : r (k + 1) + w k < r (k + 2) - w (k + 2)) :
    planarPoint '' towerRect r w k ∩ planarPoint '' towerRect r w (k + 2) = ∅ := by
  rw [← image_inter planarPoint_injective, towerRect, towerRect, rectTwo_inter,
    rectTwo_eq_empty (lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le hgap (le_max_right _ _))),
    image_empty]

private theorem int_add_val_succ {n : ℕ} (i : ℤ) (j : Fin n) :
    i + ((j.succ : ℕ) : ℤ) = i + ((j : ℕ) : ℤ) + 1 := by
  rw [Fin.val_succ]
  push_cast
  ring

private theorem isRevolvedTorusChain_tower (hr : StrictMono r) (hw : ∀ k, 0 < w k)
    (hwr : ∀ k, w k < r k) (hgap : ∀ k, r (k + 1) + w k < r (k + 2) - w (k + 2)) (i : ℤ) :
    IsRevolvedTorusChain (fun j : Fin 4 => towerPoint r (i + ((j : ℕ) : ℤ)))
      (fun j : Fin 3 => planarPoint '' towerRect r w (i + ((j : ℕ) : ℤ)))
      (fun j : Fin 3 => planarPoint '' interior (towerRect r w (i + ((j : ℕ) : ℤ))))
      (fun j : Fin 4 => revolutionOf {towerPoint r (i + ((j : ℕ) : ℤ))})
      (fun j : Fin 3 => towerAnnulus r (i + ((j : ℕ) : ℤ)))
      (fun j : Fin 3 => towerSolid r w (i + ((j : ℕ) : ℤ)))
      (fun j : Fin 3 => frontier (towerSolid r w (i + ((j : ℕ) : ℤ)))) where
  chain :=
    { halfPlane := fun j => towerRect_halfPlane (hwr _)
      cell := fun j => towerRect_cell (hw _) (hr (lt_add_one _))
      interiorSubset := fun j => image_mono interior_subset
      segmentSubset := fun j => by
        rw [Fin.val_castSucc, int_add_val_succ]
        exact segment_subset_towerRect (hw _) (hr (lt_add_one _))
      consecutiveNe := fun j => by
        rw [Fin.val_castSucc, int_add_val_succ]
        exact towerPoint_ne (hr (lt_add_one _))
      overlap := fun j => by
        rw [Fin.val_castSucc, int_add_val_succ]
        exact towerRect_overlap (hw _) (hw _) (hr (lt_add_one _)) (hr (lt_add_one _))
      apart := by
        change planarPoint '' towerRect r w (i + ((0 : ℕ) : ℤ)) ∩
          planarPoint '' towerRect r w (i + ((2 : ℕ) : ℤ)) = ∅
        rw [Nat.cast_zero, add_zero, Nat.cast_ofNat]
        exact towerRect_apart (hgap i) }
  circleEq := fun _ => rfl
  annulusEq := fun j => by
    rw [Fin.val_castSucc, int_add_val_succ]
    rfl
  solidEq := fun _ => rfl
  isSolidTorus := fun j => by
    obtain ⟨e, -⟩ := isSpine_revolutionOf_of_mem_cellInterior
      (towerRect_cell (hw _) (hr (lt_add_one _))) (towerRect_halfPlane (hwr _))
      (p := towerPoint r (i + ((j : ℕ) : ℤ)))
      ⟨_, single_mem_interior_towerRect (s := r (i + ((j : ℕ) : ℤ))) (hw _)
        (by linarith [hw (i + ((j : ℕ) : ℤ))])
        (by linarith [hw (i + ((j : ℕ) : ℤ)), hr (lt_add_one (i + ((j : ℕ) : ℤ)))]), rfl⟩
    exact ⟨e.symm⟩
  boundaryEq := fun _ => rfl
  annulusSubset := fun j =>
    (revolutionOf_mono (segment_subset_towerRect (k := i + ((j : ℕ) : ℤ)) (hw _)
      (hr (lt_add_one _)))).trans
      (revolutionOf_cellInterior_subset_interior (towerRect_cell (k := i + ((j : ℕ) : ℤ)) (hw _)
        (hr (lt_add_one _))) (towerRect_halfPlane (hwr _)))

private theorem mem_of_mem_closure_lower {X : Type*} [TopologicalSpace X] {S : ℤ → Set X}
    (hS : ∀ i, IsClosed (S i)) {F : Set X} (hF : IsClosed F) {i0 : ℤ}
    (hsub : ∀ i < i0, S i ⊆ F) {m : ℤ} {x : X} (hx : x ∈ closure (⋃ i, ⋃ (_ : i ≤ m), S i))
    (hxF : x ∉ F) : x ∈ ⋃ i, ⋃ (_ : i ≤ m), S i := by
  have hcl : IsClosed (F ∪ ⋃ i ∈ Finset.Icc i0 m, S i) :=
    hF.union (isClosed_biUnion_finset fun i _ => hS i)
  have hsub' : (⋃ i, ⋃ (_ : i ≤ m), S i) ⊆ F ∪ ⋃ i ∈ Finset.Icc i0 m, S i := by
    refine iUnion₂_subset fun i hi y hy => ?_
    by_cases h : i < i0
    · exact Or.inl (hsub i h hy)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_Icc.mpr ⟨not_lt.mp h, hi⟩, hy⟩)
  rcases closure_minimal hsub' hcl hx with h | h
  · exact absurd h hxF
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨i, (Finset.mem_Icc.mp hi).2, hxi⟩

private theorem mem_of_mem_closure_upper {X : Type*} [TopologicalSpace X] {S : ℤ → Set X}
    (hS : ∀ i, IsClosed (S i)) {F : Set X} (hF : IsClosed F) {i1 : ℤ}
    (hsub : ∀ i, i1 ≤ i → S i ⊆ F) {m : ℤ} {x : X}
    (hx : x ∈ closure (⋃ i, ⋃ (_ : m ≤ i), S i)) (hxF : x ∉ F) :
    x ∈ ⋃ i, ⋃ (_ : m ≤ i), S i := by
  have hcl : IsClosed (F ∪ ⋃ i ∈ Finset.Icc m i1, S i) :=
    hF.union (isClosed_biUnion_finset fun i _ => hS i)
  have hsub' : (⋃ i, ⋃ (_ : m ≤ i), S i) ⊆ F ∪ ⋃ i ∈ Finset.Icc m i1, S i := by
    refine iUnion₂_subset fun i hi y hy => ?_
    by_cases h : i1 ≤ i
    · exact Or.inl (hsub i h hy)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_Icc.mpr ⟨hi, (not_le.mp h).le⟩, hy⟩)
  rcases closure_minimal hsub' hcl hx with h | h
  · exact absurd h hxF
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨i, (Finset.mem_Icc.mp hi).1, hxi⟩

private theorem exists_nhds_finite_of_tails {X : Type*} [TopologicalSpace X] {S : ℤ → Set X}
    {F G : Set X} (hF : IsClosed F) (hG : IsClosed G) {i0 i1 : ℤ} (hlo : ∀ i < i0, S i ⊆ F)
    (hhi : ∀ i, i1 ≤ i → S i ⊆ G) {y : X} (hyF : y ∉ F) (hyG : y ∉ G) :
    ∃ U ∈ 𝓝 y, {i | (S i ∩ U).Nonempty}.Finite := by
  refine ⟨(F ∪ G)ᶜ, (hF.union hG).isOpen_compl.mem_nhds fun h => by
    rcases h with h | h
    exacts [hyF h, hyG h],
    (Set.finite_Ico i0 i1).subset ?_⟩
  rintro i ⟨z, hzS, hzU⟩
  exact ⟨not_lt.mp fun h => hzU (Or.inl (hlo i h hzS)),
    not_le.mp fun h => hzU (Or.inr (hhi i h hzS))⟩

private theorem exists_near_point {p : E3} {a b d : ℝ} (hab : a ≤ b) (hd : 0 ≤ d)
    (had : 0 < a - d) (h1 : (a - d) ^ 2 ≤ p 0 ^ 2 + p 2 ^ 2)
    (h2 : p 0 ^ 2 + p 2 ^ 2 ≤ (b + d) ^ 2) (h3 : -d ≤ p 1) (h4 : p 1 ≤ d) :
    ∃ q : E3, (a ^ 2 ≤ q 0 ^ 2 + q 2 ^ 2 ∧ q 0 ^ 2 + q 2 ^ 2 ≤ b ^ 2 ∧ 0 ≤ q 1 ∧ q 1 ≤ 0) ∧
      dist p q ≤ 2 * d := by
  obtain ⟨t, ht0, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 = p 0 ^ 2 + p 2 ^ 2 :=
    ⟨Real.sqrt (p 0 ^ 2 + p 2 ^ 2), Real.sqrt_pos.mpr (by nlinarith),
      Real.sq_sqrt (by positivity)⟩
  have hta : a - d ≤ t := by nlinarith
  have htb : t ≤ b + d := by nlinarith
  obtain ⟨s, hsa, hsb, hts⟩ : ∃ s : ℝ, a ≤ s ∧ s ≤ b ∧ (t - s) ^ 2 ≤ d ^ 2 := by
    rcases le_total t a with h | h
    · exact ⟨a, le_rfl, hab, by nlinarith⟩
    · rcases le_total t b with h' | h'
      · exact ⟨t, h, h', by nlinarith⟩
      · exact ⟨b, hab, le_rfl, by nlinarith⟩
  have hu : s / t * t = s := div_mul_cancel₀ s ht0.ne'
  obtain ⟨q, hq0, hq1, hq2⟩ : ∃ q : E3, q 0 = s / t * p 0 ∧ q 1 = 0 ∧ q 2 = s / t * p 2 :=
    ⟨EuclideanSpace.single 0 (s / t * p 0) + EuclideanSpace.single 2 (s / t * p 2),
      by simp, by simp, by simp⟩
  refine ⟨q, ?_, ?_⟩
  · have hq : (s / t * p 0) ^ 2 + (s / t * p 2) ^ 2 = s ^ 2 := by
      calc (s / t * p 0) ^ 2 + (s / t * p 2) ^ 2 = (s / t) ^ 2 * (p 0 ^ 2 + p 2 ^ 2) := by ring
        _ = (s / t * t) ^ 2 := by rw [← ht2]; ring
        _ = s ^ 2 := by rw [hu]
    rw [hq0, hq1, hq2, hq]
    have ha0 : 0 ≤ a := by linarith
    exact ⟨by nlinarith, by nlinarith, le_rfl, le_rfl⟩
  · rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
    simp only [Real.dist_eq, sq_abs]
    rw [hq0, hq1, hq2, sub_zero]
    have hkey : (p 0 - s / t * p 0) ^ 2 + p 1 ^ 2 + (p 2 - s / t * p 2) ^ 2 =
        (t - s) ^ 2 + p 1 ^ 2 := by
      calc (p 0 - s / t * p 0) ^ 2 + p 1 ^ 2 + (p 2 - s / t * p 2) ^ 2 =
            (1 - s / t) ^ 2 * (p 0 ^ 2 + p 2 ^ 2) + p 1 ^ 2 := by ring
        _ = (t - s / t * t) ^ 2 + p 1 ^ 2 := by rw [← ht2]; ring
        _ = (t - s) ^ 2 + p 1 ^ 2 := by rw [hu]
    rw [hkey]
    have h5 : p 1 ^ 2 ≤ d ^ 2 := sq_le_sq' h3 h4
    calc Real.sqrt ((t - s) ^ 2 + p 1 ^ 2) ≤ Real.sqrt ((2 * d) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * d := Real.sqrt_sq (by linarith)

theorem exists_isRevolvedTorusChain_tower {O : Set E3} (hO : IsOpen O)
    (hMO : unitMeridianDisk \ (unitMeridianCircle ∪ {0}) ⊆ O) :
    ∃ (Pt : ℤ → E3) (Dp Dpint J A S T : ℤ → Set E3),
      (∀ i : ℤ, IsRevolvedTorusChain (fun j : Fin 4 => Pt (i + ((j : ℕ) : ℤ)))
        (fun j : Fin 3 => Dp (i + ((j : ℕ) : ℤ))) (fun j : Fin 3 => Dpint (i + ((j : ℕ) : ℤ)))
        (fun j : Fin 4 => J (i + ((j : ℕ) : ℤ))) (fun j : Fin 3 => A (i + ((j : ℕ) : ℤ)))
        (fun j : Fin 3 => S (i + ((j : ℕ) : ℤ))) (fun j : Fin 3 => T (i + ((j : ℕ) : ℤ)))) ∧
      (∀ i, S i ⊆ O) ∧ (∀ i, IsCompact (A i)) ∧
      (∀ i k : ℤ, 2 ≤ |i - k| → Disjoint (S i) (S k)) ∧
      ⋃ i, A i = unitMeridianDisk \ (unitMeridianCircle ∪ {0}) ∧
      (∀ m : ℤ, closure (⋃ i, ⋃ (_ : i ≤ m), S i) = (⋃ i, ⋃ (_ : i ≤ m), S i) ∪ {0}) ∧
      (∀ m : ℤ, closure (⋃ i, ⋃ (_ : m ≤ i), S i) =
        (⋃ i, ⋃ (_ : m ≤ i), S i) ∪ unitMeridianCircle) ∧
      ∀ y ∈ unitSolidCylinder, y ≠ 0 → y ∉ unitMeridianCircle →
        ∃ U ∈ 𝓝 y, {i | (S i ∩ U).Nonempty}.Finite := by
  obtain ⟨r, hr, hr0, hr1, hlow, hhigh⟩ := exists_radialProfile
  have hrs : ∀ k, r k < r (k + 1) := fun k => hr (lt_add_one k)
  have hA : ∀ k, towerAnnulus r k = {p : E3 | r k ^ 2 ≤ p 0 ^ 2 + p 2 ^ 2 ∧
      p 0 ^ 2 + p 2 ^ 2 ≤ r (k + 1) ^ 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 0} := fun k => by
    rw [towerAnnulus, towerPoint, towerPoint, segment_planarPoint_single (hrs k),
      revolutionOf_planarPoint_rectTwo (hr0 k).le (hrs k).le]
  have hAM : ∀ k, towerAnnulus r k ⊆ unitMeridianDisk \ (unitMeridianCircle ∪ {0}) := by
    intro k p hp
    rw [hA k] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have h5 := hr0 k
    have h6 := hr1 (k + 1)
    have h7 := hr0 (k + 1)
    exact mem_puncturedDisk_iff.mpr ⟨le_antisymm h4 h3, by nlinarith, by nlinarith⟩
  have hAc : ∀ k, IsCompact (towerAnnulus r k) := by
    intro k
    rw [hA k]
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_setOf_band _ _ _ _) ?_
    refine (isBounded_closedBall (x := (0 : E3)) (r := 1)).subset fun p hp => ?_
    obtain ⟨-, h2, h3, h4⟩ := hp
    have h5 : p 1 = 0 := le_antisymm h4 h3
    have h6 := hr1 (k + 1)
    have h7 := hr0 (k + 1)
    rw [mem_closedBall_zero_iff]
    refine norm_le_of_coords zero_le_one ?_
    rw [h5]
    nlinarith
  choose ε hε hεO using fun k => (hAc k).exists_thickening_subset_open hO ((hAM k).trans hMO)
  obtain ⟨w, hw0, hwε, hwlo, hwhi⟩ : ∃ w : ℤ → ℝ, (∀ k, 0 < w k) ∧ (∀ k, w k ≤ ε k / 4) ∧
      (∀ k, w k ≤ (r k - r (k - 1)) / 3) ∧ ∀ k, w k ≤ (r (k + 2) - r (k + 1)) / 3 := by
    refine ⟨fun k => min (ε k / 4) (min ((r k - r (k - 1)) / 3) ((r (k + 2) - r (k + 1)) / 3)),
      fun k => ?_, fun k => min_le_left _ _,
      fun k => (min_le_right _ _).trans (min_le_left _ _),
      fun k => (min_le_right _ _).trans (min_le_right _ _)⟩
    have h1 := hε k
    have h2 := hr (show k - 1 < k by omega)
    have h3 := hr (show k + 1 < k + 2 by omega)
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hwr : ∀ k, w k < r k := fun k => by linarith [hwlo k, hr0 (k - 1), hr0 k]
  have hgap : ∀ k, r (k + 1) + w k < r (k + 2) - w (k + 2) := by
    intro k
    have h1 := hwlo (k + 2)
    rw [show k + 2 - 1 = k + 1 by ring] at h1
    linarith [hwhi k, hr (show k + 1 < k + 2 by omega)]
  have hSeq : ∀ k, towerSolid r w k = {p : E3 | (r k - w k) ^ 2 ≤ p 0 ^ 2 + p 2 ^ 2 ∧
      p 0 ^ 2 + p 2 ^ 2 ≤ (r (k + 1) + w k) ^ 2 ∧ -w k ≤ p 1 ∧ p 1 ≤ w k} := fun k => by
    rw [towerSolid, towerRect, revolutionOf_planarPoint_rectTwo (by linarith [hwr k])
      (by linarith [hwr k, hw0 k, hrs k])]
  have hS : ∀ k (p : E3), p ∈ towerSolid r w k ↔
      (r k - w k) ^ 2 ≤ p 0 ^ 2 + p 2 ^ 2 ∧ p 0 ^ 2 + p 2 ^ 2 ≤ (r (k + 1) + w k) ^ 2 ∧
        -w k ≤ p 1 ∧ p 1 ≤ w k := fun k p => Set.ext_iff.mp (hSeq k) p
  have hSclosed : ∀ k, IsClosed (towerSolid r w k) := fun k => by
    rw [hSeq k]
    exact isClosed_setOf_band _ _ _ _
  have hSO : ∀ k, towerSolid r w k ⊆ O := by
    intro k p hp
    obtain ⟨h1, h2, h3, h4⟩ := (hS k p).mp hp
    obtain ⟨q, hq, hpq⟩ := exists_near_point (hrs k).le (hw0 k).le
      (by linarith [hwr k]) h1 h2 h3 h4
    refine hεO k (mem_thickening_iff.mpr ⟨q, ?_, ?_⟩)
    · rw [hA k]
      exact hq
    · linarith [hwε k, hε k]
  have hfar : ∀ i k, i + 2 ≤ k → r (i + 1) + w i < r k - w k := by
    intro i k hik
    have h1 := hwlo k
    have h2 := hwhi i
    have h3 : r (i + 1) ≤ r (k - 1) := hr.monotone (by omega)
    have h4 : r (i + 2) ≤ r k := hr.monotone (by omega)
    have h5 := hr (show i + 1 < i + 2 by omega)
    linarith
  have hdisj : ∀ i k : ℤ, 2 ≤ |i - k| → Disjoint (towerSolid r w i) (towerSolid r w k) := by
    have key : ∀ i k, i + 2 ≤ k → Disjoint (towerSolid r w i) (towerSolid r w k) := by
      intro i k hik
      rw [Set.disjoint_left]
      intro p hpi hpk
      obtain ⟨-, h2, -, -⟩ := (hS i p).mp hpi
      obtain ⟨h1, -, -, -⟩ := (hS k p).mp hpk
      have h := hfar i k hik
      have hpos : 0 < r (i + 1) + w i := by linarith [hr0 (i + 1), hw0 i]
      nlinarith [mul_pos (sub_pos.mpr h) (by linarith : 0 < r k - w k + (r (i + 1) + w i))]
    intro i k hik
    rcases le_abs.mp hik with h | h
    · exact (key k i (by omega)).symm
    · exact key i k (by omega)
  have hpoint : ∀ k, towerPoint r k ∈ towerSolid r w k := fun k => by
    rw [hS, towerPoint_apply_zero, towerPoint_apply_one, towerPoint_apply_two]
    have h1 := hwr k
    have h2 := hw0 k
    have h3 := hrs k
    refine ⟨by nlinarith, by nlinarith, by linarith, by linarith⟩
  have hSbound : ∀ k (p : E3), p ∈ towerSolid r w k → p 0 ^ 2 + p 2 ^ 2 ≤ 1 := by
    intro k p hp
    obtain ⟨-, h2, -, -⟩ := (hS k p).mp hp
    have h3 : r (k + 1) + w k < 1 := by linarith [hwhi k, hr1 (k + 2), hr1 (k + 1)]
    have h4 : 0 < r (k + 1) + w k := by linarith [hr0 (k + 1), hw0 k]
    nlinarith
  have hB1 : ∀ δ : ℝ, 0 < δ → ∃ i0 : ℤ, ∀ i < i0, towerSolid r w i ⊆ closedBall 0 δ := by
    intro δ hδ
    obtain ⟨k, hk⟩ := hlow (δ / 3) (by positivity)
    refine ⟨k, fun i hi p hp => ?_⟩
    obtain ⟨-, h2, h3, h4⟩ := (hS i p).mp hp
    have hrk : r (i + 1) ≤ r k := hr.monotone (by omega)
    have h5 := hwr i
    have h6 := hrs i
    have h7 := hw0 i
    have h8 : r (i + 1) + w i ≤ 2 * r k := by linarith
    have h9 : 0 ≤ r (i + 1) + w i := by linarith
    have h10 : p 1 ^ 2 ≤ w i ^ 2 := sq_le_sq' h3 h4
    have h11 : (r (i + 1) + w i) ^ 2 ≤ (2 * r k) ^ 2 := pow_le_pow_left₀ h9 h8 2
    have h12 : w i ^ 2 ≤ r k ^ 2 := pow_le_pow_left₀ h7.le (by linarith) 2
    have h13 : 0 < r k := hr0 k
    rw [mem_closedBall_zero_iff]
    refine norm_le_of_coords hδ.le ?_
    nlinarith [mul_pos (by linarith : 0 < δ - 3 * r k) (by linarith : 0 < δ + 3 * r k)]
  have hB2 : ∀ δ : ℝ, 0 < δ → ∃ i1 : ℤ, ∀ i, i1 ≤ i →
      towerSolid r w i ⊆ {p : E3 | |p 1| ≤ δ} := by
    intro δ hδ
    obtain ⟨k, hk⟩ := hhigh δ hδ
    refine ⟨k, fun i hi p hp => ?_⟩
    obtain ⟨-, -, h3, h4⟩ := (hS i p).mp hp
    have h5 : r k ≤ r (i + 1) := hr.monotone (by omega)
    have h6 := hwhi i
    have h7 := hr1 (i + 2)
    change |p 1| ≤ δ
    rw [abs_le]
    constructor <;> linarith
  have hB3 : ∀ c : ℝ, 0 < c → c < 1 → ∃ i1 : ℤ, ∀ i, i1 ≤ i →
      towerSolid r w i ⊆ {p : E3 | c ≤ p 0 ^ 2 + p 2 ^ 2} := by
    intro c hc0 hc1
    obtain ⟨k, hk⟩ := hhigh ((1 - c) / 4) (by linarith)
    refine ⟨k, fun i hi p hp => ?_⟩
    obtain ⟨h1, -, -, -⟩ := (hS i p).mp hp
    have h5 : r k ≤ r i := hr.monotone hi
    have h6 := hwhi i
    have h7 := hr1 (i + 2)
    have h8 := hrs i
    have h9 : (1 + c) / 2 < r i - w i := by linarith
    have h10 : 0 < (1 + c) / 2 := by linarith
    change c ≤ p 0 ^ 2 + p 2 ^ 2
    nlinarith [mul_pos (sub_pos.mpr h9) (by linarith : 0 < r i - w i + (1 + c) / 2),
      sq_nonneg ((1 - c) / 2)]
  have hupperF : ∀ x : E3, x 0 ^ 2 + x 2 ^ 2 ≤ 1 → x ∉ unitMeridianCircle →
      ∃ (F : Set E3) (i1 : ℤ), IsClosed F ∧ (∀ i, i1 ≤ i → towerSolid r w i ⊆ F) ∧ x ∉ F := by
    intro x hρx hxR
    by_cases hx1 : x 1 = 0
    · have hlt : x 0 ^ 2 + x 2 ^ 2 < 1 := lt_of_le_of_ne hρx fun h => hxR ⟨h, hx1⟩
      have hρ0 : 0 ≤ x 0 ^ 2 + x 2 ^ 2 := by positivity
      obtain ⟨i1, hi1⟩ := hB3 ((x 0 ^ 2 + x 2 ^ 2 + 1) / 2) (by linarith) (by linarith)
      refine ⟨_, i1, isClosed_le continuous_const continuous_radiusSq, hi1, fun h => ?_⟩
      have h' : (x 0 ^ 2 + x 2 ^ 2 + 1) / 2 ≤ x 0 ^ 2 + x 2 ^ 2 := h
      linarith
    · have hpos : 0 < |x 1| := abs_pos.mpr hx1
      obtain ⟨i1, hi1⟩ := hB2 (|x 1| / 2) (by linarith)
      refine ⟨_, i1, isClosed_le (continuous_euclideanApply 1).abs continuous_const, hi1,
        fun h => ?_⟩
      have h' : |x 1| ≤ |x 1| / 2 := h
      linarith
  have hlower : ∀ m : ℤ, closure (⋃ i, ⋃ (_ : i ≤ m), towerSolid r w i) =
      (⋃ i, ⋃ (_ : i ≤ m), towerSolid r w i) ∪ {0} := by
    intro m
    refine Subset.antisymm (fun x hx => ?_) (union_subset subset_closure ?_)
    · by_cases hx0 : x = 0
      · exact Or.inr hx0
      · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        obtain ⟨i0, hi0⟩ := hB1 (‖x‖ / 2) (by positivity)
        refine Or.inl (mem_of_mem_closure_lower hSclosed isClosed_closedBall hi0 hx ?_)
        rw [mem_closedBall_zero_iff]
        exact not_le.mpr (by linarith)
    · rw [singleton_subset_iff, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := hlow ε hε
      refine ⟨towerPoint r (min k m), mem_iUnion₂.mpr ⟨min k m, min_le_right k m, hpoint _⟩, ?_⟩
      rw [dist_zero_left]
      refine norm_lt_of_coords hε ?_
      rw [towerPoint_apply_zero, towerPoint_apply_one, towerPoint_apply_two]
      have h1 : r (min k m) ≤ r k := hr.monotone (min_le_left k m)
      have h2 := hr0 (min k m)
      nlinarith [mul_pos (by linarith : 0 < ε - r (min k m)) (by linarith : 0 < ε + r (min k m))]
  have hupper : ∀ m : ℤ, closure (⋃ i, ⋃ (_ : m ≤ i), towerSolid r w i) =
      (⋃ i, ⋃ (_ : m ≤ i), towerSolid r w i) ∪ unitMeridianCircle := by
    intro m
    refine Subset.antisymm (fun x hx => ?_) (union_subset subset_closure fun c hc => ?_)
    · by_cases hxR : x ∈ unitMeridianCircle
      · exact Or.inr hxR
      · have hρx : x 0 ^ 2 + x 2 ^ 2 ≤ 1 :=
          closure_minimal (iUnion₂_subset fun i _ p hp => hSbound i p hp)
            (isClosed_le continuous_radiusSq continuous_const) hx
        obtain ⟨F, i1, hF, hFsub, hxF⟩ := hupperF x hρx hxR
        exact Or.inl (mem_of_mem_closure_upper hSclosed hF hFsub hx hxF)
    · rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := hhigh ε hε
      obtain ⟨hc1, hc2⟩ := hc
      have hmono : r k ≤ r (max k m) := hr.monotone (le_max_left k m)
      have h0 := hr0 (max k m)
      have h1 := hr1 (max k m)
      have hsm : ∀ j, (r (max k m) • c) j = r (max k m) * c j := fun j => by
        rw [PiLp.smul_apply, smul_eq_mul]
      refine ⟨r (max k m) • c, mem_iUnion₂.mpr ⟨max k m, le_max_right k m, ?_⟩, ?_⟩
      · rw [hS, hsm, hsm, hsm, hc2, mul_zero]
        have hρ : (r (max k m) * c 0) ^ 2 + (r (max k m) * c 2) ^ 2 = r (max k m) ^ 2 := by
          linear_combination r (max k m) ^ 2 * hc1
        rw [hρ]
        have h3 := hwr (max k m)
        have h4 := hw0 (max k m)
        have h5 := hrs (max k m)
        exact ⟨by nlinarith, by nlinarith, by linarith, by linarith⟩
      · rw [dist_eq_norm]
        refine norm_lt_of_coords hε ?_
        have hsub : ∀ j, (c - r (max k m) • c) j = (1 - r (max k m)) * c j := fun j => by
          rw [PiLp.sub_apply, hsm]
          ring
        rw [hsub, hsub, hsub, hc2]
        have hρ : ((1 - r (max k m)) * c 0) ^ 2 + ((1 - r (max k m)) * 0) ^ 2 +
            ((1 - r (max k m)) * c 2) ^ 2 = (1 - r (max k m)) ^ 2 := by
          linear_combination (1 - r (max k m)) ^ 2 * hc1
        rw [hρ]
        nlinarith [mul_pos (by linarith : 0 < ε - (1 - r (max k m)))
          (by linarith : 0 < ε + (1 - r (max k m)))]
  have hlf : ∀ y ∈ unitSolidCylinder, y ≠ 0 → y ∉ unitMeridianCircle →
      ∃ U ∈ 𝓝 y, {i | (towerSolid r w i ∩ U).Nonempty}.Finite := by
    intro y hy hy0 hyR
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    obtain ⟨i0, hi0⟩ := hB1 (‖y‖ / 2) (by positivity)
    obtain ⟨G, i1, hG, hGsub, hyG⟩ := hupperF y hy.1 hyR
    refine exists_nhds_finite_of_tails isClosed_closedBall hG hi0 hGsub ?_ hyG
    rw [mem_closedBall_zero_iff]
    exact not_le.mpr (by linarith)
  have hunion : ⋃ k, towerAnnulus r k = unitMeridianDisk \ (unitMeridianCircle ∪ {0}) := by
    refine Subset.antisymm (iUnion_subset hAM) fun p hp => ?_
    obtain ⟨hp1, hpos, hlt⟩ := mem_puncturedDisk_iff.mp hp
    obtain ⟨t, ht0, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 = p 0 ^ 2 + p 2 ^ 2 :=
      ⟨Real.sqrt (p 0 ^ 2 + p 2 ^ 2), Real.sqrt_pos.mpr hpos, Real.sq_sqrt hpos.le⟩
    have ht1 : t < 1 := by nlinarith
    have hbdd : ∃ b : ℤ, ∀ z : ℤ, r z ≤ t → z ≤ b := by
      obtain ⟨k, hk⟩ := hhigh (1 - t) (by linarith)
      exact ⟨k, fun z hz => (hr.lt_iff_lt.mp (by linarith)).le⟩
    have hinh : ∃ z : ℤ, r z ≤ t := by
      obtain ⟨k, hk⟩ := hlow t ht0
      exact ⟨k, hk.le⟩
    obtain ⟨k, hk, hkmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
    have hk1 : t < r (k + 1) := lt_of_not_ge fun h => by
      have := hkmax (k + 1) h
      omega
    refine mem_iUnion.mpr ⟨k, ?_⟩
    rw [hA k]
    have h0 := hr0 k
    refine ⟨?_, ?_, hp1.ge, hp1.le⟩
    · rw [← ht2]
      nlinarith
    · rw [← ht2]
      nlinarith
  exact ⟨towerPoint r, fun k => planarPoint '' towerRect r w k,
    fun k => planarPoint '' interior (towerRect r w k), fun k => revolutionOf {towerPoint r k},
    towerAnnulus r, towerSolid r w, fun k => frontier (towerSolid r w k),
    isRevolvedTorusChain_tower hr hw0 hwr hgap, hSO, hAc, hdisj, hunion, hlower, hupper, hlf⟩

end Tower

end DifferentialGeometry.Topology.PiecewiseLinear
