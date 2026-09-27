/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace DifferentialGeometry.Topology.PiecewiseLinear

def planarClamp (x : ℝ) : ℝ := min (max x 0) 1

def planarSweepParam (x y z : ℝ) : ℝ := planarClamp (-(min x (min y z)))

theorem planarClamp_nonneg (x : ℝ) : 0 ≤ planarClamp x :=
  le_min (le_max_right _ _) zero_le_one

theorem planarClamp_le_one (x : ℝ) : planarClamp x ≤ 1 :=
  min_le_right _ _

theorem planarClamp_eq_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : planarClamp x = x := by
  rw [planarClamp, max_eq_left h0, min_eq_left h1]

theorem planarClamp_eq_zero {x : ℝ} (h : x ≤ 0) : planarClamp x = 0 := by
  rw [planarClamp, max_eq_right h]
  exact min_eq_left zero_le_one

theorem planarClamp_eq_one {x : ℝ} (h : 1 ≤ x) : planarClamp x = 1 := by
  rw [planarClamp, max_eq_left (le_trans zero_le_one h), min_eq_right h]

theorem one_sub_planarClamp_le_planarClamp {x y : ℝ} (h : 1 ≤ x + y) :
    1 - planarClamp x ≤ planarClamp y := by
  simp only [planarClamp, min_def, max_def]
  split_ifs <;> linarith

theorem planarSweepParam_nonneg (x y z : ℝ) : 0 ≤ planarSweepParam x y z :=
  planarClamp_nonneg _

theorem planarSweepParam_le_one (x y z : ℝ) : planarSweepParam x y z ≤ 1 :=
  planarClamp_le_one _

theorem planarSweepParam_eq_zero {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    planarSweepParam x y z = 0 := by
  have h : 0 ≤ min x (min y z) := le_min hx (le_min hy hz)
  exact planarClamp_eq_zero (by linarith)

theorem planarSweepParam_eq_one {x y z : ℝ} (h : x = -1 ∨ y = -1 ∨ z = -1) :
    planarSweepParam x y z = 1 := by
  have hle : min x (min y z) ≤ -1 := by
    rcases h with h | h | h
    · exact h ▸ min_le_left _ _
    · exact le_trans (le_trans (min_le_right x _) (min_le_left y z)) h.le
    · exact le_trans (le_trans (min_le_right x _) (min_le_right y z)) h.le
  exact planarClamp_eq_one (by linarith)

theorem coord_add_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) (x y : Plane) :
    b.coord i (x + y) = (b.coord i).linear x + b.coord i y := by
  simpa using (b.coord i).map_vadd' y x

theorem coord_linear_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) (x : Plane) :
    (b.coord i).linear x = b.coord i x - b.coord i 0 := by
  have h := coord_add_of_affineBasis b i x 0
  rw [add_zero] at h
  linarith

theorem coord_sub_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) (x y : Plane) :
    (b.coord i).linear (x - y) = b.coord i x - b.coord i y := by
  rw [map_sub, coord_linear_of_affineBasis, coord_linear_of_affineBasis]
  ring

theorem coord_shift_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) (i j k : Fin 3) (w : Plane) :
    b.coord i (w + (b j - b k)) = b.coord i w + (b.coord i (b j) - b.coord i (b k)) := by
  have he : w + (b j - b k) = (b j - b k) + w := by abel
  rw [he, coord_add_of_affineBasis, coord_sub_of_affineBasis]
  ring

theorem coord_combo_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) (a a' : ℝ) :
    b.coord i (b 0 + a • (b 1 - b 0) + a' • (b 2 - b 0))
      = b.coord i (b 0) + a * (b.coord i (b 1) - b.coord i (b 0))
        + a' * (b.coord i (b 2) - b.coord i (b 0)) := by
  have he : b 0 + a • (b 1 - b 0) + a' • (b 2 - b 0)
      = (a • (b 1 - b 0) + a' • (b 2 - b 0)) + b 0 := by abel
  rw [he, coord_add_of_affineBasis, map_add, map_smul, map_smul, coord_sub_of_affineBasis,
    coord_sub_of_affineBasis]
  simp only [smul_eq_mul]
  ring

theorem forall_three_of_zero_one_two {Q : Fin 3 → Prop} (h0 : Q 0) (h1 : Q 1) (h2 : Q 2) :
    ∀ i, Q i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem or_three_of_exists_fin_three {Q : Fin 3 → Prop} (h : ∃ i, Q i) : Q 0 ∨ Q 1 ∨ Q 2 := by
  obtain ⟨i, hi⟩ := h
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

theorem eq_of_coord_eq_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) {x y : Plane}
    (h0 : b.coord 0 x = b.coord 0 y) (h1 : b.coord 1 x = b.coord 1 y)
    (h2 : b.coord 2 x = b.coord 2 y) : x = y :=
  b.ext_elem (forall_three_of_zero_one_two h0 h1 h2)

theorem coord_sum_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) (z : Plane) :
    b.coord 0 z + b.coord 1 z + b.coord 2 z = 1 := by
  have h := b.sum_coord_apply_eq_one z
  rw [Fin.sum_univ_three] at h
  exact h

noncomputable def planarRetract (b : AffineBasis (Fin 3) ℝ Plane) (z : Plane) : Plane :=
  b 0 + planarClamp (b.coord 1 z) • (b 1 - b 0)
    + min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z)) • (b 2 - b 0)

theorem coord_one_planarRetract (b : AffineBasis (Fin 3) ℝ Plane) (z : Plane) :
    b.coord 1 (planarRetract b z) = planarClamp (b.coord 1 z) := by
  have k0 : b.coord 1 (b 0) = 0 := b.coord_apply_ne (by decide)
  have k1 : b.coord 1 (b 1) = 1 := b.coord_apply_eq 1
  have k2 : b.coord 1 (b 2) = 0 := b.coord_apply_ne (by decide)
  rw [planarRetract, coord_combo_of_affineBasis, k0, k1, k2]
  ring

theorem coord_two_planarRetract (b : AffineBasis (Fin 3) ℝ Plane) (z : Plane) :
    b.coord 2 (planarRetract b z)
      = min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z)) := by
  have k0 : b.coord 2 (b 0) = 0 := b.coord_apply_ne (by decide)
  have k1 : b.coord 2 (b 1) = 0 := b.coord_apply_ne (by decide)
  have k2 : b.coord 2 (b 2) = 1 := b.coord_apply_eq 2
  rw [planarRetract, coord_combo_of_affineBasis, k0, k1, k2]
  ring

theorem coord_zero_planarRetract (b : AffineBasis (Fin 3) ℝ Plane) (z : Plane) :
    b.coord 0 (planarRetract b z)
      = 1 - planarClamp (b.coord 1 z)
        - min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z)) := by
  have k0 : b.coord 0 (b 0) = 1 := b.coord_apply_eq 0
  have k1 : b.coord 0 (b 1) = 0 := b.coord_apply_ne (by decide)
  have k2 : b.coord 0 (b 2) = 0 := b.coord_apply_ne (by decide)
  rw [planarRetract, coord_combo_of_affineBasis, k0, k1, k2]
  ring

theorem coord_nonneg_planarRetract (b : AffineBasis (Fin 3) ℝ Plane) (z : Plane) (i : Fin 3) :
    0 ≤ b.coord i (planarRetract b z) := by
  have hmin : min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z))
      ≤ 1 - planarClamp (b.coord 1 z) := min_le_right _ _
  have hmin0 : 0 ≤ min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z)) :=
    le_min (planarClamp_nonneg _) (by linarith [planarClamp_le_one (b.coord 1 z)])
  refine forall_three_of_zero_one_two (Q := fun i => 0 ≤ b.coord i (planarRetract b z)) ?_ ?_ ?_ i
  · rw [coord_zero_planarRetract]; linarith
  · rw [coord_one_planarRetract]; exact planarClamp_nonneg _
  · rw [coord_two_planarRetract]; exact hmin0

theorem planarRetract_eq_self (b : AffineBasis (Fin 3) ℝ Plane) {z : Plane}
    (hz : ∀ i, 0 ≤ b.coord i z) : planarRetract b z = z := by
  have hs := coord_sum_of_affineBasis b z
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have hc1 : planarClamp (b.coord 1 z) = b.coord 1 z := planarClamp_eq_self h1 (by linarith)
  have hc2 : planarClamp (b.coord 2 z) = b.coord 2 z := planarClamp_eq_self h2 (by linarith)
  have hm : min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z)) = b.coord 2 z := by
    rw [hc1, hc2]
    exact min_eq_left (by linarith)
  refine eq_of_coord_eq_of_affineBasis b ?_ ?_ ?_
  · rw [coord_zero_planarRetract, hm, hc1]; linarith
  · rw [coord_one_planarRetract, hc1]
  · rw [coord_two_planarRetract, hm]

theorem exists_coord_eq_zero_planarRetract (b : AffineBasis (Fin 3) ℝ Plane) {z : Plane}
    (hz : ∃ i, b.coord i z < 0) : ∃ i, b.coord i (planarRetract b z) = 0 := by
  have hs := coord_sum_of_affineBasis b z
  rcases or_three_of_exists_fin_three hz with h | h | h
  · refine ⟨0, ?_⟩
    have hle : 1 - planarClamp (b.coord 1 z) ≤ planarClamp (b.coord 2 z) :=
      one_sub_planarClamp_le_planarClamp (by linarith)
    rw [coord_zero_planarRetract, min_eq_right hle]
    ring
  · refine ⟨1, ?_⟩
    rw [coord_one_planarRetract, planarClamp_eq_zero h.le]
  · refine ⟨2, ?_⟩
    rw [coord_two_planarRetract, planarClamp_eq_zero h.le]
    exact min_eq_left (by linarith [planarClamp_le_one (b.coord 1 z)])

theorem exists_frontier_preimage_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) {w : Plane}
    (hw0 : ∀ i, 0 ≤ b.coord i w) (hwex : ∃ i, b.coord i w = 0) :
    ∃ z : Plane, (∀ i, -1 ≤ b.coord i z) ∧ (∃ i, b.coord i z = -1) ∧ planarRetract b z = w := by
  have hs := coord_sum_of_affineBasis b w
  have h0 := hw0 0
  have h1 := hw0 1
  have h2 := hw0 2
  have e00 : b.coord 0 (b 0) = 1 := b.coord_apply_eq 0
  have e01 : b.coord 0 (b 1) = 0 := b.coord_apply_ne (by decide)
  have e02 : b.coord 0 (b 2) = 0 := b.coord_apply_ne (by decide)
  have e10 : b.coord 1 (b 0) = 0 := b.coord_apply_ne (by decide)
  have e11 : b.coord 1 (b 1) = 1 := b.coord_apply_eq 1
  have e12 : b.coord 1 (b 2) = 0 := b.coord_apply_ne (by decide)
  have e20 : b.coord 2 (b 0) = 0 := b.coord_apply_ne (by decide)
  have e21 : b.coord 2 (b 1) = 0 := b.coord_apply_ne (by decide)
  have e22 : b.coord 2 (b 2) = 1 := b.coord_apply_eq 2
  rcases or_three_of_exists_fin_three hwex with h | h | h
  · refine ⟨w + (b 2 - b 0), ?_, ?_, ?_⟩
    · refine forall_three_of_zero_one_two ?_ ?_ ?_
      · rw [coord_shift_of_affineBasis, e02, e00]; linarith
      · rw [coord_shift_of_affineBasis, e12, e10]; linarith
      · rw [coord_shift_of_affineBasis, e22, e20]; linarith
    · exact ⟨0, by rw [coord_shift_of_affineBasis, e02, e00]; linarith⟩
    · have c1 : b.coord 1 (w + (b 2 - b 0)) = b.coord 1 w := by
        rw [coord_shift_of_affineBasis, e12, e10]; ring
      have c2 : b.coord 2 (w + (b 2 - b 0)) = b.coord 2 w + 1 := by
        rw [coord_shift_of_affineBasis, e22, e20]; ring
      have hc1 : planarClamp (b.coord 1 (w + (b 2 - b 0))) = b.coord 1 w := by
        rw [c1]; exact planarClamp_eq_self h1 (by linarith)
      have hc2 : planarClamp (b.coord 2 (w + (b 2 - b 0))) = 1 := by
        rw [c2]; exact planarClamp_eq_one (by linarith)
      have hm : min (planarClamp (b.coord 2 (w + (b 2 - b 0))))
          (1 - planarClamp (b.coord 1 (w + (b 2 - b 0)))) = 1 - b.coord 1 w := by
        rw [hc1, hc2]
        exact min_eq_right (by linarith)
      refine eq_of_coord_eq_of_affineBasis b ?_ ?_ ?_
      · rw [coord_zero_planarRetract, hm, hc1]; linarith
      · rw [coord_one_planarRetract, hc1]
      · rw [coord_two_planarRetract, hm]; linarith
  · refine ⟨w + (b 0 - b 1), ?_, ?_, ?_⟩
    · refine forall_three_of_zero_one_two ?_ ?_ ?_
      · rw [coord_shift_of_affineBasis, e00, e01]; linarith
      · rw [coord_shift_of_affineBasis, e10, e11]; linarith
      · rw [coord_shift_of_affineBasis, e20, e21]; linarith
    · exact ⟨1, by rw [coord_shift_of_affineBasis, e10, e11]; linarith⟩
    · have c1 : b.coord 1 (w + (b 0 - b 1)) = b.coord 1 w - 1 := by
        rw [coord_shift_of_affineBasis, e10, e11]; ring
      have c2 : b.coord 2 (w + (b 0 - b 1)) = b.coord 2 w := by
        rw [coord_shift_of_affineBasis, e20, e21]; ring
      have hc1 : planarClamp (b.coord 1 (w + (b 0 - b 1))) = 0 := by
        rw [c1]; exact planarClamp_eq_zero (by linarith)
      have hc2 : planarClamp (b.coord 2 (w + (b 0 - b 1))) = b.coord 2 w := by
        rw [c2]; exact planarClamp_eq_self h2 (by linarith)
      have hm : min (planarClamp (b.coord 2 (w + (b 0 - b 1))))
          (1 - planarClamp (b.coord 1 (w + (b 0 - b 1)))) = b.coord 2 w := by
        rw [hc1, hc2]
        exact min_eq_left (by linarith)
      refine eq_of_coord_eq_of_affineBasis b ?_ ?_ ?_
      · rw [coord_zero_planarRetract, hm, hc1]; linarith
      · rw [coord_one_planarRetract, hc1]; linarith
      · rw [coord_two_planarRetract, hm]
  · refine ⟨w + (b 0 - b 2), ?_, ?_, ?_⟩
    · refine forall_three_of_zero_one_two ?_ ?_ ?_
      · rw [coord_shift_of_affineBasis, e00, e02]; linarith
      · rw [coord_shift_of_affineBasis, e10, e12]; linarith
      · rw [coord_shift_of_affineBasis, e20, e22]; linarith
    · exact ⟨2, by rw [coord_shift_of_affineBasis, e20, e22]; linarith⟩
    · have c1 : b.coord 1 (w + (b 0 - b 2)) = b.coord 1 w := by
        rw [coord_shift_of_affineBasis, e10, e12]; ring
      have c2 : b.coord 2 (w + (b 0 - b 2)) = b.coord 2 w - 1 := by
        rw [coord_shift_of_affineBasis, e20, e22]; ring
      have hc1 : planarClamp (b.coord 1 (w + (b 0 - b 2))) = b.coord 1 w := by
        rw [c1]; exact planarClamp_eq_self h1 (by linarith)
      have hc2 : planarClamp (b.coord 2 (w + (b 0 - b 2))) = 0 := by
        rw [c2]; exact planarClamp_eq_zero (by linarith)
      have hm : min (planarClamp (b.coord 2 (w + (b 0 - b 2))))
          (1 - planarClamp (b.coord 1 (w + (b 0 - b 2)))) = 0 := by
        rw [hc1, hc2]
        exact min_eq_left (by linarith)
      refine eq_of_coord_eq_of_affineBasis b ?_ ?_ ?_
      · rw [coord_zero_planarRetract, hm, hc1]; linarith
      · rw [coord_one_planarRetract, hc1]
      · rw [coord_two_planarRetract, hm]; linarith

theorem coord_sum_vertices_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    b.coord i (b 0) + b.coord i (b 1) + b.coord i (b 2) = 1 := by
  refine forall_three_of_zero_one_two
    (Q := fun i => b.coord i (b 0) + b.coord i (b 1) + b.coord i (b 2) = 1) ?_ ?_ ?_ i
  · rw [b.coord_apply_eq 0, b.coord_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
      b.coord_apply_ne (show (0 : Fin 3) ≠ 2 by decide)]
    norm_num
  · rw [b.coord_apply_ne (show (1 : Fin 3) ≠ 0 by decide), b.coord_apply_eq 1,
      b.coord_apply_ne (show (1 : Fin 3) ≠ 2 by decide)]
    norm_num
  · rw [b.coord_apply_ne (show (2 : Fin 3) ≠ 0 by decide),
      b.coord_apply_ne (show (2 : Fin 3) ≠ 1 by decide), b.coord_apply_eq 2]
    norm_num

theorem isPiecewiseAffineOn_planarRetract (b : AffineBasis (Fin 3) ℝ Plane) {S : Set Plane}
    (hS : IsPolyhedron S) : IsPiecewiseAffineOn (planarRetract b) S := by
  have hbase : ∀ i : Fin 3, IsPiecewiseAffineOn (fun z => b.coord i z) S :=
    fun i => (isPiecewiseAffineOn_of_affine (b.coord i) isOpen_univ).mono_of_isPolyhedron
      hS (subset_univ _)
  have hconst : ∀ a : ℝ, IsPiecewiseAffineOn (fun _ : Plane => a) S :=
    fun a => (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ Plane a)
      isOpen_univ).mono_of_isPolyhedron hS (subset_univ _)
  have hu : IsPiecewiseAffineOn (fun z => planarClamp (b.coord 1 z)) S :=
    (((hbase 1).max (hconst 0)).min (hconst 1)).congr fun z _ => rfl
  have hw : IsPiecewiseAffineOn (fun z => planarClamp (b.coord 2 z)) S :=
    (((hbase 2).max (hconst 0)).min (hconst 1)).congr fun z _ => rfl
  have honeu : IsPiecewiseAffineOn (fun z => 1 - planarClamp (b.coord 1 z)) S := by
    refine ((hconst 1).add (hu.affine_comp (-AffineMap.id ℝ ℝ))).congr fun z _ => ?_
    simp [sub_eq_add_neg]
  have hv : IsPiecewiseAffineOn
      (fun z => min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z))) S := hw.min honeu
  have h1 : IsPiecewiseAffineOn (fun z => planarClamp (b.coord 1 z) • (b 1 - b 0)) S :=
    (hu.affine_comp (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (b 1 - b 0)).toAffineMap)).congr
      fun z _ => rfl
  have h2 : IsPiecewiseAffineOn
      (fun z => min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z)) • (b 2 - b 0)) S :=
    (hv.affine_comp (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (b 2 - b 0)).toAffineMap)).congr
      fun z _ => rfl
  have h0 : IsPiecewiseAffineOn (fun _ : Plane => b 0) S :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ Plane (b 0))
      isOpen_univ).mono_of_isPolyhedron hS (subset_univ _)
  exact ((h0.add h1).add h2).congr fun z _ => rfl

theorem isPiecewiseAffineOn_planarSweepParam (b : AffineBasis (Fin 3) ℝ Plane) {S : Set Plane}
    (hS : IsPolyhedron S) :
    IsPiecewiseAffineOn
      (fun z => planarSweepParam (b.coord 0 z) (b.coord 1 z) (b.coord 2 z)) S := by
  have hbase : ∀ i : Fin 3, IsPiecewiseAffineOn (fun z => b.coord i z) S :=
    fun i => (isPiecewiseAffineOn_of_affine (b.coord i) isOpen_univ).mono_of_isPolyhedron
      hS (subset_univ _)
  have hconst : ∀ a : ℝ, IsPiecewiseAffineOn (fun _ : Plane => a) S :=
    fun a => (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ Plane a)
      isOpen_univ).mono_of_isPolyhedron hS (subset_univ _)
  have hmin3 : IsPiecewiseAffineOn
      (fun z => min (b.coord 0 z) (min (b.coord 1 z) (b.coord 2 z))) S :=
    (hbase 0).min ((hbase 1).min (hbase 2))
  exact (((hmin3.affine_comp (-AffineMap.id ℝ ℝ)).max (hconst 0)).min (hconst 1)).congr
    fun z _ => rfl

theorem exists_isPLBall_two_exteriorBall_of_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) :
    ∃ C' : Set Plane, IsPLBall 2 C' ∧ IsPolyhedron C' ∧
      (∀ z, z ∈ C' ↔ ∀ i, -1 ≤ b.coord i z) ∧
      (∀ z, z ∈ interior C' ↔ ∀ i, -1 < b.coord i z) ∧
      (∀ z, z ∈ frontier C' ↔ (∀ i, -1 ≤ b.coord i z) ∧ ∃ i, b.coord i z = -1) := by
  have hCball : IsPLBall 2 (convexHull ℝ (Set.range b)) :=
    isPLBall_two_of_isTriangle ⟨b, b.ind, rfl⟩
  have hCpoly : IsPolyhedron (convexHull ℝ (Set.range b)) := hCball.isPolyhedron
  have hCclosed : IsClosed (convexHull ℝ (Set.range b)) := hCpoly.isCompact.isClosed
  have hCset : convexHull ℝ (Set.range b) = {z : Plane | ∀ i, 0 ≤ b.coord i z} :=
    b.convexHull_eq_nonneg_coord
  have hCint : interior (convexHull ℝ (Set.range b)) = {z : Plane | ∀ i, 0 < b.coord i z} :=
    b.interior_convexHull
  have hcc : ∀ i : Fin 3, b.coord i ((3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) = (3 : ℝ)⁻¹ := by
    intro i
    have h0 := coord_add_of_affineBasis b i ((3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) 0
    rw [add_zero] at h0
    have h1 : (b.coord i).linear ((3 : ℝ)⁻¹ • (b 0 + b 1 + b 2))
        = (3 : ℝ)⁻¹ * ((b.coord i).linear (b 0) + (b.coord i).linear (b 1)
          + (b.coord i).linear (b 2)) := by
      rw [map_smul, map_add, map_add]
      simp only [smul_eq_mul]
    have e0 := coord_linear_of_affineBasis b i (b 0)
    have e1 := coord_linear_of_affineBasis b i (b 1)
    have e2 := coord_linear_of_affineBasis b i (b 2)
    have hs := coord_sum_vertices_of_affineBasis b i
    rw [h0, h1, e0, e1, e2]
    linarith
  set dil : Plane →ᵃ[ℝ] Plane :=
    AffineMap.homothety ((3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) (4 : ℝ) with hdildef
  set shr : Plane →ᵃ[ℝ] Plane :=
    AffineMap.homothety ((3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) (4 : ℝ)⁻¹ with hshrdef
  have hdilapp : ∀ z : Plane,
      dil z = (4 : ℝ) • (z - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) + (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2) := by
    intro z; rw [hdildef]; simp [AffineMap.homothety_apply]
  have hshrapp : ∀ z : Plane,
      shr z = (4 : ℝ)⁻¹ • (z - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2))
        + (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2) := by
    intro z; rw [hshrdef]; simp [AffineMap.homothety_apply]
  have hleft : ∀ z : Plane, shr (dil z) = z := by
    intro z
    rw [hshrapp, hdilapp]
    have hz : (4 : ℝ) • (z - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) + (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)
        - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2) = (4 : ℝ) • (z - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) := by
      abel
    rw [hz, smul_smul]
    norm_num
  have hright : ∀ z : Plane, dil (shr z) = z := by
    intro z
    rw [hdilapp, hshrapp]
    have hz : (4 : ℝ)⁻¹ • (z - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) + (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)
        - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2) = (4 : ℝ)⁻¹ • (z - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2)) := by
      abel
    rw [hz, smul_smul]
    norm_num
  have hdilcoord : ∀ (i : Fin 3) (z : Plane), b.coord i (dil z) = 4 * b.coord i z - 1 := by
    intro i z
    rw [hdilapp]
    have h0 := coord_add_of_affineBasis b i
      ((4 : ℝ) • (z - (3 : ℝ)⁻¹ • (b 0 + b 1 + b 2))) ((3 : ℝ)⁻¹ • (b 0 + b 1 + b 2))
    rw [h0, map_smul, coord_sub_of_affineBasis, hcc i]
    simp only [smul_eq_mul]
    ring
  set dilHomeo : Plane ≃ₜ Plane :=
    { toFun := dil
      invFun := shr
      left_inv := hleft
      right_inv := hright
      continuous_toFun := dil.continuous_of_finiteDimensional
      continuous_invFun := shr.continuous_of_finiteDimensional } with hdilHdef
  have hdilH : ∀ z : Plane, dilHomeo z = dil z := fun _ => rfl
  refine ⟨dilHomeo '' convexHull ℝ (Set.range b), ?_, ?_, ?_, ?_, ?_⟩
  · refine hCball.of_isPLHomeomorphOn (f := dil) ⟨?_, ?_, ?_⟩
    · refine ⟨fun x hx => ⟨x, hx, rfl⟩, ?_, ?_⟩
      · intro x _ y _ hxy
        have hc2 := congrArg shr hxy
        rwa [hleft, hleft] at hc2
      · rintro y ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
    · exact (isPiecewiseAffineOn_of_affine dil isOpen_univ).mono_of_isPolyhedron
        hCpoly (subset_univ _)
    · have hbij : BijOn dil (convexHull ℝ (Set.range b)) (dilHomeo '' convexHull ℝ (Set.range b)) :=
        by
        refine ⟨fun x hx => ⟨x, hx, rfl⟩, ?_, ?_⟩
        · intro x _ y _ hxy
          have hc2 := congrArg shr hxy
          rwa [hleft, hleft] at hc2
        · rintro y ⟨w, hw, rfl⟩
          exact ⟨w, hw, rfl⟩
      have hpoly : IsPolyhedron (dilHomeo '' convexHull ℝ (Set.range b)) := by
        have himg := hCpoly.image_of_isPiecewiseAffineOn
          ((isPiecewiseAffineOn_of_affine dil isOpen_univ).mono_of_isPolyhedron
            hCpoly (subset_univ _)) hbij.injOn
        rwa [hbij.image_eq] at himg
      refine ((isPiecewiseAffineOn_of_affine shr isOpen_univ).mono_of_isPolyhedron
        hpoly (subset_univ _)).congr fun y hy => ?_
      obtain ⟨w, hw, hwy⟩ := hy
      have h2 : Function.invFunOn dil (convexHull ℝ (Set.range b)) y = w := by
        rw [← hwy]
        exact hbij.injOn.leftInvOn_invFunOn hw
      rw [h2, ← hwy, hdilH, hleft]
  · have hbij : BijOn dil (convexHull ℝ (Set.range b)) (dilHomeo '' convexHull ℝ (Set.range b)) :=
      by
      refine ⟨fun x hx => ⟨x, hx, rfl⟩, ?_, ?_⟩
      · intro x _ y _ hxy
        have hc2 := congrArg shr hxy
        rwa [hleft, hleft] at hc2
      · rintro y ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
    have himg := hCpoly.image_of_isPiecewiseAffineOn
      ((isPiecewiseAffineOn_of_affine dil isOpen_univ).mono_of_isPolyhedron
        hCpoly (subset_univ _)) hbij.injOn
    rwa [hbij.image_eq] at himg
  · intro z
    constructor
    · rintro ⟨w, hw, rfl⟩ i
      rw [hCset] at hw
      rw [hdilH, hdilcoord]
      have hwi := hw i
      linarith
    · intro hz
      refine ⟨shr z, ?_, ?_⟩
      · rw [hCset]
        intro i
        have hd := hdilcoord i (shr z)
        rw [hright] at hd
        have hi := hz i
        linarith
      · rw [hdilH]; exact hright z
  · intro z
    rw [← dilHomeo.image_interior, hCint]
    constructor
    · rintro ⟨w, hw, rfl⟩ i
      rw [hdilH, hdilcoord]
      have hwi := hw i
      linarith
    · intro hz
      refine ⟨shr z, ?_, ?_⟩
      · intro i
        have hd := hdilcoord i (shr z)
        rw [hright] at hd
        have hi := hz i
        linarith
      · rw [hdilH]; exact hright z
  · intro z
    have hC'closed : IsClosed (dilHomeo '' convexHull ℝ (Set.range b)) :=
      dilHomeo.isClosedMap _ hCclosed
    have hmem : ∀ y : Plane, y ∈ dilHomeo '' convexHull ℝ (Set.range b) ↔ ∀ i, -1 ≤ b.coord i y :=
        by
      intro y
      constructor
      · rintro ⟨w, hw, rfl⟩ i
        rw [hCset] at hw
        rw [hdilH, hdilcoord]
        have hwi := hw i
        linarith
      · intro hy
        refine ⟨shr y, ?_, ?_⟩
        · rw [hCset]
          intro i
          have hd := hdilcoord i (shr y)
          rw [hright] at hd
          have hi := hy i
          linarith
        · rw [hdilH]; exact hright y
    have hmemint : ∀ y : Plane,
        y ∈ interior (dilHomeo '' convexHull ℝ (Set.range b)) ↔ ∀ i, -1 < b.coord i y := by
      intro y
      rw [← dilHomeo.image_interior, hCint]
      constructor
      · rintro ⟨w, hw, rfl⟩ i
        rw [hdilH, hdilcoord]
        have hwi := hw i
        linarith
      · intro hy
        refine ⟨shr y, ?_, ?_⟩
        · intro i
          have hd := hdilcoord i (shr y)
          rw [hright] at hd
          have hi := hy i
          linarith
        · rw [hdilH]; exact hright y
    rw [hC'closed.frontier_eq, Set.mem_sdiff, hmem z, hmemint z]
    constructor
    · rintro ⟨hone, htwo⟩
      refine ⟨hone, ?_⟩
      by_contra hcon
      push Not at hcon
      exact htwo fun i => lt_of_le_of_ne (hone i) (Ne.symm (hcon i))
    · rintro ⟨hone, i, hi⟩
      exact ⟨hone, fun htwo => absurd (htwo i) (by rw [hi]; exact lt_irrefl _)⟩

theorem exists_exteriorCollapse_of_isTriangle {C : Set Plane} (hC : IsTriangle C) :
    ∃ (C' : Set Plane) (r : Plane → Plane) (t : Plane → ℝ),
      IsPLBall 2 C' ∧ C ⊆ interior C' ∧
      IsPiecewiseAffineOn r C' ∧ IsPiecewiseAffineOn t C' ∧
      MapsTo r C' C ∧ EqOn r id C ∧ MapsTo r (C' \ C) (frontier C) ∧
      frontier C ⊆ r '' frontier C' ∧
      EqOn t 0 C ∧ EqOn t 1 (frontier C') ∧ ∀ z ∈ C', t z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := hC
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Plane + 1 := by simp
  have hspan : affineSpan ℝ (Set.range p) = ⊤ :=
    hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcard
  set b : AffineBasis (Fin 3) ℝ Plane := ⟨p, hp, hspan⟩ with hbdef
  have hbp : Set.range p = Set.range b := rfl
  obtain ⟨C', hC'ball, hC'poly, hmemC', hmemC'int, hmemC'fr⟩ :=
    exists_isPLBall_two_exteriorBall_of_affineBasis b
  have hCset : convexHull ℝ (Set.range p) = {z : Plane | ∀ i, 0 ≤ b.coord i z} := by
    rw [hbp]
    exact b.convexHull_eq_nonneg_coord
  have hCint : interior (convexHull ℝ (Set.range p)) = {z : Plane | ∀ i, 0 < b.coord i z} := by
    rw [hbp]
    exact b.interior_convexHull
  have hCclosed : IsClosed (convexHull ℝ (Set.range p)) :=
    (isPLBall_two_of_isTriangle ⟨p, hp, rfl⟩).isPolyhedron.isCompact.isClosed
  have hfrC : ∀ z : Plane, z ∈ frontier (convexHull ℝ (Set.range p)) ↔
      (∀ i, 0 ≤ b.coord i z) ∧ ∃ i, b.coord i z = 0 := by
    intro z
    rw [hCclosed.frontier_eq, Set.mem_sdiff, hCint, hCset]
    constructor
    · rintro ⟨hone, htwo⟩
      refine ⟨hone, ?_⟩
      by_contra hcon
      push Not at hcon
      exact htwo fun i => lt_of_le_of_ne (hone i) (Ne.symm (hcon i))
    · rintro ⟨hone, i, hi⟩
      exact ⟨hone, fun htwo => absurd (htwo i) (by rw [hi]; exact lt_irrefl _)⟩
  refine ⟨C', planarRetract b,
    fun z => planarSweepParam (b.coord 0 z) (b.coord 1 z) (b.coord 2 z),
    hC'ball, ?_, isPiecewiseAffineOn_planarRetract b hC'poly,
    isPiecewiseAffineOn_planarSweepParam b hC'poly, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hCset] at hz
    exact (hmemC'int z).mpr fun i => by linarith [hz i]
  · intro z _
    rw [hCset]
    exact fun i => coord_nonneg_planarRetract b z i
  · intro z hz
    rw [hCset] at hz
    exact planarRetract_eq_self b hz
  · rintro z ⟨-, hznot⟩
    rw [hCset] at hznot
    have hneg : ∃ i, b.coord i z < 0 := by
      by_contra hcon
      push Not at hcon
      exact hznot fun i => hcon i
    rw [hfrC]
    exact ⟨fun i => coord_nonneg_planarRetract b z i, exists_coord_eq_zero_planarRetract b hneg⟩
  · intro w hw
    rw [hfrC] at hw
    obtain ⟨z, hz1, hz2, hz3⟩ := exists_frontier_preimage_of_affineBasis b hw.1 hw.2
    exact ⟨z, (hmemC'fr z).mpr ⟨hz1, hz2⟩, hz3⟩
  · intro z hz
    rw [hCset] at hz
    simp only [Pi.zero_apply]
    exact planarSweepParam_eq_zero (hz 0) (hz 1) (hz 2)
  · intro z hz
    rw [hmemC'fr] at hz
    simp only [Pi.one_apply]
    exact planarSweepParam_eq_one (or_three_of_exists_fin_three hz.2)
  · intro z _
    exact ⟨planarSweepParam_nonneg _ _ _, planarSweepParam_le_one _ _ _⟩

theorem exists_exteriorCollapse_of_isPLBall_two {D : Set Plane} (hD : IsPLBall 2 D) :
    ∃ (D' : Set Plane) (r : Plane → Plane) (t : Plane → ℝ),
      IsPLBall 2 D' ∧ D ⊆ interior D' ∧
      IsPiecewiseAffineOn r D' ∧ IsPiecewiseAffineOn t D' ∧
      MapsTo r D' D ∧ EqOn r id D ∧ MapsTo r (D' \ D) (frontier D) ∧
      frontier D ⊆ r '' frontier D' ∧
      EqOn t 0 D ∧ EqOn t 1 (frontier D') ∧ ∀ z ∈ D', t z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h, C, hCtri, hhpl, hhD, -, -⟩ :=
    exists_isPLHomeomorphOn_straighten_of_isPLBall_two hD isOpen_univ (subset_univ _)
  obtain ⟨C', r, t, hC'ball, hCsub, hrpl, htpl, hrmaps, hrid, hrfr, hfrsub, ht0, ht1, hticc⟩ :=
    exists_exteriorCollapse_of_isTriangle hCtri
  have hinvEq : Function.invFunOn (⇑h) univ = fun y => h.symm y := by
    funext y
    have hmem : ∃ a ∈ (univ : Set Plane), h a = y := ⟨h.symm y, mem_univ _, h.apply_symm_apply y⟩
    have hval := Function.invFunOn_eq hmem
    exact h.injective (by rw [hval, h.apply_symm_apply])
  have hsymmpl : IsPiecewiseAffineOn (fun y => h.symm y) univ :=
    hhpl.2.2.congr fun y _ => (congrFun hinvEq y).symm
  have hDpre : D = ⇑h ⁻¹' C := by
    rw [← hhD]
    ext x
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => (h.injective hyx) ▸ hy⟩
  have hpreimage : ⇑h ⁻¹' C' = (fun y => h.symm y) '' C' := by
    ext x
    constructor
    · intro hx
      exact ⟨h x, hx, h.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [mem_preimage, h.apply_symm_apply]
  have hD'ball : IsPLBall 2 (⇑h ⁻¹' C') := by
    rw [hpreimage]
    refine hC'ball.of_isPLHomeomorphOn (f := fun y => h.symm y) ⟨?_, ?_, ?_⟩
    · exact (h.symm.injective.injOn.mono (subset_univ C')).bijOn_image
    · exact hsymmpl.mono_of_isPolyhedron hC'ball.isPolyhedron (subset_univ _)
    · have hinj : InjOn (fun y => h.symm y) C' := h.symm.injective.injOn.mono (subset_univ C')
      have hpoly : IsPolyhedron ((fun y => h.symm y) '' C') :=
        hC'ball.isPolyhedron.image_of_isPiecewiseAffineOn
          (hsymmpl.mono_of_isPolyhedron hC'ball.isPolyhedron (subset_univ _)) hinj
      refine ((hhpl.2.1.mono_of_isPolyhedron hpoly (subset_univ _))).congr fun y hy => ?_
      obtain ⟨w, hw, rfl⟩ := hy
      have hb : BijOn (fun y => h.symm y) C' ((fun y => h.symm y) '' C') := hinj.bijOn_image
      rw [hb.injOn.leftInvOn_invFunOn hw, h.apply_symm_apply]
  have hD'poly : IsPolyhedron (⇑h ⁻¹' C') := hD'ball.isPolyhedron
  have hhD' : IsPiecewiseAffineOn (⇑h) (⇑h ⁻¹' C') :=
    hhpl.2.1.mono_of_isPolyhedron hD'poly (subset_univ _)
  have hfrD : frontier D = ⇑h ⁻¹' frontier C := by
    rw [hDpre, h.preimage_frontier]
  have hfrD' : frontier (⇑h ⁻¹' C') = ⇑h ⁻¹' frontier C' := (h.preimage_frontier C').symm
  refine ⟨⇑h ⁻¹' C', fun z => h.symm (r (h z)), fun z => t (h z), hD'ball, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← h.preimage_interior]
    rw [hDpre] at hx
    exact hCsub hx
  · have h1 : IsPiecewiseAffineOn (r ∘ ⇑h) (⇑h ⁻¹' C' ∩ ⇑h ⁻¹' C') := hrpl.comp hhD'
    rw [inter_self] at h1
    have h2 : IsPiecewiseAffineOn ((fun y => h.symm y) ∘ (r ∘ ⇑h))
        (⇑h ⁻¹' C' ∩ (r ∘ ⇑h) ⁻¹' univ) := hsymmpl.comp h1
    rw [preimage_univ, inter_univ] at h2
    exact h2.congr fun z _ => rfl
  · have h1 : IsPiecewiseAffineOn (t ∘ ⇑h) (⇑h ⁻¹' C' ∩ ⇑h ⁻¹' C') := htpl.comp hhD'
    rw [inter_self] at h1
    exact h1.congr fun z _ => rfl
  · intro z hz
    rw [hDpre, mem_preimage, h.apply_symm_apply]
    exact hrmaps hz
  · intro z hz
    rw [hDpre, mem_preimage] at hz
    change h.symm (r (h z)) = z
    rw [hrid hz]
    exact h.symm_apply_apply z
  · rintro z ⟨hz1, hz2⟩
    rw [hDpre, mem_preimage] at hz2
    rw [hfrD, mem_preimage, h.apply_symm_apply]
    exact hrfr ⟨hz1, hz2⟩
  · intro w hw
    rw [hfrD, mem_preimage] at hw
    obtain ⟨y, hy, hyw⟩ := hfrsub hw
    refine ⟨h.symm y, ?_, ?_⟩
    · rw [hfrD', mem_preimage, h.apply_symm_apply]
      exact hy
    · change h.symm (r (h (h.symm y))) = w
      rw [h.apply_symm_apply, hyw, h.symm_apply_apply]
  · intro z hz
    rw [hDpre, mem_preimage] at hz
    exact ht0 hz
  · intro z hz
    rw [hfrD', mem_preimage] at hz
    exact ht1 hz
  · intro z hz
    exact hticc (h z) hz

end DifferentialGeometry.Topology.PiecewiseLinear
