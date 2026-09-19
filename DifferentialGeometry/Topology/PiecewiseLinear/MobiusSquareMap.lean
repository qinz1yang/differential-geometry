/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGluing
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusManifold
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusSquare
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAffine

/-! Affine charts and flip-seam compatibility for the five-triangle Moebius band. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

private theorem triangleIndex_injective (i : Fin 5) :
    Function.Injective (fun j : Fin 3 => i + j.castLE (by decide : 3 ≤ 5)) := by
  intro j k h
  have h' : j.castLE (by decide : 3 ≤ 5) = k.castLE (by decide : 3 ≤ 5) :=
    add_left_cancel h
  exact Fin.ext (congrArg (Fin.val : Fin 5 → ℕ) h')

private theorem triangleIndex_mem (i : Fin 5) (j : Fin 3) :
    i + j.castLE (by decide : 3 ≤ 5) ∈ mobiusTriIdx i := by
  revert i j
  decide

private theorem exists_triangleIndex (i v : Fin 5) (hv : v ∈ mobiusTriIdx i) :
    ∃ j : Fin 3, i + j.castLE (by decide : 3 ≤ 5) = v := by
  revert i v
  decide

theorem exists_isPLHomeomorphOn_mobiusSquareTriangle_affine (i : Fin 5) :
    ∃ A : (Fin 5 → ℝ) →ᵃ[ℝ] (ℝ × ℝ),
      IsPLHomeomorphOn A (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)))
        (mobiusSquareTriangle i) ∧
      ∀ j : Fin 3, A (mobiusVertex (i + j.castLE (by decide : 3 ≤ 5))) =
        mobiusSquareTriangleVertex i j := by
  classical
  let e₀ : Fin 3 ≃ mobiusTri i := Equiv.ofBijective
    (fun j => ⟨mobiusVertex (i + j.castLE (by decide : 3 ≤ 5)),
      mobiusVertex_mem_mobiusTri (triangleIndex_mem i j)⟩) (by
      constructor
      · intro j k h
        exact triangleIndex_injective i (mobiusVertex_injective (congrArg Subtype.val h))
      · rintro ⟨v, hv⟩
        obtain ⟨k, hk, rfl⟩ := exists_eq_mobiusVertex_of_mem_mobiusTri hv
        obtain ⟨j, hj⟩ := exists_triangleIndex i k hk
        exact ⟨j, Subtype.ext (congrArg mobiusVertex hj)⟩)
  let t : Finset (ℝ × ℝ) := Finset.univ.image (mobiusSquareTriangleVertex i)
  let e₁ : Fin 3 ≃ t := Equiv.ofBijective
    (fun j => ⟨mobiusSquareTriangleVertex i j,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩) (by
      constructor
      · intro j k h
        exact (mobiusSquareTriangleVertex_affineIndependent i).injective
          (congrArg Subtype.val h)
      · rintro ⟨v, hv⟩
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
        exact ⟨j, rfl⟩)
  have ht : AffineIndependent ℝ ((↑) : t → ℝ × ℝ) :=
    (affineIndependent_equiv e₁).mp (mobiusSquareTriangleVertex_affineIndependent i)
  obtain ⟨A, hA, hAv⟩ := exists_isPLHomeomorphOn_affine_of_equiv
    (mobiusComplex.indep (mobiusTri_mem_faces i)) ht (e₀.symm.trans e₁)
  have htset : (t : Set (ℝ × ℝ)) = range (mobiusSquareTriangleVertex i) := by
    simp [t]
  refine ⟨A, ?_, ?_⟩
  · simpa only [htset, mobiusSquareTriangle] using hA
  · intro j
    have h := hAv (e₀ j)
    change A (mobiusVertex (i + j.castLE (by decide : 3 ≤ 5))) =
      (e₁ (e₀.symm (e₀ j)) : ℝ × ℝ) at h
    rw [Equiv.symm_apply_apply] at h
    exact h.trans (show (e₁ j : ℝ × ℝ) = mobiusSquareTriangleVertex i j from rfl)

def mobiusSquareChart (i : Fin 5) : (Fin 5 → ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  (exists_isPLHomeomorphOn_mobiusSquareTriangle_affine i).choose

theorem isPLHomeomorphOn_mobiusSquareChart (i : Fin 5) :
    IsPLHomeomorphOn (mobiusSquareChart i)
      (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ))) (mobiusSquareTriangle i) :=
  (exists_isPLHomeomorphOn_mobiusSquareTriangle_affine i).choose_spec.1

theorem mobiusSquareChart_apply (i : Fin 5) (j : Fin 3) :
    mobiusSquareChart i (mobiusVertex (i + j.castLE (by decide : 3 ≤ 5))) =
      mobiusSquareTriangleVertex i j :=
  (exists_isPLHomeomorphOn_mobiusSquareTriangle_affine i).choose_spec.2 j

private theorem affine_eqOn_mobiusTri_inter {F : Type*}
    [AddCommGroup F] [Module ℝ F] {i j : Fin 5} {A B : (Fin 5 → ℝ) →ᵃ[ℝ] F}
    (h : ∀ v ∈ mobiusTriIdx i, v ∈ mobiusTriIdx j →
      A (mobiusVertex v) = B (mobiusVertex v)) :
    EqOn A B (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) := by
  rw [mobiusComplex.convexHull_inter_convexHull
    (mobiusTri_mem_faces i) (mobiusTri_mem_faces j)]
  apply (AffineMap.eqOn_affineSpan ?_).mono (convexHull_subset_affineSpan _)
  rintro x ⟨hi, hj⟩
  obtain ⟨v, hv, rfl⟩ := exists_eq_mobiusVertex_of_mem_mobiusTri hi
  exact h v hv ((mobiusVertex_mem_mobiusTri_iff j v).mp hj)

private theorem triangleIndex_near_cases (i j v : Fin 5)
    (hle : i.val ≤ j.val) (hgap : j.val ≤ i.val + 2) (hne : i ≠ j)
    (hv : v ∈ mobiusTriIdx i) (hw : v ∈ mobiusTriIdx j) :
    (i = 0 ∧ j = 1 ∧ v = 1) ∨ (i = 0 ∧ j = 1 ∧ v = 2) ∨
    (i = 0 ∧ j = 2 ∧ v = 2) ∨ (i = 1 ∧ j = 2 ∧ v = 2) ∨
    (i = 1 ∧ j = 2 ∧ v = 3) ∨ (i = 1 ∧ j = 3 ∧ v = 3) ∨
    (i = 2 ∧ j = 3 ∧ v = 3) ∨ (i = 2 ∧ j = 3 ∧ v = 4) ∨
    (i = 2 ∧ j = 4 ∧ v = 4) ∨ (i = 3 ∧ j = 4 ∧ v = 4) ∨
    (i = 3 ∧ j = 4 ∧ v = 0) := by
  revert i j v
  decide

private theorem triangleIndex_wrap_cases (i j v : Fin 5)
    (hpair : (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 4))
    (hv : v ∈ mobiusTriIdx i) (hw : v ∈ mobiusTriIdx j) :
    (i = 0 ∧ j = 3 ∧ v = 0) ∨ (i = 0 ∧ j = 4 ∧ v = 0) ∨
    (i = 0 ∧ j = 4 ∧ v = 1) ∨ (i = 1 ∧ j = 4 ∧ v = 1) := by
  revert i j v
  decide
private theorem mobiusSquareChart_eqOn_inter_of_near {i j : Fin 5}
    (hle : i.val ≤ j.val) (hgap : j.val ≤ i.val + 2) :
    EqOn (mobiusSquareChart i) (mobiusSquareChart j)
      (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
        convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) := by
  by_cases heq : i = j
  · subst j
    intro x hx
    rfl
  have h01 : mobiusSquareChart 0 (mobiusVertex 1) = (1, 0) :=
    mobiusSquareChart_apply 0 1
  have h02 : mobiusSquareChart 0 (mobiusVertex 2) = (0, 1 / 4) :=
    mobiusSquareChart_apply 0 2
  have h10 : mobiusSquareChart 1 (mobiusVertex 1) = (1, 0) :=
    mobiusSquareChart_apply 1 0
  have h11 : mobiusSquareChart 1 (mobiusVertex 2) = (0, 1 / 4) :=
    mobiusSquareChart_apply 1 1
  have h12 : mobiusSquareChart 1 (mobiusVertex 3) = (1, 1 / 2) :=
    mobiusSquareChart_apply 1 2
  have h20 : mobiusSquareChart 2 (mobiusVertex 2) = (0, 1 / 4) :=
    mobiusSquareChart_apply 2 0
  have h21 : mobiusSquareChart 2 (mobiusVertex 3) = (1, 1 / 2) :=
    mobiusSquareChart_apply 2 1
  have h22 : mobiusSquareChart 2 (mobiusVertex 4) = (0, 3 / 4) :=
    mobiusSquareChart_apply 2 2
  have h30 : mobiusSquareChart 3 (mobiusVertex 3) = (1, 1 / 2) :=
    mobiusSquareChart_apply 3 0
  have h31 : mobiusSquareChart 3 (mobiusVertex 4) = (0, 3 / 4) :=
    mobiusSquareChart_apply 3 1
  have h32 : mobiusSquareChart 3 (mobiusVertex 0) = (1, 1) :=
    mobiusSquareChart_apply 3 2
  have h40 : mobiusSquareChart 4 (mobiusVertex 4) = (0, 3 / 4) :=
    mobiusSquareChart_apply 4 0
  have h41 : mobiusSquareChart 4 (mobiusVertex 0) = (1, 1) :=
    mobiusSquareChart_apply 4 1
  apply affine_eqOn_mobiusTri_inter
  intro v hv hw
  rcases triangleIndex_near_cases i j v hle hgap heq hv hw with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h01.trans h10.symm
  · exact h02.trans h11.symm
  · exact h02.trans h20.symm
  · exact h11.trans h20.symm
  · exact h12.trans h21.symm
  · exact h12.trans h30.symm
  · exact h21.trans h30.symm
  · exact h22.trans h31.symm
  · exact h22.trans h40.symm
  · exact h31.trans h40.symm
  · exact h32.trans h41.symm

private def squareFlip : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  AffineMap.const ℝ (ℝ × ℝ) (1, 1) - AffineMap.id ℝ (ℝ × ℝ)

private theorem mobiusSquareChart_eqOn_inter_of_wrap {i j : Fin 5}
    (hpair : (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 4)) :
    EqOn (mobiusSquareChart j) (squareFlip.comp (mobiusSquareChart i))
      (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
        convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) := by
  have h00 : mobiusSquareChart 0 (mobiusVertex 0) = (0, 0) :=
    mobiusSquareChart_apply 0 0
  have h01 : mobiusSquareChart 0 (mobiusVertex 1) = (1, 0) :=
    mobiusSquareChart_apply 0 1
  have h10 : mobiusSquareChart 1 (mobiusVertex 1) = (1, 0) :=
    mobiusSquareChart_apply 1 0
  have h32 : mobiusSquareChart 3 (mobiusVertex 0) = (1, 1) :=
    mobiusSquareChart_apply 3 2
  have h41 : mobiusSquareChart 4 (mobiusVertex 0) = (1, 1) :=
    mobiusSquareChart_apply 4 1
  have h42 : mobiusSquareChart 4 (mobiusVertex 1) = (0, 1) :=
    mobiusSquareChart_apply 4 2
  apply affine_eqOn_mobiusTri_inter
  intro v hv hw
  rcases triangleIndex_wrap_cases i j v hpair hv hw with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · change mobiusSquareChart 3 (mobiusVertex 0) = squareFlip (mobiusSquareChart 0 (mobiusVertex 0))
    rw [h32, h00]
    simp [squareFlip]
  · change mobiusSquareChart 4 (mobiusVertex 0) = squareFlip (mobiusSquareChart 0 (mobiusVertex 0))
    rw [h41, h00]
    simp [squareFlip]
  · change mobiusSquareChart 4 (mobiusVertex 1) = squareFlip (mobiusSquareChart 0 (mobiusVertex 1))
    rw [h42, h01]
    simp [squareFlip]
  · change mobiusSquareChart 4 (mobiusVertex 1) = squareFlip (mobiusSquareChart 1 (mobiusVertex 1))
    rw [h42, h10]
    simp [squareFlip]

private theorem mobiusSquareChart_snd_eq_zero_of_wrap {i j : Fin 5}
    (hpair : (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 4))
    {x : Fin 5 → ℝ} (hx : x ∈ convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) :
    (mobiusSquareChart i x).2 = 0 := by
  have h00 : mobiusSquareChart 0 (mobiusVertex 0) = (0, 0) :=
    mobiusSquareChart_apply 0 0
  have h01 : mobiusSquareChart 0 (mobiusVertex 1) = (1, 0) :=
    mobiusSquareChart_apply 0 1
  have h10 : mobiusSquareChart 1 (mobiusVertex 1) = (1, 0) :=
    mobiusSquareChart_apply 1 0
  have hz : EqOn ((LinearMap.snd ℝ ℝ ℝ).toAffineMap.comp (mobiusSquareChart i))
      (AffineMap.const ℝ (Fin 5 → ℝ) 0)
      (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
        convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) := by
    apply affine_eqOn_mobiusTri_inter
    intro v hv hw
    rcases triangleIndex_wrap_cases i j v hpair hv hw with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact congrArg Prod.snd h00
    · exact congrArg Prod.snd h00
    · exact congrArg Prod.snd h01
    · exact congrArg Prod.snd h10
  exact hz hx

theorem mobiusSquareChart_comp_eqOn_inter {F : Type*} (g : ℝ × ℝ → F)
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1, g (s, 1) = g (1 - s, 0)) (i j : Fin 5) :
    EqOn (g ∘ mobiusSquareChart i) (g ∘ mobiusSquareChart j)
      (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
        convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) := by
  wlog hij : i.val ≤ j.val generalizing i j
  · intro x hx
    exact (this j i (le_of_not_ge hij) ⟨hx.2, hx.1⟩).symm
  by_cases hnear : j.val ≤ i.val + 2
  · intro x hx
    exact congrArg g (mobiusSquareChart_eqOn_inter_of_near hij hnear hx)
  have hpair : (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 4) := by
    revert i j
    decide
  intro x hx
  have heq := mobiusSquareChart_eqOn_inter_of_wrap hpair hx
  have hy := mobiusSquareChart_snd_eq_zero_of_wrap hpair hx
  have hsq := mobiusSquareTriangle_subset_square i
    ((isPLHomeomorphOn_mobiusSquareChart i).bijOn.mapsTo hx.1)
  have hs : 1 - (mobiusSquareChart i x).1 ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hsq.1.2], by linarith [hsq.1.1]⟩
  have hjshape : mobiusSquareChart j x = (1 - (mobiusSquareChart i x).1, 1) := by
    rw [heq]
    change (1 - (mobiusSquareChart i x).1, 1 - (mobiusSquareChart i x).2) = _
    rw [hy, sub_zero]
  change g (mobiusSquareChart i x) = g (mobiusSquareChart j x)
  calc
    g (mobiusSquareChart i x) = g ((mobiusSquareChart i x).1, 0) :=
      congrArg g (Prod.ext rfl hy)
    _ = g (1 - (mobiusSquareChart i x).1, 1) := by
      simpa only [sub_sub_cancel] using (hseam _ hs).symm
    _ = g (mobiusSquareChart j x) := congrArg g hjshape.symm

private theorem index_le_one_of_mem_mobiusSquareTriangle_of_snd_eq_zero
    {i : Fin 5} {x : ℝ × ℝ} (hx : x ∈ mobiusSquareTriangle i) (hzero : x.2 = 0) :
    i.val ≤ 1 := by
  fin_cases i
  · decide
  · decide
  · obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_mobiusSquareTriangle_two_iff x).mp hx
    linarith
  · obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_mobiusSquareTriangle_three_iff x).mp hx
    linarith
  · obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_mobiusSquareTriangle_four_iff x).mp hx
    linarith

private theorem three_le_index_of_mem_mobiusSquareTriangle_of_snd_eq_one
    {i : Fin 5} {x : ℝ × ℝ} (hx : x ∈ mobiusSquareTriangle i) (hone : x.2 = 1) :
    3 ≤ i.val := by
  fin_cases i
  · obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_mobiusSquareTriangle_zero_iff x).mp hx
    linarith
  · obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_mobiusSquareTriangle_one_iff x).mp hx
    linarith
  · obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_mobiusSquareTriangle_two_iff x).mp hx
    linarith
  · decide
  · decide

theorem injOn_mobiusSquareTriangle {F : Type*} {g : ℝ × ℝ → F}
    (hfiber : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g x = g y →
        x = y ∨ (x.2 = 0 ∧ y.2 = 1 ∧ x.1 = 1 - y.1) ∨
          (x.2 = 1 ∧ y.2 = 0 ∧ x.1 = 1 - y.1)) (i : Fin 5) :
    InjOn g (mobiusSquareTriangle i) := by
  intro x hx y hy hxy
  rcases hfiber x (mobiusSquareTriangle_subset_square i hx)
    y (mobiusSquareTriangle_subset_square i hy) hxy with h | ⟨hx₀, hy₁, -⟩ | ⟨hx₁, hy₀, -⟩
  · exact h
  · have hi₀ := index_le_one_of_mem_mobiusSquareTriangle_of_snd_eq_zero hx hx₀
    have hi₁ := three_le_index_of_mem_mobiusSquareTriangle_of_snd_eq_one hy hy₁
    omega
  · have hi₁ := three_le_index_of_mem_mobiusSquareTriangle_of_snd_eq_one hx hx₁
    have hi₀ := index_le_one_of_mem_mobiusSquareTriangle_of_snd_eq_zero hy hy₀
    omega

theorem isPLHomeomorphOn_comp_mobiusSquareChart {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {g : ℝ × ℝ → F} (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfiber : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g x = g y →
        x = y ∨ (x.2 = 0 ∧ y.2 = 1 ∧ x.1 = 1 - y.1) ∨
          (x.2 = 1 ∧ y.2 = 0 ∧ x.1 = 1 - y.1)) (i : Fin 5) :
    IsPLHomeomorphOn (g ∘ mobiusSquareChart i)
      (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ))) (g '' mobiusSquareTriangle i) := by
  have hA := isPLHomeomorphOn_mobiusSquareChart i
  have hP := isPolyhedron_convexHull_of_affineIndependent (mobiusTri i)
    (mobiusComplex.indep (mobiusTri_mem_faces i))
  have hT : IsPolyhedron (mobiusSquareTriangle i) := by
    rw [← hA.image_eq]
    exact hP.image_of_isPiecewiseAffineOn hA.isPiecewiseAffineOn hA.bijOn.injOn
  exact hA.trans (isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hT
    (hg.mono_of_isPolyhedron hT (mobiusSquareTriangle_subset_square i))
    (injOn_mobiusSquareTriangle hfiber i).bijOn_image)

private theorem mobiusSquareChart_image_inter_indices (i j : Fin 5) :
    mobiusSquareChart i '' (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) =
      convexHull ℝ ((fun v => mobiusSquareChart i (mobiusVertex v)) ''
        ((mobiusTriIdx i ∩ mobiusTriIdx j : Finset (Fin 5)) : Set (Fin 5))) := by
  rw [mobiusComplex.convexHull_inter_convexHull
    (mobiusTri_mem_faces i) (mobiusTri_mem_faces j),
    (mobiusSquareChart i).image_convexHull]
  have hvertices : (mobiusTri i : Set (Fin 5 → ℝ)) ∩ (mobiusTri j : Set (Fin 5 → ℝ)) =
      mobiusVertex '' ((mobiusTriIdx i ∩ mobiusTriIdx j : Finset (Fin 5)) : Set (Fin 5)) := by
    simp only [Finset.coe_inter, image_inter mobiusVertex_injective, mobiusTri, Finset.coe_image]
  rw [hvertices, image_image]

private theorem mobiusSquareChart_image_inter_of_near {i j : Fin 5}
    (hle : i.val ≤ j.val) (hgap : j.val ≤ i.val + 2) :
    mobiusSquareChart i '' (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) =
      mobiusSquareTriangle i ∩ mobiusSquareTriangle j := by
  by_cases heq : i = j
  · subst j
    simpa only [inter_self] using (isPLHomeomorphOn_mobiusSquareChart i).image_eq
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
      (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
    revert i j
    decide
  have h01 : mobiusSquareChart 0 (mobiusVertex 1) = mobiusSquareVertex 1 :=
    mobiusSquareChart_apply 0 1
  have h02 : mobiusSquareChart 0 (mobiusVertex 2) = mobiusSquareVertex 2 :=
    mobiusSquareChart_apply 0 2
  have h11 : mobiusSquareChart 1 (mobiusVertex 2) = mobiusSquareVertex 2 :=
    mobiusSquareChart_apply 1 1
  have h12 : mobiusSquareChart 1 (mobiusVertex 3) = mobiusSquareVertex 3 :=
    mobiusSquareChart_apply 1 2
  have h21 : mobiusSquareChart 2 (mobiusVertex 3) = mobiusSquareVertex 3 :=
    mobiusSquareChart_apply 2 1
  have h22 : mobiusSquareChart 2 (mobiusVertex 4) = mobiusSquareVertex 4 :=
    mobiusSquareChart_apply 2 2
  have h31 : mobiusSquareChart 3 (mobiusVertex 4) = mobiusSquareVertex 4 :=
    mobiusSquareChart_apply 3 1
  have h32 : mobiusSquareChart 3 (mobiusVertex 0) = mobiusSquareVertex 5 :=
    mobiusSquareChart_apply 3 2
  rw [mobiusSquareChart_image_inter_indices]
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show mobiusTriIdx 0 ∩ mobiusTriIdx 1 = {1, 2} by decide]
    simp only [Finset.coe_pair, image_pair, h01, h02, convexHull_pair,
      mobiusSquareTriangle_zero_inter_one]
  · rw [show mobiusTriIdx 0 ∩ mobiusTriIdx 2 = {2} by decide]
    simp only [Finset.coe_singleton, image_singleton, h02, convexHull_singleton,
      mobiusSquareTriangle_zero_inter_two]
  · rw [show mobiusTriIdx 1 ∩ mobiusTriIdx 2 = {2, 3} by decide]
    simp only [Finset.coe_pair, image_pair, h11, h12, convexHull_pair,
      mobiusSquareTriangle_one_inter_two]
  · rw [show mobiusTriIdx 1 ∩ mobiusTriIdx 3 = {3} by decide]
    simp only [Finset.coe_singleton, image_singleton, h12, convexHull_singleton,
      mobiusSquareTriangle_one_inter_three]
  · rw [show mobiusTriIdx 2 ∩ mobiusTriIdx 3 = {3, 4} by decide]
    simp only [Finset.coe_pair, image_pair, h21, h22, convexHull_pair,
      mobiusSquareTriangle_two_inter_three]
  · rw [show mobiusTriIdx 2 ∩ mobiusTriIdx 4 = {4} by decide]
    simp only [Finset.coe_singleton, image_singleton, h22, convexHull_singleton,
      mobiusSquareTriangle_two_inter_four]
  · rw [show mobiusTriIdx 3 ∩ mobiusTriIdx 4 = {4, 0} by decide]
    simp only [Finset.coe_pair, image_pair, h31, h32, convexHull_pair,
      mobiusSquareTriangle_three_inter_four]

private theorem mobiusSquareChart_zero_image_inter_three :
    mobiusSquareChart 0 '' (convexHull ℝ (mobiusTri 0 : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri 3 : Set (Fin 5 → ℝ))) =
      {mobiusSquareVertex 0} := by
  have h0 : mobiusSquareChart 0 (mobiusVertex 0) = mobiusSquareVertex 0 :=
    mobiusSquareChart_apply 0 0
  rw [mobiusSquareChart_image_inter_indices,
    show mobiusTriIdx 0 ∩ mobiusTriIdx 3 = {0} by decide]
  simp only [Finset.coe_singleton, image_singleton, h0, convexHull_singleton]

private theorem mobiusSquareChart_zero_image_inter_four :
    mobiusSquareChart 0 '' (convexHull ℝ (mobiusTri 0 : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri 4 : Set (Fin 5 → ℝ))) =
      segment ℝ (mobiusSquareVertex 0) (mobiusSquareVertex 1) := by
  have h0 : mobiusSquareChart 0 (mobiusVertex 0) = mobiusSquareVertex 0 :=
    mobiusSquareChart_apply 0 0
  have h1 : mobiusSquareChart 0 (mobiusVertex 1) = mobiusSquareVertex 1 :=
    mobiusSquareChart_apply 0 1
  rw [mobiusSquareChart_image_inter_indices,
    show mobiusTriIdx 0 ∩ mobiusTriIdx 4 = {0, 1} by decide]
  simp only [Finset.coe_pair, image_pair, h0, h1, convexHull_pair]

private theorem mobiusSquareChart_one_image_inter_four :
    mobiusSquareChart 1 '' (convexHull ℝ (mobiusTri 1 : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri 4 : Set (Fin 5 → ℝ))) =
      {mobiusSquareVertex 1} := by
  have h0 : mobiusSquareChart 1 (mobiusVertex 1) = mobiusSquareVertex 1 :=
    mobiusSquareChart_apply 1 0
  rw [mobiusSquareChart_image_inter_indices,
    show mobiusTriIdx 1 ∩ mobiusTriIdx 4 = {1} by decide]
  simp only [Finset.coe_singleton, image_singleton, h0, convexHull_singleton]

private theorem mem_mobiusSquareTriangle_flip_cases {i j : Fin 5} {x y : ℝ × ℝ}
    (hx : x ∈ mobiusSquareTriangle i) (hy : y ∈ mobiusSquareTriangle j)
    (hx₀ : x.2 = 0) (hy₁ : y.2 = 1) (hxy : x.1 = 1 - y.1) :
    (i = 0 ∧ j = 3 ∧ x = mobiusSquareVertex 0) ∨
      (i = 0 ∧ j = 4 ∧ x ∈ segment ℝ (mobiusSquareVertex 0) (mobiusSquareVertex 1)) ∨
        (i = 1 ∧ j = 4 ∧ x = mobiusSquareVertex 1) := by
  have hi := index_le_one_of_mem_mobiusSquareTriangle_of_snd_eq_zero hx hx₀
  have hj := three_le_index_of_mem_mobiusSquareTriangle_of_snd_eq_one hy hy₁
  have hindices : ∀ a b : Fin 5, a.val ≤ 1 → 3 ≤ b.val →
      (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 1 ∧ b = 3) ∨ (a = 1 ∧ b = 4) := by
    decide
  rcases hindices i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hy₀, hy₂, hy₃⟩ := (mem_mobiusSquareTriangle_three_iff y).mp hy
    refine Or.inl ⟨rfl, rfl, ?_⟩
    ext <;> dsimp [mobiusSquareVertex] <;> linarith
  · refine Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)
    rw [segment_eq_image_lineMap]
    refine ⟨x.1, (mobiusSquareTriangle_subset_square 0 hx).1, ?_⟩
    ext <;> dsimp [mobiusSquareVertex, AffineMap.lineMap_apply] <;> linarith
  · obtain ⟨hu₀, hu₁, hu₂⟩ := (mem_mobiusSquareTriangle_one_iff x).mp hx
    obtain ⟨hv₀, hv₁, hv₂⟩ := (mem_mobiusSquareTriangle_three_iff y).mp hy
    linarith
  · obtain ⟨hu₀, hu₁, hu₂⟩ := (mem_mobiusSquareTriangle_one_iff x).mp hx
    refine Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)
    ext <;> dsimp [mobiusSquareVertex] <;> linarith

theorem mobiusSquareChart_comp_image_inter {F : Type*} (g : ℝ × ℝ → F)
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1, g (s, 1) = g (1 - s, 0))
    (hfiber : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g x = g y →
        x = y ∨ (x.2 = 0 ∧ y.2 = 1 ∧ x.1 = 1 - y.1) ∨
          (x.2 = 1 ∧ y.2 = 0 ∧ x.1 = 1 - y.1)) (i j : Fin 5) :
    (g ∘ mobiusSquareChart i) '' (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
      convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) =
      g '' mobiusSquareTriangle i ∩ g '' mobiusSquareTriangle j := by
  wlog hij : i.val ≤ j.val generalizing i j
  · calc
      (g ∘ mobiusSquareChart i) '' (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
          convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) =
          (g ∘ mobiusSquareChart j) '' (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
            convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) :=
        (mobiusSquareChart_comp_eqOn_inter g hseam i j).image_eq
      _ = (g ∘ mobiusSquareChart j) '' (convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ)) ∩
          convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ))) := by rw [inter_comm]
      _ = g '' mobiusSquareTriangle j ∩ g '' mobiusSquareTriangle i :=
        this j i (le_of_not_ge hij)
      _ = g '' mobiusSquareTriangle i ∩ g '' mobiusSquareTriangle j := inter_comm _ _
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨mobiusSquareChart i x,
      (isPLHomeomorphOn_mobiusSquareChart i).bijOn.mapsTo hx.1, rfl⟩,
      ⟨mobiusSquareChart j x,
        (isPLHomeomorphOn_mobiusSquareChart j).bijOn.mapsTo hx.2, ?_⟩⟩
    exact (mobiusSquareChart_comp_eqOn_inter g hseam i j hx).symm
  · rintro y ⟨⟨u, hu, huy⟩, ⟨v, hv, hvy⟩⟩
    have huv : g u = g v := huy.trans hvy.symm
    have huimage : u ∈ mobiusSquareChart i ''
        (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ)) ∩
          convexHull ℝ (mobiusTri j : Set (Fin 5 → ℝ))) := by
      rcases hfiber u (mobiusSquareTriangle_subset_square i hu)
        v (mobiusSquareTriangle_subset_square j hv) huv with
        heq | ⟨hu₀, hv₁, huv₁⟩ | ⟨hu₁, hv₀, -⟩
      · subst v
        by_cases hnear : j.val ≤ i.val + 2
        · rw [mobiusSquareChart_image_inter_of_near hij hnear]
          exact ⟨hu, hv⟩
        · have hindices : ∀ a b : Fin 5, a.val ≤ b.val → ¬ b.val ≤ a.val + 2 →
              (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 1 ∧ b = 4) := by
            decide
          have hbad : u ∈ mobiusSquareTriangle i ∩ mobiusSquareTriangle j := ⟨hu, hv⟩
          rcases hindices i j hij hnear with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [mobiusSquareTriangle_zero_inter_three] at hbad
            exact hbad.elim
          · rw [mobiusSquareTriangle_zero_inter_four] at hbad
            exact hbad.elim
          · rw [mobiusSquareTriangle_one_inter_four] at hbad
            exact hbad.elim
      · rcases mem_mobiusSquareTriangle_flip_cases hu hv hu₀ hv₁ huv₁ with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hsegment⟩ | ⟨rfl, rfl, rfl⟩
        · rw [mobiusSquareChart_zero_image_inter_three]
          exact mem_singleton _
        · rw [mobiusSquareChart_zero_image_inter_four]
          exact hsegment
        · rw [mobiusSquareChart_one_image_inter_four]
          exact mem_singleton _
      · have hi := three_le_index_of_mem_mobiusSquareTriangle_of_snd_eq_one hu hu₁
        have hj := index_le_one_of_mem_mobiusSquareTriangle_of_snd_eq_zero hv hv₀
        omega
    obtain ⟨x, hx, hxu⟩ := huimage
    exact ⟨x, hx, (congrArg g hxu).trans huy⟩

theorem exists_isPLHomeomorphOn_mobiusComplex_of_square {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {g : ℝ × ℝ → F} (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1, g (s, 1) = g (1 - s, 0))
    (hfiber : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g x = g y →
        x = y ∨ (x.2 = 0 ∧ y.2 = 1 ∧ x.1 = 1 - y.1) ∨
          (x.2 = 1 ∧ y.2 = 0 ∧ x.1 = 1 - y.1)) :
    ∃ f : (Fin 5 → ℝ) → F,
      IsPLHomeomorphOn f mobiusComplex.space (g '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  have hP (i : Fin 5) : IsPolyhedron (convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ))) :=
    isPolyhedron_convexHull_of_affineIndependent (mobiusTri i)
      (mobiusComplex.indep (mobiusTri_mem_faces i))
  obtain ⟨f, hf, -⟩ := exists_isPLHomeomorphOn_iUnion hP
    (isPLHomeomorphOn_comp_mobiusSquareChart hg hfiber)
    (mobiusSquareChart_comp_eqOn_inter g hseam)
    (mobiusSquareChart_comp_image_inter g hseam hfiber)
  have hspace : (⋃ i : Fin 5, convexHull ℝ (mobiusTri i : Set (Fin 5 → ℝ))) =
      mobiusComplex.space := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mobiusComplex.convexHull_subset_space (mobiusTri_mem_faces i) hi
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mobiusComplex.mem_space_iff.mp hx
      obtain ⟨-, i, hsi⟩ := mem_mobiusComplex_faces_iff.mp hs
      exact mem_iUnion.mpr ⟨i, convexHull_mono (Finset.coe_subset.mpr hsi) hxs⟩
  have htarget : (⋃ i : Fin 5, g '' mobiusSquareTriangle i) =
      g '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← image_iUnion, iUnion_mobiusSquareTriangle]
  exact ⟨f, by simpa only [hspace, htarget] using hf⟩

end

end DifferentialGeometry.Topology.PiecewiseLinear
