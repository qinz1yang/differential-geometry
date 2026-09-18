/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
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

end

end DifferentialGeometry.Topology.PiecewiseLinear
