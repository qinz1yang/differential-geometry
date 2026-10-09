/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellInterior
import DifferentialGeometry.Topology.PlanarJordan.DiskUnion

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def planarProjection (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (p 0) + EuclideanSpace.single 1 (p 1)

@[simp] theorem planarProjection_apply_zero (p : EuclideanSpace ℝ (Fin 3)) :
    planarProjection p 0 = p 0 := by
  simp [planarProjection, PiLp.add_apply]

@[simp] theorem planarProjection_apply_one (p : EuclideanSpace ℝ (Fin 3)) :
    planarProjection p 1 = p 1 := by
  simp [planarProjection, PiLp.add_apply]

theorem continuous_planarProjection : Continuous planarProjection := by
  have h : planarProjection = fun p : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 (fun i : Fin 2 => p i.castSucc) := by
    funext p
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [planarProjection, PiLp.add_apply]
  rw [h]
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp
    (continuous_pi fun i => continuous_euclideanApply i.castSucc)

@[simp] theorem planarProjection_planarPoint (x : EuclideanSpace ℝ (Fin 2)) :
    planarProjection (planarPoint x) = x := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp

theorem planarPoint_planarProjection {p : EuclideanSpace ℝ (Fin 3)} (hp : p 2 = 0) :
    planarPoint (planarProjection p) = p := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [hp]

theorem planarPoint_image_planarProjection_image {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ p ∈ D, p 2 = 0) :
    planarPoint '' (planarProjection '' D) = D := by
  ext p
  constructor
  · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
    rw [planarPoint_planarProjection (hhalf q hq)]
    exact hq
  · intro hp
    exact ⟨planarProjection p, ⟨p, hp, rfl⟩, planarPoint_planarProjection (hhalf p hp)⟩

theorem planarProjection_image_inter {A B : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : ∀ p ∈ A, p 2 = 0) (hB : ∀ p ∈ B, p 2 = 0) :
    planarProjection '' (A ∩ B) = planarProjection '' A ∩ planarProjection '' B := by
  apply image_inter_on
  intro p hp q hq hpq
  have h := congrArg planarPoint hpq
  rwa [planarPoint_planarProjection (hB p hp), planarPoint_planarProjection (hA q hq)] at h

theorem isTopologicalCellWithInterior_planarPoint_image {K I : Set (EuclideanSpace ℝ (Fin 2))}
    (h : IsTopologicalCellWithInterior 2 K I) :
    IsTopologicalCellWithInterior 2 (planarPoint '' K) (planarPoint '' I) := by
  rcases h with ⟨φ, hI⟩
  let e : K ≃ₜ (planarPoint '' K) :=
    isometry_planarPoint.isEmbedding.homeomorphImage K
  let ψ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ (planarPoint '' K) :=
    φ.trans e
  have hcomp : (fun x => (ψ x : EuclideanSpace ℝ (Fin 3))) =
      (fun x => planarPoint (φ x : EuclideanSpace ℝ (Fin 2))) := by
    funext q
    rfl
  have hset : ∀ S : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1),
      (Subtype.val : (planarPoint '' K) → EuclideanSpace ℝ (Fin 3)) '' (ψ '' S) =
        planarPoint '' ((Subtype.val : K → EuclideanSpace ℝ (Fin 2)) '' (φ '' S)) := by
    intro S
    rw [image_image, image_image, image_image, hcomp]
  refine ⟨ψ, ?_⟩
  rw [hI, hset]

theorem isTopologicalCell_planarPoint_image {K : Set (EuclideanSpace ℝ (Fin 2))}
    (h : IsTopologicalCell 2 K) : IsTopologicalCell 2 (planarPoint '' K) := by
  rcases h with ⟨φ⟩
  let e : K ≃ₜ (planarPoint '' K) :=
    isometry_planarPoint.isEmbedding.homeomorphImage K
  exact ⟨e.symm.trans φ⟩

theorem isTopologicalCellWithInterior_of_planarProjection
    {D Dint : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ p ∈ D, p 2 = 0) (h : IsTopologicalCellWithInterior 2 D Dint) :
    IsTopologicalCellWithInterior 2 (planarProjection '' D) (planarProjection '' Dint) := by
  rcases h with ⟨φ, hDint⟩
  let K := planarProjection '' D
  have hKD : planarPoint '' K = D := planarPoint_image_planarProjection_image hhalf
  let eK : K ≃ₜ D :=
    (isometry_planarPoint.isEmbedding.homeomorphImage K).trans (Homeomorph.setCongr hKD)
  let ψ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ K := φ.trans eK.symm
  have hval : ∀ p : D,
      (eK.symm p : EuclideanSpace ℝ (Fin 2)) =
        planarProjection (p : EuclideanSpace ℝ (Fin 3)) := by
    intro p
    have heq := congrArg Subtype.val (eK.apply_symm_apply p)
    have heq' : (eK (eK.symm p) : EuclideanSpace ℝ (Fin 3)) =
        (p : EuclideanSpace ℝ (Fin 3)) := heq
    have hpp : planarPoint (eK.symm p : EuclideanSpace ℝ (Fin 2)) =
        (p : EuclideanSpace ℝ (Fin 3)) :=
      heq'
    rw [← hpp, planarProjection_planarPoint]
  have hcomp : (fun x => (ψ x : EuclideanSpace ℝ (Fin 2))) =
      (fun x => planarProjection (φ x : EuclideanSpace ℝ (Fin 3))) := by
    funext q
    exact hval (φ q)
  have hset : ∀ S : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1),
      (Subtype.val : K → EuclideanSpace ℝ (Fin 2)) '' (ψ '' S) =
        planarProjection '' ((Subtype.val : D → EuclideanSpace ℝ (Fin 3)) '' (φ '' S)) := by
    intro S
    rw [image_image, image_image, image_image, hcomp]
  refine ⟨ψ, ?_⟩
  rw [hDint, hset]

theorem isTopologicalCell_of_planarProjection {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ p ∈ D, p 2 = 0) (h : IsTopologicalCell 2 D) :
    IsTopologicalCell 2 (planarProjection '' D) := by
  rcases h with ⟨φ⟩
  have hcell : IsTopologicalCellWithInterior 2 D
      (Subtype.val '' (φ.symm '' {q | ‖(q : EuclideanSpace ℝ (Fin 2))‖ < 1})) :=
    ⟨φ.symm, rfl⟩
  exact (isTopologicalCellWithInterior_of_planarProjection hhalf hcell).isTopologicalCell

theorem exists_isTopologicalCellWithInterior_union_consecutive_standard (j : Fin 2) :
    ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2
          (standardChainCell j.castSucc ∪ standardChainCell j.succ) Eint ∧
        standardChainCellInterior j.castSucc ⊆ Eint ∧
        standardChainCellInterior j.succ ⊆ Eint := by
  have hcast : ((j.castSucc : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by rw [Fin.val_castSucc]
  have hsucc : ((j.succ : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by
    rw [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have hab : ((j : ℕ) : ℝ) + 3 / 5 ≤ ((j : ℕ) : ℝ) + 1 + 3 / 5 := by linarith
  have ha'b : ((j : ℕ) : ℝ) + 1 + 3 / 5 ≤ ((j : ℕ) : ℝ) + 12 / 5 := by linarith
  have hbb' : ((j : ℕ) : ℝ) + 12 / 5 ≤ ((j : ℕ) : ℝ) + 1 + 12 / 5 := by linarith
  have hrect_union : standardChainRect j.castSucc ∪ standardChainRect j.succ =
      rectTwo (((j : ℕ) : ℝ) + 3 / 5) (((j : ℕ) : ℝ) + 1 + 12 / 5) (-1) 1 := by
    ext x
    rw [standardChainRect, standardChainRect, hcast, hsucc]
    simp only [mem_union, mem_rectTwo]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · refine ⟨⟨h1, h2.trans hbb'⟩, h3⟩
      · refine ⟨⟨hab.trans h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hx : x 0 ≤ ((j : ℕ) : ℝ) + 12 / 5
      · exact Or.inl ⟨⟨h1, hx⟩, h3⟩
      · have hx' : ((j : ℕ) : ℝ) + 12 / 5 < x 0 := lt_of_not_ge hx
        exact Or.inr ⟨⟨ha'b.trans hx'.le, h2⟩, h3⟩
  have hconv : Convex ℝ
      (rectTwo (((j : ℕ) : ℝ) + 3 / 5) (((j : ℕ) : ℝ) + 1 + 12 / 5) (-1) 1) :=
    convex_rectTwo _ _ _ _
  have hcl : IsClosed
      (rectTwo (((j : ℕ) : ℝ) + 3 / 5) (((j : ℕ) : ℝ) + 1 + 12 / 5) (-1) 1) :=
    isClosed_rectTwo _ _ _ _
  have hbnd : Bornology.IsBounded
      (rectTwo (((j : ℕ) : ℝ) + 3 / 5) (((j : ℕ) : ℝ) + 1 + 12 / 5) (-1) 1) :=
    isBounded_rectTwo _ _ _ _
  have hne : (interior
      (rectTwo (((j : ℕ) : ℝ) + 3 / 5) (((j : ℕ) : ℝ) + 1 + 12 / 5) (-1) 1)).Nonempty := by
    refine ⟨EuclideanSpace.single 0 (((j : ℕ) : ℝ) + 1), ?_⟩
    refine single_mem_interior_rectTwo (by linarith) (by linarith) (by norm_num) (by norm_num)
  have hcell := isTopologicalCellWithInterior_planarImage hconv hcl hbnd hne
  have hU_eq : standardChainCell j.castSucc ∪ standardChainCell j.succ =
      planarPoint ''
        rectTwo (((j : ℕ) : ℝ) + 3 / 5) (((j : ℕ) : ℝ) + 1 + 12 / 5) (-1) 1 := by
    rw [standardChainCell, standardChainCell, ← image_union, hrect_union]
  rw [← hU_eq] at hcell
  exact ⟨_, hcell,
    (isPlanarCellChain_standard.cell j.castSucc).interior_mono hcell subset_union_left,
    (isPlanarCellChain_standard.cell j.succ).interior_mono hcell subset_union_right⟩

theorem exists_isTopologicalCellWithInterior_union_consecutive_of_diskUnion
    (hdiskUnion : ∀ {A B : Set (EuclideanSpace ℝ (Fin 2))},
      IsTopologicalCell 2 A → IsTopologicalCell 2 B → IsTopologicalCell 2 (A ∩ B) →
      IsTopologicalCell 2 (A ∪ B))
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)} {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsPlanarCellChain P D Dint) (j : Fin 2) :
    ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint ∧
        Dint j.castSucc ⊆ Eint ∧ Dint j.succ ⊆ Eint := by
  have hhalf0 : ∀ p ∈ D j.castSucc, p 2 = 0 := fun p hp => (hc.halfPlane j.castSucc p hp).1
  have hhalf1 : ∀ p ∈ D j.succ, p 2 = 0 := fun p hp => (hc.halfPlane j.succ p hp).1
  have hcell0 := isTopologicalCellWithInterior_of_planarProjection hhalf0 (hc.cell j.castSucc)
  have hcell1 := isTopologicalCellWithInterior_of_planarProjection hhalf1 (hc.cell j.succ)
  have hA : IsTopologicalCell 2 (planarProjection '' D j.castSucc) := hcell0.isTopologicalCell
  have hB : IsTopologicalCell 2 (planarProjection '' D j.succ) := hcell1.isTopologicalCell
  have hhalf_inter : ∀ p ∈ D j.castSucc ∩ D j.succ, p 2 = 0 :=
    fun p hp => hhalf0 p hp.1
  have hoverlap := isTopologicalCell_of_planarProjection hhalf_inter (hc.overlap j)
  rw [planarProjection_image_inter hhalf0 hhalf1] at hoverlap
  have hunion_proj : IsTopologicalCell 2
      (planarProjection '' D j.castSucc ∪ planarProjection '' D j.succ) :=
    hdiskUnion hA hB hoverlap
  have hcell_union : IsTopologicalCell 2 (D j.castSucc ∪ D j.succ) := by
    have heq : planarPoint ''
        (planarProjection '' D j.castSucc ∪ planarProjection '' D j.succ) =
        D j.castSucc ∪ D j.succ := by
      rw [image_union, planarPoint_image_planarProjection_image hhalf0,
        planarPoint_image_planarProjection_image hhalf1]
    rw [← heq]
    exact isTopologicalCell_planarPoint_image hunion_proj
  rcases hcell_union with ⟨φ⟩
  let Eint := Subtype.val '' (φ.symm '' {q | ‖(q : EuclideanSpace ℝ (Fin 2))‖ < 1})
  have hEcell : IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint :=
    ⟨φ.symm, rfl⟩
  refine ⟨Eint, hEcell, ?_, ?_⟩
  · exact (hc.cell j.castSucc).interior_mono hEcell subset_union_left
  · exact (hc.cell j.succ).interior_mono hEcell subset_union_right

end DifferentialGeometry.Topology.PiecewiseLinear
