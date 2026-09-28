import DifferentialGeometry.Topology.SphereSeparation.SingularSubdivision
import DifferentialGeometry.Topology.SphereSeparation.PermutationDeletion
import Mathlib.Data.Fin.SuccPredOrder

set_option autoImplicit false

open Equiv
open scoped Simplicial

open Convexity.StdSimplex

namespace DifferentialGeometry.Topology.SphereSeparation


def adjacentPositionSwap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 2)) :=
  (Equiv.swap i.castSucc i.succ).trans σ

@[simp]
theorem adjacentPositionSwap_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (j : Fin (n + 2)) :
    adjacentPositionSwap σ i j = σ (Equiv.swap i.castSucc i.succ j) :=
  rfl

theorem adjacent_swap_le_iff_of_ne {n : ℕ}
    (i : Fin (n + 1)) (k a : Fin (n + 2)) (hk : k ≠ i.castSucc) :
    Equiv.swap i.castSucc i.succ a ≤ k ↔ a ≤ k := by
  rw [Equiv.swap_apply_def]
  split_ifs with ha hia
  · subst a
    constructor
    · exact fun h => (Fin.castSucc_le_succ i).trans h
    · intro h
      simpa only [Fin.orderSucc_castSucc] using
        Order.succ_le_of_lt (lt_of_le_of_ne h hk.symm)
  · subst a
    constructor
    · intro h
      simpa only [Fin.orderSucc_castSucc] using
        Order.succ_le_of_lt (lt_of_le_of_ne h hk.symm)
    · exact fun h => (Fin.castSucc_le_succ i).trans h
  · rfl

theorem barycentricPrefix_adjacentPositionSwap_of_ne {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ i.castSucc) :
    barycentricPrefix (adjacentPositionSwap σ i) k =
      barycentricPrefix σ k := by
  ext a
  simp only [mem_barycentricPrefix_iff]
  change Equiv.swap i.castSucc i.succ (σ.symm a) ≤ k ↔ σ.symm a ≤ k
  exact adjacent_swap_le_iff_of_ne i k (σ.symm a) hk

theorem barycentricPrefix_adjacentPositionSwap_succAbove {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i j : Fin (n + 1)) :
    barycentricPrefix (adjacentPositionSwap σ i)
        (i.castSucc.succAbove j) =
      barycentricPrefix σ (i.castSucc.succAbove j) := by
  apply barycentricPrefix_adjacentPositionSwap_of_ne
  exact Fin.succAbove_ne _ _

theorem barycentricPrefix_castSucc_eq_image_eraseLast {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (k : Fin (n + 1)) :
    barycentricPrefix σ k.castSucc =
      (barycentricPrefix (eraseLastPermutation σ) k).image
        (σ (Fin.last (n + 1))).succAbove := by
  classical
  ext a
  rw [mem_barycentricPrefix_iff, Finset.mem_image]
  constructor
  · intro ha
    have hqLast : σ.symm a ≠ Fin.last (n + 1) := by
      exact ne_of_lt (lt_of_le_of_lt ha (Fin.castSucc_lt_last k))
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hqLast
    have hjle : j ≤ k := by
      rw [← hj] at ha
      simpa using ha
    refine ⟨eraseLastPermutation σ j, ?_, ?_⟩
    · rw [mem_barycentricPrefix_iff]
      simpa using hjle
    · rw [succAbove_eraseLastPermutation]
      simpa using congr_arg σ hj
  · rintro ⟨b, hb, rfl⟩
    have heq :
        σ.symm ((σ (Fin.last (n + 1))).succAbove b) =
          ((eraseLastPermutation σ).symm b).castSucc := by
      apply σ.injective
      rw [σ.apply_symm_apply,
        ← succAbove_eraseLastPermutation σ
          ((eraseLastPermutation σ).symm b)]
      simp
    rw [heq]
    simpa using hb


theorem sign_adjacentPositionSwap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    Equiv.Perm.sign (adjacentPositionSwap σ i) =
      -Equiv.Perm.sign σ := by
  rw [adjacentPositionSwap, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_swap]
  · simp
  · exact Fin.castSucc_lt_succ.ne

@[simp]
theorem adjacentPositionSwap_involutive {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    adjacentPositionSwap (adjacentPositionSwap σ i) i = σ := by
  apply Equiv.ext
  intro j
  simp [adjacentPositionSwap]

theorem adjacentPositionSwap_ne {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    adjacentPositionSwap σ i ≠ σ := by
  intro h
  have h' := Equiv.congr_fun h i.castSucc
  simp only [adjacentPositionSwap_apply, Equiv.swap_apply_left] at h'
  exact Fin.castSucc_lt_succ.ne (σ.injective h'.symm)

theorem affineStandardSimplexMap_stdSimplex_map
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (v : β → coordinateSet ℝ γ) (f : α → β)
    (x : coordinateSet ℝ α) :
    affineStandardSimplexMap v (coordinateMap f x) =
      affineStandardSimplexMap (v ∘ f) x := by
  classical
  ext a
  change (∑ j, (coordinateMap f x).val j * (v j).val a) =
    ∑ i, x.val i * (v (f i)).val a
  simp only [coordinateMap_coe,
    FunOnFinite.linearMap_apply_apply]
  calc
    (∑ j, (∑ i ∈ Finset.univ with f i = j, x i) * v j a) =
        ∑ j, ∑ i ∈ Finset.univ with f i = j, x i * v (f i) a := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.1 hi).2]
    _ = ∑ i ∈ Finset.univ, x i * v (f i) a :=
      Finset.sum_fiberwise Finset.univ f (fun i => x i * v (f i) a)
    _ = ∑ i, x i * v (f i) a := by simp

theorem stdSimplex_map_nonemptyFaceBarycenter
    {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (hf : Function.Injective f)
    (A : Finset (Fin (m + 1))) (hA : A.Nonempty) :
    coordinateMap f (nonemptyFaceBarycenter A hA) =
      nonemptyFaceBarycenter (A.image f) (hA.image f) := by
  classical
  ext y
  rw [coordinateMap_coe, FunOnFinite.linearMap_apply_apply]
  have hb (A : Finset (Fin (m + 1))) (hA : A.Nonempty) (z : Fin (m + 1)) :
      (nonemptyFaceBarycenter A hA).val z =
        if z ∈ A then (A.card : ℝ)⁻¹ else 0 := nonemptyFaceBarycenter_apply A hA z
  have hb' (z : Fin (n + 1)) :
      (nonemptyFaceBarycenter (A.image f) (hA.image f)).val z =
        if z ∈ A.image f then ((A.image f).card : ℝ)⁻¹ else 0 :=
    nonemptyFaceBarycenter_apply _ _ z
  simp_rw [hb, hb']
  rw [Finset.card_image_of_injective _ hf]
  by_cases hy : y ∈ A.image f
  · obtain ⟨x, hxA, hxy⟩ := Finset.mem_image.1 hy
    subst y
    rw [ite_eq_left hy]
    have hfiber :
        Finset.univ.filter (fun z : Fin (m + 1) => f z = f x) = {x} := by
      ext z
      simp [hf.eq_iff]
    rw [hfiber]
    simp [hxA]
  · rw [ite_eq_right hy]
    apply Finset.sum_eq_zero
    intro x hx
    rw [ite_eq_right]
    intro hxA
    exact hy (Finset.mem_image.2
      ⟨x, hxA, (Finset.mem_filter.1 hx).2⟩)

theorem stdSimplex_map_affineStandardSimplexMap
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : β → γ) (v : α → coordinateSet ℝ β)
    (x : coordinateSet ℝ α) :
    coordinateMap f (affineStandardSimplexMap v x) =
      affineStandardSimplexMap (fun i => coordinateMap f (v i)) x := by
  classical
  ext y
  change (FunOnFinite.linearMap ℝ ℝ f (affineStandardSimplexMap v x).val) y =
    ∑ i, x.val i * (coordinateMap f (v i)).val y
  rw [FunOnFinite.linearMap_apply_apply]
  have haff (z : β) :
      (affineStandardSimplexMap v x).val z = ∑ i, x.val i * (v i).val z := rfl
  have hmap (i : α) :
      (coordinateMap f (v i)).val y = ∑ z with f z = y, (v i).val z := by
    rw [coordinateMap_coe, FunOnFinite.linearMap_apply_apply]
  simp_rw [haff, hmap]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem barycentricPermutationSimplexMap_finalFace
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (x : coordinateSet ℝ (Fin (n + 1))) :
    barycentricPermutationSimplexMap σ
        (coordinateMap (Fin.last (n + 1)).succAbove x) =
      coordinateMap (σ (Fin.last (n + 1))).succAbove
        (barycentricPermutationSimplexMap
          (eraseLastPermutation σ) x) := by
  unfold barycentricPermutationSimplexMap
  rw [affineStandardSimplexMap_stdSimplex_map,
    stdSimplex_map_affineStandardSimplexMap]
  apply congrArg (fun v : Fin (n + 1) → coordinateSet ℝ (Fin (n + 2)) =>
    affineStandardSimplexMap v x)
  funext k
  dsimp only [Function.comp_apply]
  rw [stdSimplex_map_nonemptyFaceBarycenter _ Fin.succAbove_right_injective]
  simp only [Fin.succAbove_last_apply, barycentricPrefix_castSucc_eq_image_eraseLast]

theorem barycentricPermutationSimplexMap_adjacentPositionSwap_face
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (x : coordinateSet ℝ (Fin (n + 1))) :
    barycentricPermutationSimplexMap (adjacentPositionSwap σ i)
        (coordinateMap i.castSucc.succAbove x) =
      barycentricPermutationSimplexMap σ
        (coordinateMap i.castSucc.succAbove x) := by
  unfold barycentricPermutationSimplexMap
  rw [affineStandardSimplexMap_stdSimplex_map,
    affineStandardSimplexMap_stdSimplex_map]
  apply congrArg (fun v : Fin (n + 1) → coordinateSet ℝ (Fin (n + 2)) =>
    affineStandardSimplexMap v x)
  funext j
  dsimp only [Function.comp_apply]
  simp only [barycentricPrefix_adjacentPositionSwap_succAbove σ i j]

theorem delta_barycentricPiece_adjacentPositionSwap
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    (TopCat.toSSet.obj X).δ i.castSucc
        (barycentricPieceOfSingularSimplex X s
          (adjacentPositionSwap σ i)) =
      (TopCat.toSSet.obj X).δ i.castSucc
        (barycentricPieceOfSingularSimplex X s σ) := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro x
  simp only [TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    ContinuousMap.comp_apply]
  apply congr_arg (X.toSSetObjEquiv _ s)
  apply (coordinateHomeomorph ℝ (Fin (n + 2))).injective
  change barycentricPermutationSimplexMap (adjacentPositionSwap σ i)
      (coordinateEquiv ℝ _ (Convexity.StdSimplex.map i.castSucc.succAbove x)) =
    barycentricPermutationSimplexMap σ
      (coordinateEquiv ℝ _ (Convexity.StdSimplex.map i.castSucc.succAbove x))
  rw [coordinateEquiv_map]
  exact barycentricPermutationSimplexMap_adjacentPositionSwap_face σ i
    (coordinateEquiv ℝ _ x)

end DifferentialGeometry.Topology.SphereSeparation
