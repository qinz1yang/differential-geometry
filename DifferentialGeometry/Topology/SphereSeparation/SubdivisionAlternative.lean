import DifferentialGeometry.Topology.SphereSeparation.SingularSubdivision
import Mathlib.GroupTheory.Perm.Fin

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open Simplicial
open scoped Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem nonemptyFaceBarycenter_eq_of_finset_eq
    {n : ℕ} {A B : Finset (Fin (n + 1))}
    (hA : A.Nonempty) (hB : B.Nonempty) (h : A = B) :
    nonemptyFaceBarycenter A hA = nonemptyFaceBarycenter B hB := by
  subst B
  rfl

private theorem affineStandardSimplexMap_stdSimplexMap
    {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (v : κ → stdSimplex ℝ μ) (f : ι → κ)
    (x : stdSimplex ℝ ι) :
    affineStandardSimplexMap v (stdSimplex.map f x) =
      affineStandardSimplexMap (v ∘ f) x := by
  classical
  apply Subtype.ext
  funext k
  change (∑ j, (stdSimplex.map f x).val j * v j k) =
    ∑ i, x i * v (f i) k
  change (∑ j, (FunOnFinite.linearMap ℝ ℝ f x) j * v j k) = _
  simp only [FunOnFinite.linearMap_apply_apply]
  simp_rw [Finset.sum_mul]
  calc
    (∑ j, ∑ i with f i = j, x i * v j k) =
        ∑ j, ∑ i with f i = j, x i * v (f i) k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    _ = ∑ i, x i * v (f i) k :=
      Finset.sum_fiberwise Finset.univ f (fun i ↦ x i * v (f i) k)

noncomputable def barycentricPermutationFaceMap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  affineStandardSimplexMap fun k ↦
    nonemptyFaceBarycenter (barycentricPrefix σ (j.succAbove k))
      (barycentricPrefix_nonempty σ (j.succAbove k))

private theorem barycentricPermutationSimplexMap_stdSimplexMap_succAbove
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    barycentricPermutationSimplexMap σ (stdSimplex.map j.succAbove x) =
      barycentricPermutationFaceMap σ j x := by
  exact affineStandardSimplexMap_stdSimplexMap _ _ x

noncomputable def barycentricFaceOfSingularSimplex
    (X : TopCat) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj X) _⦋n⦌ :=
  (X.toSSetObjEquiv _).symm
    ((X.toSSetObjEquiv _ s).comp (barycentricPermutationFaceMap σ j))

theorem delta_barycentricPieceOfSingularSimplex
    (X : TopCat) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ j
        (barycentricPieceOfSingularSimplex X s σ) =
      barycentricFaceOfSingularSimplex X s σ j := by
  apply (X.toSSetObjEquiv _).injective
  ext x
  simp only [TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    barycentricFaceOfSingularSimplex, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply]
  rw [barycentricPermutationSimplexMap_stdSimplexMap_succAbove]

private theorem adjacentSwap_le_succAbove_iff {n : ℕ}
    (a k : Fin (n + 1)) (x : Fin (n + 2)) :
    Equiv.swap a.castSucc a.succ x ≤ a.castSucc.succAbove k ↔
      x ≤ a.castSucc.succAbove k := by
  have ht : a.castSucc.succAbove k ≠ a.castSucc :=
    a.castSucc.succAbove_ne k
  have htval : (a.castSucc.succAbove k).val ≠ a.val := by
    intro h
    exact ht (Fin.ext h)
  by_cases hxa : x = a.castSucc
  · subst x
    rw [Equiv.swap_apply_left]
    change a.val + 1 ≤ (a.castSucc.succAbove k).val ↔
      a.val ≤ (a.castSucc.succAbove k).val
    omega
  · by_cases hxs : x = a.succ
    · subst x
      rw [Equiv.swap_apply_right]
      change a.val ≤ (a.castSucc.succAbove k).val ↔
        a.val + 1 ≤ (a.castSucc.succAbove k).val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxs]

private theorem barycentricPrefix_mul_adjacentSwap_succAbove
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (a k : Fin (n + 1)) :
    barycentricPrefix
        (σ * Equiv.swap a.castSucc a.succ)
        (a.castSucc.succAbove k) =
      barycentricPrefix σ (a.castSucc.succAbove k) := by
  classical
  let t := a.castSucc.succAbove k
  have hswap :
      (Finset.Iic t).image (Equiv.swap a.castSucc a.succ) =
        Finset.Iic t := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iic]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (adjacentSwap_le_succAbove_iff a k y).2 hy
    · intro hx
      refine ⟨Equiv.swap a.castSucc a.succ x, ?_, ?_⟩
      · exact (adjacentSwap_le_succAbove_iff a k _).2 hx
      · simp
  change (Finset.Iic t).image
      (σ * Equiv.swap a.castSucc a.succ) =
    (Finset.Iic t).image σ
  rw [Equiv.Perm.coe_mul, ← Finset.image_image, hswap]

private theorem barycentricPermutationFaceMap_mul_adjacentSwap
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (a : Fin (n + 1)) :
    barycentricPermutationFaceMap
        (σ * Equiv.swap a.castSucc a.succ) a.castSucc =
      barycentricPermutationFaceMap σ a.castSucc := by
  apply ContinuousMap.ext
  intro x
  unfold barycentricPermutationFaceMap
  have hv :
      (fun k ↦ nonemptyFaceBarycenter
        (barycentricPrefix
          (σ * Equiv.swap a.castSucc a.succ)
          (a.castSucc.succAbove k))
        (barycentricPrefix_nonempty
          (σ * Equiv.swap a.castSucc a.succ)
          (a.castSucc.succAbove k))) =
      (fun k ↦ nonemptyFaceBarycenter
        (barycentricPrefix σ (a.castSucc.succAbove k))
        (barycentricPrefix_nonempty σ
          (a.castSucc.succAbove k))) := by
    funext k
    apply Subtype.ext
    funext i
    let A := barycentricPrefix
      (σ * Equiv.swap a.castSucc a.succ)
      (a.castSucc.succAbove k)
    let B := barycentricPrefix σ (a.castSucc.succAbove k)
    have hA := nonemptyFaceBarycenter_apply A
      (barycentricPrefix_nonempty
        (σ * Equiv.swap a.castSucc a.succ)
        (a.castSucc.succAbove k)) i
    have hB := nonemptyFaceBarycenter_apply B
      (barycentricPrefix_nonempty σ (a.castSucc.succAbove k)) i
    change (nonemptyFaceBarycenter A _).val i = _ at hA
    change (nonemptyFaceBarycenter B _).val i = _ at hB
    rw [hA, hB]
    have hAB : A = B :=
      barycentricPrefix_mul_adjacentSwap_succAbove σ a k
    rw [hAB]
  rw [hv]

private theorem barycentricFaceOfSingularSimplex_mul_adjacentSwap
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (σ : Equiv.Perm (Fin (n + 2))) (a : Fin (n + 1)) :
    barycentricFaceOfSingularSimplex X s
        (σ * Equiv.swap a.castSucc a.succ) a.castSucc =
      barycentricFaceOfSingularSimplex X s σ a.castSucc := by
  apply (X.toSSetObjEquiv _).injective
  simp only [barycentricFaceOfSingularSimplex, Equiv.apply_symm_apply]
  rw [barycentricPermutationFaceMap_mul_adjacentSwap]

private theorem sign_mul_adjacentSwap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (a : Fin (n + 1)) :
    (Equiv.Perm.sign (σ * Equiv.swap a.castSucc a.succ) : ℤ) =
      -(Equiv.Perm.sign σ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]
  · norm_num
  · exact Fin.ne_of_lt a.castSucc_lt_succ

theorem sum_sign_barycentricFaceOfSingularSimplex_eq_zero
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (a : Fin (n + 1)) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          (TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            (barycentricFaceOfSingularSimplex X s σ a.castSucc) = 0 := by
  classical
  exact Finset.sum_involution
    (fun σ _ ↦ σ * Equiv.swap a.castSucc a.succ)
    (fun σ _ ↦ by
      rw [barycentricFaceOfSingularSimplex_mul_adjacentSwap,
        sign_mul_adjacentSwap]
      simp)
    (fun σ _ _ ↦
      (not_congr Equiv.mul_swap_eq_iff).mpr
        (Fin.ne_of_lt a.castSucc_lt_succ))
    (fun _ _ ↦ Finset.mem_univ _)
    (fun σ _ ↦ Equiv.mul_swap_involutive _ _ σ)



noncomputable def appendLastPerm {n : ℕ}
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) := by
  let f : Fin (n + 2) → Fin (n + 2) :=
    Fin.snoc (fun k ↦ r.succAbove (τ k)) r
  have hf : Function.Injective f := by
    apply Fin.snoc_injective_of_injective
    · exact r.succAbove_right_injective.comp τ.injective
    · rintro ⟨k, hk⟩
      exact r.succAbove_ne (τ k) hk
  exact Equiv.ofBijective f
    ⟨hf, Finite.surjective_of_injective hf⟩

@[simp]
theorem appendLastPerm_apply_castSucc {n : ℕ}
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    appendLastPerm r τ k.castSucc = r.succAbove (τ k) := by
  have hcoe : ⇑(appendLastPerm r τ) =
      Fin.snoc (fun k ↦ r.succAbove (τ k)) r := by
    unfold appendLastPerm
    rfl
  rw [congr_fun hcoe k.castSucc, Fin.snoc_castSucc]

@[simp]
theorem appendLastPerm_apply_last {n : ℕ}
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    appendLastPerm r τ (Fin.last (n + 1)) = r := by
  have hcoe : ⇑(appendLastPerm r τ) =
      Fin.snoc (fun k ↦ r.succAbove (τ k)) r := by
    unfold appendLastPerm
    rfl
  rw [congr_fun hcoe (Fin.last (n + 1)), Fin.snoc_last]

noncomputable def appendLastPermEquiv (n : ℕ) :
    Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ≃
      Equiv.Perm (Fin (n + 2)) := by
  let f : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) →
      Equiv.Perm (Fin (n + 2)) := fun p ↦ appendLastPerm p.1 p.2
  have hf : Function.Injective f := by
    rintro ⟨r, τ⟩ ⟨r', τ'⟩ h
    have hr : r = r' := by
      simpa only [f, appendLastPerm_apply_last] using
        congr_fun
          (congr_arg (fun e : Equiv.Perm (Fin (n + 2)) ↦
            (e : Fin (n + 2) → Fin (n + 2))) h)
          (Fin.last (n + 1))
    subst r'
    have hτ : τ = τ' := by
      apply Equiv.ext
      intro k
      apply r.succAbove_right_injective
      simpa only [f, appendLastPerm_apply_castSucc] using
        congr_fun
          (congr_arg (fun e : Equiv.Perm (Fin (n + 2)) ↦
            (e : Fin (n + 2) → Fin (n + 2))) h) k.castSucc
    exact Prod.ext rfl hτ
  exact Equiv.ofBijective f
    ⟨hf, hf.surjective_of_finite Equiv.Perm.decomposeFin.symm⟩

@[simp]
theorem appendLastPermEquiv_apply (n : ℕ)
    (p : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
    appendLastPermEquiv n p = appendLastPerm p.1 p.2 := by
  unfold appendLastPermEquiv
  rfl

private theorem barycentricPrefix_appendLastPerm_castSucc
    {n : ℕ} (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    barycentricPrefix (appendLastPerm r τ) k.castSucc =
      (barycentricPrefix τ k).image r.succAbove := by
  classical
  unfold barycentricPrefix
  rw [← Fin.finsetImage_castSucc_Iic k]
  simp_rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  simp only [Function.comp_apply, appendLastPerm_apply_castSucc]

private theorem nonemptyFaceBarycenter_image_succAbove
    {n : ℕ} (r : Fin (n + 2))
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty) :
    nonemptyFaceBarycenter (A.image r.succAbove)
        (hA.image r.succAbove) =
      stdSimplex.map r.succAbove (nonemptyFaceBarycenter A hA) := by
  classical
  apply Subtype.ext
  funext i
  change (nonemptyFaceBarycenter (A.image r.succAbove) _).val i =
    (FunOnFinite.linearMap ℝ ℝ r.succAbove
      (nonemptyFaceBarycenter A hA)) i
  have hleft := nonemptyFaceBarycenter_apply
    (A.image r.succAbove) (hA.image r.succAbove) i
  change (nonemptyFaceBarycenter (A.image r.succAbove) _).val i = _ at hleft
  rw [hleft, FunOnFinite.linearMap_apply_apply]
  by_cases hir : i = r
  · subst i
    have hnotmem : r ∉ A.image r.succAbove := by
      intro hr
      rw [Finset.mem_image] at hr
      obtain ⟨k, _, hk⟩ := hr
      exact r.succAbove_ne k hk
    have hfilter :
        Finset.univ.filter (fun k : Fin (n + 1) ↦
          r.succAbove k = r) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      exact r.succAbove_ne k
    rw [if_neg hnotmem, hfilter, Finset.sum_empty]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hir
    have hmem : r.succAbove k ∈ A.image r.succAbove ↔ k ∈ A := by
      simp [Finset.mem_image, r.succAbove_right_injective.eq_iff]
    have hfilter :
        Finset.univ.filter (fun l : Fin (n + 1) ↦
          r.succAbove l = r.succAbove k) = {k} := by
      ext l
      simp [r.succAbove_right_injective.eq_iff]
    rw [hfilter, Finset.sum_singleton,
      Finset.card_image_of_injective _ r.succAbove_right_injective]
    have hright := nonemptyFaceBarycenter_apply A hA k
    change (nonemptyFaceBarycenter A hA).val k = _ at hright
    change (if r.succAbove k ∈ A.image r.succAbove then
      (A.card : ℝ)⁻¹ else 0) =
        (nonemptyFaceBarycenter A hA).val k
    rw [hright]
    simp only [hmem]

private theorem stdSimplexMap_affineStandardSimplexMap
    {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (f : κ → μ) (v : ι → stdSimplex ℝ κ)
    (x : stdSimplex ℝ ι) :
    stdSimplex.map f (affineStandardSimplexMap v x) =
      affineStandardSimplexMap (fun i ↦ stdSimplex.map f (v i)) x := by
  classical
  apply Subtype.ext
  funext l
  change (FunOnFinite.linearMap ℝ ℝ f
      (affineStandardSimplexMap v x)) l =
    ∑ i, x i * (FunOnFinite.linearMap ℝ ℝ f (v i)) l
  simp only [FunOnFinite.linearMap_apply_apply,
    affineStandardSimplexMap_apply]
  change (∑ k ∈ Finset.univ.filter (fun k ↦ f k = l),
      ∑ i, x i * v i k) =
    ∑ i, x i *
      ∑ k ∈ Finset.univ.filter (fun k ↦ f k = l), v i k
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]


noncomputable def standardSimplexFaceMap {n : ℕ} (r : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map r.succAbove, stdSimplex.continuous_map _⟩

private theorem barycentricPermutationFaceMap_appendLastPerm_last
    {n : ℕ} (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    barycentricPermutationFaceMap (appendLastPerm r τ)
        (Fin.last (n + 1)) =
      (standardSimplexFaceMap r).comp
        (barycentricPermutationSimplexMap τ) := by
  apply ContinuousMap.ext
  intro x
  unfold barycentricPermutationFaceMap
  have hv :
      (fun k ↦ nonemptyFaceBarycenter
        (barycentricPrefix (appendLastPerm r τ)
          ((Fin.last (n + 1)).succAbove k))
        (barycentricPrefix_nonempty (appendLastPerm r τ)
          ((Fin.last (n + 1)).succAbove k))) =
      (fun k ↦ stdSimplex.map r.succAbove
        (nonemptyFaceBarycenter (barycentricPrefix τ k)
          (barycentricPrefix_nonempty τ k))) := by
    funext k
    simp only [Fin.succAbove_last_apply]
    calc
      nonemptyFaceBarycenter
          (barycentricPrefix (appendLastPerm r τ) k.castSucc)
          (barycentricPrefix_nonempty (appendLastPerm r τ) k.castSucc) =
        nonemptyFaceBarycenter
          ((barycentricPrefix τ k).image r.succAbove)
          ((barycentricPrefix_nonempty τ k).image r.succAbove) :=
            nonemptyFaceBarycenter_eq_of_finset_eq _ _
              (barycentricPrefix_appendLastPerm_castSucc r τ k)
      _ = stdSimplex.map r.succAbove
          (nonemptyFaceBarycenter (barycentricPrefix τ k)
            (barycentricPrefix_nonempty τ k)) :=
        nonemptyFaceBarycenter_image_succAbove r _ _
  rw [hv]
  exact (stdSimplexMap_affineStandardSimplexMap r.succAbove _ x).symm

private theorem barycentricFaceOfSingularSimplex_appendLastPerm_last
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    barycentricFaceOfSingularSimplex X s (appendLastPerm r τ)
        (Fin.last (n + 1)) =
      barycentricPieceOfSingularSimplex X
        ((TopCat.toSSet.obj X).δ r s) τ := by
  apply (X.toSSetObjEquiv _).injective
  ext x
  simp only [barycentricFaceOfSingularSimplex, Equiv.apply_symm_apply,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    TopCat.toSSetObjEquiv_δ_apply, ContinuousMap.comp_apply]
  rw [barycentricPermutationFaceMap_appendLastPerm_last]
  rfl

private theorem appendLastPerm_eq_cycleIcc_mul_extendDomain
    {n : ℕ} (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    appendLastPerm r τ =
      Fin.cycleIcc r (Fin.last (n + 1)) *
        τ.extendDomain
          (finSuccAboveEquiv (Fin.last (n + 1))) := by
  ext k
  induction k using Fin.lastCases with
  | last =>
      rw [appendLastPerm_apply_last, Equiv.Perm.mul_apply]
      rw [Equiv.Perm.extendDomain_apply_not_subtype]
      · exact congr_arg Fin.val
          (Fin.cycleIcc_of_last (i := r) (j := Fin.last (n + 1))
            (Fin.le_last _)).symm
      · simp
  | cast k =>
      rw [appendLastPerm_apply_castSucc, Equiv.Perm.mul_apply]
      have hext := Equiv.Perm.extendDomain_apply_image τ
        (finSuccAboveEquiv (Fin.last (n + 1))) k
      simp only [finSuccAboveEquiv_apply, Fin.succAbove_last_apply] at hext
      rw [hext]
      exact congr_arg Fin.val
        (by simpa only [Function.comp_apply, Fin.succAbove_last_apply]
          using (congr_fun
            (Fin.cycleIcc_comp_succAbove r (Fin.last (n + 1))
              (Fin.le_last _)) (τ k)).symm)

private theorem sign_appendLastPerm {n : ℕ}
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm.sign (appendLastPerm r τ) =
      (-1) ^ ((n + 1) - r.val) * Equiv.Perm.sign τ := by
  rw [appendLastPerm_eq_cycleIcc_mul_extendDomain,
    Equiv.Perm.sign_mul, Fin.sign_cycleIcc_of_le (Fin.le_last _),
    Equiv.Perm.sign_extendDomain]
  rfl

private theorem int_sign_appendLastPerm {n : ℕ}
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (appendLastPerm r τ) : ℤ) =
      (-1 : ℤ) ^ ((n + 1) - r.val) *
        (Equiv.Perm.sign τ : ℤ) := by
  have h := congr_arg (fun z : ℤˣ ↦ (z : ℤ))
    (sign_appendLastPerm r τ)
  simpa using h

private theorem int_sign_appendLastPerm_mul_boundarySign
    {n : ℕ} (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (appendLastPerm r τ) : ℤ) *
        (-1 : ℤ) ^ (n + 1) =
      (-1 : ℤ) ^ r.val * (Equiv.Perm.sign τ : ℤ) := by
  rw [int_sign_appendLastPerm]
  have hr : r.val ≤ n + 1 := Nat.le_of_lt_succ r.isLt
  have hexp : (n + 1 - r.val) + (n + 1) =
      2 * (n + 1 - r.val) + r.val := by omega
  have hpows :
      (-1 : ℤ) ^ (n + 1 - r.val) * (-1 : ℤ) ^ (n + 1) =
        (-1 : ℤ) ^ r.val := by
    rw [← pow_add, hexp, pow_add, pow_mul]
    norm_num
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    congr_arg (fun z : ℤ ↦ z * (Equiv.Perm.sign τ : ℤ)) hpows

theorem sum_sign_boundarySign_barycentricFace_last
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          ((-1 : ℤ) ^ (n + 1) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              (barycentricFaceOfSingularSimplex X s σ
                (Fin.last (n + 1)))) =
      ∑ r : Fin (n + 2),
        (-1 : ℤ) ^ r.val •
          ∑ τ : Equiv.Perm (Fin (n + 1)),
            (Equiv.Perm.sign τ : ℤ) •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                (barycentricPieceOfSingularSimplex X
                  ((TopCat.toSSet.obj X).δ r s) τ) := by
  classical
  rw [← Equiv.sum_comp (appendLastPermEquiv n), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [appendLastPermEquiv_apply,
    barycentricFaceOfSingularSimplex_appendLastPerm_last]
  rw [smul_smul, smul_smul]
  exact congr_arg (fun z : ℤ ↦ z •
      (TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        (barycentricPieceOfSingularSimplex X
          ((TopCat.toSSet.obj X).δ r s) τ))
    (int_sign_appendLastPerm_mul_boundarySign r τ)

theorem sum_sign_boundary_barycentricPiece
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          ∑ j : Fin (n + 2),
            (-1 : ℤ) ^ j.val •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj X).δ j
                  (barycentricPieceOfSingularSimplex X s σ)) =
      ∑ r : Fin (n + 2),
        (-1 : ℤ) ^ r.val •
          ∑ τ : Equiv.Perm (Fin (n + 1)),
            (Equiv.Perm.sign τ : ℤ) •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                (barycentricPieceOfSingularSimplex X
                  ((TopCat.toSSet.obj X).δ r s) τ) := by
  classical
  simp_rw [delta_barycentricPieceOfSingularSimplex]
  have hsplit (σ : Equiv.Perm (Fin (n + 2))) :
      (∑ j : Fin (n + 2),
          (-1 : ℤ) ^ j.val •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              (barycentricFaceOfSingularSimplex X s σ j)) =
        (∑ a : Fin (n + 1),
          (-1 : ℤ) ^ a.castSucc.val •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              (barycentricFaceOfSingularSimplex X s σ a.castSucc)) +
          (-1 : ℤ) ^ (Fin.last (n + 1)).val •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              (barycentricFaceOfSingularSimplex X s σ
                (Fin.last (n + 1))) := by
    exact Fin.sum_univ_castSucc _
  simp_rw [hsplit, smul_add]
  rw [Finset.sum_add_distrib]
  have hinter :
      ∑ σ : Equiv.Perm (Fin (n + 2)),
          (Equiv.Perm.sign σ : ℤ) •
            ∑ a : Fin (n + 1),
              (-1 : ℤ) ^ a.castSucc.val •
                (TopCat.toSSet.obj X).ιChainComplex
                  (R := ModuleCat.of ℤ ℤ)
                  (barycentricFaceOfSingularSimplex X s σ a.castSucc) = 0 := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    calc
      (∑ σ : Equiv.Perm (Fin (n + 2)),
          (Equiv.Perm.sign σ : ℤ) •
            ((-1 : ℤ) ^ a.castSucc.val •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                (barycentricFaceOfSingularSimplex X s σ a.castSucc))) =
          (-1 : ℤ) ^ a.castSucc.val •
            ∑ σ : Equiv.Perm (Fin (n + 2)),
              (Equiv.Perm.sign σ : ℤ) •
                (TopCat.toSSet.obj X).ιChainComplex
                  (R := ModuleCat.of ℤ ℤ)
                  (barycentricFaceOfSingularSimplex X s σ a.castSucc) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro σ _
            simp only [smul_smul]
            rw [mul_comm]
      _ = 0 := by
        rw [sum_sign_barycentricFaceOfSingularSimplex_eq_zero]
        simp
  rw [hinter, zero_add]
  exact sum_sign_boundarySign_barycentricFace_last X s

theorem barycentricSubdivisionBoundaryCompatible_all (X : TopCat) :
    BarycentricSubdivisionBoundaryCompatible X := by
  intro n
  change barycentricSubdivisionDegreeMap X (n + 1) ≫
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n =
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
      barycentricSubdivisionDegreeMap X n
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc, ιChainComplex_barycentricSubdivisionDegreeMap,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ιChainComplex_d]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    ιChainComplex_barycentricSubdivisionDegreeMap]
  exact sum_sign_boundary_barycentricPiece X s

private theorem barycentricPermutationSimplexMap_refl_vertex_zero :
    barycentricPermutationSimplexMap (Equiv.refl (Fin 2))
        (stdSimplex.vertex 0) =
      stdSimplex.vertex 0 := by
  rw [barycentricPermutationSimplexMap_vertex]
  apply Subtype.ext
  funext i
  have hvalue := nonemptyFaceBarycenter_apply
    (barycentricPrefix (Equiv.refl (Fin 2)) 0)
    (barycentricPrefix_nonempty (Equiv.refl (Fin 2)) 0) i
  change (nonemptyFaceBarycenter
    (barycentricPrefix (Equiv.refl (Fin 2)) 0) _).val i = _ at hvalue
  rw [hvalue]
  fin_cases i <;> simp [barycentricPrefix]

private theorem barycentricPermutationSimplexMap_swap_vertex_zero :
    barycentricPermutationSimplexMap (Equiv.swap (0 : Fin 2) 1)
        (stdSimplex.vertex 0) =
      stdSimplex.vertex 1 := by
  rw [barycentricPermutationSimplexMap_vertex]
  apply Subtype.ext
  funext i
  have hvalue := nonemptyFaceBarycenter_apply
    (barycentricPrefix (Equiv.swap (0 : Fin 2) 1) 0)
    (barycentricPrefix_nonempty (Equiv.swap (0 : Fin 2) 1) 0) i
  change (nonemptyFaceBarycenter
    (barycentricPrefix (Equiv.swap (0 : Fin 2) 1) 0) _).val i = _ at hvalue
  rw [hvalue]
  fin_cases i
  · simp [barycentricPrefix]
  · rw [barycentricPrefix,
      Finset.card_image_of_injective _ (Equiv.swap (0 : Fin 2) 1).injective]
    simp

private theorem barycentricPermutationSimplexMap_vertex_one_eq
    (σ : Equiv.Perm (Fin 2)) :
    barycentricPermutationSimplexMap σ (stdSimplex.vertex 1) =
      nonemptyFaceBarycenter Finset.univ Finset.univ_nonempty := by
  rw [barycentricPermutationSimplexMap_vertex]
  simp only [show (1 : Fin 2) = Fin.last 1 by rfl,
    barycentricPrefix_last]

private theorem delta_zero_barycentricPiece_one_refl_eq_swap
    (X : TopCat) (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).δ 0
        (barycentricPieceOfSingularSimplex X s (Equiv.refl (Fin 2))) =
      (TopCat.toSSet.obj X).δ 0
        (barycentricPieceOfSingularSimplex X s (Equiv.swap 0 1)) := by
  apply (X.toSSetObjEquiv _).injective
  ext x
  simp only [TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    ContinuousMap.comp_apply]
  rw [Subsingleton.elim x (stdSimplex.vertex 0), stdSimplex.map_vertex]
  simp only [Fin.zero_succAbove]
  rw [show Fin.succ (0 : Fin 1) = (1 : Fin 2) by rfl]
  rw [barycentricPermutationSimplexMap_vertex_one_eq,
    barycentricPermutationSimplexMap_vertex_one_eq]

private theorem delta_one_barycentricPiece_one_refl
    (X : TopCat) (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).δ 1
        (barycentricPieceOfSingularSimplex X s (Equiv.refl (Fin 2))) =
      (TopCat.toSSet.obj X).δ 1 s := by
  apply (X.toSSetObjEquiv _).injective
  ext x
  simp only [TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    ContinuousMap.comp_apply]
  rw [Subsingleton.elim x (stdSimplex.vertex 0), stdSimplex.map_vertex]
  simp only [Fin.one_succAbove_zero]
  rw [barycentricPermutationSimplexMap_refl_vertex_zero]

private theorem delta_one_barycentricPiece_one_swap
    (X : TopCat) (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).δ 1
        (barycentricPieceOfSingularSimplex X s (Equiv.swap 0 1)) =
      (TopCat.toSSet.obj X).δ 0 s := by
  apply (X.toSSetObjEquiv _).injective
  ext x
  simp only [TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    ContinuousMap.comp_apply]
  rw [Subsingleton.elim x (stdSimplex.vertex 0), stdSimplex.map_vertex,
    stdSimplex.map_vertex]
  simp only [Fin.one_succAbove_zero, Fin.zero_succAbove]
  rw [show Fin.succ (0 : Fin 1) = (1 : Fin 2) by rfl]
  rw [barycentricPermutationSimplexMap_swap_vertex_zero]

theorem barycentricSubdivisionDegreeMap_boundary_zero (X : TopCat) :
    barycentricSubdivisionDegreeMap X 1 ≫
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj X).d 1 0 =
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj X).d 1 0 ≫
        barycentricSubdivisionDegreeMap X 0 := by
  change barycentricSubdivisionDegreeMap X 1 ≫
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 =
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫
      barycentricSubdivisionDegreeMap X 0
  rw [barycentricSubdivisionDegreeMap_zero, Category.comp_id]
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc, ιChainComplex_barycentricSubdivisionDegreeMap,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ιChainComplex_d]
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
  rw [Fintype.sum_prod_type]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finset.univ_unique,
    Equiv.Perm.default_eq, Equiv.Perm.decomposeFin.symm_sign, Fin.isValue,
    ite_mul, one_mul, neg_mul, Int.reduceNeg, Fin.sum_univ_two,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_smul, Nat.mod_succ,
    pow_one, neg_smul, smul_add, smul_neg, Finset.sum_singleton,
    Equiv.Perm.sign_one, Equiv.Perm.decomposeFin_symm_of_one, ↓reduceIte,
    Units.val_one, Equiv.swap_self, one_ne_zero, Units.val_neg, neg_neg]
  rw [delta_zero_barycentricPiece_one_refl_eq_swap,
    delta_one_barycentricPiece_one_refl,
    delta_one_barycentricPiece_one_swap]
  abel

end DifferentialGeometry.Topology.SphereSeparation
