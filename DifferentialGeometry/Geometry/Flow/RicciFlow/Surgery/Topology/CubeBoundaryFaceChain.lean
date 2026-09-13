import DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology unitInterval Simplicial

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

abbrev cube3 : Type := Fin 3 → unitInterval

private def cubeFace (k : Fin 4) : C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 4)) :=
  ⟨stdSimplex.map (SimplexCategory.δ k).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ k).toOrderHom⟩

private theorem cubeFace_self (k : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    cubeFace k q k = 0 := by
  change FunOnFinite.linearMap ℝ ℝ k.succAbove (q : Fin 3 → ℝ) k = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne k j (Finset.mem_filter.mp hj).2)

private theorem cubeFace_succAbove (k : Fin 4) (q : stdSimplex ℝ (Fin 3)) (j : Fin 3) :
    cubeFace k q (k.succAbove j) = q j := by
  change FunOnFinite.linearMap ℝ ℝ k.succAbove (q : Fin 3 → ℝ) (k.succAbove j) = q j
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

private theorem staircaseCoordinate_face (e : Equiv.Perm (Fin 3)) (k : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) (i : Fin 3) :
    staircaseCoordinate e (cubeFace k q) i =
      ∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then q j else 0 := by
  unfold staircaseCoordinate
  rw [Fin.sum_univ_succAbove _ k]
  have hz : (if (e.symm i).val < k.val then (cubeFace k q).val k else 0) = 0 := by
    split_ifs
    · exact cubeFace_self k q
    · rfl
  have hsum :
      (∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then
        (cubeFace k q).val (k.succAbove j) else 0) =
      ∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then q.val j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact cubeFace_succAbove k q j
    · rfl
  exact (congrArg₂ (fun a b : ℝ => a + b) hz hsum).trans (zero_add _)

private theorem staircase_face_zero (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) : staircaseSimplex e (cubeFace 0 q) (e 0) = 1 := by
  apply Subtype.ext
  change staircaseCoordinate e (cubeFace 0 q) (e 0) = 1
  rw [staircaseCoordinate_face]
  simp [Fin.succAbove]

private theorem staircase_face_three (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) : staircaseSimplex e (cubeFace 3 q) (e 2) = 0 := by
  apply Subtype.ext
  change staircaseCoordinate e (cubeFace 3 q) (e 2) = 0
  rw [staircaseCoordinate_face]
  simp [Fin.sum_univ_succ, Fin.succAbove]

private theorem staircase_face_one_swap (e : Equiv.Perm (Fin 3)) :
    (staircaseSimplex e).comp (cubeFace 1) =
      (staircaseSimplex ((Equiv.swap 0 1).trans e)).comp (cubeFace 1) := by
  ext q i
  obtain ⟨k, rfl⟩ := e.surjective i
  change staircaseCoordinate e (cubeFace 1 q) (e k) =
    staircaseCoordinate ((Equiv.swap 0 1).trans e) (cubeFace 1 q) (e k)
  rw [staircaseCoordinate_face, staircaseCoordinate_face]
  fin_cases k <;> simp [Fin.sum_univ_succ, Equiv.swap_apply_def, Fin.succAbove]

private theorem staircase_face_two_swap (e : Equiv.Perm (Fin 3)) :
    (staircaseSimplex e).comp (cubeFace 2) =
      (staircaseSimplex ((Equiv.swap 1 2).trans e)).comp (cubeFace 2) := by
  ext q i
  obtain ⟨k, rfl⟩ := e.surjective i
  change staircaseCoordinate e (cubeFace 2 q) (e k) =
    staircaseCoordinate ((Equiv.swap 1 2).trans e) (cubeFace 2 q) (e k)
  rw [staircaseCoordinate_face, staircaseCoordinate_face]
  fin_cases k <;> simp [Fin.sum_univ_succ, Equiv.swap_apply_def, Fin.succAbove]

def cubeChain : integralCoefficients ⟶ (IntegralChains cube3).X 3 :=
  ∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) • singularSimplexChain (staircaseSimplex e)

def cubeTopFaceChain (i : Fin 3) : integralCoefficients ⟶ (IntegralChains cube3).X 2 :=
  ∑ e : Equiv.Perm (Fin 3), if e 0 = i then
    ((e.sign : ℤˣ) : ℤ) • singularSimplexChain ((staircaseSimplex e).comp (cubeFace 0)) else 0

def cubeBottomFaceChain (i : Fin 3) : integralCoefficients ⟶ (IntegralChains cube3).X 2 :=
  ∑ e : Equiv.Perm (Fin 3), if e 2 = i then
    ((e.sign : ℤˣ) : ℤ) • singularSimplexChain ((staircaseSimplex e).comp (cubeFace 3)) else 0

theorem card_topFace_permutations (i : Fin 3) :
    Fintype.card {e : Equiv.Perm (Fin 3) // e 0 = i} = 2 := by
  fin_cases i <;> decide

theorem card_bottomFace_permutations (i : Fin 3) :
    Fintype.card {e : Equiv.Perm (Fin 3) // e 2 = i} = 2 := by
  fin_cases i <;> decide

private theorem nativeCubeTetrahedronBoundary (s : C(stdSimplex ℝ (Fin 4), cube3)) :
    singularSimplexChain s ≫ (IntegralChains cube3).d 3 2 =
      ∑ k : Fin 4, (-1 : ℤ) ^ k.val • singularSimplexChain (s.comp (cubeFace k)) :=
  (TopCat.toSSet.obj (TopCat.of cube3)).ιChainComplex_d
    (R := integralCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of cube3) (.op ⦋3⦌)).symm s)

private theorem cubeChain_tetrahedron_boundary (e : Equiv.Perm (Fin 3)) :
    singularSimplexChain (staircaseSimplex e) ≫ (IntegralChains cube3).d 3 2 =
      singularSimplexChain ((staircaseSimplex e).comp (cubeFace 0)) -
        singularSimplexChain ((staircaseSimplex e).comp (cubeFace 1)) +
        singularSimplexChain ((staircaseSimplex e).comp (cubeFace 2)) -
        singularSimplexChain ((staircaseSimplex e).comp (cubeFace 3)) := by
  rw [nativeCubeTetrahedronBoundary]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, one_smul, add_zero]
  norm_num
  abel

private theorem signed_swap_pairing {A : Type*} [AddCommGroup A] (F : Equiv.Perm (Fin 3) → A)
    (i j : Fin 3) (hij : i ≠ j) (hF : ∀ e, F ((Equiv.swap i j).trans e) = F e) :
    (∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) • F e) = 0 := by
  classical
  apply Finset.sum_ninvolution (fun e => (Equiv.swap i j).trans e)
  · intro e
    rw [hF]
    simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hij]
  · intro e _ he
    have h := congrArg (fun p : Equiv.Perm (Fin 3) => p i) he
    have hji : j = i := e.injective (by simpa using h)
    exact hij hji.symm
  · intro e
    exact Finset.mem_univ _
  · intro e
    ext k
    exact congrArg (fun z => (e z).val) (Equiv.swap_apply_self i j k)

theorem cubeChain_boundary :
    cubeChain ≫ (IntegralChains cube3).d 3 2 =
      ∑ i : Fin 3, (cubeTopFaceChain i - cubeBottomFaceChain i) := by
  classical
  have h₁ := signed_swap_pairing (fun e : Equiv.Perm (Fin 3) =>
    singularSimplexChain ((staircaseSimplex e).comp (cubeFace 1))) 0 1 (by decide)
    (fun e => by rw [← staircase_face_one_swap e])
  have h₂ := signed_swap_pairing (fun e : Equiv.Perm (Fin 3) =>
    singularSimplexChain ((staircaseSimplex e).comp (cubeFace 2))) 1 2 (by decide)
    (fun e => by rw [← staircase_face_two_swap e])
  have htop : (∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
      singularSimplexChain ((staircaseSimplex e).comp (cubeFace 0))) =
      ∑ i : Fin 3, cubeTopFaceChain i := by
    simp only [cubeTopFaceChain]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hbot : (∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
      singularSimplexChain ((staircaseSimplex e).comp (cubeFace 3))) =
      ∑ i : Fin 3, cubeBottomFaceChain i := by
    simp only [cubeBottomFaceChain]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  unfold cubeChain
  simp only [Preadditive.sum_comp, Linear.smul_comp, cubeChain_tetrahedron_boundary,
    smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h₁, h₂, htop, hbot]
  abel

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem moduleCat_sum_apply {ι : Type*} {M N : ModuleCat ℤ} (s : Finset ι)
    (f : ι → (M ⟶ N)) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

private theorem moduleCat_sum_sub_apply {ι : Type*} {M N : ModuleCat ℤ} (s : Finset ι)
    (f g : ι → (M ⟶ N)) (x : M) :
    (∑ i ∈ s, (f i - g i)) x = ∑ i ∈ s, (f i x - g i x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

abbrev cubeTetrahedralChain : (integralSingularChains (Fin 3 → unitInterval)).X 3 :=
  cubeChain (ULift.up (1 : ℤ) : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)

abbrev cubeTopFaceElement (i : Fin 3) : (integralSingularChains (Fin 3 → unitInterval)).X 2 :=
  cubeTopFaceChain i (ULift.up (1 : ℤ) : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)

abbrev cubeBottomFaceElement (i : Fin 3) : (integralSingularChains (Fin 3 → unitInterval)).X 2 :=
  cubeBottomFaceChain i (ULift.up (1 : ℤ) : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)

theorem cubeTopFaceMap_mem_boundary (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) :
    staircaseSimplex e (cubeFace 0 q) ∈ Cube.boundary (Fin 3) :=
  ⟨e 0, Or.inr (staircase_face_zero e q)⟩

theorem cubeBottomFaceMap_mem_boundary (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) :
    staircaseSimplex e (cubeFace 3 q) ∈ Cube.boundary (Fin 3) :=
  ⟨e 2, Or.inl (staircase_face_three e q)⟩

theorem cubeTetrahedralChain_boundary :
    (integralSingularChains (Fin 3 → unitInterval)).d 3 2 cubeTetrahedralChain =
      ∑ i : Fin 3, (cubeTopFaceElement i - cubeBottomFaceElement i) := by
  have h := congrArg (fun k => k (ULift.up (1 : ℤ) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)) cubeChain_boundary
  have h' : (integralSingularChains (Fin 3 → unitInterval)).d 3 2 cubeTetrahedralChain =
      (∑ i : Fin 3, (cubeTopFaceChain i - cubeBottomFaceChain i)) (ULift.up (1 : ℤ) :
        DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients) := h
  erw [moduleCat_sum_sub_apply Finset.univ] at h'
  exact h'

end DifferentialGeometry.Topology
