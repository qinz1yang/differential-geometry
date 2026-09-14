import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Topology unitInterval Simplicial Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def staircaseCoordinate (sigma : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 4)) (i : Fin 3) : ℝ :=
  ∑ j : Fin 4, if (sigma.symm i).val < j.val then q.val j else 0

theorem staircaseCoordinate_mem (sigma : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 4)) (i : Fin 3) :
    staircaseCoordinate sigma q i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact q.property.1 j
    · exact le_rfl
  · calc
      staircaseCoordinate sigma q i ≤ ∑ j : Fin 4, q.val j := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact le_rfl
        · exact q.property.1 j
      _ = 1 := q.property.2


def staircaseSimplex (sigma : Equiv.Perm (Fin 3)) :
    C(stdSimplex ℝ (Fin 4), I^(Fin 3)) where
  toFun q i := ⟨staircaseCoordinate sigma q i, staircaseCoordinate_mem sigma q i⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    unfold staircaseCoordinate
    apply continuous_finsetSum
    intro j _
    split_ifs
    · exact (continuous_apply j).comp continuous_subtype_val
    · exact continuous_const

variable {X : Type u} [TopologicalSpace X] {x : X}

variable {Y : Type u} [TopologicalSpace Y]


def genLoopPostcompose {N : Type*} (f : C(X, Y)) (c : GenLoop N X x) :
    GenLoop N Y (f x) :=
  ⟨f.comp c.val, fun z hz => by simp only [ContinuousMap.comp_apply, c.property z hz]⟩


def basedHomotopyMap {N : Type*} (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (genLoopPostcompose f) (fun _ _ h => h.comp_continuousMap f)

@[simp] theorem basedHomotopyMap_mk {N : Type*} (f : C(X, Y))
    (c : GenLoop N X x) :
    basedHomotopyMap f x (Quotient.mk _ c) = Quotient.mk _ (genLoopPostcompose f c) := rfl


theorem genLoopPostcompose_transAt {N : Type*} [DecidableEq N] (i : N)
    (f : C(X, Y)) (c d : GenLoop N X x) :
    genLoopPostcompose f (GenLoop.transAt i c d) =
      GenLoop.transAt i (genLoopPostcompose f c) (genLoopPostcompose f d) := by
  ext z
  change f (GenLoop.transAt i c d z) =
    GenLoop.transAt i (genLoopPostcompose f c) (genLoopPostcompose f d) z
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl


def basedHomotopyHom {N : Type*} [DecidableEq N] [Nonempty N] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x →* HomotopyGroup N Y (f x) where
  toFun := basedHomotopyMap f x
  map_one' := rfl
  map_mul' := by
    classical
    intro c d
    induction c using Quotient.inductionOn with | h c =>
      induction d using Quotient.inductionOn with | h d =>
        simp only [HomotopyGroup.mul_spec (i := Classical.arbitrary N), basedHomotopyMap_mk]
        rw [genLoopPostcompose_transAt]

def hurewiczCubeChain (c : GenLoop (Fin 3) X x) :
    integralCoefficients ⟶ (IntegralChains X).X 3 :=
  ∑ sigma : Equiv.Perm (Fin 3), ((sigma.sign : ℤˣ) : ℤ) •
    singularSimplexChain (c.val.comp (staircaseSimplex sigma))

private theorem nativeSimplex_chain_map (f : C(X, Y)) {n : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    singularSimplexChain s ≫ (integralChainsFunctor.map (TopCat.ofHom f)).f n =
      singularSimplexChain (f.comp s) := by
  exact SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom f))
    integralCoefficients ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm s)


theorem hurewiczCubeChain_natural (f : C(X, Y)) (c : GenLoop (Fin 3) X x) :
    hurewiczCubeChain c ≫ (integralChainsFunctor.map (TopCat.ofHom f)).f 3 =
      hurewiczCubeChain (genLoopPostcompose f c) := by
  classical
  simp only [hurewiczCubeChain, Preadditive.sum_comp, Linear.smul_comp,
    nativeSimplex_chain_map]
  rfl

private theorem permutation_sign_sum_zero :
    (∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ)) = 0 := by
  classical
  have h := Equiv.sum_comp (Equiv.mulLeft (Equiv.swap (0 : Fin 3) 1))
    (fun e : Equiv.Perm (Fin 3) => ((e.sign : ℤˣ) : ℤ))
  simp only [Equiv.coe_mulLeft, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 by decide),
    Units.val_neg, neg_one_mul, Finset.sum_neg_distrib] at h
  omega


theorem hurewiczCubeChain_const (x : X) :
    hurewiczCubeChain (GenLoop.const : GenLoop (Fin 3) X x) = 0 := by
  classical
  have hs : ∀ e : Equiv.Perm (Fin 3),
      (GenLoop.const : GenLoop (Fin 3) X x).val.comp (staircaseSimplex e) =
        ContinuousMap.const (stdSimplex ℝ (Fin 4)) x := by
    intro e
    rfl
  simp only [hurewiczCubeChain, hs, ← Finset.sum_smul, permutation_sign_sum_zero, zero_smul]

private def staircaseFace (k : Fin 4) :
    C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 4)) :=
  ⟨stdSimplex.map (SimplexCategory.δ k).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ k).toOrderHom⟩

private theorem staircaseFace_self (k : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    staircaseFace k q k = 0 := by
  change FunOnFinite.linearMap ℝ ℝ k.succAbove (q : Fin 3 → ℝ) k = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne k j (Finset.mem_filter.mp hj).2)

private theorem staircaseFace_succAbove (k : Fin 4) (q : stdSimplex ℝ (Fin 3)) (j : Fin 3) :
    staircaseFace k q (k.succAbove j) = q j := by
  change FunOnFinite.linearMap ℝ ℝ k.succAbove (q : Fin 3 → ℝ) (k.succAbove j) = q j
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

private theorem staircase_face_coordinate (e : Equiv.Perm (Fin 3)) (k : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) (i : Fin 3) :
    staircaseCoordinate e (staircaseFace k q) i =
      ∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then q j else 0 := by
  unfold staircaseCoordinate
  rw [Fin.sum_univ_succAbove _ k]
  have hz : (if (e.symm i).val < k.val then (staircaseFace k q).val k else 0) = 0 := by
    split_ifs
    · exact staircaseFace_self k q
    · rfl
  have hsum :
      (∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then
        (staircaseFace k q).val (k.succAbove j) else 0) =
      ∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then q.val j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact staircaseFace_succAbove k q j
    · rfl
  exact (congrArg₂ (fun a b : ℝ => a + b) hz hsum).trans (zero_add _)

private theorem staircase_face_zero (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) : staircaseSimplex e (staircaseFace 0 q) (e 0) = 1 := by
  apply Subtype.ext
  change staircaseCoordinate e (staircaseFace 0 q) (e 0) = 1
  rw [staircase_face_coordinate]
  simp [Fin.succAbove]

private theorem staircase_face_three (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) : staircaseSimplex e (staircaseFace 3 q) (e 2) = 0 := by
  apply Subtype.ext
  change staircaseCoordinate e (staircaseFace 3 q) (e 2) = 0
  rw [staircase_face_coordinate]
  simp [Fin.sum_univ_succ, Fin.succAbove]

private theorem staircase_face_one_swap (e : Equiv.Perm (Fin 3)) :
    (staircaseSimplex e).comp (staircaseFace 1) =
      (staircaseSimplex ((Equiv.swap 0 1).trans e)).comp (staircaseFace 1) := by
  ext q i
  obtain ⟨k, rfl⟩ := e.surjective i
  change staircaseCoordinate e (staircaseFace 1 q) (e k) =
    staircaseCoordinate ((Equiv.swap 0 1).trans e) (staircaseFace 1 q) (e k)
  rw [staircase_face_coordinate, staircase_face_coordinate]
  fin_cases k <;> simp [Fin.sum_univ_succ, Equiv.swap_apply_def, Fin.succAbove]

private theorem staircase_face_two_swap (e : Equiv.Perm (Fin 3)) :
    (staircaseSimplex e).comp (staircaseFace 2) =
      (staircaseSimplex ((Equiv.swap 1 2).trans e)).comp (staircaseFace 2) := by
  ext q i
  obtain ⟨k, rfl⟩ := e.surjective i
  change staircaseCoordinate e (staircaseFace 2 q) (e k) =
    staircaseCoordinate ((Equiv.swap 1 2).trans e) (staircaseFace 2 q) (e k)
  rw [staircase_face_coordinate, staircase_face_coordinate]
  fin_cases k <;> simp [Fin.sum_univ_succ, Equiv.swap_apply_def, Fin.succAbove]

private theorem native_tetrahedron_boundary
    (s : C(stdSimplex ℝ (Fin 4), X)) :
    singularSimplexChain s ≫ (IntegralChains X).d 3 2 =
      ∑ k : Fin 4, (-1 : ℤ) ^ k.val • singularSimplexChain (s.comp (staircaseFace k)) := by
  exact (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
    (R := integralCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋3⦌)).symm s)

private theorem mapped_staircase_boundary (c : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) :
    singularSimplexChain (c.val.comp (staircaseSimplex e)) ≫ (IntegralChains X).d 3 2 =
      -singularSimplexChain (c.val.comp ((staircaseSimplex e).comp (staircaseFace 1))) +
        singularSimplexChain (c.val.comp ((staircaseSimplex e).comp (staircaseFace 2))) := by
  have hzero : (c.val.comp (staircaseSimplex e)).comp (staircaseFace 0) =
      ContinuousMap.const (stdSimplex ℝ (Fin 3)) x := by
    ext q
    exact c.property _ ⟨e 0, Or.inr (staircase_face_zero e q)⟩
  have hthree : (c.val.comp (staircaseSimplex e)).comp (staircaseFace 3) =
      ContinuousMap.const (stdSimplex ℝ (Fin 3)) x := by
    ext q
    exact c.property _ ⟨e 2, Or.inl (staircase_face_three e q)⟩
  rw [native_tetrahedron_boundary]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, one_smul, add_zero]
  norm_num
  simp only [ContinuousMap.comp_assoc] at hzero hthree
  have hthree' : c.val.comp ((staircaseSimplex e).comp
      (staircaseFace (Fin.succ (2 : Fin 3)))) =
      ContinuousMap.const (stdSimplex ℝ (Fin 3)) x := hthree
  rw [hzero, hthree']
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

theorem hurewiczCubeChain_boundary (c : GenLoop (Fin 3) X x) :
    hurewiczCubeChain c ≫ (IntegralChains X).d 3 2 = 0 := by
  classical
  have h₁ := signed_swap_pairing
    (fun e => singularSimplexChain (c.val.comp ((staircaseSimplex e).comp (staircaseFace 1))))
    0 1 (by decide) (fun e => by rw [← staircase_face_one_swap e])
  have h₂ := signed_swap_pairing
    (fun e => singularSimplexChain (c.val.comp ((staircaseSimplex e).comp (staircaseFace 2))))
    1 2 (by decide) (fun e => by rw [← staircase_face_two_swap e])
  unfold hurewiczCubeChain
  simp only [Preadditive.sum_comp, Linear.smul_comp, mapped_staircase_boundary,
    smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [h₁, h₂, neg_zero, zero_add]


def hurewiczCubeClass (c : GenLoop (Fin 3) X x) : IntegralHomology X 3 :=
  ((IntegralChains X).liftCycles (hurewiczCubeChain c) 2
    ((ComplexShape.down ℕ).next_eq' (by rfl))
    (hurewiczCubeChain_boundary c) ≫ (IntegralChains X).homologyπ 3) (ULift.up 1)

private def cubeBoundarySetoid : Setoid (ULift.{u} (I^(Fin 3))) where
  r a b := a = b ∨ (a.down ∈ Cube.boundary (Fin 3) ∧ b.down ∈ Cube.boundary (Fin 3))
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr ⟨hab.1, hbc.2⟩

private abbrev CubeBoundaryQuotient := Quotient cubeBoundarySetoid.{u}

private def cubeQuotientBase : CubeBoundaryQuotient.{u} :=
  Quotient.mk _ (ULift.up (fun _ => 0))

private def universalCube : GenLoop (Fin 3) CubeBoundaryQuotient.{u} cubeQuotientBase :=
  ⟨⟨fun z => Quotient.mk _ (ULift.up z),
    continuous_quotient_mk'.comp continuous_uliftUp⟩, by
    intro z hz
    apply Quotient.sound
    exact Or.inr ⟨hz, ⟨(0 : Fin 3), Or.inl rfl⟩⟩⟩

private theorem cube_factor_respects (c : GenLoop (Fin 3) X x)
    (a b : ULift.{u} (I^(Fin 3))) (h : cubeBoundarySetoid.r a b) : c a.down = c b.down := by
  rcases h with rfl | h
  · rfl
  · exact (c.property _ h.1).trans (c.property _ h.2).symm

private def cubeFactor (c : GenLoop (Fin 3) X x) : C(CubeBoundaryQuotient.{u}, X) where
  toFun := Quotient.lift (fun z => c z.down) (cube_factor_respects c)
  continuous_toFun := (c.val.continuous.comp continuous_uliftDown).quotient_lift _

private theorem cubeFactor_class (c : GenLoop (Fin 3) X x) :
    hurewiczCubeClass (genLoopPostcompose (cubeFactor c) universalCube) = hurewiczCubeClass c := rfl

private theorem cube_homotopy_respects {c d : GenLoop (Fin 3) X x}
    (h : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (t : I) (a b : ULift.{u} (I^(Fin 3))) (hab : cubeBoundarySetoid.r a b) :
    h (t, a.down) = h (t, b.down) := by
  rcases hab with rfl | hab
  · rfl
  · exact ((h.eq_fst t hab.1).trans (c.property _ hab.1)).trans
      ((h.eq_fst t hab.2).trans (c.property _ hab.2)).symm

private def cubeFactorHomotopy {c d : GenLoop (Fin 3) X x}
    (h : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3))) :
    ContinuousMap.Homotopy (cubeFactor c) (cubeFactor d) where
  toFun p := Quotient.lift (fun z => h (p.1, z.down)) (cube_homotopy_respects h p.1) p.2
  continuous_toFun := by
    apply (isQuotientMap_quotient_mk' (s := cubeBoundarySetoid.{u})).continuous_lift_prod_right
    exact h.continuous.comp
      (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd))
  map_zero_left q := by
    induction q using Quotient.inductionOn with
    | h q => exact h.apply_zero q.down
  map_one_left q := by
    induction q using Quotient.inductionOn with
    | h q => exact h.apply_one q.down

private theorem cubeClass_natural (f : C(X, Y)) (c : GenLoop (Fin 3) X x) :
    hurewiczCubeClass (genLoopPostcompose f c) = integralHomologyMap 3 f (hurewiczCubeClass c) := by
  let F : IntegralChains X ⟶ IntegralChains Y := integralChainsFunctor.map (TopCat.ofHom f)
  have he :
      (IntegralChains X).liftCycles (hurewiczCubeChain c) 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary c) ≫
        (IntegralChains X).homologyπ 3 ≫ HomologicalComplex.homologyMap F 3 =
      (IntegralChains Y).liftCycles (hurewiczCubeChain (genLoopPostcompose f c)) 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary _) ≫
        (IntegralChains Y).homologyπ 3 := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap]
    apply congrArg (fun k : integralCoefficients ⟶ (IntegralChains Y).cycles 3 =>
      k ≫ (IntegralChains Y).homologyπ 3)
    apply (cancel_mono ((IntegralChains Y).iCycles 3)).1
    simp only [HomologicalComplex.liftCycles_i]
    exact hurewiczCubeChain_natural f c
  exact (congrArg (fun k : integralCoefficients ⟶ IntegralHomology Y 3 => k (ULift.up 1)) he).symm

theorem hurewiczCubeClass_homotopic {c d : GenLoop (Fin 3) X x} (h : GenLoop.Homotopic c d) :
    hurewiczCubeClass c = hurewiczCubeClass d := by
  obtain ⟨h⟩ := h
  have hmaps : integralHomologyMap 3 (cubeFactor c) = integralHomologyMap 3 (cubeFactor d) :=
    (show TopCat.Homotopy (TopCat.ofHom (cubeFactor c)) (TopCat.ofHom (cubeFactor d)) from
      cubeFactorHomotopy h).congr_homologyMap_singularChainComplexFunctor integralCoefficients 3
  have hc := cubeClass_natural (cubeFactor c) universalCube
  have hd := cubeClass_natural (cubeFactor d) universalCube
  rw [cubeFactor_class] at hc hd
  exact hc.trans ((congrArg
    (fun k : IntegralHomology CubeBoundaryQuotient.{u} 3 ⟶ IntegralHomology X 3 =>
      k (hurewiczCubeClass universalCube)) hmaps).trans hd.symm)


def hurewiczThree (x : X) : HomotopyGroup (Fin 3) X x → IntegralHomology X 3 :=
  Quotient.lift hurewiczCubeClass (fun _ _ h => hurewiczCubeClass_homotopic h)

@[simp] theorem hurewiczThree_mk (c : GenLoop (Fin 3) X x) :
    hurewiczThree x (Quotient.mk _ c) = hurewiczCubeClass c := rfl

theorem hurewiczThree_one (x : X) : hurewiczThree x 1 = 0 := by
  change hurewiczCubeClass (GenLoop.const : GenLoop (Fin 3) X x) = 0
  have hz : (IntegralChains X).liftCycles
      (hurewiczCubeChain (GenLoop.const : GenLoop (Fin 3) X x)) 2
      ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary _) = 0 := by
    apply (cancel_mono ((IntegralChains X).iCycles 3)).1
    rw [HomologicalComplex.liftCycles_i, zero_comp, hurewiczCubeChain_const]
  unfold hurewiczCubeClass
  rw [hz, zero_comp]
  rfl

private abbrev ConcatVertex := Fin 3 × Fin 2 × Fin 2

private def concatCells : Fin 12 → Fin 5 → ConcatVertex :=
  ![![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 1, 0), (2, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 0, 1), (2, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (2, 0, 1), (2, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (2, 0, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1), (2, 1, 1)]]
private def concatSigns : Fin 12 → ℤ := ![1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1]
private def concatFaces : Fin 12 → Fin 5 → Fin 4 → ConcatVertex :=
  ![![![(1, 0, 0), (2, 0, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (2, 0, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 1, 0)]],
    ![![(1, 0, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (2, 1, 0)]],
    ![![(1, 0, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)]],
    ![![(0, 1, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (2, 1, 0), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (2, 1, 0)]],
    ![![(0, 1, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (1, 1, 1)]],
    ![![(0, 1, 0), (0, 1, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 1, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (1, 1, 1)]],
    ![![(1, 0, 0), (2, 0, 0), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (2, 0, 0), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 0, 1)]],
    ![![(1, 0, 0), (1, 0, 1), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 1), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (2, 0, 1)]],
    ![![(1, 0, 0), (1, 0, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (1, 1, 1)]],
    ![![(0, 0, 1), (1, 0, 1), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 1), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (2, 0, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (2, 0, 1)]],
    ![![(0, 0, 1), (1, 0, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (1, 0, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1)]],
    ![![(0, 0, 1), (0, 1, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 1, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (1, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (0, 1, 1), (2, 1, 1)], ![(0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1)]]]
private def concatEndFaces : Fin 18 → Fin 4 → ConcatVertex :=
  ![![(1, 0, 0), (2, 0, 0), (2, 1, 0), (2, 1, 1)],
    ![(1, 0, 0), (2, 0, 0), (2, 0, 1), (2, 1, 1)],
    ![(1, 0, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)],
    ![(1, 0, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)],
    ![(1, 0, 0), (1, 0, 1), (2, 0, 1), (2, 1, 1)],
    ![(1, 0, 0), (1, 0, 1), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (2, 0, 0), (2, 1, 0), (2, 1, 1)],
    ![(0, 0, 0), (2, 0, 0), (2, 0, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (2, 1, 0), (2, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (2, 0, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (0, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (1, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (1, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (1, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1)]]
private def concatEndSigns : Fin 18 → ℤ := ![1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1]
private def concatSideFaces : Fin 12 → Fin 4 → ConcatVertex :=
  ![![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 1, 0)],
    ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (2, 1, 0)],
    ![(0, 1, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)],
    ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (2, 1, 0)],
    ![(0, 1, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)],
    ![(0, 1, 0), (0, 1, 1), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 0), (1, 0, 0), (2, 0, 0), (2, 0, 1)],
    ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (2, 0, 1)],
    ![(0, 0, 1), (1, 0, 1), (2, 0, 1), (2, 1, 1)],
    ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (2, 0, 1)],
    ![(0, 0, 1), (1, 0, 1), (1, 1, 1), (2, 1, 1)],
    ![(0, 0, 1), (0, 1, 1), (1, 1, 1), (2, 1, 1)]]
private def concatSideSigns : Fin 12 → ℤ := ![1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1]

private theorem concatFaces_eq (k : Fin 12) (i : Fin 5) :
    (fun j : Fin 4 => concatCells k (i.succAbove j)) = concatFaces k i := by
  fin_cases k <;> fin_cases i <;> funext j <;> fin_cases j <;> rfl

private theorem concat_four_chain_faces {A : Type*} [AddCommGroup A]
    (F : (Fin 4 → ConcatVertex) → A) :
    (∑ k : Fin 12, concatSigns k •
      ∑ i : Fin 5, (-1 : ℤ) ^ i.val • F (fun j => concatCells k (i.succAbove j))) =
    (∑ k : Fin 18, concatEndSigns k • F (concatEndFaces k)) +
      ∑ k : Fin 12, concatSideSigns k • F (concatSideFaces k) := by
  simp only [concatFaces_eq]
  norm_num [Fin.sum_univ_succ, concatSigns, concatFaces, concatEndSigns, concatEndFaces,
    concatSideSigns, concatSideFaces]
  abel

private theorem concat_side_constant_coordinate (k : Fin 12) :
    (∃ b : Fin 2, ∀ j : Fin 4, (concatSideFaces k j).2.1 = b) ∨
      (∃ b : Fin 2, ∀ j : Fin 4, (concatSideFaces k j).2.2 = b) := by
  fin_cases k <;> decide

private theorem concat_side_sign_sum : (∑ k : Fin 12, concatSideSigns k) = 0 := by
  norm_num [Fin.sum_univ_succ, concatSideSigns]

private def concatVertexPoint (v : ConcatVertex) : I^(Fin 3) :=
  ![⟨(v.1.val : ℝ) / 2, by positivity, by
      have h : v.1.val ≤ 2 := by omega
      have h' : (v.1.val : ℝ) ≤ 2 := by exact_mod_cast h
      linarith⟩,
    ⟨(v.2.1.val : ℝ), Nat.cast_nonneg _, by
      have h : v.2.1.val ≤ 1 := by omega
      exact_mod_cast h⟩,
    ⟨(v.2.2.val : ℝ), Nat.cast_nonneg _, by
      have h : v.2.2.val ≤ 1 := by omega
      exact_mod_cast h⟩]

private def concatAffineSimplex {n : ℕ} (v : Fin (n + 1) → ConcatVertex) :
    C(stdSimplex ℝ (Fin (n + 1)), I^(Fin 3)) where
  toFun q i := ⟨∑ j, q.val j * (concatVertexPoint (v j) i : ℝ), by
    constructor
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (q.property.1 j)
        (concatVertexPoint (v j) i).property.1)
    · calc
        ∑ j, q.val j * (concatVertexPoint (v j) i : ℝ) ≤ ∑ j, q.val j * 1 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
            (concatVertexPoint (v j) i).property.2 (q.property.1 j))
        _ = 1 := by simpa only [mul_one] using q.property.2⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ (fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).mul continuous_const)

private def concatPrismChain {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) : integralCoefficients ⟶ (IntegralChains X).X 4 :=
  ∑ k : Fin 12, concatSigns k • singularSimplexChain
    ((GenLoop.transAt (0 : Fin 3) p q).val.comp (concatAffineSimplex (concatCells k)))

private def concatSimplexFace (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

private theorem concatSimplexFace_self (n : ℕ) (i : Fin (n + 2))
    (q : stdSimplex ℝ (Fin (n + 1))) : (concatSimplexFace n i q).val i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (q : Fin (n + 1) → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2)

private theorem concatSimplexFace_above (n : ℕ) (i : Fin (n + 2))
    (q : stdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    (concatSimplexFace n i q).val (i.succAbove j) = q.val j := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (q : Fin (n + 1) → ℝ) (i.succAbove j) = q j
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

private theorem concatAffineSimplex_face {n : ℕ} (v : Fin (n + 2) → ConcatVertex)
    (i : Fin (n + 2)) :
    (concatAffineSimplex v).comp (concatSimplexFace n i) =
      concatAffineSimplex (fun j => v (i.succAbove j)) := by
  ext q k
  change (∑ j : Fin (n + 2), (concatSimplexFace n i q).val j *
      (concatVertexPoint (v j) k : ℝ)) =
    ∑ j : Fin (n + 1), q.val j * (concatVertexPoint (v (i.succAbove j)) k : ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  have hz : (concatSimplexFace n i q).val i * (concatVertexPoint (v i) k : ℝ) = 0 := by
    rw [concatSimplexFace_self, zero_mul]
  have hs :
      (∑ j : Fin (n + 1), (concatSimplexFace n i q).val (i.succAbove j) *
        (concatVertexPoint (v (i.succAbove j)) k : ℝ)) =
      ∑ j : Fin (n + 1), q.val j * (concatVertexPoint (v (i.succAbove j)) k : ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun a : ℝ => a * (concatVertexPoint (v (i.succAbove j)) k : ℝ))
      (concatSimplexFace_above n i q j)
  exact (congrArg₂ (fun a b : ℝ => a + b) hz hs).trans (zero_add _)

private theorem concat_singular_boundary {X : Type u} [TopologicalSpace X] {n : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    singularSimplexChain s ≫ (IntegralChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        singularSimplexChain (s.comp (concatSimplexFace n i)) := by
  exact (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d (R := integralCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n + 1⦌)).symm s)

private theorem concatPrismChain_boundary_table {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    concatPrismChain p q ≫ (IntegralChains X).d 4 3 =
      (∑ k : Fin 18, concatEndSigns k • singularSimplexChain
        ((GenLoop.transAt (0 : Fin 3) p q).val.comp (concatAffineSimplex (concatEndFaces k)))) +
      ∑ k : Fin 12, concatSideSigns k • singularSimplexChain
        ((GenLoop.transAt (0 : Fin 3) p q).val.comp (concatAffineSimplex (concatSideFaces k))) := by
  simp only [concatPrismChain, Preadditive.sum_comp, Linear.smul_comp,
    concat_singular_boundary, ContinuousMap.comp_assoc, concatAffineSimplex_face]
  exact concat_four_chain_faces
    (fun v => singularSimplexChain ((GenLoop.transAt (0 : Fin 3) p q).val.comp
      (concatAffineSimplex v)))

private def concatPerms : Fin 6 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 1 2, Equiv.swap 0 1, (Equiv.swap 1 2).trans (Equiv.swap 0 1),
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), Equiv.swap 0 2]

private theorem concatPerms_bijective : Function.Bijective concatPerms := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨by decide, by norm_num [Fintype.card_perm, Nat.factorial]⟩

private theorem concat_oriented_sum {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (Fin 3) → A) :
    (∑ e, ((e.sign : ℤˣ) : ℤ) • f e) =
      f (concatPerms 0) - f (concatPerms 1) - f (concatPerms 2) +
        f (concatPerms 3) + f (concatPerms 4) - f (concatPerms 5) := by
  rw [← concatPerms_bijective.sum_comp (fun e => ((e.sign : ℤˣ) : ℤ) • f e)]
  simp [Fin.sum_univ_succ, concatPerms, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_swap', sub_eq_add_neg, add_assoc]

private def concatHalf (b : Fin 2) : C(I^(Fin 3), I^(Fin 3)) where
  toFun z := Function.update z 0 ⟨((z 0 : ℝ) + b.val) / 2, by
    have h0 := unitInterval.nonneg (z 0)
    have h1 := unitInterval.le_one (z 0)
    have hb0 : (0 : ℝ) ≤ b.val := Nat.cast_nonneg _
    have hb1 : (b.val : ℝ) ≤ 1 := by exact_mod_cast (show b.val ≤ 1 by omega)
    constructor <;> linarith⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [Function.update_self]
      exact Continuous.subtype_mk
        (((continuous_apply 0).subtype_val.add continuous_const).div_const 2) _
    · simp only [Function.update_of_ne hi]
      exact continuous_apply i

private theorem concatHalf_zero (b : Fin 2) (z : I^(Fin 3)) :
    ((concatHalf b z) 0 : ℝ) = ((z 0 : ℝ) + b.val) / 2 := by
  rfl

private theorem concatHalf_coordinate (b : Fin 2) (z : I^(Fin 3)) (i : Fin 3) :
    ((concatHalf b z) i : ℝ) =
      if i = 0 then ((z 0 : ℝ) + b.val) / 2 else (z i : ℝ) := by
  by_cases hi : i = 0
  · subst i
    rw [if_pos rfl, concatHalf_zero]
  · change ((Function.update z 0 _) i : ℝ) = _
    simp only [Function.update_of_ne hi, if_neg hi]

private theorem concat_half_lower {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (concatHalf 0) = p.val := by
  ext z
  have hz0 := unitInterval.nonneg (z 0)
  have hz1 := unitInterval.le_one (z 0)
  have hhalf : ((concatHalf 0 z) 0 : ℝ) ≤ 1 / 2 := by
    change ((z 0 : ℝ) + (0 : Fin 2).val) / 2 ≤ 1 / 2
    norm_num
    linarith
  change (if ((concatHalf 0 z) 0 : ℝ) ≤ 1 / 2 then
    p (Function.update (concatHalf 0 z) 0
      (Set.projIcc 0 1 zero_le_one (2 * ((concatHalf 0 z) 0 : ℝ)))) else _) = p z
  rw [if_pos hhalf]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    apply Subtype.ext
    simp only [Function.update_self, Set.coe_projIcc]
    rw [concatHalf_zero]
    simp only [Fin.val_zero, Nat.cast_zero]
    change max (0 : ℝ) (min 1 (2 * (((z 0 : ℝ) + 0) / 2))) = (z 0 : ℝ)
    have he : 2 * (((z 0 : ℝ) + 0) / 2) = (z 0 : ℝ) := by ring
    rw [he, min_eq_right hz1, max_eq_right hz0]
  · simp [concatHalf, Function.update_of_ne hi]

private theorem concat_half_upper {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (concatHalf 1) = q.val := by
  ext z
  have hz0 := unitInterval.nonneg (z 0)
  have hz1 := unitInterval.le_one (z 0)
  change (if ((concatHalf 1 z) 0 : ℝ) ≤ 1 / 2 then
    p (Function.update (concatHalf 1 z) 0
      (Set.projIcc 0 1 zero_le_one (2 * ((concatHalf 1 z) 0 : ℝ)))) else
    q (Function.update (concatHalf 1 z) 0
      (Set.projIcc 0 1 zero_le_one (2 * ((concatHalf 1 z) 0 : ℝ) - 1)))) = q z
  by_cases hz : (z 0 : ℝ) = 0
  · have he : z 0 = 0 := Subtype.ext hz
    have hhalf : ((concatHalf 1 z) 0 : ℝ) = 1 / 2 := by
      change ((z 0 : ℝ) + (1 : Fin 2).val) / 2 = 1 / 2
      norm_num [hz]
    rw [if_pos (le_of_eq hhalf)]
    have hp : p.val (Function.update (concatHalf 1 z) 0
        (Set.projIcc 0 1 zero_le_one (2 * ((concatHalf 1 z) 0 : ℝ)))) = x :=
      p.property _ ⟨0, Or.inr (by
      apply Subtype.ext
      simp only [Function.update_self, Set.coe_projIcc, hhalf]
      norm_num)⟩
    exact hp.trans (q.property z ⟨0, Or.inl he⟩).symm
  · have hzpos : 0 < (z 0 : ℝ) := lt_of_le_of_ne hz0 (Ne.symm hz)
    have hhalf : ¬ ((concatHalf 1 z) 0 : ℝ) ≤ 1 / 2 := by
      change ¬ ((z 0 : ℝ) + (1 : Fin 2).val) / 2 ≤ 1 / 2
      norm_num
      linarith
    rw [if_neg hhalf]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst i
      apply Subtype.ext
      simp only [Function.update_self, Set.coe_projIcc]
      rw [concatHalf_zero]
      simp only [Fin.val_one, Nat.cast_one]
      change max (0 : ℝ) (min 1 (2 * (((z 0 : ℝ) + 1) / 2) - 1)) = (z 0 : ℝ)
      have he : 2 * (((z 0 : ℝ) + 1) / 2) - 1 = (z 0 : ℝ) := by ring
      rw [he, min_eq_right hz1, max_eq_right hz0]
    · simp [concatHalf, Function.update_of_ne hi]

private theorem concatPerms_inverse (k : Fin 6) (i : Fin 3) :
    (concatPerms k).symm i =
      ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![1, 2, 0], ![2, 1, 0]] k i := by
  fin_cases k <;> fin_cases i <;> rfl

private def concatEndVertexValues : Fin 18 → Fin 4 → Fin 3 → ℝ :=
  ![![![1 / 2, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]],
    ![![1 / 2, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1]],
    ![![1 / 2, 0, 0], ![1 / 2, 1, 0], ![1, 1, 0], ![1, 1, 1]],
    ![![1 / 2, 0, 0], ![1 / 2, 1, 0], ![1 / 2, 1, 1], ![1, 1, 1]],
    ![![1 / 2, 0, 0], ![1 / 2, 0, 1], ![1, 0, 1], ![1, 1, 1]],
    ![![1 / 2, 0, 0], ![1 / 2, 0, 1], ![1 / 2, 1, 1], ![1, 1, 1]],
    ![![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]],
    ![![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1]],
    ![![0, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 1, 1]],
    ![![0, 0, 0], ![0, 1, 0], ![0, 1, 1], ![1, 1, 1]],
    ![![0, 0, 0], ![0, 0, 1], ![1, 0, 1], ![1, 1, 1]],
    ![![0, 0, 0], ![0, 0, 1], ![0, 1, 1], ![1, 1, 1]],
    ![![0, 0, 0], ![1 / 2, 0, 0], ![1 / 2, 1, 0], ![1 / 2, 1, 1]],
    ![![0, 0, 0], ![1 / 2, 0, 0], ![1 / 2, 0, 1], ![1 / 2, 1, 1]],
    ![![0, 0, 0], ![0, 1, 0], ![1 / 2, 1, 0], ![1 / 2, 1, 1]],
    ![![0, 0, 0], ![0, 1, 0], ![0, 1, 1], ![1 / 2, 1, 1]],
    ![![0, 0, 0], ![0, 0, 1], ![1 / 2, 0, 1], ![1 / 2, 1, 1]],
    ![![0, 0, 0], ![0, 0, 1], ![0, 1, 1], ![1 / 2, 1, 1]]]

private theorem concatEndFaces_row_0 : concatEndFaces 0 = ![(1, 0, 0), (2, 0, 0), (2, 1, 0), (2, 1, 1)] := rfl
private theorem concatEndValues_row_0 : concatEndVertexValues 0 = ![![1 / 2, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_1 : concatEndFaces 1 = ![(1, 0, 0), (2, 0, 0), (2, 0, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_1 : concatEndVertexValues 1 = ![![1 / 2, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_2 : concatEndFaces 2 = ![(1, 0, 0), (1, 1, 0), (2, 1, 0), (2, 1, 1)] := rfl
private theorem concatEndValues_row_2 : concatEndVertexValues 2 = ![![1 / 2, 0, 0], ![1 / 2, 1, 0], ![1, 1, 0], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_3 : concatEndFaces 3 = ![(1, 0, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_3 : concatEndVertexValues 3 = ![![1 / 2, 0, 0], ![1 / 2, 1, 0], ![1 / 2, 1, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_4 : concatEndFaces 4 = ![(1, 0, 0), (1, 0, 1), (2, 0, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_4 : concatEndVertexValues 4 = ![![1 / 2, 0, 0], ![1 / 2, 0, 1], ![1, 0, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_5 : concatEndFaces 5 = ![(1, 0, 0), (1, 0, 1), (1, 1, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_5 : concatEndVertexValues 5 = ![![1 / 2, 0, 0], ![1 / 2, 0, 1], ![1 / 2, 1, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_6 : concatEndFaces 6 = ![(0, 0, 0), (2, 0, 0), (2, 1, 0), (2, 1, 1)] := rfl
private theorem concatEndValues_row_6 : concatEndVertexValues 6 = ![![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_7 : concatEndFaces 7 = ![(0, 0, 0), (2, 0, 0), (2, 0, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_7 : concatEndVertexValues 7 = ![![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_8 : concatEndFaces 8 = ![(0, 0, 0), (0, 1, 0), (2, 1, 0), (2, 1, 1)] := rfl
private theorem concatEndValues_row_8 : concatEndVertexValues 8 = ![![0, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_9 : concatEndFaces 9 = ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_9 : concatEndVertexValues 9 = ![![0, 0, 0], ![0, 1, 0], ![0, 1, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_10 : concatEndFaces 10 = ![(0, 0, 0), (0, 0, 1), (2, 0, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_10 : concatEndVertexValues 10 = ![![0, 0, 0], ![0, 0, 1], ![1, 0, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_11 : concatEndFaces 11 = ![(0, 0, 0), (0, 0, 1), (0, 1, 1), (2, 1, 1)] := rfl
private theorem concatEndValues_row_11 : concatEndVertexValues 11 = ![![0, 0, 0], ![0, 0, 1], ![0, 1, 1], ![1, 1, 1]] := rfl

private theorem concatEndFaces_row_12 : concatEndFaces 12 = ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)] := rfl
private theorem concatEndValues_row_12 : concatEndVertexValues 12 = ![![0, 0, 0], ![1 / 2, 0, 0], ![1 / 2, 1, 0], ![1 / 2, 1, 1]] := rfl

private theorem concatEndFaces_row_13 : concatEndFaces 13 = ![(0, 0, 0), (1, 0, 0), (1, 0, 1), (1, 1, 1)] := rfl
private theorem concatEndValues_row_13 : concatEndVertexValues 13 = ![![0, 0, 0], ![1 / 2, 0, 0], ![1 / 2, 0, 1], ![1 / 2, 1, 1]] := rfl

private theorem concatEndFaces_row_14 : concatEndFaces 14 = ![(0, 0, 0), (0, 1, 0), (1, 1, 0), (1, 1, 1)] := rfl
private theorem concatEndValues_row_14 : concatEndVertexValues 14 = ![![0, 0, 0], ![0, 1, 0], ![1 / 2, 1, 0], ![1 / 2, 1, 1]] := rfl

private theorem concatEndFaces_row_15 : concatEndFaces 15 = ![(0, 0, 0), (0, 1, 0), (0, 1, 1), (1, 1, 1)] := rfl
private theorem concatEndValues_row_15 : concatEndVertexValues 15 = ![![0, 0, 0], ![0, 1, 0], ![0, 1, 1], ![1 / 2, 1, 1]] := rfl

private theorem concatEndFaces_row_16 : concatEndFaces 16 = ![(0, 0, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1)] := rfl
private theorem concatEndValues_row_16 : concatEndVertexValues 16 = ![![0, 0, 0], ![0, 0, 1], ![1 / 2, 0, 1], ![1 / 2, 1, 1]] := rfl

private theorem concatEndFaces_row_17 : concatEndFaces 17 = ![(0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1)] := rfl
private theorem concatEndValues_row_17 : concatEndVertexValues 17 = ![![0, 0, 0], ![0, 0, 1], ![0, 1, 1], ![1 / 2, 1, 1]] := rfl

private theorem concatEndVertex_values_0 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 0 j) i : ℝ) = concatEndVertexValues 0 j i := by
  rw [concatEndFaces_row_0, concatEndValues_row_0]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_1 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 1 j) i : ℝ) = concatEndVertexValues 1 j i := by
  rw [concatEndFaces_row_1, concatEndValues_row_1]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_2 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 2 j) i : ℝ) = concatEndVertexValues 2 j i := by
  rw [concatEndFaces_row_2, concatEndValues_row_2]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_3 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 3 j) i : ℝ) = concatEndVertexValues 3 j i := by
  rw [concatEndFaces_row_3, concatEndValues_row_3]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_4 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 4 j) i : ℝ) = concatEndVertexValues 4 j i := by
  rw [concatEndFaces_row_4, concatEndValues_row_4]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_5 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 5 j) i : ℝ) = concatEndVertexValues 5 j i := by
  rw [concatEndFaces_row_5, concatEndValues_row_5]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_6 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 6 j) i : ℝ) = concatEndVertexValues 6 j i := by
  rw [concatEndFaces_row_6, concatEndValues_row_6]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_7 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 7 j) i : ℝ) = concatEndVertexValues 7 j i := by
  rw [concatEndFaces_row_7, concatEndValues_row_7]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_8 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 8 j) i : ℝ) = concatEndVertexValues 8 j i := by
  rw [concatEndFaces_row_8, concatEndValues_row_8]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_9 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 9 j) i : ℝ) = concatEndVertexValues 9 j i := by
  rw [concatEndFaces_row_9, concatEndValues_row_9]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_10 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 10 j) i : ℝ) = concatEndVertexValues 10 j i := by
  rw [concatEndFaces_row_10, concatEndValues_row_10]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_11 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 11 j) i : ℝ) = concatEndVertexValues 11 j i := by
  rw [concatEndFaces_row_11, concatEndValues_row_11]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_12 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 12 j) i : ℝ) = concatEndVertexValues 12 j i := by
  rw [concatEndFaces_row_12, concatEndValues_row_12]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_13 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 13 j) i : ℝ) = concatEndVertexValues 13 j i := by
  rw [concatEndFaces_row_13, concatEndValues_row_13]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_14 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 14 j) i : ℝ) = concatEndVertexValues 14 j i := by
  rw [concatEndFaces_row_14, concatEndValues_row_14]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_15 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 15 j) i : ℝ) = concatEndVertexValues 15 j i := by
  rw [concatEndFaces_row_15, concatEndValues_row_15]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_16 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 16 j) i : ℝ) = concatEndVertexValues 16 j i := by
  rw [concatEndFaces_row_16, concatEndValues_row_16]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values_17 (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces 17 j) i : ℝ) = concatEndVertexValues 17 j i := by
  rw [concatEndFaces_row_17, concatEndValues_row_17]
  fin_cases j <;> fin_cases i <;>
    norm_num [concatVertexPoint, Matrix.cons_val_two, Matrix.cons_val_three]
private theorem concatEndVertex_values (k : Fin 18) (j : Fin 4) (i : Fin 3) :
    (concatVertexPoint (concatEndFaces k j) i : ℝ) = concatEndVertexValues k j i := by
  fin_cases k
  · exact concatEndVertex_values_0 j i
  · exact concatEndVertex_values_1 j i
  · exact concatEndVertex_values_2 j i
  · exact concatEndVertex_values_3 j i
  · exact concatEndVertex_values_4 j i
  · exact concatEndVertex_values_5 j i
  · exact concatEndVertex_values_6 j i
  · exact concatEndVertex_values_7 j i
  · exact concatEndVertex_values_8 j i
  · exact concatEndVertex_values_9 j i
  · exact concatEndVertex_values_10 j i
  · exact concatEndVertex_values_11 j i
  · exact concatEndVertex_values_12 j i
  · exact concatEndVertex_values_13 j i
  · exact concatEndVertex_values_14 j i
  · exact concatEndVertex_values_15 j i
  · exact concatEndVertex_values_16 j i
  · exact concatEndVertex_values_17 j i
private def concatStaircaseValues (k : Fin 6) (q : stdSimplex ℝ (Fin 4)) : Fin 3 → ℝ :=
  ![![q.val 1 + q.val 2 + q.val 3, q.val 2 + q.val 3, q.val 3],
        ![q.val 1 + q.val 2 + q.val 3, q.val 3, q.val 2 + q.val 3],
        ![q.val 2 + q.val 3, q.val 1 + q.val 2 + q.val 3, q.val 3],
        ![q.val 3, q.val 1 + q.val 2 + q.val 3, q.val 2 + q.val 3],
        ![q.val 2 + q.val 3, q.val 3, q.val 1 + q.val 2 + q.val 3],
        ![q.val 3, q.val 2 + q.val 3, q.val 1 + q.val 2 + q.val 3]] k

private theorem concatStaircaseValues_row_0 (q : stdSimplex ℝ (Fin 4)) :
    concatStaircaseValues 0 q = ![q.val 1 + q.val 2 + q.val 3, q.val 2 + q.val 3, q.val 3] := rfl

private theorem concatStaircaseValues_row_1 (q : stdSimplex ℝ (Fin 4)) :
    concatStaircaseValues 1 q = ![q.val 1 + q.val 2 + q.val 3, q.val 3, q.val 2 + q.val 3] := rfl

private theorem concatStaircaseValues_row_2 (q : stdSimplex ℝ (Fin 4)) :
    concatStaircaseValues 2 q = ![q.val 2 + q.val 3, q.val 1 + q.val 2 + q.val 3, q.val 3] := rfl

private theorem concatStaircaseValues_row_3 (q : stdSimplex ℝ (Fin 4)) :
    concatStaircaseValues 3 q = ![q.val 3, q.val 1 + q.val 2 + q.val 3, q.val 2 + q.val 3] := rfl

private theorem concatStaircaseValues_row_4 (q : stdSimplex ℝ (Fin 4)) :
    concatStaircaseValues 4 q = ![q.val 2 + q.val 3, q.val 3, q.val 1 + q.val 2 + q.val 3] := rfl

private theorem concatStaircaseValues_row_5 (q : stdSimplex ℝ (Fin 4)) :
    concatStaircaseValues 5 q = ![q.val 3, q.val 2 + q.val 3, q.val 1 + q.val 2 + q.val 3] := rfl

private theorem concatStaircase_value (k : Fin 6) (q : stdSimplex ℝ (Fin 4)) (i : Fin 3) :
    staircaseCoordinate (concatPerms k) q i =
      concatStaircaseValues k q i := by
  fin_cases k <;> fin_cases i
  · change (∑ j : Fin 4, if (0 : ℕ) < j.val then q.val j else 0) = q.val 1 + q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (1 : ℕ) < j.val then q.val j else 0) = q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (2 : ℕ) < j.val then q.val j else 0) = q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (0 : ℕ) < j.val then q.val j else 0) = q.val 1 + q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (2 : ℕ) < j.val then q.val j else 0) = q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (1 : ℕ) < j.val then q.val j else 0) = q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (1 : ℕ) < j.val then q.val j else 0) = q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (0 : ℕ) < j.val then q.val j else 0) = q.val 1 + q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (2 : ℕ) < j.val then q.val j else 0) = q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (2 : ℕ) < j.val then q.val j else 0) = q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (0 : ℕ) < j.val then q.val j else 0) = q.val 1 + q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (1 : ℕ) < j.val then q.val j else 0) = q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (1 : ℕ) < j.val then q.val j else 0) = q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (2 : ℕ) < j.val then q.val j else 0) = q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (0 : ℕ) < j.val then q.val j else 0) = q.val 1 + q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (2 : ℕ) < j.val then q.val j else 0) = q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (1 : ℕ) < j.val then q.val j else 0) = q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num
  · change (∑ j : Fin 4, if (0 : ℕ) < j.val then q.val j else 0) = q.val 1 + q.val 2 + q.val 3
    simp only [Fin.sum_univ_four]
    norm_num

private theorem concatEnd_upper (k : Fin 6) :
    concatAffineSimplex (concatEndFaces ⟨k.val, by omega⟩) =
      (concatHalf 1).comp (staircaseSimplex (concatPerms k)) := by
  ext q i
  have hsum := q.property.2
  change (∑ j : Fin 4, q.val j) = 1 at hsum
  rw [Fin.sum_univ_four] at hsum
  change (∑ j : Fin 4, q.val j *
      (concatVertexPoint (concatEndFaces ⟨k.val, by omega⟩ j) i : ℝ)) =
    ((concatHalf 1 (staircaseSimplex (concatPerms k) q)) i : ℝ)
  rw [concatHalf_coordinate]
  simp only [Fin.val_one, Nat.cast_one]
  change (∑ j : Fin 4, q.val j *
      (concatVertexPoint (concatEndFaces ⟨k.val, by omega⟩ j) i : ℝ)) =
    if i = 0 then (staircaseCoordinate (concatPerms k) q 0 + 1) / 2
      else staircaseCoordinate (concatPerms k) q i
  simp only [concatEndVertex_values, concatStaircase_value]
  fin_cases k
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 0 j i) =
      if i = 0 then (concatStaircaseValues 0 q 0 + 1) / 2
        else concatStaircaseValues 0 q i
    rw [concatEndValues_row_0, concatStaircaseValues_row_0]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals linarith
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 1 j i) =
      if i = 0 then (concatStaircaseValues 1 q 0 + 1) / 2
        else concatStaircaseValues 1 q i
    rw [concatEndValues_row_1, concatStaircaseValues_row_1]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals linarith
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 2 j i) =
      if i = 0 then (concatStaircaseValues 2 q 0 + 1) / 2
        else concatStaircaseValues 2 q i
    rw [concatEndValues_row_2, concatStaircaseValues_row_2]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals linarith
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 3 j i) =
      if i = 0 then (concatStaircaseValues 3 q 0 + 1) / 2
        else concatStaircaseValues 3 q i
    rw [concatEndValues_row_3, concatStaircaseValues_row_3]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals linarith
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 4 j i) =
      if i = 0 then (concatStaircaseValues 4 q 0 + 1) / 2
        else concatStaircaseValues 4 q i
    rw [concatEndValues_row_4, concatStaircaseValues_row_4]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals linarith
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 5 j i) =
      if i = 0 then (concatStaircaseValues 5 q 0 + 1) / 2
        else concatStaircaseValues 5 q i
    rw [concatEndValues_row_5, concatStaircaseValues_row_5]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals linarith

private theorem concatEnd_full (k : Fin 6) :
    concatAffineSimplex (concatEndFaces ⟨6 + k.val, by omega⟩) =
      staircaseSimplex (concatPerms k) := by
  ext q i
  change (∑ j : Fin 4, q.val j *
      (concatVertexPoint (concatEndFaces ⟨6 + k.val, by omega⟩ j) i : ℝ)) =
    staircaseCoordinate (concatPerms k) q i
  simp only [concatEndVertex_values, concatStaircase_value]
  fin_cases k
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 6 j i) =
      concatStaircaseValues 0 q i
    rw [concatEndValues_row_6, concatStaircaseValues_row_0]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 7 j i) =
      concatStaircaseValues 1 q i
    rw [concatEndValues_row_7, concatStaircaseValues_row_1]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 8 j i) =
      concatStaircaseValues 2 q i
    rw [concatEndValues_row_8, concatStaircaseValues_row_2]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 9 j i) =
      concatStaircaseValues 3 q i
    rw [concatEndValues_row_9, concatStaircaseValues_row_3]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 10 j i) =
      concatStaircaseValues 4 q i
    rw [concatEndValues_row_10, concatStaircaseValues_row_4]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 11 j i) =
      concatStaircaseValues 5 q i
    rw [concatEndValues_row_11, concatStaircaseValues_row_5]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]

private theorem concatEnd_lower (k : Fin 6) :
    concatAffineSimplex (concatEndFaces ⟨12 + k.val, by omega⟩) =
      (concatHalf 0).comp (staircaseSimplex (concatPerms k)) := by
  ext q i
  change (∑ j : Fin 4, q.val j *
      (concatVertexPoint (concatEndFaces ⟨12 + k.val, by omega⟩ j) i : ℝ)) =
    ((concatHalf 0 (staircaseSimplex (concatPerms k) q)) i : ℝ)
  rw [concatHalf_coordinate]
  simp only [Fin.val_zero, Nat.cast_zero]
  change (∑ j : Fin 4, q.val j *
      (concatVertexPoint (concatEndFaces ⟨12 + k.val, by omega⟩ j) i : ℝ)) =
    if i = 0 then (staircaseCoordinate (concatPerms k) q 0 + 0) / 2
      else staircaseCoordinate (concatPerms k) q i
  simp only [concatEndVertex_values, concatStaircase_value]
  fin_cases k
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 12 j i) =
      if i = 0 then (concatStaircaseValues 0 q 0 + 0) / 2
        else concatStaircaseValues 0 q i
    rw [concatEndValues_row_12, concatStaircaseValues_row_0]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals ring
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 13 j i) =
      if i = 0 then (concatStaircaseValues 1 q 0 + 0) / 2
        else concatStaircaseValues 1 q i
    rw [concatEndValues_row_13, concatStaircaseValues_row_1]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals ring
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 14 j i) =
      if i = 0 then (concatStaircaseValues 2 q 0 + 0) / 2
        else concatStaircaseValues 2 q i
    rw [concatEndValues_row_14, concatStaircaseValues_row_2]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals ring
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 15 j i) =
      if i = 0 then (concatStaircaseValues 3 q 0 + 0) / 2
        else concatStaircaseValues 3 q i
    rw [concatEndValues_row_15, concatStaircaseValues_row_3]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals ring
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 16 j i) =
      if i = 0 then (concatStaircaseValues 4 q 0 + 0) / 2
        else concatStaircaseValues 4 q i
    rw [concatEndValues_row_16, concatStaircaseValues_row_4]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals ring
  · change (∑ j : Fin 4, q.val j * concatEndVertexValues 17 j i) =
      if i = 0 then (concatStaircaseValues 5 q 0 + 0) / 2
        else concatStaircaseValues 5 q i
    rw [concatEndValues_row_17, concatStaircaseValues_row_5]
    fin_cases i <;> simp only [Fin.sum_univ_four] <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals ring

private theorem concatAffineSimplex_constant_coordinate {n : ℕ}
    (v : Fin (n + 1) → ConcatVertex) (i : Fin 3) (b : I)
    (hb : ∀ j, concatVertexPoint (v j) i = b)
    (q : stdSimplex ℝ (Fin (n + 1))) : concatAffineSimplex v q i = b := by
  apply Subtype.ext
  change (∑ j, q.val j * (concatVertexPoint (v j) i : ℝ)) = (b : ℝ)
  simp only [hb, ← Finset.sum_mul, q.property.2, one_mul]

private theorem concatSide_constant {X : Type u} [TopologicalSpace X] {x : X}
    (c : GenLoop (Fin 3) X x) (k : Fin 12) :
    c.val.comp (concatAffineSimplex (concatSideFaces k)) =
      ContinuousMap.const (stdSimplex ℝ (Fin 4)) x := by
  ext z
  apply c.property
  rcases concat_side_constant_coordinate k with ⟨b, hb⟩ | ⟨b, hb⟩
  · fin_cases b
    · exact ⟨1, Or.inl (concatAffineSimplex_constant_coordinate _ 1 0
        (fun j => by simp [concatVertexPoint, hb j]) z)⟩
    · exact ⟨1, Or.inr (concatAffineSimplex_constant_coordinate _ 1 1
        (fun j => by simp [concatVertexPoint, hb j]) z)⟩
  · fin_cases b
    · exact ⟨2, Or.inl (concatAffineSimplex_constant_coordinate _ 2 0
        (fun j => by simp [concatVertexPoint, hb j]) z)⟩
    · exact ⟨2, Or.inr (concatAffineSimplex_constant_coordinate _ 2 1
        (fun j => by simp [concatVertexPoint, hb j]) z)⟩

private theorem concatSide_sum_zero {X : Type u} [TopologicalSpace X] {x : X}
    (c : GenLoop (Fin 3) X x) :
    (∑ k : Fin 12, concatSideSigns k • singularSimplexChain
      (c.val.comp (concatAffineSimplex (concatSideFaces k)))) = 0 := by
  simp only [concatSide_constant, ← Finset.sum_smul, concat_side_sign_sum, zero_smul]

private def concatEndMaps {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    Fin 18 → C(stdSimplex ℝ (Fin 4), X) :=
  ![    q.val.comp (staircaseSimplex (concatPerms 0)),
    q.val.comp (staircaseSimplex (concatPerms 1)),
    q.val.comp (staircaseSimplex (concatPerms 2)),
    q.val.comp (staircaseSimplex (concatPerms 3)),
    q.val.comp (staircaseSimplex (concatPerms 4)),
    q.val.comp (staircaseSimplex (concatPerms 5)),
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (staircaseSimplex (concatPerms 0)),
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (staircaseSimplex (concatPerms 1)),
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (staircaseSimplex (concatPerms 2)),
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (staircaseSimplex (concatPerms 3)),
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (staircaseSimplex (concatPerms 4)),
    (GenLoop.transAt (0 : Fin 3) p q).val.comp (staircaseSimplex (concatPerms 5)),
    p.val.comp (staircaseSimplex (concatPerms 0)),
    p.val.comp (staircaseSimplex (concatPerms 1)),
    p.val.comp (staircaseSimplex (concatPerms 2)),
    p.val.comp (staircaseSimplex (concatPerms 3)),
    p.val.comp (staircaseSimplex (concatPerms 4)),
    p.val.comp (staircaseSimplex (concatPerms 5))]

private theorem concatEnd_sum {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    (∑ k : Fin 18, concatEndSigns k • singularSimplexChain
      ((GenLoop.transAt (0 : Fin 3) p q).val.comp
        (concatAffineSimplex (concatEndFaces k)))) =
      hurewiczCubeChain q - hurewiczCubeChain (GenLoop.transAt (0 : Fin 3) p q) +
        hurewiczCubeChain p := by
  have hu (k : Fin 6) :
      (GenLoop.transAt (0 : Fin 3) p q).val.comp
        (concatAffineSimplex (concatEndFaces ⟨k.val, by omega⟩)) =
        q.val.comp (staircaseSimplex (concatPerms k)) := by
    rw [concatEnd_upper, ← ContinuousMap.comp_assoc, concat_half_upper]
  have hf (k : Fin 6) :
      (GenLoop.transAt (0 : Fin 3) p q).val.comp
        (concatAffineSimplex (concatEndFaces ⟨6 + k.val, by omega⟩)) =
        (GenLoop.transAt (0 : Fin 3) p q).val.comp (staircaseSimplex (concatPerms k)) := by
    rw [concatEnd_full]
  have hl (k : Fin 6) :
      (GenLoop.transAt (0 : Fin 3) p q).val.comp
        (concatAffineSimplex (concatEndFaces ⟨12 + k.val, by omega⟩)) =
        p.val.comp (staircaseSimplex (concatPerms k)) := by
    rw [concatEnd_lower, ← ContinuousMap.comp_assoc, concat_half_lower]
  have hm (k : Fin 18) :
      (GenLoop.transAt (0 : Fin 3) p q).val.comp
        (concatAffineSimplex (concatEndFaces k)) = concatEndMaps p q k := by
    fin_cases k
    · exact hu (0 : Fin 6)
    · exact hu (1 : Fin 6)
    · exact hu (2 : Fin 6)
    · exact hu (3 : Fin 6)
    · exact hu (4 : Fin 6)
    · exact hu (5 : Fin 6)
    · exact hf (0 : Fin 6)
    · exact hf (1 : Fin 6)
    · exact hf (2 : Fin 6)
    · exact hf (3 : Fin 6)
    · exact hf (4 : Fin 6)
    · exact hf (5 : Fin 6)
    · exact hl (0 : Fin 6)
    · exact hl (1 : Fin 6)
    · exact hl (2 : Fin 6)
    · exact hl (3 : Fin 6)
    · exact hl (4 : Fin 6)
    · exact hl (5 : Fin 6)
  have hs : (∑ k : Fin 18, concatEndSigns k • singularSimplexChain
      ((GenLoop.transAt (0 : Fin 3) p q).val.comp
        (concatAffineSimplex (concatEndFaces k)))) =
      ∑ k : Fin 18, concatEndSigns k • singularSimplexChain (concatEndMaps p q k) := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun f : C(stdSimplex ℝ (Fin 4), X) =>
      concatEndSigns k • singularSimplexChain f) (hm k)
  refine hs.trans ?_
  simp only [hurewiczCubeChain, concat_oriented_sum]
  norm_num [Fin.sum_univ_succ, concatEndSigns, concatEndMaps]
  abel

private theorem concatPrismChain_boundary {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    concatPrismChain p q ≫ (IntegralChains X).d 4 3 =
      hurewiczCubeChain q - hurewiczCubeChain (GenLoop.transAt (0 : Fin 3) p q) +
        hurewiczCubeChain p := by
  rw [concatPrismChain_boundary_table, concatEnd_sum,
    concatSide_sum_zero, add_zero]


private theorem hurewiczCubeClass_transAt {X : Type u} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    hurewiczCubeClass (GenLoop.transAt (0 : Fin 3) p q) =
      hurewiczCubeClass p + hurewiczCubeClass q := by
  let K := IntegralChains X
  let c := GenLoop.transAt (0 : Fin 3) p q
  let z (r : GenLoop (Fin 3) X x) : integralCoefficients ⟶ K.cycles 3 :=
    K.liftCycles (hurewiczCubeChain r) 2
      ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary r)
  have hb : hurewiczCubeChain c - (hurewiczCubeChain p + hurewiczCubeChain q) =
      (-concatPrismChain p q) ≫ K.d 4 3 := by
    rw [Preadditive.neg_comp, concatPrismChain_boundary]
    dsimp only [c]
    abel
  have hz : z c - (z p + z q) = K.liftCycles
      (hurewiczCubeChain c - (hurewiczCubeChain p + hurewiczCubeChain q)) 2
      ((ComplexShape.down ℕ).next_eq' (by rfl))
      (by rw [hb, Category.assoc, K.d_comp_d, comp_zero]) := by
    apply (cancel_mono (K.iCycles 3)).1
    simp only [Preadditive.sub_comp, Preadditive.add_comp, z,
      HomologicalComplex.liftCycles_i]
  have hzero : (z c - (z p + z q)) ≫ K.homologyπ 3 = 0 := by
    rw [hz]
    exact K.liftCycles_homologyπ_eq_zero_of_boundary _ 2
      ((ComplexShape.down ℕ).next_eq' (by rfl)) (-concatPrismChain p q) hb
  have he : z c ≫ K.homologyπ 3 = z p ≫ K.homologyπ 3 + z q ≫ K.homologyπ 3 := by
    simpa only [Preadditive.sub_comp, Preadditive.add_comp, sub_eq_zero] using hzero
  exact congrArg (fun f : integralCoefficients ⟶ IntegralHomology X 3 => f (ULift.up 1)) he


theorem hurewiczThree_mul (c d : HomotopyGroup (Fin 3) X x) :
    hurewiczThree x (c * d) = hurewiczThree x c + hurewiczThree x d := by
  induction c using Quotient.inductionOn with | h p =>
    induction d using Quotient.inductionOn with | h q =>
      have hm : ((· * ·) : _ → _ → HomotopyGroup (Fin 3) X x) ⟦p⟧ ⟦q⟧ =
          (⟦GenLoop.transAt (0 : Fin 3) q p⟧ : HomotopyGroup (Fin 3) X x) :=
        HomotopyGroup.mul_spec (i := (0 : Fin 3)) (p := p) (q := q)
      exact (congrArg (hurewiczThree x) hm).trans
        ((hurewiczCubeClass_transAt q p).trans (add_comm _ _))

theorem hurewiczThree_natural (f : C(X, Y)) (c : HomotopyGroup (Fin 3) X x) :
    hurewiczThree (f x) (basedHomotopyMap f x c) =
      integralHomologyMap 3 f (hurewiczThree x c) := by
  induction c using Quotient.inductionOn with | h c =>
    let F : IntegralChains X ⟶ IntegralChains Y := integralChainsFunctor.map (TopCat.ofHom f)
    have he :
        (IntegralChains X).liftCycles (hurewiczCubeChain c) 2
          ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary c) ≫
          (IntegralChains X).homologyπ 3 ≫ HomologicalComplex.homologyMap F 3 =
        (IntegralChains Y).liftCycles (hurewiczCubeChain (genLoopPostcompose f c)) 2
          ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary _) ≫
          (IntegralChains Y).homologyπ 3 := by
      rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
        HomologicalComplex.liftCycles_comp_cyclesMap]
      apply congrArg (fun k : integralCoefficients ⟶ (IntegralChains Y).cycles 3 =>
        k ≫ (IntegralChains Y).homologyπ 3)
      apply (cancel_mono ((IntegralChains Y).iCycles 3)).1
      simp only [HomologicalComplex.liftCycles_i]
      exact hurewiczCubeChain_natural f c
    exact (congrArg (fun k : integralCoefficients ⟶ IntegralHomology Y 3 => k (ULift.up 1)) he).symm

def hurewiczThreeHom (x : X) :
    HomotopyGroup (Fin 3) X x →* Multiplicative (IntegralHomology X 3) where
  toFun c := Multiplicative.ofAdd (hurewiczThree x c)
  map_one' := hurewiczThree_one x
  map_mul' := hurewiczThree_mul

theorem hurewiczThree_zpow (c : HomotopyGroup (Fin 3) X x) (z : ℤ) :
    hurewiczThree x (c ^ z) = z • hurewiczThree x c := by
  exact congrArg Multiplicative.toAdd ((hurewiczThreeHom x).map_zpow c z)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
