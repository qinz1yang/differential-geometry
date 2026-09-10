import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

namespace DifferentialGeometry.SSet

variable {k : Type u} [Ring k]

def realizationChainMap (X : _root_.SSet.{u}) (R : ModuleCat.{u} k) :
    X.chainComplex R ⟶
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj
        (_root_.SSet.toTop.obj X) :=
  _root_.SSet.chainComplexMap (sSetTopAdj.unit.app X) R


theorem realizationChainMap_naturality {X Y : _root_.SSet.{u}} (f : X ⟶ Y)
    (R : ModuleCat.{u} k) :
    _root_.SSet.chainComplexMap f R ≫ realizationChainMap Y R =
      realizationChainMap X R ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
          (_root_.SSet.toTop.map f) := by
  have h : f ≫ sSetTopAdj.unit.app Y = sSetTopAdj.unit.app X ≫
      TopCat.toSSet.map (_root_.SSet.toTop.map f) := sSetTopAdj.unit.naturality f
  change (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map f) ≫
    (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map
      (sSetTopAdj.unit.app Y)) = _
  rw [← Functor.map_comp, h]
  exact Functor.map_comp _ _ _

theorem ι_realizationChainMap_f (X : _root_.SSet.{u}) (R : ModuleCat.{u} k)
    {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (realizationChainMap X R).f n =
      (TopCat.toSSet.obj (_root_.SSet.toTop.obj X)).ιChainComplex
        ((sSetTopAdj.unit.app X).app _ x) :=
  _root_.SSet.ι_chainComplexMap_f _ _ _ R x


theorem homologyMap_homology₀ε {X Y : _root_.SSet.{u}} (f : X ⟶ Y) (R : ModuleCat.{u} k) :
    _root_.SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  apply (cancel_epi ((X.chainComplex R).homologyπ 0)).mp
  apply (cancel_epi ((X.chainComplex R).cycles₀Iso.inv)).mp
  apply X.chainComplex_hom_ext
  intro x
  have hX : X.ιChainComplex x ≫ (X.chainComplex R).cycles₀Iso.inv =
      (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((X.chainComplex R).iCycles 0)).mp
    simp
  rw [← Category.assoc, hX]
  simp only [_root_.SSet.homologyMap, HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  simp only [_root_.SSet.ι_chainComplexMap_f,
    _root_.SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε]
  rw [← Category.assoc, hX]
  simp


theorem isConnected_stdSimplex (n : ℕ) : (Δ[n] : _root_.SSet.{u}).IsConnected := by
  let ed := _root_.SSet.Augmented.StandardSimplex.extraDegeneracy.{u} ⦋n⦌
  let v : (Δ[n] : _root_.SSet.{u}) _⦋0⦌ := ed.s' (default : terminal (Type u))
  have hv (x : (Δ[n] : _root_.SSet.{u}) _⦋0⦌) : _root_.SSet.π₀.mk v = _root_.SSet.π₀.mk x := by
    have h := _root_.SSet.π₀.sound (_root_.SSet.Edge.mk' (ed.s 0 x))
    have h0 : (Δ[n] : _root_.SSet.{u}).δ 0 (ed.s 0 x) = x :=
      ConcreteCategory.congr_hom (ed.s_comp_δ₀ 0) x
    have h1 : (Δ[n] : _root_.SSet.{u}).δ 1 (ed.s 0 x) = v := by
      have h := ConcreteCategory.congr_hom ed.s₀_comp_δ₁ x
      have ha : @Eq (terminal (Type u))
          ((_root_.SSet.Augmented.stdSimplex.obj ⦋n⦌).hom.app (Opposite.op ⦋0⦌) x) default :=
        Subsingleton.elim _ _
      exact h.trans (congrArg (fun p : terminal (Type u) => ed.s' p) ha)
    change _root_.SSet.π₀.mk ((Δ[n] : _root_.SSet.{u}).δ 1 (ed.s 0 x)) =
      _root_.SSet.π₀.mk ((Δ[n] : _root_.SSet.{u}).δ 0 (ed.s 0 x)) at h
    rwa [h0, h1] at h
  refine { allEq := ?_, nonempty := ⟨v⟩ }
  intro x y
  obtain ⟨x, rfl⟩ := _root_.SSet.π₀.mk_surjective x
  obtain ⟨y, rfl⟩ := _root_.SSet.π₀.mk_surjective y
  exact (hv x).symm.trans (hv y)

theorem isZero_homology_stdSimplex (n m : ℕ) (hm : m ≠ 0) (R : ModuleCat.{u} k) :
    IsZero ((Δ[n] : _root_.SSet.{u}).homology (C := ModuleCat.{u} k) R m) := by
  let e : HomotopyEquiv ((Δ[n] : _root_.SSet.{u}).chainComplex R)
      ((ChainComplex.single₀ (ModuleCat.{u} k)).obj (∐ fun (_ : terminal (Type u)) => R)) :=
    ((_root_.SSet.Augmented.StandardSimplex.extraDegeneracy ⦋n⦌).map (sigmaConst.obj R)).homotopyEquiv
  have hz : IsZero (((ChainComplex.single₀ (ModuleCat.{u} k)).obj
      (∐ fun (_ : terminal (Type u)) => R)).X m) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 _ m hm
  exact (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology.of_iso (e.toHomologyIso m)

private theorem isZero_homology_toSSet_of_contractible (X : TopCat.{u}) [ContractibleSpace X]
    (R : ModuleCat.{u} k) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((TopCat.toSSet.obj X).homology (C := ModuleCat.{u} k) R n) := by
  let Y : TopCat.{u} := TopCat.of PUnit.{u + 1}
  obtain ⟨e⟩ := ContractibleSpace.hequiv X Y
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R
  let ec : HomotopyEquiv (F.obj X) (F.obj Y) :=
    { hom := F.map (TopCat.ofHom e.toFun)
      inv := F.map (TopCat.ofHom e.invFun)
      homotopyHomInvId := by
        have H : TopCat.Homotopy
            (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
        have h : Homotopy (F.map (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun))
            (F.map (𝟙 X)) := H.singularChainComplexFunctorObjMap R
        rwa [F.map_comp, F.map_id] at h
      homotopyInvHomId := by
        have H : TopCat.Homotopy
            (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
        have h : Homotopy (F.map (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun))
            (F.map (𝟙 Y)) := H.singularChainComplexFunctorObjMap R
        rwa [F.map_comp, F.map_id] at h }
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{u} k) n R Y hn).of_iso (ec.toHomologyIso n)

theorem contractibleSpace_realization_stdSimplex (n : ℕ) :
    ContractibleSpace (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u})) := by
  have : ContractibleSpace (_root_.stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  exact (SimplexCategory.toTopHomeo ⦋n⦌).contractibleSpace

theorem quasiIso_realizationChainMap_stdSimplex (n : ℕ) (R : ModuleCat.{u} k) :
    QuasiIso (realizationChainMap (Δ[n] : _root_.SSet.{u}) R) := by
  have : (Δ[n] : _root_.SSet.{u}).IsConnected := isConnected_stdSimplex n
  have : ContractibleSpace (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u})) :=
    contractibleSpace_realization_stdSimplex n
  have : (TopCat.toSSet.obj (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))).IsConnected :=
    inferInstance
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hm : m = 0
  · subst m
    have : IsIso ((TopCat.toSSet.obj
        (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))).homology₀ε
          (C := ModuleCat.{u} k) R) := inferInstance
    have h := homologyMap_homology₀ε (X := Δ[n])
      (Y := TopCat.toSSet.obj (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u})))
      (sSetTopAdj.unit.app (Δ[n] : _root_.SSet.{u})) R
    have : IsIso (_root_.SSet.homologyMap (sSetTopAdj.unit.app (Δ[n] : _root_.SSet.{u})) R 0 ≫
        (TopCat.toSSet.obj (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))).homology₀ε R) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right
      (_root_.SSet.homologyMap (sSetTopAdj.unit.app (Δ[n] : _root_.SSet.{u})) R 0)
      ((TopCat.toSSet.obj (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))).homology₀ε
        (C := ModuleCat.{u} k) R)
  · exact (isZero_homology_stdSimplex n m hm R).isIso
      (isZero_homology_toSSet_of_contractible _ R m hm) _

end DifferentialGeometry.SSet
