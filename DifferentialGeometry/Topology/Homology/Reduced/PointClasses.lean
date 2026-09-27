import DifferentialGeometry.Topology.Homology.Coefficients

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k) (X : TopCat.{u}) (x y : X)

private def pointDifferenceChain : R ⟶ (augmentedSingularChainComplex R X).X 1 :=
  (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x) -
    (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm y)

private theorem pointDifferenceChain_augmentation :
    pointDifferenceChain R X x y ≫ (augmentedSingularChainComplex R X).d 1 0 = 0 := by
  change ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x) -
    (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm y)) ≫
      singularAugmentation R X = 0
  simp [Preadditive.sub_comp]

def reducedSingularPointDifference : R ⟶ reducedSingularHomology R X 0 :=
  (augmentedSingularChainComplex R X).liftCycles (i := 1)
    (pointDifferenceChain R X x y) 0 (by simp) (pointDifferenceChain_augmentation R X x y) ≫
      (augmentedSingularChainComplex R X).homologyπ 1

@[reassoc]
theorem reducedSingularPointDifference_zeroIso :
    reducedSingularPointDifference R X x y ≫ (reducedSingularHomologyZeroIso R X).hom ≫
        ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom).subtype =
      ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x) -
        (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm y)) ≫
        singularZeroProjection R X :=
  reducedSingularHomologyZeroIso_cycle R X
    (pointDifferenceChain R X x y) (pointDifferenceChain_augmentation R X x y)

private theorem point_projection (z : X) :
    (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm z) ≫
        singularZeroProjection R X ≫ (TopCat.singularHomology₀Iso X R).hom =
      Sigma.ι (fun _ : ZerothHomotopy X => R) (ZerothHomotopy.mk z) := by
  change _ ≫ singularZeroProjection R X ≫
    ((TopCat.toSSet.obj X).homology₀Iso R).hom ≫
    (sigmaConst.obj R).map TopCat.zerothHomotopyEquiv.toIso.inv = _
  rw [← Category.assoc, ι_singularZeroProjection]
  simp

@[reassoc]
theorem reducedSingularPointDifference_coordinates :
    reducedSingularPointDifference R X x y ≫ (reducedSingularHomologyZeroIso R X).hom ≫
        ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom).subtype ≫
        (TopCat.singularHomology₀Iso X R).hom =
      Sigma.ι (fun _ : ZerothHomotopy X => R) (ZerothHomotopy.mk x) -
        Sigma.ι (fun _ : ZerothHomotopy X => R) (ZerothHomotopy.mk y) := by
  exact (reducedSingularPointDifference_zeroIso_assoc R X x y
    (TopCat.singularHomology₀Iso X R).hom).trans (by
      simpa! only [Preadditive.sub_comp, Category.assoc] using
        congrArg₂ (· - ·) (point_projection R X x) (point_projection R X y))

theorem reducedSingularPointDifference_injective (hxy : ¬ Joined x y) :
    Function.Injective (reducedSingularPointDifference R X x y) := by
  classical
  have hcomponents : ZerothHomotopy.mk x ≠ ZerothHomotopy.mk y :=
    fun h => hxy (Quotient.exact h)
  let c : (∐ fun _ : ZerothHomotopy X => R) ⟶ R :=
    Sigma.desc (fun z => if z = ZerothHomotopy.mk x then 𝟙 R else 0)
  let g : reducedSingularHomology R X 0 ⟶ R :=
    (reducedSingularHomologyZeroIso R X).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom).subtype ≫
      (TopCat.singularHomology₀Iso X R).hom ≫ c
  have hleft : reducedSingularPointDifference R X x y ≫ g = 𝟙 R := by
    change reducedSingularPointDifference R X x y ≫
      (reducedSingularHomologyZeroIso R X).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom).subtype ≫
      (TopCat.singularHomology₀Iso X R).hom ≫ c = _
    exact (reducedSingularPointDifference_coordinates_assoc R X x y c).trans (by
      simp [c, Preadditive.sub_comp, hcomponents.symm])
  intro a b hab
  have ha : g (reducedSingularPointDifference R X x y a) = a := congr($(hleft) a)
  have hb : g (reducedSingularPointDifference R X x y b) = b := congr($(hleft) b)
  exact ha.symm.trans ((congrArg g hab).trans hb)

theorem reducedSingularPointDifference_ne_zero (hxy : ¬ Joined x y) {a : R} (ha : a ≠ 0) :
    reducedSingularPointDifference R X x y a ≠ 0 := by
  intro h
  apply ha
  exact reducedSingularPointDifference_injective R X x y hxy
    (h.trans (map_zero (reducedSingularPointDifference R X x y).hom).symm)

variable {X} {Y : TopCat.{u}} (f : X ⟶ Y)

private theorem pointDifferenceChain_naturality :
    pointDifferenceChain R X x y ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f 0 =
      pointDifferenceChain R Y (f x) (f y) := by
  change ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x) -
    (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm y)) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f 0 =
    (TopCat.toSSet.obj Y).ιChainComplex (TopCat.toSSetObj₀Equiv.symm (f x)) -
      (TopCat.toSSet.obj Y).ιChainComplex (TopCat.toSSetObj₀Equiv.symm (f y))
  simp only [Preadditive.sub_comp, SSet.ι_chainComplexMap_f]
  rfl

@[reassoc]
theorem reducedSingularPointDifference_naturality :
    reducedSingularPointDifference R X x y ≫ reducedSingularHomologyMap R f 0 =
      reducedSingularPointDifference R Y (f x) (f y) := by
  unfold reducedSingularPointDifference reducedSingularHomologyMap
  rw [Category.assoc, _root_.HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, _root_.HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 1
  apply (cancel_mono ((augmentedSingularChainComplex R Y).iCycles 1)).mp
  simp only [_root_.HomologicalComplex.liftCycles_i]
  exact pointDifferenceChain_naturality R x y f

variable (X)

variable {R} {S : ModuleCat.{u} k} (φ : R ⟶ S)

private theorem pointDifferenceChain_coefficient_naturality :
    pointDifferenceChain R X x y ≫
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map φ).app X).f 0 =
      φ ≫ pointDifferenceChain S X x y := by
  change (Sigma.ι (fun _ : TopCat.toSSet.obj X _⦋0⦌ => R) (TopCat.toSSetObj₀Equiv.symm x) -
      Sigma.ι (fun _ : TopCat.toSSet.obj X _⦋0⦌ => R) (TopCat.toSSetObj₀Equiv.symm y)) ≫
      CategoryTheory.Limits.Sigma.map (fun _ => φ) = φ ≫
    (Sigma.ι (fun _ : TopCat.toSSet.obj X _⦋0⦌ => S) (TopCat.toSSetObj₀Equiv.symm x) -
      Sigma.ι (fun _ : TopCat.toSSet.obj X _⦋0⦌ => S) (TopCat.toSSetObj₀Equiv.symm y))
  simp [Preadditive.sub_comp, Preadditive.comp_sub]

@[reassoc]
theorem reducedSingularPointDifference_coefficient_naturality :
    reducedSingularPointDifference R X x y ≫ reducedSingularHomologyCoefficientMap φ X 0 =
      φ ≫ reducedSingularPointDifference S X x y := by
  unfold reducedSingularPointDifference reducedSingularHomologyCoefficientMap
  rw [Category.assoc, _root_.HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, _root_.HomologicalComplex.liftCycles_comp_cyclesMap,
    ← Category.assoc, _root_.HomologicalComplex.comp_liftCycles]
  congr 1
  apply (cancel_mono ((augmentedSingularChainComplex S X).iCycles 1)).mp
  simp only [_root_.HomologicalComplex.liftCycles_i]
  exact pointDifferenceChain_coefficient_naturality X x y φ

end DifferentialGeometry.Homology
