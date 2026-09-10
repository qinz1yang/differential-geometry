import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Compactification.OnePoint.Sphere
import DifferentialGeometry.Topology.SphereSeparation.JordanBrouwer
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open scoped Manifold ContDiff Topology

namespace Poincare.Topology.SphereSeparation


abbrev integerDual (M : ModuleCat ℤ) := Module.Dual ℤ M

def dualDifferential {M N : ModuleCat ℤ} (d : N ⟶ M) :
    integerDual M →ₗ[ℤ] integerDual N :=
  Module.Dual.transpose d.hom

@[simp]
theorem dualDifferential_apply {M N : ModuleCat ℤ} (d : N ⟶ M)
    (f : integerDual M) (x : N) :
    dualDifferential d f x = f (d x) :=
  rfl


noncomputable def dualCochainComplex (C : ChainComplex (ModuleCat ℤ) ℕ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of
    (fun n => ModuleCat.of ℤ (integerDual (C.X n)))
    (fun n => ModuleCat.ofHom (dualDifferential (C.d (n + 1) n)))
    (fun n => by
      ext f x
      change f (C.d (n + 1) n (C.d (n + 2) (n + 1) x)) = (0 : ℤ)
      have hdd : C.d (n + 2) (n + 1) ≫ C.d (n + 1) n = 0 :=
        C.d_comp_d (n + 2) (n + 1) n
      have hx : C.d (n + 1) n (C.d (n + 2) (n + 1) x) = 0 := by
        change (C.d (n + 2) (n + 1) ≫ C.d (n + 1) n) x = 0
        rw [hdd]
        rfl
      rw [hx]
      exact map_zero f)


noncomputable def singularCochainComplex (X : TopCat) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  dualCochainComplex
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X)

noncomputable def singularCohomology (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  (singularCochainComplex X).homology n


noncomputable def dualCochainMap {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (f : C ⟶ D) :
    dualCochainComplex D ⟶ dualCochainComplex C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (dualDifferential (f.f n)))
    (fun n => by
      dsimp only [dualCochainComplex]
      simp only [CochainComplex.of_d]
      ext φ x
      change φ (f.f n (C.d (n + 1) n x)) =
        φ (D.d (n + 1) n (f.f (n + 1) x))
      have hcomm := f.comm (n + 1) n
      have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcomm) x
      exact congrArg φ hx.symm)


noncomputable def singularCochainMap {X Y : TopCat} (f : X ⟶ Y) :
    singularCochainComplex Y ⟶ singularCochainComplex X :=
  dualCochainMap
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map f)

@[simp]
theorem dualCochainMap_id (C : ChainComplex (ModuleCat ℤ) ℕ) :
    dualCochainMap (𝟙 C) = 𝟙 (dualCochainComplex C) := by
  apply HomologicalComplex.hom_ext
  intro n
  ext φ
  rfl

@[simp]
theorem dualCochainMap_comp
    {C D E : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (g : D ⟶ E) :
    dualCochainMap (f ≫ g) = dualCochainMap g ≫ dualCochainMap f := by
  apply HomologicalComplex.hom_ext
  intro n
  ext φ
  rfl

noncomputable def dualCochainIso
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (e : C ≅ D) :
    dualCochainComplex D ≅ dualCochainComplex C where
  hom := dualCochainMap e.hom
  inv := dualCochainMap e.inv
  hom_inv_id := by
    rw [← dualCochainMap_comp, e.inv_hom_id, dualCochainMap_id]
  inv_hom_id := by
    rw [← dualCochainMap_comp, e.hom_inv_id, dualCochainMap_id]

noncomputable def singularCochainIsoOfHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    singularCochainComplex (TopCat.of Y) ≅
      singularCochainComplex (TopCat.of X) :=
  dualCochainIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e))


noncomputable def singularCohomologyIsoOfHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    singularCohomology (TopCat.of Y) n ≅
      singularCohomology (TopCat.of X) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
    (singularCochainIsoOfHomeomorph e)



noncomputable def finTwoAugmentationKernelEquivInt :
    LinearMap.ker (finsuppAugmentation (Fin 2)) ≃ₗ[ℤ] ℤ where
  toFun x := x.1 0
  invFun z := ⟨Finsupp.single 0 z - Finsupp.single 1 z, by simp⟩
  map_add' x y := by simp
  map_smul' z x := by simp
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · have hx := x.2
      simp only [LinearMap.mem_ker] at hx
      change finsuppAugmentation (Fin 2) x.1 = 0 at hx
      rw [show finsuppAugmentation (Fin 2) x.1 = x.1 0 + x.1 1 by
        classical
        simp [finsuppAugmentation, Finsupp.sum_fintype]] at hx
      simpa using (eq_neg_of_add_eq_zero_right hx).symm
  right_inv z := by simp

theorem finsuppAugmentation_domLCongr {ι κ : Type*} (e : ι ≃ κ)
    (x : ι →₀ ℤ) :
    finsuppAugmentation κ
        ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) x) =
      finsuppAugmentation ι x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      calc
        finsuppAugmentation κ
            ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) (f + g)) =
            finsuppAugmentation κ
              ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) f +
                (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) g) := by rw [map_add]
        _ = finsuppAugmentation κ
              ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) f) +
            finsuppAugmentation κ
              ((Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) g) := by rw [map_add]
        _ = finsuppAugmentation ι f + finsuppAugmentation ι g := by rw [hf, hg]
        _ = finsuppAugmentation ι (f + g) := by rw [map_add]
  | single i z => simp

noncomputable def augmentationKernelCongr {ι κ : Type*} (e : ι ≃ κ) :
    LinearMap.ker (finsuppAugmentation ι) ≃ₗ[ℤ]
      LinearMap.ker (finsuppAugmentation κ) where
  toFun x := ⟨(Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) x.1, by
    rw [LinearMap.mem_ker]
    rw [finsuppAugmentation_domLCongr]
    exact x.2⟩
  invFun x := ⟨(Finsupp.domLCongr e.symm : (κ →₀ ℤ) ≃ₗ[ℤ] (ι →₀ ℤ)) x.1, by
    rw [LinearMap.mem_ker]
    rw [finsuppAugmentation_domLCongr]
    exact x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simpa using
      (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).map_add x.1 y.1
  map_smul' z x := by
    apply Subtype.ext
    exact
      (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).map_smul z x.1
  left_inv x := by
    apply Subtype.ext
    exact (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact (Finsupp.domLCongr e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)).apply_symm_apply x.1

noncomputable def augmentationKernelEquivIntOfEquivFinTwo {ι : Type*}
    (e : ι ≃ Fin 2) :
    LinearMap.ker (finsuppAugmentation ι) ≃ₗ[ℤ] ℤ :=
  augmentationKernelCongr e ≪≫ₗ finTwoAugmentationKernelEquivInt

noncomputable def reducedSingularH0IsoIntOfZerothHomotopyEquiv
    (X : TopCat) (e : ZerothHomotopy X ≃ Fin 2) :
    reducedSingularH0 X ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularH0IsoAugmentedFinsuppKernel X ≪≫
    (augmentationKernelEquivIntOfEquivFinTwo e).toModuleIso

theorem reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two
    (X : TopCat) [LocallyPathConnectedSpace X]
    (e : ConnectedComponents X ≃ Fin 2) :
    Nonempty (reducedSingularH0 X ≅ ModuleCat.of ℤ ℤ) :=
  ⟨reducedSingularH0IsoIntOfZerothHomotopyEquiv X
    (connectedComponentsEquivZerothHomotopy.symm.trans e)⟩

theorem standardSphere_hasAlexanderDualityH0Certificate :
    HasAlexanderDualityH0Certificate
      (Subtype.val : SphereTwo → EuclideanThree) := by
  have hrange :
      Set.range (Subtype.val : SphereTwo → EuclideanThree) =
        Metric.sphere (0 : EuclideanThree) 1 := by
    ext x
    simp
  let X := ((Metric.sphere (0 : EuclideanThree) 1)ᶜ : Set EuclideanThree)
  let _ : LocallyPathConnectedSpace X :=
    Metric.isClosed_sphere.isOpen_compl.locallyPathConnectedSpace
  have h := reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two
    (TopCat.of X) standardUnitSphereComplementComponents
  unfold HasAlexanderDualityH0Certificate
  rw [hrange]
  have hcompl :
      ({x : EuclideanThree | x ∉ Metric.sphere (0 : EuclideanThree) 1} :
          Set EuclideanThree) =
        (Metric.sphere (0 : EuclideanThree) 1)ᶜ := rfl
  rw [hcompl]
  simpa only [X] using h



def embeddedSphereInOnePoint (e : SphereTwo → EuclideanThree) :
    Set (OnePoint EuclideanThree) :=
  ((↑) : EuclideanThree → OnePoint EuclideanThree) '' Set.range e

theorem compl_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree) :
    (embeddedSphereInOnePoint e)ᶜ =
      ((↑) : EuclideanThree → OnePoint EuclideanThree) ''
          (Set.range e)ᶜ ∪ {OnePoint.infty} := by
  exact OnePoint.compl_image_coe (Set.range e)

theorem isCompact_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsCompact (embeddedSphereInOnePoint e) := by
  exact (isCompact_range he.contMDiff.continuous).image OnePoint.continuous_coe

theorem isClosed_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsClosed (embeddedSphereInOnePoint e) :=
  (isCompact_embeddedSphereInOnePoint e he).isClosed

noncomputable def sphereTwoHomeomorphEmbeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    SphereTwo ≃ₜ embeddedSphereInOnePoint e := by
  let f : SphereTwo → OnePoint EuclideanThree := fun x => (e x : OnePoint EuclideanThree)
  have hf : Topology.IsEmbedding f :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp he.isEmbedding
  have hrange : Set.range f = embeddedSphereInOnePoint e := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hrange)

def alexanderDualityCompactum (e : SphereTwo → EuclideanThree) :
    Set (OnePoint EuclideanThree) :=
  embeddedSphereInOnePoint e ∪ {OnePoint.infty}

theorem compl_alexanderDualityCompactum
    (e : SphereTwo → EuclideanThree) :
    (alexanderDualityCompactum e)ᶜ =
      ((↑) : EuclideanThree → OnePoint EuclideanThree) ''
        (Set.range e)ᶜ := by
  ext y
  induction y using OnePoint.rec with
  | infty => simp [alexanderDualityCompactum, embeddedSphereInOnePoint]
  | coe y => simp [alexanderDualityCompactum, embeddedSphereInOnePoint]


theorem isCompact_alexanderDualityCompactum
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsCompact (alexanderDualityCompactum e) :=
  (isCompact_embeddedSphereInOnePoint e he).union isCompact_singleton


theorem isClosed_alexanderDualityCompactum
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsClosed (alexanderDualityCompactum e) :=
  (isCompact_alexanderDualityCompactum e he).isClosed


def compactumInfinity (e : SphereTwo → EuclideanThree) :
    alexanderDualityCompactum e :=
  ⟨OnePoint.infty, Or.inr rfl⟩


def compactumInfinityNeighborhood (e : SphereTwo → EuclideanThree) :
    Set (alexanderDualityCompactum e) :=
  (Subtype.val : alexanderDualityCompactum e → OnePoint EuclideanThree) ⁻¹'
    (embeddedSphereInOnePoint e)ᶜ

theorem isOpen_compactumInfinityNeighborhood
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    IsOpen (compactumInfinityNeighborhood e) := by
  exact (isClosed_embeddedSphereInOnePoint e he).isOpen_compl.preimage
    continuous_subtype_val


theorem compactumInfinityNeighborhood_eq_singleton
    (e : SphereTwo → EuclideanThree) :
    compactumInfinityNeighborhood e = {compactumInfinity e} := by
  ext x
  constructor
  · intro hx
    apply Subtype.ext
    rcases x.property with hxA | hxInf
    · exact (hx hxA).elim
    · exact hxInf
  · intro hx
    have hxEq : x = compactumInfinity e := by simpa using hx
    subst x
    exact OnePoint.infty_notMem_image_coe

noncomputable def homeomorphSumComplOfIsClopen
    {X : Type*} [TopologicalSpace X] (s : Set X) (hs : IsClopen s) :
    s ⊕ (sᶜ : Set X) ≃ₜ X := by
  classical
  exact (Equiv.Set.sumCompl s).toHomeomorphOfContinuousOpen
    (continuous_sum_dom.mpr ⟨continuous_subtype_val, continuous_subtype_val⟩)
    (isOpenMap_sum.mpr
      ⟨hs.isOpen.isOpenMap_subtype_val,
        hs.isClosed.isOpen_compl.isOpenMap_subtype_val⟩)


noncomputable def compactumInfinityNeighborhoodHomeomorphPUnit
    (e : SphereTwo → EuclideanThree) :
    compactumInfinityNeighborhood e ≃ₜ PUnit :=
  (Homeomorph.setCongr (compactumInfinityNeighborhood_eq_singleton e)).trans
    (Homeomorph.homeomorphOfUnique _ PUnit)

noncomputable def compactumAwayFromInfinityHomeomorphEmbeddedSphere
    (e : SphereTwo → EuclideanThree) :
    ((compactumInfinityNeighborhood e)ᶜ :
        Set (alexanderDualityCompactum e)) ≃ₜ
      embeddedSphereInOnePoint e := by
  let f : ((compactumInfinityNeighborhood e)ᶜ :
      Set (alexanderDualityCompactum e)) → OnePoint EuclideanThree :=
    fun x => x.1.1
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range f = embeddedSphereInOnePoint e := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rcases x.1.property with hxA | hxInf
      · exact hxA
      · exfalso
        exact x.2 (by
          change x.1.1 ∉ embeddedSphereInOnePoint e
          rw [Set.mem_singleton_iff] at hxInf
          rw [hxInf]
          exact OnePoint.infty_notMem_image_coe)
    · intro hy
      let x : alexanderDualityCompactum e := ⟨y, Or.inl hy⟩
      have hx : x ∉ compactumInfinityNeighborhood e := by
        intro hx'
        exact hx' hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hrange)

noncomputable def sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    SphereTwo ⊕ PUnit ≃ₜ alexanderDualityCompactum e := by
  have hclopen : IsClopen (compactumInfinityNeighborhood e) := by
    constructor
    · rw [compactumInfinityNeighborhood_eq_singleton]
      exact isClosed_singleton
    · exact isOpen_compactumInfinityNeighborhood e he
  exact (Homeomorph.sumComm SphereTwo PUnit).trans
    ((Homeomorph.sumCongr
      (compactumInfinityNeighborhoodHomeomorphPUnit e).symm
      ((sphereTwoHomeomorphEmbeddedSphereInOnePoint e he).trans
        (compactumAwayFromInfinityHomeomorphEmbeddedSphere e).symm)).trans
      (homeomorphSumComplOfIsClopen (compactumInfinityNeighborhood e) hclopen))

noncomputable def alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e) :
    singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2 ≅
      singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 :=
  singularCohomologyIsoOfHomeomorph
    (sphereTwoSumPUnitHomeomorphAlexanderDualityCompactum e he) 2

theorem hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hduality : Nonempty
      (reducedSingularH0
          (TopCat.of {x : EuclideanThree | x ∉ Set.range e}) ≅
        singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2))
    (hsphere : Nonempty
      (singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 ≅
        ModuleCat.of ℤ ℤ)) :
    HasAlexanderDualityH0Certificate e := by
  obtain ⟨duality⟩ := hduality
  obtain ⟨sphereCohomology⟩ := hsphere
  exact ⟨duality ≪≫
    alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit e he ≪≫
    sphereCohomology⟩

noncomputable def onePointEuclideanThreeHomeomorphSphereThree :
    OnePoint EuclideanThree ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  onePointEquivSphereOfFinrankEq (by
    norm_num [EuclideanThree, Module.finrank_fin_fun])

theorem infty_mem_compl_embeddedSphereInOnePoint
    (e : SphereTwo → EuclideanThree) :
    OnePoint.infty ∈ (embeddedSphereInOnePoint e)ᶜ := by
  exact OnePoint.infty_notMem_image_coe

noncomputable def embeddedSphereInOnePointCohomologyIsoSphereTwo
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (n : ℕ) :
    singularCohomology (TopCat.of (embeddedSphereInOnePoint e)) n ≅
      singularCohomology (TopCat.of SphereTwo) n :=
  singularCohomologyIsoOfHomeomorph
    (sphereTwoHomeomorphEmbeddedSphereInOnePoint e he) n

end Poincare.Topology.SphereSeparation
