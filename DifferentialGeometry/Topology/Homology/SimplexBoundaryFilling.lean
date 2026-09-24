import DifferentialGeometry.Topology.Homology.ModuleHomologyClasses
import DifferentialGeometry.Topology.Homology.EuclideanSimplexGeneratorComputation

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology Simplicial

namespace DifferentialGeometry.Topology

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralChainHom_apply_one (n : ℕ) (c : (integralSingularChains X).X n) :
    integralChainHom n c (ULift.up (1 : ℤ)) = c := by
  change (integralChainHom n c).hom (ULift.up (1 : ℤ)) = c
  rw [integralChainHom_hom, LinearMap.comp_apply]
  exact LinearMap.toSpanSingleton_apply_one ℤ _ c

theorem integralChainHom_ext {n : ℕ}
    {M : integralSingularCoefficients ⟶ (integralSingularChains X).X n}
    {c : (integralSingularChains X).X n} (h : M (ULift.up (1 : ℤ)) = c) :
    M = integralChainHom n c := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rcases y with ⟨k⟩
  have hk : (ULift.up k : ULift.{u} ℤ) = k • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  rw [hk, map_zsmul, map_zsmul, h, integralChainHom_apply_one]

theorem integralChainHom_sub (n : ℕ) (c d : (integralSingularChains X).X n) :
    integralChainHom n (c - d) = integralChainHom n c - integralChainHom n d := by
  apply ModuleCat.hom_ext
  have hsub : LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) (c - d) =
      LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) c -
        LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) d := by
    apply LinearMap.ext
    intro r
    simp only [LinearMap.sub_apply, LinearMap.toSpanSingleton_apply, smul_sub]
  rw [integralChainHom_hom, ModuleCat.hom_sub, integralChainHom_hom, integralChainHom_hom, hsub,
    LinearMap.sub_comp]

theorem moduleCatCyclesIso_hom_val (S : ShortComplex (ModuleCat.{u} ℤ)) (z : S.cycles) :
    (S.moduleCatCyclesIso.hom z).val = S.iCycles z := by
  have h := congrArg (fun f : S.cycles ⟶ S.X₂ => f z) (ShortComplex.moduleCatCyclesIso_hom_i S)
  simp only [ModuleCat.comp_apply] at h
  exact h

def integralChainLiftCycle (n : ℕ) (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    integralSingularCoefficients ⟶ ((integralSingularChains X).sc (n + 1)).cycles :=
  (integralSingularChains X).liftCycles (integralChainHom (n + 1) c) n
    ((ComplexShape.down ℕ).next_eq' (by rfl))
    (by rw [integralChainHom_d n c, hc, integralChainHom_zero])

theorem integralChainLiftCycle_apply (n : ℕ) (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    (integralSingularChains X).iCycles (n + 1)
      (integralChainLiftCycle n c hc (ULift.up (1 : ℤ))) = c := by
  have h := congrArg (fun f : integralSingularCoefficients ⟶
      (integralSingularChains X).X (n + 1) => f (ULift.up (1 : ℤ)))
    ((integralSingularChains X).liftCycles_i (integralChainHom (n + 1) c) n
      ((ComplexShape.down ℕ).next_eq' (by rfl))
      (by rw [integralChainHom_d n c, hc, integralChainHom_zero]))
  rw [ModuleCat.comp_apply, integralChainHom_apply_one] at h
  rw [integralChainLiftCycle]
  exact h

def integralSingularCycleOfChain (n : ℕ) (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    LinearMap.ker (((integralSingularChains X).sc (n + 1)).g.hom) :=
  ((integralSingularChains X).sc (n + 1)).moduleCatCyclesIso.hom
    (integralChainLiftCycle n c hc (ULift.up 1))

theorem integralSingularCycleOfChain_val (n : ℕ)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    (integralSingularCycleOfChain n c hc).val = c := by
  have h₁ := moduleCatCyclesIso_hom_val ((integralSingularChains X).sc (n + 1))
    (integralChainLiftCycle n c hc (ULift.up 1))
  rw [integralSingularCycleOfChain, h₁]
  exact integralChainLiftCycle_apply n c hc

theorem integralHomologyClassOf_integralChainHom (n : ℕ)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0)
    {hz : integralChainHom (n + 1) c ≫ (integralSingularChains X).d (n + 1) n = 0} :
    integralHomologyClassOf n (integralChainHom (n + 1) c) hz =
      integralHomologyClass n c hc := rfl

theorem integralHomologyClass_eq_moduleHomologyClass (n : ℕ)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    integralHomologyClass n c hc =
      moduleHomologyClass ((integralSingularChains X).sc (n + 1))
        (integralSingularCycleOfChain n c hc) := by
  have h : moduleHomologyClass ((integralSingularChains X).sc (n + 1))
      (integralSingularCycleOfChain n c hc) =
      ((integralSingularChains X).sc (n + 1)).homologyπ
        (integralChainLiftCycle n c hc (ULift.up (1 : ℤ))) := by
    rw [moduleHomologyClass, integralSingularCycleOfChain]
    change (((integralSingularChains X).sc (n + 1)).homologyπ.hom ∘ₗ
        ((integralSingularChains X).sc (n + 1)).moduleCatCyclesIso.inv.hom)
      (((integralSingularChains X).sc (n + 1)).moduleCatCyclesIso.hom
        (integralChainLiftCycle n c hc (ULift.up (1 : ℤ)))) = _
    rw [LinearMap.comp_apply, Iso.hom_inv_id_apply]
  rw [h, integralHomologyClass, integralHomologyClassOf, integralChainLiftCycle,
    ModuleCat.comp_apply]
  rfl

theorem exists_chain_of_integralHomologyClass_eq (n : ℕ)
    (c₁ c₂ : (integralSingularChains X).X (n + 1))
    (h₁ : (integralSingularChains X).d (n + 1) n c₁ = 0)
    (h₂ : (integralSingularChains X).d (n + 1) n c₂ = 0)
    (h : integralHomologyClass n c₁ h₁ = integralHomologyClass n c₂ h₂) :
    ∃ b : (integralSingularChains X).X (n + 2),
      (integralSingularChains X).d (n + 2) (n + 1) b = c₁ - c₂ := by
  have hmod : moduleHomologyClass ((integralSingularChains X).sc (n + 1))
        (integralSingularCycleOfChain n c₁ h₁) =
      moduleHomologyClass ((integralSingularChains X).sc (n + 1))
        (integralSingularCycleOfChain n c₂ h₂) := by
    rw [← integralHomologyClass_eq_moduleHomologyClass n c₁ h₁,
      ← integralHomologyClass_eq_moduleHomologyClass n c₂ h₂]
    exact h
  obtain ⟨b, hb⟩ := (moduleHomologyClass_eq_iff ((integralSingularChains X).sc (n + 1))
    (integralSingularCycleOfChain n c₁ h₁) (integralSingularCycleOfChain n c₂ h₂)).mp hmod
  rw [integralSingularCycleOfChain_val n c₁ h₁,
    integralSingularCycleOfChain_val n c₂ h₂] at hb
  let e := ChainComplex.prev ℕ (n + 1)
  refine ⟨((integralSingularChains X).XIsoOfEq e).hom b, ?_⟩
  have hcomp : (integralSingularChains X).d (n + 2) (n + 1)
      (((integralSingularChains X).XIsoOfEq e).hom b) = c₁ - c₂ := by
    have h₁' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.XIsoOfEq_hom_comp_d (integralSingularChains X) e (n + 1))) b
    simp only [ModuleCat.hom_comp] at h₁'
    exact h₁'.trans hb
  exact hcomp

theorem simplexBoundaryLiftedChain_apply_boundary :
    (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1
      (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) = 0 := by
  have h := congrArg (fun f : integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 1 => f (ULift.up (1 : ℤ)))
    simplexBoundaryLiftedChain_boundary.{u}
  rw [ModuleCat.comp_apply] at h
  simpa using h

theorem integralChainHom_simplexBoundaryLiftedChain :
    integralChainHom 2 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) =
      simplexBoundaryLiftedChain.{u} :=
  (integralChainHom_ext (M := simplexBoundaryLiftedChain.{u})
    (c := simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) rfl).symm

theorem simplexBoundaryLiftedChain_class_eq_integralHomologyClass :
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
        simplexBoundaryLiftedChain_apply_boundary := by
  have hz : integralChainHom 2 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
    rw [integralChainHom_d 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))),
      simplexBoundaryLiftedChain_apply_boundary, integralChainHom_zero]
  exact (integralHomologyClassOf_congr (n := 1)
      (hz := simplexBoundaryLiftedChain_boundary) (hz' := hz)
      integralChainHom_simplexBoundaryLiftedChain.symm).trans
    (integralHomologyClassOf_integralChainHom 1
      (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
      simplexBoundaryLiftedChain_apply_boundary (hz := hz))

theorem squareSphereFundamentalClass_eq_integralHomologyClass :
    squareSphereFundamentalClass.{u} =
      integralHomologyClass 1 squareSphereFundamentalChain squareSphereFundamentalChain_boundary :=
  squareSphereFundamentalClass_eq_classOf.trans
    (integralHomologyClassOf_integralChainHom 1 squareSphereFundamentalChain
      squareSphereFundamentalChain_boundary (hz :=
        integralChainHom_squareSphereFundamentalChain_boundary))

theorem simplexBoundarySphereFilling_iff_exists_filling :
    SimplexBoundarySphereFilling.{u} ↔
      ∃ z : integralSingularCoefficients ⟶
          (integralSingularChains (liftedHomotopySphere.{u} 1)).X 3,
        z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
          simplexBoundaryLiftedChain - integralChainHom 2 squareSphereFundamentalChain := by
  constructor
  · rintro (⟨z, hz | hz⟩)
    · exact ⟨z, hz⟩
    · exact ⟨-z, by rw [Preadditive.neg_comp, hz, neg_sub]⟩
  · rintro ⟨z, hz⟩
    unfold SimplexBoundarySphereFilling
    exact ⟨z, Or.inl hz⟩

theorem class_eq_of_simplexBoundarySphereFilling (h : SimplexBoundarySphereFilling.{u}) :
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      squareSphereFundamentalClass.{u} := by
  obtain ⟨z, hz | hz⟩ := h
  · exact (integralHomologyClassOf_eq_of_sub_eq 1 simplexBoundaryLiftedChain
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain_boundary
      integralChainHom_squareSphereFundamentalChain_boundary z hz.symm).trans
      squareSphereFundamentalClass_eq_classOf.symm
  · exact (integralHomologyClassOf_eq_of_sub_eq 1
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain
      integralChainHom_squareSphereFundamentalChain_boundary simplexBoundaryLiftedChain_boundary
      z hz.symm).symm.trans squareSphereFundamentalClass_eq_classOf

theorem simplexBoundarySphereFilling_of_integralHomologyClass_eq
    (h : integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
        simplexBoundaryLiftedChain_apply_boundary =
      integralHomologyClass 1 squareSphereFundamentalChain squareSphereFundamentalChain_boundary) :
    SimplexBoundarySphereFilling.{u} := by
  obtain ⟨b, hb⟩ := exists_chain_of_integralHomologyClass_eq 1
    (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) squareSphereFundamentalChain
    simplexBoundaryLiftedChain_apply_boundary squareSphereFundamentalChain_boundary h
  unfold SimplexBoundarySphereFilling
  exact ⟨integralChainHom 3 b, Or.inl (by
    rw [integralChainHom_d 2 b, hb, integralChainHom_sub,
      integralChainHom_simplexBoundaryLiftedChain])⟩

theorem simplexBoundarySphereFilling_iff_integralHomologyClass_eq :
    SimplexBoundarySphereFilling.{u} ↔
      integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
          simplexBoundaryLiftedChain_apply_boundary =
        integralHomologyClass 1 squareSphereFundamentalChain
          squareSphereFundamentalChain_boundary :=
  ⟨fun h =>
      simplexBoundaryLiftedChain_class_eq_integralHomologyClass.symm.trans
        ((class_eq_of_simplexBoundarySphereFilling h).trans
          squareSphereFundamentalClass_eq_integralHomologyClass),
    simplexBoundarySphereFilling_of_integralHomologyClass_eq⟩

theorem simplexBoundarySphereFilling_iff_class_eq :
    SimplexBoundarySphereFilling.{u} ↔
      integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
        squareSphereFundamentalClass.{u} :=
  by
    rw [simplexBoundaryLiftedChain_class_eq_integralHomologyClass,
      squareSphereFundamentalClass_eq_integralHomologyClass]
    exact simplexBoundarySphereFilling_iff_integralHomologyClass_eq

theorem not_simplexBoundarySphereFilling_of_class_eq_neg
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u})
    (h : integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      -squareSphereFundamentalClass.{u}) :
    ¬ SimplexBoundarySphereFilling.{u} := by
  intro hf
  have hneg : squareSphereFundamentalClass.{u} = -squareSphereFundamentalClass.{u} :=
    (class_eq_of_simplexBoundarySphereFilling hf).symm.trans h
  obtain ⟨e, he⟩ := hg
  have hcoe := congrArg e hneg
  rw [map_neg, he] at hcoe
  norm_num at hcoe

theorem simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg :
    SimplexBoundarySphereAlignment.{u} ↔
      SimplexBoundarySphereFilling.{u} ∨
        integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          -squareSphereFundamentalClass.{u} := by
  simp only [SimplexBoundarySphereAlignment, simplexBoundarySphereFilling_iff_class_eq]

theorem euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereFilling_or_class_eq_neg
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexClassGenerator.{u} ↔
      SimplexBoundarySphereFilling.{u} ∨
        integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          -squareSphereFundamentalClass.{u} :=
  (euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereAlignment hg).trans
    simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg

end DifferentialGeometry.Topology
