import DifferentialGeometry.Topology.Homology.SimplexDegreeChainLevel
import DifferentialGeometry.Topology.Homology.LocalCharts

noncomputable section
open CategoryTheory CategoryTheory.Limits Set AlgebraicTopology
open scoped Simplicial

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency false in
private theorem relative_simplex_chain_map (g : C(X, Y)) {A : Set X} {B : Set Y}
    (hg : MapsTo g A B) (σ : C(stdSimplex ℝ (Fin 4), X)) :
    (integralSimplexChain 3 σ ≫ (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion A))).f 3) ≫ (integralRelativeChainMap g hg).f 3 =
      integralSimplexChain 3 (g.comp σ) ≫
        (cokernel.π (integralSingularChainMap (singularSubspaceInclusion B))).f 3 := by
  have hnat := congrArg (fun k => k.f 3) (integralRelativeChainMap_π g hg)
  simp only [HomologicalComplex.comp_f] at hnat
  rw [Category.assoc, hnat, ← Category.assoc]
  congr 1
  have h := SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom g))
    integralSingularCoefficients ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋3⦌)).symm σ)
  exact h

theorem integralRelativeHomologyMap_simplexLocalClass
    (g : C(X, Y)) (p : X) (q : Y)
    (hg : MapsTo g ({p}ᶜ : Set X) ({q}ᶜ : Set Y))
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (t : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i t) ≠ p) :
    integralRelativeHomologyMap 3 g hg (simplexLocalClass p σ hσ) =
      simplexLocalClass q (g.comp σ) (fun i t => hg (hσ i t)) := by
  have hchain := relative_simplex_chain_map g hg σ
  unfold simplexLocalClass
  generalize_proofs _ _ _ _ hpcycle _ _ _ hqcycle
  change (HomologicalComplex.homologyMap (integralRelativeChainMap g hg) 3).hom _ = _
  rw [chainComplex_homologyMap_liftCycles_apply (integralRelativeChainMap g hg) 2 _ hpcycle
    (hchain.symm ▸ hqcycle)]
  exact congrArg (fun k : integralSingularCoefficients ⟶ (integralRelativeChains ({q}ᶜ : Set Y)).homology 3 =>
    k (ULift.up 1)) (chainComplex_liftCycles_homologyπ_congr 2 _ _ _ _ hchain)

theorem integralLocalHomologyHomeomorphIso_simplexLocalClass
    (g : X ≃ₜ Y) (p : X) (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    (integralLocalHomologyHomeomorphIso 3 g p).hom.hom (simplexLocalClass p σ hσ) =
      simplexLocalClass (g p) ((⟨g, g.continuous⟩ : C(X, Y)).comp σ)
        (fun i q h => hσ i q (g.injective h)) := by
  exact integralRelativeHomologyMap_simplexLocalClass ⟨g, g.continuous⟩ p (g p) (fun _ hy => g.injective.ne hy) σ hσ

theorem integralLocalHomologyNeighborhoodIso_simplexLocalClass [T1Space X]
    (U : Set X) (hU : IsOpen U) (p : X) (hp : p ∈ U)
    (σ : C(stdSimplex ℝ (Fin 4), U))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      σ (orientedSimplexFace i q) ≠ (⟨p, hp⟩ : U)) :
    (integralLocalHomologyNeighborhoodIso 3 p U hU hp).hom.hom
      (simplexLocalClass (⟨p, hp⟩ : U) σ hσ) =
      simplexLocalClass p ((singularSubspaceInclusion U).comp σ)
        (fun i q h => hσ i q (Subtype.ext h)) := by
  exact integralRelativeHomologyMap_simplexLocalClass (singularSubspaceInclusion U) ⟨p, hp⟩ p _ σ hσ

theorem integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass
    [T1Space X] [T1Space Y]
    (e : OpenPartialHomeomorph X Y) (p : X) (hp : p ∈ e.source)
    (σ : C(stdSimplex ℝ (Fin 4), X)) (hσsource : ∀ q, σ q ∈ e.source)
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    (integralLocalHomologyOpenPartialHomeomorphIso 3 e p hp).hom.hom
      (simplexLocalClass p σ hσ) =
      simplexLocalClass (e p)
        ⟨fun q => e (σ q), e.continuousOn.comp_continuous σ.continuous hσsource⟩
        (fun i q h => hσ i q (e.injOn (hσsource _) hp h)) := by
  let σU : C(stdSimplex ℝ (Fin 4), e.source) :=
    ⟨fun q => ⟨σ q, hσsource q⟩, σ.continuous.subtype_mk hσsource⟩
  have hσU : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      σU (orientedSimplexFace i q) ≠ (⟨p, hp⟩ : e.source) :=
    fun i q h => hσ i q (congrArg Subtype.val h)
  have hU : (integralLocalHomologyNeighborhoodIso 3 p e.source e.open_source hp).hom.hom
      (simplexLocalClass (⟨p, hp⟩ : e.source) σU hσU) = simplexLocalClass p σ hσ :=
    integralLocalHomologyNeighborhoodIso_simplexLocalClass e.source e.open_source p hp σU hσU
  rw [← hU]
  change (integralLocalHomologyNeighborhoodIso 3 (e p) e.target e.open_target
    (e.map_source hp)).hom.hom
      ((integralLocalHomologyHomeomorphIso 3 e.toHomeomorphSourceTarget
        (⟨p, hp⟩ : e.source)).hom.hom
          ((integralLocalHomologyNeighborhoodIso 3 p e.source e.open_source hp).inv.hom
            ((integralLocalHomologyNeighborhoodIso 3 p e.source e.open_source hp).hom.hom
              (simplexLocalClass (⟨p, hp⟩ : e.source) σU hσU)))) = _
  rw [Iso.hom_inv_id_apply, integralLocalHomologyHomeomorphIso_simplexLocalClass]
  exact integralLocalHomologyNeighborhoodIso_simplexLocalClass e.target e.open_target (e p)
    (e.map_source hp) _ _

end DifferentialGeometry.Topology.SimplexDegree
