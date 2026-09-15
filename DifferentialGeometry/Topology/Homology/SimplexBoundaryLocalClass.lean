import DifferentialGeometry.Topology.Homology.SimplexBoundaryChain
import DifferentialGeometry.Topology.Homology.SimplexDegreeNaturality
import DifferentialGeometry.Topology.Homology.HurewiczOnePathLoopBridge
import DifferentialGeometry.Topology.Homology.SimplexFaceLocalHomology
import DifferentialGeometry.Topology.Homology.TetrahedronLocalGenerator

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

private theorem simplexChainHom_eq {X : Type u} [TopologicalSpace X]
    (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    integralChainHom n (integralSimplexChain n
      ((integralSingularSimplexEquiv n X).symm σ)) =
      SimplexDegree.integralSimplexChain n σ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rcases y with ⟨k⟩
  have hk : (ULift.up k : ULift.{u} ℤ) = k • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  rw [hk, map_zsmul, map_zsmul]
  congr 1
  exact integralChainHom_apply_one n _

private theorem simplexChain_projection_zero {X : Type u} [TopologicalSpace X]
    (n : ℕ) (A : Set X) (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    (hσ : ∀ t, σ t ∈ A) :
    SimplexDegree.integralSimplexChain n σ ≫ (integralRelativeProjection A).f n = 0 := by
  let τ : C(stdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun t => ⟨σ t, hσ t⟩, σ.continuous.subtype_mk _⟩
  have hchain : SimplexDegree.integralSimplexChain n τ ≫
      (integralSingularChainMap (singularSubspaceInclusion A)).f n =
      SimplexDegree.integralSimplexChain n σ :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A))
      (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSet.map (TopCat.ofHom (singularSubspaceInclusion A)))
      integralSingularCoefficients
      ((TopCat.toSSetObjEquiv (TopCat.of A) (.op ⦋n⦌)).symm τ)
  have hπ : (integralSingularChainMap (singularSubspaceInclusion A)).f n ≫
      (integralRelativeProjection A).f n = 0 :=
    congrArg (fun f => f.f n) (integralRelativeProjection_condition A)
  rw [← hchain]
  erw [Category.assoc, hπ, Limits.comp_zero]

theorem simplexBoundaryFace_ne_face_zero_barycenter (n : ℕ)
    (i : Fin (n + 3)) (hi : i ≠ 0) (q : stdSimplex ℝ (Fin (n + 2))) :
    simplexBoundaryFace.{u} n i q ≠ simplexBoundaryFace n 0 stdSimplex.barycenter := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
  intro h
  have he := congrArg (fun p : ULift.{u} (Simplex.boundary (Fin (n + 3))) =>
    p.down.val.val j.succ) h
  change (stdSimplex.map j.succ.succAbove q).val j.succ =
    (stdSimplex.map (0 : Fin (n + 3)).succAbove stdSimplex.barycenter).val j.succ at he
  rw [Simplex.map_succAbove_apply_pivot] at he
  have hj : (0 : Fin (n + 3)).succAbove j = j.succ := rfl
  rw [← hj, Simplex.map_succAbove_apply_image, stdSimplex.barycenter_apply] at he
  have hn : (0 : ℝ) < Fintype.card (Fin (n + 2)) := by positivity
  exact (ne_of_gt (inv_pos.mpr hn)) he.symm

private theorem integralChainHom_sum_smul {X : Type u} [TopologicalSpace X]
    {ι : Type*} [Fintype ι] (n : ℕ) (a : ι → ℤ)
    (c : ι → (integralSingularChains X).X n) :
    integralChainHom n (∑ i, a i • c i) = ∑ i, a i • integralChainHom n (c i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rcases y with ⟨k⟩
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, integralChainHom_hom, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

theorem simplexBoundaryChain_comp_projection_face_zero (n : ℕ) :
    integralChainHom (n + 1) (simplexBoundaryChain.{u} n) ≫
      (integralRelativeProjection
        ({simplexBoundaryFace n 0 stdSimplex.barycenter}ᶜ :
          Set (ULift.{u} (Simplex.boundary (Fin (n + 3)))))).f (n + 1) =
      SimplexDegree.integralSimplexChain (n + 1) (simplexBoundaryFace n 0) ≫
        (integralRelativeProjection
          ({simplexBoundaryFace n 0 stdSimplex.barycenter}ᶜ :
            Set (ULift.{u} (Simplex.boundary (Fin (n + 3)))))).f (n + 1) := by
  classical
  rw [simplexBoundaryChain, integralChainHom_sum_smul]
  simp_rw [simplexChainHom_eq]
  rw [Preadditive.sum_comp, Finset.sum_eq_single (0 : Fin (n + 3))]
  · simp
  · intro i _ hi
    rw [Linear.smul_comp, simplexChain_projection_zero]
    · exact smul_zero _
    · exact fun q => simplexBoundaryFace_ne_face_zero_barycenter n i hi q
  · exact fun h => (h (Finset.mem_univ _)).elim

private theorem simplexBoundaryFace_zero_faces_ne_barycenter
    (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    simplexBoundaryFace.{u} 2 0 (SimplexDegree.orientedSimplexFace i q) ≠
      simplexBoundaryFace 2 0 stdSimplex.barycenter := by
  intro h
  apply SimplexDegree.tetrahedronIdentitySimplex_face_ne_barycenter.{u} i q
  exact Simplex.liftedFaceToBoundary_injective (0 : Fin 5) h

theorem integralAbsoluteToRelative_simplexBoundaryChain_face_zero :
    integralAbsoluteToRelative 3
      ({simplexBoundaryFace 2 0 stdSimplex.barycenter}ᶜ :
        Set (ULift.{u} (Simplex.boundary (Fin 5))))
      (integralHomologyClass 2 (simplexBoundaryChain 2) (simplexBoundaryChain_boundary 2)) =
      SimplexDegree.simplexLocalClass (simplexBoundaryFace 2 0 stdSimplex.barycenter)
        (simplexBoundaryFace 2 0) simplexBoundaryFace_zero_faces_ne_barycenter := by
  have hz : (integralChainHom 3 (simplexBoundaryChain.{u} 2) ≫
      (integralRelativeProjection
        ({simplexBoundaryFace 2 0 stdSimplex.barycenter}ᶜ :
          Set (ULift.{u} (Simplex.boundary (Fin 5))))).f 3) ≫
      (integralRelativeChains ({simplexBoundaryFace 2 0 stdSimplex.barycenter}ᶜ :
        Set (ULift.{u} (Simplex.boundary (Fin 5))))).d 3 2 = 0 := by
    rw [simplexBoundaryChain_comp_projection_face_zero]
    exact integralRelativeChain_projection_boundary 1 _ _
      (SimplexDegree.puncturedSimplexBoundary _ _ simplexBoundaryFace_zero_faces_ne_barycenter)
      (SimplexDegree.puncturedSimplexBoundary_chain _ _ simplexBoundaryFace_zero_faces_ne_barycenter)
  rw [integralAbsoluteToRelative_homologyClass 2 _ _ _ hz]
  exact integralRelativeClassOf_congr 2 _ (simplexBoundaryChain_comp_projection_face_zero 2)

theorem simplexBoundaryFace_zero_localClass_generator :
    Function.Bijective (fun z : ℤ => z •
      SimplexDegree.simplexLocalClass (simplexBoundaryFace.{u} 2 0 stdSimplex.barycenter)
        (simplexBoundaryFace 2 0) simplexBoundaryFace_zero_faces_ne_barycenter) := by
  let f := integralRelativeHomologyMap 3 (Simplex.liftedFaceToBoundary.{u} (0 : Fin 5))
    (Simplex.liftedFaceToBoundary_mapsTo 0 SimplexDegree.liftedTetrahedronBarycenter)
  have hf : Function.Bijective f :=
    integralRelativeHomologyMap_liftedFaceToBoundary_barycenter_bijective 3 0
  have h := hf.comp SimplexDegree.simplexIdentityLocalClass_generator.{u}
  have heq : (fun z : ℤ => f (z • SimplexDegree.simplexLocalClass
      SimplexDegree.liftedTetrahedronBarycenter SimplexDegree.tetrahedronIdentitySimplex
        SimplexDegree.tetrahedronIdentitySimplex_face_ne_barycenter)) =
      fun z => z • SimplexDegree.simplexLocalClass
        (simplexBoundaryFace 2 0 stdSimplex.barycenter) (simplexBoundaryFace 2 0)
          simplexBoundaryFace_zero_faces_ne_barycenter := by
    funext z
    rw [map_zsmul]
    congr 1
    exact SimplexDegree.integralRelativeHomologyMap_simplexLocalClass
      (Simplex.liftedFaceToBoundary 0) _ _ _ _ _
  exact heq ▸ h

end DifferentialGeometry.Topology
