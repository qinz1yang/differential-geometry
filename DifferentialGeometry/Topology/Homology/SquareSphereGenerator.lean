import DifferentialGeometry.Topology.Homology.CubeSphereLocalHomology
import DifferentialGeometry.Topology.Homology.TriangleLocalDegree
import DifferentialGeometry.Topology.Homology.LiftedSquareBoundaryDegree

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

private def squareTriangleCenter : liftedSquare.{u} :=
  ULift.up ![⟨2 / 3, by norm_num⟩, ⟨1 / 3, by norm_num⟩]

private def squareTriangleCoordinate : C(liftedSquare.{u}, liftedSphereSpace.{u} 0) where
  toFun t := ULift.up (WithLp.toLp 2
    ![1 - (t.down 0 : ℝ) - (t.down 1 : ℝ), (t.down 0 : ℝ) - 2 * (t.down 1 : ℝ)])
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

private theorem squareTriangleCoordinate_center :
    squareTriangleCoordinate squareTriangleCenter = (0 : liftedSphereSpace.{u} 0) := by
  apply ULift.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> norm_num [squareTriangleCoordinate, squareTriangleCenter]

private theorem squareTriangleCoordinate_eq_zero_iff (t : liftedSquare.{u}) :
    squareTriangleCoordinate t = 0 ↔ t = squareTriangleCenter := by
  constructor
  · intro h
    have h0 := congrArg (fun z : liftedSphereSpace.{u} 0 => z.down 0) h
    have h1 := congrArg (fun z : liftedSphereSpace.{u} 0 => z.down 1) h
    change 1 - (t.down 0 : ℝ) - (t.down 1 : ℝ) = 0 at h0
    change (t.down 0 : ℝ) - 2 * (t.down 1 : ℝ) = 0 at h1
    apply ULift.ext
    funext i
    apply Subtype.ext
    fin_cases i <;> dsimp [squareTriangleCenter] <;> linarith
  · rintro rfl
    exact squareTriangleCoordinate_center

private theorem squareTriangleCoordinate_mapsTo :
    MapsTo squareTriangleCoordinate ({squareTriangleCenter}ᶜ : Set (liftedSquare.{u}))
      ({0}ᶜ : Set (liftedSphereSpace.{u} 0)) := by
  intro t ht h
  exact ht ((squareTriangleCoordinate_eq_zero_iff t).mp h)

private theorem squareTriangleCenter_not_mem_boundary :
    squareTriangleCenter ∉ liftedSquareBoundary.{u} := by
  rintro ⟨i, hi⟩
  rcases hi with hi | hi <;>
    have h := congrArg (fun a : unitInterval => (a : ℝ)) hi <;>
    fin_cases i <;> norm_num [squareTriangleCenter] at h

private theorem squareTriangleCenter_mem_cubeInterior :
    squareTriangleCenter.{u}.down ∈ cubeInterior (Fin 2) := by
  rw [cubeInterior_eq_compl_boundary]
  exact squareTriangleCenter_not_mem_boundary.{u}



private theorem squareTriangleCoordinate_lower :
    (squareTriangleCoordinate.{u}.comp liftedSquareUp).comp
      (squareAffineMap 2 ![squareOrigin, squareEast, squareNorthEast]) =
        SimplexDegree.standardTriangleSimplex := by
  apply ContinuousMap.ext
  intro t
  apply ULift.ext
  apply PiLp.ext
  intro i
  have hs := t.property.2
  rw [Fin.sum_univ_three] at hs
  fin_cases i <;>
    simp [squareTriangleCoordinate, liftedSquareUp, squareAffineMap_apply_coe,
      SimplexDegree.standardTriangleSimplex, affineSimplexMap, SimplexDegree.standardTriangleVertex,
      squareOrigin, squareEast, squareNorthEast, squarePoint, Fin.sum_univ_three] <;>
    linarith

private theorem squareTriangleCoordinate_upper_ne_zero (t : stdSimplex ℝ (Fin 3)) :
    (squareTriangleCoordinate.{u}.comp liftedSquareUp)
      (squareAffineMap 2 ![squareOrigin, squareNorth, squareNorthEast] t) ≠ 0 := by
  intro h
  have ht := (squareTriangleCoordinate_eq_zero_iff _).mp h
  have h0 := congrArg (fun z : liftedSquare.{u} => (z.down 0 : ℝ)) ht
  have h1 := congrArg (fun z : liftedSquare.{u} => (z.down 1 : ℝ)) ht
  simp [liftedSquareUp, squareAffineMap_apply_coe, squareTriangleCenter,
    squareOrigin, squareNorth, squareNorthEast, squarePoint, Fin.sum_univ_three] at h0 h1
  linarith [t.property.1 1]

private theorem squareTriangleCoordinate_lower_chain :
    singularChainImageGen 2 (squareTriangleCoordinate.{u}.comp liftedSquareUp)
      (squareTriangleChain squareOrigin squareEast squareNorthEast) =
        SimplexDegree.standardTriangleChain := by
  rw [squareTriangleChain, singularChainImageGen_simplex]
  change integralSimplexChain 2 _ = integralSimplexChain 2 _
  congr 1
  apply (integralSingularSimplexEquiv 2 _).injective
  rw [singularSimplexImageGen_apply_val, squareAffineSimplex_coe]
  exact squareTriangleCoordinate_lower

private theorem squareTriangleCoordinate_upper_mem :
    singularChainImageGen 2 (squareTriangleCoordinate.{u}.comp liftedSquareUp)
      (squareTriangleChain squareOrigin squareNorth squareNorthEast) ∈
        integralSingularChainsIn 2 ({0}ᶜ : Set (liftedSphereSpace.{u} 0)) := by
  rw [squareTriangleChain, singularChainImageGen_simplex]
  apply Submodule.subset_span
  refine ⟨_, ?_, rfl⟩
  rintro _ ⟨t, rfl⟩
  rw [singularSimplexImageGen_apply_val, squareAffineSimplex_coe]
  exact squareTriangleCoordinate_upper_ne_zero t

private theorem integralRelativeProjection_eq_zero_of_mem {X : Type u} [TopologicalSpace X]
    (n : ℕ) (A : Set X) (c : (integralSingularChains X).X n)
    (hc : c ∈ integralSingularChainsIn n A) : (integralRelativeProjection A).f n c = 0 := by
  rw [integralSingularChainsIn_eq_range] at hc
  obtain ⟨z, hz⟩ := hc
  rw [← hz]
  have h := congrArg (fun f : integralSingularChains A ⟶ integralRelativeChains A => f.f n)
    (integralRelativeProjection_condition A)
  exact congrArg (fun f => f z) h

private theorem squareTriangleCoordinate_fundamentalChain_relative :
    (integralRelativeProjection ({0}ᶜ : Set (liftedSphereSpace.{u} 0))).f 2
      ((integralSingularChainMap squareTriangleCoordinate).f 2 liftedSquareFundamentalChain) =
    (integralRelativeProjection ({0}ᶜ : Set (liftedSphereSpace.{u} 0))).f 2
      SimplexDegree.standardTriangleChain := by
  rw [integralSingularChainMap_apply_eq_singularChainImageGen, liftedSquareFundamentalChain]
  change (integralRelativeProjection ({0}ᶜ : Set (liftedSphereSpace.{u} 0))).f 2
    (((singularChainImageGen 2 squareTriangleCoordinate).comp
      (singularChainImageGen 2 liftedSquareUp)) squareFundamentalChain) = _
  rw [← singularChainImageGen_comp, squareFundamentalChain, map_sub, map_sub,
    squareTriangleCoordinate_lower_chain,
    integralRelativeProjection_eq_zero_of_mem 2 _ _ squareTriangleCoordinate_upper_mem, sub_zero]



private theorem integralCoefficients_hom_ext {M : ModuleCat.{u} ℤ}
    {f g : integralSingularCoefficients ⟶ M}
    (h : f (ULift.up (1 : ℤ)) = g (ULift.up (1 : ℤ))) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨k⟩
  have hk : (ULift.up k : ULift.{u} ℤ) = k • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  rw [hk, map_zsmul, map_zsmul, h]

private theorem squareBoundary_avoids_triangleCenter :
    liftedSquareBoundary.{u} ⊆ ({squareTriangleCenter}ᶜ : Set liftedSquare) := by
  intro x hx h
  exact squareTriangleCenter_not_mem_boundary (h ▸ hx)

private theorem liftedSquareFundamentalChain_boundary_mem_triangleCenter_compl :
    (integralSingularChains liftedSquare).d 2 1 liftedSquareFundamentalChain ∈
      integralSingularChainsIn 1 ({squareTriangleCenter}ᶜ : Set (liftedSquare.{u})) := by
  apply integralSingularChainsIn_mono 1 squareBoundary_avoids_triangleCenter
  rw [integralSingularChainsIn_eq_range]
  exact ⟨liftedSquareBoundaryLoopChain, liftedSquareBoundaryLoopChain_inclusion⟩

private def squareTriangleLocalChain :
    integralSingularCoefficients ⟶
      (integralRelativeChains ({squareTriangleCenter}ᶜ : Set (liftedSquare.{u}))).X 2 :=
  integralChainHom 2 liftedSquareFundamentalChain ≫
    (integralRelativeProjection ({squareTriangleCenter}ᶜ : Set liftedSquare)).f 2

private theorem squareTriangleLocalChain_boundary :
    squareTriangleLocalChain ≫
      (integralRelativeChains ({squareTriangleCenter}ᶜ : Set (liftedSquare.{u}))).d 2 1 = 0 := by
  rw [squareTriangleLocalChain, Category.assoc, HomologicalComplex.Hom.comm,
    ← Category.assoc, integralChainHom_d]
  apply integralCoefficients_hom_ext
  rw [ModuleCat.comp_apply, SimplexDegree.integralChainHom_apply_one,
    integralRelativeProjection_eq_zero_of_mem 1 _ _
      liftedSquareFundamentalChain_boundary_mem_triangleCenter_compl]
  rfl

private def squareTriangleLocalClass : integralLocalHomology 2 squareTriangleCenter.{u} :=
  integralRelativeClassOf 1 ({squareTriangleCenter}ᶜ : Set liftedSquare)
    squareTriangleLocalChain squareTriangleLocalChain_boundary

private theorem squareTriangleCoordinate_localChain :
    squareTriangleLocalChain ≫
      (integralRelativeChainMap squareTriangleCoordinate squareTriangleCoordinate_mapsTo).f 2 =
        SimplexDegree.standardTriangleRelativeChain.{u} := by
  rw [squareTriangleLocalChain, Category.assoc, integralRelativeProjection_chainMap_component,
    ← Category.assoc, integralChainHom_comp_map, SimplexDegree.standardTriangleRelativeChain]
  apply integralCoefficients_hom_ext
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    SimplexDegree.integralChainHom_apply_one, SimplexDegree.integralChainHom_apply_one]
  exact squareTriangleCoordinate_fundamentalChain_relative

private theorem squareTriangleCoordinate_localClass :
    integralRelativeHomologyMap 2 squareTriangleCoordinate squareTriangleCoordinate_mapsTo
      squareTriangleLocalClass = SimplexDegree.standardTriangleLocalClass.{u} := by
  refine (integralRelativeHomologyMap_liftCycles_apply 1 squareTriangleCoordinate
    squareTriangleCoordinate_mapsTo squareTriangleLocalChain squareTriangleLocalChain_boundary
    (by rw [squareTriangleCoordinate_localChain]; exact
      SimplexDegree.standardTriangleRelativeChain_boundary)).trans ?_
  exact integralRelativeClassOf_congr 1 _ squareTriangleCoordinate_localChain



private theorem squareTriangleCollapse_mapsTo :
    MapsTo liftedSquareCollapse ({squareTriangleCenter}ᶜ : Set (liftedSquare.{u}))
      ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1)) := by
  intro t ht h
  exact ht (liftedCubeSphereProjection_eq_of_mem 1 squareTriangleCenter_mem_cubeInterior h)

private theorem squareTriangleCollapse_localChain :
    squareTriangleLocalChain ≫
      (integralRelativeChainMap liftedSquareCollapse squareTriangleCollapse_mapsTo).f 2 =
        integralChainHom 2 squareSphereFundamentalChain ≫
          (integralRelativeProjection
            ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1))).f 2 := by
  rw [squareTriangleLocalChain, Category.assoc, integralRelativeProjection_chainMap_component,
    ← Category.assoc, integralChainHom_comp_map, liftedSquareCollapse_fundamentalChain]

private theorem squareTriangleCollapse_localClass :
    integralRelativeHomologyMap 2 liftedSquareCollapse squareTriangleCollapse_mapsTo
      squareTriangleLocalClass =
        integralAbsoluteToRelative 2
          ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1))
          squareSphereFundamentalClass := by
  have hz : (integralChainHom 2 squareSphereFundamentalChain ≫
      (integralRelativeProjection
        ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1))).f 2) ≫
      (integralRelativeChains
        ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1))).d 2 1 = 0 := by
    rw [← squareTriangleCollapse_localChain, Category.assoc, HomologicalComplex.Hom.comm,
      ← Category.assoc, squareTriangleLocalChain_boundary, Limits.zero_comp]
  refine (integralRelativeHomologyMap_liftCycles_apply 1 liftedSquareCollapse
    squareTriangleCollapse_mapsTo squareTriangleLocalChain squareTriangleLocalChain_boundary
    (by rw [squareTriangleCollapse_localChain]; exact hz)).trans ?_
  refine (integralRelativeClassOf_congr 1 _ (hz := by rw [squareTriangleCollapse_localChain]; exact hz)
    (hz' := hz) squareTriangleCollapse_localChain).trans ?_
  exact (integralAbsoluteToRelative_homologyClass 1 _ squareSphereFundamentalChain
    squareSphereFundamentalChain_boundary hz).symm

def squareSphereLocalDegree : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) →ₗ[ℤ] ℤ :=
  SimplexDegree.standardTriangleLocalDegree.comp
    ((integralRelativeHomologyMap 2 squareTriangleCoordinate squareTriangleCoordinate_mapsTo).comp
      ((LinearEquiv.ofBijective
        (integralRelativeHomologyMap 2 liftedSquareCollapse squareTriangleCollapse_mapsTo)
        (integralRelativeHomologyMap_liftedCubeSphereProjection_bijective 1 2 squareTriangleCenter
          squareTriangleCenter_mem_cubeInterior)).symm.toLinearMap.comp
        (integralAbsoluteToRelative 2
          ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1)))))

theorem squareSphereLocalDegree_squareSphereFundamentalClass :
    squareSphereLocalDegree squareSphereFundamentalClass.{u} = 1 := by
  let e := LinearEquiv.ofBijective
    (integralRelativeHomologyMap 2 liftedSquareCollapse squareTriangleCollapse_mapsTo)
    (integralRelativeHomologyMap_liftedCubeSphereProjection_bijective 1 2 squareTriangleCenter
      squareTriangleCenter_mem_cubeInterior)
  have he : e squareTriangleLocalClass =
      integralAbsoluteToRelative 2
        ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1))
        squareSphereFundamentalClass := squareTriangleCollapse_localClass
  unfold squareSphereLocalDegree
  simp only [LinearMap.comp_apply]
  change SimplexDegree.standardTriangleLocalDegree
    (integralRelativeHomologyMap 2 squareTriangleCoordinate squareTriangleCoordinate_mapsTo
      (e.symm (integralAbsoluteToRelative 2
        ({liftedSquareCollapse squareTriangleCenter}ᶜ : Set (liftedHomotopySphere.{u} 1))
        squareSphereFundamentalClass))) = 1
  rw [← he, e.symm_apply_apply]
  rw [squareTriangleCoordinate_localClass,
    SimplexDegree.standardTriangleLocalDegree_standardTriangleLocalClass]

theorem isSphereHomologyGenerator_squareSphereFundamentalClass :
    IsSphereHomologyGenerator 1 squareSphereFundamentalClass.{u} :=
  (isSphereHomologyGenerator_iff_exists_functional 1 _).mpr
    ⟨squareSphereLocalDegree, squareSphereLocalDegree_squareSphereFundamentalClass⟩


end DifferentialGeometry.Topology
