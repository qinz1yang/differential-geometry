import DifferentialGeometry.Topology.Homology.SphereNullity
import DifferentialGeometry.Topology.Simplex.Extension

noncomputable section

open Convexity.StdSimplex (coordinateSet coordinateMap coordinateEquiv
  coordinateHomeomorph coordinateEquiv_map)
open scoped Simplicial

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private theorem exists_integralSingularSimplex_three_of_compatible_faces_of_boundary
    (f : Fin 4 → integralSingularSimplex 2 X)
    (h : ∀ (i : Fin 4) (j : Fin 3),
      (TopCat.toSSet.obj (TopCat.of X)).δ j (f i) =
        (TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i) (f (i.succAbove j)))
    (b : (integralSingularChains X).X 3)
    (hb : (integralSingularChains X).d 3 2 b =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2 (f i)) :
    ∃ σ : integralSingularSimplex 3 X,
      ∀ i : Fin 4, (TopCat.toSSet.obj (TopCat.of X)).δ i σ = f i := by
  let F : Fin 4 → C(coordinateSet ℝ (Fin 3), X) :=
    fun i => (integralSingularSimplexEquiv 2 X (f i)).comp
      ⟨(coordinateEquiv ℝ _).symm, (coordinateHomeomorph ℝ _).symm.continuous⟩
  have hF : ∀ (i : Fin 4) (j : Fin 3) (p : coordinateSet ℝ (Fin 2)),
      F i (coordinateMap j.succAbove p) =
        F (i.succAbove j) (coordinateMap (j.predAbove i).succAbove p) := by
    intro i j p
    obtain ⟨p, rfl⟩ := (coordinateEquiv ℝ _).surjective p
    have he := congrArg (fun s => integralSingularSimplexEquiv 1 X s p) (h i j)
    change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ j (f i)) p =
      (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i) (f (i.succAbove j))) p at he
    rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at he
    change integralSingularSimplexEquiv 2 X (f i)
        ((coordinateEquiv ℝ _).symm (coordinateMap j.succAbove (coordinateEquiv ℝ _ p))) =
      integralSingularSimplexEquiv 2 X (f (i.succAbove j))
        ((coordinateEquiv ℝ _).symm
          (coordinateMap (j.predAbove i).succAbove (coordinateEquiv ℝ _ p)))
    rw [← coordinateEquiv_map, Equiv.symm_apply_apply,
      ← coordinateEquiv_map, Equiv.symm_apply_apply]
    exact he
  have hF_comp (i : Fin 4) :
      (F i).comp ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩ =
        integralSingularSimplexEquiv 2 X (f i) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg (integralSingularSimplexEquiv 2 X (f i))
      ((coordinateEquiv ℝ _).symm_apply_apply p)
  let g := Simplex.boundarySphereDesc F hF
  have hgchain : (integralSingularChainMap
      (g.comp (liftedHomotopySphereDown 1))).f 2 (simplexBoundarySphereChain.{u} 1) =
      (integralSingularChains X).d 3 2 b := by
    rw [hb]
    simpa only [g, liftedHomotopySphereDown, hF_comp, Equiv.symm_apply_apply] using
      integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain 1 F hF
  have hgzero : freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1)
      (ZerothHomotopy.mk g) = 0 := by
    rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass,
      integralSingularCycleClass_map]
    apply (integralSingularCycleClass_eq_zero_iff 1 X _).mpr
    refine ⟨b, ?_⟩
    apply Subtype.ext
    exact hgchain.symm
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hgnull :=
    nullhomotopic_of_freeSphereHomologyImage_simplexBoundary_eq_zero x g hgzero
  let e := Simplex.stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
  have heq : g.comp ⟨e, e.continuous⟩ = Simplex.boundaryDesc F hF := by
    ext p
    exact congrArg (Simplex.boundaryDesc F hF) (e.symm_apply_apply p)
  have hboundary : (Simplex.boundaryDesc F hF).Nullhomotopic := by
    rw [← heq]
    exact hgnull.comp_left ⟨e, e.continuous⟩
  obtain ⟨H, hH⟩ := Simplex.exists_continuous_extension_of_nullhomotopic 3
    (Simplex.boundaryDesc F hF) hboundary
  let H' := H.comp ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩
  refine ⟨(integralSingularSimplexEquiv 3 X).symm H', ?_⟩
  intro i
  apply (integralSingularSimplexEquiv 2 X).injective
  ext p
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i ((integralSingularSimplexEquiv 3 X).symm H')) p = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change H (coordinateEquiv ℝ _ (Convexity.StdSimplex.map i.succAbove p)) = _
  rw [coordinateEquiv_map]
  have hface := (hH ⟨coordinateMap i.succAbove (coordinateEquiv ℝ _ p),
    ⟨i, Simplex.map_succAbove_apply_pivot i _⟩⟩).trans
      (Simplex.boundaryDesc_face F hF i (coordinateEquiv ℝ _ p))
  change H (coordinateMap i.succAbove (coordinateEquiv ℝ _ p)) =
    integralSingularSimplexEquiv 2 X (f i)
      ((coordinateEquiv ℝ _).symm (coordinateEquiv ℝ _ p)) at hface
  rwa [Equiv.symm_apply_apply] at hface

theorem exists_integralSingularSimplex_three_iff_boundary_of_compatible_faces
    (f : Fin 4 → integralSingularSimplex 2 X)
    (h : ∀ (i : Fin 4) (j : Fin 3),
      (TopCat.toSSet.obj (TopCat.of X)).δ j (f i) =
        (TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i) (f (i.succAbove j))) :
    (∃ σ : integralSingularSimplex 3 X,
      ∀ i : Fin 4, (TopCat.toSSet.obj (TopCat.of X)).δ i σ = f i) ↔
    ∃ b : (integralSingularChains X).X 3,
      (integralSingularChains X).d 3 2 b =
        ∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2 (f i) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨integralSimplexChain 3 σ, ?_⟩
    rw [integralSimplexChain_boundary]
    simp only [hσ]
  · rintro ⟨b, hb⟩
    exact exists_integralSingularSimplex_three_of_compatible_faces_of_boundary f h b hb


theorem exists_integralSingularConeTetrahedron_iff_integralSingularCycleClass_eq_zero
    (x : X) (σ : integralSingularSimplex 2 X) :
    (∃ τ : integralSingularSimplex 3 X,
      ∀ i : Fin 4, (TopCat.toSSet.obj (TopCat.of X)).δ i τ =
        integralSingularConeFaces x σ i) ↔
    integralSingularCycleClass 1 X
      (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)) = 0 := by
  rw [exists_integralSingularSimplex_three_iff_boundary_of_compatible_faces
    (integralSingularConeFaces x σ) (integralSingularConeFaces_compatible x σ),
    integralSingularCycleClass_eq_zero_iff]
  have heq : (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)).val =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2
        (integralSingularConeFaces x σ i) := by
    rw [integralSingularTwoCycleProjection_val, integralSimplexChain_boundary_two,
      map_add, map_sub, integralSingularConeOne_simplex, integralSingularConeOne_simplex,
      integralSingularConeOne_simplex, Fin.sum_univ_four]
    norm_num
    dsimp [integralSingularConeFaces, Fin.cons]
    abel
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, Subtype.ext ?_⟩
    exact hb.trans heq.symm
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    exact (congrArg Subtype.val hb).trans heq

end DifferentialGeometry.Topology
