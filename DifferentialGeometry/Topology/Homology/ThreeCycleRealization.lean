import DifferentialGeometry.Topology.Homology.TwoCycleRealization
import DifferentialGeometry.Topology.Homology.SimplexFilling
noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [hpi : Subsingleton (HomotopyGroup (Fin 2) X x)]

def integralSingularConeTetrahedron (σ : integralSingularSimplex 2 X) :
    integralSingularSimplex 3 X :=
  (exists_integralSingularSimplex_of_compatible_faces 1 x (integralSingularConeFaces x σ)
    (integralSingularConeFaces_compatible x σ)).choose

theorem integralSingularConeTetrahedron_face (σ : integralSingularSimplex 2 X)
    (i : Fin 4) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (integralSingularConeTetrahedron x σ) =
      integralSingularConeFaces x σ i :=
  (exists_integralSingularSimplex_of_compatible_faces 1 x (integralSingularConeFaces x σ)
    (integralSingularConeFaces_compatible x σ)).choose_spec i

def integralSingularConeTwo :
    (integralSingularChains X).X 2 →ₗ[ℤ] (integralSingularChains X).X 3 :=
  (integralSingularChainBasis 2 X).constr (M' := (integralSingularChains X).X 3) ℕ
    (fun σ => integralSimplexChain 3 (integralSingularConeTetrahedron x σ))

theorem integralSingularConeTwo_simplex (σ : integralSingularSimplex 2 X) :
    integralSingularConeTwo x (integralSimplexChain 2 σ) =
      integralSimplexChain 3 (integralSingularConeTetrahedron x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 2 X).constr_basis ℕ _ σ

theorem integralSingularConeTetrahedron_boundary (σ : integralSingularSimplex 2 X) :
    (integralSingularChains X).d 3 2
      (integralSimplexChain 3 (integralSingularConeTetrahedron x σ)) =
      integralSimplexChain 2 σ - integralSingularConeOne x
        ((integralSingularChains X).d 2 1 (integralSimplexChain 2 σ)) := by
  rw [integralSimplexChain_boundary]
  simp only [integralSingularConeTetrahedron_face]
  change (∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2
    (integralSingularConeFaces x σ i)) = _
  rw [Fin.sum_univ_four, integralSimplexChain_boundary_two, map_add, map_sub,
    integralSingularConeOne_simplex, integralSingularConeOne_simplex,
    integralSingularConeOne_simplex]
  norm_num
  dsimp [integralSingularConeFaces, Fin.cons]
  abel

theorem integralSingularConeTwo_equation :
    ((integralSingularChains X).d 3 2).hom.comp (integralSingularConeTwo x) =
      LinearMap.id - (integralSingularConeOne x).comp ((integralSingularChains X).d 2 1).hom := by
  apply (integralSingularChainBasis 2 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.comp_apply,
    integralSingularConeTwo_simplex, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply]
  exact integralSingularConeTetrahedron_boundary x σ

theorem integralSingularConeTwo_bounds (z : (integralSingularChains X).X 2)
    (hz : (integralSingularChains X).d 2 1 z = 0) :
    (integralSingularChains X).d 3 2 (integralSingularConeTwo x z) = z := by
  have h := LinearMap.congr_fun (integralSingularConeTwo_equation x) z
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hz, map_zero, sub_zero] using h

def integralSingularThreeCycleProjection :
    (integralSingularChains X).X 3 →ₗ[ℤ] integralSingularCycles 2 X :=
  (LinearMap.id - (integralSingularConeTwo x).comp
    ((integralSingularChains X).d 3 2).hom).codRestrict (integralSingularCycles 2 X) fun z => by
      change (integralSingularChains X).d 3 2
        (z - integralSingularConeTwo x ((integralSingularChains X).d 3 2 z)) = 0
      rw [map_sub, integralSingularConeTwo_bounds, sub_self]
      exact congrArg (fun f => f z) ((integralSingularChains X).d_comp_d 3 2 1)

theorem integralSingularThreeCycleProjection_val (z : (integralSingularChains X).X 3) :
    (integralSingularThreeCycleProjection x z).val =
      z - integralSingularConeTwo x ((integralSingularChains X).d 3 2 z) := rfl

@[simp] theorem integralSingularThreeCycleProjection_cycle (z : integralSingularCycles 2 X) :
    integralSingularThreeCycleProjection x z.val = z := by
  apply Subtype.ext
  rw [integralSingularThreeCycleProjection_val]
  have hz : (integralSingularChains X).d 3 2 z.val = 0 := z.property
  rw [hz, map_zero, sub_zero]

def integralSingularConeThreeFaces (σ : integralSingularSimplex 3 X) :
    Fin 5 → integralSingularSimplex 3 X :=
  Fin.cons σ fun i => integralSingularConeTetrahedron x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)

theorem integralSingularConeThreeFaces_compatible (σ : integralSingularSimplex 3 X)
    (i : Fin 5) (j : Fin 4) :
    (TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeThreeFaces x σ i) =
      (TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
        (integralSingularConeThreeFaces x σ (i.succAbove j)) := by
  have h00 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 0
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (0 : Fin 3) ≤ 0 by decide))
  have h01 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 1
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (0 : Fin 3) ≤ 1 by decide))
  have h02 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 2
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (0 : Fin 3) ≤ 2 by decide))
  have h11 : (TopCat.toSSet.obj (TopCat.of X)).δ 1
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 1
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (1 : Fin 3) ≤ 1 by decide))
  have h12 : (TopCat.toSSet.obj (TopCat.of X)).δ 1
      ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 2
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (1 : Fin 3) ≤ 2 by decide))
  have h22 : (TopCat.toSSet.obj (TopCat.of X)).δ 2
      ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 2
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (2 : Fin 3) ≤ 2 by decide))
  fin_cases i <;> fin_cases j
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    rw [h00]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    rw [h01]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    rw [h02]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    rw [h00]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    rw [h11]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    rw [h12]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    rw [h01]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    rw [h11]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    rw [h22]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    rw [h02]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    rw [h12]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    rw [h22]

private def integralSingularConeThreeBoundaryMap (σ : integralSingularSimplex 3 X) :
    C(DifferentialGeometry.Simplex.boundary (Fin 5), X) :=
  DifferentialGeometry.Simplex.boundaryDesc
    (fun i => integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ i))
    (fun i j p => by
      have h := congrArg (fun s => integralSingularSimplexEquiv 2 X s p)
        (integralSingularConeThreeFaces_compatible x σ i j)
      change (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ j
          (integralSingularConeThreeFaces x σ i)) p =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
            (integralSingularConeThreeFaces x σ (i.succAbove j))) p at h
      rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at h
      exact h)

def integralSingularConeThreeSphereMap (σ : integralSingularSimplex 3 X) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X) :=
  (integralSingularConeThreeBoundaryMap x σ).comp
    ⟨(DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 4) ℝ).symm).symm,
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 4) ℝ).symm).symm.continuous⟩

theorem integralSingularConeThreeSphereMap_simplexBoundarySphereChain
    (σ : integralSingularSimplex 3 X) :
    (integralSingularChainMap
      ((integralSingularConeThreeSphereMap x σ).comp ⟨ULift.down, continuous_uliftDown⟩)).f 3
      (simplexBoundarySphereChain.{u} 2) =
        (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)).val := by
  have h := integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain 2
    (fun i => integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ i))
    (by
      intro i j p
      have he := congrArg (fun s => integralSingularSimplexEquiv 2 X s p)
        (integralSingularConeThreeFaces_compatible x σ i j)
      change (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ j
          (integralSingularConeThreeFaces x σ i)) p =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
            (integralSingularConeThreeFaces x σ (i.succAbove j))) p at he
      rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at he
      exact he)
  change (integralSingularChainMap
      ((integralSingularConeThreeSphereMap x σ).comp ⟨ULift.down, continuous_uliftDown⟩)).f 3
      (simplexBoundarySphereChain 2) = _ at h
  rw [h]
  change (∑ i : Fin 5, (-1 : ℤ) ^ i.val • integralSimplexChain 3
    (integralSingularConeThreeFaces x σ i)) = _
  rw [integralSingularThreeCycleProjection_val, integralSimplexChain_boundary,
    map_sum]
  simp only [map_zsmul, integralSingularConeTwo_simplex]
  change (∑ i : Fin 5, (-1 : ℤ) ^ i.val • integralSimplexChain 3
      (integralSingularConeThreeFaces x σ i)) =
    integralSimplexChain 3 σ - ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
      integralSimplexChain 3 (integralSingularConeTetrahedron x
        ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))
  have hz : integralSingularConeThreeFaces x σ 0 = σ := rfl
  have hs (i : Fin 4) : integralSingularConeThreeFaces x σ i.succ =
      integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := rfl
  rw [Fin.sum_univ_succ, hz]
  simp only [hs, Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, pow_succ,
    mul_neg_one, neg_zsmul, Finset.sum_neg_distrib]
  exact (sub_eq_add_neg _ _).symm

theorem span_integralSingularThreeCycleProjection :
    Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 3 X =>
      integralSingularCycleClass 2 X
        (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)))) = ⊤ := by
  let f := (integralSingularCycleClassLinearMap 2 X).comp (integralSingularThreeCycleProjection x)
  have hspan : Submodule.span ℤ (Set.range (integralSingularChainBasis 3 X)) ≤
      Submodule.comap f (Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 3 X =>
        integralSingularCycleClass 2 X
          (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ))))) := by
    rw [Submodule.span_le]
    rintro z ⟨σ, rfl⟩
    exact Submodule.subset_span ⟨σ, by
      simp only [f, LinearMap.comp_apply, integralSingularChainBasis_apply,
        integralSingularCycleClassLinearMap_apply]⟩
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 2 X y
  have hz : f z.val ∈ Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 3 X =>
      integralSingularCycleClass 2 X
        (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)))) := by
    apply hspan
    rw [Basis.span_eq]
    exact Submodule.mem_top
  simpa only [f, LinearMap.comp_apply, integralSingularThreeCycleProjection_cycle,
    integralSingularCycleClassLinearMap_apply] using hz

theorem integralSingularConeThreeSphereMap_simplexBoundarySphereClass
    (σ : integralSingularSimplex 3 X) :
    freeSphereHomologyImage 2 (simplexBoundarySphereClass.{u} 2)
      (ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ)) =
        integralSingularCycleClass 2 X
          (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)) := by
  rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass,
    integralSingularCycleClass_map]
  congr 1
  apply Subtype.ext
  rw [integralSingularCycleMap_val]
  exact integralSingularConeThreeSphereMap_simplexBoundarySphereChain x σ

include hpi in
theorem span_range_freeSphereHomologyImage_three
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Submodule.span ℤ (Set.range (freeSphereHomologyImage (X := X) 2 c)) = ⊤ := by
  obtain ⟨k, hk⟩ := (isSphereHomologyGenerator_iff_forall_exists_zsmul 2 c).mp hc
    (simplexBoundarySphereClass.{u} 2)
  apply top_unique
  rw [← span_integralSingularThreeCycleProjection x]
  apply Submodule.span_le.mpr
  rintro y ⟨σ, rfl⟩
  change integralSingularCycleClass 2 X
      (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)) ∈ _
  rw [← integralSingularConeThreeSphereMap_simplexBoundarySphereClass, hk,
    freeSphereHomologyImage_zsmul]
  have hm : freeSphereHomologyImage (X := X) 2 c
      (ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ)) ∈
      Submodule.span ℤ (Set.range (freeSphereHomologyImage (X := X) 2 c)) :=
    Submodule.subset_span ⟨ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ), rfl⟩
  exact zsmul_mem hm k

include hpi in
theorem span_range_sphereHurewicz_three
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Submodule.span ℤ (Set.range (sphereHurewicz 2 x c)) = ⊤ := by
  rw [sphereHurewicz,
    (homotopyGroupToFreeSphere_surjective 2 x).range_comp (freeSphereHomologyImage 2 c)]
  exact span_range_freeSphereHomologyImage_three x c hc

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularHomology_three_subsingleton_of_subsingleton_homotopyGroup
    (x : X) [hpi : Subsingleton (HomotopyGroup (Fin 2) X x)]
    [Subsingleton (HomotopyGroup (Fin 3) X x)] :
    Subsingleton (integralSingularHomology 3 X) := by
  have hspan := span_range_sphereHurewicz_three x
    (integralLiftedSphereGenerator.{u} 2)
    (integralLiftedSphereGenerator_isGenerator 2)
  have hzero : Submodule.span ℤ
      (Set.range (sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro y ⟨a, rfl⟩
    rw [Subsingleton.elim a 1, sphereHurewicz_one]
  have ht : (⊤ : Submodule ℤ (integralSingularHomology 3 X)) = ⊥ := hspan.symm.trans hzero
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have h : a ∈ (⊤ : Submodule ℤ (integralSingularHomology 3 X)) := Submodule.mem_top
    rwa [ht, Submodule.mem_bot] at h
  have hb : b = 0 := by
    have h : b ∈ (⊤ : Submodule ℤ (integralSingularHomology 3 X)) := Submodule.mem_top
    rwa [ht, Submodule.mem_bot] at h
  exact ha.trans hb.symm

end DifferentialGeometry.Topology
