import DifferentialGeometry.Topology.Homology.FourSimplexConeHomotopy
import DifferentialGeometry.Topology.Homology.ConeThreeSphereHomotopy

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology ContinuousMap
open Convexity.StdSimplex (coordinateSet coordinateMap continuous_coordinateMap
  coordinateEquiv coordinateHomeomorph coordinateEquiv_map coordinateMap_comp_apply)
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

theorem exists_fourSimplex_cone_terminal_faces
    (τ : integralSingularSimplex 4 X) :
    ∃ g : C(coordinateSet ℝ (Fin 5), X),
      ((integralSingularSimplexEquiv 4 X τ).comp
        ⟨(coordinateHomeomorph ℝ (Fin 5)).symm,
          (coordinateHomeomorph ℝ (Fin 5)).symm.continuous⟩).Homotopic g ∧
      (∀ p : Simplex.skeleton (Fin 5) 2, g p.val = x) ∧
      ∀ i : Fin 5,
        ∃ hgi : ∀ p ∈ Simplex.boundary (Fin 4),
          (g.comp ⟨coordinateMap i.succAbove, continuous_coordinateMap i.succAbove⟩) p = x,
          (integralSingularConeThreeSphereMap x ((TopCat.toSSet.obj (TopCat.of X)).δ i τ)).Homotopic
            (Simplex.tetrahedronSphereMap
              (g.comp ⟨coordinateMap i.succAbove, continuous_coordinateMap i.succAbove⟩) x hgi) := by
  classical
  obtain ⟨F, hF0, hFs, hFskel⟩ := exists_fourSimplex_cone_triangle_homotopy x τ
  have htrace (i : Fin 5) (j : Fin 4) (t : unitInterval) (p : coordinateSet ℝ (Fin 3)) :
      F (t, coordinateMap i.succAbove (coordinateMap j.succAbove p)) =
        integralSingularConeTriangleHomotopy x
          ((TopCat.toSSet.obj (TopCat.of X)).δ j
            ((TopCat.toSSet.obj (TopCat.of X)).δ i τ)) (t, p) := by
    let f : Fin 3 → Fin 5 := i.succAbove ∘ j.succAbove
    have hf : StrictMono f := (Fin.strictMono_succAbove i).comp (Fin.strictMono_succAbove j)
    let s : Finset (Fin 5) := Finset.univ.image f
    have hs : s.card = 3 := by
      rw [Finset.card_image_of_injective _ hf.injective]
      rfl
    have he : f = s.orderEmbOfFin hs :=
      Finset.orderEmbOfFin_unique hs (fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩) hf
    have h := hFs s hs t p
    rw [← he] at h
    have hsimplex : (integralSingularSimplexEquiv 2 X).symm
        ((integralSingularSimplexEquiv 4 X τ).comp
          ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩) =
        (TopCat.toSSet.obj (TopCat.of X)).δ j
          ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) := by
      apply (integralSingularSimplexEquiv 2 X).injective
      rw [Equiv.apply_symm_apply]
      ext q
      change integralSingularSimplexEquiv 4 X τ (Convexity.StdSimplex.map f q) =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ j
            ((TopCat.toSSet.obj (TopCat.of X)).δ i τ)) q
      rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
      change integralSingularSimplexEquiv 4 X τ (Convexity.StdSimplex.map f q) =
        integralSingularSimplexEquiv 4 X τ
          (Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.map j.succAbove q))
      congr 1
      apply (coordinateEquiv ℝ (Fin 5)).injective
      rw [coordinateEquiv_map, coordinateEquiv_map, coordinateEquiv_map,
        coordinateMap_comp_apply]
    rw [hsimplex] at h
    simpa only [coordinateMap_comp_apply] using h
  let g : C(coordinateSet ℝ (Fin 5), X) := ⟨fun p => F (1, p), by fun_prop⟩
  let H : ((integralSingularSimplexEquiv 4 X τ).comp
      ⟨(coordinateHomeomorph ℝ (Fin 5)).symm,
        (coordinateHomeomorph ℝ (Fin 5)).symm.continuous⟩).Homotopy g :=
    { toContinuousMap := F
      map_zero_left := hF0
      map_one_left := fun _ => rfl }
  refine ⟨g, ⟨H⟩, hFskel, ?_⟩
  intro i
  let gi : C(coordinateSet ℝ (Fin 4), X) :=
    g.comp ⟨coordinateMap i.succAbove, continuous_coordinateMap i.succAbove⟩
  have hgi : ∀ p ∈ Simplex.boundary (Fin 4), gi p = x := by
    intro p hp
    obtain ⟨j, hj⟩ := hp
    let q := Simplex.faceDelete j ⟨p, hj⟩
    have hq : coordinateMap j.succAbove q = p :=
      congrArg Subtype.val (Simplex.faceInsert_faceDelete j ⟨p, hj⟩)
    change F (1, coordinateMap i.succAbove p) = x
    rw [← hq, htrace, integralSingularConeTriangleHomotopy_one]
  let Hi : ((integralSingularSimplexEquiv 3 X
      ((TopCat.toSSet.obj (TopCat.of X)).δ i τ)).comp
        ⟨(coordinateHomeomorph ℝ (Fin 4)).symm,
          (coordinateHomeomorph ℝ (Fin 4)).symm.continuous⟩).Homotopy gi :=
    { toContinuousMap := ⟨fun z => F (z.1, coordinateMap i.succAbove z.2),
        F.continuous.comp (continuous_fst.prodMk
          ((continuous_coordinateMap i.succAbove).comp continuous_snd))⟩
      map_zero_left := by
        intro p
        change F (0, coordinateMap i.succAbove p) = _
        rw [hF0]
        obtain ⟨p, rfl⟩ := (coordinateHomeomorph ℝ (Fin 4)).surjective p
        change integralSingularSimplexEquiv 4 X τ
            ((coordinateEquiv ℝ (Fin 5)).symm
              (coordinateMap i.succAbove (coordinateEquiv ℝ (Fin 4) p))) =
          (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i τ)
            ((coordinateHomeomorph ℝ (Fin 4)).symm (coordinateHomeomorph ℝ (Fin 4) p))
        rw [← coordinateEquiv_map, Equiv.symm_apply_apply, Homeomorph.symm_apply_apply,
          TopCat.toSSetObjEquiv_δ_apply]
        rfl
      map_one_left := fun _ => rfl }
  exact ⟨hgi, integralSingularConeThreeSphereMap_homotopic_tetrahedronSphereMap x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) gi hgi Hi (fun t j p => htrace i j t p)⟩

end DifferentialGeometry.Topology
