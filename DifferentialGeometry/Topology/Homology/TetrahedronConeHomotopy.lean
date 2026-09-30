import DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import DifferentialGeometry.Topology.Simplex.TetrahedronEdgeIntersection
import DifferentialGeometry.Topology.Simplex.TetrahedronOneSkeletonGluing
import DifferentialGeometry.Topology.Simplex.TetrahedronHomotopyExtension

noncomputable section
namespace DifferentialGeometry.Topology
open CategoryTheory AlgebraicTopology
open Convexity.StdSimplex (coordinateSet coordinateMap coordinateHomeomorph
  coordinateHomeomorphI coordinateEquiv_map)
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private def tetrahedronEdgeSimplex (tau : integralSingularSimplex 3 X) (i : Fin 4) (j : Fin 3) :
    integralSingularSimplex 1 X :=
  (TopCat.toSSet.obj (TopCat.of X)).δ j ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)

omit [SimplyConnectedSpace X] in
private theorem tetrahedronEdgeSimplex_apply (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) (p : coordinateSet ℝ (Fin 2)) :
    integralSingularSimplexEquiv 1 X (tetrahedronEdgeSimplex tau i j)
        ((coordinateHomeomorph ℝ (Fin 2)).symm p) =
      integralSingularSimplexEquiv 3 X tau
        ((coordinateHomeomorph ℝ (Fin 4)).symm
          (coordinateMap i.succAbove (coordinateMap j.succAbove p))) := by
  obtain ⟨p, rfl⟩ := (coordinateHomeomorph ℝ (Fin 2)).surjective p
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ j ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)) _ = _
  rw [Homeomorph.symm_apply_apply, TopCat.toSSetObjEquiv_δ_apply,
    TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 3 X tau _ =
    integralSingularSimplexEquiv 3 X tau
      ((coordinateHomeomorph ℝ (Fin 4)).symm
        (coordinateMap i.succAbove (coordinateMap j.succAbove
          (Convexity.StdSimplex.coordinateEquiv ℝ (Fin 2) p))))
  rw [← coordinateEquiv_map, ← coordinateEquiv_map]
  exact congrArg _ ((coordinateHomeomorph ℝ (Fin 4)).symm_apply_apply _).symm

private def tetrahedronEdgeConeHomotopy (x : X) (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) : C(unitInterval × coordinateSet ℝ (Fin 2), X) :=
  (integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)).comp
    ⟨fun z => (z.1, coordinateHomeomorphI z.2),
      continuous_fst.prodMk (coordinateHomeomorphI.continuous.comp continuous_snd)⟩

private theorem tetrahedronEdgeConeHomotopy_zero (x : X) (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) (p : coordinateSet ℝ (Fin 2)) :
    tetrahedronEdgeConeHomotopy x tau i j (0,p) =
      integralSingularSimplexEquiv 3 X tau
        ((coordinateHomeomorph ℝ (Fin 4)).symm
          (coordinateMap i.succAbove (coordinateMap j.succAbove p))) := by
  change integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)
    (0, coordinateHomeomorphI p) = _
  rw [integralSingularConeEdgeHomotopy_zero]
  have h := integralPathSimplex_apply (integralSimplexPath (tetrahedronEdgeSimplex tau i j))
    ((coordinateHomeomorph ℝ (Fin 2)).symm p)
  rw [integralPathSimplex_simplexPath] at h
  exact h.symm.trans (tetrahedronEdgeSimplex_apply tau i j p)


private theorem tetrahedronEdgeConeHomotopy_one (x : X) (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) (p : coordinateSet ℝ (Fin 2)) :
    tetrahedronEdgeConeHomotopy x tau i j (1,p) = x :=
  integralSingularConeEdgeHomotopy_one x (tetrahedronEdgeSimplex tau i j) _

private theorem tetrahedronEdgeConeHomotopy_eq_of_mem_boundary
    (x : X) (tau : integralSingularSimplex 3 X)
    (i k : Fin 4) (j l : Fin 3) (p q : coordinateSet ℝ (Fin 2))
    (hp : p ∈ Simplex.boundary (Fin 2)) (hq : q ∈ Simplex.boundary (Fin 2))
    (hpq : Simplex.edgeIntoTetrahedronOneSkeleton i j p =
      Simplex.edgeIntoTetrahedronOneSkeleton k l q) (t : unitInterval) :
    tetrahedronEdgeConeHomotopy x tau i j (t,p) =
      tetrahedronEdgeConeHomotopy x tau k l (t,q) := by
  change integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)
      (t, coordinateHomeomorphI p) =
    integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau k l)
      (t, coordinateHomeomorphI q)
  rw [integralSingularConeEdgeHomotopy_boundary x _ p hp,
    integralSingularConeEdgeHomotopy_boundary x _ q hq,
    tetrahedronEdgeSimplex_apply, tetrahedronEdgeSimplex_apply]
  have he : coordinateMap i.succAbove (coordinateMap j.succAbove p) =
      coordinateMap k.succAbove (coordinateMap l.succAbove q) :=
    congrArg Subtype.val hpq
  rw [he]

omit [SimplyConnectedSpace X] in
private theorem tetrahedronEdgeSimplex_eq_of_map_eq
    (tau : integralSingularSimplex 3 X) (i k : Fin 4) (j l : Fin 3)
    (he : (fun p : coordinateSet ℝ (Fin 2) => coordinateMap i.succAbove
        (coordinateMap j.succAbove p)) =
      fun p : coordinateSet ℝ (Fin 2) => coordinateMap k.succAbove
        (coordinateMap l.succAbove p)) :
    tetrahedronEdgeSimplex tau i j = tetrahedronEdgeSimplex tau k l := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro p
  have h := congrFun he (coordinateHomeomorph ℝ (Fin 2) p)
  have hi := tetrahedronEdgeSimplex_apply tau i j (coordinateHomeomorph ℝ (Fin 2) p)
  have hk := tetrahedronEdgeSimplex_apply tau k l (coordinateHomeomorph ℝ (Fin 2) p)
  rw [Homeomorph.symm_apply_apply] at hi hk
  exact hi.trans ((congrArg (fun q => integralSingularSimplexEquiv 3 X tau
    ((coordinateHomeomorph ℝ (Fin 4)).symm q)) h).trans hk.symm)


private theorem tetrahedronEdgeConeHomotopy_overlap
    (x : X) (tau : integralSingularSimplex 3 X)
    (i k : Fin 4) (j l : Fin 3) (p q : coordinateSet ℝ (Fin 2)) (t : unitInterval)
    (hpq : Simplex.edgeIntoTetrahedronOneSkeleton i j p =
      Simplex.edgeIntoTetrahedronOneSkeleton k l q) :
    tetrahedronEdgeConeHomotopy x tau i j (t,p) =
      tetrahedronEdgeConeHomotopy x tau k l (t,q) := by
  obtain ⟨he, rfl⟩ | ⟨hp, hq⟩ :=
    Simplex.edgeIntoTetrahedronOneSkeleton_intersection i k j l p q hpq
  · have hmap : (fun p : coordinateSet ℝ (Fin 2) => coordinateMap i.succAbove
        (coordinateMap j.succAbove p)) =
        fun p : coordinateSet ℝ (Fin 2) => coordinateMap k.succAbove
          (coordinateMap l.succAbove p) := by
      funext p
      exact congrArg Subtype.val (ContinuousMap.congr_fun he p)
    have hs := tetrahedronEdgeSimplex_eq_of_map_eq tau i k j l hmap
    change integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)
        (t, coordinateHomeomorphI p) =
      integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau k l)
        (t, coordinateHomeomorphI p)
    rw [hs]
  · exact tetrahedronEdgeConeHomotopy_eq_of_mem_boundary x tau i k j l p q hp hq hpq t

theorem exists_tetrahedron_cone_edge_homotopy
    (x : X) (tau : integralSingularSimplex 3 X) :
    ∃ F : C(unitInterval × coordinateSet ℝ (Fin 4), X),
      (∀ p, F (0,p) = integralSingularSimplexEquiv 3 X tau
        ((coordinateHomeomorph ℝ (Fin 4)).symm p)) ∧
      (∀ (i : Fin 4) (j : Fin 3) (t : unitInterval) (p : coordinateSet ℝ (Fin 2)),
        F (t, coordinateMap i.succAbove (coordinateMap j.succAbove p)) =
          integralSingularConeEdgeHomotopy x
            ((TopCat.toSSet.obj (TopCat.of X)).δ j ((TopCat.toSSet.obj (TopCat.of X)).δ i tau))
            (t, coordinateHomeomorphI p)) ∧
      ∀ p : Simplex.tetrahedronOneSkeleton, F (1,p.val) = x := by
  let f : C(coordinateSet ℝ (Fin 4), X) :=
    (integralSingularSimplexEquiv 3 X tau).comp
      ⟨(coordinateHomeomorph ℝ (Fin 4)).symm,
        (coordinateHomeomorph ℝ (Fin 4)).symm.continuous⟩
  let H := Simplex.tetrahedronOneSkeletonHomotopyDesc (tetrahedronEdgeConeHomotopy x tau)
    (tetrahedronEdgeConeHomotopy_overlap x tau)
  have hH : ∀ p : Simplex.tetrahedronOneSkeleton,
      H (0,p) = f p.val := by
    intro p
    exact Simplex.tetrahedronOneSkeletonHomotopyDesc_eq _ _ 0
      (fun p => f p.val)
      (tetrahedronEdgeConeHomotopy_zero x tau) p
  obtain ⟨F, hF0, hFs⟩ := Simplex.exists_continuous_homotopy_extension_tetrahedronOneSkeleton
    f H hH
  refine ⟨F, hF0, ?_, ?_⟩
  · intro i j t p
    exact (hFs t (Simplex.edgeIntoTetrahedronOneSkeleton i j p)).trans
      (Simplex.tetrahedronOneSkeletonHomotopyDesc_edge _ _ i j p t)
  · intro p
    exact (hFs 1 p).trans
      (Simplex.tetrahedronOneSkeletonHomotopyDesc_eq _ _ 1 (fun _ => x)
        (tetrahedronEdgeConeHomotopy_one x tau) p)

end DifferentialGeometry.Topology
