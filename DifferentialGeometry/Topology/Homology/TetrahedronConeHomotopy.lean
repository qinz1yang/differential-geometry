import DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import DifferentialGeometry.Topology.Simplex.TetrahedronEdgeIntersection
import DifferentialGeometry.Topology.Simplex.TetrahedronOneSkeletonGluing
import DifferentialGeometry.Topology.Simplex.TetrahedronHomotopyExtension

noncomputable section
namespace DifferentialGeometry.Topology
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private def tetrahedronEdgeSimplex (tau : integralSingularSimplex 3 X) (i : Fin 4) (j : Fin 3) :
    integralSingularSimplex 1 X :=
  (TopCat.toSSet.obj (TopCat.of X)).δ j ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)

omit [SimplyConnectedSpace X] in
private theorem tetrahedronEdgeSimplex_apply (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    integralSingularSimplexEquiv 1 X (tetrahedronEdgeSimplex tau i j) p =
      integralSingularSimplexEquiv 3 X tau
        (stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p)) := by
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ j ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)) p = _
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  rfl

private def tetrahedronEdgeConeHomotopy (x : X) (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) : C(unitInterval × stdSimplex ℝ (Fin 2), X) :=
  (integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)).comp
    ⟨fun z => (z.1, stdSimplexHomeomorphUnitInterval z.2),
      continuous_fst.prodMk (stdSimplexHomeomorphUnitInterval.continuous.comp continuous_snd)⟩

private theorem tetrahedronEdgeConeHomotopy_zero (x : X) (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    tetrahedronEdgeConeHomotopy x tau i j (0,p) =
      integralSingularSimplexEquiv 3 X tau
        (stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p)) := by
  change integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)
    (0, stdSimplexHomeomorphUnitInterval p) = _
  rw [integralSingularConeEdgeHomotopy_zero]
  have h := integralPathSimplex_apply (integralSimplexPath (tetrahedronEdgeSimplex tau i j)) p
  rw [integralPathSimplex_simplexPath] at h
  rw [← h, tetrahedronEdgeSimplex_apply]


private theorem tetrahedronEdgeConeHomotopy_one (x : X) (tau : integralSingularSimplex 3 X)
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    tetrahedronEdgeConeHomotopy x tau i j (1,p) = x :=
  integralSingularConeEdgeHomotopy_one x (tetrahedronEdgeSimplex tau i j) _

private theorem tetrahedronEdgeConeHomotopy_eq_of_mem_boundary
    (x : X) (tau : integralSingularSimplex 3 X)
    (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2))
    (hp : p ∈ Simplex.boundary (Fin 2)) (hq : q ∈ Simplex.boundary (Fin 2))
    (hpq : Simplex.edgeIntoTetrahedronOneSkeleton i j p =
      Simplex.edgeIntoTetrahedronOneSkeleton k l q) (t : unitInterval) :
    tetrahedronEdgeConeHomotopy x tau i j (t,p) =
      tetrahedronEdgeConeHomotopy x tau k l (t,q) := by
  change integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)
      (t, stdSimplexHomeomorphUnitInterval p) =
    integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau k l)
      (t, stdSimplexHomeomorphUnitInterval q)
  rw [integralSingularConeEdgeHomotopy_boundary x _ p hp,
    integralSingularConeEdgeHomotopy_boundary x _ q hq,
    tetrahedronEdgeSimplex_apply, tetrahedronEdgeSimplex_apply]
  have he : stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p) =
      stdSimplex.map k.succAbove (stdSimplex.map l.succAbove q) :=
    congrArg Subtype.val hpq
  rw [he]

omit [SimplyConnectedSpace X] in
private theorem tetrahedronEdgeSimplex_eq_of_map_eq
    (tau : integralSingularSimplex 3 X) (i k : Fin 4) (j l : Fin 3)
    (he : (fun p : stdSimplex ℝ (Fin 2) => stdSimplex.map i.succAbove
        (stdSimplex.map j.succAbove p)) =
      fun p : stdSimplex ℝ (Fin 2) => stdSimplex.map k.succAbove
        (stdSimplex.map l.succAbove p)) :
    tetrahedronEdgeSimplex tau i j = tetrahedronEdgeSimplex tau k l := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro p
  rw [tetrahedronEdgeSimplex_apply, tetrahedronEdgeSimplex_apply, congrFun he p]


private theorem tetrahedronEdgeConeHomotopy_overlap
    (x : X) (tau : integralSingularSimplex 3 X)
    (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)) (t : unitInterval)
    (hpq : Simplex.edgeIntoTetrahedronOneSkeleton i j p =
      Simplex.edgeIntoTetrahedronOneSkeleton k l q) :
    tetrahedronEdgeConeHomotopy x tau i j (t,p) =
      tetrahedronEdgeConeHomotopy x tau k l (t,q) := by
  obtain ⟨he, rfl⟩ | ⟨hp, hq⟩ :=
    Simplex.edgeIntoTetrahedronOneSkeleton_intersection i k j l p q hpq
  · have hmap : (fun p : stdSimplex ℝ (Fin 2) => stdSimplex.map i.succAbove
        (stdSimplex.map j.succAbove p)) =
        fun p : stdSimplex ℝ (Fin 2) => stdSimplex.map k.succAbove
          (stdSimplex.map l.succAbove p) := by
      funext p
      exact congrArg Subtype.val (ContinuousMap.congr_fun he p)
    have hs := tetrahedronEdgeSimplex_eq_of_map_eq tau i k j l hmap
    change integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau i j)
        (t, stdSimplexHomeomorphUnitInterval p) =
      integralSingularConeEdgeHomotopy x (tetrahedronEdgeSimplex tau k l)
        (t, stdSimplexHomeomorphUnitInterval p)
    rw [hs]
  · exact tetrahedronEdgeConeHomotopy_eq_of_mem_boundary x tau i k j l p q hp hq hpq t

theorem exists_tetrahedron_cone_edge_homotopy
    (x : X) (tau : integralSingularSimplex 3 X) :
    ∃ F : C(unitInterval × stdSimplex ℝ (Fin 4), X),
      (∀ p, F (0,p) = integralSingularSimplexEquiv 3 X tau p) ∧
      (∀ (i : Fin 4) (j : Fin 3) (t : unitInterval) (p : stdSimplex ℝ (Fin 2)),
        F (t, stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p)) =
          integralSingularConeEdgeHomotopy x
            ((TopCat.toSSet.obj (TopCat.of X)).δ j ((TopCat.toSSet.obj (TopCat.of X)).δ i tau))
            (t, stdSimplexHomeomorphUnitInterval p)) ∧
      ∀ p : Simplex.tetrahedronOneSkeleton, F (1,p.val) = x := by
  let H := Simplex.tetrahedronOneSkeletonHomotopyDesc (tetrahedronEdgeConeHomotopy x tau)
    (tetrahedronEdgeConeHomotopy_overlap x tau)
  have hH : ∀ p : Simplex.tetrahedronOneSkeleton,
      H (0,p) = integralSingularSimplexEquiv 3 X tau p.val := by
    intro p
    exact Simplex.tetrahedronOneSkeletonHomotopyDesc_eq _ _ 0
      (fun p => integralSingularSimplexEquiv 3 X tau p.val)
      (tetrahedronEdgeConeHomotopy_zero x tau) p
  obtain ⟨F, hF0, hFs⟩ := Simplex.exists_continuous_homotopy_extension_tetrahedronOneSkeleton
    (integralSingularSimplexEquiv 3 X tau) H hH
  refine ⟨F, hF0, ?_, ?_⟩
  · intro i j t p
    exact (hFs t (Simplex.edgeIntoTetrahedronOneSkeleton i j p)).trans
      (Simplex.tetrahedronOneSkeletonHomotopyDesc_edge _ _ i j p t)
  · intro p
    exact (hFs 1 p).trans
      (Simplex.tetrahedronOneSkeletonHomotopyDesc_eq _ _ 1 (fun _ => x)
        (tetrahedronEdgeConeHomotopy_one x tau) p)

end DifferentialGeometry.Topology
