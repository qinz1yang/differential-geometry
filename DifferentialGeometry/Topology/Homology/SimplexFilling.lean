import DifferentialGeometry.Topology.Simplex.BoundaryGluing
import DifferentialGeometry.Topology.Homotopy.SphereFilling
import DifferentialGeometry.Topology.Homotopy.SphereClasses
import DifferentialGeometry.Topology.Homology.SimplexMaps

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial Topology

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

theorem sphereMap_nullhomotopic_of_subsingleton_homotopyGroup (n : ℕ) (x : X)
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)]
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    f.Nullhomotopic := by
  obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective n x (ZerothHomotopy.mk f)
  rw [Subsingleton.elim a 1, homotopyGroupToFreeSphere_one] at ha
  exact ⟨x, (homotopic_iff_joined _ _).mpr (Quotient.exact ha.symm)⟩

theorem exists_simplex_extension_of_subsingleton_homotopyGroup (n : ℕ) (x : X)
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)]
    (f : C(Simplex.boundary (Fin (n + 3)), X)) :
    ∃ F : C(stdSimplex ℝ (Fin (n + 3)), X), ∀ z : Simplex.boundary (Fin (n + 3)),
      F z.val = f z := by
  let e := Simplex.stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
  let b := Simplex.stdSimplexNormedBallHomeomorph
    (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
  let g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
    f.comp ⟨e.symm, e.symm.continuous⟩
  obtain ⟨G, hG⟩ := exists_continuous_closedBall_of_nullhomotopic
    (sphereMap_nullhomotopic_of_subsingleton_homotopyGroup n x g)
  refine ⟨G.comp ⟨b, b.continuous⟩, ?_⟩
  intro z
  have h := congrArg (fun k => k (e z)) hG
  change G ⟨(e z).val, _⟩ = f (e.symm (e z)) at h
  rw [e.symm_apply_apply] at h
  exact h

theorem exists_integralSingularSimplex_of_compatible_faces (n : ℕ) (x : X)
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)]
    (f : Fin (n + 3) → integralSingularSimplex (n + 1) X)
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2)),
      (TopCat.toSSet.obj (TopCat.of X)).δ j (f i) =
        (TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i) (f (i.succAbove j))) :
    ∃ σ : integralSingularSimplex (n + 2) X,
      ∀ i : Fin (n + 3), (TopCat.toSSet.obj (TopCat.of X)).δ i σ = f i := by
  let F : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X) :=
    fun i => integralSingularSimplexEquiv (n + 1) X (f i)
  have hF : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      F i (stdSimplex.map j.succAbove p) =
        F (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j p
    have he := congrArg (fun s => integralSingularSimplexEquiv n X s p) (h i j)
    change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ j (f i)) p =
      (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i) (f (i.succAbove j))) p at he
    rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at he
    exact he
  obtain ⟨G, hG⟩ := exists_simplex_extension_of_subsingleton_homotopyGroup n x
    (Simplex.boundaryDesc F hF)
  refine ⟨(integralSingularSimplexEquiv (n + 2) X).symm G, ?_⟩
  intro i
  apply (integralSingularSimplexEquiv (n + 1) X).injective
  ext p
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i ((integralSingularSimplexEquiv (n + 2) X).symm G)) p = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change G (stdSimplex.map i.succAbove p) = _
  exact (hG ⟨stdSimplex.map i.succAbove p,
    ⟨i, Simplex.map_succAbove_apply_pivot i p⟩⟩).trans
      (Simplex.boundaryDesc_face F hF i p)

end DifferentialGeometry.Topology
