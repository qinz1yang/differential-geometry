import DifferentialGeometry.Topology.Homology.SimplexMaps
import Mathlib.Analysis.Normed.Module.Convex



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def affineSimplexMap {ι : Type*} [Fintype ι] (v : ι → E) : C(stdSimplex ℝ ι, E) :=
  ⟨fun t => ∑ i, t.val i • v i,
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)⟩


theorem affineSimplexMap_vertex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → E) (i : ι) : affineSimplexMap v (stdSimplex.vertex i) = v i := by
  change ∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j • v j = v i
  simp [Pi.single_apply]



theorem affineSimplexMap_mem_convexHull {ι : Type*} [Fintype ι] (v : ι → E)
    (t : stdSimplex ℝ ι) : affineSimplexMap v t ∈ convexHull ℝ (range v) :=
  (convex_convexHull ℝ (range v)).sum_mem (fun i _ => t.property.1 i) t.property.2
    (fun i _ => subset_convexHull ℝ (range v) ⟨i, rfl⟩)



theorem affineSimplexMap_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (v : κ → E) (t : stdSimplex ℝ ι) :
    affineSimplexMap v (stdSimplex.map f t) = affineSimplexMap (v ∘ f) t := by
  classical
  change (∑ j, (FunOnFinite.linearMap ℝ ℝ f t.val) j • v j) = ∑ i, t.val i • v (f i)
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  calc
    (∑ j, ∑ i with f i = j, t.val i • v j) =
        ∑ j, ∑ i with f i = j, t.val i • v (f i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, t.val i • v (f i) := Finset.sum_fiberwise Finset.univ f _


def affineSingularSimplex (n : ℕ) (v : Fin (n + 1) → E) : integralSingularSimplex n E :=
  (integralSingularSimplexEquiv n E).symm (affineSimplexMap v)


theorem affineSingularSimplex_face (n : ℕ) (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i (affineSingularSimplex (n + 1) v) =
      affineSingularSimplex n (v ∘ i.succAbove) := by
  apply (integralSingularSimplexEquiv n E).injective
  apply ContinuousMap.ext
  intro t
  change (TopCat.of E).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of E)).δ i
    (affineSingularSimplex (n + 1) v)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv (n + 1) E
    ((integralSingularSimplexEquiv (n + 1) E).symm (affineSimplexMap v))
      (stdSimplex.map i.succAbove t) =
    integralSingularSimplexEquiv n E ((integralSingularSimplexEquiv n E).symm
      (affineSimplexMap (v ∘ i.succAbove))) t
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact affineSimplexMap_map i.succAbove v t

end DifferentialGeometry.Topology
