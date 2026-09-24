import DifferentialGeometry.Topology.Simplex.TetrahedronOneSkeletonGluing
import Mathlib.Order.Fin.Basic
import DifferentialGeometry.Topology.Simplex.MapInjectivity

noncomputable section
namespace DifferentialGeometry.Simplex
open Set

theorem edgeIntoTetrahedronOneSkeleton_injective (i : Fin 4) (j : Fin 3) :
    Function.Injective (edgeIntoTetrahedronOneSkeleton i j) := by
  intro p q h
  apply (faceHomeomorph j).injective
  apply Subtype.ext
  apply (faceHomeomorph i).injective
  apply Subtype.ext
  change stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p) =
    stdSimplex.map i.succAbove (stdSimplex.map j.succAbove q)
  exact congrArg (fun r : tetrahedronOneSkeleton => r.val) h

theorem edgeIntoTetrahedronOneSkeleton_eq_of_not_mem_boundary
    (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2))
    (hp : p ∉ boundary (Fin 2))
    (h : edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q) :
    edgeIntoTetrahedronOneSkeleton i j = edgeIntoTetrahedronOneSkeleton k l ∧ p = q := by
  have hmap : stdSimplex.map (i.succAbove ∘ j.succAbove) p =
      stdSimplex.map (k.succAbove ∘ l.succAbove) q := by
    rw [← stdSimplex.map_comp_apply, ← stdSimplex.map_comp_apply]
    exact congrArg (fun r : tetrahedronOneSkeleton => r.val) h
  obtain ⟨hf, hpq⟩ := stdSimplex.eq_and_eq_of_map_eq_of_strictMono
    ((Fin.strictMono_succAbove i).comp (Fin.strictMono_succAbove j))
    ((Fin.strictMono_succAbove k).comp (Fin.strictMono_succAbove l))
    (fun a ha => hp ⟨a, ha⟩) hmap
  refine ⟨?_, hpq⟩
  apply ContinuousMap.ext
  intro r
  apply Subtype.ext
  change stdSimplex.map i.succAbove (stdSimplex.map j.succAbove r) =
    stdSimplex.map k.succAbove (stdSimplex.map l.succAbove r)
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, hf]

theorem edgeIntoTetrahedronOneSkeleton_intersection
    (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2))
    (h : edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q) :
    (edgeIntoTetrahedronOneSkeleton i j = edgeIntoTetrahedronOneSkeleton k l ∧ p = q) ∨
      (p ∈ boundary (Fin 2) ∧ q ∈ boundary (Fin 2)) := by
  by_cases hp : p ∈ boundary (Fin 2)
  · by_cases hq : q ∈ boundary (Fin 2)
    · exact Or.inr ⟨hp, hq⟩
    · obtain ⟨he, hpq⟩ := edgeIntoTetrahedronOneSkeleton_eq_of_not_mem_boundary k i l j q p hq h.symm
      exact Or.inl ⟨he.symm, hpq.symm⟩
  · exact Or.inl (edgeIntoTetrahedronOneSkeleton_eq_of_not_mem_boundary i k j l p q hp h)

end DifferentialGeometry.Simplex
