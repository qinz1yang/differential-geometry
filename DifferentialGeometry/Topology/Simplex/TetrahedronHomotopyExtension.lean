import DifferentialGeometry.Topology.Simplex.HomotopyExtension
import DifferentialGeometry.Topology.Simplex.TetrahedronOneSkeleton

noncomputable section
namespace DifferentialGeometry.Simplex
variable {X : Type*} [TopologicalSpace X]

theorem exists_continuous_homotopy_extension_tetrahedronOneSkeleton
    (f : C(stdSimplex ℝ (Fin 4), X))
    (H : C(unitInterval × tetrahedronOneSkeleton, X))
    (hH : ∀ p : tetrahedronOneSkeleton, H (0, p) = f p.val) :
    ∃ F : C(unitInterval × stdSimplex ℝ (Fin 4), X),
      (∀ p, F (0, p) = f p) ∧
      ∀ t (p : tetrahedronOneSkeleton), F (t, p.val) = H (t, p) := by
  classical
  have hface (i : Fin 4) :
      ∃ G : C(unitInterval × stdSimplex ℝ (Fin 3), X),
        (∀ p, G (0, p) = f (stdSimplex.map i.succAbove p)) ∧
        ∀ t (q : boundary (Fin 3)),
          G (t, q.val) = H (t, faceBoundaryIntoTetrahedronOneSkeleton i q) := by
    let fi : C(stdSimplex ℝ (Fin 3), X) :=
      f.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩
    let Hi : C(unitInterval × boundary (Fin 3), X) :=
      H.comp ⟨fun z => (z.1, faceBoundaryIntoTetrahedronOneSkeleton i z.2),
        continuous_fst.prodMk ((faceBoundaryIntoTetrahedronOneSkeleton i).continuous.comp continuous_snd)⟩
    have hHi : ∀ q : boundary (Fin 3), Hi (0, q) = fi q.val := by
      intro q
      exact hH (faceBoundaryIntoTetrahedronOneSkeleton i q)
    exact exists_continuous_homotopy_extension 2 fi Hi hHi
  choose G hG0 hGb using hface
  have hcomp : ∀ (i : Fin 4) (j : Fin 3)
      (p : stdSimplex ℝ (Fin 2)) (t : unitInterval),
      G i (t, stdSimplex.map j.succAbove p) =
        G (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j p t
    exact tetrahedronOneSkeleton_restriction_compatibility
      (fun i q => G i (t, q)) (fun q => H (t, q)) (fun i q => hGb i t q) i j p
  obtain ⟨F, hF0, hFb⟩ := exists_continuous_homotopy_extension_of_faces 1 f G (fun i j t p => hcomp i j p t) hG0
  refine ⟨F, hF0, ?_⟩
  intro t p
  obtain ⟨i, q, rfl⟩ := exists_faceBoundaryIntoTetrahedronOneSkeleton_eq p
  exact (hFb i t q.val).trans (hGb i t q)

end DifferentialGeometry.Simplex
