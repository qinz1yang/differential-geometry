import DifferentialGeometry.Topology.Morse.SublevelEuclidean
import DifferentialGeometry.Geometry.Boundary.Corestrict
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

namespace DifferentialGeometry.Topology.Morse

open Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

def manifoldSublevelBoundaryDiffeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    BoundaryManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a)
      ≃ₘ⟮HasSmoothBoundary.boundaryModel (modelWithCornersEuclideanHalfSpace (m + 1)),
        𝓘(ℝ, MorseModel m)⟯ LevelSetSpace f a := by
  letI := manifoldSublevelChartedSpace I f a hf hreg
  letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
  letI := manifoldLevelSetChartedSpace I f a hf hreg
  letI := manifoldLevelSetIsManifold I f a hf hreg
  let e := manifoldSublevelEuclideanBoundaryHomeomorph I f a hf hreg
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hc := (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg).comp
      (boundaryInclusion_contMDiff (I := modelWithCornersEuclideanHalfSpace (m + 1))
        (M := SublevelSpace f a))
    exact contMDiff_levelSet_factor I f a hf hreg
      (fun x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a) =>
        x.1.1) hc
      (fun x => (manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg x.1).mp x.2)
  · have hc := contMDiff_levelSetSublevelInclusion (I := I) f a hf hreg
    have hce := (manifoldSublevelEuclideanDiffeomorph I f a hf hreg).contMDiff.comp hc
    exact contMDiff_boundaryCorestrict
      (fun x : LevelSetSpace f a => (⟨x.1, le_of_eq x.2⟩ : SublevelSpace f a)) hce
      (fun x => (manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg _).mpr x.2)

@[simp]
theorem manifoldSublevelBoundaryDiffeomorph_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    ∀ x, (manifoldSublevelBoundaryDiffeomorph I f a hf hreg x).1 = x.1.1 := fun _ => rfl

@[simp]
theorem manifoldSublevelBoundaryDiffeomorph_symm_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : LevelSetSpace f a) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    ((manifoldSublevelBoundaryDiffeomorph I f a hf hreg).symm x).1.1 = x.1 := rfl

end

end DifferentialGeometry.Topology.Morse
