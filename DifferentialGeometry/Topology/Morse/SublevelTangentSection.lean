import DifferentialGeometry.Bundle.TangentSectionPullback
import DifferentialGeometry.Topology.Morse.SublevelEuclidean

namespace DifferentialGeometry.Topology.Morse

open Bundle
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

private theorem sublevelInclusion_isInvertible (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    ∀ x : SublevelSpace f a,
      (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
        (Subtype.val : SublevelSpace f a → M) x).IsInvertible := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  intro x
  let L : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] MorseModel (m + 1) :=
    mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
    (Subtype.val : SublevelSpace f a → M) x
  let e := (LinearEquiv.ofBijective L.toLinearMap
    (mfderiv_manifoldSublevelEuclideanInclusion_bijective I f a hf hreg x)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

def sublevelTangentSection (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (X : Cₛ^∞⟮I; MorseModel (m + 1), (TangentSpace I : M → Type)⟯) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    Cₛ^∞⟮modelWithCornersEuclideanHalfSpace (m + 1); EuclideanSpace ℝ (Fin (m + 1)),
      (TangentSpace (modelWithCornersEuclideanHalfSpace (m + 1)) : SublevelSpace f a → Type)⟯ := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  exact pullbackTangentSection (Subtype.val : SublevelSpace f a → M)
    (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg)
    (sublevelInclusion_isInvertible I f a hf hreg) X

theorem mfderiv_sublevelTangentSection (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (X : Cₛ^∞⟮I; MorseModel (m + 1), (TangentSpace I : M → Type)⟯) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    ∀ x : SublevelSpace f a,
      mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
        (Subtype.val : SublevelSpace f a → M) x (sublevelTangentSection I f a hf hreg X x) = X x.1 := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  exact mfderiv_pullbackTangentSection _
    (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg)
    (sublevelInclusion_isInvertible I f a hf hreg) X

theorem mvfderiv_sublevelTangentSection (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (X : Cₛ^∞⟮I; MorseModel (m + 1), (TangentSpace I : M → Type)⟯)
    (u : M → ℝ) (x : SublevelSpace f a) (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x.1) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    mvfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) (fun y : SublevelSpace f a => u y.1) x
      (sublevelTangentSection I f a hf hreg X x) = mvfderiv I u x.1 (X x.1) := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  exact mvfderiv_pullbackTangentSection _
    (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg)
    (sublevelInclusion_isInvertible I f a hf hreg) X u x hu

end

end DifferentialGeometry.Topology.Morse
