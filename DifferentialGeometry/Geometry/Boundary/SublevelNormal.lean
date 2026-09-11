import DifferentialGeometry.Geometry.Boundary.SublevelMetric
import DifferentialGeometry.Geometry.Boundary.ExtremumNormal
import DifferentialGeometry.Geometry.Boundary.PullbackNormal

namespace DifferentialGeometry.Topology.Morse

open Integral.DivergenceTheorem.WithBoundary Geometry.Operator Geometry.Boundary
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem mfderiv_outwardNormal_sublevelMetric (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    ∀ x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a),
      mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
        (fun y : SublevelSpace f a => y.1) x.1 (outwardNormal (sublevelMetric I g f a hf hreg) x) =
        levelSetOutwardNormal g f x.1.1 := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  intro x
  let J := modelWithCornersEuclideanHalfSpace (m + 1)
  let ι : SublevelSpace f a → M := fun y => y.1
  have hι : ContMDiff J I ∞ ι := contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg
  have hιd := (hι x.1).mdifferentiableAt (by simp)
  have hfd := (hf x.1.1).mdifferentiableAt (by simp)
  have hbij := mfderiv_manifoldSublevelEuclideanInclusion_bijective I f a hf hreg x.1
  have hx : f x.1.1 = a :=
    (manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg x.1).mp x.2
  have hmax : IsLocalMax (f ∘ ι) x.1 := by
    apply Filter.Eventually.of_forall
    intro y
    change f y.1 ≤ f x.1.1
    rw [hx]
    exact y.2
  have hregι : mfderiv J 𝓘(ℝ, ℝ) (f ∘ ι) x.1 ≠ 0 := by
    intro hz
    apply hreg x.1.1 hx
    change mfderiv I 𝓘(ℝ, ℝ) f x.1.1 = 0
    ext v
    obtain ⟨w, rfl⟩ := hbij.surjective v
    have hc := congrArg (fun L => L w) (mfderiv_comp x.1 hfd hιd)
    rw [hz] at hc
    exact hc.symm
  have hn := outwardNormal_eq_levelSetOutwardNormal_of_isLocalMax
    (sublevelMetric I g f a hf hreg) hmax (hfd.comp x.1 hιd) hregι
  rw [hn]
  exact mfderiv_levelSetOutwardNormal_pullback g ι hι
    (fun y => (mfderiv_manifoldSublevelEuclideanInclusion_bijective I f a hf hreg y).injective)
    f x.1 hfd hbij.surjective

theorem sublevelMetric_outwardNormal_inner (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    ∀ (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a)) v,
      (sublevelMetric I g f a hf hreg).inner x.1 (outwardNormal (sublevelMetric I g f a hf hreg) x) v =
        (Real.sqrt (normGradSqFun g f x.1.1))⁻¹ * mvfderiv I f x.1.1
          (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
            (fun y : SublevelSpace f a => y.1) x.1 v) := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  intro x v
  rw [sublevelMetric_inner, mfderiv_outwardNormal_sublevelMetric, levelSetOutwardNormal_inner]

end

end DifferentialGeometry.Topology.Morse
