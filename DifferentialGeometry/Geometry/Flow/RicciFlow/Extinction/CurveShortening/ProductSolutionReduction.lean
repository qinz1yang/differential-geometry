import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CoverCovariantDerivative
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem uniqueMDiffWithinAt_of_mem_Ico_or_Icc {s u t : ℝ} {J : Set ℝ} (hsu : s < u)
    (hJ : J = Ico s u ∨ J = Icc s u) (ht : t ∈ J) :
    UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t := by
  have h : UniqueDiffWithinAt ℝ J t := by
    rcases hJ with rfl | rfl
    · exact uniqueDiffOn_Ico s u t ht
    · exact uniqueDiffOn_Icc hsu t ht
  exact h.uniqueMDiffWithinAt

namespace ProductCurve

def CoverSmoothLift (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (c : ProductCurve M) (J : Set ℝ) : Prop :=
  letI := A.charts
  letI := A.smoothManifold
  c.map.SmoothOn (I := I.prod 𝓘(ℝ, ℝ)) J → c.SmoothOn (I := I) J

omit [CompleteSpace E] in
theorem map_isSolutionOn_of_frontiers
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) {J : Set ℝ}
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J)
    (huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t)
    (hc : c.IsSolutionOn g lambda J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  let := A.charts
  let := A.smoothManifold
  exact c.map_isSolutionOn_of_isSolutionOn A g lambda hlambda huniq hc hU

omit [CompleteSpace E] in
theorem isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) {J : Set ℝ}
    (hlift : CoverSmoothLift A c J)
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J)
    (huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t)
    (hm : letI := A.charts
      letI := A.smoothManifold
      c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J) :
    c.IsSolutionOn g lambda J := by
  let := A.charts
  let := A.smoothManifold
  have hc : c.SmoothOn (I := I) J := hlift hm.smooth
  refine ⟨hc, (c.map_immersedOn_iff A hc).mp hm.immersed, ?_⟩
  intro x t ht
  have h1 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
      (c.coverLift x t) (c.velocity (I := I) J x t) =
      c.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t :=
    (c.map_velocity_eq A J hc x t ht (huniq t ht)).symm
  have h2 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
      (c.coverLift x t) (c.curvatureVector (I := I) g lambda x t) =
      c.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t :=
    (c.map_curvatureVector_eq A g lambda hlambda hc hU x t ht).trans
      (hm.equation x t ht).symm
  exact (A.cover_derivative_bijective (c.coverLift x t)).injective (h1.trans h2.symm)

omit [CompleteSpace E] in
theorem product_solution_iff_of_frontiers
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) {s u : ℝ} (hsu : s < u) {J : Set ℝ}
    (hJ : J = Ico s u ∨ J = Icc s u)
    (hlift : CoverSmoothLift A c J)
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J) :
    letI := A.charts
    letI := A.smoothManifold
    c.IsSolutionOn g lambda J ↔
      c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  let := A.charts
  let := A.smoothManifold
  have huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t :=
    fun _ ht => uniqueMDiffWithinAt_of_mem_Ico_or_Icc hsu hJ ht
  exact ⟨c.map_isSolutionOn_of_frontiers A g lambda hlambda hU huniq,
    c.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift A g lambda hlambda hlift hU huniq⟩

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
