import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem velocity_congr {c c' : CurveMap M} {J : Set ℝ}
    (h : ∀ x t, t ∈ J → c'.lift x t = c.lift x t) {x t : ℝ} (ht : t ∈ J) :
    c'.velocity (I := I) J x t = c.velocity (I := I) J x t := by
  have hL : (c'.lift x) =ᶠ[𝓝[J] t] (c.lift x) :=
    Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => h x y hy
  have hx : (c'.lift x) t = (c.lift x) t := h x t ht
  have heq : mfderivWithin 𝓘(ℝ, ℝ) I (c'.lift x) J t =
      mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x) J t :=
    Filter.EventuallyEq.mfderivWithin_eq (I := 𝓘(ℝ, ℝ)) (I' := I) hL hx
  simp only [velocity]
  exact congrArg (fun L => L (1 : ℝ)) heq

omit [CompleteSpace E] in
theorem isSolutionOn_congr {c c' : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M}
    {J : Set ℝ} (h : ∀ x t, t ∈ J → c'.lift x t = c.lift x t)
    (hc : c.IsSolutionOn (I := I) g J) : c'.IsSolutionOn (I := I) g J where
  smooth := hc.smooth.congr fun p hp => h p.1 p.2 hp.2
  immersed := fun x t ht => by
    rw [X_congr (c := c') (d := c) (t := t) (fun z => h z t ht) x]
    exact hc.immersed x t ht
  equation := fun x t ht => by
    have hv : c'.velocity (I := I) J x t = c.velocity (I := I) J x t := velocity_congr h ht
    have hcv : c'.curvatureVector g x t = c.curvatureVector g x t :=
      curvatureVector_congr (c := c') (d := c) (g := g) (t := t) (fun z => h z t ht) x
    exact hv.trans ((hc.equation x t ht).trans hcv.symm)

end CurveMap

omit [CompleteSpace E] in
theorem product_solution_lift_of_coverCurve
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : CurveMap (M × Surgery.Topology.Circle)) (ĉ : ProductCurve M)
    {s u : ℝ} (hsu : s < u) (J : Set ℝ) (hJ : J = Ico s u ∨ J = Icc s u)
    (hmap : ∀ z t, t ∈ J → ĉ.map z t = c z t)
    (hyc : ContinuousOn (fun p : ℝ × ℝ => ĉ.y p.1 p.2) (univ ×ˢ J))
    (htangent : (ĉ.unitTangent g lambda).SmoothOn (I := I) J)
    (hc : letI := A.charts
      letI := A.smoothManifold
      c.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J) :
    ĉ.IsSolutionOn g lambda J ∧ ∀ z t, t ∈ J → ĉ.map z t = c z t := by
  have huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t :=
    fun t ht => uniqueMDiffWithinAt_of_mem_Ico_or_Icc hsu hJ ht
  refine ⟨?_, hmap⟩
  let := A.charts
  let := A.smoothManifold
  have hsol : (ĉ.map).IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J :=
    CurveMap.isSolutionOn_congr (I := I.prod 𝓘(ℝ, ℝ))
      (M := M × Surgery.Topology.Circle)
      (fun x t ht => hmap (x : Surgery.Topology.Circle) t ht) hc
  exact ĉ.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift A g lambda hlambda
    hyc htangent huniq hsol

omit [CompleteSpace E] in
theorem product_solution_lift_of_frontiers
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : CurveMap (M × Surgery.Topology.Circle)) {s u : ℝ} (hsu : s < u) (J : Set ℝ)
    (hJ : J = Ico s u ∨ J = Icc s u)
    (hLift : ∃ ĉ : ProductCurve M, (∀ z t, t ∈ J → ĉ.map z t = c z t) ∧
      ContinuousOn (fun p : ℝ × ℝ => ĉ.y p.1 p.2) (univ ×ˢ J) ∧
      (ĉ.unitTangent g lambda).SmoothOn (I := I) J)
    (hc : letI := A.charts
      letI := A.smoothManifold
      c.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J) :
    ∃ ĉ : ProductCurve M, ĉ.IsSolutionOn g lambda J ∧
      ∀ z t, t ∈ J → ĉ.map z t = c z t := by
  obtain ⟨ĉ, hmap, hyc, htangent⟩ := hLift
  exact ⟨ĉ, (product_solution_lift_of_coverCurve A g lambda hlambda c ĉ hsu J hJ
    hmap hyc htangent hc).1, hmap⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
