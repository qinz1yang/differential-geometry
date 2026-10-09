import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReconstruction

noncomputable section

open Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem hasDerivWithinAt_parametric_chart_of_velocity_eq
    {g : ℝ → SmoothRiemannianMetric I M} {c : CurveMap M} {J : Set ℝ}
    (β : M) (x t : ℝ)
    (htime : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) J t)
    (hslice : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hchart : c.lift x t ∈ (extChartAt I β).source)
    (heq : c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t) :
    HasDerivWithinAt (fun τ => extChartAt I β (c.lift x τ))
      (curveShorteningParametricChartRhs g β
        (t, extChartAt I β (c.lift x t), deriv (fun y => extChartAt I β (c.lift y t)) x,
          deriv (deriv (fun y => extChartAt I β (c.lift y t))) x)) J t := by
  have hsrc : c.lift x t ∈ (chartAt H β).source := by
    rwa [extChartAt_source] at hchart
  have hcoord : DifferentiableWithinAt ℝ (fun τ => extChartAt I β (c.lift x τ)) J t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp
      ((mdifferentiableAt_extChartAt (I := I) hsrc).comp_mdifferentiableWithinAt t htime)
  have hbridge := chartCoord_mfderivWithin_along_curve_eq_fderivWithin
    htime htime.continuousWithinAt hJ.uniqueMDiffWithinAt hsrc
  have hrhs := trivToE_parametric_acceleration_eq_chart g c β x t hslice hchart
  have hvel : derivWithin (fun τ => extChartAt I β (c.lift x τ)) J t =
      curveShorteningParametricChartRhs g β
        (t, extChartAt I β (c.lift x t), deriv (fun y => extChartAt I β (c.lift y t)) x,
          deriv (deriv (fun y => extChartAt I β (c.lift y t))) x) := by
    rw [← hrhs, ← heq]
    exact hbridge.symm
  rw [← hvel]
  exact hcoord.hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace K] {I' : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold I' ∞ N]

theorem velocity_comp_eq_parametric_acceleration
    {g : ℝ → SmoothRiemannianMetric I M} {g' : ℝ → SmoothRiemannianMetric I' N}
    {e : M → N} (he : ContMDiff I I' ∞ e)
    (hg : ∀ t p v w, (g' t).inner (e p) (mfderiv I I' e p v) (mfderiv I I' e p w) =
      (g t).inner p v w)
    (hII : ∀ t, hasVanishingSecondFundamentalFormAlongCurves (g t) (g' t) e)
    {c : CurveMap M} {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    {x t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (heq : c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t) :
    CurveMap.velocity (I := I') (fun z τ => e (c z τ)) J x t =
      CurveMap.speed (I := I') (fun z τ => e (c z τ)) g' x t ^ (-2 : ℤ) •
        CurveMap.Dx (I := I') (fun z τ => e (c z τ)) g'
          (CurveMap.X (I := I') (fun z τ => e (c z τ))) x t := by
  have hs := c.smooth_slice hc ht
  have htime := (c.time_slice_contMDiffWithinAt J hc x t ht).mdifferentiableWithinAt
    (by simp)
  rw [velocity_comp he htime hJ, heq, map_smul,
    speed_comp_of_inner_map he hg (hs.mdifferentiableAt (by simp)),
    Dx_X_comp_of_vanishingSecondFundamentalForm hII hs x]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section

open Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem hasDerivWithinAt_retraction_chart_of_parametric_equation
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    {c : CurveMap M} {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    {x t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (heq : c.velocity (I := I) J x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t) :
    HasDerivWithinAt (fun s => e (c.lift x s))
      (curveShorteningParametricChartRhs (fun s => retractionMetric (g s) he hr) β
        (t, e (c.lift x t), deriv (fun y => e (c.lift y t)) x,
          deriv (deriv (fun y => e (c.lift y t))) x)) J t := by
  let j : M → U := fun p => ⟨e p, hEU (mem_range_self p)⟩
  have hj : ContMDiff I 𝓘(ℝ, F) ∞ j := (ContMDiff.subtypeVal_comp_iff U j).mp he
  have hmetric : ∀ s p v w,
      (retractionMetric (g s) he hr).inner (j p)
        (mfderiv I 𝓘(ℝ, F) j p v) (mfderiv I 𝓘(ℝ, F) j p w) = (g s).inner p v w := by
    intro s p v w
    rw [← mfderiv_subtypeVal_comp j p]
    exact retractionMetric_inner_map (g s) he hr hEU hleft p v w
  let d : CurveMap U := fun z s => j (c z s)
  have hd : d.SmoothOn (I := 𝓘(ℝ, F)) J := hj.comp_contMDiffOn hc
  have hdtime := (d.time_slice_contMDiffWithinAt J hd x t ht).mdifferentiableWithinAt
    (by simp)
  have hdslice : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 (fun y => d.lift y t) x :=
    (d.smooth_slice hd ht).contMDiffAt.of_le (by decide)
  have hdeq := velocity_comp_eq_parametric_acceleration hj hmetric
    (fun s => hasVanishingSecondFundamentalFormAlongCurves_retractionMetric
      (g s) he hr hEU hleft) hc ht hJ heq
  have hpde := hasDerivWithinAt_parametric_chart_of_velocity_eq β x t hdtime hdslice hJ
    (by rw [DifferentialGeometry.extChartAt_opens_source]; trivial) hdeq
  simpa only [DifferentialGeometry.extChartAt_opens_apply, CurveMap.lift, d, j] using hpde

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end
