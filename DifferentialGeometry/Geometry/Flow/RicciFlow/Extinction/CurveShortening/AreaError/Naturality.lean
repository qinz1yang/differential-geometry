import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReconstruction

noncomputable section
open Set Manifold
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curve
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace K] {I' : ModelWithCorners ℝ F K} [I'.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold I' ∞ N]

theorem areaError_comp_of_vanishingSecondFundamentalForm
    {g : ℝ → SmoothRiemannianMetric I M} {g' : ℝ → SmoothRiemannianMetric I' N}
    {e : M → N} (he : ContMDiff I I' ∞ e)
    (hg : ∀ t p v w, (g' t).inner (e p) (mfderiv I I' e p v) (mfderiv I I' e p w) =
      (g t).inner p v w)
    (hII : ∀ t, hasVanishingSecondFundamentalFormAlongCurves (g t) (g' t) e)
    {c : CurveMap M} {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) :
    CurveMap.areaError (I := I') (fun z τ => e (c z τ)) g' J t = c.areaError g J t := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hs' : ContMDiff 𝓘(ℝ, ℝ) I' ∞
      (fun y => CurveMap.lift (fun z τ => e (c z τ)) y t) := he.comp hs
  unfold areaError integral
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [areaError_integrand_eq_normalVelocityErrorDensity (fun z τ => e (c z τ)) g' J x t ((hs' x).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)),
    areaError_integrand_eq_normalVelocityErrorDensity c g J x t ((hs x).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out))]
  have hX : CurveMap.X (I := I') (fun z τ => e (c z τ)) x t =
      mfderiv I I' e (c.lift x t) (c.X (I := I) x t) :=
    mfderiv_comp_apply x (he.mdifferentiableAt (by simp)) (hs.mdifferentiableAt (by simp)) 1
  have hV := velocity_comp he
    ((c.time_slice_contMDiffWithinAt J hc x t ht).mdifferentiableWithinAt (by simp)) hJ
  have hA := Dx_X_comp_of_vanishingSecondFundamentalForm hII hs x
  rw [hX, hV, hA]
  exact normalVelocityErrorDensity_comp _ _ (mfderiv I I' e (c.lift x t)).toLinearMap
    (hg t (c.lift x t)) _ _ _

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end
