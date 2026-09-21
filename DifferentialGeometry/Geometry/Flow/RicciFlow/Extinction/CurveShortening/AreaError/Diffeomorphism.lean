import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport

section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem velocity_postcomposeDiffeomorph
    (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) {J : Set ℝ} {x t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) J t)
    (hJ : UniqueDiffWithinAt ℝ J t) :
    (c.postcomposeDiffeomorph Φ).velocity J x t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.velocity J x t) := by
  have h := mfderiv_comp_mfderivWithin t (Φ.contMDiff.mdifferentiableAt (by simp)) hc
    hJ.uniqueMDiffWithinAt
  exact congrArg (fun L => L (1 : ℝ)) h

theorem curvatureVector_postcomposeDiffeomorph_of_mem [I.Boundaryless] [T2Space Q] [T2Space A]
    (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : ℝ → SmoothRiemannianMetric I Q)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    (c.postcomposeDiffeomorph Φ).curvatureVector
        (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) x t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.curvatureVector g x t) := by
  have hV : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t)
      (fun y => c.unitTangent g y t) x) x :=
    Variation.chartRepAt_differentiableAt_of_total_contMDiffAt
      ((c.unitTangent_contMDiff g J hc hi t ht).contMDiffAt.of_le
        (by decide : (2 : WithTop ℕ∞) ≤ ∞))
  have hVT : (fun y => (c.postcomposeDiffeomorph Φ).unitTangent
      (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) y t) =
      fun y => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift y t) (c.unitTangent g y t) := by
    funext y
    exact unitTangent_postcomposeDiffeomorph c Φ g y t (slice_mdifferentiableAt c J hc t ht y)
  change ((c.postcomposeDiffeomorph Φ).speed
      (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) x t)⁻¹ •
      covDerivAlong (Diffeomorph.pullbackMetricCross (g t) Φ.symm)
        (fun y => Φ (c.lift y t))
        (fun y => (c.postcomposeDiffeomorph Φ).unitTangent
          (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) y t) x = _
  rw [hVT, covDerivAlong_comp_symm (g t) Φ (fun y => c.lift y t)
    (fun y => c.unitTangent g y t) x (slice_contMDiffAt c J hc t ht x) hV,
    speed_postcomposeDiffeomorph c Φ g x t (slice_mdifferentiableAt c J hc t ht x)]
  exact (map_smul _ _ _).symm

theorem normalVelocityError_postcomposeDiffeomorph [I.Boundaryless] [T2Space Q] [T2Space A]
    (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : ℝ → SmoothRiemannianMetric I Q)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) :
    (c.postcomposeDiffeomorph Φ).normalVelocityError
        (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) J x t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.normalVelocityError g J x t) := by
  have hvel := velocity_postcomposeDiffeomorph c Φ
    ((c.time_slice_contMDiffWithinAt J hc x t ht).mdifferentiableWithinAt (by simp)) hJ
  have hcurv := curvatureVector_postcomposeDiffeomorph_of_mem c Φ g hc hi x t ht
  have hT := unitTangent_postcomposeDiffeomorph c Φ g x t (slice_mdifferentiableAt c J hc t ht x)
  let L := mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t)
  let W := c.velocity J x t - c.curvatureVector g x t
  let T := c.unitTangent g x t
  have hsub : L (c.velocity J x t) - L (c.curvatureVector g x t) = L W :=
    (map_sub L _ _).symm
  have hinner := Diffeomorph.inner_pullbackMetricCross_comp (g t) Φ (c.lift x t) W T
  simp only [normalVelocityError, hvel, hcurv, hT, lift_postcomposeDiffeomorph]
  change L (c.velocity J x t) - L (c.curvatureVector g x t) -
    (Diffeomorph.pullbackMetricCross (g t) Φ.symm).inner (Φ (c.lift x t))
      (L (c.velocity J x t) - L (c.curvatureVector g x t)) (L T) • L T =
    L (W - (g t).inner (c.lift x t) W T • T)
  rw [hsub, hinner]
  exact ((map_sub L W ((g t).inner (c.lift x t) W T • T)).trans
    (congrArg (fun v => L W - v) (map_smul L ((g t).inner (c.lift x t) W T) T))).symm

theorem areaError_postcomposeDiffeomorph [I.Boundaryless] [T2Space Q] [T2Space A]
    (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : ℝ → SmoothRiemannianMetric I Q)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) :
    (c.postcomposeDiffeomorph Φ).areaError
        (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) J t = c.areaError g J t := by
  simp only [areaError, integral]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [speed_postcomposeDiffeomorph c Φ g x t (slice_mdifferentiableAt c J hc t ht x)]
  simp only [normSq, normalVelocityError_postcomposeDiffeomorph c Φ g hc hi x t ht hJ,
    lift_postcomposeDiffeomorph]
  exact congrArg (fun v : ℝ => Real.sqrt v * c.speed g x t)
    (Diffeomorph.inner_pullbackMetricCross_comp (g t) Φ (c.lift x t)
      (c.normalVelocityError g J x t) (c.normalVelocityError g J x t))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

end

section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
  [T2Space A] [CompactSpace A] [SigmaCompactSpace A]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [SigmaCompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
  [CompactSpace A] [SigmaCompactSpace A] in
theorem CurveMap.SmoothOn.postcomposeDiffeomorph {c : CurveMap M} {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (Φ : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) :
    (c.postcomposeDiffeomorph Φ).SmoothOn (I := 𝓘(ℝ, E)) J :=
  Φ.contMDiff.comp_contMDiffOn hc

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [SigmaCompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
  [CompactSpace A] [SigmaCompactSpace A] in
theorem CurveMap.ImmersedOn.postcomposeDiffeomorph {c : CurveMap M} {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (Φ : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) :
    (c.postcomposeDiffeomorph Φ).ImmersedOn (I := 𝓘(ℝ, E)) J := by
  intro x t ht hz
  have hX := c.X_postcomposeDiffeomorph Φ x t ((c.smooth_slice hc ht).mdifferentiableAt (by simp))
  have hv : mfderiv I 𝓘(ℝ, E) (Φ : M → A) (c.lift x t) (c.X x t) = 0 := hX.symm.trans hz
  have hinv := congrArg (fun v => mfderiv 𝓘(ℝ, E) I (Φ.symm : A → M) (Φ (c.lift x t)) v) hv
  rw [Diffeomorph.mfderiv_symm_apply_mfderiv_apply, map_zero] at hinv
  exact hi x t ht hinv

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
