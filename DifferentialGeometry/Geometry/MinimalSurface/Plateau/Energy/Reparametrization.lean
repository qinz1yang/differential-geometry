import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Analysis.Integration.Measure.LipschitzChangeOfVariables
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Analysis.Calculus.Complex.RadialExtension
import DifferentialGeometry.Tensor.LinearAlgebra.PlanarBilinear

noncomputable section

open Manifold MeasureTheory Set Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem riemannianDiskEnergy_inverse_reparametrize
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (φ : closedDisk ≃ₜ closedDisk) (hφ : LipschitzWith K φ) (hψ : LipschitzWith L φ.symm) :
    let Φ : ℂ → ℂ := diskExtension (fun z => (φ z : ℂ))
    let Ψ : ℂ → ℂ := diskExtension (fun z => (φ.symm z : ℂ))
    let U := diskExtension u
    riemannianDiskEnergy g (u ∘ φ.symm) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        |(fderiv ℝ Φ z).toLinearMap.det| *
          (g.inner (U z)
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) 1))
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) 1)) +
            g.inner (U z)
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) Complex.I))
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) Complex.I))) / 2 := by
  let Φ : ℂ → ℂ := diskExtension (fun z => (φ z : ℂ))
  let Ψ : ℂ → ℂ := diskExtension (fun z => (φ.symm z : ℂ))
  let U := diskExtension u
  have hΦ : LipschitzWith K Φ := diskExtension_lipschitz (fun x y => hφ x y)
  have hΨ : LipschitzWith L Ψ := diskExtension_lipschitz (fun x y => hψ x y)
  have hΦcoe (z : closedDisk) : Φ z = φ z := diskExtension_coe _ z
  have hΨcoe (z : closedDisk) : Ψ z = φ.symm z := diskExtension_coe _ z
  have hinv (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) : Ψ (Φ z) = z := by
    rw [hΦcoe ⟨z, hz⟩, hΨcoe (φ ⟨z, hz⟩), φ.symm_apply_apply]
  have himage : Φ '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hΦcoe ⟨z, hz⟩]
      exact (φ ⟨z, hz⟩).property
    · intro z hz
      refine ⟨φ.symm ⟨z, hz⟩, (φ.symm ⟨z, hz⟩).property, ?_⟩
      rw [hΦcoe, φ.apply_symm_apply]
  have hinj : InjOn Φ (Metric.closedBall (0 : ℂ) 1) := by
    intro x hx y hy hxy
    simpa only [hinv x hx, hinv y hy] using congrArg Ψ hxy
  have hcomp : diskExtension (u ∘ φ.symm) = U ∘ Ψ := by
    funext z
    change u (φ.symm (diskRetraction z)) = u (diskRetraction (Ψ z))
    rw [show Ψ z = (φ.symm (diskRetraction z) : ℂ) from rfl, diskRetraction_coe]
  change (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u ∘ φ.symm)) z) = _
  rw [hcomp]
  conv_lhs => rw [← himage]
  rw [integral_image_eq_integral_abs_det_of_lipschitz hΦ measurableSet_closedBall hinj]
  have hDU := ae_mdifferentiableAt_of_riemannian_lipschitz g
    (diskExtension_riemannian_lipschitz g hu)
  have hDΨ := ae_comp_of_lipschitz_leftInverse_on hΨ hinv
    (hΨ.ae_differentiableAt (μ := volume))
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hDU, ae_restrict_of_ae hDΨ,
    ae_restrict_mem measurableSet_closedBall] with z hUz hΨz hz
  have hUΦ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (Ψ (Φ z)) := by
    rw [hinv z hz]
    exact hUz
  have hchain := mfderiv_comp (Φ z) hUΦ (hΨz hz).mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hchain
  change |(fderiv ℝ Φ z).toLinearMap.det| • diskMapEnergyDensity g (U ∘ Ψ) (Φ z) = _
  unfold diskMapEnergyDensity diskMapPartial
  rw [hchain]
  simp only [Function.comp_apply]
  rw [hinv z hz]
  change |(fderiv ℝ Φ z).toLinearMap.det| *
    ((g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) 1))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) 1)) +
    g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) Complex.I))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (fderiv ℝ Ψ (Φ z) Complex.I))) / 2) = _
  dsimp only [Φ, Ψ, U]
  ring

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold MeasureTheory Set Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

theorem riemannianDiskEnergy_inverse_radial_reparametrize
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (δ : loopCircle ≃ₜ loopCircle) {f : ℝ → ℝ}
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = (f s : loopCircle))
    (hf : Differentiable ℝ f) (hpos : ∀ s, 0 < deriv f s)
    (hF : LipschitzWith K (geometricCircleHomeomorph δ))
    (hG : LipschitzWith L (geometricCircleHomeomorph δ).symm) :
    let φ := radialDiskHomeomorph (geometricCircleHomeomorph δ) hF hG
    let U := diskExtension u
    riemannianDiskEnergy g (u ∘ φ.symm) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        (deriv f (Complex.arg z / (2 * Real.pi)) *
            g.inner (U z) (diskMapPartial U z (radialDirection z))
              (diskMapPartial U z (radialDirection z)) +
          (deriv f (Complex.arg z / (2 * Real.pi)))⁻¹ *
            g.inner (U z) (diskMapPartial U z (Complex.I * (radialDirection z : ℂ)))
              (diskMapPartial U z (Complex.I * (radialDirection z : ℂ)))) / 2 := by
  let φ := radialDiskHomeomorph (geometricCircleHomeomorph δ) hF hG
  let Φ : ℂ → ℂ := diskExtension (fun z => (φ z : ℂ))
  let Ψ : ℂ → ℂ := diskExtension (fun z => (φ.symm z : ℂ))
  let U := diskExtension u
  have hΨ : LipschitzWith (2 * L + 1) Ψ :=
    diskExtension_lipschitz (radialDiskHomeomorph_symm_lipschitz _ hF hG)
  have hΦcoe (z : closedDisk) : Φ z = φ z := diskExtension_coe _ z
  have hΨcoe (z : closedDisk) : Ψ z = φ.symm z := diskExtension_coe _ z
  have hinv (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) : Ψ (Φ z) = z := by
    rw [hΦcoe ⟨z, hz⟩, hΨcoe (φ ⟨z, hz⟩), φ.symm_apply_apply]
  have hDΨ := ae_comp_of_lipschitz_leftInverse_on hΨ hinv
    (hΨ.ae_differentiableAt (μ := volume))
  change riemannianDiskEnergy g (u ∘ φ.symm) = _
  rw [riemannianDiskEnergy_inverse_reparametrize g hu φ
    (radialDiskHomeomorph_lipschitz _ hF hG)
    (radialDiskHomeomorph_symm_lipschitz _ hF hG)]
  apply integral_congr_ae
  filter_upwards [ae_disk_interior, ae_restrict_of_ae ae_mem_complex_slitPlane,
    ae_restrict_of_ae hDΨ] with z hz hzs hDz
  have hzclosed := Metric.ball_subset_closedBall hz
  have heqΦ : Φ =ᶠ[𝓝 z] radialExtension (geometricCircleHomeomorph δ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hΦcoe ⟨w, Metric.ball_subset_closedBall hw⟩
  have hdiffΦ : DifferentiableAt ℝ Φ z :=
    (hasFDerivAt_radialExtension_geometricCircleHomeomorph δ hδ hzs (hf _)).differentiableAt.congr_of_eventuallyEq heqΦ
  have heqcomp : Ψ ∘ Φ =ᶠ[𝓝 z] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hinv w (Metric.ball_subset_closedBall hw)
  have hBA : (fderiv ℝ Ψ (Φ z)).comp (fderiv ℝ Φ z) = 1 := by
    rw [← fderiv_comp z (hDz hzclosed) hdiffΦ, heqcomp.fderiv_eq]
    exact fderiv_id
  let e : ℂ := radialDirection z
  let e' : ℂ := geometricCircleHomeomorph δ (radialDirection z)
  let a := deriv f (Complex.arg z / (2 * Real.pi))
  have hrad : fderiv ℝ Φ z e = e' := by
    rw [heqΦ.fderiv_eq]
    exact fderiv_radialExtension_radialDirection δ hδ hzs (hf _)
  have htan : fderiv ℝ Φ z (Complex.I * e) = a • (Complex.I * e') := by
    rw [heqΦ.fderiv_eq]
    exact fderiv_radialExtension_tangentDirection δ hδ hzs (hf _)
  have hBr : fderiv ℝ Ψ (Φ z) e' = e := by
    have h := congrArg (fun A : ℂ →L[ℝ] ℂ => A e) hBA
    simpa only [ContinuousLinearMap.comp_apply, hrad, one_apply_eq_self] using h
  have hBt : fderiv ℝ Ψ (Φ z) (Complex.I * e') = a⁻¹ • (Complex.I * e) := by
    have h := congrArg (fun A : ℂ →L[ℝ] ℂ => A (Complex.I * e)) hBA
    simp only [ContinuousLinearMap.comp_apply, htan, map_smul, one_apply_eq_self] at h
    calc
      _ = a⁻¹ • (a • fderiv ℝ Ψ (Φ z) (Complex.I * e')) := by
        rw [inv_smul_smul₀ (ne_of_gt (hpos _))]
      _ = _ := by rw [h]
  have hdet : |(fderiv ℝ Φ z).toLinearMap.det| = a := by
    rw [heqΦ.fderiv_eq, det_fderiv_radialExtension_geometricCircleHomeomorph δ hδ hzs (hf _)]
    exact abs_of_pos (hpos _)
  let Q := (g.inner (U z)).bilinearComp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
  change |(fderiv ℝ Φ z).toLinearMap.det| *
      (Q (fderiv ℝ Ψ (Φ z) 1) (fderiv ℝ Ψ (Φ z) 1) +
        Q (fderiv ℝ Ψ (Φ z) Complex.I) (fderiv ℝ Ψ (Φ z) Complex.I)) / 2 =
    (a * Q e e + a⁻¹ * Q (Complex.I * e) (Complex.I * e)) / 2
  rw [hdet]
  exact radial_inverse_quadratic_energy Q _ (Circle.norm_coe _) hBr hBt

end DifferentialGeometry.Geometry

end
