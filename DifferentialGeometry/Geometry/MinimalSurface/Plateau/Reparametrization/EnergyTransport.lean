import DifferentialGeometry.Geometry.Measure.Area.Regularization
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.RegularizedMetric
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Measure.Area.ChangeOfFrame
import Mathlib.MeasureTheory.Function.Jacobian
import DifferentialGeometry.Geometry.Coordinates.Isothermal.Disk

section

noncomputable section

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem energy_comp_le_regularized_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Q : ℂ → M}
    (Ω : TopologicalSpace.Opens ℂ) (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (heq : ∀ (x : Ω) (v w : ℂ), h.inner x v w =
      pullbackMetricCoefficients g Q x.1 v w + δ * inner ℝ v w)
    {φ : ℂ → ℂ} {z : ℂ} (hz : φ z ∈ Ω)
    (hQ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (φ z))
    (hφ : DifferentiableAt ℝ φ z)
    (hc : ∃ c : ℝ, ∀ v : ℂ,
      h.inner ⟨φ z, hz⟩ (fderiv ℝ φ z v) (fderiv ℝ φ z v) = c * Complex.normSq v) :
    diskMapEnergyDensity g (Q ∘ φ) z ≤
      |(fderiv ℝ φ z).toLinearMap.det| * regularizedPullbackAreaDensity g Q δ (φ z) := by
  obtain ⟨c, hc⟩ := hc
  let x : Ω := ⟨φ z, hz⟩
  let A := fderiv ℝ φ z
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := h.inner x
  have h1 := hc 1
  rw [Complex.normSq_one, mul_one] at h1
  change B (A 1) (A 1) = c at h1
  have hI := hc Complex.I
  rw [Complex.normSq_I, mul_one] at hI
  change B (A Complex.I) (A Complex.I) = c at hI
  have horth : B (A 1) (A Complex.I) = 0 := by
    have hsum := hc (1 + Complex.I)
    change B (A (1 + Complex.I)) (A (1 + Complex.I)) = _ at hsum
    simp only [map_add, _root_.add_apply] at hsum
    have hs : B (A Complex.I) (A 1) = B (A 1) (A Complex.I) := h.symm x _ _
    rw [hs, h1, hI] at hsum
    norm_num [Complex.normSq_apply] at hsum
    linarith
  have harea : c = |A.toLinearMap.det| * regularizedPullbackAreaDensity g Q δ (φ z) := by
    have hj := tangentTwoJacobian_of_conformal h horth (h1.trans hI.symm)
    have hf := tangentTwoJacobian_comp_complex h (x := x) (ContinuousLinearMap.id ℝ ℂ) A
    change tangentTwoJacobian h (A 1) (A Complex.I) =
      |A.toLinearMap.det| * tangentTwoJacobian h (1 : ℂ) Complex.I at hf
    rw [hj] at hf
    change B (A 1) (A 1) = _ at hf
    rw [h1] at hf
    rw [regularizedPullbackAreaDensity_eq_sqrt_metric_gram g Ω h δ heq x]
    exact hf
  have hbound (v : ℂ) : pullbackMetricCoefficients g Q (φ z) (A v) (A v) ≤
      h.inner x (A v) (A v) := by
    rw [heq]
    exact le_add_of_nonneg_right (mul_nonneg hδ (real_inner_self_nonneg))
  have hchain : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Q ∘ φ) z =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (φ z)).comp A := by
    rw [mfderiv_comp z hQ hφ.mdifferentiableAt, mfderiv_eq_fderiv]
    rfl
  have henergy : diskMapEnergyDensity g (Q ∘ φ) z =
      (pullbackMetricCoefficients g Q (φ z) (A 1) (A 1) +
        pullbackMetricCoefficients g Q (φ z) (A Complex.I) (A Complex.I)) / 2 := by
    simp only [diskMapEnergyDensity, diskMapPartial, hchain,
      pullbackMetricCoefficients_apply, Function.comp_apply]
    rfl
  rw [henergy, ← harea]
  have hb1 := hbound 1
  have hbI := hbound Complex.I
  change _ ≤ B (A 1) (A 1) at hb1
  change _ ≤ B (A Complex.I) (A Complex.I) at hbI
  rw [h1] at hb1
  rw [hI] at hbI
  linarith

theorem integral_diskMapEnergyDensity_comp_le_regularizedPullbackAreaDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Q : ℂ → M}
    (Ω : TopologicalSpace.Opens ℂ) (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω)
    (hD : Metric.closedBall (0 : ℂ) 1 ⊆ Ω)
    (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 Q Ω)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (heq : ∀ (x : Ω) (v w : ℂ), h.inner x v w =
      pullbackMetricCoefficients g Q x.1 v w + δ * inner ℝ v w)
    {φ : ℂ → ℂ} (hφ : ContDiffOn ℝ 1 φ (Metric.ball 0 1))
    (hbij : BijOn φ (Metric.ball 0 1) (Metric.ball 0 1))
    (hc : ∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1), ∃ c : ℝ, ∀ v : ℂ,
      h.inner ⟨φ z, hD (Metric.ball_subset_closedBall (hbij.mapsTo hz))⟩
        (fderiv ℝ φ z v) (fderiv ℝ φ z v) = c * Complex.normSq v) :
    IntegrableOn (diskMapEnergyDensity g (Q ∘ φ)) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (Q ∘ φ) z) ≤
        ∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z := by
  let D : Set ℂ := Metric.ball 0 1
  let K : Set ℂ := Metric.closedBall 0 1
  let J := regularizedPullbackAreaDensity g Q δ
  let e := diskMapEnergyDensity g (Q ∘ φ)
  have hφD (z : ℂ) (hz : z ∈ D) : DifferentiableAt ℝ φ z :=
    ((hφ z hz).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt one_ne_zero
  have hmaps : MapsTo φ D Ω := fun z hz => hD (Metric.ball_subset_closedBall (hbij.mapsTo hz))
  have hQD (z : ℂ) (hz : z ∈ D) : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (φ z) :=
    ((hQ (φ z) (hmaps hz)).contMDiffAt (Ω.isOpen.mem_nhds (hmaps hz))).mdifferentiableAt
      one_ne_zero
  have hpoint (z : ℂ) (hz : z ∈ D) :
      e z ≤ |(fderiv ℝ φ z).toLinearMap.det| * J (φ z) :=
    energy_comp_le_regularized_area g Ω h hδ heq (hmaps hz) (hQD z hz) (hφD z hz) (hc z hz)
  have hJ : IntegrableOn J K :=
    ((continuousOn_regularizedPullbackAreaDensity g Ω.isOpen hQ δ).mono hD).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)
  have hJimage : IntegrableOn J (φ '' D) := by
    rw [hbij.image_eq]
    exact hJ.mono_set Metric.ball_subset_closedBall
  have hJac : ∀ z ∈ D, HasFDerivWithinAt φ (fderiv ℝ φ z) D z :=
    fun z hz => (hφD z hz).hasFDerivAt.hasFDerivWithinAt
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    Metric.isOpen_ball.measurableSet hJac hbij.injOn J).mp hJimage
  have hcQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (Q ∘ φ) D :=
    hQ.comp (contMDiffOn_iff_contDiffOn.mpr hφ) hmaps
  have hcB := continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g
    Metric.isOpen_ball hcQ
  have hecont : ContinuousOn e D :=
    ((((hcB.clm_apply continuousOn_const).clm_apply continuousOn_const).add
      ((hcB.clm_apply continuousOn_const).clm_apply continuousOn_const)).div_const 2)
  have henonneg (z : ℂ) : 0 ≤ e z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g ((Q ∘ φ) z) _)
      (metric_inner_self_nonneg g ((Q ∘ φ) z) _)) (by norm_num)
  have heint : IntegrableOn e D := by
    apply Integrable.mono' hi (hecont.aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    rw [Real.norm_of_nonneg (henonneg z)]
    exact hpoint z hz
  have hmeasure : volume.restrict D = volume.restrict K := by
    apply Measure.restrict_congr_set
    have ha := (ae_restrict_iff' measurableSet_closedBall).mp ae_disk_interior
    filter_upwards [ha] with z hz
    exact propext ⟨fun hz => Metric.ball_subset_closedBall hz, hz⟩
  have hbound : (∫ z in D, e z) ≤ ∫ z in D, |(fderiv ℝ φ z).toLinearMap.det| • J (φ z) :=
    integral_mono_ae heint hi (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      exact hpoint z hz)
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume
    Metric.isOpen_ball.measurableSet hJac hbij.injOn J
  rw [hbij.image_eq] at hchange
  rw [← hchange] at hbound
  change (∫ z in D, e z) ≤ ∫ z in D, J z at hbound
  exact ⟨by simpa only [IntegrableOn, hmeasure] using heint,
    by simpa only [hmeasure] using hbound⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_normalized_disk_coordinate_energy_le_regularized_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (Q : ℂ → M) (Ω : TopologicalSpace.Opens ℂ)
    (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω) {δ : ℝ} (hδ : 0 < δ)
    (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 Q Ω)
    (hinner : ∀ (x : Ω) (ξ ζ : ℂ), h.inner x ξ ζ =
      pullbackMetricCoefficients g Q x.1 ξ ζ + δ * inner ℝ ξ ζ)
    {r : ℝ} (hr : 1 < r) (hD : Metric.closedBall (0 : ℂ) 1 ⊆ Ω)
    {W : ℂ → ℂ} (hW : ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r))
    (hi : InjOn W (Metric.ball (0 : ℂ) r))
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) r, (fderiv ℝ W z).toLinearMap.det ≠ 0)
    (hBel : ∀ z ∈ Metric.ball (0 : ℂ) r, complexAntilinearPart (fderiv ℝ W z) =
      pullbackBeltramiCoefficient g Q δ z * complexLinearPart (fderiv ℝ W z)) :
    ∃ (e f ψ : OpenPartialHomeomorph ℂ ℂ),
      e.source = Metric.ball (0 : ℂ) r ∧ e.target = W '' Metric.ball (0 : ℂ) r ∧
      (e : ℂ → ℂ) = W ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      f.source = W '' Metric.ball (0 : ℂ) 1 ∧ f.target = Metric.ball (0 : ℂ) 1 ∧
      DifferentiableOn ℂ f f.source ∧ DifferentiableOn ℂ f.symm f.target ∧
      (∀ z ∈ f.source, deriv f z ≠ 0) ∧
      ψ.source = Metric.ball (0 : ℂ) 1 ∧ ψ.target = Metric.ball (0 : ℂ) 1 ∧
      ψ 0 = 0 ∧ ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ z, ψ z = f (W z)) ∧ (∀ z, ψ.symm z = e.symm (f.symm z)) ∧
      IntegrableOn (diskMapEnergyDensity g (Q ∘ ψ.symm)) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (Q ∘ ψ.symm) z) ≤
        ∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z := by
  obtain ⟨e, f, ψ, hes, het, heW, he, hei, hfs, hft, hf, hfi, hfd,
    hψs, hψt, hψ0, hψ, hψi, hψeq, hψieq, hψΩ, hconf⟩ :=
    exists_normalized_conformal_inverse_regularized_metric g Q Ω h hδ hinner hr hD hW hi hd hBel
  have hφ : ContDiffOn ℝ 1 ψ.symm (Metric.ball (0 : ℂ) 1) :=
    hψt ▸ hψi.of_le (by norm_cast)
  have hbij : BijOn ψ.symm (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    simpa only [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target, hψt, hψs]
      using ψ.symm.bijOn
  have hc : ∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1), ∃ c : ℝ, ∀ ξ : ℂ,
      h.inner ⟨ψ.symm z, hD (Metric.ball_subset_closedBall (hbij.mapsTo hz))⟩
        (fderiv ℝ ψ.symm z ξ) (fderiv ℝ ψ.symm z ξ) = c * Complex.normSq ξ := by
    intro z hz
    obtain ⟨c, _, hce⟩ := hconf z (hψt.symm ▸ hz)
    exact ⟨c, hce⟩
  obtain ⟨hInt, hEn⟩ := integral_diskMapEnergyDensity_comp_le_regularizedPullbackAreaDensity
    g Ω h hD hQ hδ.le hinner hφ hbij hc
  exact ⟨e, f, ψ, hes, het, heW, he, hei, hfs, hft, hf, hfi, hfd,
    hψs, hψt, hψ0, hψ, hψi, hψeq, hψieq, hInt, hEn⟩

end DifferentialGeometry.Geometry

end

end
