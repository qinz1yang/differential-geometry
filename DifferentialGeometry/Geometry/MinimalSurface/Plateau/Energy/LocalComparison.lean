import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Retraction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusEnergy
import DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusComparison

noncomputable section

open Manifold Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem disk_energy_inf_le_pullback_integral_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} {τ : C(loopCircle, loopCircle)} (hτ : IsWeaklyMonotoneOnce τ)
    {z : ℂ → F} {L : ℝ≥0} (hz : LipschitzWith L z)
    (hzΦ : MapsTo z (Metric.closedBall (0 : ℂ) 1) (range Φ))
    (htrace : ∀ θ, z (diskBoundary θ) = Φ (γ (τ θ))) :
    sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) ≤
      ∫ x in Metric.closedBall (0 : ℂ) 1,
        (pullbackMetricCoefficients g r (z x) (fderiv ℝ z x 1) (fderiv ℝ z x 1) +
          pullbackMetricCoefficients g r (z x)
            (fderiv ℝ z x Complex.I) (fderiv ℝ z x Complex.I)) / 2 := by
  obtain ⟨C, hC⟩ := exists_riemannian_lipschitz_disk_of_lipschitz_retraction
    g hΦ hU hr hΦU hleft
  obtain ⟨u, _, _, huLip, hut, _, _, hue⟩ := hC z L hz hzΦ γ τ htrace
  have hu : u ∈ weaklyMonotoneDiskCompetitors g γ :=
    ⟨⟨τ, hτ, hut⟩, C * L, huLip⟩
  have hbound : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g v
  have hle := csInf_le hbound (mem_image_of_mem (fun v : C(closedDisk, M) =>
    riemannianDiskEnergy g v) hu)
  exact hle.trans_eq hue

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem pullback_energy_closedBall_le_of_attachThinAnnulus
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} {τ : C(loopCircle, loopCircle)} (hτ : IsWeaklyMonotoneOnce τ)
    (u v : ℂ → F) (T : F → F) {L Lw : ℝ≥0} {R h : ℝ}
    (hh : 0 < h) (hhR : h < R) (hR1 : R ≤ 1)
    (hu : LipschitzWith L u) (huΦ : MapsTo u (Metric.closedBall (0 : ℂ) 1) (range Φ))
    (htrace : ∀ θ, u (diskBoundary θ) = Φ (γ (τ θ)))
    (hw : LipschitzWith Lw (attachThinAnnulus u v T R h))
    (hwΦ : MapsTo (attachThinAnnulus u v T R h) (Metric.closedBall (0 : ℂ) 1) (range Φ)) :
    let A := pullbackMetricCoefficients g r
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    (∫ z in Metric.closedBall (0 : ℂ) R, e u z) ≤
      (∫ z in Metric.closedBall (0 : ℂ) R, e v z) +
        (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall (0 : ℂ) (R - h),
          e (attachThinAnnulus u v T R h) z) +
        ((∫ z in Metric.closedBall (0 : ℂ) 1, e u z) -
          sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  let A := pullbackMetricCoefficients g r
  let e : (ℂ → F) → ℂ → ℝ := fun f z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  let w := attachThinAnnulus u v T R h
  have hwtrace (θ : loopCircle) : w (diskBoundary θ) = Φ (γ (τ θ)) := by
    rw [show w (diskBoundary θ) = u (diskBoundary θ) from
      attachThinAnnulus_outer u v T hh (by
        change R ≤ ‖(AddCircle.toCircle θ : ℂ)‖
        rw [Circle.norm_coe]
        exact hR1)]
    exact htrace θ
  have hInf := disk_energy_inf_le_pullback_integral_of_lipschitz g hΦ hU hr
    hΦU hleft hτ hw hwΦ hwtrace
  obtain ⟨C, hC⟩ := exists_riemannian_lipschitz_disk_of_lipschitz_retraction
    g hΦ hU hr hΦU hleft
  obtain ⟨_, _, _, _, _, _, hue, _⟩ := hC u L hu huΦ γ τ htrace
  obtain ⟨_, _, _, _, _, _, hwe, _⟩ := hC w Lw hw hwΦ γ τ hwtrace
  have hsplit := DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_closedBall
    A u v T hh hhR hR1 hwe
  have hsplitu := setIntegral_sdiff measurableSet_closedBall hue
    (Metric.closedBall_subset_closedBall hR1)
  change (∫ z in Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) R, e u z) =
    (∫ z in Metric.closedBall (0 : ℂ) 1, e u z) -
      ∫ z in Metric.closedBall (0 : ℂ) R, e u z at hsplitu
  change sInf _ ≤ ∫ z in Metric.closedBall (0 : ℂ) 1, e w z at hInf
  change (∫ z in Metric.closedBall (0 : ℂ) 1, e w z) =
    (∫ z in Metric.closedBall (0 : ℂ) R, e v z) +
      (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall (0 : ℂ) (R - h), e w z) +
        ∫ z in Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall (0 : ℂ) R, e u z at hsplit
  change (∫ z in Metric.closedBall (0 : ℂ) R, e u z) ≤
    (∫ z in Metric.closedBall (0 : ℂ) R, e v z) +
      (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall (0 : ℂ) (R - h), e w z) +
        ((∫ z in Metric.closedBall (0 : ℂ) 1, e u z) - _)
  linarith

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_pullback_energy_comparison_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (τ : ℕ → C(loopCircle, loopCircle))
    (hτ : ∀ n, IsWeaklyMonotoneOnce (τ n))
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) 1) (range Φ))
    (hvK : ∀ n, MapsTo (v n) (Metric.closedBall (0 : ℂ) b) (range Φ))
    (htrace : ∀ n θ, u n (diskBoundary θ) = Φ (γ (τ n θ)))
    (hgap : Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc a b},
      ‖u n z - v n z‖ ^ 2) atTop (𝓝 0))
    {B : ℝ} (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc a b},
      ‖fderiv ℝ (u n) z‖ ^ 2 + ‖fderiv ℝ (v n) z‖ ^ 2) ≤ B)
    {V : Set F} (hV : IsOpen V) (hKV : range Φ ⊆ V)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    (hTK : MapsTo T V (range Φ)) (hfix : ∀ y ∈ range Φ, T y = y)
    (hmin : Tendsto (fun n => ∫ z in Metric.closedBall (0 : ℂ) 1,
      (pullbackMetricCoefficients g r (u n z)
          (fderiv ℝ (u n) z 1) (fderiv ℝ (u n) z 1) +
        pullbackMetricCoefficients g r (u n z)
          (fderiv ℝ (u n) z Complex.I) (fderiv ℝ (u n) z Complex.I)) / 2) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ)))) :
    let A := pullbackMetricCoefficients g r
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    let infimum := sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
    ∃ (ρ h : ℕ → ℝ), (∀ n, ρ n ∈ Icc a b) ∧ (∀ n, 0 < h n) ∧
      Tendsto h atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, h n < ρ n / 2 ∧
        (∃ C : ℝ≥0, LipschitzWith C (attachThinAnnulus (u n) (v n) T (ρ n) (h n))) ∧
        MapsTo (attachThinAnnulus (u n) (v n) T (ρ n) (h n))
          (Metric.closedBall (0 : ℂ) 1) (range Φ)) ∧
      (∀ n z, ρ n ≤ ‖z‖ → attachThinAnnulus (u n) (v n) T (ρ n) (h n) z = u n z) ∧
      let ε : ℕ → ℝ := fun n =>
        (∫ z in Metric.closedBall (0 : ℂ) (ρ n) \ Metric.closedBall (0 : ℂ) (ρ n - h n),
          e (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z) +
            ((∫ z in Metric.closedBall (0 : ℂ) 1, e (u n) z) - infimum)
      Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, (∫ z in Metric.closedBall (0 : ℂ) (ρ n), e (u n) z) ≤
          (∫ z in Metric.closedBall (0 : ℂ) (ρ n), e (v n) z) + ε n := by
  let A := pullbackMetricCoefficients g r
  let e : (ℂ → F) → ℂ → ℝ := fun f z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  have hA : ContinuousOn A (range Φ) :=
    (contDiffOn_pullback_metric_coefficients g hU hr).continuousOn.mono hΦU
  obtain ⟨ρ, h, hρ, hh, hh0, hgood, houter, _, _, hshell⟩ :=
    DifferentialGeometry.Analysis.exists_target_valued_attachThinAnnulus_tendsto_quadratic_annulus_energy_zero
      u v Ku Kv hu hv ha hab hb1 hgap henergy (isCompact_range hΦ) hV hKV
      huK hvK T hT hL hTK hfix A hA
  refine ⟨ρ, h, hρ, hh, hh0, hgood, houter, ?_, ?_⟩
  · simpa only [A, sub_self, add_zero] using hshell.add (hmin.sub_const
      (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ)))
  · filter_upwards [hgood] with n hn
    obtain ⟨C, hC⟩ := hn.2.1
    have hhρ : h n < ρ n := by linarith [hn.1, hh n]
    have hle := pullback_energy_closedBall_le_of_attachThinAnnulus g hΦ hU
      (hr.of_le (by simp)) hΦU hleft (hτ n) (u n) (v n) T (hh n) hhρ
      ((hρ n).2.trans hb1) (hu n) (huK n) (htrace n) hC hn.2.2
    dsimp only [A, e] at hle ⊢
    linarith

end DifferentialGeometry.Geometry

end
