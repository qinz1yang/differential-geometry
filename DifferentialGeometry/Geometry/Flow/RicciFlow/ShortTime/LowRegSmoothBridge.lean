import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDenseSolve
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

theorem symm_h2_of_state
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
      (ccTensor02Symm (I := I) (M := M) g₀ S)‖ ≤ R := by
  calc
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
        (ccTensor02Symm (I := I) (M := M) g₀ S)‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ :=
      norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S)‖ := by
      rw [tensorHsInclusion_smoothCcToTensorHs]
    _ ≤ R := hS

theorem lowRegN_on_core
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (x : smoothCore (I := I) (M := M) g₀ R) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal x.1 =
      coreN (I := I) (M := M) g₀ g_bg hδ hreal x := by
  simpa only [lowRegN] using
    (smoothCore_dense (I := I) (M := M) g₀ hR).extend_eq hcore x

theorem lowRegN_on_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S, hS⟩ =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg 1
        (ccTensor02Symm (I := I) (M := M) g₀ S) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hS)) := by
  let u : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2) S, hS⟩
  let x : smoothCore (I := I) (M := M) g₀ R := ⟨u, ⟨S, rfl⟩⟩
  have hrep : coreRep g₀ x = S := by
    apply smoothHs_inj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
    rw [coreRep_spec]
  have hx := lowRegN_on_core (I := I) (M := M) g₀ g_bg hR hδ hreal hcore x
  unfold coreN at hx
  simpa only [u, x, hrep] using hx

theorem lowReg_force_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂(timeMeasure T),
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t)))
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (hpin : ∀ᵐ t ∂(timeMeasure T),
      smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) (F t) = field t)
    (hball : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R) :
    gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg 1
        (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))) := by
  filter_upwards [hforce, hstate, hpin] with t htforce htstate htpin
  let uF : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2) (F t), hball t⟩
  have hlift : aeSetLift
      (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t = uF := by
    apply Subtype.ext
    simp only [aeSetLift, dif_pos htstate, uF]
    exact htpin.symm
  rw [htforce, hlift]
  simpa only [uF] using
    lowRegN_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore (F t) (hball t)

end DifferentialGeometry.PDE.RicciFlow

end
