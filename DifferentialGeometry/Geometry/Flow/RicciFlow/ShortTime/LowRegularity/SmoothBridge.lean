import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.DenseSolution
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
      norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S)‖ := by
      rw [tensorHsInclusion_smoothCcToTensorHs]
    _ ≤ R := hS

theorem deTurckRemainderOnLowerState_on_smoothCore
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (x : smoothCore (I := I) (M := M) g₀ R) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal x.1 =
      deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal x := by
  simpa only [deTurckRemainderOnLowerState] using
    (smoothCore_dense (I := I) (M := M) g₀ hR).extend_eq hcore x

theorem deTurckRemainderOnLowerState_on_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
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
  have hx := deTurckRemainderOnLowerState_on_smoothCore (I := I) (M := M) g₀ g_bg hR hδ hreal hcore x
  unfold deTurckRemainderOnSmoothCore at hx
  simpa only [u, x, hrep] using hx

theorem exists_zero_state_deTurck_remainder_spectral_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal)) :
    ∃ Cseed : ℕ → ℝ, (∀ n, 0 ≤ Cseed n) ∧
      ∀ (n : ℕ) (F : Finset
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2)),
        ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            ((deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
              ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i) ^ 2 ≤
          Cseed n ^ 2 := by
  classical
  have hzero_embed :
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) =
        smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (0 : SmoothCcTensor g₀ 0 2) := by
    refine TensorHs.ext ?_
    funext i
    rw [TensorHs.zero_coeff, smoothCcToTensorHs_coeff,
      show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _,
      tensorL2Coeff_eq_inner, inner_zero_right]
  have hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2))‖ ≤ R := by
    rw [← hzero_embed]
    simpa only [map_zero, norm_zero] using hR.le
  have hsub : (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) =
      ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2), hS⟩ := Subtype.ext hzero_embed
  have hN := deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore
    (0 : SmoothCcTensor g₀ 0 2) hS
  refine ⟨fun n => ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
      (deTurckSmoothRemainder (I := I) g₀ g_bg
        (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
          (0 : SmoothCcTensor g₀ 0 2) hS)))‖,
    fun n => norm_nonneg _, ?_⟩
  intro n F
  have hcoeff : ∀ i, (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i =
      (ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS)))).coeff i := by
    intro i
    rw [hsub, hN, deTurckSmoothN_coeff, ccTensorToHs_coeff]
  have hbridge : ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS))) =
      smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS))) :=
    TensorHs.ext (funext (fun _ => rfl))
  calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
        ((deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i) ^ 2
      = ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          ((ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
            (deTurckSmoothRemainder (I := I) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
              (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
                (0 : SmoothCcTensor g₀ 0 2) hS)))).coeff i) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => by rw [hcoeff i])
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg
            (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
              (0 : SmoothCcTensor g₀ 0 2) hS)))‖ ^ 2 :=
        cc_partial_le_norm (I := I) (M := M) g₀ 2 (n : ℝ) _ F
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg
            (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
              (0 : SmoothCcTensor g₀ 0 2) hS)))‖ ^ 2 := by rw [hbridge]

theorem deTurck_remainder_forcing_eq_smooth_remainder_ae
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂(timeMeasure T),
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
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
    deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore (F t) (hball t)

end DifferentialGeometry.PDE.RicciFlow

end
