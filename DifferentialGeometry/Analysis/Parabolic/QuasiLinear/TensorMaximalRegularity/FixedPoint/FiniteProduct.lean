import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.TimeDependentForcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem exists_vector_fixed_forcing_of_tame
    (hT : 0 < T) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (N : ℝ → {u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) |
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} →
        PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hPR : Real.sqrt (1 + T) * ρ ≤ R)
    (hzero : ∀ᵐ t ∂(timeMeasure T), ‖N t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR⟩‖ ≤ D)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ u v,
      ‖N t u - N t v‖ ≤ (A : ℝ) * R * ‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) - (v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))‖ +
        (B : ℝ) * ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) ((u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) - (v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))))‖ +
        (C : ℝ) * (‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))‖ + ‖(v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))‖) *
          ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a + 1 ≤ a + 2 by linarith)) ((u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) - (v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))))‖)
    (hmeas : TimeNemyMeas
      (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
        {u | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} by
          simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) N T)
    (hκ : (A : ℝ) * R * (1 + T) + (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) < 1)
    (hstay : Real.sqrt T * D ≤ (1 - ((A : ℝ) * R * (1 + T) +
      (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T))) * ρ) :
    ∃ F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T,
      ‖F‖ ≤ ρ ∧
      (∀ᵐ t ∂(timeMeasure T),
        ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith))
          (maximalRegularityDuhamelVectorField hT 0 F t)‖ ≤ R) ∧
      F =ᵐ[timeMeasure T] fun t => N t (aeSetLift
        (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
          {u | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} by
          simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR)
        (maximalRegularityDuhamelVectorField hT 0 F) t) := by
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a + 1 ≤ a + 2 by linarith))
  let L := maximalRegularityVectorFieldL (I := I) (M := M) (g := g)
    (r := r) (s := s) (ι := ι) a hT.le
  have hL (F) : ‖L F‖ ≤ (1 + T) * ‖F‖ := by
    exact (L.le_opNorm F).trans (mul_le_mul_of_nonneg_right
      (maximalRegularityVectorFieldL_norm_le hT) (norm_nonneg F))
  have hp (F) : ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤ Real.sqrt (1 + T) * ‖F‖ := by
    dsimp only [L]
    rw [maximalRegularityVectorFieldL_eq_duhamel hT F]
    exact maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le hT F
  obtain ⟨F, hF, hstate, hforce⟩ := exists_fixed_forcing_of_tame hR hρ
    (show 0 ≤ 1 + T by linarith) (Real.sqrt_nonneg _) J L hL hp hPR
      N A B C D hD hzero htame (fun f hf => hmeas le_rfl f hf) hκ hstay
  refine ⟨F, hF, ?_, ?_⟩
  · dsimp only [L] at hstate
    rw [maximalRegularityVectorFieldL_eq_duhamel hT F] at hstate
    exact hstate
  · dsimp only [L] at hforce
    rw [maximalRegularityVectorFieldL_eq_duhamel hT F] at hforce
    exact hforce

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
