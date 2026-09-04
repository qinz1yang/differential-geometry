import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Galerkin.ForcingSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Solution.Pointwise

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_galerkin_projected_forcing_sequence_background (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (solution : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 solution fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      Tendsto fseq atTop (𝓝 fLo) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius K.top K.slope K.outer K.realize)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
                K.threshold_lt K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hlo.metric_realization)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                    K.outer_pos K.realize_pos).le)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) t)) ∧
          timeH1.trace0 _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) = 0 ∧
          timeH1.timeDeriv _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) + fseq N ∧
          ‖fseq N‖ ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize / 4 := by
  set R : ℝ := lowRegularityStateRadius K.top K.slope K.outer K.realize with hRdef
  have hRpos : 0 < R := lowRegularityStateRadius_pos
    K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos
  have hQnn : 0 ≤ lowRegularityOuterRadius K.top K.outer K.realize :=
    (lowRegularityOuterRadius_pos K.top_nonneg K.outer_pos K.realize_pos).le
  set Nfun := boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
    K.threshold_lt K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hlo.metric_realization
    with hNfundef
  set A : ℝ≥0 := Real.toNNReal (K.top * lowRegularityOuterRadius K.top K.outer K.realize / R) with hAdef
  set B : ℝ≥0 := Real.toNNReal K.base with hBdef
  set C : ℝ≥0 := Real.toNNReal K.slope with hCdef
  have hAarg : 0 ≤ K.top * lowRegularityOuterRadius K.top K.outer K.realize / R :=
    div_nonneg (mul_nonneg K.top_nonneg hQnn) hRpos.le
  have hAcoe : (A : ℝ) = K.top * lowRegularityOuterRadius K.top K.outer K.realize / R :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = K.base := Real.coe_toNNReal _ K.base_nonneg
  have hCcoe : (C : ℝ) = K.slope := Real.coe_toNNReal _ K.slope_nonneg
  have hAR : (A : ℝ) * R = K.top * lowRegularityOuterRadius K.top K.outer K.realize := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hRpos.ne'
  have hsmallA : (A : ℝ) * R ≤ 1 / 16 := by
    rw [hAR]; exact lowRegularityOuterRadius_small K.top_nonneg
  have hsmallC : (C : ℝ) * R ≤ 1 / 16 := by
    rw [hCcoe, hRdef]; exact lowRegularityStateRadius_small K.slope_nonneg
  have hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ 1 R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) -
              (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(u' : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (u' : _))‖ := by
    intro u u'
    rw [hAR, hBcoe, hCcoe]
    exact hlo.remainder_lipschitz u u'
  have hDnn : 0 ≤ K.zeroBd := le_trans (norm_nonneg _) hlo.remainder_zero_bound
  have hTB : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2) := by
    rw [hBcoe]
    exact le_trans hlo.time_le_horizon (le_trans (min_le_right _ _) (min_le_left _ _))
  have hex : ∀ N : ℕ,
      ∃ gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T,
        (timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N gforce =
            gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce t ∈ lowerState (I := I) (M := M) g₀ 1 R) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  gforce) t)) ∧
          timeH1.trace0 _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce) = 0 ∧
          timeH1.timeDeriv _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  gforce) + gforce ∧
          ‖gforce‖ ≤ R / 4) ∧
        ‖gforce - fLo‖ ≤
          2 * ‖timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N fLo -
            fLo‖ := by
    intro N
    obtain ⟨T₀, hT₀eq, _hT₀pos, hsol⟩ :=
      exists_tame_projected_partial_solution
        (I := I) (M := M) g₀ 1 hRpos N Nfun hlo.remainder_continuous A B C K.zeroBd
        hDnn hlo.remainder_zero_bound hsmallA hsmallC hsingle
    have hTT₀ : T ≤ T₀ := by
      rw [hT₀eq, hBcoe]
      exact hlo.time_le_horizon
    obtain ⟨u, gforce, hu, hstate, hgE, htr, hpde, hgball⟩ :=
      hsol hT hTT₀
    subst hu
    refine ⟨gforce, ⟨?_, hstate, hgE, htr, hpde, hgball⟩, ?_⟩
    · exact projForce_fixed (I := I) (M := M) g₀ 1 N gforce
        (fun t => aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce) t)
        hgE
    · exact projFixTame_le_two (I := I) (M := M) g₀ 1 hRpos N hlo.remainder_continuous hsingle
        hsmallA hsmallC hT hT1 hTB fLo gforce hlo.forcing_norm_le_quarter_radius hgball hlo.forcing_ae_eq_remainder hgE
  choose fseq hpack hK using hex
  exact ⟨fseq, projFix_tendsto (I := I) (M := M) g₀ (K := 2) fLo fseq hK, hpack⟩

theorem exists_galerkin_projected_forcing_sequence_with_mode_convergence_background (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (solution : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 solution fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      Tendsto fseq atTop (𝓝 fLo) ∧
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) (fseq N) i) u) t) atTop
          (𝓝 (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius K.top K.slope K.outer K.realize)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
                K.threshold_lt K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hlo.metric_realization)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                    K.outer_pos K.realize_pos).le)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) t)) ∧
          timeH1.trace0 _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) = 0 ∧
          timeH1.timeDeriv _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) + fseq N ∧
          ‖fseq N‖ ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize / 4 := by
  obtain ⟨fseq, hconv, hpack⟩ :=
    exists_galerkin_projected_forcing_sequence_background (I := I) (M := M) g₀ g_bg K hT hT1 solution fLo hlo
  refine ⟨fseq, hconv, fun i t ht => ?_, hpack⟩
  have hmode : Tendsto (fun N => timeModeCoeff (I := I) (M := M) (fseq N) i)
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) fLo i)) := by
    have hcl := ((tensorHsCoeffL (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (a := ((1 : ℕ) : ℝ)) i).compLpL 2 (timeMeasure T)).continuous.tendsto fLo
    exact Tendsto.congr' (Filter.Eventually.of_forall fun _ => rfl) (hcl.comp hconv)
  exact tendsto_perModeConvolution_of_tendsto_timeL2
    (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hmode ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
