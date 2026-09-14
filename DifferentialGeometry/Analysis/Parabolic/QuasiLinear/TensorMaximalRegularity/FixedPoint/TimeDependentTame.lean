import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.TimeDependentForcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearResponse
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeDependent
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.TameForcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.State.TensorSobolevLower

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem field_mem_lowerRS
    (g₀ : SmoothRiemannianMetric I M) (r s a : ℕ) {T ρ R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (hρR : 2 * ρ ≤ R)
    (F : timeL2 (TensorHs (I := I) (M := M) g₀ r s (a : ℝ)) T)
    (hF : ‖F‖ ≤ ρ) :
    ∀ᵐ t ∂(timeMeasure T),
      maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) F t ∈
        lowerStateRS (I := I) (M := M) g₀ r s a R := by
  let field := maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT
    (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) F
  have hincl :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) field)
        =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) field
  have hpoint := maximalRegularityDuhamelSolutionField_inclusion_Ha1_ae_pointwise_le
    (I := I) (M := M) (g₀ := g₀) hT F
  have hsqrt : Real.sqrt (1 + T) ≤ 2 := by
    have hsq : Real.sqrt (1 + T) ≤ 1 + T := by
      calc
        Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
        _ = 1 + T := Real.sqrt_sq (by linarith)
    linarith
  filter_upwards [hincl, hpoint] with t htincl ht
  change ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field t)‖ ≤ R
  calc
    ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (field t)‖ =
        ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) field) t‖ := by rw [htincl]
    _ ≤ Real.sqrt (1 + T) * ‖F‖ := ht
    _ ≤ 2 * ρ := mul_le_mul hsqrt hF (norm_nonneg F) (by positivity)
    _ ≤ R := hρR

private theorem time_partial_tame_at
    (g₀ : SmoothRiemannianMetric I M) (r s a : ℕ)
    {R τ T : ℝ} (hR : 0 < R) (hT : 0 < T) (hT1 : T ≤ 1)
    (hTτ : T ≤ τ)
    (Nfun : ℝ → lowerStateRS (I := I) (M := M) g₀ r s a R →
      TensorHs (I := I) (M := M) g₀ r s (a : ℝ))
    (hNmeas : TimeNemyMeas
      (zero_mem_lowerRS (I := I) (M := M) g₀ r s a hR.le) Nfun τ)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hTlo : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2))
    (hTstay : T ≤ ((R / 4) / (2 * (D + 1))) ^ 2)
    (hzero : ∀ t ∈ Icc (0 : ℝ) τ,
      ‖Nfun t ⟨0, zero_mem_lowerRS (I := I) (M := M) g₀ r s a hR.le⟩‖ ≤ D)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16)
    (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    (hsingle : ∀ t ∈ Icc (0 : ℝ) τ,
      ∀ u u' : lowerStateRS (I := I) (M := M) g₀ r s a R,
      ‖Nfun t u - Nfun t u'‖ ≤
        (A : ℝ) * R *
            ‖(u : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2))‖ +
                ‖(u' : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) (g := g₀)
        (r := r) (s := s) (a : ℝ) T)
      (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ r s (a : ℝ)) T),
      let field := maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT
        (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) gforce
      u = maximalRegularityDuhamelMap (I := I) (M := M) (a : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) gforce ∧
        (∀ᵐ t ∂(timeMeasure T),
          field t ∈ lowerStateRS (I := I) (M := M) g₀ r s a R) ∧
        gforce =ᵐ[timeMeasure T]
          (fun t => Nfun t (aeSetLift
            (zero_mem_lowerRS (I := I) (M := M) g₀ r s a hR.le) field t)) ∧
        timeH1.trace0 _ T u = 0 ∧
        timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) (a : ℝ) field + gforce ∧
        ‖gforce‖ ≤ R / 4 := by
  classical
  let X := TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)
  let Y := TensorHs (I := I) (M := M) g₀ r s (a : ℝ)
  let J := tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
  let L := maximalRegularitySolutionFieldL (I := I) (M := M) (g := g₀) (r := r) (s := s)
    (a : ℝ) hT.le
  have hL (F : timeL2 Y T) : ‖L F‖ ≤ (1 + T) * ‖F‖ := by
    exact (L.le_opNorm F).trans (mul_le_mul_of_nonneg_right
      (maximalRegularitySolutionFieldL_norm_le hT.le) (norm_nonneg F))
  have hpoint (F : timeL2 Y T) : ∀ᵐ t ∂(timeMeasure T), ‖J (L F t)‖ ≤
      Real.sqrt (1 + T) * ‖F‖ := by
    have hp := maximalRegularityDuhamelSolutionField_inclusion_Ha1_ae_pointwise_le hT F
    have heq := J.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT (0 : X) F)
    filter_upwards [hp, heq] with t ht he
    change ‖J (maximalRegularitySolutionFieldL (a : ℝ) hT.le F t)‖ ≤ _
    rw [maximalRegularitySolutionFieldL_eq_duhamel hT F]
    exact he ▸ ht
  have hsqrt : Real.sqrt (1 + T) ≤ 2 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  let ρ := R / 4
  let κ := (A : ℝ) * R * (1 + T) + (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
    2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T)
  have hκle : κ ≤ 1 / 2 := by
    have ha : (A : ℝ) * R * (1 + T) ≤ 1 / 8 := by
      nlinarith [mul_le_mul_of_nonneg_left (show 1 + T ≤ 2 by linarith)
        (mul_nonneg A.coe_nonneg hR.le)]
    have hst : Real.sqrt T ≤ 1 / (8 * ((B : ℝ) + 1)) := by
      rw [show 1 / (8 * ((B : ℝ) + 1)) = Real.sqrt ((1 / (8 * ((B : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      convert hTlo using 1
      rw [div_pow, one_pow, mul_pow]
      norm_num
    have hb : (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) ≤ 1 / 4 := by
      have hb' : (B : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
        calc
          _ ≤ (B : ℝ) * (2 * (1 / (8 * ((B : ℝ) + 1)))) := by gcongr
          _ ≤ 1 / 4 := by
            have hfrac : (B : ℝ) / ((B : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [B.coe_nonneg]
            have he : (B : ℝ) * (2 * (1 / (8 * ((B : ℝ) + 1)))) =
              ((B : ℝ) / ((B : ℝ) + 1)) * (1 / 4) := by field_simp; ring
            rw [he]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg B.coe_nonneg (Real.sqrt_nonneg T))]
    have hc : 2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) ≤ 1 / 8 := by
      calc
        _ ≤ 2 * (C : ℝ) * ρ * 2 * 2 := by
          dsimp only [ρ]
          gcongr
          linarith
        _ = 2 * ((C : ℝ) * R) := by dsimp only [ρ]; ring
        _ ≤ 1 / 8 := by linarith
    dsimp only [κ]
    linarith
  have hstay : Real.sqrt T * D ≤ (1 - κ) * ρ := by
    have hst : Real.sqrt T ≤ ρ / (2 * (D + 1)) := by
      rw [show ρ / (2 * (D + 1)) = Real.sqrt ((ρ / (2 * (D + 1))) ^ 2) from
        (Real.sqrt_sq (by dsimp only [ρ]; positivity)).symm]
      exact Real.sqrt_le_sqrt hTstay
    have hD1 : 0 < D + 1 := by linarith
    calc
      _ ≤ (ρ / (2 * (D + 1))) * D := mul_le_mul_of_nonneg_right hst hD
      _ ≤ (ρ / (2 * (D + 1))) * (D + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        dsimp only [ρ]
        positivity
      _ = ρ / 2 := by field_simp
      _ ≤ (1 - κ) * ρ := by dsimp only [ρ]; nlinarith [hR]
  have htime : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) τ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨ht.1, ht.2.trans hTτ⟩
  obtain ⟨F, hF, hstate, hforce⟩ := exists_fixed_forcing_of_tame hR.le
    (show 0 ≤ ρ by dsimp only [ρ]; positivity) (show 0 ≤ 1 + T by linarith)
    (Real.sqrt_nonneg (1 + T)) J L hL hpoint
    (show Real.sqrt (1 + T) * ρ ≤ R by dsimp only [ρ]; nlinarith [hR])
    Nfun A B C D hD
    (by filter_upwards [htime] with t ht; exact hzero t ht)
    (by filter_upwards [htime] with t ht; exact hsingle t ht)
    (fun f hf => hNmeas hTτ f hf) (show κ < 1 by linarith) hstay
  refine ⟨maximalRegularityDuhamelMap (I := I) (M := M) (a : ℝ) hT (0 : X) F, F, rfl, ?_, ?_, ?_, ?_, hF⟩
  · change ∀ᵐ t ∂(timeMeasure T), L F t ∈ lowerStateRS (I := I) (M := M) g₀ r s a R at hstate
    dsimp only [L] at hstate
    rw [maximalRegularitySolutionFieldL_eq_duhamel hT F] at hstate
    exact hstate
  · dsimp only [L] at hforce
    rw [maximalRegularitySolutionFieldL_eq_duhamel hT F] at hforce
    exact hforce
  · rw [maximalRegularityDuhamelMap_trace0, map_zero]
  · exact maximalRegularityDuhamelMap_timeDeriv_eq hT
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ r s) (0 : X) F

theorem time_partial_tame
    (g₀ : SmoothRiemannianMetric I M) (r s a : ℕ)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    (Nfun : ℝ → lowerStateRS (I := I) (M := M) g₀ r s a R →
      TensorHs (I := I) (M := M) g₀ r s (a : ℝ))
    (hNmeas : TimeNemyMeas
      (zero_mem_lowerRS (I := I) (M := M) g₀ r s a hR.le) Nfun τ)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ∀ t ∈ Icc (0 : ℝ) τ,
      ‖Nfun t ⟨0, zero_mem_lowerRS (I := I) (M := M) g₀ r s a hR.le⟩‖ ≤ D)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16)
    (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    (hsingle : ∀ t ∈ Icc (0 : ℝ) τ,
      ∀ u u' : lowerStateRS (I := I) (M := M) g₀ r s a R,
      ‖Nfun t u - Nfun t u'‖ ≤
        (A : ℝ) * R *
            ‖(u : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2))‖ +
                ‖(u' : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∃ T₀ : ℝ,
      T₀ = min τ (min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
        ((((R / 4) / (2 * (D + 1))) ^ 2)))) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀),
      ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) (g := g₀)
          (r := r) (s := s) (a : ℝ) T)
        (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ r s (a : ℝ)) T),
        let field := maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) gforce
        u = maximalRegularityDuhamelMap (I := I) (M := M) (a : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ lowerStateRS (I := I) (M := M) g₀ r s a R) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun t (aeSetLift
              (zero_mem_lowerRS (I := I) (M := M) g₀ r s a hR.le) field t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (a : ℝ) field + gforce ∧
          ‖gforce‖ ≤ R / 4 := by
  set T₀ : ℝ := min τ (min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
    (((R / 4) / (2 * (D + 1))) ^ 2))) with hT₀def
  have hD1 : 0 < D + 1 := by linarith
  have hT₀ : 0 < T₀ := by
    rw [hT₀def]
    refine lt_min hτ (lt_min one_pos (lt_min (by positivity) ?_))
    positivity
  refine ⟨T₀, hT₀def, hT₀, ?_⟩
  intro T hT hTT₀
  have hTτ : T ≤ τ := le_trans hTT₀ (hT₀def ▸ min_le_left _ _)
  have hTbase : T ≤ min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
      (((R / 4) / (2 * (D + 1))) ^ 2)) :=
    le_trans hTT₀ (hT₀def ▸ min_le_right _ _)
  have hT1 : T ≤ 1 := le_trans hTbase (min_le_left _ _)
  have hTlo : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2) :=
    le_trans hTbase (le_trans (min_le_right _ _) (min_le_left _ _))
  have hTstay : T ≤ ((R / 4) / (2 * (D + 1))) ^ 2 :=
    le_trans hTbase (le_trans (min_le_right _ _) (min_le_right _ _))
  exact time_partial_tame_at (I := I) (M := M) g₀ r s a hR hT hT1 hTτ
    Nfun hNmeas A B C D hD hTlo hTstay hzero hsmallA hsmallC hsingle

end DifferentialGeometry.Analysis.Parabolic

end
