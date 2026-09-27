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

theorem time_partial_tame_vector
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    (Nfun : ℝ → {u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)) |
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (I := I) (M := M) (g := g₀) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} →
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s a))
    (hNmeas : TimeNemyMeas
      (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) ∈
        {u | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g₀) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} by
          simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) Nfun τ)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ∀ t ∈ Icc (0 : ℝ) τ,
      ‖Nfun t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le⟩‖ ≤ D)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16)
    (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    (hsingle : ∀ t ∈ Icc (0 : ℝ) τ,
      ∀ u u',
      ‖Nfun t u - Nfun t u'‖ ≤
        (A : ℝ) * R * ‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) - (u' : _)‖ +
        (B : ℝ) * ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g₀) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) ((u : _) - (u' : _))‖ +
        (C : ℝ) * (‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)))‖ + ‖(u' : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)))‖) *
          ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g₀) (r := r) (s := s)
              (show a + 1 ≤ a + 2 by linarith)) ((u : _) - (u' : _))‖) :
    ∃ T₀ : ℝ,
      T₀ = min τ (min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
        ((((R / 4) / (2 * (D + 1))) ^ 2)))) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s a)) T)
        (gforce : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s a)) T),
        let field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) gforce
        u = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ {v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)) |
              ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
                (I := I) (M := M) (g := g₀) (r := r) (s := s)
                (show a + 1 ≤ a + 2 by linarith)) v‖ ≤ R}) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun t (aeSetLift
              (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) ∈
                {v | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
                  (I := I) (M := M) (g := g₀) (r := r) (s := s)
                    (show a + 1 ≤ a + 2 by linarith)) v‖ ≤ R} by
                  simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) field t)) ∧
          u.toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := I) (M := M) (g := g₀) (r := r) (s := s)
                (show a ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := I) (M := M) (g := g₀) (r := r) (s := s) a)).compLpL
                2 (timeMeasure T) field + gforce ∧
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
  obtain ⟨hPR, hκ, hstay⟩ := tame_forcing_contraction_bounds hR.le hT1
    A B C hD hTlo hTstay hsmallA hsmallC
  have htime : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) τ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨ht.1, ht.2.trans hTτ⟩
  obtain ⟨F, hF, hstate, hforce⟩ := exists_vector_fixed_forcing_of_tame hT hR.le
    (show 0 ≤ R / 4 by positivity) Nfun A B C D hD hPR
    (by filter_upwards [htime] with t ht; exact hzero t ht)
    (by filter_upwards [htime] with t ht; exact hsingle t ht)
    (fun {T'} hTT f hf => hNmeas (hTT.trans hTτ) f hf) (by linarith) hstay
  refine ⟨maximalRegularityDuhamelVectorMap hT
      (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) F,
    F, rfl, hstate, hforce, ?_, ?_, ?_, hF⟩
  · exact (maximalRegularityDuhamelVectorField_toFunL2 hT
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g₀ r s) _ F).symm
  · rw [maximalRegularityDuhamelVectorMap_trace0, map_zero]
  · exact maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g₀ r s) _ F

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

section
open MeasureTheory Filter
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

theorem strongPair_eq_of_tame_vector
    (hT : 0 < T) {R : ℝ} (hR : 0 ≤ R)
    {S : Set (PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))}
    (hzero : (0 : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) ∈ S)
    (N : ℝ → S → PiLp 2 (fun _ : ι => TensorHs g r s a))
    (A B C : ℝ≥0)
    (htame : ∀ᵐ t ∂(timeMeasure T), ∀ v w : S,
      ‖N t v - N t w‖ ≤
        (A : ℝ) * R * ‖(v : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) - w‖ +
          (B : ℝ) * ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
              ((v : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) - w)‖ +
          (C : ℝ) * (‖(v : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))‖ +
            ‖(w : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))‖) *
            ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
                ((v : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) - w)‖)
    (force₁ force₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (u₁ u₂ : timeH1 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (field₁ field₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) T)
    (htrace : timeH1.trace0 _ T u₁ = timeH1.trace0 _ T u₂)
    (hlink₁ : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
          2 (timeMeasure T) field₁ = u₁.toFunL2)
    (hlink₂ : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
          2 (timeMeasure T) field₂ = u₂.toFunL2)
    (heq₁ : timeH1.timeDeriv _ T u₁ =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := r) (s := s) a)).compLpL 2 (timeMeasure T) field₁ + force₁)
    (heq₂ : timeH1.timeDeriv _ T u₂ =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := r) (s := s) a)).compLpL 2 (timeMeasure T) field₂ + force₂)
    (hstate₁ : ∀ᵐ t ∂(timeMeasure T), field₁ t ∈ S)
    (hstate₂ : ∀ᵐ t ∂(timeMeasure T), field₂ t ∈ S)
    (hforce₁ : force₁ =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero field₁ t))
    (hforce₂ : force₂ =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero field₂ t))
    (hsmall : (A : ℝ) * R * (1 + T) +
      (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
        (C : ℝ) * Real.sqrt (1 + T) * (‖field₁‖ + ‖field₂‖) < 1) :
    force₁ = force₂ ∧ field₁ = field₂ ∧ u₁ = u₂ := by
  let hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := I) (M := M) g r s
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  let L := maximalRegularityVectorFieldL (ι := ι) (g := g) (r := r) (s := s) a hT.le
  have hL (F) : ‖L F‖ ≤ (1 + T) * ‖F‖ :=
    (L.le_opNorm F).trans (mul_le_mul_of_nonneg_right
      (maximalRegularityVectorFieldL_norm_le hT) (norm_nonneg F))
  have hp (F) : ∀ᵐ t ∂(timeMeasure T),
      ‖J (L F t)‖ ≤ Real.sqrt (1 + T) * ‖F‖ := by
    dsimp only [L]
    rw [maximalRegularityVectorFieldL_eq_duhamel hT F]
    exact maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le hT F
  have htrace0 : timeH1.trace0 _ T (u₁ - u₂) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))
          (0 : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) := by
    rw [map_sub, htrace, sub_self, map_zero]
  have hlink : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
        2 (timeMeasure T) (field₁ - field₂) = (u₁ - u₂).toFunL2 := by
    change _ = timeH1.toTimeL2 _ T (u₁ - u₂)
    rw [map_sub, map_sub, hlink₁, hlink₂]
    rfl
  have heq : timeH1.timeDeriv _ T (u₁ - u₂) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := r) (s := s) a)).compLpL 2 (timeMeasure T)
          (field₁ - field₂) + (force₁ - force₂) := by
    rw [map_sub, heq₁, heq₂, map_sub]
    abel
  obtain ⟨hfield, _⟩ := strongPair_eq_duhamel_vector hT hc 0
    (force₁ - force₂) (u₁ - u₂) (field₁ - field₂) htrace0 hlink heq
  have hresponse : field₁ - field₂ = L (force₁ - force₂) :=
    hfield.trans (maximalRegularityVectorFieldL_eq_duhamel hT (force₁ - force₂)).symm
  have hforce : force₁ = force₂ := forcing_eq_of_tame hzero hR
    (Real.sqrt_nonneg _) J L hL hp N A B C htame force₁ force₂ field₁ field₂
      hresponse hstate₁ hstate₂ hforce₁ hforce₂ hsmall
  have hfields : field₁ = field₂ := by
    apply sub_eq_zero.mp
    rw [hresponse, hforce, sub_self, map_zero]
  have hu : u₁ = u₂ := by
    apply timeH1.ext
    · exact htrace
    · change timeH1.timeDeriv _ T u₁ = timeH1.timeDeriv _ T u₂
      rw [heq₁, heq₂, hfields, hforce]
  exact ⟨hforce, hfields, hu⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
