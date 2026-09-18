import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.ParameterDependence
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
variable {Ptype : Type*} [PseudoMetricSpace Ptype]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem exists_lipschitz_vector_fixed_forcing_of_tame
    (hT : 0 < T) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (N : Ptype → ℝ → {u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) |
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} →
        PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hPR : Real.sqrt (1 + T) * ρ ≤ R)
    (hzero : ∀ p, ∀ᵐ t ∂(timeMeasure T), ‖N p t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR⟩‖ ≤ D)
    (htame : ∀ p, ∀ᵐ t ∂(timeMeasure T), ∀ u v,
      ‖N p t u - N p t v‖ ≤ (A : ℝ) * R * ‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) - (v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))‖ +
        (B : ℝ) * ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) ((u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) - (v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))))‖ +
        (C : ℝ) * (‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))‖ + ‖(v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))‖) *
          ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a + 1 ≤ a + 2 by linarith)) ((u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) - (v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))))‖)
    (hmeas : ∀ p (f : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) T)
      (_ : ∀ᵐ t ∂(timeMeasure T), ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) (f t)‖ ≤ R),
      AEStronglyMeasurable (fun t => N p t (aeSetLift
        (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
          {u | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} by
            simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) f t)) (timeMeasure T))
    (hκ : (A : ℝ) * R * (1 + T) + (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) < 1)
    (hstay : Real.sqrt T * D ≤ (1 - ((A : ℝ) * R * (1 + T) +
      (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T))) * ρ)
    (K₀ K₁ : ℝ≥0)
    (hparam : ∀ p q, ∀ᵐ t ∂(timeMeasure T), ∀ u,
      ‖N p t u - N q t u‖ ≤
        ((K₁ : ℝ) * ‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))‖ + (K₀ : ℝ)) * dist p q) :
    let κ := (A : ℝ) * R * (1 + T) + (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T)
    ∃ F : Ptype → timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T,
      LipschitzWith ((K₁ * (1 + T).toNNReal * ρ.toNNReal + (Real.sqrt T).toNNReal * K₀) /
        (1 - κ).toNNReal) F ∧
      ∀ p, ‖F p‖ ≤ ρ ∧
      (∀ᵐ t ∂(timeMeasure T),
        ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith))
          (maximalRegularityDuhamelVectorField hT 0 (F p) t)‖ ≤ R) ∧
      F p =ᵐ[timeMeasure T] fun t => N p t (aeSetLift
        (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
          {u | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} by
          simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR)
        (maximalRegularityDuhamelVectorField hT 0 (F p)) t) := by
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
  obtain ⟨F, hLip, hF⟩ := exists_lipschitz_fixed_forcing_of_tame hR hρ
    (show 0 ≤ 1 + T by linarith) (Real.sqrt_nonneg _) J L hL hp hPR
      N A B C D hD hzero htame hmeas hκ hstay K₀ K₁ hparam
  refine ⟨F, hLip, ?_⟩
  intro p
  obtain ⟨hbound, hstate, hforce⟩ := hF p
  refine ⟨hbound, ?_, ?_⟩
  · dsimp only [L] at hstate
    rw [maximalRegularityVectorFieldL_eq_duhamel hT (F p)] at hstate
    exact hstate
  · dsimp only [L] at hforce
    rw [maximalRegularityVectorFieldL_eq_duhamel hT (F p)] at hforce
    exact hforce

theorem exists_lipschitz_time_partial_tame_vector
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    (Nfun : Ptype → ℝ → {u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)) |
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (I := I) (M := M) (g := g₀) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} →
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s a))
    (hNmeas : ∀ p, TimeNemyMeas
      (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) ∈
        {u | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g₀) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) u‖ ≤ R} by
          simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) (Nfun p) τ)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ∀ p, ∀ t ∈ Icc (0 : ℝ) τ,
      ‖Nfun p t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le⟩‖ ≤ D)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16)
    (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    (hsingle : ∀ p, ∀ t ∈ Icc (0 : ℝ) τ,
      ∀ u u',
      ‖Nfun p t u - Nfun p t u'‖ ≤
        (A : ℝ) * R * ‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) - (u' : _)‖ +
        (B : ℝ) * ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (I := I) (M := M) (g := g₀) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)) ((u : _) - (u' : _))‖ +
        (C : ℝ) * (‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)))‖ + ‖(u' : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)))‖) *
          ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (I := I) (M := M) (g := g₀) (r := r) (s := s)
              (show a + 1 ≤ a + 2 by linarith)) ((u : _) - (u' : _))‖)
    (K₀ K₁ : ℝ≥0)
    (hparam : ∀ p q, ∀ t ∈ Icc (0 : ℝ) τ, ∀ u,
      ‖Nfun p t u - Nfun q t u‖ ≤
        ((K₁ : ℝ) * ‖(u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)))‖ + (K₀ : ℝ)) * dist p q) :
    ∃ T₀ : ℝ,
      T₀ = min τ (min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
        ((((R / 4) / (2 * (D + 1))) ^ 2)))) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      let κ := (A : ℝ) * R * (1 + T) + (B : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
        2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T)
      ∃ (u : Ptype → timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s a)) T)
        (gforce : Ptype → timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s a)) T),
        LipschitzWith
          ((K₁ * (1 + T).toNNReal * (R / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal) gforce ∧
        LipschitzWith
          (2 * ((K₁ * (1 + T).toNNReal * (R / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal)) u ∧
        ∀ p,
        let field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) (gforce p)
        u p = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) (gforce p) ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ {v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2)) |
              ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
                (I := I) (M := M) (g := g₀) (r := r) (s := s)
                (show a + 1 ≤ a + 2 by linarith)) v‖ ≤ R}) ∧
          gforce p =ᵐ[timeMeasure T]
            (fun t => Nfun p t (aeSetLift
              (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) ∈
                {v | ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
                  (I := I) (M := M) (g := g₀) (r := r) (s := s)
                    (show a + 1 ≤ a + 2 by linarith)) v‖ ≤ R} by
                  simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) field t)) ∧
          (u p).toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := I) (M := M) (g := g₀) (r := r) (s := s)
                (show a ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T) field ∧
          timeH1.trace0 _ T (u p) = 0 ∧
          timeH1.timeDeriv _ T (u p) =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := I) (M := M) (g := g₀) (r := r) (s := s) a)).compLpL
                2 (timeMeasure T) field + gforce p ∧
          ‖gforce p‖ ≤ R / 4 := by
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
  obtain ⟨F, hLip, hF⟩ := exists_lipschitz_vector_fixed_forcing_of_tame hT hR.le
    (show 0 ≤ R / 4 by positivity) Nfun A B C D hD hPR
    (fun p => by filter_upwards [htime] with t ht; exact hzero p t ht)
    (fun p => by filter_upwards [htime] with t ht; exact hsingle p t ht)
    (fun p f hf => hNmeas p hTτ f hf) (by linarith) hstay K₀ K₁
    (fun p q => by filter_upwards [htime] with t ht; exact hparam p q t ht)
  refine ⟨fun p => maximalRegularityDuhamelVectorMap hT
      (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) (F p),
    F, hLip, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    have hmap := maximalRegularityDuhamelVectorMap_dist_le hT
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g₀ r s)
      (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g₀ r s (a + 2))) (F p) (F q)
    exact hmap.trans (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc] using
      mul_le_mul_of_nonneg_left (hLip.dist_le_mul p q) (by norm_num : (0 : ℝ) ≤ 2))
  intro p
  obtain ⟨hbound, hstate, hforce⟩ := hF p
  refine ⟨rfl, hstate, hforce, ?_, ?_, ?_, hbound⟩
  · exact (maximalRegularityDuhamelVectorField_toFunL2 hT
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g₀ r s) _ (F p)).symm
  · rw [maximalRegularityDuhamelVectorMap_trace0, map_zero]
  · exact maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g₀ r s) _ (F p)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
