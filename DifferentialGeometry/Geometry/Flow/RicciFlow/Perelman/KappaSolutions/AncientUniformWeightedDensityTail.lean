import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientWeightedDensityTail
import DifferentialGeometry.Analysis.Integration.Measure.Estimates.GaussianTail

noncomputable section

open Filter Set MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance uniformWeightedTailTopology
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    TopologicalSpace F.M := F.topology
private local instance uniformWeightedTailCharted
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    ChartedSpace H F.M := F.charted
private local instance uniformWeightedTailSmooth
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    IsManifold I ∞ F.M := F.smooth
private local instance uniformWeightedTailT2
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : T2Space F.M := F.t2
private local instance uniformWeightedTailSigma
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    SigmaCompactSpace F.M := F.sigmaCompact
private local instance uniformWeightedTailMeasurable
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    MeasurableSpace F.M := borel F.M
private local instance uniformWeightedTailBorel
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    BorelSpace F.M := ⟨rfl⟩

theorem exists_uniform_ancient_sqrt_redLength_mul_redDensity_tail_bound
    {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
      ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (p q : F.M) {tau : ℝ}, tau ∈ Icc a b → redLength F.S 0 p q tau ≤ B →
      (∫⁻ x in {x : F.M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal},
        ENNReal.ofReal (Real.sqrt (redLength F.S 0 p x tau) * redDensity F.S 0 p x tau)
          ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) < ε := by
  let c : ℝ := 1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp ((1 + B) / 2)) *
    ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹))
  have hC : C ≠ (⊤ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (measure_ne_top volume.toSphere univ) ENNReal.ofReal_ne_top)
  have hlim : Tendsto (fun N => C * gaussianTail (Module.finrank ℝ E) ((c / b) / 2) N)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (tendsto_gaussianTail (Module.finrank ℝ E)
        (div_pos (div_pos hc hb) (by norm_num : (0 : ℝ) < 2))) (Or.inr hC)
  obtain ⟨N, hN⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  refine ⟨N, ?_⟩
  intro F kappa hF p q tau htau hq
  have htau0 : 0 < tau := lt_of_lt_of_le ha htau.1
  have hpref :
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp ((1 + B) / 2)) ≤
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp ((1 + B) / 2)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    apply sub_le_sub_right
    exact mul_le_mul_of_nonpos_left (Real.log_le_log ha htau.1)
      (neg_nonpos.mpr (by positivity))
  have htail : gaussianTail (Module.finrank ℝ E) ((c / tau) / 2) N ≤
      gaussianTail (Module.finrank ℝ E) ((c / b) / 2) N :=
    antitone_gaussianTail_decay _ _ (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left hc.le htau0 htau.2) (by norm_num : (0 : ℝ) ≤ 2))
  apply lt_of_le_of_lt
    (ancient_sqrt_redLength_mul_redDensity_tail_le_of_redLength_le F hF p q htau0 hq N)
  apply lt_of_le_of_lt _ hN
  dsimp only [C, c] at *
  simpa only [mul_assoc] using mul_le_mul' hpref (mul_le_mul_right htail
    ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)))

theorem exists_uniform_ancient_sqrt_redLength_mul_redDensity_integral_bound
    {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
        ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
        ∀ (p q : F.M) {tau : ℝ}, tau ∈ Icc a b →
          redLength F.S 0 p q tau ≤ B →
          (∫⁻ x : F.M,
            ENNReal.ofReal (Real.sqrt (redLength F.S 0 p x tau) * redDensity F.S 0 p x tau)
              ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) ≤ C := by
  let c : ℝ := 1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := ha.trans_le hab
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp ((1 + B) / 2)) *
    (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
      gaussianTail (Module.finrank ℝ E) ((c / b) / 2) 0)
  have hseries : gaussianTail (Module.finrank ℝ E) ((c / b) / 2) 0 < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    simpa only [gaussianTail, Nat.add_zero] using
      (summable_gaussianShell (Module.finrank ℝ E)
        (div_pos (div_pos hc hb) (by norm_num : (0 : ℝ) < 2))).tsum_ofReal_ne_top
  have hC : C < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (measure_lt_top volume.toSphere univ) ENNReal.ofReal_lt_top)
        hseries)
  refine ⟨C, hC, ?_⟩
  intro F kappa hF p q tau htau hq
  have htau0 : 0 < tau := ha.trans_le htau.1
  have hpref :
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        Real.exp ((1 + B) / 2)) ≤
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        Real.exp ((1 + B) / 2)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    apply sub_le_sub_right
    exact mul_le_mul_of_nonpos_left (Real.log_le_log ha htau.1)
      (neg_nonpos.mpr (by positivity))
  have htail : gaussianTail (Module.finrank ℝ E) ((c / tau) / 2) 0 ≤
      gaussianTail (Module.finrank ℝ E) ((c / b) / 2) 0 :=
    antitone_gaussianTail_decay _ _ (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left hc.le htau0 htau.2) (by norm_num : (0 : ℝ) ≤ 2))
  have hbound := ancient_sqrt_redLength_mul_redDensity_tail_le_of_redLength_le
    F hF p q htau0 hq 0
  simp only [Nat.cast_zero, ENNReal.toReal_nonneg, Set.ofPred_true,
    Measure.restrict_univ] at hbound
  apply hbound.trans
  dsimp only [C, c] at *
  exact mul_le_mul' hpref (mul_le_mul_right htail
    ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
