import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolutionFinite
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.FiniteProductL2
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.RecenteredTame
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.AffineMajorant
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.TimeDependentForcingL2

namespace Real

private theorem mul_add_sqrt_mul_le_of_le {K D eps eta T : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (heps : 0 ≤ eps)
    (heta : eta ≤ eps / (2 * (K + 1)))
    (hT : T ≤ (eps / (2 * (D + 1))) ^ 2) :
    K * eta + Real.sqrt T * D ≤ eps := by
  have hK1 : 0 < K + 1 := by linarith
  have hD1 : 0 < D + 1 := by linarith
  have hKratio : K / (K + 1) ≤ 1 := (div_le_iff₀ hK1).2 (by linarith)
  have hDratio : D / (D + 1) ≤ 1 := (div_le_iff₀ hD1).2 (by linarith)
  have hKeta : K * eta ≤ eps / 2 := by
    calc
      K * eta ≤ K * (eps / (2 * (K + 1))) := mul_le_mul_of_nonneg_left heta hK
      _ = (eps / 2) * (K / (K + 1)) := by field_simp
      _ ≤ (eps / 2) * 1 := mul_le_mul_of_nonneg_left hKratio (by positivity)
      _ = eps / 2 := mul_one _
  have hsqrt : Real.sqrt T ≤ eps / (2 * (D + 1)) :=
    Real.sqrt_le_iff.2 ⟨by positivity, hT⟩
  have hDsqrt : Real.sqrt T * D ≤ eps / 2 := by
    calc
      Real.sqrt T * D ≤ (eps / (2 * (D + 1))) * D := mul_le_mul_of_nonneg_right hsqrt hD
      _ = (eps / 2) * (D / (D + 1)) := by field_simp
      _ ≤ (eps / 2) * 1 := mul_le_mul_of_nonneg_left hDratio (by positivity)
      _ = eps / 2 := mul_one _
  linarith

private theorem mul_add_sqrt_mul_le_of_le_min {R Kb Db Kf Df eta T : ℝ}
    (hR : 0 ≤ R) (hKb : 0 ≤ Kb) (hDb : 0 ≤ Db) (hKf : 0 ≤ Kf) (hDf : 0 ≤ Df)
    (heta : eta ≤ min (1 / (16 * (Kb + 1))) (R / (16 * (Kf + 1))))
    (hT : T ≤ min 1 (min ((1 / (16 * (Db + 1))) ^ 2)
      ((R / (16 * (Df + 1))) ^ 2))) :
    Kb * eta + Real.sqrt T * Db ≤ 1 / 8 ∧
      Kf * eta + Real.sqrt T * Df ≤ R / 8 := by
  have threshold_eq (a b : ℝ) : (a / 8) / (2 * (b + 1)) = a / (16 * (b + 1)) := by
    rw [div_div]
    congr 1
    ring
  constructor
  · apply mul_add_sqrt_mul_le_of_le hKb hDb (by norm_num)
    · rw [threshold_eq]
      exact heta.trans (min_le_left _ _)
    · rw [threshold_eq]
      exact hT.trans ((min_le_right _ _).trans (min_le_left _ _))
  · apply mul_add_sqrt_mul_le_of_le hKf hDf (by positivity)
    · rw [threshold_eq]
      exact heta.trans (min_le_right _ _)
    · rw [threshold_eq]
      exact hT.trans ((min_le_right _ _).trans (min_le_right _ _))

end Real

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private abbrev VectorHs (g : SmoothRiemannianMetric I M) (ι : Type*) (r s : ℕ) (a : ℝ) :=
  PiLp 2 (fun _ : ι => TensorHs g r s a)

theorem exists_heatDuhamelVectorEvolution_of_tame_timeL2
    (hT : 0 < T) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (u₀ : VectorHs g ι r s (a + 1))
    (N : ℝ → VectorHs g ι r s (a + 2) → VectorHs g ι r s a)
    (A C : ℝ≥0) (B : timeL2 ℝ T) (F0 : timeL2 (VectorHs g ι r s a) T)
    (hPR : Real.sqrt (1 + T) * ρ ≤ R)
    (hκ : (A : ℝ) * R * (1 + T) + ‖B‖ * Real.sqrt (1 + T) +
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T) < 1)
    (hstay : ‖F0‖ ≤ (1 - ((A : ℝ) * R * (1 + T) + ‖B‖ * Real.sqrt (1 + T) +
      2 * (C : ℝ) * ρ * Real.sqrt (1 + T) * (1 + T))) * ρ)
    :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
      (g := g) (r := r) (s := s) a)
    let Q := fun t (v : {v : VectorHs g ι r s (a + 2) | ‖J v‖ ≤ R}) =>
      N t (heatVectorField a T u₀ t + v.val) - L (heatVectorField a T u₀ t + v.val)
    (∀ᵐ t ∂timeMeasure T, Q t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR⟩ = F0 t) →
    (∀ᵐ t ∂timeMeasure T, ∀ u v,
      ‖Q t u - Q t v‖ ≤ (A : ℝ) * R * ‖(u : VectorHs g ι r s (a + 2)) - v‖ +
        ‖B t‖ * ‖J ((u : VectorHs g ι r s (a + 2)) - v)‖ +
        (C : ℝ) * (‖(u : VectorHs g ι r s (a + 2))‖ + ‖(v : VectorHs g ι r s (a + 2))‖) *
          ‖J ((u : VectorHs g ι r s (a + 2)) - v)‖) →
    (TimeNemyMeas (show (0 : VectorHs g ι r s (a + 2)) ∈ {v | ‖J v‖ ≤ R} by
      simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR) Q T) →
    ∃ F : timeL2 (VectorHs g ι r s a) T, ‖F‖ ≤ ρ ∧
      (∀ᵐ t ∂timeMeasure T, ‖J (maximalRegularityDuhamelVectorField hT 0 F t)‖ ≤ R) ∧
      (timeH1.timeDeriv _ T (heatDuhamelVectorEvolution hT u₀ F) =ᵐ[timeMeasure T]
        fun t => N t (heatDuhamelVectorField hT u₀ F t)) ∧
      timeH1.trace0 _ T (heatDuhamelVectorEvolution hT u₀ F) =
        ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith)) u₀ ∧
      (heatDuhamelVectorEvolution hT u₀ F).toFunL2 =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
            2 (timeMeasure T) (heatDuhamelVectorField hT u₀ F) := by
  dsimp only
  intro hzero htame hmeas
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
    (g := g) (r := r) (s := s) a)
  let Q := fun t (v : {v : VectorHs g ι r s (a + 2) | ‖J v‖ ≤ R}) =>
    N t (heatVectorField a T u₀ t + v.val) - L (heatVectorField a T u₀ t + v.val)
  have hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := I) (M := M) g r s
  obtain ⟨F, hF, hstate, hforce⟩ := exists_vector_fixed_forcing_of_tame_timeL2
    hT hR hρ Q A C B F0 hPR hzero htame hmeas hκ hstay
  refine ⟨F, hF, hstate, ?_, heatDuhamelVectorEvolution_trace0 hT u₀ F,
    (heatDuhamelVectorField_toFunL2 hT hc u₀ F).symm⟩
  have heq := heatDuhamelVectorEvolution_timeDeriv hT hc u₀ F
  rw [heq]
  have hsum := Lp.coeFn_add (heatVectorField a T u₀)
    (maximalRegularityDuhamelVectorField hT 0 F)
  have hsplit := heatDuhamelVectorField_eq_add hT hc u₀ F
  have hL := L.coeFn_compLpL (p := 2) (μ := timeMeasure T) (heatDuhamelVectorField hT u₀ F)
  have hLF := Lp.coeFn_add (L.compLpL 2 (timeMeasure T) (heatDuhamelVectorField hT u₀ F)) F
  filter_upwards [hstate, hforce, hsum, hL, hLF] with t hs hf hst hLt hLFt
  have hv : heatDuhamelVectorField hT u₀ F t =
      heatVectorField a T u₀ t + maximalRegularityDuhamelVectorField hT 0 F t := by
    rw [hsplit, hst]
    rfl
  have hforce' : F t = N t (heatDuhamelVectorField hT u₀ F t) -
      L (heatDuhamelVectorField hT u₀ F t) := by
    rw [hf]
    simp only [aeSetLift, Set.mem_ofPred_eq, dite_eq_left hs]
    change N t (heatVectorField a T u₀ t + maximalRegularityDuhamelVectorField hT 0 F t) -
      L (heatVectorField a T u₀ t + maximalRegularityDuhamelVectorField hT 0 F t) = _
    rw [← hv]
  change ((L.compLpL 2 (timeMeasure T) (heatDuhamelVectorField hT u₀ F)) + F) t = _
  rw [hLFt, Pi.add_apply, hLt, hforce']
  abel
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem aestronglyMeasurable_of_continuous_time_cylinder
    {Z W : Type*} [PseudoMetricSpace Z] [TopologicalSpace W]
    {S : Set Z} (z₀ : S) {T τ : ℝ} (hτ : 0 ≤ τ) (hTτ : T ≤ τ)
    (alpha : ℝ → Z → W)
    (hα : Continuous (fun p : Icc (0 : ℝ) τ × S => alpha p.1 p.2))
    {z : ℝ → Z} (hz : AEStronglyMeasurable z (timeMeasure T))
    (hmem : ∀ᵐ t ∂timeMeasure T, z t ∈ S) :
    AEStronglyMeasurable (fun t => alpha t (z t)) (timeMeasure T) := by
  classical
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) τ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨ht.1, ht.2.trans hTτ⟩
  let ts : ℝ → Icc (0 : ℝ) τ := fun t =>
    if ht : t ∈ Icc (0 : ℝ) τ then ⟨t, ht⟩ else ⟨0, le_rfl, hτ⟩
  let zs : ℝ → S := fun t => if ht : z t ∈ S then ⟨z t, ht⟩ else z₀
  have hts : (fun t => (ts t : ℝ)) =ᵐ[timeMeasure T] fun t => t := by
    filter_upwards [htime] with t ht
    simp only [ts, dite_eq_left ht]
  have hzs : (fun t => (zs t : Z)) =ᵐ[timeMeasure T] z := by
    filter_upwards [hmem] with t ht
    simp only [zs, dite_eq_left ht]
  have htmeas : AEStronglyMeasurable ts (timeMeasure T) := by
    apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
    exact aestronglyMeasurable_id.congr hts.symm
  have hzmeas : AEStronglyMeasurable zs (timeMeasure T) := by
    apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
    exact hz.congr hzs.symm
  apply (hα.comp_aestronglyMeasurable (htmeas.prodMk hzmeas)).congr
  filter_upwards [hts, hzs] with t ht hz'
  simp only [ht, hz']

private theorem aestronglyMeasurable_recentered_of_continuous_time_cylinder
    {X Z W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace W]
    (J : X →L[ℝ] Z) (u₀ : Z) {R T τ : ℝ} (hR : 0 ≤ R) (hτ : 0 ≤ τ)
    (hTτ : T ≤ τ) (alpha : ℝ → Z → W)
    (hα : Continuous (fun p : Icc (0 : ℝ) τ × Metric.closedBall u₀ (2 * R) =>
      alpha p.1 p.2))
    (h : timeL2 X T) (hh : ∀ᵐ t ∂timeMeasure T, ‖J (h t) - u₀‖ ≤ R)
    {T' : ℝ} (hT' : T' ≤ T) (f : timeL2 X T')
    (hf : ∀ᵐ t ∂timeMeasure T', ‖J (f t)‖ ≤ R) :
    AEStronglyMeasurable (fun t => alpha t (J (h t + f t))) (timeMeasure T') := by
  have hμ : timeMeasure T' ≤ timeMeasure T :=
    Measure.restrict_mono (Icc_subset_Icc le_rfl hT') le_rfl
  have hh' := (Lp.aestronglyMeasurable h).mono_measure hμ
  have hz := J.continuous.comp_aestronglyMeasurable (hh'.add (Lp.aestronglyMeasurable f))
  have hmem : ∀ᵐ t ∂timeMeasure T', J (h t + f t) ∈ Metric.closedBall u₀ (2 * R) := by
    filter_upwards [ae_mono hμ hh, hf] with t ht hft
    rw [Metric.mem_closedBall, dist_eq_norm, map_add]
    calc
      ‖J (h t) + J (f t) - u₀‖ = ‖(J (h t) - u₀) + J (f t)‖ := by congr 1; abel
      _ ≤ ‖J (h t) - u₀‖ + ‖J (f t)‖ := norm_add_le _ _
      _ ≤ 2 * R := by linarith
  exact aestronglyMeasurable_of_continuous_time_cylinder
    ⟨u₀, Metric.mem_closedBall_self (by positivity)⟩ hτ (hT'.trans hTτ) alpha hα hz hmem

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ}

theorem exists_heatDuhamelVectorEvolution_of_recentered_coefficients
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (u₀ : VectorHs g ι r s (a + 1))
    (m : W →L[ℝ] VectorHs g ι r s a →L[ℝ] VectorHs g ι r s a)
    (Q : VectorHs g ι r s (a + 2) →L[ℝ] VectorHs g ι r s a)
    (D : VectorHs g ι r s (a + 1) →L[ℝ] VectorHs g ι r s a)
    (d : VectorHs g ι r s a →L[ℝ] VectorHs g ι r s a) (q : W)
    (alpha : ℝ → VectorHs g ι r s (a + 1) → W)
    (reaction : ℝ → VectorHs g ι r s (a + 1) → VectorHs g ι r s a)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (K L B C₀ : ℝ≥0)
    (ha : Continuous (fun p : Icc (0 : ℝ) τ × Metric.closedBall u₀ (2 * R) => alpha p.1 p.2))
    (hb : Continuous (fun p : Icc (0 : ℝ) τ × Metric.closedBall u₀ (2 * R) => reaction p.1 p.2))
    (halip : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z - u₀‖ ≤ 2 * R →
      ∀ w, ‖w - u₀‖ ≤ 2 * R → ‖alpha t z - alpha t w‖ ≤ (L : ℝ) * ‖z - w‖)
    (haclose : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z - u₀‖ ≤ 2 * R →
      ‖alpha t z - q‖ ≤ (K : ℝ) * R)
    (hblip : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z - u₀‖ ≤ 2 * R →
      ∀ w, ‖w - u₀‖ ≤ 2 * R → ‖reaction t z - reaction t w‖ ≤ (B : ℝ) * ‖z - w‖)
    (hbnd : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z - u₀‖ ≤ 2 * R → ‖reaction t z‖ ≤ C₀)
    (hsmallA : (‖m‖ * K * ‖Q‖) * R ≤ 1 / 16)
    (hsmallC : (‖m‖ * L * ‖Q‖) * R ≤ 1 / 16) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
    let Δ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
      (g := g) (r := r) (s := s) a)
    Δ = (m q).comp Q + d.comp (D.comp J) →
    ∃ T₀ ∈ Ioc (0 : ℝ) τ, ∀ (T : ℝ) (hT : T ∈ Ioc (0 : ℝ) T₀),
    ∃ F : timeL2 (VectorHs g ι r s a) T, ‖F‖ ≤ R / 4 ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖J (heatDuhamelVectorField hT.1 u₀ F t) - u₀‖ ≤ 2 * R) ∧
      (timeH1.timeDeriv _ T
        (heatDuhamelVectorEvolution hT.1 u₀ F) =ᵐ[timeMeasure T]
        fun t => m (alpha t (J (heatDuhamelVectorField
          hT.1 u₀ F t)))
            (Q (heatDuhamelVectorField hT.1 u₀ F t)) +
          reaction t (J (heatDuhamelVectorField hT.1 u₀ F t))) ∧
      timeH1.trace0 _ T (heatDuhamelVectorEvolution
        hT.1 u₀ F) =
        ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith)) u₀ ∧
      (heatDuhamelVectorEvolution hT.1 u₀ F).toFunL2 =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
            2 (timeMeasure T) (heatDuhamelVectorField
              hT.1 u₀ F) := by
  dsimp only
  intro hΔ
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  let Δ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
    (g := g) (r := r) (s := s) a)
  let N := fun t (x : VectorHs g ι r s (a + 2)) => m (alpha t (J x)) (Q x) + reaction t (J x)
  have hΔ' : Δ = (m q).comp Q + d.comp (D.comp J) := hΔ
  have heq (t : ℝ) (h v : VectorHs g ι r s (a + 2)) :
      N t (h + v) - Δ (h + v) = recenteredRemainder m Q J D d q alpha reaction h t v := by
    have hi : Δ (h + v) + recenteredRemainder m Q J D d q alpha reaction h t v = N t (h + v) := by
      rw [hΔ']
      simpa only [N, map_add] using
        recentered_remainder_operator_identity m Q J D d q alpha reaction h t v
    rw [← hi]
    abel
  let Aconst : ℝ≥0 := ‖m‖₊ * K * ‖Q‖₊
  let Cconst : ℝ≥0 := ‖m‖₊ * L * ‖Q‖₊
  let Kb : ℝ := ‖m‖ * L * ‖Q‖
  let Db : ℝ := B + ‖d‖ * ‖D‖
  let Kf : ℝ := ‖m‖ * K * R * ‖Q‖ + ‖d‖ * ‖D‖ * ‖J‖
  let Df : ℝ := C₀
  have hKb : 0 ≤ Kb := by dsimp only [Kb]; positivity
  have hDb : 0 ≤ Db := by dsimp only [Db]; positivity
  have hKf : 0 ≤ Kf := by dsimp only [Kf]; positivity
  have hDf : 0 ≤ Df := C₀.coe_nonneg
  let ε := min (1 / (16 * (Kb + 1))) (R / (16 * (Kf + 1)))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := I) (M := M) g r s
  obtain ⟨δ₁, hδ₁, hnear⟩ := heatVectorField_near_initial hc u₀ hτ hR
  obtain ⟨δ₂, hδ₂, hsmall⟩ := heatVectorField_norm_small_time hc u₀ hε hτ
  let T₀ := min δ₁ (min δ₂ (min 1 (min ((1 / (16 * (Db + 1))) ^ 2)
    ((R / (16 * (Df + 1))) ^ 2))))
  have hδ₁pos := hδ₁.1
  have hδ₂pos := hδ₂.1
  have hT₀ : 0 < T₀ := by dsimp only [T₀]; positivity
  refine ⟨T₀, ⟨hT₀, (min_le_left _ _).trans hδ₁.2⟩, ?_⟩
  intro T hT
  have hTδ₁ : T ≤ δ₁ := hT.2.trans (min_le_left _ _)
  have hTδ₂ : T ≤ δ₂ := hT.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTtime : T ≤ min 1 (min ((1 / (16 * (Db + 1))) ^ 2) ((R / (16 * (Df + 1))) ^ 2)) :=
    hT.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hTτ : T ≤ τ := hTδ₁.trans hδ₁.2
  have hT1 : T ≤ 1 := hTtime.trans (min_le_left _ _)
  let h := heatVectorField a T u₀
  have hhsmall : ‖h‖ ≤ ε := (hsmall T ⟨hT.1, hTδ₂⟩).le
  have hhnear : ∀ᵐ t ∂timeMeasure T, ‖J (h t) - u₀‖ < R := hnear T ⟨hT.1, hTδ₁⟩
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) τ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨ht.1, ht.2.trans hTτ⟩
  have hmem (x : VectorHs g ι r s (a + 2)) (hx : ‖J x - u₀‖ ≤ R)
      (v : VectorHs g ι r s (a + 1)) (hv : ‖v‖ ≤ R) : ‖J x + v - u₀‖ ≤ 2 * R := by
    have hle := (norm_add_le (J x - u₀) v).trans (add_le_add hx hv)
    simpa only [sub_add_eq_add_sub, two_mul] using hle
  let Bt := affineNormMajorant h Kb Db
  have hBae := affineNormMajorant_ae h Kb Db
  have hBnorm := affineNormMajorant_norm_le h hKb hDb
  have hhmem : ∀ᵐ t ∂timeMeasure T, J (h t) ∈ Metric.closedBall u₀ (2 * R) := by
    filter_upwards [hhnear] with t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith
  have haz := aestronglyMeasurable_of_continuous_time_cylinder
    ⟨u₀, Metric.mem_closedBall_self (by positivity)⟩ hτ.le hTτ alpha ha
    (J.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h)) hhmem
  have hbz := aestronglyMeasurable_of_continuous_time_cylinder
    ⟨u₀, Metric.mem_closedBall_self (by positivity)⟩ hτ.le hTτ reaction hb
    (J.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h)) hhmem
  have hFmeas : AEStronglyMeasurable (fun t => N t (h t) - Δ (h t)) (timeMeasure T) := by
    have hmul : Continuous (fun p : W × VectorHs g ι r s a => m p.1 p.2) :=
      (m.continuous.comp continuous_fst).clm_apply continuous_snd
    exact ((hmul.comp_aestronglyMeasurable
      (haz.prodMk (Q.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h)))).add hbz).sub
      (Δ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h))
  have hFbound : ∀ᵐ t ∂timeMeasure T, ‖N t (h t) - Δ (h t)‖ ≤ Kf * ‖h t‖ + Df := by
    filter_upwards [hhnear, htime] with t ht hτt
    have hclose : ‖alpha t (J (h t)) - q‖ ≤ (K : ℝ) * R :=
      haclose t hτt _ (by linarith)
    have hzero := recentered_remainder_zero_norm_le m Q J D d q alpha reaction (h t) t hclose
    have heq0 : N t (h t) - Δ (h t) = recenteredRemainder m Q J D d q alpha reaction (h t) t 0 := by
      simpa only [add_zero] using heq t (h t) 0
    rw [heq0]
    calc
      _ ≤ ‖m‖ * ((K : ℝ) * R) * ‖Q (h t)‖ + ‖reaction t (J (h t))‖ +
          ‖d‖ * ‖D‖ * ‖J (h t)‖ := hzero
      _ ≤ ‖m‖ * ((K : ℝ) * R) * (‖Q‖ * ‖h t‖) + (C₀ : ℝ) +
          ‖d‖ * ‖D‖ * (‖J‖ * ‖h t‖) := by
        gcongr
        · exact Q.le_opNorm _
        · exact hbnd t hτt _ (by linarith)
        · exact J.le_opNorm _
      _ = Kf * ‖h t‖ + Df := by dsimp only [Kf, Df]; ring
  let hFm := memLp_of_ae_norm_le_mul_norm_add_const h hFmeas hFbound
  let F0 := hFm.toLp (fun t => N t (h t) - Δ (h t))
  have hF0ae : F0 =ᵐ[timeMeasure T] (fun t => N t (h t) - Δ (h t)) := hFm.coeFn_toLp
  have hF0norm : ‖F0‖ ≤ Kf * ‖h‖ + Real.sqrt T * Df :=
    norm_toLp_le_of_ae_norm_le_mul_norm_add_const h hFmeas hKf hDf hFbound
  have hzero : ∀ᵐ t ∂timeMeasure T,
      N t (h t + 0) - Δ (h t + 0) = F0 t := by
    filter_upwards [hF0ae] with t ht
    simpa only [add_zero] using ht.symm
  have htame : ∀ᵐ t ∂timeMeasure T, ∀ u v : {v : VectorHs g ι r s (a + 2) | ‖J v‖ ≤ R},
      ‖(N t (h t + u.val) - Δ (h t + u.val)) - (N t (h t + v.val) - Δ (h t + v.val))‖ ≤
        (Aconst : ℝ) * R * ‖u.val - v.val‖ + ‖Bt t‖ * ‖J (u.val - v.val)‖ +
        (Cconst : ℝ) * (‖u.val‖ + ‖v.val‖) * ‖J (u.val - v.val)‖ := by
    filter_upwards [hhnear, htime, hBae] with t ht hτt hBt
    intro u v
    rw [heq, heq]
    have hraw := recentered_tame_estimate m Q J D d q alpha reaction (h t) t
      (fun z hz w hw => by
        simpa only [add_sub_add_left_eq_sub] using
          halip t hτt _ (hmem _ ht.le z hz) _ (hmem _ ht.le w hw))
      (fun z hz => haclose t hτt _ (hmem _ ht.le z hz))
      (fun z hz w hw => by
        simpa only [add_sub_add_left_eq_sub] using
          hblip t hτt _ (hmem _ ht.le z hz) _ (hmem _ ht.le w hw))
      u.property v.property
    have hBt0 : 0 ≤ Kb * ‖h t‖ + Db := by positivity
    rw [hBt, Real.norm_eq_abs, abs_of_nonneg hBt0]
    apply hraw.trans
    dsimp only [Aconst, Cconst, Kb, Db]
    simp only [NNReal.coe_mul, coe_nnnorm]
    have hQ := mul_le_mul_of_nonneg_left (Q.le_opNorm (h t))
      (show 0 ≤ ‖m‖ * (L : ℝ) by positivity)
    have hcoef : ‖m‖ * (L : ℝ) * ‖Q (h t)‖ + (B : ℝ) + ‖d‖ * ‖D‖ ≤
        ‖m‖ * (L : ℝ) * ‖Q‖ * ‖h t‖ + ((B : ℝ) + ‖d‖ * ‖D‖) := by
      nlinarith only [hQ]
    exact add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))) le_rfl
  have hmeas : TimeNemyMeas
      (show (0 : VectorHs g ι r s (a + 2)) ∈ {v | ‖J v‖ ≤ R} by
        simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le)
      (fun t v => N t (h t + v.val) - Δ (h t + v.val)) T := by
    intro T' hT' f hf
    have hμ : timeMeasure T' ≤ timeMeasure T :=
      Measure.restrict_mono (Icc_subset_Icc le_rfl hT') le_rfl
    have hsum := ((Lp.aestronglyMeasurable h).mono_measure hμ).add (Lp.aestronglyMeasurable f)
    have hα := aestronglyMeasurable_recentered_of_continuous_time_cylinder
      J u₀ hR.le hτ.le hTτ alpha ha h (hhnear.mono fun _ ht => ht.le) hT' f hf
    have hβ := aestronglyMeasurable_recentered_of_continuous_time_cylinder
      J u₀ hR.le hτ.le hTτ reaction hb h (hhnear.mono fun _ ht => ht.le) hT' f hf
    have hmul : Continuous (fun p : W × VectorHs g ι r s a => m p.1 p.2) :=
      (m.continuous.comp continuous_fst).clm_apply continuous_snd
    have hm := ((hmul.comp_aestronglyMeasurable
      (hα.prodMk (Q.continuous.comp_aestronglyMeasurable hsum))).add hβ).sub
      (Δ.continuous.comp_aestronglyMeasurable hsum)
    apply hm.congr
    filter_upwards [hf] with t ht
    simp only [N, aeSetLift, Set.mem_ofPred_eq, dite_eq_left ht, Pi.add_apply, Pi.sub_apply]
  have hBounds := Real.mul_add_sqrt_mul_le_of_le_min hR.le hKb hDb hKf hDf hhsmall hTtime
  have hbn : ‖Bt‖ ≤ 1 / 8 := hBnorm.trans hBounds.1
  have hfn : ‖F0‖ ≤ R / 8 := hF0norm.trans hBounds.2
  obtain ⟨hPR, hκ, hstay⟩ := tame_forcing_contraction_bounds_of_integrated_bounds
    hR.le hT1 Aconst Cconst hbn hfn hsmallA hsmallC
  obtain ⟨F, hF, hstate, hderiv, htrace, hfield⟩ :=
    exists_heatDuhamelVectorEvolution_of_tame_timeL2 hT.1 hR.le
      (show 0 ≤ R / 4 by positivity) u₀ N Aconst Cconst Bt F0 hPR (by linarith) hstay
      hzero htame hmeas
  refine ⟨F, hF, ?_, hderiv, htrace, hfield⟩
  have hsum := Lp.coeFn_add h (maximalRegularityDuhamelVectorField hT.1 0 F)
  have hsplit := heatDuhamelVectorField_eq_add hT.1 hc u₀ F
  filter_upwards [hstate, hhnear, hsum] with t hs ht hst
  rw [hsplit, hst, Pi.add_apply, map_add]
  exact hmem _ ht.le _ hs
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
