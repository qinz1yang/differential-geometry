import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRescaledVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalPoleCenters

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped ContDiff ENNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem exists_pos_le_ancient_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ v : ℝ, 0 < v ∧ ∀ (p : F.M) (tau : ℝ), 0 < tau →
      ENNReal.ofReal v ≤ intrinsicReducedVolume F.S 0 p tau := by
  let A : ℝ := (Module.finrank ℝ E : ℝ) / 2
  let L : ℝ := (Real.sqrt A + Real.sqrt 3 / 2) ^ 2
  let K : ℝ := 1 + (Module.finrank ℝ E : ℝ) ^ 2 * (3 * L)
  have hK : 0 < K := by dsimp only [K, L]; positivity
  let r : ℝ := min 1 (1 / Real.sqrt K)
  have hr : 0 < r := lt_min zero_lt_one (one_div_pos.mpr (Real.sqrt_pos.mpr hK))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrK : r ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * (3 * L)) ≤ 1 := by
    have hm : r * Real.sqrt K ≤ 1 :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hK)).mp (min_le_right _ _)
    have hs := (sq_le_sq₀ (mul_nonneg hr.le (Real.sqrt_nonneg K)) zero_le_one).2 hm
    rw [mul_pow, Real.sq_sqrt hK.le, one_pow] at hs
    have hB : (Module.finrank ℝ E : ℝ) ^ 2 * (3 * L) ≤ K := by dsimp only [K]; linarith
    exact (mul_le_mul_of_nonneg_left hB (sq_nonneg r)).trans hs
  let c : ℝ := Real.exp (-L - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hc : 0 < c := Real.exp_pos _
  refine ⟨kappa * r ^ Module.finrank ℝ E * c, by positivity [hF.kappa_pos], ?_⟩
  intro p tau htau
  obtain ⟨q, hq⟩ := exists_redLength_le_half_finrank_of_ancient F hF p htau
  let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
  let B : Set F.M := {y | riemannianEDistOf g q y < ENNReal.ofReal r}
  let mu := riemannianVolumeMeasure (I := I) (M := F.M) g
  have hB : MeasurableSet B :=
    (isOpen_lt (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g q)
      continuous_const).measurableSet
  have hvol : ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤ mu B := by
    apply volume_lower_bound_of_rescaled_distance_le F hF p q q htau (D := 0) le_rfl hq
    · simp only [riemannianEDistOf_self, ENNReal.ofReal_zero, le_refl]
    · exact hr
    · exact hr1
    · simpa only [zero_add, mul_one] using hrK
  have hlength : ∀ y ∈ B, redLength F.S 0 p y tau ≤ L := by
    intro y hy
    have hd : riemannianEDistOf g q y ≤ ENNReal.ofReal 1 :=
      hy.le.trans (ENNReal.ofReal_le_ofReal hr1)
    simpa only [mul_one] using redLength_le_of_rescaled_distance_le F hF p q y htau
      zero_le_one hq hd
  have hmass : mu B * ENNReal.ofReal c ≤ normalizedShrinkerMass g (fun y => redLength F.S 0 p y tau) := by
    calc
      _ = ∫⁻ _ in B, ENNReal.ofReal c ∂mu := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in B, ENNReal.ofReal (Real.exp (-redLength F.S 0 p y tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) ∂mu := by
        apply lintegral_mono_ae
        apply ae_restrict_of_forall_mem hB
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hl := hlength y hy
        linarith
      _ ≤ normalizedShrinkerMass g (fun y => redLength F.S 0 p y tau) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  have hscale : intrinsicReducedVolume F.S 0 p tau =
      normalizedShrinkerMass g (fun y => redLength F.S 0 p y tau) := by
    simpa only [zero_sub] using intrinsicReducedVolume_eq_normalizedShrinkerMass F.S 0 p htau
  rw [hscale]
  calc
    ENNReal.ofReal (kappa * r ^ Module.finrank ℝ E * c) =
        (ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E) * ENNReal.ofReal c := by
      rw [ENNReal.ofReal_mul (mul_nonneg hF.kappa_pos.le (pow_nonneg hr.le _)),
        ENNReal.ofReal_mul hF.kappa_pos.le, ENNReal.ofReal_pow hr.le]
    _ ≤ mu B * ENNReal.ofReal c := mul_le_mul_of_nonneg_right hvol (by positivity)
    _ ≤ _ := hmass

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
