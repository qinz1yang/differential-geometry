import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import DifferentialGeometry.Geometry.Metric.Sphere.RoundChartGram
import DifferentialGeometry.Analysis.Integration.Measure.NoAtoms
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket


noncomputable section

open Manifold Metric Module Set MeasureTheory Filter Topology
open scoped Manifold Topology RealInnerProductSpace
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry
namespace Geometry

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private local instance :
    MeasurableSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := borel _
private local instance :
    BorelSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := ⟨rfl⟩

def northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

def stereoHeight (x : EuclideanSpace ℝ (Fin 2)) : ℝ := (4 - ‖x‖ ^ 2) / (4 + ‖x‖ ^ 2)

def stereoDensity (x : EuclideanSpace ℝ (Fin 2)) : ℝ := (4 / (‖x‖ ^ 2 + 4)) ^ 2

theorem innerCoordFun_northPole_symm (x : EuclideanSpace ℝ (Fin 2)) :
    innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
        (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
        ((extChartAt (𝓡 2) northPole).symm x)
      = stereoHeight x := by
  have hw : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3))
      = (northPole : EuclideanSpace ℝ (Fin 3)) := rfl
  change ⟪(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)),
      ((extChartAt (𝓡 2) northPole).symm x : EuclideanSpace ℝ (Fin 3))⟫ = stereoHeight x
  rw [show ((extChartAt (𝓡 2) northPole).symm x : EuclideanSpace ℝ (Fin 3))
      = ((stereographic' 2 (-northPole)).symm x : EuclideanSpace ℝ (Fin 3)) from rfl]
  rw [stereographic'_symm_apply]
  simp only [inner_add_right, real_inner_smul_right]
  set U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-northPole))).repr with hU
  set y := U.symm x with hy
  have hu : (↑northPole : EuclideanSpace ℝ (Fin 3))
      ∈ ℝ ∙ (↑(-northPole) : EuclideanSpace ℝ (Fin 3)) := by
    rw [Submodule.mem_span_singleton]
    exact ⟨-1, by rw [coe_neg_sphere]; module⟩
  have hA : ⟪(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)),
      (↑y : EuclideanSpace ℝ (Fin 3))⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu (Submodule.coe_mem y)
  have hB : ⟪(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)),
      (↑(-northPole) : EuclideanSpace ℝ (Fin 3))⟫ = -1 := by
    rw [coe_neg_sphere, inner_neg_right, hw, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp northPole.2]
    norm_num
  have hC : ‖(↑y : EuclideanSpace ℝ (Fin 3))‖ = ‖x‖ := by
    rw [hy]; exact U.symm.norm_map x
  rw [hA, hB, hC]
  simp only [stereoHeight]
  ring

private lemma stereoDensity_nonneg (y : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ stereoDensity y := by
  rw [stereoDensity]; positivity

private lemma continuous_stereoDensity : Continuous stereoDensity := by
  unfold stereoDensity
  exact
    (continuous_const.div (by fun_prop) (fun y => by positivity)).pow 2

private lemma integrable_stereoDensity :
    Integrable stereoDensity (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  have hnr : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)) < 4 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hdom :=
    (integrable_rpow_neg_one_add_norm_sq (E := EuclideanSpace ℝ (Fin 2))
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) hnr).const_mul (16 : ℝ)
  have he : ∀ z : ℝ, 0 < z → z ^ (-4/2 : ℝ) = (z ^ 2)⁻¹ := by
    intro z hz
    rw [show (-4/2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hz.le,
      Real.rpow_natCast]
  refine hdom.mono' continuous_stereoDensity.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.norm_of_nonneg (stereoDensity_nonneg y), he (1 + ‖y‖ ^ 2) (by positivity)]
  rw [stereoDensity, div_pow, show ((4 : ℝ)) ^ 2 = 16 by norm_num, ← mul_one_div, ← one_div]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
  exact one_div_le_one_div_of_le (by positivity)
    (by nlinarith [sq_nonneg (‖y‖ : ℝ), norm_nonneg y])

private lemma extChartAt_northPole_target :
    (extChartAt (𝓡 2) northPole).target
      = (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) := by
  have h : (chartAt (EuclideanSpace ℝ (Fin 2)) northPole).target
      = (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) := stereographic'_target (-northPole)
  rw [extChartAt_target, h]
  simp [Set.preimage_univ]

private lemma continuous_extChartAt_northPole_symm :
    Continuous ((extChartAt (𝓡 2) northPole).symm) := by
  rw [← continuousOn_univ, ← extChartAt_northPole_target]
  exact continuousOn_extChartAt_symm northPole

private lemma integral_chartDensity_modelHaar_eq_stereoDensity_volume
    {G : EuclideanSpace ℝ (Fin 2) → ℝ} (hG : Continuous G) :
    (∫ y, chartDensity (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) northPole
            ((extChartAt (𝓡 2) northPole).symm y) * G y
          ∂(modelHaar (E := EuclideanSpace ℝ (Fin 2))))
      = ∫ y, stereoDensity y * G y ∂volume := sorry

private lemma integral_rvm_eq_of_support_in_chart
    {H : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ} (hH : Continuous H)
    (hsupp : tsupport H ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) northPole).source) :
    (∫ p, H p
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      = ∫ y, stereoDensity y * H ((extChartAt (𝓡 2) northPole).symm y) ∂volume := by
  haveI : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Metric.sphere.compactSpace _ _
  rw [DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) northPole hH hsupp]
  rw [integral_chartLocalMeasure (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    northPole H hH.measurable]
  rw [extChartAt_northPole_target, setIntegral_univ]
  exact integral_chartDensity_modelHaar_eq_stereoDensity_volume
    (hH.comp continuous_extChartAt_northPole_symm)

theorem integral_roundMetric_stereographic_reduction
    {F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ} (hF : Continuous F) :
    (∫ p, F p
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      = ∫ x : EuclideanSpace ℝ (Fin 2),
          stereoDensity x *
            F ((extChartAt (𝓡 2) northPole).symm x) ∂volume := by
  classical
  haveI : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Metric.sphere.compactSpace _ _
  haveI : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := ⟨northPole⟩
  haveI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  haveI hfin : IsFiniteMeasure
      (riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ p, |F p| ≤ C := by
    obtain ⟨p₀, -, hp₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hF.abs.continuousOn
    exact ⟨|F p₀|, fun p => isMaxOn_iff.mp hp₀ p (Set.mem_univ p)⟩
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC northPole)
  have hchart_src : (chartAt (EuclideanSpace ℝ (Fin 2)) northPole).source
      = ({-northPole}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    stereographic'_source (-northPole)
  set d : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ :=
    fun p => ‖(p : EuclideanSpace ℝ (Fin 3)) + (northPole : EuclideanSpace ℝ (Fin 3))‖
    with hd_def
  have hd_cont : Continuous d := (continuous_subtype_val.add continuous_const).norm
  have hd_zero_iff : ∀ p, d p = 0 ↔ p = -northPole := by
    intro p
    simp only [hd_def]
    rw [norm_eq_zero, add_eq_zero_iff_eq_neg, ← coe_neg_sphere]
    exact Subtype.ext_iff.symm
  set cutoff : ℕ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ :=
    fun n p => min (1 : ℝ) (max 0 (((n : ℝ) + 1) * d p - 1)) with hcut_def
  have hcut_cont : ∀ n, Continuous (cutoff n) := fun n =>
    continuous_const.min
      (continuous_const.max ((continuous_const.mul hd_cont).sub continuous_const))
  have hcut01 : ∀ n p, 0 ≤ cutoff n p ∧ cutoff n p ≤ 1 := fun n p =>
    ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hcut_tendsto : ∀ p, p ≠ -northPole →
      Tendsto (fun n => cutoff n p) atTop (𝓝 1) := by
    intro p hp
    have hdne : d p ≠ 0 := fun h => hp ((hd_zero_iff p).mp h)
    have hdp : 0 < d p := lt_of_le_of_ne (by rw [hd_def]; exact norm_nonneg _) (Ne.symm hdne)
    have hev : ∀ᶠ n in atTop, cutoff n p = 1 := by
      obtain ⟨N, hN⟩ := exists_nat_ge (2 / d p)
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hge : (2 : ℝ) / d p ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
      rw [div_le_iff₀ hdp] at hge
      have h1 : (2 : ℝ) ≤ ((n : ℝ) + 1) * d p := by nlinarith [hdp.le, hge]
      have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) * d p - 1 := by linarith
      simp only [hcut_def]
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1) * d p - 1), min_eq_left h2]
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  have hlim_rvm : Tendsto
      (fun n => ∫ p, F p * cutoff n p
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      atTop (𝓝 (∫ p, F p
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hF.mul (hcut_cont n)).aestronglyMeasurable) (integrable_const C)
      (fun n => Filter.Eventually.of_forall (fun p => ?_)) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      calc |F p| * |cutoff n p|
          ≤ C * 1 := by
            refine mul_le_mul (hC p) ?_ (abs_nonneg _) (le_trans (abs_nonneg _) (hC p))
            rw [abs_of_nonneg (hcut01 n p).1]; exact (hcut01 n p).2
        _ = C := mul_one C
    · have hnull : (riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) {(-northPole)} = 0 :=
        riemannianVolumeMeasure_singleton _ (-northPole)
      rw [ae_iff]
      refine measure_mono_null ?_ hnull
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      simp only [Set.mem_singleton_iff]
      by_contra hpne
      exact hp (by simpa using (tendsto_const_nhds (x := F p)).mul (hcut_tendsto p hpne))
  have hlim_vol : Tendsto
      (fun n => ∫ y, stereoDensity y *
        (F ((extChartAt (𝓡 2) northPole).symm y)
          * cutoff n ((extChartAt (𝓡 2) northPole).symm y)) ∂volume)
      atTop (𝓝 (∫ y, stereoDensity y
        * F ((extChartAt (𝓡 2) northPole).symm y) ∂volume)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => C * stereoDensity y)
      (fun n => (continuous_stereoDensity.mul
        ((hF.comp continuous_extChartAt_northPole_symm).mul
          ((hcut_cont n).comp continuous_extChartAt_northPole_symm))).aestronglyMeasurable)
      (integrable_stereoDensity.const_mul C)
      (fun n => Filter.Eventually.of_forall (fun y => ?_)) (Filter.Eventually.of_forall (fun y => ?_))
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (stereoDensity_nonneg y)]
      calc stereoDensity y * (|F ((extChartAt (𝓡 2) northPole).symm y)|
            * |cutoff n ((extChartAt (𝓡 2) northPole).symm y)|)
          ≤ stereoDensity y * (C * 1) := by
            have h2 : |cutoff n ((extChartAt (𝓡 2) northPole).symm y)| ≤ 1 := by
              rw [abs_of_nonneg (hcut01 n _).1]; exact (hcut01 n _).2
            have hb : |F ((extChartAt (𝓡 2) northPole).symm y)|
                * |cutoff n ((extChartAt (𝓡 2) northPole).symm y)| ≤ C * 1 :=
              calc |F ((extChartAt (𝓡 2) northPole).symm y)|
                    * |cutoff n ((extChartAt (𝓡 2) northPole).symm y)|
                  ≤ C * |cutoff n ((extChartAt (𝓡 2) northPole).symm y)| :=
                    mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
                _ ≤ C * 1 := mul_le_mul_of_nonneg_left h2 hC0
            exact mul_le_mul_of_nonneg_left hb (stereoDensity_nonneg y)
        _ = C * stereoDensity y := by ring
    · have hsy : (extChartAt (𝓡 2) northPole).symm y ≠ -northPole := by
        have hmem : (extChartAt (𝓡 2) northPole).symm y
            ∈ (extChartAt (𝓡 2) northPole).source :=
          (extChartAt (𝓡 2) northPole).map_target
            (by rw [extChartAt_northPole_target]; exact Set.mem_univ y)
        rw [extChartAt_source, hchart_src] at hmem
        simpa using hmem
      have h2 : Tendsto (fun n => stereoDensity y *
          (F ((extChartAt (𝓡 2) northPole).symm y)
            * cutoff n ((extChartAt (𝓡 2) northPole).symm y))) atTop
          (𝓝 (stereoDensity y * (F ((extChartAt (𝓡 2) northPole).symm y) * 1))) :=
        (tendsto_const_nhds (x := stereoDensity y)).mul
          ((tendsto_const_nhds (x := F ((extChartAt (𝓡 2) northPole).symm y))).mul
            (hcut_tendsto _ hsy))
      rwa [mul_one] at h2
  have hpk : ∀ n, (∫ p, F p * cutoff n p
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      = ∫ y, stereoDensity y *
          (F ((extChartAt (𝓡 2) northPole).symm y)
            * cutoff n ((extChartAt (𝓡 2) northPole).symm y)) ∂volume := by
    intro n
    have hsupp : tsupport (fun p => F p * cutoff n p)
        ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) northPole).source := by
      rw [hchart_src]
      have hclosed : IsClosed {q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
          | (1 : ℝ) / ((n : ℝ) + 1) ≤ d q} := isClosed_le continuous_const hd_cont
      have hsub : tsupport (fun p => F p * cutoff n p)
          ⊆ {q | (1 : ℝ) / ((n : ℝ) + 1) ≤ d q} := by
        refine closure_minimal ?_ hclosed
        intro q hq
        rw [Function.mem_support] at hq
        have hcne : cutoff n q ≠ 0 := fun h => hq (by rw [h, mul_zero])
        change (1 : ℝ) / ((n : ℝ) + 1) ≤ d q
        by_contra hlt
        rw [not_le] at hlt
        apply hcne
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hlt2 : ((n : ℝ) + 1) * d q - 1 < 0 := by
          have h := mul_lt_mul_of_pos_left hlt hn1
          rw [mul_one_div, div_self hn1.ne'] at h
          linarith
        simp only [hcut_def]
        rw [max_eq_left (le_of_lt hlt2), min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      intro p hp
      have h1 := hsub hp
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      rw [heq] at h1
      simp only [Set.mem_setOf_eq] at h1
      rw [(hd_zero_iff (-northPole)).mpr rfl] at h1
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    exact integral_rvm_eq_of_support_in_chart (hF.mul (hcut_cont n)) hsupp
  have hseq : (fun n => ∫ p, F p * cutoff n p
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      = fun n => ∫ y, stereoDensity y *
          (F ((extChartAt (𝓡 2) northPole).symm y)
            * cutoff n ((extChartAt (𝓡 2) northPole).symm y)) ∂volume := funext hpk
  rw [hseq] at hlim_rvm
  exact tendsto_nhds_unique hlim_rvm hlim_vol

def zonalRadialIntegrand (y : ℝ) : ℝ :=
  (4 / (y ^ 2 + 4)) ^ 2 *
    (((3 * ((4 - y ^ 2) / (4 + y ^ 2)) ^ 2 - 1) / 2) *
      (1 - ((4 - y ^ 2) / (4 + y ^ 2)) ^ 2))

def zonalRadialAntideriv (y : ℝ) : ℝ :=
  128 * (-(y ^ 2 + 4) ^ (-2 : ℤ) / 2 + 28 * (y ^ 2 + 4) ^ (-3 : ℤ) / 3
    - 48 * (y ^ 2 + 4) ^ (-4 : ℤ) + 384 * (y ^ 2 + 4) ^ (-5 : ℤ) / 5)

private lemma hasDerivAt_zonalRadialAntideriv (y : ℝ) :
    HasDerivAt zonalRadialAntideriv (y * zonalRadialIntegrand y) y := by
  have hne : (y ^ 2 + 4 : ℝ) ≠ 0 := by positivity
  have hbase : HasDerivAt (fun y : ℝ => y ^ 2 + 4) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const 4
  have hpow : ∀ m : ℤ, HasDerivAt (fun y : ℝ => (y ^ 2 + 4) ^ m)
      ((m : ℝ) * (y ^ 2 + 4) ^ (m - 1) * (2 * y)) y := by
    intro m
    simpa [Function.comp] using
      (hasDerivAt_zpow m (y ^ 2 + 4) (Or.inl hne)).comp y hbase
  have hH := ((((((hpow (-2)).neg.div_const 2).add
      (((hpow (-3)).const_mul 28).div_const 3)).sub
      ((hpow (-4)).const_mul 48)).add
      (((hpow (-5)).const_mul 384).div_const 5)).const_mul 128)
  convert hH using 1
  rw [zonalRadialIntegrand]
  rw [show ((-2 : ℤ) - 1) = -3 by rfl, show ((-3 : ℤ) - 1) = -4 by rfl,
      show ((-4 : ℤ) - 1) = -5 by rfl, show ((-5 : ℤ) - 1) = -6 by rfl]
  rw [show (4 + y ^ 2 : ℝ) = (y ^ 2 + 4) by ring]
  simp only [zpow_neg]
  rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by rfl,
      show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by rfl, show ((5 : ℤ)) = ((5 : ℕ) : ℤ) by rfl,
      show ((6 : ℤ)) = ((6 : ℕ) : ℤ) by rfl]
  simp only [zpow_natCast]
  field_simp
  ring

private lemma zonalRadialAntideriv_zero : zonalRadialAntideriv 0 = 4 / 15 := by
  rw [zonalRadialAntideriv]; norm_num

private lemma tendsto_zonalRadialAntideriv :
    Tendsto zonalRadialAntideriv atTop (nhds 0) := by
  have h : Tendsto (fun y : ℝ => (y ^ 2 + 4)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 4 (tendsto_pow_atTop (by norm_num))
  have t : ∀ k : ℤ, k < 0 → Tendsto (fun y : ℝ => (y ^ 2 + 4) ^ k) atTop (nhds 0) :=
    fun k hk => (tendsto_zpow_atTop_zero hk).comp h
  have hexpr := ((((t (-2) (by norm_num)).neg.div_const 2).add
      (((t (-3) (by norm_num)).const_mul 28).div_const 3)).sub
      ((t (-4) (by norm_num)).const_mul 48)).add
      (((t (-5) (by norm_num)).const_mul 384).div_const 5)
  have := hexpr.const_mul 128
  simpa [zonalRadialAntideriv] using this

private lemma zonalRadialIntegrand_val (y : ℝ) :
    y * zonalRadialIntegrand y
      = 256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16) / (y ^ 2 + 4) ^ 6 := by
  rw [zonalRadialIntegrand]
  have h1 : (y ^ 2 + 4 : ℝ) ≠ 0 := by positivity
  have h2 : (4 + y ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma continuous_mul_zonalRadialIntegrand :
    Continuous (fun y : ℝ => y * zonalRadialIntegrand y) := by
  have : (fun y : ℝ => y * zonalRadialIntegrand y)
      = fun y => 256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16) / (y ^ 2 + 4) ^ 6 := by
    funext y; exact zonalRadialIntegrand_val y
  rw [this]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro y; positivity

private lemma integrableOn_mul_zonalRadialIntegrand :
    IntegrableOn (fun y : ℝ => y * zonalRadialIntegrand y) (Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (g := fun y => 1600 * (1 + y ^ 2)⁻¹)
    ((integrable_inv_one_add_sq.const_mul 1600).integrableOn) ?_ ?_
  · exact continuous_mul_zonalRadialIntegrand.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 ≤ y := le_of_lt hy
    rw [Real.norm_eq_abs, zonalRadialIntegrand_val y]
    rw [show (1600 : ℝ) * (1 + y ^ 2)⁻¹ = 1600 / (1 + y ^ 2) by rw [div_eq_mul_inv]]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y ^ 2 + 4) ^ 6)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have habs : |256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16)|
        ≤ 256 * y ^ 3 * (25 * (y ^ 2 + 4) ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 256 * y ^ 3)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg y, sq_nonneg (y ^ 2), sq_nonneg (y ^ 2 - 4)]
      · nlinarith [sq_nonneg y, sq_nonneg (y ^ 2)]
    calc |256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16)| * (1 + y ^ 2)
        ≤ (256 * y ^ 3 * (25 * (y ^ 2 + 4) ^ 2)) * (1 + y ^ 2) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
      _ ≤ 1600 * (y ^ 2 + 4) ^ 6 := by
          nlinarith [pow_nonneg hy0 3, sq_nonneg y, sq_nonneg (y ^ 2),
            pow_nonneg (by positivity : (0:ℝ) ≤ y ^ 2 + 4) 4,
            mul_nonneg (pow_nonneg hy0 3) (sq_nonneg (y ^ 2 - 1))]

theorem integral_stereoDensity_legendreTwo :
    (∫ x : EuclideanSpace ℝ (Fin 2),
        stereoDensity x *
          (((3 * stereoHeight x ^ 2 - 1) / 2) * (1 - stereoHeight x ^ 2)) ∂volume)
      = -(8 * Real.pi / 15) := by
  have hGrw : (∫ x : EuclideanSpace ℝ (Fin 2),
      stereoDensity x * (((3 * stereoHeight x ^ 2 - 1) / 2) * (1 - stereoHeight x ^ 2)) ∂volume)
      = ∫ x : EuclideanSpace ℝ (Fin 2), zonalRadialIntegrand ‖x‖ ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => rfl))
  rw [hGrw]
  rw [MeasureTheory.integral_fun_norm_addHaar volume zonalRadialIntegrand]
  rw [finrank_euclideanSpace_fin]
  have hballr : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = Real.pi := by
    rw [MeasureTheory.measureReal_def, EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_ofReal Real.pi_pos.le]
  have hI : (∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • zonalRadialIntegrand y) = -(4 / 15) := by
    have he : (fun y : ℝ => y ^ (2 - 1) • zonalRadialIntegrand y)
        = fun y => y * zonalRadialIntegrand y := by
      funext y; rw [show (2 - 1) = 1 from rfl, pow_one, smul_eq_mul]
    rw [he]
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x _ => hasDerivAt_zonalRadialAntideriv x) integrableOn_mul_zonalRadialIntegrand
      tendsto_zonalRadialAntideriv]
    rw [zonalRadialAntideriv_zero]; norm_num
  rw [hI, hballr]
  rw [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem integral_legendreTwo_height_roundMetric :
    (∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2 - 1) / 2)
          * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := 𝓡 2)
          (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (DifferentialGeometry.Geometry.roundMetric
            (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      = -(8 * Real.pi / 15) := by
  have hc : Continuous
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
          (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p)) :=
    (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))).contMDiff.continuous
  have hcont : Continuous
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        ((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2 - 1) / 2)
          * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2)) :=
    (((continuous_const.mul (hc.pow 2)).sub continuous_const).div_const 2).mul
      (continuous_const.sub (hc.pow 2))
  calc
    (∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2 - 1) / 2)
          * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2)
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
        = ∫ x : EuclideanSpace ℝ (Fin 2),
            stereoDensity x *
              (((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
                  (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
                  ((extChartAt (𝓡 2) northPole).symm x)) ^ 2 - 1) / 2)
                * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
                  (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
                  ((extChartAt (𝓡 2) northPole).symm x)) ^ 2)) ∂volume :=
      integral_roundMetric_stereographic_reduction hcont
    _ = ∫ x : EuclideanSpace ℝ (Fin 2),
          stereoDensity x *
            (((3 * stereoHeight x ^ 2 - 1) / 2) * (1 - stereoHeight x ^ 2)) ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        dsimp only
        rw [innerCoordFun_northPole_symm]
    _ = -(8 * Real.pi / 15) := integral_stereoDensity_legendreTwo

end Geometry
end DifferentialGeometry
