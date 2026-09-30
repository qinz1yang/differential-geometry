import DifferentialGeometry.Geometry.Comparison.BufferedAngleShortening
import DifferentialGeometry.Geometry.Comparison.OppositeCrossAngles
import DifferentialGeometry.Analysis.Asymptotics.ReciprocalShortening
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixCrossComparison

open Set Filter Metric
open scoped Topology

open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)] [∀ i, CompleteSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y]
variable {o : ∀ i, A i} {p : Y} {R ε σ : ℕ → ℝ}

theorem germComparisonAngle_eq_pi_div_two_of_converging_radial_prefixes
    (hs : fourPointComparison 0 (univ : Set Y))
    (hcurves : ∀ i, ∀ a b : A i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → A i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    {n : ℕ} (hdim : ∀ i, dimH (ball (o i) ((σ i)⁻¹)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (o i) ((σ i)⁻¹),
      ∃ Ω : Set (A i), IsOpen Ω ∧ fourPointComparison (σ i) Ω ∧ z ∈ Ω)
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0))
    (aPlus aMinus : ∀ i, ι → A i)
    (qPlus qMinus : ∀ i, ι → Icc (0 : ℝ) ((σ i)⁻¹) → A i)
    (hqPlus : ∀ i j, Isometry (qPlus i j)) (hqMinus : ∀ i j, Isometry (qMinus i j))
    (hqPlus0 : ∀ i j, qPlus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (hσpos i)).le⟩⟩ = o i)
    (hqMinus0 : ∀ i j, qMinus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (hσpos i)).le⟩⟩ = o i)
    (hqPlusEnd : ∀ i j, qPlus i j ⟨(σ i)⁻¹, ⟨(inv_pos.mpr (hσpos i)).le, le_rfl⟩⟩ = aPlus i j)
    (hqMinusEnd : ∀ i j, qMinus i j ⟨(σ i)⁻¹, ⟨(inv_pos.mpr (hσpos i)).le, le_rfl⟩⟩ = aMinus i j)
    (hcrossPlus : ∀ j k, j ≠ k → ∀ᶠ i in atTop,
      Real.pi / 2 - σ i ≤ comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (dist (aPlus i j) (aPlus i k)))
    (hcrossMinus : ∀ j k, j ≠ k → ∀ᶠ i in atTop,
      Real.pi / 2 - σ i ≤ comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (dist (aPlus i j) (aMinus i k)))
    (Q : ∀ i, ι → Icc (-((σ i)⁻¹)) ((σ i)⁻¹) → A i)
    (hLip : ∀ i j, LipschitzWith 1 (Q i j))
    (hbase : ∀ i j, Q i j ⟨0, ⟨by linarith [inv_pos.mpr (hσpos i)],
      (inv_pos.mpr (hσpos i)).le⟩⟩ = o i)
    (halignPlus : ∀ i j, ∀ t : Icc (0 : ℝ) ((σ i)⁻¹),
      Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos i)], t.property.2⟩⟩ = qPlus i j t)
    (halignMinus : ∀ i j, ∀ t : Icc (0 : ℝ) ((σ i)⁻¹),
      Q i j ⟨-t.val, ⟨by linarith [t.property.2],
        by linarith [t.property.1, inv_pos.mpr (hσpos i)]⟩⟩ = qMinus i j t)
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0)) (γ : ι → ℝ → Y)
    (hγ : ∀ j, Isometry (γ j)) (hγ0 : ∀ j, γ j 0 = p)
    (hconv : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ j, S ≤ (σ i)⁻¹ ∧
      ∀ t : Icc (-((σ i)⁻¹)) ((σ i)⁻¹), |t.val| ≤ S →
        ∀ ht : dist (Q i j t) (o i) ≤ R i,
          dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ) :
    ∀ j k, j ≠ k → germComparisonAngle 0 (γ j) (γ k) = Real.pi / 2 := by
  let b (i : ℕ) : ℝ := 2 * Real.arcsin (max 0 (Real.sin ((Real.pi / 2 - σ i) / 2) -
    ((Real.sin ((Real.pi / 2 - σ i) / 2))⁻¹ - Real.sin ((Real.pi / 2 - σ i) / 2)) /
      (Real.exp (2 * (Real.sqrt (σ i) * ((σ i)⁻¹ / 1024))) - 1)))
  have hb : Tendsto b atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_reciprocal_shortened_angle_lower_bound (by norm_num) hσpos hσ
  have hwithin : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hr : Tendsto (fun i => (σ i)⁻¹ / 1024) atTop atTop :=
    (tendsto_inv_nhdsGT_zero.comp hwithin).atTop_div_const (by norm_num)
  have hsmall : ∀ᶠ i in atTop, σ i < Real.pi / 2 :=
    hσ.eventually (gt_mem_nhds (by linarith [Real.pi_pos]))
  have hplus (i : ℕ) (j : ι) (hi : 1 ≤ (σ i)⁻¹) :
      IccExtend (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹)
        (Q i j) 1 = qPlus i j ⟨1, ⟨by norm_num, hi⟩⟩ := by
    rw [IccExtend_of_mem (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹)
      (Q i j) (show (1 : ℝ) ∈ Icc (-((σ i)⁻¹)) ((σ i)⁻¹) from ⟨by linarith, hi⟩)]
    exact halignPlus i j ⟨1, ⟨by norm_num, hi⟩⟩
  have hminus (i : ℕ) (j : ι) (hi : 1 ≤ (σ i)⁻¹) :
      IccExtend (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹)
        (Q i j) (-1) = qMinus i j ⟨1, ⟨by norm_num, hi⟩⟩ := by
    rw [IccExtend_of_mem (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹)
      (Q i j) (show (-1 : ℝ) ∈ Icc (-((σ i)⁻¹)) ((σ i)⁻¹) from ⟨by linarith, by linarith⟩)]
    exact halignMinus i j ⟨1, ⟨by norm_num, hi⟩⟩
  intro j k hjk
  have hanglePlus := tendsto_comparisonAngle_IccExtend_of_converging_signed_prefixes
    (L := fun i (_ : ι) => (σ i)⁻¹) (fun i _ => (inv_pos.mpr (hσpos i)).le)
    Q hLip hbase f hε γ hconv hσ (Eventually.of_forall fun i => (hσpos i).le)
    j k (s := 1) (t := 1) (by norm_num) (by norm_num)
  have hangleMinus := tendsto_comparisonAngle_IccExtend_of_converging_signed_prefixes
    (L := fun i (_ : ι) => (σ i)⁻¹) (fun i _ => (inv_pos.mpr (hσpos i)).le)
    Q hLip hbase f hε γ hconv hσ (Eventually.of_forall fun i => (hσpos i).le)
    j k (s := 1) (t := -1) (by norm_num) (by norm_num)
  simp only [abs_one, abs_neg] at hanglePlus hangleMinus
  have hbound : ∀ᶠ i in atTop,
      b i ≤ comparisonAngleNegCurvature (σ i) 1 1 (dist
        (IccExtend (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹) (Q i j) 1)
        (IccExtend (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹) (Q i k) 1)) ∧
      b i ≤ comparisonAngleNegCurvature (σ i) 1 1 (dist
        (IccExtend (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹) (Q i j) 1)
        (IccExtend (by linarith [inv_pos.mpr (hσpos i)] : -((σ i)⁻¹) ≤ (σ i)⁻¹) (Q i k) (-1))) := by
    filter_upwards [hsmall, hr.eventually_ge_atTop 1, hcrossPlus j k hjk,
      hcrossMinus j k hjk] with i hismall hi hcp hcm
    have hLpos : 0 < (σ i)⁻¹ := inv_pos.mpr (hσpos i)
    have hrpos : 0 < (σ i)⁻¹ / 1024 := div_pos hLpos (by norm_num)
    have hbuffer : 256 * ((σ i)⁻¹ / 1024) < (σ i)⁻¹ := by linarith
    have hiL : 1 ≤ (σ i)⁻¹ := by linarith
    have hT : (1 : ℝ) ∈ Ioc 0 ((σ i)⁻¹ / 1024) := ⟨by norm_num, hi⟩
    have hθ : 0 < Real.pi / 2 - σ i := sub_pos.mpr hismall
    have hcp' := comparison_angle_lower_bound_at_fixed_time_of_long_radial_isometries
      (hcurves i) (o i) (hσpos i) hrpos hbuffer (hdim i) (hlocal i)
      (qPlus i j) (qPlus i k) (hqPlus i j) (hqPlus i k) (hqPlus0 i j) (hqPlus0 i k)
      hT hθ (by simpa only [hqPlusEnd] using hcp)
    have hcm' := comparison_angle_lower_bound_at_fixed_time_of_long_radial_isometries
      (hcurves i) (o i) (hσpos i) hrpos hbuffer (hdim i) (hlocal i)
      (qPlus i j) (qMinus i k) (hqPlus i j) (hqMinus i k) (hqPlus0 i j) (hqMinus0 i k)
      hT hθ (by simpa only [hqPlusEnd, hqMinusEnd] using hcm)
    rw [hplus i j hiL, hplus i k hiL, hminus i k hiL]
    exact ⟨hcp', hcm'⟩
  have hp : Real.pi / 2 ≤ comparisonAngle 1 1 (dist (γ j 1) (γ k 1)) := by
    simpa only [abs_one, comparisonAngleNegCurvature_zero] using
      le_of_tendsto_of_tendsto hb hanglePlus (hbound.mono fun _ hi => hi.1)
  have hm : Real.pi / 2 ≤ comparisonAngle 1 1 (dist (γ j 1) (γ k (-1))) := by
    simpa only [abs_one, abs_neg, comparisonAngleNegCurvature_zero] using
      le_of_tendsto_of_tendsto hb hangleMinus (hbound.mono fun _ hi => hi.2)
  exact germComparisonAngle_eq_pi_div_two_of_opposite_cross_lower_bounds hs
    (hγ j) (hγ k) (by rw [hγ0, hγ0]) zero_lt_one hp hm

end GC.MetricGeometry
