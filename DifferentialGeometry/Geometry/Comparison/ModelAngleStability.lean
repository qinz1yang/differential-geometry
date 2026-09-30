import DifferentialGeometry.Geometry.Comparison.ModelAngleContinuity
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleStability

set_option autoImplicit false

open Set Filter Real Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem comparisonAngleNegCurvature_uniform_stability_on_side_window
    {κ Lmin Lmax η : ℝ} (hκ : 0 ≤ κ) (hmin : 0 < Lmin) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b c a' b' c' : ℝ,
      a ∈ Icc Lmin Lmax → b ∈ Icc Lmin Lmax → c ∈ Icc 0 (2 * Lmax) →
      a' ∈ Icc Lmin Lmax → b' ∈ Icc Lmin Lmax → c' ∈ Icc 0 (2 * Lmax) →
      |a - a'| < δ → |b - b'| < δ → |c - c'| < δ →
      |comparisonAngleNegCurvature κ a b c - comparisonAngleNegCurvature κ a' b' c'| < η := by
  by_cases hk : κ = 0
  · subst κ
    simpa only [comparisonAngleNegCurvature_zero] using
      comparisonAngle_uniform_stability_on_side_window (Lmax := Lmax) hmin hη
  have hkpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hk)
  let K : Set (ℝ × ℝ × ℝ) := Icc Lmin Lmax ×ˢ (Icc Lmin Lmax ×ˢ Icc 0 (2 * Lmax))
  let f : ℝ × ℝ × ℝ → ℝ := fun z => comparisonAngleNegCurvature κ z.1 z.2.1 z.2.2
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hf : ContinuousOn f K := by
    intro z hz
    have hcont : ContinuousAt f z :=
      tendsto_comparisonAngleNegCurvature_of_pos hkpos continuous_fst.continuousAt.tendsto
        (continuous_fst.comp continuous_snd).continuousAt.tendsto
        (continuous_snd.comp continuous_snd).continuousAt.tendsto
        (hmin.trans_le hz.1.1) (hmin.trans_le hz.2.1.1)
    exact hcont.continuousWithinAt
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ, hδ, ?_⟩
  intro a b c a' b' c' ha hb hc ha' hb' hc' hab hbb hcc
  have hdist : dist (a, b, c) (a', b', c') < δ := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using ⟨hab, hbb, hcc⟩
  exact hd (a, b, c) ⟨ha, hb, hc⟩ (a', b', c') ⟨ha', hb', hc'⟩ hdist

theorem exists_uniform_comparisonAngleNegCurvature_near_pi
    {κ Lmin Lmax η : ℝ} (hκ : 0 ≤ κ) (hmin : 0 < Lmin) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b c : ℝ,
      a ∈ Icc Lmin Lmax → b ∈ Icc Lmin Lmax → 0 ≤ c → c ≤ a + b →
      a + b - c < δ → |comparisonAngleNegCurvature κ a b c - Real.pi| < η := by
  obtain ⟨δ, hδ, hd⟩ := comparisonAngleNegCurvature_uniform_stability_on_side_window
    (Lmax := Lmax) hκ hmin hη
  refine ⟨δ, hδ, ?_⟩
  intro a b c ha hb hc hcab hdef
  have ha0 : 0 < a := hmin.trans_le ha.1
  have hb0 : 0 < b := hmin.trans_le hb.1
  have hcwin : c ∈ Icc (0 : ℝ) (2 * Lmax) := ⟨hc, by linarith [ha.2, hb.2]⟩
  have hsumwin : a + b ∈ Icc (0 : ℝ) (2 * Lmax) :=
    ⟨(add_pos ha0 hb0).le, by linarith [ha.2, hb.2]⟩
  have hdiff : |c - (a + b)| < δ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hcab)]
    linarith
  have h := hd a b c a b (a + b) ha hb hcwin ha hb hsumwin
    (by simpa using hδ) (by simpa using hδ) hdiff
  rwa [comparisonAngleNegCurvature_add hκ ha0 hb0] at h

theorem tendsto_comparisonAngleNegCurvature_pi_of_deficit
    {I : Type*} {l : Filter I} {a b c : I → ℝ} {κ Lmin Lmax : ℝ}
    (hκ : 0 ≤ κ) (hmin : 0 < Lmin)
    (hbound : ∀ᶠ i in l, a i ∈ Icc Lmin Lmax ∧ b i ∈ Icc Lmin Lmax ∧
      0 ≤ c i ∧ c i ≤ a i + b i)
    (hdef : Tendsto (fun i => a i + b i - c i) l (𝓝 0)) :
    Tendsto (fun i => comparisonAngleNegCurvature κ (a i) (b i) (c i)) l (𝓝 Real.pi) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨δ, hδ, hd⟩ := exists_uniform_comparisonAngleNegCurvature_near_pi
    (Lmax := Lmax) hκ hmin hη
  have hsmall := Metric.tendsto_nhds.mp hdef δ hδ
  filter_upwards [hbound, hsmall] with i hi hdiff
  rw [Real.dist_eq]
  apply hd (a i) (b i) (c i) hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hdiff)

end DifferentialGeometry.Geometry.Comparison.Toponogov
