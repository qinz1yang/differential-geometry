import DifferentialGeometry.Geometry.Comparison.ModelSide
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

set_option autoImplicit false

open Set Filter Real Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_uniform_modelSideNegCurvature_near_sum
    {κ L η : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b θ : ℝ,
      a ∈ Icc (0 : ℝ) L → b ∈ Icc (0 : ℝ) L → θ ∈ Icc (0 : ℝ) Real.pi →
      |θ - Real.pi| < δ → |modelSideNegCurvature κ a b θ - (a + b)| < η := by
  let K : Set (ℝ × ℝ × ℝ) := Icc (0 : ℝ) L ×ˢ (Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) Real.pi)
  let f : ℝ × ℝ × ℝ → ℝ := fun z => modelSideNegCurvature κ z.1 z.2.1 z.2.2
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hf : ContinuousOn f K := by
    intro z hz
    have hcont : ContinuousAt f z :=
      tendsto_modelSideNegCurvature hκ continuous_fst.continuousAt.tendsto
        (continuous_fst.comp continuous_snd).continuousAt.tendsto
        (continuous_snd.comp continuous_snd).continuousAt.tendsto hz.1.1 hz.2.1.1
    exact hcont.continuousWithinAt
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ, hδ, ?_⟩
  intro a b θ ha hb hθ hclose
  have hdist : dist (a, b, θ) (a, b, Real.pi) < δ := by
    simp only [Prod.dist_eq, dist_self, Real.dist_eq, max_lt_iff]
    exact ⟨hδ, hδ, hclose⟩
  have h := hd (a, b, θ) ⟨ha, hb, hθ⟩ (a, b, Real.pi)
    ⟨ha, hb, pi_nonneg, le_rfl⟩ hdist
  change |modelSideNegCurvature κ a b θ - modelSideNegCurvature κ a b Real.pi| < η at h
  rwa [modelSideNegCurvature_pi hκ ha.1 hb.1] at h

theorem tendsto_modelSideNegCurvature_deficit_of_angle_pi
    {I : Type*} {l : Filter I} {a b θ : I → ℝ} {κ L : ℝ} (hκ : 0 ≤ κ)
    (hbound : ∀ᶠ i in l, a i ∈ Icc (0 : ℝ) L ∧ b i ∈ Icc (0 : ℝ) L ∧
      θ i ∈ Icc (0 : ℝ) Real.pi) (hθ : Tendsto θ l (𝓝 Real.pi)) :
    Tendsto (fun i => a i + b i - modelSideNegCurvature κ (a i) (b i) (θ i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨δ, hδ, hd⟩ := exists_uniform_modelSideNegCurvature_near_sum (L := L) hκ hη
  have hsmall := Metric.tendsto_nhds.mp hθ δ hδ
  filter_upwards [hbound, hsmall] with i hi hclose
  rw [Real.dist_eq, sub_zero, abs_sub_comm]
  apply hd (a i) (b i) (θ i) hi.1 hi.2.1 hi.2.2
  simpa only [Real.dist_eq] using hclose

end DifferentialGeometry.Geometry.Comparison.Toponogov
