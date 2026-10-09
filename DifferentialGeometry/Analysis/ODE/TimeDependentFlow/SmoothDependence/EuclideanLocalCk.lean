import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.EuclideanCk

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology NNReal ContDiff
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE

theorem exists_confined_isLocalFlow_contDiffOn_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ∞} (hk : 1 ≤ k)
    {Ω : Set E} (hΩ : IsOpen Ω) {F : E → E}
    (hF : ContDiffOn ℝ k F Ω) {z₀ : E} (hz₀ : z₀ ∈ Ω) :
    ∃ (r : ℝ≥0) (ε : ℝ), 0 < (r : ℝ) ∧ 0 < ε ∧
      ∃ Φ : E × ℝ → E,
        IsLocalFlow (fun _ z => F z) 0 z₀ r (-ε) ε Φ ∧
        ContDiffOn ℝ k Φ (closedBall z₀ (r : ℝ) ×ˢ Icc (-ε) ε) ∧
        MapsTo Φ (closedBall z₀ (r : ℝ) ×ˢ Icc (-ε) ε) Ω := by
  obtain ⟨G, hG, _, hGF⟩ := exists_contDiffOn_cutoff_extension
    (S := (univ : Set E)) hΩ (by simpa only [univ_inter] using hF) hz₀
  have hGtime : ContDiff ℝ k (Function.uncurry (fun (_ : ℝ) z => G z)) :=
    (contDiffOn_univ.mp hG).comp contDiff_snd
  obtain ⟨r₀, ε₀, hr₀, _hε₀, Φ, hflow, ρ, T, hρ, hT, hρr, hTε, hΦ⟩ :=
    exists_isLocalFlow_contDiffOn_Ck (t₀ := 0) (x₀ := z₀) hk hGtime
  let V : Set E := Ω ∩ {z | G z = F z}
  have hV : V ∈ 𝓝 z₀ := inter_mem (hΩ.mem_nhds hz₀) hGF
  have hzero : Φ (z₀, 0) = z₀ := hflow.apply_initial z₀ (mem_closedBall_self hr₀.le)
  have hcenter : (z₀, (0 : ℝ)) ∈ ball z₀ ρ ×ˢ Ioo (0 - T) (0 + T) :=
    ⟨mem_ball_self hρ, by constructor <;> linarith⟩
  have hbox : ball z₀ ρ ×ˢ Ioo (0 - T) (0 + T) ∈ 𝓝 (z₀, (0 : ℝ)) :=
    (isOpen_ball.prod isOpen_Ioo).mem_nhds hcenter
  have hΦat : ContinuousAt Φ (z₀, (0 : ℝ)) := hΦ.continuousOn.continuousAt hbox
  have hpre : Φ ⁻¹' V ∈ 𝓝 (z₀, (0 : ℝ)) :=
    hΦat.preimage_mem_nhds (by rwa [hzero])
  let D : Set (E × ℝ) := (ball z₀ ρ ×ˢ Ioo (0 - T) (0 + T)) ∩ Φ ⁻¹' V
  have hD : D ∈ 𝓝 (z₀, (0 : ℝ)) := inter_mem hbox hpre
  obtain ⟨A, hA, C, hC, hAC⟩ := mem_nhds_prod_iff.mp hD
  obtain ⟨a, ha, hballA⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨b, hb, hballC⟩ := Metric.mem_nhds_iff.mp hC
  let r : ℝ≥0 := ⟨a / 2, by positivity⟩
  let ε : ℝ := b / 2
  have hr : 0 < (r : ℝ) := by
    change 0 < a / 2
    exact div_pos ha (by norm_num)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hspaceA : closedBall z₀ (r : ℝ) ⊆ A := by
    apply subset_trans (closedBall_subset_ball ?_) hballA
    change a / 2 < a
    linarith
  have htimeC : Icc (-ε) ε ⊆ C := by
    intro t ht
    apply hballC
    rw [mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.mpr ht).trans_lt (by dsimp [ε]; linarith)
  have hsub : closedBall z₀ (r : ℝ) ×ˢ Icc (-ε) ε ⊆ D :=
    fun q hq => hAC ⟨hspaceA hq.1, htimeC hq.2⟩
  have htimeZero : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hspaceFlow : closedBall z₀ (r : ℝ) ⊆ closedBall z₀ (r₀ : ℝ) := by
    intro z hz
    have hz' : (z, (0 : ℝ)) ∈ D := hsub ⟨hz, htimeZero⟩
    exact ball_subset_closedBall (ball_subset_ball hρr hz'.1.1)
  have htimeFlow : Icc (-ε) ε ⊆ Icc (0 - ε₀) (0 + ε₀) := by
    intro t ht
    have hzt : (z₀, t) ∈ D := hsub ⟨mem_closedBall_self hr.le, ht⟩
    have ht' := hzt.1.2
    exact ⟨by linarith [ht'.1, hTε], by linarith [ht'.2, hTε]⟩
  have hΦnew : ContDiffOn ℝ k Φ (closedBall z₀ (r : ℝ) ×ˢ Icc (-ε) ε) :=
    hΦ.mono (fun q hq => (hsub hq).1)
  refine ⟨r, ε, hr, hε, Φ, ?_, hΦnew, ?_⟩
  · refine
      { minTime_le_initial := by linarith
        initial_le_maxTime := hε.le
        apply_initial := fun z hz => hflow.apply_initial z (hspaceFlow hz)
        hasDerivWithinAt := ?_
        continuousOn := hΦnew.continuousOn
        exists_lipschitz := ?_ }
    · intro z hz t ht
      have hd := (hflow.hasDerivWithinAt z (hspaceFlow hz) t (htimeFlow ht)).mono htimeFlow
      have hagree : G (Φ (z, t)) = F (Φ (z, t)) := (hsub ⟨hz, ht⟩).2.2
      simpa only [hagree] using hd
    · obtain ⟨L, hL⟩ := hflow.exists_lipschitz
      exact ⟨L, fun t ht => (hL t (htimeFlow ht)).mono hspaceFlow⟩
  · intro q hq
    exact (hsub hq).2.1

end DifferentialGeometry.Analysis.ODE
