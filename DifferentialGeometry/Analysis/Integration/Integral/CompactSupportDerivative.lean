import DifferentialGeometry.Analysis.Integration.Integral.CompactSupportParametric
import Mathlib.Analysis.Calculus.ParametricIntegral



noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis




theorem hasDerivAt_planeIntegral_of_compact_support
    {f : ℝ → ℂ → ℝ} {S : Set ℝ} {K : Set ℂ} (hS : IsOpen S) (hK : IsCompact K)
    (hzero : ∀ r, ∀ w, r ∈ S → w ∉ K → f r w = 0)
    (hf : ContDiffOn ℝ 1 (fun q : ℝ × ℂ => f q.1 q.2) (S ×ˢ univ))
    {r₀ : ℝ} (hr₀ : r₀ ∈ S) :
    HasDerivAt (fun r => ∫ w : ℂ, f r w) (∫ w : ℂ, deriv (fun r => f r w) r₀) r₀ := by
  let d : ℝ × ℂ → ℝ := fun q => fderiv ℝ (fun p : ℝ × ℂ => f p.1 p.2) q (1, 0)
  have hd : ContinuousOn d (S ×ˢ univ) :=
    (hf.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) le_rfl).clm_apply continuousOn_const
  have hder (r : ℝ) (hr : r ∈ S) (w : ℂ) : HasDerivAt (fun t => f t w) (d (r, w)) r := by
    have hp : (r, w) ∈ S ×ˢ (univ : Set ℂ) := ⟨hr, mem_univ _⟩
    have hj := ((hf _ hp).contDiffAt ((hS.prod isOpen_univ).mem_nhds hp)).differentiableAt
      (by simp : (1 : WithTop ℕ∞) ≠ 0)
    have hline : HasDerivAt (fun t : ℝ => (t, w)) (1, 0) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r w)
    exact hj.hasFDerivAt.comp_hasDerivAt r hline
  have hslice (r : ℝ) (hr : r ∈ S) : Continuous (f r) := by
    rw [← continuousOn_univ]
    exact hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hr, mem_univ _⟩)
  have hdslice (r : ℝ) (hr : r ∈ S) : Continuous (fun w => d (r, w)) := by
    rw [← continuousOn_univ]
    exact hd.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hr, mem_univ _⟩)
  obtain ⟨a, ha, haS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hr₀)
  have hclosed : closedBall r₀ (a / 2) ⊆ S :=
    (closedBall_subset_ball (by linarith : a / 2 < a)).trans haS
  have hprod : closedBall r₀ (a / 2) ×ˢ K ⊆ S ×ˢ (univ : Set ℂ) :=
    fun _ hp => ⟨hclosed hp.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r₀ (a / 2)).prod hK).exists_bound_of_continuousOn
    (hd.mono hprod)
  let μ : Measure ℂ := volume.restrict K
  have : IsFiniteMeasure μ := ⟨by
    change (volume.restrict K) univ < ⊤
    simpa using hK.measure_lt_top (μ := volume)⟩
  have hmem : ∀ᵐ w ∂μ, w ∈ K := ae_restrict_mem hK.measurableSet
  have hSr : ∀ᶠ r in 𝓝 r₀, r ∈ S := hS.mem_nhds hr₀
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := f) (F' := fun r w => d (r, w)) (x₀ := r₀)
    (bound := fun _ => C) (s := ball r₀ (a / 2)) (ball_mem_nhds _ (by linarith))
    (hSr.mono fun r hr => (hslice r hr).aestronglyMeasurable)
    ((hslice r₀ hr₀).continuousOn.integrableOn_compact hK)
    ((hdslice r₀ hr₀).aestronglyMeasurable)
    (hmem.mono fun w hw r hr => hC (r, w) ⟨ball_subset_closedBall hr, hw⟩)
    (integrable_const C)
    (Eventually.of_forall fun w r hr => hder r (hclosed (ball_subset_closedBall hr)) w)
  have hd0 (w : ℂ) (hw : w ∉ K) : d (r₀, w) = 0 := by
    have hz : (fun r => f r w) =ᶠ[𝓝 r₀] (fun _ => (0 : ℝ)) :=
      hSr.mono fun r hr => hzero r w hr hw
    exact (hder r₀ hr₀ w).unique ((hasDerivAt_const r₀ (0 : ℝ)).congr_of_eventuallyEq hz)
  have hfull : (fun r => ∫ w : ℂ, f r w) =ᶠ[𝓝 r₀] (fun r => ∫ w, f r w ∂μ) := by
    filter_upwards [hS.mem_nhds hr₀] with r hr
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => hzero r w hr hw)).symm
  have hdint : (∫ w, d (r₀, w) ∂μ) = ∫ w : ℂ, deriv (fun r => f r w) r₀ := by
    change (∫ w in K, d (r₀, w)) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hd0]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => (hder r₀ hr₀ w).deriv.symm
  rw [hdint] at hint
  exact hint.2.congr_of_eventuallyEq hfull




theorem hasDerivAt_planeIntegral_of_compact_support_rclike
    {𝕜 : Type*} [RCLike 𝕜] {f f' : 𝕜 → ℂ → 𝕜} {S : Set 𝕜} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K)
    (hzero : ∀ p, ∀ w, p ∈ S → w ∉ K → f p w = 0)
    (hf : ContinuousOn (fun q : 𝕜 × ℂ => f q.1 q.2) (S ×ˢ univ))
    (hf' : ContinuousOn (fun q : 𝕜 × ℂ => f' q.1 q.2) (S ×ˢ univ))
    (hder : ∀ p, p ∈ S → ∀ w, HasDerivAt (fun q => f q w) (f' p w) p)
    {p₀ : 𝕜} (hp₀ : p₀ ∈ S) :
    HasDerivAt (fun p => ∫ w : ℂ, f p w) (∫ w : ℂ, f' p₀ w) p₀ := by
  have hslice (p : 𝕜) (hp : p ∈ S) : Continuous (f p) := by
    rw [← continuousOn_univ]
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hp, mem_univ _⟩)
  have hdslice (p : 𝕜) (hp : p ∈ S) : Continuous (f' p) := by
    rw [← continuousOn_univ]
    exact hf'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hp, mem_univ _⟩)
  obtain ⟨a, ha, haS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hp₀)
  have hclosed : closedBall p₀ (a / 2) ⊆ S :=
    (closedBall_subset_ball (by linarith : a / 2 < a)).trans haS
  have hprod : closedBall p₀ (a / 2) ×ˢ K ⊆ S ×ˢ (univ : Set ℂ) :=
    fun _ hp => ⟨hclosed hp.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ (a / 2)).prod hK).exists_bound_of_continuousOn
    (hf'.mono hprod)
  let μ : Measure ℂ := volume.restrict K
  have : IsFiniteMeasure μ := ⟨by
    change (volume.restrict K) univ < ⊤
    simpa using hK.measure_lt_top (μ := volume)⟩
  have hmem : ∀ᵐ w ∂μ, w ∈ K := ae_restrict_mem hK.measurableSet
  have hSp : ∀ᶠ p in nhds p₀, p ∈ S := hS.mem_nhds hp₀
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := f) (F' := f') (x₀ := p₀)
    (bound := fun _ => C) (s := ball p₀ (a / 2)) (ball_mem_nhds _ (by linarith))
    (hSp.mono fun p hp => (hslice p hp).aestronglyMeasurable)
    ((hslice p₀ hp₀).continuousOn.integrableOn_compact hK)
    ((hdslice p₀ hp₀).aestronglyMeasurable)
    (hmem.mono fun w hw p hp => hC (p, w) ⟨ball_subset_closedBall hp, hw⟩)
    (integrable_const C)
    (Eventually.of_forall fun w p hp => hder p (hclosed (ball_subset_closedBall hp)) w)
  have hd0 (w : ℂ) (hw : w ∉ K) : f' p₀ w = 0 := by
    have hz : Filter.EventuallyEq (nhds p₀) (fun p => f p w) (fun _ => (0 : 𝕜)) :=
      hSp.mono fun p hp => hzero p w hp hw
    exact (hder p₀ hp₀ w).unique ((hasDerivAt_const p₀ (0 : 𝕜)).congr_of_eventuallyEq hz)
  have hfull : Filter.EventuallyEq (nhds p₀) (fun p => ∫ w : ℂ, f p w)
      (fun p => ∫ w, f p w ∂μ) := by
    filter_upwards [hS.mem_nhds hp₀] with p hp
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => hzero p w hp hw)).symm
  have hdint : (∫ w, f' p₀ w ∂μ) = ∫ w : ℂ, f' p₀ w := by
    change (∫ w in K, f' p₀ w) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hd0]
  rw [hdint] at hint
  exact hint.2.congr_of_eventuallyEq hfull

end DifferentialGeometry.Analysis
