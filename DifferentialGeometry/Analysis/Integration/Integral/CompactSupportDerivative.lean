import DifferentialGeometry.Analysis.Integration.Integral.CompactSupportParametric
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace DifferentialGeometry.Analysis

theorem hasDerivAt_integral_of_compact_support
    {𝕜 X F : Type*} [RCLike 𝕜] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [T2Space X] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {f f' : 𝕜 → X → F} {S : Set 𝕜} {K : Set X}
    (hS : IsOpen S) (hK : IsCompact K)
    (hzero : ∀ p, ∀ w, p ∈ S → w ∉ K → f p w = 0)
    (hf : ContinuousOn (fun q : 𝕜 × X => f q.1 q.2) (S ×ˢ univ))
    (hf' : ContinuousOn (fun q : 𝕜 × X => f' q.1 q.2) (S ×ˢ univ))
    (hder : ∀ p, p ∈ S → ∀ w, HasDerivAt (fun q => f q w) (f' p w) p)
    {p₀ : 𝕜} (hp₀ : p₀ ∈ S) :
    HasDerivAt (fun p => ∫ w : X, f p w ∂μ) (∫ w : X, f' p₀ w ∂μ) p₀ := by
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
  have hprod : closedBall p₀ (a / 2) ×ˢ K ⊆ S ×ˢ (univ : Set X) :=
    fun _ hp => ⟨hclosed hp.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ (a / 2)).prod hK).exists_bound_of_continuousOn
    (hf'.mono hprod)
  let ν : Measure X := μ.restrict K
  have : IsFiniteMeasure ν := ⟨by
    change (μ.restrict K) univ < ⊤
    simpa using hK.measure_lt_top (μ := μ)⟩
  have hmem : ∀ᵐ w ∂ν, w ∈ K := ae_restrict_mem hK.measurableSet
  have hSp : ∀ᶠ p in nhds p₀, p ∈ S := hS.mem_nhds hp₀
  have hcs (p : 𝕜) (hp : p ∈ S) : HasCompactSupport (f p) :=
    HasCompactSupport.intro hK (fun w hw => hzero p w hp hw)
  have hd0 (p : 𝕜) (hp : p ∈ S) (w : X) (hw : w ∉ K) : f' p w = 0 := by
    have hSp' : ∀ᶠ q in 𝓝 p, q ∈ S := hS.mem_nhds hp
    have hz : (fun q => f q w) =ᶠ[𝓝 p] (fun _ => (0 : F)) :=
      hSp'.mono fun q hq => hzero q w hq hw
    exact (hder p hp w).unique ((hasDerivAt_const p (0 : F)).congr_of_eventuallyEq hz)
  have hcd (p : 𝕜) (hp : p ∈ S) : HasCompactSupport (f' p) :=
    HasCompactSupport.intro hK (fun w hw => hd0 p hp w hw)
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (F := f) (F' := f') (x₀ := p₀)
    (bound := fun _ => C) (s := ball p₀ (a / 2)) (ball_mem_nhds _ (by linarith))
    (hSp.mono fun p hp => ((hslice p hp).stronglyMeasurable_of_hasCompactSupport (hcs p hp)).aestronglyMeasurable)
    ((hslice p₀ hp₀).continuousOn.integrableOn_compact hK)
    (((hdslice p₀ hp₀).stronglyMeasurable_of_hasCompactSupport (hcd p₀ hp₀)).aestronglyMeasurable)
    (hmem.mono fun w hw p hp => hC (p, w) ⟨ball_subset_closedBall hp, hw⟩)
    (integrable_const C)
    (Eventually.of_forall fun w p hp => hder p (hclosed (ball_subset_closedBall hp)) w)
  have hfull : Filter.EventuallyEq (nhds p₀) (fun p => ∫ w : X, f p w ∂μ)
      (fun p => ∫ w, f p w ∂ν) := by
    filter_upwards [hS.mem_nhds hp₀] with p hp
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => hzero p w hp hw)).symm
  have hdint : (∫ w, f' p₀ w ∂ν) = ∫ w : X, f' p₀ w ∂μ := by
    change (∫ w in K, f' p₀ w ∂μ) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hd0 p₀ hp₀)]
  rw [hdint] at hint
  exact hint.2.congr_of_eventuallyEq hfull


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
  have h := hasDerivAt_integral_of_compact_support (μ := volume) hS hK hzero
    hf.continuousOn hd hder hr₀
  have he : (fun w => d (r₀, w)) = fun w => deriv (fun r => f r w) r₀ :=
    funext (fun w => (hder r₀ hr₀ w).deriv.symm)
  simpa only [he] using h

theorem hasDerivAt_planeIntegral_of_compact_support_rclike
    {𝕜 : Type*} [RCLike 𝕜] {f f' : 𝕜 → ℂ → 𝕜} {S : Set 𝕜} {K : Set ℂ}
    (hS : IsOpen S) (hK : IsCompact K)
    (hzero : ∀ p, ∀ w, p ∈ S → w ∉ K → f p w = 0)
    (hf : ContinuousOn (fun q : 𝕜 × ℂ => f q.1 q.2) (S ×ˢ univ))
    (hf' : ContinuousOn (fun q : 𝕜 × ℂ => f' q.1 q.2) (S ×ˢ univ))
    (hder : ∀ p, p ∈ S → ∀ w, HasDerivAt (fun q => f q w) (f' p w) p)
    {p₀ : 𝕜} (hp₀ : p₀ ∈ S) :
    HasDerivAt (fun p => ∫ w : ℂ, f p w) (∫ w : ℂ, f' p₀ w) p₀ :=
  hasDerivAt_integral_of_compact_support (μ := volume) hS hK hzero hf hf' hder hp₀

end DifferentialGeometry.Analysis
