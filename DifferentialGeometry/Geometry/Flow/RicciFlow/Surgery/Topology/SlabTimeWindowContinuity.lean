import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCapBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabPointPicking

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private theorem exists_forall_abs_sub_lt_of_continuousOn {f : ℝ × P.Carrier → ℝ}
    (hf : ContinuousOn f (Ico a s ×ˢ univ)) {t₀ ζ : ℝ} (ht₀ : t₀ ∈ Ico a s) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico a s, |t - t₀| < δ → ∀ x : P.Carrier,
      |f (t, x) - f (t₀, x)| < ζ := by
  let τ₀ : Ico a s := ⟨t₀, ht₀⟩
  let g : Ico a s × P.Carrier → ℝ := fun z => f (z.1.1, z.2)
  have hg : Continuous g :=
    hf.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun z => ⟨z.1.2, mem_univ _⟩
  have hP : ∀ y ∈ (univ : Set P.Carrier),
      ∀ᶠ z : Ico a s × P.Carrier in 𝓝 (τ₀, y), |g (z.1, z.2) - g (τ₀, z.2)| < ζ := by
    intro y _
    have h1 : ∀ᶠ z : Ico a s × P.Carrier in 𝓝 (τ₀, y), g z ∈ Metric.ball (g (τ₀, y)) (ζ / 2) :=
      hg.continuousAt.eventually (Metric.ball_mem_nhds (g (τ₀, y)) (half_pos hζ))
    have hc : Continuous fun z : Ico a s × P.Carrier => g (τ₀, z.2) :=
      hg.comp ((continuous_const : Continuous fun _ : Ico a s × P.Carrier => τ₀).prodMk
        continuous_snd)
    have h2 : ∀ᶠ z : Ico a s × P.Carrier in 𝓝 (τ₀, y),
        g (τ₀, z.2) ∈ Metric.ball (g (τ₀, y)) (ζ / 2) :=
      (hc.continuousAt (x := (τ₀, y))).eventually (Metric.ball_mem_nhds _ (half_pos hζ))
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [Metric.mem_ball, Real.dist_eq] at hz1 hz2
    rw [abs_sub_lt_iff] at hz1 hz2 ⊢
    constructor <;> linarith
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff.mp (isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun t x => |g (t, x) - g (τ₀, x)| < ζ) hP)
  refine ⟨δ, hδ, fun t ht htd x => ?_⟩
  exact hball (y := ⟨t, ht⟩) (by rw [Subtype.dist_eq, Real.dist_eq]; exact htd) x (mem_univ x)

theorem exists_forall_Icc_scalar_riemannNorm_metric_close {t₀ ζ : ℝ} (ht₀ : t₀ ∈ Ico a s)
    (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ t₀ + δ < s ∧
      ∀ t ∈ Icc (max a (t₀ - δ)) (t₀ + δ), ∀ t' ∈ Icc (max a (t₀ - δ)) (t₀ + δ),
        ∀ x : P.Carrier,
          |G.flow.scalar t x - G.flow.scalar t' x| ≤ ζ ∧
          |G.riemannNorm t x - G.riemannNorm t' x| ≤ ζ ∧
          ∀ v : TangentSpace ThreeModel x,
            (G.flow.base.metric t).inner x v v ≤ (1 + ζ) * (G.flow.base.metric t').inner x v v := by
  have hsc : ContinuousOn (fun z : ℝ × P.Carrier => G.flow.scalar z.1 z.2) (Ico a s ×ˢ univ) :=
    G.equation.scalarCont
  have hrn : ContinuousOn (fun z : ℝ × P.Carrier => G.riemannNorm z.1 z.2) (Ico a s ×ˢ univ) :=
    G.continuousOn_riemannNorm
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_forall_abs_sub_lt_of_continuousOn hsc ht₀ (half_pos hζ)
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_forall_abs_sub_lt_of_continuousOn hrn ht₀ (half_pos hζ)
  have hb : (t₀ + s) / 2 < s := by linarith [ht₀.2]
  obtain ⟨K, hK⟩ := G.exists_forall_Icc_riemannNorm_le hb
  set K' : ℝ := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set L : ℝ := Real.log (1 + ζ) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hs : 0 < s - t₀ := sub_pos.mpr ht₀.2
  set δ : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) (min ((s - t₀) / 2) (L / (36 * (K' + 1))))
    with hδdef
  have hδa : δ ≤ δ₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδb : δ ≤ δ₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδc : δ ≤ (s - t₀) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδd : δ ≤ L / (36 * (K' + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hδ : 0 < δ := lt_min (lt_min (half_pos hδ₁) (half_pos hδ₂))
    (lt_min (half_pos hs) (div_pos hL (by positivity)))
  refine ⟨δ, hδ, by linarith, fun t ht t' ht' x => ?_⟩
  have hmem : ∀ r ∈ Icc (max a (t₀ - δ)) (t₀ + δ), r ∈ Ico a s ∧ |r - t₀| < δ₁ ∧
      |r - t₀| < δ₂ ∧ r ∈ Icc a ((t₀ + s) / 2) := by
    intro r hr
    have hra : a ≤ r := (le_max_left _ _).trans hr.1
    have hrl : t₀ - δ ≤ r := (le_max_right _ _).trans hr.1
    have habs : |r - t₀| ≤ δ := abs_sub_le_iff.mpr ⟨by linarith [hr.2], by linarith⟩
    exact ⟨⟨hra, by linarith [hr.2]⟩, by linarith, by linarith, ⟨hra, by linarith [hr.2]⟩⟩
  obtain ⟨hti, ht1, ht2, htK⟩ := hmem t ht
  obtain ⟨hti', ht1', ht2', htK'⟩ := hmem t' ht'
  refine ⟨?_, ?_, fun v => ?_⟩
  · have e := h₁ t hti ht1 x
    have e' := h₁ t' hti' ht1' x
    simp only at e e'
    rw [abs_sub_lt_iff] at e e'
    rw [abs_le]
    constructor <;> linarith
  · have e := h₂ t hti ht2 x
    have e' := h₂ t' hti' ht2' x
    simp only at e e'
    rw [abs_sub_lt_iff] at e e'
    rw [abs_le]
    constructor <;> linarith
  · have hRm : ∀ r ∈ Icc (max a (t₀ - δ)) (t₀ + δ),
        normSq0S (G.flow.base.metric r) x 4 (G.flow.base.rm04 r x) ≤ K' ^ 2 := by
      intro r hr
      have hle : G.riemannNorm r x ≤ K' := (hK r (hmem r hr).2.2.2 x).trans (le_max_left _ _)
      have hsq := Real.sq_sqrt (normSq0S_nonneg (G.flow.base.metric r) x 4
        (G.flow.base.rm04 r x))
      have hn : 0 ≤ G.riemannNorm r x := Real.sqrt_nonneg _
      rw [riemannNorm] at hle hn
      nlinarith
    have hcmp := (metric_inner_exp_bounds_of_curvature_bound G.flow G.equation
      (a := max a (t₀ - δ)) (b := t₀ + δ) (C := K' ^ 2)
      (fun r hr => (hmem r hr).1)
      (fun r hr => ⟨(le_max_left _ _).trans_lt hr.1, by linarith [hr.2]⟩) x hRm ht ht' v).2
    have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
    rw [hdim, Real.sqrt_sq hK'0] at hcmp
    have habs : |t - t'| ≤ 2 * δ := by
      have h1 := (le_max_right a (t₀ - δ)).trans ht.1
      have h2 := (le_max_right a (t₀ - δ)).trans ht'.1
      exact abs_sub_le_iff.mpr ⟨by linarith [ht.2], by linarith [ht'.2]⟩
    have hKδ : 36 * (K' + 1) * δ ≤ L := by
      rw [le_div_iff₀ (by positivity)] at hδd
      linarith
    have hexp : 2 * (3 : ℝ) ^ 2 * K' * |t - t'| ≤ L := by
      have := mul_le_mul_of_nonneg_left habs (by positivity : (0 : ℝ) ≤ 18 * K')
      nlinarith
    have hL1 : Real.exp L = 1 + ζ := Real.exp_log (by linarith)
    calc (G.flow.base.metric t).inner x v v
        ≤ Real.exp (2 * (3 : ℝ) ^ 2 * K' * |t - t'|) * (G.flow.base.metric t').inner x v v :=
          hcmp
      _ ≤ Real.exp L * (G.flow.base.metric t').inner x v v :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
            (metric_inner_self_nonneg (G.flow.base.metric t') x v)
      _ = (1 + ζ) * (G.flow.base.metric t').inner x v v := by rw [hL1]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
