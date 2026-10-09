import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeLifts

/-!
# LFR43 for every border lift

Blueprint 207A, LFR43 (`lem:collapse-strong-border-lift`, A:28535–28612): "For EVERY `|t| ≤ 12Δ`,
choose an actual `F`-lift `q` of `(t,0)` with error `< 2e`. Then `d_p(p,q) < 13Δ`, and `q` has strong
`(b_E,s)` edge maps at its OWN scale". The accepted `exists_strong_edge_interval_lift` and
`exists_strong_edge_ray_lift` produce one such lift. Here the conclusion is proved for EVERY actual
lift: every point `a` of the tested ball `B(p, e⁻¹)` (AC49's open-ball convention, where coverage
witnesses live) whose image is within `2e` of `(t, 0)`.

The ambient manifold structure of the row is not used: the statements hold on any metric space
with a positive `Λ`-Lipschitz scale (a strengthening).
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

/-- The radius, scale and model-height estimates at an arbitrary actual lift of `(t, z)`, `z` the
model endpoint. -/
theorem endpoint_lift_estimates_of_mem_ball {X : Type*} [MetricSpace X]
    {p : X} {S : Set ℝ} {o : S} {Δ e θ t : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (heΔ : e ≤ 1 / (1000 * Δ)) (V : X → S)
    (hcompat : ∀ x ∈ ball p (1000 * Δ), dist (V x) (H.toFun x).snd < θ)
    (z : S) (hz : z.val = 0) (ho : dist z o ≤ Δ / 2) (ht : |t| ≤ 12 * Δ)
    {a : X} (ha : a ∈ ball p e⁻¹) (hlift : dist (H.toFun a) (WithLp.toLp 2 (t, z)) < 2 * e) :
    dist a p < |t| + dist z o + 3 * e ∧ dist a p < 13 * Δ ∧
      (ρ a)⁻¹ ∈ Icc (1 / 2 : ℝ) 2 ∧ (V a).val ≤ 2 * e + θ := by
  have he := H.error_pos
  have hΔpos : 0 < Δ := by linarith
  have hprod : e * (1000 * Δ) ≤ 1 := (le_div_iff₀ (by positivity)).mp heΔ
  have he1 : e ≤ 1 / 1000 := by nlinarith only [hprod, hΔ, he]
  have hradius : dist (WithLp.toLp 2 (t, z)) (WithLp.toLp 2 ((0 : ℝ), o)) ≤ |t| + dist z o := by
    have htri := dist_triangle (WithLp.toLp 2 (t, z)) (WithLp.toLp 2 ((0 : ℝ), z))
      (WithLp.toLp 2 ((0 : ℝ), o))
    have h1 := (WithLp.isometry_prodMk_right (E := ℝ) z).dist_eq t 0
    have h2 := (WithLp.isometry_prodMk_left (Y := S) (0 : ℝ)).dist_eq z o
    simpa only [h1, h2, Real.dist_eq, sub_zero] using htri
  have hrad := (abs_le.mp (H.radial_error a ha)).1
  have htri := dist_triangle (H.toFun a) (WithLp.toLp 2 (t, z)) (WithLp.toLp 2 ((0 : ℝ), o))
  have hdist : dist a p < |t| + dist z o + 3 * e := by
    linarith only [hrad, htri, hlift, hradius]
  have h13 : dist a p < 13 * Δ := hdist.trans_le (by linarith only [ht, ho, he1, hΔ])
  have hΛΔ : (Λ : ℝ) * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hρbound : |ρ a - 1| ≤ (Λ : ℝ) * (13 * Δ) := by
    have hh := hρ.dist_le_mul a p
    rw [Real.dist_eq, hρp] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left h13.le Λ.coe_nonneg)
  have hlo : 1 / 2 < ρ a := by nlinarith only [hΛΔ, (abs_le.mp hρbound).1]
  have hhi : ρ a < 2 := by nlinarith only [hΛΔ, (abs_le.mp hρbound).2]
  have hcinv : (ρ a)⁻¹ ∈ Icc (1 / 2 : ℝ) 2 := by
    rw [← one_div]
    constructor
    · exact (le_div_iff₀ (hρpos a)).mpr (by linarith only [hhi])
    · exact (div_le_iff₀ (hρpos a)).mpr (by linarith only [hlo])
  have hca := hcompat a (h13.trans (by linarith only [hΔpos]))
  have hfactor := WithLp.dist_snd_le (H.toFun a) (WithLp.toLp 2 (t, z))
  change dist (H.toFun a).snd z ≤ _ at hfactor
  have htri' := dist_triangle (V a) (H.toFun a).snd z
  have hv : (V a).val ≤ dist (V a) z := by
    rw [Subtype.dist_eq, Real.dist_eq, hz, sub_zero]
    exact le_abs_self _
  exact ⟨hdist, h13, hcinv, by linarith only [hv, htri', hca, hfactor, hlift]⟩

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {Δ β βE s η e θ t : ℝ} {Λ : NNReal} {ρ : X → ℝ}

/-- **LFR43**, finite interval model: EVERY actual lift `a` of `(t, 0)`, `|t| ≤ 12Δ`, is within
`|t| + o + 3e < 13Δ` of `p` and is a strong edge point at its own scale. -/
theorem isEdgePoint_of_every_interval_lift {C : ℝ} {o : Icc (0 : ℝ) C}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o η)
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hC : 500 * Δ < C) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hηs : η ≤ s / 1000) (hηΔ : η ≤ 1 / (100000 * Δ))
    (he : e ≤ s / 1000) (heΔ : e ≤ 1 / (1000 * Δ)) (hθ : θ ≤ s / 1000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ)) (ho : o.val ≤ Δ / 2)
    (hcompat : ∀ x ∈ ball p (1000 * Δ),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ)
    (ht : |t| ≤ 12 * Δ) {a : X} (ha : a ∈ ball p e⁻¹)
    (hlift : dist (H.toFun a)
      (WithLp.toLp 2 (t, (⟨0, le_rfl, o.property.1.trans o.property.2⟩ : Icc (0 : ℝ) C))) < 2 * e) :
    dist a p < |t| + o.val + 3 * e ∧ dist a p < 13 * Δ ∧
      (@isEdgePoint.{u, v} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) := by
  let z : Icc (0 : ℝ) C := ⟨0, le_rfl, o.property.1.trans o.property.2⟩
  have hzo : dist z o = o.val := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |0 - o.val| = o.val
    rw [zero_sub, abs_neg, abs_of_nonneg o.property.1]
  obtain ⟨hrad, h13, hc, hheight⟩ := endpoint_lift_estimates_of_mem_ball H hρ hρpos hρp
    hΔ hscale heΔ (fun x => G.toFun (F.toFun x).snd) hcompat z rfl (by rwa [hzo]) ht ha hlift
  refine ⟨by rwa [hzo] at hrad, h13, ?_⟩
  exact isEdgePoint_of_marked_interval_model F G hΔ hC hβE hβsmall hβdomain hs hssmall
    hηs hηΔ hc h13.le ho he hθ hheight

/-- **LFR43**, ray model: EVERY actual lift `a` of `(t, 0)`, `|t| ≤ 12Δ`, is within
`|t| + o + 3e < 13Δ` of `p` and is a strong edge point at its own scale. -/
theorem isEdgePoint_of_every_ray_lift {o : Ici (0 : ℝ)}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o η)
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hηs : η ≤ s / 1000) (hηΔ : η ≤ 1 / (100000 * Δ))
    (he : e ≤ s / 1000) (heΔ : e ≤ 1 / (1000 * Δ)) (hθ : θ ≤ s / 1000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ)) (ho : o.val ≤ Δ / 2)
    (hcompat : ∀ x ∈ ball p (1000 * Δ),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ)
    (ht : |t| ≤ 12 * Δ) {a : X} (ha : a ∈ ball p e⁻¹)
    (hlift : dist (H.toFun a)
      (WithLp.toLp 2 (t, (⟨0, by norm_num⟩ : Ici (0 : ℝ)))) < 2 * e) :
    dist a p < |t| + o.val + 3 * e ∧ dist a p < 13 * Δ ∧
      (@isEdgePoint.{u, v} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) := by
  let z : Ici (0 : ℝ) := ⟨0, by norm_num⟩
  have hzo : dist z o = o.val := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |0 - o.val| = o.val
    rw [zero_sub, abs_neg, abs_of_nonneg o.property]
  obtain ⟨hrad, h13, hc, hheight⟩ := endpoint_lift_estimates_of_mem_ball H hρ hρpos hρp
    hΔ hscale heΔ (fun x => G.toFun (F.toFun x).snd) hcompat z rfl (by rwa [hzo]) ht ha hlift
  refine ⟨by rwa [hzo] at hrad, h13, ?_⟩
  exact isEdgePoint_of_ray_model F G hΔ hβE hβsmall hβdomain hs hssmall
    hηs hηΔ hc h13.le ho he hθ hheight

end GC.MetricGeometry
