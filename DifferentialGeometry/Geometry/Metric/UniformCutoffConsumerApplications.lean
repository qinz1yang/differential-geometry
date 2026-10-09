import DifferentialGeometry.Geometry.Metric.UniformCutoffConsumer

/-!
# Consumers of CFS25

* `cfs25_parameter_choice_identity_modulus`: the numerical clause is non-vacuous (identity
  smoothing modulus): stage targets with preceding errors `≤ 4κ/5` and `≤ 3Σ_j/10` exist.
* `cfs25_scalar_zero_marker`: the (ZL) route for a scalar marker `⟪e₀, ·⟫`: an originally zero
  marker stays zero through every adjustment stage, which gives (ZM) `|⟪e₀, g_k p⟫| ≤ r/32`.
* `cfs25_edge_tube_mem`: on the closed support of the edge cutoff, the perturbed point lies in the
  projected tube around the original threshold-`7Δ` centres (the CFS18 input set).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff BigOperators InnerProductSpace

namespace GC.MetricGeometry

/-- The CFS25 numerical clause with the identity smoothing modulus. -/
theorem cfs25_parameter_choice_identity_modulus {cadj L₀ Ω P : ℝ} (N : ℕ) (C : Fin 3 → ℝ)
    (hcadj : 0 < cadj) (hP1 : 1 ≤ P) (hL : 0 ≤ L₀) (hΩ : 1 ≤ Ω) (hC : ∀ j, 0 < C j) :
    ∃ c S : Fin 3 → ℝ,
      (c 0 ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 ∧ c 0 ≤ 3 * S 1 / 10) ∧
      (c 1 ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 ∧ c 1 ≤ 3 * S 2 / 10) ∧
      ∀ j, 0 < c j ∧ 0 < S j := by
  obtain ⟨c, Γ, S, h0, h1, hj⟩ := cfs25_parameter_choice (fun _ Γ => Γ) (fun _ _ h => h)
    (fun _ => Filter.tendsto_id.mono_left nhdsWithin_le_nhds) N C hcadj hP1 hL hΩ hC
  exact ⟨c, S, h0, h1, fun j => ⟨(hj j).1, (hj j).2.2.2.1⟩⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The (ZL) route of CFS25 for the scalar marker `⟪e₀, ·⟫`. -/
theorem cfs25_scalar_zero_marker (e₀ : H) (Q : ℕ → Submodule ℝ H)
    [∀ k, (Q k).HasOrthogonalProjection] [∀ k, (Q k)ᗮ.HasOrthogonalProjection]
    (Pm : ℕ → H → H) (hPm : ∀ k z, Pm k z ∈ Q k) (ψ : ℕ → H → ℝ) {X : Type*} (g : ℕ → X → H)
    (hg : ∀ k p, g (k + 1) p = DifferentialGeometry.Analysis.adjustmentMap (Q k) (Pm k) (ψ k)
      (g k p))
    (hZL : ∀ k p, (ℝ ∙ e₀).starProjection (g k p) = 0 →
      ((ℝ ∙ e₀) ≤ Q k ∧ (ψ k (g k p) ≠ 0 →
        (ℝ ∙ e₀).starProjection (Pm k ((Q k).starProjection (g k p))) = 0)) ∨
        (ℝ ∙ e₀) ≤ (Q k)ᗮ)
    {r : ℝ} (hr : 0 ≤ r) (p : X) (h0 : ⟪e₀, g 0 p⟫_ℝ = 0) :
    ∀ k, ⟪e₀, g k p⟫_ℝ = 0 ∧ |⟪e₀, g k p⟫_ℝ| ≤ r / 32 := by
  have hJ : ∀ z, innerSL ℝ e₀ z = innerSL ℝ e₀ ((ℝ ∙ e₀).starProjection z) := fun z => by
    rw [innerSL_apply_apply, innerSL_apply_apply,
      ← Submodule.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff).mpr (Submodule.mem_span_singleton_self e₀)]
  have hV0 : (ℝ ∙ e₀).starProjection (g 0 p) = 0 := by
    rw [Submodule.starProjection_singleton, h0, zero_div, zero_smul]
  intro k
  obtain ⟨hk, hbound⟩ := cfs25_zero_marker_of_locality (ℝ ∙ e₀) Q Pm hPm ψ g hg hZL
    (innerSL ℝ e₀) hJ hr p hV0 k
  rw [innerSL_apply_apply] at hbound
  refine ⟨?_, hbound⟩
  rw [← innerSL_apply_apply, hJ, hk, map_zero]

variable {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  {Hq : Type*} [NormedAddCommGroup Hq] [NormedSpace ℝ Hq]

/-- On the closed support of the CFS23 edge cutoff, the perturbed point lies in the projected
tube around the original threshold-`7Δ` centres with radii `σ ρ(sel p)` (the set `U` of CFS18). -/
theorem cfs25_edge_tube_mem {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1)
    (hx2 : ‖x2‖ ≤ 1) {X : Type*} {Δ : ℝ} (hΔ : 1 ≤ Δ) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H) (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (π : H →L[ℝ] Hq) (hπ : ‖π‖ ≤ 1) (m : I → Hq →L[ℝ] ℝ) (hm : ∀ i z, m i (π z) = v i z)
    (sel : X → X) (hsel : ∀ p, π (F (sel p)) = π (F p)) {σ e : ℝ} (hσ : 0 < σ)
    (he4 : e ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (he3 : e ≤ 3 * σ / 10)
    (herr : ∀ p, ‖f p - F p‖ ≤ e * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (h : ℝ → ℝ) (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1)
    (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      ‖x1 (F p)‖ = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ)) (p : X)
    (hp : f p ∈ tsupport (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2)) :
    f p ∈ cfsProjectedTube π F {q | ∃ i, q ∈ U i ∧ ‖η i q‖ < 7 * Δ ∧ t q < 7 * Δ}
      (fun q => σ * ρ (sel q)) := by
  obtain ⟨-, -, -, -, hloc⟩ := cfs25_edge_consumer hχ hχ0 hχ1 hχI hχmono hP1 hP N u v xρ x1 x2
    hu hv hxρ hx1 hx2 hΔ R hR ρ hρ U η ζ hζI F f hζU hblock hcount hcomp π hπ m hm sel hsel hσ
    he4 he3 herr hZM t h hhI hhg hxρF hedgeblock hedge
  obtain ⟨hcore, -, -, hd, -, -⟩ := hloc p hp
  have hr : 0 < σ * ρ (sel p) := mul_pos hσ (hρ (sel p))
  refine ⟨p, hcore, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

end GC.MetricGeometry
