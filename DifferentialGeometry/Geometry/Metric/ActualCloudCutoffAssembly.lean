import DifferentialGeometry.Geometry.Metric.ActualCloudCutoffSequence
import DifferentialGeometry.Analysis.Calculus.Cutoff.BufferedEdgeCutoff

/-! CFS31 (master207B, B:3783–3855): the full sequential cutoff construction WITHOUT a marker assumption.

Three stages `g 1 = Ψ₀ ∘ F`, `g 2 = Ψ₁ ∘ g 1`, `g 3 = Ψ₂ ∘ g 2` (FC32 adjustments) use, in this order,
* the source first cutoff `ψ₁` of the two-stratum family (`markerLocalitySourceCutoff`, at `f = F`),
* the buffered edge cutoff `ψ_e` of CFS23 (`cfsBufferedEdgeCutoff`, `cfs23_row`, lane C14-KA),
* the uniform one-axis slim cutoff `ψ_s` of CFS22 (`cfsUniformAxisCutoff`, `cfs22_row`).
The induction is sequential: stage one's localization comes from `ψ₁`'s closed support; CFS29/CFS30 (scalar
markers) then PROVE the zero-marker input (ZM) of CFS23 at `g 1`; CFS23's closed support localizes stage two;
CFS29/CFS30 prove (ZM) of CFS22 at `g 2`; CFS22's closed support localizes stage three; CFS30 gives (AZM) after
stage three. No later cutoff is used for an earlier marker bound. The (MB) choices of `c₁, c₂, c₃` and the tube
bounds `t₂ ≤ 3Σ₁/10`, `t₃ ≤ 3Σ₂/10` are hypotheses on the CFS20 budgets; the stage projections' small-marker
locality (`hnear`) is G4's binding of the actual CFS14 nearest maps. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

/-- CFS31 assembly: all three cutoffs have their support / plateau / derivative conclusions at the actual stage
inputs, the small markers vanish exactly at every stage, and (AZM) holds after stage three. -/
theorem actualCloud_cutoff_sequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {A X : Type*}
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1)
    (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ) {P : ℝ} (hP1 : 1 ≤ P)
    (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    -- the retained scalar markers on the original map (CFS26)
    (v : A → H →L[ℝ] ℝ) (hv : ∀ a, ‖v a‖ ≤ 1) (R : A → ℝ) (hR : ∀ a, 0 < R a)
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (ζ : A → X → ℝ) (hζI : ∀ a p, ζ a p ∈ Icc (0 : ℝ) 1)
    (F : X → H) (hvF : ∀ a p, v a (F p) = R a * ζ a p)
    (hcompA : ∀ a p, 0 < ζ a p → 3 / 4 * R a ≤ ρ p ∧ ρ p ≤ 5 / 4 * R a)
    -- the two-stratum family (source first cutoff)
    {I₁ : Type*} [Fintype I₁] {E₁ : I₁ → Type*} [∀ i, NormedAddCommGroup (E₁ i)]
    [∀ i, InnerProductSpace ℝ (E₁ i)] (ι₁ : I₁ → A) (u₁ : ∀ i, H →L[ℝ] E₁ i)
    (hu₁ : ∀ i, ‖u₁ i‖ ≤ 1) (U₁ : I₁ → Set X) (η₁ : ∀ i, X → E₁ i)
    (hζU₁ : ∀ i p, p ∉ U₁ i → ζ (ι₁ i) p = 0)
    (hu₁F : ∀ i p, u₁ i (F p) = (R (ι₁ i) * ζ (ι₁ i) p) • η₁ i p)
    (hcount₁ : ∀ p, (Finset.univ.filter fun i => 0 < ζ (ι₁ i) p).card ≤ N)
    (hplateau₁ : ∀ i p, p ∈ U₁ i → ‖η₁ i p‖ < 6 → ζ (ι₁ i) p = 1)
    -- the edge family (CFS23)
    {I₂ : Type*} [Fintype I₂] {E₂ : I₂ → Type*} [∀ i, NormedAddCommGroup (E₂ i)]
    [∀ i, InnerProductSpace ℝ (E₂ i)] {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (ι₂ : I₂ → A) (u₂ : ∀ i, H →L[ℝ] E₂ i) (hu₂ : ∀ i, ‖u₂ i‖ ≤ 1)
    (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1)
    (hx2 : ‖x2‖ ≤ 1) {Δ : ℝ} (hΔ : 1 ≤ Δ) (U₂ : I₂ → Set X) (η₂ : ∀ i, X → E₂ i)
    (hζU₂ : ∀ i p, p ∉ U₂ i → ζ (ι₂ i) p = 0)
    (hu₂F : ∀ i p, u₂ i (F p) = (R (ι₂ i) * ζ (ι₂ i) p) • η₂ i p)
    (hcount₂ : ∀ p, (Finset.univ.filter fun i => 0 < ζ (ι₂ i) p).card ≤ N)
    (hη₂ : ∀ i p, 0 < ζ (ι₂ i) p → ‖η₂ i p‖ ≤ 9 * Δ)
    (tE : X → ℝ) (h : ℝ → ℝ) (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1)
    (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U₂ i) →
      ‖x1 (F p)‖ = ρ p * tE p * (h (tE p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ (ι₂ i) p)) ∧
      x2 (F p) = ρ p * (h (tE p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ (ι₂ i) p)))
    (hedge : ∀ i p, p ∈ U₂ i → ‖η₂ i p‖ < 8 * Δ → ζ (ι₂ i) p = 1 - cfsRamp χ 8 9 (tE p / Δ))
    -- the slim family (CFS22)
    {I₃ : Type*} [Fintype I₃] {E₃ : I₃ → Type*} [∀ i, NormedAddCommGroup (E₃ i)]
    [∀ i, InnerProductSpace ℝ (E₃ i)] (ι₃ : I₃ → A) (u₃ : ∀ i, H →L[ℝ] E₃ i)
    (hu₃ : ∀ i, ‖u₃ i‖ ≤ 1) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (U₃ : I₃ → Set X) (η₃ : ∀ i, X → E₃ i)
    (hζU₃ : ∀ i p, p ∉ U₃ i → ζ (ι₃ i) p = 0)
    (hu₃F : ∀ i p, u₃ i (F p) = (R (ι₃ i) * ζ (ι₃ i) p) • η₃ i p)
    (hcount₃ : ∀ p, (Finset.univ.filter fun i => 0 < ζ (ι₃ i) p).card ≤ N)
    (hη₃ : ∀ i p, 0 < ζ (ι₃ i) p → ‖η₃ i p‖ ≤ 9 * ℓ)
    (hplateau₃ : ∀ i p, p ∈ U₃ i → ‖η₃ i p‖ < 6 * ℓ → ζ (ι₃ i) p = 1)
    -- the three stages
    (Q : ℕ → Submodule ℝ H) (Pst : ℕ → H → H) (hPst : ∀ k z, Pst k z ∈ Q k)
    (g : ℕ → X → H) (hg0 : ∀ q, g 0 q = F q)
    (hstep₀ : ∀ q, g 1 q = adjustmentMap (Q 0) (Pst 0)
      (markerLocalitySourceCutoff χ (fun i => R (ι₁ i)) u₁ (fun i => v (ι₁ i))) (g 0 q))
    (hstep₁ : ∀ q, g 2 q = adjustmentMap (Q 1) (Pst 1)
      (cfsBufferedEdgeCutoff χ Δ (fun i => R (ι₂ i)) u₂ (fun i => v (ι₂ i)) xρ x1 x2) (g 1 q))
    (hstep₂ : ∀ q, g 3 q = adjustmentMap (Q 2) (Pst 2)
      (cfsUniformAxisCutoff χ ℓ (fun i => R (ι₃ i)) u₃ (fun i => v (ι₃ i))) (g 2 q))
    (hretained : ∀ k < 3, ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q k ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ (Q k)ᗮ)
    (S : ℕ → Set H) (select : ℕ → H → X) (σ : ℕ → ℝ)
    (hsupport : ∀ k < 3, ∀ a q, 0 < v a ((Q k).starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hfullS : ∀ k < 3, ∀ q, (Q k).starProjection (F q) ∈ S k →
      ∃ a, v a ((Q k).starProjection (F q)) = R a)
    (hselect : ∀ k < 3, ∀ x ∈ S k, (Q k).starProjection (F (select k x)) = x)
    (hσ : ∀ k < 3, 0 < σ k)
    (hnear : ∀ k < 3, ∀ x ∈ S k, ∀ z ∈ ball x (σ k * ρ (select k x)), ∀ q,
      (Q k).starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (Pst k z) = 0)
    (hS₀ : ∀ q, (∃ i, q ∈ U₁ i ∧ ‖η₁ i q‖ < 7) → (Q 0).starProjection (F q) ∈ S 0)
    (hS₁ : ∀ q, (∃ i, q ∈ U₂ i ∧ ‖η₂ i q‖ < 7 * Δ ∧ tE q < 7 * Δ) →
      (Q 1).starProjection (F q) ∈ S 1)
    (hS₂ : ∀ q, (∃ i, q ∈ U₃ i ∧ ‖η₃ i q‖ < 7 * ℓ) → (Q 2).starProjection (F q) ∈ S 2)
    -- CFS20 cumulative errors and the (MB) choices
    {c₁ c₂ c₃ t₂ t₃ : ℝ} (hc₁0 : 0 ≤ c₁) (hc₂0 : 0 ≤ c₂) (hc₃0 : 0 ≤ c₃)
    (hc₁ : c₁ ≤ min t₂ (min (4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (1 / 512)))
    (hc₂ : c₂ ≤ min t₃ (min (4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (1 / 512)))
    (hc₃ : c₃ ≤ 1 / 512) (ht₂ : t₂ ≤ 3 * σ 1 / 10) (ht₃ : t₃ ≤ 3 * σ 2 / 10)
    (hcum₁ : ∀ q, ‖g 1 q - F q‖ ≤ c₁ * ρ q) (hcum₂ : ∀ q, ‖g 2 q - F q‖ ≤ c₂ * ρ q)
    (hcum₃ : ∀ q, ‖g 3 q - F q‖ ≤ c₃ * ρ q) :
    -- stage one: the source first cutoff at the original map
    (ContDiff ℝ ∞ (markerLocalitySourceCutoff χ (fun i => R (ι₁ i)) u₁ (fun i => v (ι₁ i))) ∧
      (∀ p, (∃ i, p ∈ U₁ i ∧ ‖η₁ i p‖ < 6) →
        markerLocalitySourceCutoff χ (fun i => R (ι₁ i)) u₁ (fun i => v (ι₁ i)) (F p) = 1) ∧
      (∀ p, F p ∈ tsupport (markerLocalitySourceCutoff χ (fun i => R (ι₁ i)) u₁ (fun i => v (ι₁ i))) →
        ∃ i, p ∈ U₁ i ∧ ‖η₁ i p‖ < 7) ∧
      (∀ p, ‖fderiv ℝ (markerLocalitySourceCutoff χ (fun i => R (ι₁ i)) u₁ (fun i => v (ι₁ i)))
        (F p)‖ ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p)) ∧
    -- stage two: the edge cutoff at the stage-one output (ZM proved)
    (ContDiffOn ℝ ∞ (cfsBufferedEdgeCutoff χ Δ (fun i => R (ι₂ i)) u₂ (fun i => v (ι₂ i)) xρ x1 x2)
        {z | 0 < xρ z} ∧
      (∀ p, (∃ i, p ∈ U₂ i ∧ ‖η₂ i p‖ < 6 * Δ ∧ tE p < 6 * Δ) →
        cfsBufferedEdgeCutoff χ Δ (fun i => R (ι₂ i)) u₂ (fun i => v (ι₂ i)) xρ x1 x2 (g 1 p) = 1) ∧
      (∀ p, g 1 p ∈ tsupport
          (cfsBufferedEdgeCutoff χ Δ (fun i => R (ι₂ i)) u₂ (fun i => v (ι₂ i)) xρ x1 x2) →
        ∃ i, p ∈ U₂ i ∧ ‖η₂ i p‖ < 7 * Δ ∧ tE p < 7 * Δ) ∧
      (∀ p, ∀ s ∈ Icc (0 : ℝ) 1, 0 < xρ ((1 - s) • F p + s • g 1 p) ∧
        ‖fderiv ℝ (cfsBufferedEdgeCutoff χ Δ (fun i => R (ι₂ i)) u₂ (fun i => v (ι₂ i)) xρ x1 x2)
          ((1 - s) • F p + s • g 1 p)‖ ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p)) ∧
    -- stage three: the slim cutoff at the stage-two output (ZM proved)
    (ContDiff ℝ ∞ (cfsUniformAxisCutoff χ ℓ (fun i => R (ι₃ i)) u₃ (fun i => v (ι₃ i))) ∧
      (∀ p, (∃ i, p ∈ U₃ i ∧ ‖η₃ i p‖ < 6 * ℓ) →
        cfsUniformAxisCutoff χ ℓ (fun i => R (ι₃ i)) u₃ (fun i => v (ι₃ i)) (g 2 p) = 1) ∧
      (∀ p, g 2 p ∈ tsupport (cfsUniformAxisCutoff χ ℓ (fun i => R (ι₃ i)) u₃ (fun i => v (ι₃ i))) →
        ∃ i, p ∈ U₃ i ∧ ‖η₃ i p‖ < 7 * ℓ) ∧
      (∀ p, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (cfsUniformAxisCutoff χ ℓ (fun i => R (ι₃ i)) u₃ (fun i => v (ι₃ i)))
          ((1 - s) • F p + s • g 2 p)‖ ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p)) ∧
    -- markers after every stage
    (∀ k ≤ 3, ∀ q a, R a < ρ q / 16 → v a (g k q) = 0) ∧
    ∀ a p, ζ a p = 0 → ∀ z ∈ segment ℝ (F p) (g 3 p), |v a z| ≤ R a / 32 := by
  -- the three cutoffs and per-stage constants
  set ψ₁ := markerLocalitySourceCutoff χ (fun i => R (ι₁ i)) u₁ (fun i => v (ι₁ i)) with hψ₁
  set ψe := cfsBufferedEdgeCutoff χ Δ (fun i => R (ι₂ i)) u₂ (fun i => v (ι₂ i)) xρ x1 x2 with hψe
  set ψs := cfsUniformAxisCutoff χ ℓ (fun i => R (ι₃ i)) u₃ (fun i => v (ι₃ i)) with hψs
  let ψ : ℕ → H → ℝ := fun k => if k = 0 then ψ₁ else if k = 1 then ψe else ψs
  have hψ0 : ψ 0 = ψ₁ := rfl
  have hψ1 : ψ 1 = ψe := rfl
  have hψ2 : ψ 2 = ψs := rfl
  let e : ℕ → ℝ := fun k => if k = 0 then 0 else if k = 1 then t₂ else t₃
  have he0 : e 0 = 0 := rfl
  have he1 : e 1 = t₂ := rfl
  have he2 : e 2 = t₃ := rfl
  have hζ0 : ∀ a p, 0 ≤ ζ a p := fun a p => (hζI a p).1
  have hstep : ∀ k < 3, ∀ q, g (k + 1) q = adjustmentMap (Q k) (Pst k) (ψ k) (g k q) := by
    intro k hk q
    interval_cases k
    · exact hstep₀ q
    · exact hstep₁ q
    · exact hstep₂ q
  have hfull : ∀ k < 3, ∀ q, (Q k).starProjection (F q) ∈ S k → ψ k (g k q) ≠ 0 →
      ∃ a, v a ((Q k).starProjection (F q)) = R a := fun k hk q hq _ => hfullS k hk q hq
  -- stage one: the source first cutoff
  have he012 : ∀ k < 3, e k ≤ 3 * σ k / 10 := by
    intro k hk
    interval_cases k
    · rw [he0]; linarith [hσ 0 (by norm_num)]
    · rw [he1]; exact ht₂
    · rw [he2]; exact ht₃
  have row₁ := markerLocalitySourceCutoff_row hχ hχ0 hχ1 hχI hP1 hP N u₁ (fun i => v (ι₁ i)) hu₁
    (fun i => hv _) (fun i => R (ι₁ i)) (fun i => hR _) ρ hρ U₁ η₁ (fun i => ζ (ι₁ i)) F hζU₁
    (fun i p => ⟨hu₁F i p, hvF _ p⟩) hcount₁ (fun i p hpos => hcompA _ p hpos) hplateau₁
  have hloc0 : ∀ q, ψ 0 (g 0 q) ≠ 0 → (Q 0).starProjection (F q) ∈ S 0 := by
    intro q hq
    rw [hψ0, hg0] at hq
    obtain ⟨i, hiU, hη⟩ := row₁.2.2.2.1 q (subset_tsupport _ hq)
    exact hS₀ q ⟨i, hiU, by linarith⟩
  have herr0 : ∀ q, ‖g 0 q - F q‖ ≤ e 0 * ρ q := fun q => by
    rw [hg0, sub_self, norm_zero, he0, zero_mul]
  -- after stage one: (ZM) for CFS23
  obtain ⟨hpert₁, htube₁, hZM₁, -⟩ := actualCloud_stage_output_supplies_cutoff_contract v hv R hR ρ
    hρ ζ hζ0 F hvF hcompA 1 Q Pst hPst ψ g hg0 (fun k hk => hstep k (by omega))
    (fun k hk => hretained k (by omega)) S select σ e (fun k hk => hsupport k (by omega))
    (fun k hk q hψq => hfull k (by omega) q (by obtain rfl : k = 0 := (by omega); exact hloc0 q hψq) hψq)
    (fun k hk => hselect k (by omega)) (fun k hk => hσ k (by omega))
    (fun k hk => he012 k (by omega))
    (fun k hk => by obtain rfl : k = 0 := (by omega); exact hloc0)
    (fun k hk q _ => by obtain rfl : k = 0 := (by omega); exact herr0 q)
    (fun k hk => hnear k (by omega)) hc₁0 hc₁ hcum₁
  have row₂ := cfs23_row (fun i => R (ι₂ i)) u₂ (fun i => v (ι₂ i)) xρ x1 x2 hχ hχ0 hχ1 hχI hχmono
    hP1 hP N hu₂ (fun i => hv _) hxρ hx1 hx2 hΔ (fun i => hR _) ρ hρ U₂ η₂ (fun i => ζ (ι₂ i))
    (fun i p => hζI _ p) F (g 1) hζU₂ (fun i p => ⟨hu₂F i p, hvF _ p⟩) hcount₂
    (fun i p hpos => ⟨(hcompA _ p hpos).1, (hcompA _ p hpos).2, hη₂ i p hpos⟩) hpert₁
    (fun i p hz => hZM₁ (ι₂ i) p hz) tE h hhI hhg hxρF hedgeblock hedge
  have hloc1 : ∀ q, ψ 1 (g 1 q) ≠ 0 → (Q 1).starProjection (F q) ∈ S 1 := by
    intro q hq
    rw [hψ1] at hq
    exact hS₁ q (row₂.2.2.2.1 q (subset_tsupport _ hq))
  have herr1 : ∀ q, ‖g 1 q - F q‖ ≤ e 1 * ρ q := fun q => by rw [he1]; exact htube₁ q
  have hloc01 : ∀ k < 2, ∀ q, ψ k (g k q) ≠ 0 → (Q k).starProjection (F q) ∈ S k := by
    intro k hk
    interval_cases k
    · exact hloc0
    · exact hloc1
  have herr01 : ∀ k < 2, ∀ q, ψ k (g k q) ≠ 0 → ‖g k q - F q‖ ≤ e k * ρ q := by
    intro k hk q _
    interval_cases k
    · exact herr0 q
    · exact herr1 q
  -- after stage two: (ZM) for CFS22
  obtain ⟨hpert₂, htube₂, hZM₂, -⟩ := actualCloud_stage_output_supplies_cutoff_contract v hv R hR ρ
    hρ ζ hζ0 F hvF hcompA 2 Q Pst hPst ψ g hg0 (fun k hk => hstep k (by omega))
    (fun k hk => hretained k (by omega)) S select σ e (fun k hk => hsupport k (by omega))
    (fun k hk q hψq => hfull k (by omega) q (hloc01 k hk q hψq) hψq)
    (fun k hk => hselect k (by omega)) (fun k hk => hσ k (by omega))
    (fun k hk => he012 k (by omega)) hloc01 herr01
    (fun k hk => hnear k (by omega)) hc₂0 hc₂ hcum₂
  have row₃ := cfs22_row hχ hχ0 hχ1 hχI hP1 hP N u₃ (fun i => v (ι₃ i)) hu₃ (fun i => hv _) hℓ
    (fun i => R (ι₃ i)) (fun i => hR _) ρ hρ U₃ η₃ (fun i => ζ (ι₃ i)) (fun i p => hζI _ p) F
    (g 2) hζU₃ (fun i p => ⟨hu₃F i p, hvF _ p⟩) hcount₃
    (fun i p hpos => ⟨(hcompA _ p hpos).1, (hcompA _ p hpos).2, hη₃ i p hpos⟩) hplateau₃ hpert₂
    (fun i p hz => hZM₂ (ι₃ i) p hz)
  have hloc2 : ∀ q, ψ 2 (g 2 q) ≠ 0 → (Q 2).starProjection (F q) ∈ S 2 := by
    intro q hq
    rw [hψ2] at hq
    exact hS₂ q (row₃.2.2.2.1 q (subset_tsupport _ hq))
  have herr2 : ∀ q, ‖g 2 q - F q‖ ≤ e 2 * ρ q := fun q => by rw [he2]; exact htube₂ q
  have hloc012 : ∀ k < 3, ∀ q, ψ k (g k q) ≠ 0 → (Q k).starProjection (F q) ∈ S k := by
    intro k hk
    interval_cases k
    · exact hloc0
    · exact hloc1
    · exact hloc2
  have herr012 : ∀ k < 3, ∀ q, ψ k (g k q) ≠ 0 → ‖g k q - F q‖ ≤ e k * ρ q := by
    intro k hk q _
    interval_cases k
    · exact herr0 q
    · exact herr1 q
    · exact herr2 q
  -- after stage three: exact small markers and (AZM)
  have hfin := actualCloud_scalar_zero_marker_bound v hv R hR ρ ζ hζ0 F hvF hcompA 3 Q Pst hPst ψ g
    hg0 hstep hretained S select σ e hsupport
    (fun k hk q hψq => hfull k hk q (hloc012 k hk q hψq) hψq) hselect hσ he012 hloc012 herr012
    hnear hc₃0 hc₃ hcum₃
  refine ⟨⟨row₁.1, row₁.2.2.1, fun p hp => ?_, row₁.2.2.2.2.2⟩,
    ⟨row₂.1, row₂.2.2.1, row₂.2.2.2.1, row₂.2.2.2.2⟩,
    ⟨row₃.1, row₃.2.2.1, row₃.2.2.2.1, row₃.2.2.2.2⟩, hfin.1, hfin.2⟩
  obtain ⟨i, hiU, hη⟩ := row₁.2.2.2.1 p hp
  exact ⟨i, hiU, by linarith⟩

end GC.MetricGeometry
