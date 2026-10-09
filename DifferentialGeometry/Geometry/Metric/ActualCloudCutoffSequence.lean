import DifferentialGeometry.Geometry.Metric.ActualCloudZeroMarkerBound
import DifferentialGeometry.Analysis.Calculus.Cutoff.MarkerLocalitySourceCutoff

/-! CFS31 (master207B, B:3783): the sequential cutoff construction without a marker assumption.

* `actualCloud_marker_budget`: the (MB) choices `c₃ ≤ 1/512`, `c₂ ≤ min{t₃, 4κ/5, 1/512}`, `c₁ ≤ min{t₂, 4κ/5, 1/512}`,
  `κ = 1/(1000(N+1)P²)` give every inequality used below, and `80 N P² ≤ C = 10⁴ (N+1)² P⁴`.
* `actualCloud_first_stage_localization`: the source first cutoff `ψ₁` localizes the ORIGINAL point to the
  stage-one core `A₁ = {∃ i, p ∈ U_i, |η_i(p)| < 7}` on its closed support — CFS29's localization hypothesis for
  stage one (the "first-stage" condition of review 39's §4.2 list).
* `actualCloud_stage_output_supplies_cutoff_contract`: after any initial segment of stages with CFS29's hypotheses
  and cumulative error `< c ρ`, CFS30 (scalar markers `v_i`, blocks `(ker v_i)ᗮ`) supplies BOTH boxed fields of the
  next cutoff contract (review 39 §5.2/§5.3): `|f − F| ≤ (4κ/5) ρ` and `ζ_i = 0 ⇒ |v_i(f)| ≤ R_i/32`, also along
  the segment, plus the next tube bound `|f − F| ≤ t ρ`. No later cutoff is used.
* `actualCloud_third_cutoff_of_stages`: the stage outputs feed CFS22 (`cfs22_row`) — the slim cutoff's support,
  plateau and `C/ρ` derivative conclusions hold WITHOUT assuming (ZM). The edge link (CFS23) consumes the same
  supply lemma (lane C14-KA). -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

/-- (MB) arithmetic of CFS31. -/
theorem actualCloud_marker_budget
    {N P : ℝ} (hN : 0 ≤ N) (hP : 1 ≤ P) {c₁ c₂ c₃ t₂ t₃ : ℝ}
    (hc₃ : c₃ ≤ 1 / 512)
    (hc₂ : c₂ ≤ min t₃ (min (4 * (1 / (1000 * (N + 1) * P ^ 2)) / 5) (1 / 512)))
    (hc₁ : c₁ ≤ min t₂ (min (4 * (1 / (1000 * (N + 1) * P ^ 2)) / 5) (1 / 512))) :
    80 * N * P ^ 2 ≤ 10000 * (N + 1) ^ 2 * P ^ 4 ∧
      c₁ ≤ t₂ ∧ c₂ ≤ t₃ ∧ c₁ ≤ 1 / 512 ∧ c₂ ≤ 1 / 512 ∧ c₃ ≤ 1 / 512 ∧
      c₁ ≤ 4 * (1 / (1000 * (N + 1) * P ^ 2)) / 5 ∧
      c₂ ≤ 4 * (1 / (1000 * (N + 1) * P ^ 2)) / 5 := by
  have hP2 : (1 : ℝ) ≤ P ^ 2 := by nlinarith
  have hP4 : P ^ 2 ≤ P ^ 4 := by nlinarith
  have hN2 : 80 * N ≤ 10000 * (N + 1) ^ 2 := by nlinarith
  refine ⟨?_, hc₁.trans (min_le_left _ _), hc₂.trans (min_le_left _ _),
    hc₁.trans ((min_le_right _ _).trans (min_le_right _ _)),
    hc₂.trans ((min_le_right _ _).trans (min_le_right _ _)), hc₃,
    hc₁.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hc₂.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  calc 80 * N * P ^ 2 ≤ 10000 * (N + 1) ^ 2 * P ^ 2 :=
        mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ ≤ 10000 * (N + 1) ^ 2 * P ^ 4 := mul_le_mul_of_nonneg_left hP4 (by positivity)

/-- Stage-one localization: wherever the stage-one adjustment acts (`ψ₁ (F q) ≠ 0`), the ORIGINAL point lies in the
core `A₁ = {∃ i, q ∈ U_i ∧ |η_i(q)| < 7}` (with the strict buffer `13/2 < 7`); hence its stage image lies in any set
`S₁ ⊇ π(F(A₁))`. -/
theorem actualCloud_first_stage_localization {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    {X : Type*} (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p)
    (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ) (F : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 → ζ i p = 1)
    {G : Type*} (π : H → G) (S₁ : Set G)
    (hS₁ : ∀ q, (∃ i, q ∈ U i ∧ ‖η i q‖ < 7) → π (F q) ∈ S₁) :
    ∀ q, markerLocalitySourceCutoff χ R u v (F q) ≠ 0 →
      (∃ i, q ∈ U i ∧ ‖η i q‖ < 7) ∧ π (F q) ∈ S₁ := by
  intro q hq
  obtain ⟨i, hiU, hη⟩ := (markerLocalitySourceCutoff_row hχ hχ0 hχ1 hχI hP1 hP N u v hu hv R hR
    ρ hρ U η ζ F hζU hblock hcount hcomp hplateau).2.2.2.1 q (subset_tsupport _ hq)
  have hA : ∃ i, q ∈ U i ∧ ‖η i q‖ < 7 := ⟨i, hiU, by linarith⟩
  exact ⟨hA, hS₁ q hA⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- CFS30 in scalar-marker form (blocks `(ker v_a)ᗮ`, "a scalar marker suffices"): after any initial segment of
stages with CFS29's hypotheses, every marker with `R_a < ρ/16` vanishes exactly at every stage, and (AZM) holds on
the segment `[F p, g n p]` once the cumulative error is at most `E ρ`, `E ≤ 1/512`. -/
theorem actualCloud_scalar_zero_marker_bound {A X : Type*}
    (v : A → H →L[ℝ] ℝ) (hv : ∀ a, ‖v a‖ ≤ 1) (R : A → ℝ) (hR : ∀ a, 0 < R a)
    (ρ : X → ℝ) (ζ : A → X → ℝ) (hζ0 : ∀ a p, 0 ≤ ζ a p) (F : X → H)
    (hvF : ∀ a p, v a (F p) = R a * ζ a p)
    (hcomp : ∀ a p, 0 < ζ a p → 3 / 4 * R a ≤ ρ p ∧ ρ p ≤ 5 / 4 * R a)
    (n : ℕ) (Q : ℕ → Submodule ℝ H) (Pst : ℕ → H → H) (hPst : ∀ k z, Pst k z ∈ Q k)
    (ψ : ℕ → H → ℝ) (g : ℕ → X → H) (hg0 : ∀ q, g 0 q = F q)
    (hstep : ∀ k < n, ∀ q, g (k + 1) q = adjustmentMap (Q k) (Pst k) (ψ k) (g k q))
    (hretained : ∀ k < n, ∀ a,
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q k ∨ (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ (Q k)ᗮ)
    (S : ℕ → Set H) (select : ℕ → H → X) (σ e : ℕ → ℝ)
    (hsupport : ∀ k < n, ∀ a q, 0 < v a ((Q k).starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (hfull : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → ∃ a, v a ((Q k).starProjection (F q)) = R a)
    (hselect : ∀ k < n, ∀ x ∈ S k, (Q k).starProjection (F (select k x)) = x)
    (hσ : ∀ k < n, 0 < σ k) (he : ∀ k < n, e k ≤ 3 * σ k / 10)
    (hloc : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → (Q k).starProjection (F q) ∈ S k)
    (herror : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → ‖g k q - F q‖ ≤ e k * ρ q)
    (hnear : ∀ k < n, ∀ x ∈ S k, ∀ z ∈ ball x (σ k * ρ (select k x)), ∀ q,
      (Q k).starProjection (F q) = x → ∀ a, R a < ρ q / 16 → v a (Pst k z) = 0)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512) (hcum : ∀ q, ‖g n q - F q‖ ≤ E * ρ q) :
    (∀ k ≤ n, ∀ q a, R a < ρ q / 16 → v a (g k q) = 0) ∧
      ∀ a p, ζ a p = 0 → ∀ z ∈ segment ℝ (F p) (g n p), |v a z| ≤ R a / 32 := by
  set V : A → Submodule ℝ H := fun a => (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ with hVdef
  have hVzero : ∀ a y, (V a).starProjection y = 0 ↔ v a y = 0 := by
    intro a y
    rw [(V a).starProjection_apply_eq_zero_iff, hVdef]
    simp only
    rw [Submodule.orthogonal_orthogonal, LinearMap.mem_ker]
    rfl
  have hazm := actualCloud_zero_marker_bound n Q Pst hPst ψ F g hg0 hstep ρ V
    (fun a y => v a y) R hR
    (fun a q => by rw [hvF]; exact mul_nonneg (hR a).le (hζ0 a q))
    (by
      intro a q hpos
      rw [hvF] at hpos
      have hζ : 0 < ζ a q := pos_of_mul_pos_right hpos (hR a).le
      have hc := hcomp a q hζ
      constructor <;> linarith [hc.1, hc.2])
    (fun a q hz => (hVzero a (F q)).mpr hz) hretained S select σ e hsupport hfull hselect hσ he
    hloc herror
    (fun k hk x hx z hz q hq a ha => (hVzero a _).mpr (hnear k hk x hx z hz q hq a ha))
    v hv (fun a y hy => (hVzero a y).mp hy) hE hE512 hcum
  refine ⟨fun k hk q a ha => (hVzero a _).mp (hazm.1 k hk q a ha), ?_⟩
  intro a p hζ z hz
  exact hazm.2 p a (by rw [hvF, hζ, mul_zero]) z hz

/-- CFS31 sequential step: an initial segment of stages (CFS29 hypotheses, scalar markers `v_i`) with cumulative
error `≤ c ρ`, `c ≤ min{t, 4κ/5, 1/512}`, supplies both boxed fields of the next cutoff contract. -/
theorem actualCloud_stage_output_supplies_cutoff_contract {I X : Type*}
    (v : I → H →L[ℝ] ℝ) (hv : ∀ i, ‖v i‖ ≤ 1) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (ζ : I → X → ℝ) (hζ0 : ∀ i p, 0 ≤ ζ i p) (F : X → H)
    (hvF : ∀ i p, v i (F p) = R i * ζ i p)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i)
    (n : ℕ) (Q : ℕ → Submodule ℝ H) (Pst : ℕ → H → H) (hPst : ∀ k z, Pst k z ∈ Q k)
    (ψ : ℕ → H → ℝ) (g : ℕ → X → H) (hg0 : ∀ q, g 0 q = F q)
    (hstep : ∀ k < n, ∀ q, g (k + 1) q = adjustmentMap (Q k) (Pst k) (ψ k) (g k q))
    (hretained : ∀ k < n, ∀ i,
      (LinearMap.ker (v i : H →ₗ[ℝ] ℝ))ᗮ ≤ Q k ∨ (LinearMap.ker (v i : H →ₗ[ℝ] ℝ))ᗮ ≤ (Q k)ᗮ)
    (S : ℕ → Set H) (select : ℕ → H → X) (σ e : ℕ → ℝ)
    (hsupport : ∀ k < n, ∀ i q, 0 < v i ((Q k).starProjection (F q)) →
      3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hfull : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → ∃ i, v i ((Q k).starProjection (F q)) = R i)
    (hselect : ∀ k < n, ∀ x ∈ S k, (Q k).starProjection (F (select k x)) = x)
    (hσ : ∀ k < n, 0 < σ k) (he : ∀ k < n, e k ≤ 3 * σ k / 10)
    (hloc : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → (Q k).starProjection (F q) ∈ S k)
    (herror : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → ‖g k q - F q‖ ≤ e k * ρ q)
    (hnear : ∀ k < n, ∀ x ∈ S k, ∀ z ∈ ball x (σ k * ρ (select k x)), ∀ q,
      (Q k).starProjection (F q) = x → ∀ i, R i < ρ q / 16 → v i (Pst k z) = 0)
    {c t κ : ℝ} (hc0 : 0 ≤ c) (hcB : c ≤ min t (min (4 * κ / 5) (1 / 512)))
    (hcum : ∀ q, ‖g n q - F q‖ ≤ c * ρ q) :
    (∀ p, ‖g n p - F p‖ ≤ 4 * κ / 5 * ρ p) ∧ (∀ p, ‖g n p - F p‖ ≤ t * ρ p) ∧
      (∀ i p, ζ i p = 0 → |v i (g n p)| ≤ R i / 32) ∧
      ∀ i p, ζ i p = 0 → ∀ z ∈ segment ℝ (F p) (g n p), |v i z| ≤ R i / 32 := by
  have hseg := (actualCloud_scalar_zero_marker_bound v hv R hR ρ ζ hζ0 F hvF hcomp n Q Pst hPst ψ g
    hg0 hstep hretained S select σ e hsupport hfull hselect hσ he hloc herror hnear hc0
    (hcB.trans ((min_le_right _ _).trans (min_le_right _ _))) hcum).2
  refine ⟨fun p => (hcum p).trans (mul_le_mul_of_nonneg_right
      (hcB.trans ((min_le_right _ _).trans (min_le_left _ _))) (hρ p).le),
    fun p => (hcum p).trans (mul_le_mul_of_nonneg_right (hcB.trans (min_le_left _ _)) (hρ p).le),
    fun i p hζ => hseg i p hζ _ (right_mem_segment ℝ _ _), hseg⟩

/-- CFS31, third cutoff: the stage outputs (CFS29 hypotheses, cumulative error `≤ c₂ ρ`, (MB)) satisfy CFS22's
contract, so the slim cutoff has all its support, plateau and derivative conclusions — (ZM) is PROVED, not
assumed. -/
theorem actualCloud_third_cutoff_of_stages {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1)
    (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    {X : Type*} {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ)
    (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * ℓ)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 * ℓ → ζ i p = 1)
    (n : ℕ) (Q : ℕ → Submodule ℝ H) (Pst : ℕ → H → H) (hPst : ∀ k z, Pst k z ∈ Q k)
    (ψ : ℕ → H → ℝ) (g : ℕ → X → H) (hg0 : ∀ q, g 0 q = F q)
    (hstep : ∀ k < n, ∀ q, g (k + 1) q = adjustmentMap (Q k) (Pst k) (ψ k) (g k q))
    (hretained : ∀ k < n, ∀ i,
      (LinearMap.ker (v i : H →ₗ[ℝ] ℝ))ᗮ ≤ Q k ∨ (LinearMap.ker (v i : H →ₗ[ℝ] ℝ))ᗮ ≤ (Q k)ᗮ)
    (S : ℕ → Set H) (select : ℕ → H → X) (σ e : ℕ → ℝ)
    (hsupport : ∀ k < n, ∀ i q, 0 < v i ((Q k).starProjection (F q)) →
      3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hfull : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → ∃ i, v i ((Q k).starProjection (F q)) = R i)
    (hselect : ∀ k < n, ∀ x ∈ S k, (Q k).starProjection (F (select k x)) = x)
    (hσ : ∀ k < n, 0 < σ k) (he : ∀ k < n, e k ≤ 3 * σ k / 10)
    (hloc : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → (Q k).starProjection (F q) ∈ S k)
    (herror : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → ‖g k q - F q‖ ≤ e k * ρ q)
    (hnear : ∀ k < n, ∀ x ∈ S k, ∀ z ∈ ball x (σ k * ρ (select k x)), ∀ q,
      (Q k).starProjection (F q) = x → ∀ i, R i < ρ q / 16 → v i (Pst k z) = 0)
    {c₂ t₃ : ℝ} (hc0 : 0 ≤ c₂)
    (hc₂ : c₂ ≤ min t₃ (min (4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (1 / 512)))
    (hcum : ∀ q, ‖g n q - F q‖ ≤ c₂ * ρ q) :
    (∀ p, ‖g n p - F p‖ ≤ t₃ * ρ p) ∧
      ContDiff ℝ ∞ (cfsUniformAxisCutoff χ ℓ R u v) ∧
      (∀ z, cfsUniformAxisCutoff χ ℓ R u v z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6 * ℓ) → cfsUniformAxisCutoff χ ℓ R u v (g n p) = 1) ∧
      (∀ p, g n p ∈ tsupport (cfsUniformAxisCutoff χ ℓ R u v) →
        ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ) ∧
      (∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (cfsUniformAxisCutoff χ ℓ R u v) ((1 - t) • F p + t • g n p)‖ ≤
          10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p) := by
  obtain ⟨hpert, htube, hZM, -⟩ := actualCloud_stage_output_supplies_cutoff_contract v hv R hR ρ hρ ζ
    (fun i p => (hζI i p).1) F (fun i p => (hblock i p).2)
    (fun i p hζ => ⟨(hcomp i p hζ).1, (hcomp i p hζ).2.1⟩) n Q Pst hPst ψ g hg0 hstep hretained S
    select σ e hsupport hfull hselect hσ he hloc herror hnear hc0 hc₂ hcum
  exact ⟨htube, cfs22_row hχ hχ0 hχ1 hχI hP1 hP N u v hu hv hℓ R hR ρ hρ U η ζ hζI F (g n) hζU
    hblock hcount hcomp hplateau hpert hZM⟩

end GC.MetricGeometry
