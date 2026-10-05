import DifferentialGeometry.Geometry.Metric.ActualCloudStagePreservation
import DifferentialGeometry.Analysis.NormedSpace.ScaleVanishing

/-! CFS30 (master207B, B:3757): the zero-marker bound (AZM) from the actual plane rule.

Start with `F` and perform any initial segment of stages `g (k+1) = adjustmentMap (Q k) (Pst k) (ψ k) ∘ g k`, each with
CFS29's support, localization and error hypotheses. Induction with CFS29, starting from the original zero blocks
(CFS26's scale gap), gives EXACT vanishing of every block with `R_i < ρ(p)/16` at every stage. For the remaining
blocks the scalar marker moves by at most `E ρ ≤ 16 E R_i ≤ R_i/32`; convexity gives the bound on the whole segment
`[F p, g n p]`. This is the boxed ZM field of the CFS22/CFS23 contracts (review 39, §5.2–§5.3); no zero marker is
inferred from `|f − F| ≪ ρ` alone. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- CFS30: exact vanishing of the small blocks at every stage, and (AZM) on the straight segment. -/
theorem actualCloud_zero_marker_bound {M A : Type*}
    (n : ℕ) (Q : ℕ → Submodule ℝ H) (Pst : ℕ → H → H) (hP : ∀ k z, Pst k z ∈ Q k)
    (ψ : ℕ → H → ℝ) (F : M → H) (g : ℕ → M → H) (hg0 : ∀ q, g 0 q = F q)
    (hstep : ∀ k < n, ∀ q, g (k + 1) q = adjustmentMap (Q k) (Pst k) (ψ k) (g k q))
    (ρ : M → ℝ) (V : A → Submodule ℝ H) (marker : A → H → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i)
    (hnonneg : ∀ i q, 0 ≤ marker i (F q))
    (hsupport₀ : ∀ i q, 0 < marker i (F q) → 3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hblock : ∀ i q, marker i (F q) = 0 → (V i).starProjection (F q) = 0)
    (hretained : ∀ k < n, ∀ i, V i ≤ Q k ∨ V i ≤ (Q k)ᗮ)
    (S : ℕ → Set H) (select : ℕ → H → M) (σ e : ℕ → ℝ)
    (hsupport : ∀ k < n, ∀ i q, 0 < marker i ((Q k).starProjection (F q)) →
      3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hfull : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 →
      ∃ i, marker i ((Q k).starProjection (F q)) = R i)
    (hselect : ∀ k < n, ∀ x ∈ S k, (Q k).starProjection (F (select k x)) = x)
    (hσ : ∀ k < n, 0 < σ k) (he : ∀ k < n, e k ≤ 3 * σ k / 10)
    (hloc : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → (Q k).starProjection (F q) ∈ S k)
    (herror : ∀ k < n, ∀ q, ψ k (g k q) ≠ 0 → ‖g k q - F q‖ ≤ e k * ρ q)
    (hnear : ∀ k < n, ∀ x ∈ S k, ∀ z ∈ ball x (σ k * ρ (select k x)), ∀ q,
      (Q k).starProjection (F q) = x → ∀ i, R i < ρ q / 16 → (V i).starProjection (Pst k z) = 0)
    (J : A → H →L[ℝ] ℝ) (hJ : ∀ i, ‖J i‖ ≤ 1)
    (hJV : ∀ i y, (V i).starProjection y = 0 → J i y = 0)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512) (hcum : ∀ q, ‖g n q - F q‖ ≤ E * ρ q) :
    (∀ k ≤ n, ∀ q i, R i < ρ q / 16 → (V i).starProjection (g k q) = 0) ∧
      ∀ q i, J i (F q) = 0 → ∀ z ∈ segment ℝ (F q) (g n q), |J i z| ≤ R i / 32 := by
  have hexact : ∀ k ≤ n, ∀ q i, R i < ρ q / 16 → (V i).starProjection (g k q) = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ q i hi
      rw [hg0]
      apply hblock i q
      apply le_antisymm ?_ (hnonneg i q)
      by_contra hpos
      have hs := hsupport₀ i q (lt_of_not_ge hpos)
      linarith [hR i, hs.2]
    | succ k ih =>
      intro hk q i hi
      have hkn : k < n := hk
      rw [hstep k hkn q]
      exact actualCloud_stage_small_marker_preservation (Q k) (Pst k) (hP k) (ψ k) F (g k) ρ V
        marker R hR (hsupport k hkn) (hfull k hkn) (S k) (select k) (hselect k hkn) (hσ k hkn)
        (he k hkn) (hloc k hkn) (herror k hkn) (hnear k hkn) (hretained k hkn)
        (ih hkn.le) q i hi
  refine ⟨hexact, ?_⟩
  intro q i hJF z hz
  have hseg := (J i).norm_on_segment_le_of_vanishing_at_small_scale (hJ i) hJF (hR i).le
    (by norm_num : (0 : ℝ) < 16) (hcum q)
    (fun h => hJV i _ (hexact n le_rfl q i h)) hE z hz
  rw [← Real.norm_eq_abs]
  have hRi := (hR i).le
  calc ‖J i z‖ ≤ 16 * E * R i := hseg
    _ ≤ 16 * (1 / 512) * R i := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE512 (by norm_num)) hRi
    _ = R i / 32 := by ring

end GC.MetricGeometry
