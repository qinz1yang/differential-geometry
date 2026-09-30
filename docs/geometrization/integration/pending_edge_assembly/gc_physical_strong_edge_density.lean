import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeProduction
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

set_option autoImplicit false
open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GC.MetricGeometry

universe u v w w'

theorem exists_strong_edge_density_parameters
    {Δ β₂ s : ℝ}
    (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (hs : 0 < s) (hssmall : s < 1 / 100) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ βE : ℝ, 0 < βE → βE < 1 / 100 →
      ∃ b₀ : ℝ, 0 < b₀ ∧
        ∀ (X : Type u) (mX : MetricSpace X), letI := mX
          ∀ (p : X) (Λ : NNReal) (ρ : X → ℝ) (hρpos : ∀ x, 0 < ρ x),
        LipschitzWith Λ ρ → (Λ : ℝ) < 1 / (1000000 * Δ) →
        ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
        (∀ a b : C, ∀ ε : ℝ, 0 < ε →
          ∃ f : unitInterval → C, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
            eVariationOn f univ < ENNReal.ofReal (dist a b + ε)) →
        dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
        ∀ (Z : Type w) [MetricSpace Z] (z : Z) (σ β : ℝ), σ ≤ a₀ → β < b₀ →
          letI := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          KleinerLottApprox p c σ →
          KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β →
          (∀ a b : X, ∃ γ : Icc (0 : ℝ) 1 → X,
            γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
            ∀ t₁ t₂, dist (γ t₁) (γ t₂) = dist a b * dist t₁ t₂) →
          (¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β₂)) →
          (∀ (A : Type w) [MetricSpace A] (a : A),
            Bornology.IsBounded (univ : Set A) → diam (univ : Set A) < 1000 * Δ →
              ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) β)) →
          (∃ a : X, (@isEdgePoint.{u, w} X
            (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ @dist X mX.toDist a p < Δ * ρ a) ∧
          ∀ (b' s' : ℝ) (q : X), b' < 1 / 100000000 → s' < 1 / 100000000 →
            (@isEdgePoint.{u, w'} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q Δ b' s') →
            @dist X mX.toDist q p < 10 * Δ * ρ p →
            ∃ a : X, (@isEdgePoint.{u, w} X
              (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ @dist X mX.toDist q a < ρ a := by
  obtain ⟨a₀, ha₀, hb⟩ := exists_normalized_strong_edge_density_parameters.{u, v, w, w'} hβ₂ hβ₂small hΔ hs hssmall
  refine ⟨a₀, ha₀, ?_⟩
  intro βE hβEpos hβE
  obtain ⟨b₀, hb₀, hdata⟩ := hb βE hβEpos hβE
  refine ⟨b₀, hb₀, ?_⟩
  intro X mX p Λ ρ hρpos hρ hscale C mC hc c hcurves hdim hcomp Z mZ z σ β hσ hβ
    f F hseg hnoplane hnobounded
  let mNorm := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
  let r : X → ℝ := fun x => ρ x / ρ p
  have hrpos (x : X) : 0 < r x := div_pos (hρpos x) (hρpos p)
  have hrp : r p = 1 := div_self (hρpos p).ne'
  have hr := @lipschitzWith_normalized_scale X mX ρ Λ hρ p (hρpos p)
  obtain ⟨hstrong, hweak⟩ := hdata X mNorm p C c hcurves hdim hcomp Z z σ β hσ hβ
    f F hseg hnoplane hnobounded Λ r hrpos hr hrp hscale
  have heq (x : X) : mNorm.rescale (r x)⁻¹ (inv_pos.mpr (hrpos x)) =
      mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x)) :=
    mX.rescale_inv_ratio (hρpos p) (hρpos x)
  have hdist {x y : X} {t : ℝ}
      (h : @dist X mNorm.toDist x y < t / ρ p) : @dist X mX.toDist x y < t := by
    change (ρ p)⁻¹ * @dist X mX.toDist x y < t / ρ p at h
    rw [← div_eq_inv_mul] at h
    exact (div_lt_div_iff_of_pos_right (hρpos p)).mp h
  constructor
  · obtain ⟨a, hed, hd⟩ := hstrong
    refine ⟨a, ?_, ?_⟩
    · rwa [heq a] at hed
    · apply hdist
      simpa only [r, mul_div_assoc] using hd
  · intro b' s' q hb' hs' hq hrad
    have hqnorm : @isEdgePoint.{u, w'} X
        (mNorm.rescale (r q)⁻¹ (inv_pos.mpr (hrpos q))) q Δ b' s' := by
      rw [heq q]
      exact hq
    have hradnorm : @dist X mNorm.toDist q p < 10 * Δ := by
      change (ρ p)⁻¹ * @dist X mX.toDist q p < 10 * Δ
      rw [← div_eq_inv_mul]
      exact (div_lt_iff₀ (hρpos p)).mpr hrad
    obtain ⟨a, hed, hd⟩ := hweak b' s' q hb' hs' hqnorm hradnorm
    refine ⟨a, ?_, hdist hd⟩
    rwa [heq a] at hed

end GC.MetricGeometry
