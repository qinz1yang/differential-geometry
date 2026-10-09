import DifferentialGeometry.Geometry.Metric.Approximation.CompatibleEndpointModels
import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeDensity
import DifferentialGeometry.Geometry.Metric.Approximation.WeakEdgeDensity

set_option autoImplicit false
open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GC.MetricGeometry

universe u v w w'

theorem exists_normalized_strong_edge_density_parameters
    {Δ β₂ s : ℝ}
    (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (hs : 0 < s) (hssmall : s < 1 / 100) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ βE : ℝ, 0 < βE → βE < 1 / 100 →
      ∃ b₀ : ℝ, 0 < b₀ ∧
        ∀ (X : Type u) (mX : MetricSpace X), letI := mX
          ∀ (p : X) (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
        (∀ a b : C, ∀ ε : ℝ, 0 < ε →
          ∃ f : unitInterval → C, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
            eVariationOn f univ < ENNReal.ofReal (dist a b + ε)) →
        dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
        ∀ (Z : Type w) [MetricSpace Z] (z : Z) (σ β : ℝ), σ ≤ a₀ → β < b₀ →
          KleinerLottApprox p c σ →
          KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β →
          (∀ a b : X, ∃ γ : Icc (0 : ℝ) 1 → X,
            γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
            ∀ t₁ t₂, dist (γ t₁) (γ t₂) = dist a b * dist t₁ t₂) →
          (¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β₂)) →
          (∀ (A : Type w) [MetricSpace A] (a : A),
            Bornology.IsBounded (univ : Set A) → diam (univ : Set A) < 1000 * Δ →
              ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) β)) →
          ∀ (Λ : NNReal) (ρ : X → ℝ) (hρpos : ∀ x, 0 < ρ x),
          LipschitzWith Λ ρ → ρ p = 1 → (Λ : ℝ) < 1 / (1000000 * Δ) →
          (∃ a : X, (@isEdgePoint.{u, w} X
            (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist a p < Δ * ρ a) ∧
          ∀ (b' s' : ℝ) (q : X), b' < 1 / 100000000 → s' < 1 / 100000000 →
            (@isEdgePoint.{u, w'} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q Δ b' s') →
            q ∈ ball p (10 * Δ) →
            ∃ a : X, (@isEdgePoint.{u, w} X
              (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist q a < ρ a := by
  have hΔone : 1 ≤ Δ := by
    have hh : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  let η := min (s / 2000) (1 / (200000 * Δ))
  let θ := s / 2000
  have hη : 0 < η := by dsimp [η]; positivity
  have hηs : η ≤ s / 1000 := (min_le_left _ _).trans (by linarith)
  have hηscale : η ≤ 1 / (100000 * Δ) := (min_le_right _ _).trans (by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith)
  have hηone : η < 1 := hηs.trans_lt (by linarith)
  have hηΔ : 900 * Δ < η⁻¹ := by
    have hh : η * (200000 * Δ) ≤ 1 := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    rw [← one_div]
    apply (lt_div_iff₀ hη).mpr
    nlinarith only [hh, mul_pos hη hΔpos]
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθs : θ ≤ s / 1000 := by dsimp [θ]; linarith
  let εmax := min (1 / 100000000) (min (s / 1000) (1 / (1000 * Δ)))
  have hεmax : 0 < εmax := by dsimp [εmax]; positivity
  obtain ⟨e, _, hemax, a₀, ha₀, hmodel⟩ :=
    exists_compatible_endpoint_model_parameters.{u, v, w}
      (L := 1000 * Δ) hβ₂ hβ₂small hΔ (by linarith) hη hηone hηΔ hθ hεmax
  have heprec : e < 1 / 100000000 := hemax.trans_le (min_le_left _ _)
  have hes : e ≤ s / 1000 :=
    hemax.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heΔ : e ≤ 1 / (1000 * Δ) :=
    hemax.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a₀, ha₀, ?_⟩
  intro βE hβEpos hβE
  let b₀ := min a₀ (min (βE / 100) (1 / (100 * Δ + 100 / βE)))
  have hb₀ : 0 < b₀ := by dsimp [b₀]; positivity
  refine ⟨b₀, hb₀, ?_⟩
  intro X mX p C mC hc c hcurves hdim hcomp Z mZ z σ β hσ hβ f F hseg hnoplane hnobounded
    Λ ρ hρpos hρ hρp hscale
  have hβa : β ≤ a₀ := (hβ.trans_le (min_le_left _ _)).le
  have hβsmall : β < βE / 100 := hβ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβdomain : β < 1 / (100 * Δ + 100 / βE) :=
    hβ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  rcases hmodel X p C c hcurves hdim hcomp Z z σ β hσ hβa f F hseg hnoplane hnobounded with
    ⟨D, hD, o, ho, G, H, _, hcompat⟩ | ⟨o, ho, G, H, _, hcompat⟩
  · constructor
    · exact exists_strong_edge_near_interval_model F G H hρ hρpos hρp hΔone hD
        hβE hβsmall hβdomain hs hssmall hηs hηscale hes heΔ hθs hscale ho.le hcompat
    · intro b' s' q hb' hs' hq hrad
      exact exists_strong_edge_near_weak_interval_model F G H hρ hρpos hρp hΔone hD
        hβE hβsmall hβdomain hs hssmall hηs hηscale hes heΔ hθs hscale ho.le hcompat
        heprec hb' hs' hq hrad
  · constructor
    · exact exists_strong_edge_near_ray_model F G H hρ hρpos hρp hΔone
        hβE hβsmall hβdomain hs hssmall hηs hηscale hes heΔ hθs hscale ho.le hcompat
    · intro b' s' q hb' hs' hq hrad
      exact exists_strong_edge_near_weak_ray_model F G H hρ hρpos hρp hΔone
        hβE hβsmall hβdomain hs hssmall hηs hηscale hes heΔ hθs hscale ho.le hcompat
        heprec hb' hs' hq hrad

end GC.MetricGeometry
