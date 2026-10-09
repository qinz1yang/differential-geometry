import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedLowDimensionalModel
import DifferentialGeometry.Geometry.Metric.Approximation.CommonCoordinateCancellation
import DifferentialGeometry.Geometry.Metric.Approximation.NonslimFactorEndpoint
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport

set_option autoImplicit false
open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GC.MetricGeometry

universe u v w

theorem exists_compatible_endpoint_model_parameters
    {Δ β₂ L η θ εmax : ℝ}
    (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (hL : 1 ≤ L) (hη : 0 < η) (hηone : η < 1) (hηΔ : 900 * Δ < η⁻¹)
    (hθ : 0 < θ) (hεmax : 0 < εmax) :
    ∃ e : ℝ, 0 < e ∧ e < εmax ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (X : Type u) [MetricSpace X] (p : X)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ a b : C, ∀ ε : ℝ, 0 < ε →
        ∃ f : unitInterval → C, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
          eVariationOn f univ < ENNReal.ofReal (dist a b + ε)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ (Z : Type w) [MetricSpace Z] (z : Z) (σ β : ℝ), σ ≤ a₀ → β ≤ a₀ →
        KleinerLottApprox p c σ →
        ∀ F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β,
        (∀ a b : X, ∃ γ : Icc (0 : ℝ) 1 → X,
          γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (γ s) (γ t) = dist a b * dist s t) →
        (¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β₂)) →
        (∀ (A : Type w) [MetricSpace A] (a : A),
          Bornology.IsBounded (univ : Set A) → diam (univ : Set A) < 1000 * Δ →
            ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) β)) →
        (∃ D : ℝ, 500 * Δ < D ∧ ∃ o : Icc (0 : ℝ) D, o.val < Δ / 2 ∧
          ∃ G : KleinerLottApprox z o η,
            ∃ H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e,
              (∀ x, (H.toFun x).fst = (F.toFun x).fst) ∧
              ∀ x ∈ ball p L, dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ) ∨
        (∃ o : Ici (0 : ℝ), o.val < Δ / 2 ∧
          ∃ G : KleinerLottApprox z o η,
            ∃ H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e,
              (∀ x, (H.toFun x).fst = (F.toFun x).fst) ∧
              ∀ x ∈ ball p L, dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ) := by
  obtain ⟨ξ, hξ, hcancel⟩ :=
    exists_factor_approximation_of_common_coordinate.{u, 0, w, 0} hL hη hηone hθ
  let e := min (εmax / 2) (min (β₂ / 200) (min (ξ / 2) (1 / 2)))
  have he : 0 < e := by dsimp [e]; positivity
  have hemax : e < εmax := (min_le_left _ _).trans_lt (by linarith)
  have heβ : e < β₂ / 100 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have heξ : e < ξ :=
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (by linarith)
  have heone : e < 1 :=
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by norm_num)
  obtain ⟨a, ha, _, hmodel⟩ := exists_prescribed_one_dimensional_model_parameter.{u, v, w} he heone
  refine ⟨e, he, hemax, min a (ξ / 2), by positivity, ?_⟩
  intro X mX p C mC hc c hcurves hdim hcomp Z mZ z σ β hσ hβ f F hseg hnoplane hnobounded
  obtain ⟨Y, mY, y, _, hcY, hYcomp, hYdim, hYseg, H, hH⟩ :=
    hmodel X p C c hcurves hdim hcomp Z z σ β
      (hσ.trans (min_le_left _ _)) (hβ.trans (min_le_left _ _)) f F
  let := mY
  let := hcY
  obtain ⟨G, hG⟩ := hcancel p 0 z y β e
    ((hβ.trans (min_le_right _ _)).trans_lt (by linarith)) heξ F H (fun x => (hH x).symm)
  rcases exists_nearby_endpoint_of_no_bounded_factor F G H hseg hYseg hYcomp hYdim
      hβ₂ hβ₂small hΔ heβ hηΔ hnoplane hnobounded with ⟨D, hD, fY, hy⟩ | ⟨fY, hy⟩
  · left
    let G' := G.mapTargetIsometry fY
    let H' := H.mapTargetIsometryAt ((IsometryEquiv.refl ℝ).withLpProdCongr 2 fY)
      (WithLp.toLp 2 ((0 : ℝ), fY y)) rfl
    refine ⟨D, hD, fY y, hy, G', H', ?_, ?_⟩
    · exact hH
    · intro x hx
      exact (fY.dist_eq _ _).trans_lt (hG x hx)
  · right
    let G' := G.mapTargetIsometry fY
    let H' := H.mapTargetIsometryAt ((IsometryEquiv.refl ℝ).withLpProdCongr 2 fY)
      (WithLp.toLp 2 ((0 : ℝ), fY y)) rfl
    refine ⟨fY y, hy, G', H', ?_, ?_⟩
    · exact hH
    · intro x hx
      exact (fY.dist_eq _ _).trans_lt (hG x hx)

end GC.MetricGeometry
