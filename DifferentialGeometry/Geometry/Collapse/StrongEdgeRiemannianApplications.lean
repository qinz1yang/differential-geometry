import DifferentialGeometry.Geometry.Collapse.StrongEdgeTail
import DifferentialGeometry.Geometry.Metric.Approximation.PlaneReferenceChart
import DifferentialGeometry.Geometry.Metric.Approximation.EveryBorderLift

/-!
# Concrete consumers of the LFR35/LFR41/LFR44 bindings

* `closedManifold_slim_splitting_of_bounded_factor`: LFR41 for the actual distance
  `inducedMetricSpace g` of a closed connected manifold, rescaled by `ρ(p)⁻¹` (completeness and the
  length identity are discharged, not assumed).
* `closedManifold_strong_edge_density`: LFR44 items 1–2 for the same actual distance.
* `plane_identity_chart_kleinerLott`: LFR35's plane comparison map for the identity chart of the
  Euclidean plane (`Q = id`, `τ = 0`), at the point `(0, 10⁷)`, `Δ = 10⁸`, `β₂ = 1/200`, `q = 1`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v w w'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]

/-- LFR41 on a closed connected manifold with its actual Riemannian distance. -/
theorem closedManifold_slim_splitting_of_bounded_factor (g : SmoothRiemannianMetric I M)
    {ρ : M → ℝ} (hρ : ∀ x, 0 < ρ x) {X : Type v} {Y : Type w} [MetricSpace X] [MetricSpace Y]
    {p : M} {x₀ : X} {y₀ : Y} {b η Δ : ℝ}
    (hY : Bornology.IsBounded (univ : Set Y)) (hD : diam (univ : Set Y) ≤ 500 * Δ)
    (hΔ : 1 ≤ Δ) (hη : 900 * Δ < η⁻¹) (G : KleinerLottApprox x₀ y₀ η) :
    letI := (inducedMetricSpace g).rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))
    KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), x₀)) b →
    ∃ (A : Type v) (_ : MetricSpace A) (a : A), Bornology.IsBounded (univ : Set A) ∧
      diam (univ : Set A) < 1000 * Δ ∧
      Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) b) := by
  let m := inducedMetricSpace g
  have : CompleteSpace M := inducedMetricSpace_completeSpace g
  intro f
  obtain ⟨F, _, _, hbd, hdiam⟩ := exists_slim_splitting_of_bounded_factor_riemannian (M := M) g
    (inducedMetricSpace_hmetric g) (inv_pos.mpr (hρ p)) hY hD hΔ hη G f
  exact ⟨_, inferInstance, _, hbd, hdiam, ⟨F⟩⟩

/-- LFR44 items 1–2 on a closed connected manifold with its actual Riemannian distance. -/
theorem closedManifold_strong_edge_density {Δ β₂ s : ℝ} (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100)
    (hΔ : 100 / β₂ < Δ) (hs : 0 < s) (hssmall : s < 1 / 100) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ βE : ℝ, 0 < βE → βE < 1 / 100 → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ g : SmoothRiemannianMetric I M,
      letI m := inducedMetricSpace g
      ∀ (Λ : NNReal) (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x), LipschitzWith Λ ρ →
        (Λ : ℝ) < 1 / (1000000 * Δ) →
      ∀ β : ℕ → ℝ, β 2 = β₂ → β 1 < b₀ →
      ∀ p ∈ scaledSplittingStratum.{u, w} ρ hρpos β 1,
      (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
        ∀ (A : Type w) [MetricSpace A] (a : A), Bornology.IsBounded (univ : Set A) →
          diam (univ : Set A) < 1000 * Δ →
          ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C) (σ : ℝ),
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) → σ ≤ a₀ →
      (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p));
        Nonempty (KleinerLottApprox p c σ)) →
      ∃ a : M, (@isEdgePoint.{u, w} M
          (m.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist a p < Δ * ρ a := by
  obtain ⟨a₀, ha₀, hpar⟩ := exists_strong_edge_density_riemannian.{u, v, w, 0} (I := I)
    hβ₂ hβ₂small hΔ hs hssmall
  refine ⟨a₀, ha₀, fun βE hβE hβE' => ?_⟩
  obtain ⟨b₀, hb₀, hdata⟩ := hpar βE hβE hβE'
  refine ⟨b₀, hb₀, fun g => ?_⟩
  let m := inducedMetricSpace g
  have : CompleteSpace M := inducedMetricSpace_completeSpace g
  intro Λ ρ hρpos hρ hscale β hβ2 hβ1 p hp hnonslim C _ _ c σ hseg hdim hcomp hσ hmodel
  exact (hdata M g (inducedMetricSpace_hmetric g) Λ ρ hρpos hρ hscale β hβ2 hβ1 p hp hnonslim
    C c σ hseg hdim hcomp hσ hmodel).1

end DifferentialGeometry.Geometry.Collapse

namespace GC.MetricGeometry

/-- LFR35's plane comparison map for the identity chart of the Euclidean plane (a lifted copy
`X = ULift ℝ²` as source, `Q = ULift.down`). -/
theorem plane_identity_chart_kleinerLott :
    letI := (inferInstance : MetricSpace (ULift.{0} (WithLp 2 (ℝ × ℝ)))).rescale (1 : ℝ)⁻¹
      (by norm_num)
    ∃ Φ : KleinerLottApprox (ULift.up.{0} (WithLp.toLp 2 ((0 : ℝ), (10000000 : ℝ))))
        (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 200),
      ∀ y, Φ.toFun y = @planeComparisonMap (ULift.{0} (WithLp 2 (ℝ × ℝ))) instMetricSpaceULift ULift.down
        (ULift.up.{0} 0) (ULift.up.{0} (WithLp.toLp 2 ((0 : ℝ), (10000000 : ℝ)))) 100000000 1 y := by
  have hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * 100000000 →
      z.snd ∈ Icc 0 (100 * 100000000) →
      ∃ x ∈ ball (ULift.up.{0} (0 : WithLp 2 (ℝ × ℝ))) (200 * 100000000),
        dist (ULift.down x) z ≤ 0 * 100000000 := by
    intro z hz1 hz2
    refine ⟨ULift.up z, ?_, by simp⟩
    rw [mem_ball, ULift.dist_eq, dist_zero_right]
    have h := WithLp.prod_norm_sq_eq_of_L2 z
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have h1 : |z.fst| ^ 2 ≤ (100 * 100000000) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz1 2
    have h2 : |z.snd| ^ 2 ≤ (100 * 100000000) ^ 2 := by
      rw [abs_of_nonneg hz2.1]
      exact pow_le_pow_left₀ hz2.1 hz2.2 2
    nlinarith [norm_nonneg z]
  have hx : ULift.up.{0} (WithLp.toLp 2 ((0 : ℝ), (10000000 : ℝ))) ∈
      ball (ULift.up.{0} (0 : WithLp 2 (ℝ × ℝ))) (15 * 100000000) := by
    rw [mem_ball, ULift.dist_eq, dist_zero_right]
    have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((0 : ℝ), (10000000 : ℝ)))
    have h0 : ‖WithLp.toLp 2 ((0 : ℝ), (10000000 : ℝ))‖ ^ 2 = 10000000 ^ 2 := by
      rw [h]
      simp
    nlinarith [norm_nonneg (WithLp.toLp 2 ((0 : ℝ), (10000000 : ℝ)))]
  exact exists_planeComparison_kleinerLott (Q := ULift.down.{0}) (p := ULift.up.{0} 0) (τ := 0)
    (Δ := 100000000) (β₂ := 1 / 200) (q := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
    (fun x _ y _ => by simp [ULift.dist_eq]) hcover hx (by simp; norm_num) (by simp; norm_num)
    (by norm_num) (by norm_num)

end GC.MetricGeometry
