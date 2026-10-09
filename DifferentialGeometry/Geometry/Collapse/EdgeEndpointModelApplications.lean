import DifferentialGeometry.Geometry.Collapse.EdgeEndpointModel
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Consumer: the flat half-plane edge has an actual endpoint model

Model and source `N = M_i = ℓ²(ℝ × ℝ≥0)` (the flat edge), `j_i = id`, `Φ = id`, `q = (0, 0)`, chart
`Q(t, r) = (t, r)` in `ℓ²(ℝ × ℝ)`. All hypotheses of `exists_edgeEndpointModel` hold exactly, so the
factor `ℝ≥0` carries an endpoint model of `[0, 10Δ]` with error `20τΔ`
(`halfPlane_edgeEndpointModel`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- The flat edge chart `(t, r) ↦ (t, r)`. -/
def halfPlaneChart (x : WithLp 2 (ℝ × ℝ≥0)) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 (x.fst, (x.snd : ℝ))

theorem dist_halfPlaneChart (x y : WithLp 2 (ℝ × ℝ≥0)) :
    dist (halfPlaneChart x) (halfPlaneChart y) = dist x y := by
  rw [dist_withLp_two_prod, dist_withLp_two_prod]
  simp only [halfPlaneChart, WithLp.toLp_fst, WithLp.toLp_snd]
  rfl

/-- **Concrete consumer.** The flat half-plane edge: the factor `ℝ≥0` has an actual endpoint model
of `[0, 10Δ]` (value `0` at the endpoint, distortion and density error `20τΔ`). -/
theorem halfPlane_edgeEndpointModel {Δ τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 1000) :
    ∃ e : ℝ≥0 → ℝ, e 0 = 0 ∧
      (∀ w ∈ closedBall (0 : ℝ≥0) (10 * Δ), ∀ w' ∈ closedBall (0 : ℝ≥0) (10 * Δ),
        |dist (e w) (e w') - dist w w'| ≤ 20 * τ * Δ) ∧
      ∀ s ∈ Icc (0 : ℝ) (10 * Δ), ∃ w ∈ closedBall (0 : ℝ≥0) (10 * Δ),
        |e w - s| ≤ 20 * τ * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  set N := WithLp 2 (ℝ × ℝ≥0)
  set q : N := WithLp.toLp 2 ((0 : ℝ), (0 : ℝ≥0))
  have hQq : halfPlaneChart q = 0 := by
    simp only [halfPlaneChart, q, WithLp.toLp_fst, WithLp.toLp_snd, NNReal.coe_zero]
    rfl
  obtain ⟨e, he0, -, hdis, hden, -⟩ := exists_edgeEndpointModel (M := fun _ : ℕ => N)
    (fun _ => id) q
    (fun R ε hε => Eventually.of_forall fun _ x _ y _ => by simpa using hε)
    (fun R ε hε => Eventually.of_forall fun _ y hy =>
      ⟨y, ball_subset_ball (by linarith) hy, by simpa using hε⟩)
    (IsometryEquiv.refl N) rfl hΔ hτ hτ1 (fun _ => halfPlaneChart) (fun _ => hQq)
    (fun _ x _ y _ => by
      rw [dist_halfPlaneChart, sub_self, abs_zero]
      positivity)
    (fun _ x _ => by
      simp only [halfPlaneChart, WithLp.toLp_snd]
      exact x.snd.2)
    (fun _ z hz1 hz2 => by
      refine ⟨WithLp.toLp 2 (z.fst, ⟨z.snd, hz2.1⟩), ?_, ?_⟩
      · change dist _ q < 200 * Δ
        rw [← dist_halfPlaneChart, hQq, dist_withLp_two_prod]
        simp only [halfPlaneChart, WithLp.toLp_fst, WithLp.toLp_snd]
        change Real.sqrt (dist z.fst (0 : ℝ) ^ 2 + dist z.snd (0 : ℝ) ^ 2) < 200 * Δ
        rw [Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, sq_abs, sq_abs,
          Real.sqrt_lt' (by positivity)]
        have h1 := abs_le.mp hz1
        nlinarith [hz2.1, hz2.2]
      · have hz : halfPlaneChart (WithLp.toLp 2 (z.fst, ⟨z.snd, hz2.1⟩)) = z := rfl
        rw [hz, dist_self]
        positivity)
    (Metric.tendstoUniformlyOn_iff.mpr fun ε hε => Eventually.of_forall fun _ x _ => by
      change dist (x : N).fst (x : N).fst < ε
      rw [dist_self]
      exact hε)
  exact ⟨e, he0, hdis, hden⟩

end DifferentialGeometry.Geometry.Collapse
