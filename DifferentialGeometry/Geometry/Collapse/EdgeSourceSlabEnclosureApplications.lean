import DifferentialGeometry.Geometry.Collapse.EdgeSourceSlabEnclosure
import DifferentialGeometry.Geometry.Collapse.EdgeEndpointModelApplications

/-!
# Consumer: the flat half-plane slab lies in the model cylinder

Model and source `ℓ²(ℝ × ℝ≥0)`, `j_i = id`, `Φ = id`, chart `Q(t, r) = (t, r)`, border `A = {r = 0}`,
`F = d_A`, `f = t`, `ρ = 1`. B5 (`eventually_edgeSourceSlab_mem_image`) gives: every point of the slab
`{|t| ≤ 4Δ, d_A ≤ 4Δ}` in `B(q, 100Δ)` lies in `B(q, 6.5Δ)` with `|t| < 5Δ` and `r < 5Δ`
(`halfPlane_edgeSourceSlab_mem_cylinder`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- **Concrete consumer.** The flat half-plane edge slab lies in LFR24's cylinder window. -/
theorem halfPlane_edgeSourceSlab_mem_cylinder {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ y ∈ ball (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ≥0))) (100 * Δ),
      |y.fst| ≤ 4 * Δ →
      infDist y {x : WithLp 2 (ℝ × ℝ≥0) | x.snd = 0} ≤ 4 * Δ →
      dist y (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ≥0))) < 13 / 2 * Δ ∧ |y.fst| < 5 * Δ ∧
        dist y.snd (0 : ℝ≥0) < 5 * Δ := by
  set N := WithLp 2 (ℝ × ℝ≥0)
  set q : N := WithLp.toLp 2 ((0 : ℝ), (0 : ℝ≥0))
  set A : Set N := {x | x.snd = 0}
  have hQq : halfPlaneChart q = 0 := by
    simp only [halfPlaneChart, q, WithLp.toLp_fst, WithLp.toLp_snd, NNReal.coe_zero]
    rfl
  have hmain := eventually_edgeSourceSlab_mem_image (M := fun _ : ℕ => N) (fun _ => id) q
    (fun R ε hε => Eventually.of_forall fun _ x _ y _ => by simpa using hε)
    (fun a b _ hab => Eventually.of_forall fun _ y hy =>
      ⟨y, ball_subset_ball hab.le hy, rfl⟩)
    (IsometryEquiv.refl N) (z₀ := (0 : ℝ≥0)) rfl (Δ := Δ) (μ := 1 / 1000) (τ := 0) (h := 1 / 20)
    (l := 0) (Λ := 0) hΔ (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by simp) (by norm_num) (by simp)
    (fun _ => halfPlaneChart) (fun _ => A) (fun _ x => infDist x A) (fun _ x => x.fst)
    (fun _ _ => 1) (fun _ => hQq)
    (fun _ x _ y _ => by rw [dist_halfPlaneChart, sub_self, abs_zero]; simp)
    (fun _ x _ => by
      simp only [halfPlaneChart, WithLp.toLp_snd]
      exact x.snd.2)
    (Metric.tendstoUniformlyOn_iff.mpr fun ε hε => Eventually.of_forall fun _ x _ => by
      change dist (x : N).fst (x : N).fst < ε
      rw [dist_self]
      exact hε)
    (fun _ => rfl)
    (fun _ a ha => by
      have : a.snd = 0 := ha.1
      simp only [halfPlaneChart, WithLp.toLp_snd, this, NNReal.coe_zero, zero_mul, le_refl])
    (fun _ t ht => by
      refine ⟨WithLp.toLp 2 (t, (0 : ℝ≥0)), ⟨rfl, ?_⟩, ?_⟩
      · change dist (WithLp.toLp 2 (t, (0 : ℝ≥0))) q < 190 * Δ
        rw [dist_toLp_same_snd, sub_zero]
        linarith
      · change dist (WithLp.toLp 2 (t, ((0 : ℝ≥0) : ℝ))) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ 0 * Δ
        simp)
    (fun _ x => by rw [sub_self, abs_zero]; positivity)
    (fun _ x _ => by
      simp only [halfPlaneChart, WithLp.toLp_fst, sub_self, abs_zero]
      positivity)
    (fun _ => LipschitzWith.const 1) (fun _ => rfl)
  obtain ⟨i, hi⟩ := hmain.exists
  intro y hy hfy hA
  obtain ⟨x, hx, hxy, hx1, hx2⟩ := hi y hy hfy (by simpa using hA)
  change x = y at hxy
  subst hxy
  exact ⟨hx, hx1, hx2⟩

end DifferentialGeometry.Geometry.Collapse
