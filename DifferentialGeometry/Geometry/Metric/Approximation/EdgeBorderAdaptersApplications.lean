import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBorderAdapters
import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderDistance

/-!
# Consumer: the edge predicates control the distance to the closed weak edge border (LFR32 → LFR25)

The closed coarse border produced by LFR32 from the ACTUAL strong edge maps at `p` (normalized metric,
`coarse_border_of_lipschitz_scale`) is fed into the LFR25 metric kernel: on `B(p, 70Δ)` the distance to
`A = closure E'` differs from the actual composite height `G (v x)` by at most `2τΔ` (LFR25.2), and every
`x ∈ B(p, 30Δ)` with `d_A(x) ≤ 12Δ` has an actual outward point (LFR25.3). No chart is assumed: all
hypotheses are those of LFR29.1 on the original maps.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]

theorem coarseBorder_distance_of_edge_maps {p : X} {q : Y} {C b s : ℝ} {hC : 0 ≤ C}
    {Δ τ b' s' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000)
    (hbs : b < s / 100000) (hlength : 200 * Δ ≤ C) :
    let A : Set X := closure {x | @isEdgePoint.{u, v} X
      (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
    (∀ x ∈ ball p (70 * Δ), |infDist x A - (F.stripMap G x).snd| ≤ 2 * (τ * Δ)) ∧
    ∀ x ∈ ball p (30 * Δ), infDist x A ≤ 12 * Δ →
      ∃ y ∈ ball p (70 * Δ), |dist x y - infDist x A| ≤ 4 * (τ * Δ) ∧
        |infDist y A - 2 * infDist x A| ≤ 7 * (τ * Δ) := by
  intro A
  obtain ⟨-, hpA, hQp, hheight, hdist, hcover, hborder, hbordercover⟩ :=
    F.coarse_border_of_lipschitz_scale (hC := hC) G hρ hρpos hρp hΔ hτ hτsmall hscale hend
      hb'domain hs'domain hb'error hs'error hsb' hss' hbs hlength
  have hΔ0 : 0 < Δ := by linarith
  have hcover' : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (F.stripMap G x) z ≤ τ * Δ := fun z h1 h2 => by
    obtain ⟨x, hx, hxz⟩ := hcover z h1 h2
    exact ⟨x, hx, hxz.le⟩
  have hbc' : ∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
      dist (F.stripMap G a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ := fun t ht => by
    obtain ⟨a, ⟨haE, ha⟩, hat⟩ := hbordercover t ht
    exact ⟨a, ⟨subset_closure haE, ha⟩, hat.le⟩
  refine ⟨fun x hx => coarseBorder_abs_infDist_sub_height_le hΔ0 (by linarith) hQp hdist
    (fun x _ => hheight x) hpA hborder hbc' hx, fun x hx hxA => ?_⟩
  exact exists_coarseBorder_outward_point hΔ0 (by linarith) hQp hdist (fun x _ => hheight x)
    hcover' hpA hborder hbc' hx hxA

end GC.MetricGeometry
