import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleSmooth
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleEnvelopeApplications

/-!
# Consumer of BSA05: the smooth scale along the boundary counterexample sequence

Blueprint 207B, BSA05 in its sequence form: "on one sufficiently late tail there is a smooth
positive `Λ`-Lipschitz `ρ` ... for every fixed `ε > 0`, on a further tail it also satisfies
`ρ < ε` throughout all collar regions; the tail is uniform over components". Along any sequence of
connected nearly cuspidal carriers with static collapse at the ratios
`δ_n = boundaryCounterexampleRatio δ₀ n` (`0 < δ₀ ≤ δStar`, `K ≥ 2`), `H_bsa05_eventually`
chooses ONE `ρ_n` per member, with the BSA05.a properties on one tail and, for every `ε > 0`,
`ρ_n < ε` on all collar regions `0 ≤ z ≤ 96` on a further tail.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **BSA05 along the boundary counterexample sequence.** One smooth scale `ρ_n` per member:
smooth, positive, `Λ`-Lipschitz, `r_p(w)/2 ≤ ρ_n(p) ≤ 2 r_p(w')` on one tail, and for every
`ε > 0`, `ρ_n < ε` on all collar regions `0 ≤ z ≤ 96` of all components on a further tail. -/
theorem H_bsa05_eventually :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧ (∀ p, 0 < ρ n p) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ n p ∧
                ρ n p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              ∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δStar, hδStar, hS⟩ := H_smooth_scale.{u}
  refine ⟨min δStar (1 / 100), lt_min hδStar (by norm_num), ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK W _ g B hcoll Λ w hΛ hw hwc
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := by positivity
  have hδle (n : ℕ) : boundaryCounterexampleRatio δ₀ n ≤ min δStar (1 / 100) :=
    (boundaryCounterexampleRatio_le δ₀ n).trans hδ₀S
  have hex : ∀ n : ℕ, ∃ ρ : (W n).Carrier → ℝ,
      (3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧ (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧
        0 ≤ boundaryCounterexampleRatio δ₀ n ∧
        boundaryCounterexampleRatio δ₀ n * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
        1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
          w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2) →
      ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
        (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ p ∧
          ρ p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
        ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y := by
    intro n
    by_cases htail : 3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧
        (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧ 0 ≤ boundaryCounterexampleRatio δ₀ n ∧
        boundaryCounterexampleRatio δ₀ n * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
        1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
          w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2
    · obtain ⟨h3, h2S, hnw, hδ0, hδn, hδa⟩ := htail
      obtain ⟨ρ, hρ⟩ := hS (W n) (g n) K _ hK hδ0 ((hδle n).trans (min_le_left _ _)) (B n)
        (hcoll n) hΛ hw hwc h3 h2S hnw hδn hδa
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨fun _ => 0, fun h => absurd h htail⟩
  choose ρ hρ using hex
  refine ⟨ρ, ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw] with n hn
    exact hρ n hn
  · have hc : 0 < w / (2 * (1 + 2 / Λ) ^ 3) * min (1 / 2) (ε / 4) ^ 2 :=
      mul_pos hw' (pow_pos (lt_min (by norm_num) (by positivity)) 2)
    filter_upwards [eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw,
      eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt hδ₀ hc] with n hn hsmall
    intro i p hp
    exact (B n).lt_of_le_two_mul_firstVolumeScale ((hδle n).trans (min_le_right _ _)) hw' hε
      hsmall (fun p => ((hρ n hn).2.2.1 p).2) i hp

end DifferentialGeometry.Geometry.Collapse
