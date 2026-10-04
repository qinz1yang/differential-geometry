import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleEnvelope
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.ScalarSmoothing
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarBinding

/-!
# One smooth scale on the whole boundary carrier (BSA05)

Blueprint 207B, BSA05 (`B:7915–7978`); route R3, statement H and the `ρ < ε` clause
(design errata E8 = disposition D8). With `S = 1 + 2/Λ`, `w' = w/(2S³)`:

* `H_smooth_scale` (BSA05.a): on the uniform tail of `H_envelope` there is a smooth (up to the
  boundary) positive `Λ`-Lipschitz `ρ` on ALL of `W` with `r_p(w)/2 ≤ ρ(p) ≤ 2 r_p(w')`
  (`H_envelope`, then the smoothing step `exists_smooth_scale_of_envelope`).
* `NearlyCuspidalBoundary.lt_of_le_two_mul_firstVolumeScale` (the collar clause): on the further
  tail `1000δ² < w'·a_ε²`, `a_ε = min (1/2) (ε/4)`, EVERY function `ρ ≤ 2 r(w')` is `< ε` on all
  collar regions `0 ≤ z ≤ 96` of all components (the blueprint states `z ≤ 95`). It consumes the
  high-height-band volume clause `NearlyCuspidalBoundary.ballVolume_le_thousand` (`z ≤ 96`), not
  only G's `d(p, ∂W) ≤ 10` clause (D8). No collapse hypothesis is used near the boundary.
* `H_bsa05`: both, for one `ρ`.

BSA02 is not used (it stays open, disposition D5).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **BSA05.a (one smooth scale).** On the uniform tail of `H_envelope`, a smooth positive
`Λ`-Lipschitz function `ρ` on all of `W` (up to its boundary) with `r_p(w)/2 ≤ ρ(p) ≤ 2 r_p(w')`. -/
theorem H_smooth_scale :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      boundaryVolumeCollapsed W g δ →
      ∀ {Λ w n : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
        3 ≤ n → 2 * (1 + 2 / Λ) < n → n⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) →
        δ * (16 * n ^ 4) ≤ 1 →
        1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 →
        ∃ ρ : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
          (∀ p, firstVolumeScale g p w / 2 ≤ ρ p ∧
            ρ p ≤ 2 * firstVolumeScale g p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
          ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y := by
  obtain ⟨δStar, hδStar, hH⟩ := H_envelope.{u}
  refine ⟨δStar, hδStar, ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll Λ w n hΛ hw hwc hn hnS hnw hδn hδa
  exact exists_smooth_scale_of_envelope W g hΛ
    (fun p => firstVolumeScale_pos_everywhere W g p hw hwc)
    (hH W g K δ hK hδ0 hδ B hcoll hΛ hw hwc hn hnS hnw hδn hδa)

/-- **BSA05, collar clause.** For `δ ≤ 1/100` and `1000 δ² < w' a_ε²`, `a_ε = min (1/2) (ε/4)`,
every function `ρ ≤ 2 r(w')` (any admissible choice) is `< ε` at every collar point of height
`z ≤ 96`, of every component: `r(w') < a_ε` there by the collar volume bound
`vol B(e_i p, a) ≤ 1000 δ² a`, so `ρ < 2 a_ε ≤ ε/2`. -/
theorem NearlyCuspidalBoundary.lt_of_le_two_mul_firstVolumeScale {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) {w' ε : ℝ} (hw' : 0 < w')
    (hε : 0 < ε) (hδε : 1000 * δ ^ 2 < w' * min (1 / 2) (ε / 4) ^ 2)
    {ρ : W.Carrier → ℝ} (hρ : ∀ p, ρ p ≤ 2 * firstVolumeScale g p w') (i : Fin B.count)
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) :
    ρ ((B.collar i).toFun p) < ε := by
  set a := min (1 / 2 : ℝ) (ε / 4)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have haε : a ≤ ε / 4 := min_le_right _ _
  have hvol := B.ballVolume_le_thousand hδ i hp ha1
  have hr := firstVolumeScale_lt_of_ballVolume_le_linear g ((B.collar i).toFun p) ha hw' hvol hδε
  have h := hρ ((B.collar i).toFun p)
  linarith

/-- **BSA05** (both assertions, one `ρ`): on the uniform tail, a smooth positive `Λ`-Lipschitz
`ρ` on all of `W` with `r_p(w)/2 ≤ ρ(p) ≤ 2 r_p(w')`, and for every `ε > 0`, on the further tail
`1000 δ² < w' (min (1/2) (ε/4))²`, `ρ < ε` on all collar regions `0 ≤ z ≤ 96`. -/
theorem H_bsa05 :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → ∀ B : NearlyCuspidalBoundary W g K δ,
      boundaryVolumeCollapsed W g δ →
      ∀ {Λ w n : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
        3 ≤ n → 2 * (1 + 2 / Λ) < n → n⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) →
        δ * (16 * n ^ 4) ≤ 1 →
        1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 →
        ∃ ρ : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
          (∀ p, firstVolumeScale g p w / 2 ≤ ρ p ∧
            ρ p ≤ 2 * firstVolumeScale g p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) ∧
          ∀ ε > 0, 1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * min (1 / 2) (ε / 4) ^ 2 →
            ∀ (i : Fin B.count) (p : CuspHalfSpace), p.2.val 0 ≤ 96 →
              ρ ((B.collar i).toFun p) < ε := by
  obtain ⟨δStar, hδStar, hS⟩ := H_smooth_scale.{u}
  refine ⟨min δStar (1 / 100), lt_min hδStar (by norm_num), ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll Λ w n hΛ hw hwc hn hnS hnw hδn hδa
  obtain ⟨ρ, hsmooth, hpos, hbounds, hlip⟩ :=
    hS W g K δ hK hδ0 (hδ.trans (min_le_left _ _)) B hcoll hΛ hw hwc hn hnS hnw hδn hδa
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := by positivity
  refine ⟨ρ, hsmooth, hpos, hbounds, hlip, fun ε hε hδε i p hp => ?_⟩
  exact B.lt_of_le_two_mul_firstVolumeScale (hδ.trans (min_le_right _ _)) hw' hε hδε
    (fun p => (hbounds p).2) i hp

end DifferentialGeometry.Geometry.Collapse
