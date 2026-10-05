import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapBCP03Unit
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleSmooth

/-!
# Consumers of the BCG01 binding

* `BoundaryCollarPacket.exists_scale_bcg01`: with BSA05's smooth scale `ρ` (`H_bsa05`, on its
  uniform tail, for the packet's own boundary and volume premises), every original reference
  domain `B(p_a, C_a ρ(p_a))` meeting the `b`th closed boundary support has `ρ(p_a) < 2 r_∂` and
  lies in `{19 < η_b < 91}` (BCG01.b), for every `r_∂ > 0` on the further BSA05 tail.
* `BoundaryCollarPacket.product_or_supports_subsingleton`: on a connected carrier, BCP03's
  alternative for the packet: the carrier is `T² × [0, 1]` with its two labels, or at most one
  closed boundary support meets any set of diameter `< 1`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **BCG01.b with BSA05's scale.** -/
theorem BoundaryCollarPacket.exists_scale_bcg01 :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ ε : ℝ)
      (P : BoundaryCollarPacket W g K A w₀ ε), 2 ≤ K → w₀ ≤ δStar → ε ≤ 1 / 4 →
      ∀ {Λ w n : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
        3 ≤ n → 2 * (1 + 2 / Λ) < n → n⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) →
        w₀ * (16 * n ^ 4) ≤ 1 →
        1000 * w₀ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 →
        ∃ ρ : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) ∧
          ∀ r > 0, 1000 * w₀ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
            ∀ C L : ℝ, 0 < L → C ≤ 95 / 100 * L → Λ * C ≤ 1 / 2 → r * (1000 * L) < 1 →
              ∀ (p : W.Carrier) (b : Fin P.cusp.count),
                (∃ x ∈ tsupport (P.block b),
                  riemannianEDistOf g p x < ENNReal.ofReal (C * ρ p)) →
                ρ p < 2 * r ∧ ∀ y, riemannianEDistOf g p y < ENNReal.ofReal (C * ρ p) →
                  ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧ 19 < q.2.val 0 ∧
                    q.2.val 0 < 91 ∧ 19 < P.height b y ∧ P.height b y < 91 := by
  obtain ⟨δStar, hδStar, hS⟩ := H_bsa05.{u}
  refine ⟨δStar, hδStar, ?_⟩
  intro W _ g K A w₀ ε P hK hw hε Λ w n hΛ hw0 hwc hn hnS hnw hδn hδa
  have hw₀ : 0 ≤ w₀ := (P.cusp.collar ⟨0, P.cusp.count_pos⟩).delta_nonneg
  obtain ⟨ρ, hρs, hρ, -, hlip, hsmall⟩ :=
    hS W g K w₀ hK hw₀ hw P.cusp P.volume hΛ hw0 hwc hn hnS hnw hδn hδa
  refine ⟨ρ, hρs, hρ, hlip, fun r hr hδr C L hL hC hΛC hrL p b hmeet => ?_⟩
  exact P.bcg01_reference_domain hε hρ hΛ.le hlip (hsmall r hr hδr) hL hC hΛC hrL hmeet

/-- **BCP03's alternative for the packet.** On a connected carrier: either `W ≅ T² × [0, 1]`
with two distinct labelled boundary components at the ends, or at most one closed boundary
support meets any set of diameter `< 1` (tolerance `ε ≤ 1/2`). -/
theorem BoundaryCollarPacket.product_or_supports_subsingleton {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
    {A : ℝ → ℝ} {w₀ ε : ℝ} (P : BoundaryCollarPacket W g K A w₀ ε) (hK : 1 ≤ K)
    (hε : ε ≤ 1 / 2) :
    (∃ (i j : Fin P.cusp.count), i ≠ j ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
        (∀ p, D p ∈ P.cusp.component i ↔ p.2.1 = 0) ∧
          ∀ p, D p ∈ P.cusp.component j ↔ p.2.1 = 1) ∨
    ∀ D : Set W.Carrier, (∀ x ∈ D, ∀ y ∈ D, riemannianEDistOf g x y < ENNReal.ofReal 1) →
      {b : Fin P.cusp.count | (tsupport (P.block b) ∩ D).Nonempty}.Subsingleton := by
  have hw₀ : 0 ≤ w₀ := (P.cusp.collar ⟨0, P.cusp.count_pos⟩).delta_nonneg
  rcases P.cusp.bcp03_unit hK hw₀ (by linarith [P.threshold]) with hprod | hdisj
  · exact Or.inl hprod
  · exact Or.inr fun D hD => P.subsingleton_supports_of_edist_lt_one hε
      (fun i j hij => (hdisj i j hij).1) hD

end DifferentialGeometry.Geometry.Collapse
