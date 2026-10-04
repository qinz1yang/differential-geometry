import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02
import DifferentialGeometry.Geometry.Collapse.RankStrata

/-!
# Consumers of row BCP02

* `NearlyCuspidalBoundary.bcp02_at_scale`: in the `i`-th collar, with ONE BCP01 height `η`, for
  any positive scale function `ρ` that is `≤ β³/(2000(1 + L))` on the collar band (the BSA05
  scale on its late tail, `H_bsa05`), every band point with `5 ≤ η ≤ 95` splits off a line at
  scale `β` in `(W, ρ(p)⁻¹ d_g)`, with the coordinate `(η − η(p))/ρ(p)` (BCP02.a).
* `NearlyCuspidalBoundary.one_le_scaledSplittingRank_bcp02`: hence the `ρ`-scaled splitting rank
  of LC16 is at least one there: the zero stratum is excluded on the band `5 ≤ η ≤ 95`
  (last sentence of BCP02, with `β = β₁`).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- BCP02.a at the scale `ρ(p)` of a scale function that is small on the collar band. -/
theorem NearlyCuspidalBoundary.bcp02_at_scale [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η ((B.collar i).toFun p) - p.2.val 0| < ε) ∧
      ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (β γ L : ℝ), 0 < β → β < γ → γ < 1 → 0 ≤ L →
        δ ≤ β ^ 2 / 1000 → ε ≤ β ^ 2 / 1000 →
        (∀ p ∈ cuspDomain, p.2.val 0 ≤ 98 → ρ ((B.collar i).toFun p) ≤ β ^ 3 / (2000 * (1 + L))) →
        ∀ q₀ : CuspHalfSpace, 2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 →
          5 ≤ η ((B.collar i).toFun q₀) → η ((B.collar i).toFun q₀) ≤ 95 →
          @HasEuclideanSplitting.{u, 0} W.Carrier
            ((inducedMetricSpace g).rescale (ρ ((B.collar i).toFun q₀))⁻¹
              (inv_pos.mpr (hρ _))) ((B.collar i).toFun q₀) 1 β := by
  obtain ⟨η, hη, hηz, hrow⟩ := (B.collar i).bcp02 hK hδ0 hδ hε hε1
  refine ⟨η, hη, hηz, fun ρ hρ β γ L hβ hβγ hγ1 hL hδβ hεβ hsmall q₀ hz2 hz98 h5 h95 => ?_⟩
  have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
  exact (hrow β γ L (ρ ((B.collar i).toFun q₀)) q₀ (hρ _) hβ hβγ hγ1 hL hδβ hεβ
    (hsmall q₀ hq₀ hz98) hz2 hz98 h5 h95).1

/-- The zero stratum is excluded on the collar band `5 ≤ η ≤ 95`: the `ρ`-scaled splitting rank
(LC16, cap `3`) is at least one, for parameters with `β₁ = βs 1`. -/
theorem NearlyCuspidalBoundary.one_le_scaledSplittingRank_bcp02 [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (βs : ℕ → ℝ) (γ L : ℝ), 0 < βs 1 →
        βs 1 < γ → γ < 1 → 0 ≤ L → δ ≤ βs 1 ^ 2 / 1000 → ε ≤ βs 1 ^ 2 / 1000 →
        (∀ p ∈ cuspDomain, p.2.val 0 ≤ 98 →
          ρ ((B.collar i).toFun p) ≤ βs 1 ^ 3 / (2000 * (1 + L))) →
        ∀ q₀ : CuspHalfSpace, 2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 →
          5 ≤ η ((B.collar i).toFun q₀) → η ((B.collar i).toFun q₀) ≤ 95 →
          1 ≤ @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs
            ((B.collar i).toFun q₀) := by
  obtain ⟨η, hη, -, hrow⟩ := B.bcp02_at_scale i hK hδ0 hδ hε hε1
  refine ⟨η, hη, fun ρ hρ βs γ L hβ hβγ hγ1 hL hδβ hεβ hsmall q₀ hz2 hz98 h5 h95 => ?_⟩
  exact @le_splittingRank.{u, 0} W.Carrier
    ((inducedMetricSpace g).rescale (ρ ((B.collar i).toFun q₀))⁻¹ (inv_pos.mpr (hρ _)))
    ((B.collar i).toFun q₀) βs 3 1 (by norm_num)
    (hrow ρ hρ (βs 1) γ L hβ hβγ hγ1 hL hδβ hεβ hsmall q₀ hz2 hz98 h5 h95)

end DifferentialGeometry.Geometry.Collapse
