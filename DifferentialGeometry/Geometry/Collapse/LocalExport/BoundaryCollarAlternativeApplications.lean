import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarAlternative
import DifferentialGeometry.Geometry.Collapse.RankStrata

/-!
# Consumers of the LC88 export layer

* `BoundaryExportPacket.nonempty_of_hypotheses`: the tree's `boundaryCollapseHypotheses` on a
  connected carrier give an export packet (`2 ≤ K`, `w₀ ≤ 1/6408`, `0 < ε ≤ 1/1000`).
* `BoundaryExportPacket.one_le_scaledSplittingRank` (the LC88 zero-rank exclusion on the
  depth band): for a positive scale `ρ` that is small on the collar (BSA05), every point of
  `e_i{2 ≤ z ≤ 98}` with `5 ≤ η_i ≤ 95` has `ρ`-scaled splitting rank at least one (LC16, `β₁`).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

namespace BoundaryExportPacket

variable {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- The tree's boundary collapse hypotheses give an export packet. -/
theorem nonempty_of_hypotheses (h : boundaryCollapseHypotheses W g K A w₀) (hK : 2 ≤ K)
    (hw : w₀ ≤ 1 / 6408) (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    Nonempty (BoundaryExportPacket W g K A w₀ ε) :=
  nonempty_of_premises (BoundaryCollapsePremises.ofHypotheses h) hK hw hε hε1

/-- **Zero rank excluded on the depth band** (LC88 / KL 16.4 with `β₁ = βs 1`), for the packet's
own height. -/
theorem one_le_scaledSplittingRank (P : BoundaryExportPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (βs : ℕ → ℝ) {γ L : ℝ}
    (hβ : 0 < βs 1) (hβγ : βs 1 < γ) (hγ1 : γ < 1) (hL : 0 ≤ L)
    (hδβ : w₀ ≤ βs 1 ^ 2 / 1000) (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (hsmall : ∀ p ∈ cuspDomain, p.2.val 0 ≤ 98 →
      ρ ((P.cusp.collar i).toFun p) ≤ βs 1 ^ 3 / (2000 * (1 + L)))
    {q₀ : CuspHalfSpace} (hz2 : 2 ≤ q₀.2.val 0) (hz98 : q₀.2.val 0 ≤ 98)
    (h5 : 5 ≤ P.height i ((P.cusp.collar i).toFun q₀))
    (h95 : P.height i ((P.cusp.collar i).toFun q₀) ≤ 95) :
    1 ≤ @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs
      ((P.cusp.collar i).toFun q₀) := by
  have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
  exact @le_splittingRank.{u, 0} W.Carrier
    ((inducedMetricSpace g).rescale (ρ ((P.cusp.collar i).toFun q₀))⁻¹ (inv_pos.mpr (hρ _)))
    ((P.cusp.collar i).toFun q₀) βs 3 1 (by norm_num)
    (P.adapted i (βs 1) γ L (ρ ((P.cusp.collar i).toFun q₀)) q₀ (hρ _) hβ hβγ hγ1 hL hδβ hεβ
      (hsmall q₀ hq₀ hz98) hz2 hz98 h5 h95).1

end BoundaryExportPacket

end DifferentialGeometry.Geometry.Collapse
