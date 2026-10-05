import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroSeparation

/-!
# Local scale control for boundary zero-ball exclusion

The splitting-rank argument consumes scale control only at its actual collar point.
Consequently BSA06's height-96 bound suffices: every witness in a meeting selected
ball has height below 93. No extension of scale control to height 98 is needed.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} [connectedW : ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

theorem BoundaryExportPacket.one_le_rank_of_small_scale
    (P : BoundaryExportPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (βs : ℕ → ℝ)
    (γ L : ℝ) (hβ : 0 < βs 1) (hβγ : βs 1 < γ) (hγ1 : γ < 1) (hL : 0 ≤ L)
    (hδβ : w₀ ≤ βs 1 ^ 2 / 1000) (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (q : CuspHalfSpace) (hz2 : 2 ≤ q.2.val 0) (hz98 : q.2.val 0 ≤ 98)
    (hsmall : ρ ((P.cusp.collar i).toFun q) ≤ βs 1 ^ 3 / (2000 * (1 + L)))
    (h5 : 5 ≤ P.height i ((P.cusp.collar i).toFun q))
    (h95 : P.height i ((P.cusp.collar i).toFun q) ≤ 95) :
    1 ≤ @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs
      ((P.cusp.collar i).toFun q) := by
  have hs := (P.adapted i (βs 1) γ L (ρ ((P.cusp.collar i).toFun q)) q (hρ _)
    hβ hβγ hγ1 hL hδβ hεβ hsmall hz2 hz98 h5 h95).1
  exact @le_splittingRank.{u, 0} W.Carrier
    ((inducedMetricSpace g).rescale (ρ ((P.cusp.collar i).toFun q))⁻¹ (inv_pos.mpr (hρ _)))
    ((P.cusp.collar i).toFun q) βs 3 1 (by norm_num) hs

theorem BoundaryExportPacket.zeroBall_disjoint_enlargedCollar_96
    (P : BoundaryExportPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) (ρ : W.Carrier → ℝ) (hρ : ∀ y, 0 < ρ y) (βs : ℕ → ℝ)
    (γ L : ℝ) (hβ : 0 < βs 1) (hβγ : βs 1 < γ) (hγ1 : γ < 1) (hL : 0 ≤ L)
    (hδβ : w₀ ≤ βs 1 ^ 2 / 1000) (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (hsmall : ∀ q ∈ cuspDomain, q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ βs 1 ^ 3 / (2000 * (1 + L)))
    (z : W.Carrier) (R V n : ℝ) (hV : 0 ≤ V) (hn : 300 * V < n)
    (hR : R ≤ V * ρ z) (hscale : ENNReal.ofReal (n * ρ z) < curvatureRadius g z)
    (hz : ENNReal.ofReal 10 < distanceToBoundary W g z)
    (hzero : ∃ y ∈ riemannianBallOf g z R,
      @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs y = 0) :
    Disjoint (riemannianBallOf g z R)
      ((P.cusp.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92}) := by
  refine Set.disjoint_left.mpr fun x hx hxc => ?_
  obtain ⟨p, hp, rfl⟩ := hxc
  change p.2.val 0 < 92 at hp
  have hn0 : 0 < n := by linarith
  have hbounds := P.zeroBall_curvature_bounds i (hρ z) (by linarith : V < n) hR hscale
    (show p ∈ cuspDomain from by change p.2.val 0 < 100; linarith) hx
  have hr : R < 1 / 100 := hbounds.2.2.trans
    ((div_lt_iff₀ hn0).mpr (by linarith))
  obtain ⟨y, hy, hyzero⟩ := hzero
  obtain ⟨q, hqd, hqy, hq6, hq93, hη5, hη95⟩ :=
    P.small_ball_height_band i hr hz hp hx y hy
  have hrank := P.one_le_rank_of_small_scale i ρ hρ βs γ L hβ hβγ hγ1 hL hδβ hεβ q
    (by linarith) (by linarith) (hsmall q hqd (by linarith))
    (by simpa only [hqy] using hη5.le) (by simpa only [hqy] using hη95.le)
  rw [hqy, hyzero] at hrank
  omega

end DifferentialGeometry.Geometry.Collapse
