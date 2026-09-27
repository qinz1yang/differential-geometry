import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Manifold Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem eventually_slope_riemannianEDistOf_lt
    [PreconnectedSpace M]
    (g : Real → SmoothRiemannianMetric I M)
    (x y : Real → M) (phi : Real → Real)
    {tau d vx vy : Real}
    (hcontact : phi tau =
      (riemannianEDistOf (I := I) (g tau) (x tau) (y tau)).toReal)
    (hupper :
      (fun s ↦
        (riemannianEDistOf (I := I) (g s) (x tau) (y tau)).toReal)
          ≤ᶠ[𝓝[>] tau] phi)
    (hphi : HasDerivWithinAt phi d (Ioi tau) tau)
    (hx : ∀ eps > 0, ∀ᶠ s in 𝓝[>] tau,
      (riemannianEDistOf (I := I) (g s) (x s) (x tau)).toReal /
          (s - tau) < vx + eps)
    (hy : ∀ eps > 0, ∀ᶠ s in 𝓝[>] tau,
      (riemannianEDistOf (I := I) (g s) (y tau) (y s)).toReal /
          (s - tau) < vy + eps) :
    ∀ eps > 0, ∀ᶠ s in 𝓝[>] tau,
      slope
          (fun u ↦
            (riemannianEDistOf (I := I) (g u) (x u) (y u)).toReal)
          tau s < d + vx + vy + eps := by
  intro eps heps
  let q : Real := eps / 3
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hphiSlope : ∀ᶠ s in 𝓝[>] tau, slope phi tau s < d + q :=
    ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hphi).eventually_lt_const
      (by linarith)
  filter_upwards [hupper, hx q hq, hy q hq, hphiSlope,
    self_mem_nhdsWithin] with s hsupper hsx hsy hsphi htaus
  have hden : 0 < s - tau := sub_pos.mpr htaus
  let F : Real → Real := fun u ↦
    (riemannianEDistOf (I := I) (g u) (x u) (y u)).toReal
  let X : Real :=
    (riemannianEDistOf (I := I) (g s) (x s) (x tau)).toReal
  let Y : Real :=
    (riemannianEDistOf (I := I) (g s) (y tau) (y s)).toReal
  have htri : F s ≤ X +
      (riemannianEDistOf (I := I) (g s) (x tau) (y tau)).toReal + Y := by
    calc
      F s ≤ X +
          (riemannianEDistOf (I := I) (g s) (x tau) (y s)).toReal := by
        simpa only [F, X] using
          riemannianEDistOf_toReal_triangle (g s) (x s) (x tau) (y s)
            (riemannianEDistOf_ne_top (g s) _ _) (riemannianEDistOf_ne_top (g s) _ _)
      _ ≤ X +
          ((riemannianEDistOf (I := I) (g s) (x tau) (y tau)).toReal +
            Y) := by
        have htail :
            (riemannianEDistOf (I := I) (g s) (x tau) (y s)).toReal ≤
              (riemannianEDistOf (I := I) (g s) (x tau) (y tau)).toReal +
                Y := by
          simpa only [Y] using
            riemannianEDistOf_toReal_triangle (g s) (x tau) (y tau) (y s)
              (riemannianEDistOf_ne_top (g s) _ _) (riemannianEDistOf_ne_top (g s) _ _)
        linarith
      _ = X +
          (riemannianEDistOf (I := I) (g s) (x tau) (y tau)).toReal + Y := by
        ring
  have hmove : F s ≤ X + phi s + Y := by
    exact htri.trans (by gcongr)
  have hFtau : F tau = phi tau := by
    exact hcontact.symm
  have hslope : slope F tau s ≤
      X / (s - tau) + slope phi tau s + Y / (s - tau) := by
    rw [slope_def_field, hFtau]
    have hdiv := (div_le_div_iff_of_pos_right hden).2
      (sub_le_sub_right hmove (phi tau))
    rw [slope_def_field]
    calc
      (F s - phi tau) / (s - tau) ≤
          (X + phi s + Y - phi tau) / (s - tau) := hdiv
      _ = X / (s - tau) + (phi s - phi tau) / (s - tau) +
          Y / (s - tau) := by ring
  change slope F tau s < d + vx + vy + eps
  calc
    slope F tau s ≤
        X / (s - tau) + slope phi tau s + Y / (s - tau) := hslope
    _ < (vx + q) + (d + q) + (vy + q) := by
      dsimp only [X, Y]
      linarith
    _ ≤ d + vx + vy + eps := by
      dsimp only [q]
      linarith
end DifferentialGeometry
