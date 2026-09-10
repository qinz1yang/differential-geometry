import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornAnnulusCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCurveMinimizer

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_isCompact_subradial_closedBall (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∀ R : ℝ, R < dist (x : UniformSpace.Completion W) H.endpoint →
        IsCompact (Metric.closedBall x R) := by
  obtain ⟨delta, hdelta, htail⟩ := finiteHorn_ball_subset_subend g H 0
  refine ⟨delta / 4, by positivity, ?_⟩
  intro x hx R hR
  have ha : 0 < dist (x : UniformSpace.Completion W) H.endpoint - R := sub_pos.mpr hR
  apply (finiteHorn_isCompact_radial_annulus g H 0 ha).of_isClosed_subset
    Metric.isClosed_closedBall
  intro y hy
  have hyx : dist y x ≤ R := hy
  have hxy : dist x y ≤ R := by simpa only [dist_comm] using hyx
  have hupper : dist (y : UniformSpace.Completion W) H.endpoint < delta := by
    have htri := dist_triangle (y : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq] at htri
    linarith
  refine ⟨subset_closure ⟨y, htail y hupper, rfl⟩, ?_⟩
  have htri := dist_triangle (x : UniformSpace.Completion W)
    (y : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq] at htri
  linarith

variable [T2Space (TangentBundle I3 W)] [SigmaCompactSpace W]

theorem finiteHorn_exists_subradial_minimizer (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∀ y : W, dist x y < dist (x : UniformSpace.Completion W) H.endpoint →
      ∃ R : ℝ, dist x y < R ∧ R < dist (x : UniformSpace.Completion W) H.endpoint ∧
        IsCompact (Metric.closedBall x R) ∧
        ∃ gamma : ℝ → W, gamma 0 = x ∧ gamma 1 = y ∧
          ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma ∧
          (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ Metric.closedBall x R) ∧
          metricPathELength g gamma 0 1 = ENNReal.ofReal (dist x y) ∧
          ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
            metricPathELength g gamma a b =
              ENNReal.ofReal (b - a) * ENNReal.ofReal (dist x y) := by
  obtain ⟨d, hd, hcpt⟩ := finiteHorn_isCompact_subradial_closedBall g H
  refine ⟨d, hd, ?_⟩
  intro x hx y hxy
  let R : ℝ := (dist x y + dist (x : UniformSpace.Completion W) H.endpoint) / 2
  have hxyR : dist x y < R := by dsimp [R]; linarith
  have hR : R < dist (x : UniformSpace.Completion W) H.endpoint := by dsimp [R]; linarith
  have hK := hcpt x hx R hR
  let eta : ℝ := (R - dist x y) / 2
  have heta : 0 < eta := half_pos (sub_pos.mpr hxyR)
  have hfinite : riemannianEDistOf g x y ≠ ⊤ := by
    rw [H.edist_eq_ofReal_dist]
    exact ENNReal.ofReal_ne_top
  have htrap : ∀ gamma : ℝ → W,
      ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) →
      gamma 0 = x → gamma 1 = y →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g x y + ENNReal.ofReal eta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ Metric.closedBall x R := by
    intro gamma hsmooth hstart _hend hnear s hs
    have hprefix := edistOf_le_metricPathELength g hs.1
      (hsmooth.mono (Icc_subset_Icc le_rfl hs.2))
    rw [hstart] at hprefix
    have hbound := (hprefix.trans (metricPathELength_mono g gamma le_rfl hs.2)).trans hnear
    rw [H.edist_eq_ofReal_dist, H.edist_eq_ofReal_dist,
      ← ENNReal.ofReal_add dist_nonneg heta.le] at hbound
    have hreal : dist x (gamma s) ≤ dist x y + eta :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
    change dist (gamma s) x ≤ R
    rw [dist_comm]
    dsimp [eta] at hreal
    linarith
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, hsub⟩ :=
    exists_smooth_minimizer_with_subinterval_lengths g hK heta hfinite htrap
  refine ⟨R, hxyR, hR, hK, gamma, hstart, hend, hsmooth, hmem, ?_, ?_⟩
  · simpa only [H.edist_eq_ofReal_dist] using hlength
  · intro a ha b hb
    simpa only [H.edist_eq_ofReal_dist] using hsub a ha b hb

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
