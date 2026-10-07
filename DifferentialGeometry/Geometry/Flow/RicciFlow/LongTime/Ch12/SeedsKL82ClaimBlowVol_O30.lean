import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimSelVol_O30
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# CH12-O30, G3b-4: the volume input of the blow-up from the local volume bound

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5 (blow-up step of the
proof of claim (C)); not a verbatim transcription.  The reference PDFs named in AGENTS.md are not
on this machine.

`blowup_volume_of_local_O30` rescales a local volume lower bound `vol B(x, ρ) ≥ c ρ³`
(`x ∈ B(p, r1)`, `ρ ≤ r2`, the conclusion of `kl82_selected_volume_O30` with `r1 = 15r0/32`,
`r2 = 17r0/32`) to the metric `Q g`: every point of the `Q g`-closed ball `B̄(y, D)` and every
radius `s ≤ D` satisfy `vol_{Qg} B_{Qg}(x, s) ≥ c s³`, provided `B_g(y, D/√Q) ⊆ B_g(p, r1)`
and `D/√Q ≤ r2`.  This is the `hvol` input of `blowup_core_local_O25`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

/-- **G3b-4**: rescaled volume lower bound on the blow-up balls. -/
theorem blowup_volume_of_local_O30 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p y : M) {Q c D r1 r2 : ℝ} (hQ : 0 < Q)
    (hy : riemannianEDistOf g p y < ENNReal.ofReal (r1 - D / Real.sqrt Q))
    (hDr2 : D / Real.sqrt Q ≤ r2)
    (hvol : ∀ x ∈ riemannianBallOf g p r1, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r2 →
      ENNReal.ofReal (c * ρ ^ 3) ≤ ballVolume g x ρ) :
    ∀ x ∈ riemannianClosedBallOf (scaleMetric Q hQ g) y D, ∀ s : ℝ, 0 < s → s ≤ D →
      ENNReal.ofReal (c * s ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel M (scaleMetric Q hQ g)
          (riemannianBallOf (scaleMetric Q hQ g) x s) := by
  intro x hx s hs hsD
  set σ : ℝ := Real.sqrt Q with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr hQ
  have hD : 0 < D := hs.trans_le hsD
  have hDσ : σ * (D / σ) = D := mul_div_cancel₀ D hσ.ne'
  have hsσ : σ * (s / σ) = s := mul_div_cancel₀ s hσ.ne'
  -- `x` is in the `g`-closed ball of radius `D/√Q` around `y`
  have hx' : x ∈ riemannianClosedBallOf g y (D / σ) := by
    rw [← riemannianClosedBallOf_scaleMetric Q hQ g y (D / σ), hDσ]
    exact hx
  have hyx : riemannianEDistOf g y x ≤ ENNReal.ofReal (D / σ) := hx'
  have hr1 : 0 < r1 - D / σ := by
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hneg)] at hy
    exact (ENNReal.not_lt_zero hy).elim
  have hpx : x ∈ riemannianBallOf g p r1 := by
    change riemannianEDistOf g p x < ENNReal.ofReal r1
    calc riemannianEDistOf g p x ≤ riemannianEDistOf g p y + riemannianEDistOf g y x :=
          riemannianEDistOf_triangle g p y x
      _ ≤ riemannianEDistOf g p y + ENNReal.ofReal (D / σ) := add_le_add_right hyx _
      _ < ENNReal.ofReal (r1 - D / σ) + ENNReal.ofReal (D / σ) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hy
      _ = ENNReal.ofReal r1 := by
          rw [← ENNReal.ofReal_add hr1.le (by positivity)]
          congr 1
          ring
  have hsr : s / σ ≤ r2 := (div_le_div_of_nonneg_right hsD hσ.le).trans hDr2
  have h := hvol x hpx (s / σ) (div_pos hs hσ) hsr
  have h' := (le_ballVolume_scaleMetric_iff finrank_euclideanSpace_fin Q hQ).mpr h
  rw [hsσ] at h'
  exact h'

end GC.LongTime.Ch12
