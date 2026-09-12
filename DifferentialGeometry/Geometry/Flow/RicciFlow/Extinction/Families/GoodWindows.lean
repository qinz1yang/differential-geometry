import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

theorem rfs_ramp_small_angle (g : SmoothRiemannianMetric I Q)
    (c : ProductCurve Q) (lambda t ell K : ℝ) (hlambda : 0 < lambda)
    (hell : 0 < ell) (hK : 0 < K) (hdegree : c.degree = 1)
    (hsmooth : c.SmoothOn (I := I) {t})
    (hramp : c.IsRampOn (fun _ => g) lambda {t})
    (hlength : ell ≤ c.length (fun _ => g) lambda t)
    (hcurvature : ∀ x, c.curvature (fun _ => g) lambda x t ≤ K) :
    ∀ x, c.angle (fun _ => g) lambda x t ≤ 2 * lambda / ell + 2 * Real.sqrt (K * lambda) := by
  sorry


def localRegularityDelta (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℝ :=
  K.delta

def localRegularityRadius (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℝ :=
  K.radius

def localRegularityCoefficient (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℕ → ℝ :=
  K.coefficient


def goodWindowUnion (starts : Finset ℝ) (d : ℝ) : Set ℝ :=
  {t | ∃ w ∈ starts, t ∈ Icc (w + 5 * d / 8) (w + 7 * d / 8)}

theorem rfs_finite_good_windows (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀) :
    let delta := localRegularityDelta B L₀ Theta₀ K
    let r₀ := localRegularityRadius B L₀ Theta₀ K
    let areg := localRegularityCoefficient B L₀ Theta₀ K 0
    let C_E := Real.exp (B.B₀ * (b - a)) * L₀
    ∀ ell threshold : ℝ, 0 < ell → 0 < threshold →
      let r := min r₀ (min (ell / 2) (delta ^ 2 / threshold))
      let d := delta * r ^ 2
      d < b - a →
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b, ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          (∀ w ∈ starts, w ∈ Icc a (b - d) ∧ c.energy B.family.metric lambda w ≤ threshold) ∧
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤ ENNReal.ofReal (d + C_E / threshold) ∧
          (∀ x t, t ∈ goodWindowUnion starts d →
            c.curvature B.family.metric lambda x t ≤ Real.sqrt (2 * areg / d)) ∧
          ∀ w ∈ starts, Icc (w + 5 * d / 8) (w + 7 * d / 8) ⊆ Ioo (w + d / 2) (w + d) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
