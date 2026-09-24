import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : ℕ → Type u} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace ThreeSpace (M n)]
  [∀ n, IsManifold ThreeModel ∞ (M n)]

theorem NormalizedNeck.metricCInfConvergenceOn_restrict_of_precision_tendsto_zero
    {g : ∀ n, SmoothRiemannianMetric ThreeModel (M n)} {eps : ℕ → ℝ} {k : ℕ → ℕ}
    (N : ∀ n, NormalizedNeck (g n) (eps n) (k n))
    {δ : ℝ} (hprecision : ∀ n, eps n ≤ δ)
    (heps : Tendsto eps atTop (𝓝 0)) (hk : Tendsto k atTop atTop) :
    ∀ K : Set (neckBuffer δ), MetricCInfConvergenceOn K
      (fun n => (N n).normalizedMetric.restrictOpenOfSubset
        (neckBuffer_le_of_le (N n).delta_pos (hprecision n)))
      (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) := by
  have hδ : 0 < δ := (N 0).delta_pos.trans_le (hprecision 0)
  intro K p η hη
  have hsmall : ∀ᶠ n in atTop, eps n < min (η / 2) ((δ⁻¹ + 1)⁻¹) :=
    heps.eventually_lt_const (lt_min (by positivity) (by positivity))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hsmall.and (hk.eventually_ge_atTop p))
  refine ⟨n₀, fun n hn => ?_⟩
  have hepsη : eps n < η / 2 := (hn₀ n hn).1.trans_le (min_le_left _ _)
  have hwidth : δ⁻¹ + 1 < (eps n)⁻¹ := by
    have hepswidth : eps n < (δ⁻¹ + 1)⁻¹ :=
      (hn₀ n hn).1.trans_le (min_le_right _ _)
    have hinv := (inv_lt_inv₀ (by positivity : 0 < (δ⁻¹ + 1)⁻¹)
      (N n).delta_pos).mpr hepswidth
    simpa only [inv_inv] using hinv
  have hreference : (roundCylinderMetric.restrictOpen (neckBuffer (eps n))).restrictOpenOfSubset
      (neckBuffer_le_of_le (N n).delta_pos (hprecision n)) =
      roundCylinderMetric.restrictOpen (neckBuffer δ) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  have hpoint (a : ℕ) (ha : a ≤ p) (x : neckBuffer δ) :
      metricDerivNorm a
        ((N n).normalizedMetric.restrictOpenOfSubset
          (neckBuffer_le_of_le (N n).delta_pos (hprecision n)))
        (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)) x ≤ η / 2 := by
    let : SigmaCompactSpace (neckBuffer (eps n)) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer (eps n)).isOpen)
    rw [← hreference, metricDerivNorm_flat]
    apply le_trans (derivNorm_le_sup (isCompact_neckClosedTest (eps n))
      (ha.trans (hn₀ n hn).2) _ _ _ ?_) (le_trans (N n).closeness.le hepsη.le)
    have hx := x.property
    change -(eps n)⁻¹ ≤ x.val.2 ∧ x.val.2 ≤ (eps n)⁻¹
    change -δ⁻¹ - 1 < x.val.2 ∧ x.val.2 < δ⁻¹ + 1 at hx
    constructor <;> linarith
  exact lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ _
    (η / 2) (by positivity) (fun a ha x _ => hpoint a ha x)) (by linarith)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
