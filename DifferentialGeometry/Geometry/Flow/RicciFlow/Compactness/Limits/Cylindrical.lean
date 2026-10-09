import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.CylinderPinchingLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.TerminalCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ShrinkingCylinderIsometries

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Set Filter Bundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

variable {δ : ℕ → ℝ}

theorem exists_subsequence_converges_to_shrinkingCylinder_of_neck_terminal_convergence
    (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {a : ℝ} (ha : a < 0)
    (hslab : Icc a 0 ⊆ D.carrier) (hreg : Ico a 0 ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (hcurv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc a 0, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc a 0 →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ n, ∀ t ∈ Icc a 0, ∀ᶠ i in atTop, ∀ x : neckBuffer (δ n),
      curvatureOperatorLowerBoundAt ((S n i).base.metric t) x
        (metricAlgebraicCurvatureTensorAt ((S n i).base.metric t) x)
        (rescalePinchingFunction (Q (i + N n)) Phi
          (metricScalarAt ((S n i).base.metric t) x)))
    {C : ℝ}
    (hbound : ∀ n, ∀ t ∈ Icc a 0, ∀ x : neckBuffer (δ n), ∀ᶠ i in atTop,
      normSq0S ((S n i).base.metric t) x 4 (metricRm04At ((S n i).base.metric t) x) ≤ C) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc a 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer (δ n)))
            (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η := by
  obtain ⟨rho, hrho, G, hGzero, hGsol, hcone, _, _, hRm, hconv⟩ :=
    exists_global_complete_nonnegative_neck_limit_of_curvature_bound
      hδ hδlim S hS ha hslab hreg hterminal hcurv N hcompat hPhi Q hQpos hQ hpinching hbound
  let T : SolutionOn (I := NeckCylinderModel) (M := NeckCylinder)
      (RealTimeInterval.closed a 0 ha.le) := { base.metric := G }
  have hzero : T.family.metric 0 = Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2) :=
    hGzero.trans roundCylinderMetric_eq_geometry
  have hmodel := metric_eq_shrinkingCylinderMetric_of_terminal_roundCylinderMetric
    T hGsol ha Subset.rfl Subset.rfl hcone
    ⟨100 ^ 2 * (9 * Real.sqrt C) ^ 2, by positivity, hRm⟩ hzero
  refine ⟨rho, hrho, ?_⟩
  intro n K hK p η hη
  obtain ⟨j, hj⟩ := hconv n K hK p η hη
  refine ⟨j, fun i hi t ht => ?_⟩
  have h := hj i hi t ht
  have heq : G t = PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t := hmodel t ht
  rwa [heq] at h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
