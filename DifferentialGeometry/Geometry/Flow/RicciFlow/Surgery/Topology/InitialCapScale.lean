import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_uniform_identified_initial_pinching_and_static_cap_scale
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    {c ρ q₀ C₀ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hC₀ : 0 < C₀) :
    ∃ a₀ δ₀ : ℝ, 0 < a₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      ∀ p : CutoffParameters, p.recenterConstant ≤ c →
      ∀ records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p,
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
        ∀ i : Fin H.eventCount, p.delta (H.time i.succ) ≤ δ₀ →
          p.neckRadius (H.time i.succ) ≤ ρ →
          ∀ b : (H.event i).RetainedBoundaryIndex,
            q₀ ≤ C₀ * ((records i).static b).neck.scale ∧
              1 ≤ a₀ * ((records i).static b).neck.scale := by
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  let K := max (q₀ / C₀) a₀⁻¹
  have hK : 0 < K := (inv_pos.mpr ha₀).trans_le (le_max_right _ _)
  obtain ⟨δ₀, hδ₀, hscale⟩ := exists_uniform_static_cap_scale_lower_bound c ρ K hc hρ hK
  refine ⟨a₀, δ₀, ha₀, hδ₀, ?_⟩
  intro H hH p hpc records
  obtain ⟨hfixed, hscalar⟩ := hinitial H hH
  refine ⟨hfixed, hscalar, ?_⟩
  intro i hδ hρp b
  have hcap := hscale H i p hpc hδ hρp (records i) b
  have hq : q₀ / C₀ ≤ ((records i).static b).neck.scale :=
    (le_max_left _ _).trans hcap.le
  have ha : a₀⁻¹ ≤ ((records i).static b).neck.scale :=
    (le_max_right _ _).trans hcap.le
  constructor
  · have hh := (div_le_iff₀ hC₀).mp hq
    simpa only [mul_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left ha ha₀.le
    simpa only [mul_inv_cancel₀ ha₀.ne'] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
