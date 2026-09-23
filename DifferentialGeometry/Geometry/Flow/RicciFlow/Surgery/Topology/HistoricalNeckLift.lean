import DifferentialGeometry.Geometry.Neck.NormalizedLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Topology.Manifold.ImmersionRange

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

theorem NormalizedNeck.exists_historical_footprint_neck
    {δ₀ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k)
    (hprecision : δ₀ ≤ eps) (a : ℝ) (ha : 24 < a) (hfit : 4 * a < eps⁻¹)
    (htrace : ∀ x ∈ N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
      Nonempty (BackwardPointTrace H first i.castSucc hle x.val)) :
    let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
    let f := H.backwardSurvivorFootprintMap first i hle K
    let hf := H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K
    ∃ hδ : δ₀ ≤ 2 / a,
      ∃ N' : NormalizedNeck (localPullMetric (H.event i).terminal.metric f hf) (2 / a) k,
        2 / a < 1 / 11 ∧ N'.scale = N.scale ∧ N'.sphereMark = N.sphereMark ∧
        f N'.center = N.center ∧
        f ∘ N'.chart = (N.monoDelta hδ N'.delta_lt_one).chart ∧
        N'.normalizedMetric = N.normalizedMetric.restrictOpenOfSubset
          (neckBuffer_le_of_le N.delta_pos hδ) := by
  have ha0 : 0 < a := by linarith
  have heps : 0 < eps := N.delta_pos.trans_le hprecision
  have hmul : (4 * a) * eps < 1 := by
    have h := mul_lt_mul_of_pos_right hfit heps
    rwa [inv_mul_cancel₀ heps.ne'] at h
  have hδ : δ₀ ≤ 2 / a := by
    apply (le_div_iff₀ ha0).mpr
    have hh := mul_le_mul_of_nonneg_right hprecision ha0.le
    nlinarith
  have hsmall : 2 / a < 1 / 11 := (div_lt_iff₀ ha0).mpr (by linarith)
  have hδ1 : 2 / a < 1 := hsmall.trans (by norm_num)
  let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
  let N₀ := N.monoDelta hδ hδ1
  have hinv : (2 / a)⁻¹ = a / 2 := by field_simp
  have hsub : range N₀.chart ⊆ K := by
    rintro x ⟨z, rfl⟩
    refine ⟨TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hδ) z, ?_, rfl⟩
    have hz := z.property
    change -(2 / a)⁻¹ - 1 < z.val.2 ∧ z.val.2 < (2 / a)⁻¹ + 1 at hz
    rw [hinv] at hz
    constructor <;> linarith [hz.1, hz.2]
  have hopen : IsOpen (range N₀.chart) :=
    Manifold.isOpen_range_of_isSmoothEmbedding
      (by simp [ThreeSpace, Module.finrank_prod]) N₀.chart_smooth
  have hinside : range N₀.chart ⊆ interior K := interior_maximal hsub hopen
  let f := H.backwardSurvivorFootprintMap first i hle K
  let hf := H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K
  let Φ := H.backwardSurvivorFootprintLift first i hle K htrace N₀.chart hinside
  have hΦ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ :=
    H.backwardSurvivorFootprintLift_isSmoothEmbedding first i hle K htrace
      N₀.chart hinside N₀.chart_smooth
  have hcomp : f ∘ Φ = N₀.chart :=
    H.backwardSurvivorFootprintMap_comp_lift first i hle K htrace N₀.chart hinside
  let N' := N₀.lift f hf Φ hΦ hcomp
  refine ⟨hδ, N', hsmall, rfl, rfl, ?_, ?_, rfl⟩
  · exact N₀.map_lift_center f hf Φ hΦ hcomp
  · exact N₀.map_lift_chart f hf Φ hΦ hcomp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
