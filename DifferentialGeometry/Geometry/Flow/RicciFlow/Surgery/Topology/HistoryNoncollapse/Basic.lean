import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

/-!
# S-CH11-SHIM shim for `Surgery.Topology.HistoryNoncollapse.Basic` (not a copy of the astra file)

Jui-Hui's chapter-11 branch (`gc/juihuichung/chapter11-astra-20261005`) split this
module out of the fat W8 module(s) below.  In this tree the host module(s) still
contain every public declaration of the astra file with the same signature, so this
shim only re-exports them: the import lines are those of the astra file verbatim,
plus an import of the host.  Modules copied verbatim from astra that import this
path then compile unchanged, without duplicate declarations.
The only declarations are the two `private` helpers of the astra file; they must live
in *this* module because astra users write
`open private ... from ...HistoryNoncollapse.Basic`.  The public declarations are the
host's.  No new public declaration here.

Host module(s) (prefix `DifferentialGeometry.Geometry.Flow.RicciFlow.` omitted):
  `Surgery.Topology.CanonicalNeighborhoodInduction`
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
namespace RetainedCoreHistory
variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u})

private theorem rm_bound_of_stage_eq {K : ObservedHistory.{u}}
    {first last : Fin (K.eventCount + 1)} {hle : first ≤ last} {x : (K.stage last).Carrier}
    (B : BackwardPointTrace K first last hle x) {m m' : Fin (K.eventCount + 1)} (hm : m' = m)
    (h1 : first ≤ m) (h2 : m ≤ last) (h1' : first ≤ m') (h2' : m' ≤ last) (v r : ℝ)
    (h : r ^ 4 * normSq0S (K.stageMetric m' v) (B.point m' h1' h2') 4
      (metricRm04At (K.stageMetric m' v) (B.point m' h1' h2')) ≤ 1) :
    r ^ 4 * normSq0S (K.stageMetric m v) (B.point m h1 h2) 4
      (metricRm04At (K.stageMetric m v) (B.point m h1 h2)) ≤ 1 := by
  subst hm
  exact h

private theorem volume_lower_bound_of_stage_index {κ ρ t₀ : ℝ} (hH : H.NoncollapsedBefore κ ρ t₀)
    (τ : Icc (0 : ℝ) H.toHistory.horizon) (hτ : (τ : ℝ) ≤ t₀)
    (last : Fin (H.eventCount + 1)) (hlast : H.toHistory.activeStage τ = last)
    (p : (H.stage last).Carrier) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (a : Icc (0 : ℝ) H.toHistory.horizon) (hat : a ≤ τ) (ha : (a : ℝ) = (τ : ℝ) - r ^ 2)
    (first : Fin (H.eventCount + 1)) (hfirst : first ≤ H.toHistory.activeStage a)
    (hf : first ≤ last)
    (htrace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric last τ) p r,
      ∃ B : BackwardPointTrace H.toHistory first last hf x,
        (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ τ),
          r ^ 4 * normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (B.point (H.toHistory.activeStage v) (hfirst.trans (H.toHistory.activeStage_mono hav))
              ((H.toHistory.activeStage_mono hvt).trans hlast.le)) 4
            (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              (B.point (H.toHistory.activeStage v)
                (hfirst.trans (H.toHistory.activeStage_mono hav))
                ((H.toHistory.activeStage_mono hvt).trans hlast.le))) ≤ 1) ∧
        ∀ (i : Fin H.eventCount) (hi : H.toHistory.activeStage a ≤ i.castSucc)
          (hil : i.succ ≤ last),
          let y : (H.toHistory.event i).incoming.terminalRegularOpen :=
            ⟨B.point i.castSucc (hfirst.trans hi) (i.castSucc_lt_succ.le.trans hil),
              (B.crossing i (hfirst.trans hi) hil).mem_terminalRegularRegion
                (H.toHistory.event i)⟩;
          r ^ 4 * normSq0S (H.toHistory.event i).terminal.metric y 4
            (metricRm04At (H.toHistory.event i).terminal.metric y) ≤ 1) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stage last).Carrier
        (H.toHistory.stageMetric last τ)
        (riemannianBallOf (H.toHistory.stageMetric last τ) p r) := by
  subst hlast
  refine hH τ p r hτ hrρ ⟨hr, a, hat, ha, fun x hx => ?_⟩
  obtain ⟨B, hobs, hseam⟩ := htrace x hx
  exact ⟨B.restrictFirst hfirst (H.toHistory.activeStage_mono hat), hobs,
    fun i hi hil => hseam i hi hil⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
