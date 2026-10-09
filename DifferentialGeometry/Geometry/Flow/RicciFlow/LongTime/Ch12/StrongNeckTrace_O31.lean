import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreBufferRCW_O31
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
# CH12-O31, group 5: regular open backward traces and `hStrong v2` (`[FROZEN v2] CH12-O31 hStrong`)

External review R4 / D-R4-1: the neck branch of `hStrong` must bind the strong-neck solution `S`
to the actual surgery history on the whole window `[t − Q⁻¹, t]`, not only at the terminal time.

`RegularOpenBackwardTrace_O31 H first U` (lead-authorised data structure): every point of the open set
`U` of the last stage of `H` has a `BackwardPointTrace` down to stage `first` (so it crosses every
event in between regularly — surgery may happen outside `U`), and every survivor map
`U → stage j` (`first ≤ j`) is a local diffeomorphism.  Slab identification (one carrier per stage),
`RegularCrossing` compatibility (`BackwardPointTrace.crossing`), uniqueness and restriction /
composition coherence (`BackwardPointTrace.point_unique`, `backwardSurvivorMap_eq_point`) are those
of the tree's survivor maps; at the last stage the map is the inclusion (`atStage_last_O31`).
Inhabitants: `ofBot_O31` (empty `U`), `ofLast_O31` (no backward window, any `U`).
`hStrong_v1_of_v2_O31`: v2 ⇒ the old `[FROZEN] CH12-O23 hStrong`, so every delivered v1 consumer
(O23/O29/O31 G1–G2) is fed from v2; G3/G4 take v2 directly (`NK` instance).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

/-- **Regular open backward trace** of an open set `U` of the last stage of `H` down to stage `first`. -/
structure RegularOpenBackwardTrace_O31 (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (U : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier) : Prop where
  survive : ∀ x ∈ U,
    Nonempty (BackwardPointTrace H first (Fin.last H.eventCount) (Fin.le_last first) x)
  localDiffeo : ∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ Fin.last H.eventCount),
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun x : U =>
      H.backwardSurvivorMap first (Fin.last H.eventCount) (Fin.le_last first) j hj hl
        ⟨x.1, survive x.1 x.2⟩)

namespace RegularOpenBackwardTrace_O31

variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)}
  {U : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier}

/-- The trace map of `U` at stage `j`. -/
def atStage (E : RegularOpenBackwardTrace_O31 H first U) (j : Fin (H.eventCount + 1))
    (hj : first ≤ j) (hl : j ≤ Fin.last H.eventCount) : U → (H.stage j).Carrier := fun x =>
  H.backwardSurvivorMap first (Fin.last H.eventCount) (Fin.le_last first) j hj hl
    ⟨x.1, E.survive x.1 x.2⟩

theorem atStage_isLocalDiffeomorph (E : RegularOpenBackwardTrace_O31 H first U)
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ Fin.last H.eventCount) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (E.atStage j hj hl) :=
  E.localDiffeo j hj hl

/-- At the last stage the trace is the inclusion (`E.atTop = inclusion U`). -/
theorem atStage_last_O31 (E : RegularOpenBackwardTrace_O31 H first U) (x : U) :
    E.atStage (Fin.last H.eventCount) (Fin.le_last first) le_rfl x = x.1 :=
  H.backwardSurvivorMap_last first (Fin.last H.eventCount) (Fin.le_last first) _

/-- Event compatibility: consecutive trace positions are a `RegularCrossing`. -/
theorem atStage_crossing_O31 (E : RegularOpenBackwardTrace_O31 H first U) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) (hl : i.succ ≤ Fin.last H.eventCount) (x : U) :
    (H.event i).RegularCrossing
      (E.atStage i.castSucc hf ((Fin.castSucc_lt_succ (i := i)).le.trans hl) x)
      (E.atStage i.succ (hf.trans (Fin.castSucc_lt_succ (i := i)).le) hl x) :=
  (Classical.choice (E.survive x.1 x.2)).crossing i hf hl

end RegularOpenBackwardTrace_O31

/-- Inhabitant 1 (empty family): the empty open set. -/
theorem ofBot_O31 (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1)) :
    RegularOpenBackwardTrace_O31 H first ⊥ where
  survive x hx := absurd hx (by simp)
  localDiffeo j hj hl x := by
    have hx : x.1 ∈ (⊥ : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier) := x.2
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_bot] at hx
    exact absurd hx (Set.notMem_empty _)

/-- Inhabitant 2 (no backward window): any open set of the last stage, `first = last`; the trace
map is the inclusion. -/
theorem ofLast_O31 (H : ObservedHistory.{u})
    (U : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier) :
    RegularOpenBackwardTrace_O31 H (Fin.last H.eventCount) U where
  survive x _ := ⟨BackwardPointTrace.singleton H (Fin.last H.eventCount) x⟩
  localDiffeo j hj hl := by
    obtain rfl : j = Fin.last H.eventCount := le_antisymm hl hj
    have hfun : (fun x : U => H.backwardSurvivorMap (Fin.last H.eventCount)
        (Fin.last H.eventCount) (Fin.le_last _) (Fin.last H.eventCount) hj hl
        ⟨x.1, ⟨BackwardPointTrace.singleton H (Fin.last H.eventCount) x.1⟩⟩) = Subtype.val :=
      funext fun x => H.backwardSurvivorMap_last _ _ _ _
    rw [hfun]
    exact isLocalDiffeomorph_subtype_val U

end GC.LongTime.Ch12
