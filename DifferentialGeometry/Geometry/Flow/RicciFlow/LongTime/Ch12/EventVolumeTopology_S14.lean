import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

/-- Points of the incoming stage lying in the retained core. -/
def retainedPts_S14 : Set P.Carrier := Subtype.val '' E.transition.trace.retainedCore

/-- The (closed) tube images. -/
def tubeClosure_S14 : Set P.Carrier := ⋃ α, Set.range (E.transition.trace.tubes.tube α)

theorem isClosed_tubeClosure_S14 : IsClosed (tubeClosure_S14 E) := by
  have : Finite E.transition.trace.tubes.Index := inferInstance
  exact isClosed_iUnion_of_finite fun α =>
    (isCompact_range (E.transition.trace.tubes.tube α).continuous).isClosed

theorem tubeClosure_compl_subset_core_S14 :
    (tubeClosure_S14 E)ᶜ ⊆ E.transition.trace.tubes.core := by
  intro p hp hpb
  apply hp
  simp only [mem_iUnion] at hpb
  obtain ⟨α, hα⟩ := hpb
  obtain ⟨z, _, rfl⟩ := hα
  exact mem_iUnion.mpr ⟨α, mem_range_self z⟩

/-- A preconnected subset of the core lies entirely inside the retained core or entirely outside
it. -/
theorem conn_retained_S14 {T : Set P.Carrier} (hT : IsPreconnected T)
    (hTc : T ⊆ E.transition.trace.tubes.core) {x y : P.Carrier} (hx : x ∈ T) (hy : y ∈ T)
    (hxr : x ∈ retainedPts_S14 E) : y ∈ retainedPts_S14 E := by
  have hpc : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp hT
  let g : T → Q.Carrier ⊕ E.discarded.Carrier := fun p =>
    E.transition.trace.presentation (E.transition.trace.capping.coreInclusion ⟨p.1, hTc p.2⟩)
  have hg : Continuous g :=
    E.transition.trace.presentation.continuous.comp
      (E.transition.trace.capping.coreInclusion.continuous.comp
        (continuous_subtype_val.subtype_mk _))
  have hrange : IsPreconnected (range g) := isPreconnected_range hg
  have hcases := hrange.subset_or_subset isOpen_range_inl isOpen_range_inr
    (Set.disjoint_left.mpr (by rintro _ ⟨a, rfl⟩ ⟨b, hb⟩; cases hb)) (by rw [Set.range_inl_union_range_inr]; exact subset_univ _)
  obtain ⟨xx, hxx, rfl⟩ := hxr
  obtain ⟨q, hq⟩ := hxx
  have hgx : g ⟨xx.1, hx⟩ = Sum.inl q := by
    simpa only [g] using hq
  have hleft : range g ⊆ range (Sum.inl : Q.Carrier → _) := by
    rcases hcases with h | h
    · exact h
    · exfalso
      obtain ⟨q', hq'⟩ := h (mem_range_self (⟨xx.1, hx⟩ : T))
      rw [hgx] at hq'
      cases hq'
  obtain ⟨q', hq'⟩ := hleft (mem_range_self (⟨y, hy⟩ : T))
  exact ⟨⟨y, hTc hy⟩, ⟨q', hq'.symm⟩, rfl⟩

/-- Retained core points off the closed tubes. -/
def offTubeRetained_S14 : Set P.Carrier := (tubeClosure_S14 E)ᶜ ∩ retainedPts_S14 E

theorem isOpen_offTubeRetained_S14 [LocallyConnectedSpace P.Carrier] :
    IsOpen (offTubeRetained_S14 E) := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hpU, hpR⟩
  have hU : (tubeClosure_S14 E)ᶜ ∈ 𝓝 p :=
    (isClosed_tubeClosure_S14 E).isOpen_compl.mem_nhds hpU
  obtain ⟨V, ⟨hVo, hpV, hVc⟩, hVU⟩ := (LocallyConnectedSpace.open_connected_basis p).mem_iff.mp hU
  refine Filter.mem_of_superset (hVo.mem_nhds hpV) fun y hy => ?_
  exact ⟨hVU hy, conn_retained_S14 E hVc.isPreconnected
    (hVU.trans (tubeClosure_compl_subset_core_S14 E)) hpV hy hpR⟩

theorem offTubeRetained_subset_old_S14 :
    offTubeRetained_S14 E ⊆ Subtype.val '' E.old := by
  rintro p ⟨hpU, xx, hxx, rfl⟩
  refine ⟨xx, E.old_contains_outside xx hxx fun α hα => hpU ?_, rfl⟩
  exact mem_iUnion.mpr ⟨α, hα.choose, by rw [hα.choose_spec.2]⟩

private local instance sigmaCompactTRO3_S14 {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- The retained core off the closed tubes is mapped isometrically onto an open set of the output:
`T` covers `oldOutput` of every old point off the tubes, and its volume is at most that of the
corresponding open region of the terminal limit. -/
theorem offTube_image_S14 [LocallyConnectedSpace P.Carrier] : ∃ T : Set Q.Carrier,
    riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric T ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
        {y | y.1 ∈ offTubeRetained_S14 E} ∧
    ∀ z : E.old, z.1.1 ∉ tubeClosure_S14 E → E.oldOutput z ∈ T := by
  let W : TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
    ⟨{y | y.1 ∈ offTubeRetained_S14 E},
      (isOpen_offTubeRetained_S14 E).preimage continuous_subtype_val⟩
  have hzW : ∀ z : E.old, z.1.1 ∉ tubeClosure_S14 E → E.oldTerminal z ∈ W := by
    intro z hz
    change (E.oldTerminal z).1 ∈ offTubeRetained_S14 E
    rw [E.oldTerminal_eq]
    exact ⟨hz, z.1, E.old_retained z.2, rfl⟩
  by_cases hne : Nonempty W
  · obtain ⟨x₀⟩ := hne
    have hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old) := by
      intro x hx
      exact interior_maximal (offTubeRetained_subset_old_S14 E) (isOpen_offTubeRetained_S14 E) hx
    obtain ⟨F, hsource, _, hold, hmetric⟩ := E.exists_survivor_partialDiffeomorph W x₀ hW
    let F₁ : PartialDiffeomorph ThreeModel ThreeModel E.incoming.terminalRegularOpen Q.Carrier 1 :=
      { F.toPartialEquiv with
        open_source := F.open_source
        open_target := F.open_target
        contMDiffOn_toFun := F.contMDiffOn_toFun.of_le (by norm_num)
        contMDiffOn_invFun := F.contMDiffOn_invFun.of_le (by norm_num) }
    let : MeasurableSpace E.incoming.terminalRegularOpen := borel _
    have : BorelSpace E.incoming.terminalRegularOpen := ⟨rfl⟩
    have hvol := riemannianVolumeMeasure_image_of_partialIsometry E.terminal.metric E.outputMetric F₁
      (A := (W : Set E.incoming.terminalRegularOpen))
      (fun x hx v w => by
        change x ∈ F.source at hx
        rw [hsource] at hx
        exact (hmetric x hx v w).symm)
      W.isOpen.measurableSet (by change _ ⊆ F.source; rw [hsource])
    refine ⟨F₁ '' (W : Set E.incoming.terminalRegularOpen), hvol.symm.le, ?_⟩
    intro z hz
    refine ⟨E.oldTerminal z, hzW z hz, ?_⟩
    exact hold z (hzW z hz)
  · refine ⟨∅, by simp, fun z hz => ?_⟩
    exact absurd ⟨E.oldTerminal z, hzW z hz⟩ hne

end GC.LongTime.Ch12
