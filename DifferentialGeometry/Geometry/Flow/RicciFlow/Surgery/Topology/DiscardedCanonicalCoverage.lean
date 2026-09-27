import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCoreGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingModelCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalCapture
import DifferentialGeometry.Geometry.Neck.ScalarRetainedCore

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_scalar_gt_on_closed_set
    (g : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C*G.flow.scalar t x^2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {F : Set P.Carrier} (hF : IsClosed F) {Q L : ℝ} (hQL : Q < L)
    (hlower : ∀ x : G.terminalRegularOpen, x.val ∈ F → L < metricScalarAt g.metric x) :
    ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s, ∀ x ∈ F, Q < G.flow.scalar t x := by
  obtain ⟨K,hK,hKreg,d0,hd0,hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels hq hbound hPhi hpinch Q
  let K' : Set G.terminalRegularOpen := Subtype.val ⁻¹' (K ∩ F)
  have hK' : IsCompact K' := _root_.Topology.IsInducing.subtypeVal.isCompact_preimage'
    (hK.inter_right hF) (fun x hx => ⟨⟨x,hKreg hx.1⟩,rfl⟩)
  have hclose := g.eventually_scalar_close_on_compact hK' (sub_pos.mpr hQL)
  obtain ⟨d1,hd1,hclose'⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp hclose
  refine ⟨max d0 d1,⟨hd0.1.trans (le_max_left _ _),max_lt hd0.2 hd1.2⟩,?_⟩
  intro t ht x hx
  by_contra hnot
  have hxQ : G.flow.scalar t x ≤ Q := le_of_not_gt hnot
  have hxK : x ∈ K := hcapture t ⟨(le_max_left _ _).trans_lt ht.1,ht.2⟩ x hxQ
  let y : G.terminalRegularOpen := ⟨x,hKreg hxK⟩
  have hyK : y ∈ K' := ⟨hxK,hx⟩
  have hh := (abs_lt.mp (hclose' ⟨(le_max_right _ _).trans_lt ht.1,ht.2⟩ y hyK)).1
  have hl := hlower y hx
  change -(L-Q) < G.flow.scalar t x - metricScalarAt g.metric y at hh
  linarith

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem TerminalLimitMetric.eventually_canonical_on_discarded_core
    (g : G.TerminalLimitMetric) {eps C1 C2 Q : ℝ} (hQ : 0 < Q) (hC2 : 0 ≤ C2)
    (hcanonical : ∀ x : P.Carrier, ∀ t ∈ Ico a s, Q ≤ G.flow.scalar t x →
      Nonempty (CanonicalWitness G.flow eps C1 C2 x t))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {ι : Type*} [Finite ι] {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i)
    (f : ∀ i, bufferedCylinder (δ i) → P.Carrier)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (L : ℝ) (hQL : Q < L) :
    ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
      ∀ z : cutCore f, z ∈ discardedCore f (scalarSublevelComponents G.terminalRegularOpen g.metric f L) →
        Q < G.flow.scalar t z.val ∧ Nonempty (CanonicalWitness G.flow eps C1 C2 z.val t) := by
  let : LocallyPathConnectedSpace P.Carrier :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners ThreeModel
  let R := scalarSublevelComponents G.terminalRegularOpen g.metric f L
  let F := (Subtype.val : cutCore f → P.Carrier) '' discardedCore f R
  have hc : IsCompact F := ((isCompact_retained_discardedCore hδ f hf hdisj R).2).image continuous_subtype_val
  have hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, Q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤
        (⟨C2,hC2⟩ : ℝ≥0)*G.flow.scalar t x^2 := by
    intro x t ht hhigh
    exact (hcanonical x t ⟨ht.1.le,ht.2⟩ hhigh.le).some.time_derivative
  have hlow : ∀ x : G.terminalRegularOpen, x.val ∈ F → L < metricScalarAt g.metric x := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := hx
    by_contra hnot
    have hxcore : x.val ∈ cutCore f := hzx ▸ z.property
    have hret : ConnectedComponents.mk z ∈ R :=
      ⟨x,le_of_not_gt hnot,hxcore,congrArg ConnectedComponents.mk (Subtype.ext hzx.symm)⟩
    exact hz hret
  obtain ⟨d,hd,hhigh⟩ := g.eventually_scalar_gt_on_closed_set hQ hbound hPhi hpinch hc.isClosed hQL hlow
  refine ⟨d,hd,?_⟩
  intro t ht z hz
  have h := hhigh t ht z.val ⟨z,hz,rfl⟩
  exact ⟨h,hcanonical z.val t ⟨hd.1.trans ht.1.le,ht.2⟩ h.le⟩

theorem TerminalLimitMetric.exists_canonical_threshold_discarded_core
    (g : G.TerminalLimitMetric)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 Q : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < Q ∧
        ∀ {ι : Type*} [Finite ι] {δ : ι → ℝ} (_ : ∀ i, 0 < δ i)
          (f : ∀ i, bufferedCylinder (δ i) → P.Carrier)
          (_ : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
          (_ : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
          (L : ℝ), Q < L →
          ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
            ∀ z : cutCore f, z ∈ discardedCore f (scalarSublevelComponents G.terminalRegularOpen g.metric f L) →
              Q < G.flow.scalar t z.val ∧ Nonempty (CanonicalWitness G.flow eps C1 C2 z.val t) := by
  obtain ⟨epsCan,hepsCan,hall⟩ := G.exists_all_point_canonical_neighborhoods
  refine ⟨epsCan,hepsCan,?_⟩
  intro eps heps hsmall
  obtain ⟨C1,C2,Q,hC1,hC2,hQ,hcanonical⟩ := hall eps heps hsmall
  refine ⟨C1,C2,Q,hC1,hC2,hQ,?_⟩
  intro ι _ δ hδ f hf hdisj L hQL
  exact g.eventually_canonical_on_discarded_core hQ (zero_le_one.trans hC2) hcanonical
    hPhi hpinch hδ f hf hdisj L hQL

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
private theorem exists_late_scalar_gt_on_discarded_core_of_pinching
    {q0 Q : ℝ} {Ctime : ℝ≥0} (hq0 : 0 < q0)
    (hbound : ∀ x : (H.stage i.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), q0 < (H.event i).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤
          Ctime * (H.event i).incoming.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative (H.event i).incoming.flow
      (Ico (H.time i.castSucc) (H.time i.succ)) Phi)
    (hprotected : Q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ),
        ∀ z : (H.event i).transition.trace.tubes.core,
          z ∉ (H.event i).transition.trace.retainedCore →
            Q < (H.event i).incoming.flow.scalar t z.val := by
  let _ := (H.event i).transition.core_compact
  let F := Subtype.val '' (H.event i).transition.trace.retainedCoreᶜ
  have hF : IsCompact F := (H.event i).transition.trace.isClopen_retainedCore.compl.isClosed.isCompact.image
    continuous_subtype_val
  have hlow : ∀ x : (H.event i).incoming.terminalRegularOpen,
      x.val ∈ F → ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
        metricScalarAt (H.event i).terminal.metric x := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hxcore : x.val ∈ (H.event i).transition.trace.tubes.core := hzx ▸ z.property
    apply G.scalar_gt_protected_of_not_mem_retainedCore x hxcore
    exact (Subtype.ext hzx : z = ⟨x.val, hxcore⟩) ▸ hz
  obtain ⟨d, hd, hhigh⟩ := (H.event i).terminal.eventually_scalar_gt_on_closed_set
    hq0 hbound hPhi hpinch hF.isClosed hprotected hlow
  refine ⟨d, hd, ?_⟩
  intro t ht z hz
  exact hhigh t ht z.val ⟨z, hz, rfl⟩

include G in
theorem exists_late_scalar_gt_on_discarded_core
    {q0 Q : ℝ} {Ctime : ℝ≥0} (hq0 : 0 < q0)
    (hbound : ∀ x : (H.stage i.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), q0 < (H.event i).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤
          Ctime * (H.event i).incoming.flow.scalar t x ^ 2)
    (hprotected : Q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ),
        ∀ z : (H.event i).transition.trace.tubes.core,
          z ∉ (H.event i).transition.trace.retainedCore →
            Q < (H.event i).incoming.flow.scalar t z.val := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      (H.event i).incoming.lt (H.event i).incoming.flow (H.event i).incoming.equation
      (by simp [ThreeSpace])
  exact G.exists_late_scalar_gt_on_discarded_core_of_pinching hq0 hbound hPhi hpinch hprotected


include G in
theorem exists_late_canonical_on_discarded_core_with_cap_neck_charts_of_canonical_neighborhoods
    {eps C1 C2 Q : ℝ} {Ctime : ℝ≥0} (hQ : 0 < Q)
    (hcanonical : ∀ x : (H.stage i.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), Q < (H.event i).incoming.flow.scalar t x →
        ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 x t,
          W.capTubeHasNeckChart eps)
    (hbound : ∀ x : (H.stage i.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
        Q < (H.event i).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤
            Ctime * (H.event i).incoming.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative (H.event i).incoming.flow
      (Ico (H.time i.castSucc) (H.time i.succ)) Phi)
    (hprotected : Q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ),
        ∀ z : (H.event i).transition.trace.tubes.core,
          z ∉ (H.event i).transition.trace.retainedCore →
            Q < (H.event i).incoming.flow.scalar t z.val ∧
              ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 z.val t,
                W.capTubeHasNeckChart eps := by
  obtain ⟨d, hd, hhigh⟩ :=
    G.exists_late_scalar_gt_on_discarded_core_of_pinching hQ hbound hPhi hpinch hprotected
  refine ⟨d, hd, ?_⟩
  intro t ht z hz
  have h := hhigh t ht z hz
  exact ⟨h, hcanonical z.val t ⟨hd.1.trans_lt ht.1, ht.2⟩ h⟩

include G in
theorem exists_late_canonical_on_discarded_core_with_cap_neck_charts
    {eps C1 C2 Q : ℝ} {Ctime : ℝ≥0} (hQ : 0 < Q)
    (hcanonical : ∀ x : (H.stage i.castSucc).Carrier,
      ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ), Q ≤ (H.event i).incoming.flow.scalar t x →
        ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 x t,
          W.capTubeHasNeckChart eps)
    (hbound : ∀ x : (H.stage i.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
        Q < (H.event i).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤
            Ctime * (H.event i).incoming.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative (H.event i).incoming.flow
      (Ico (H.time i.castSucc) (H.time i.succ)) Phi)
    (hprotected : Q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ),
        ∀ z : (H.event i).transition.trace.tubes.core,
          z ∉ (H.event i).transition.trace.retainedCore →
            Q < (H.event i).incoming.flow.scalar t z.val ∧
              ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 z.val t,
                W.capTubeHasNeckChart eps := by
  exact exists_late_canonical_on_discarded_core_with_cap_neck_charts_of_canonical_neighborhoods G
    hQ (fun x t ht hscalar => hcanonical x t ⟨ht.1.le, ht.2⟩ hscalar.le) hbound
      hPhi hpinch hprotected

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
