import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCap

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

theorem retainedCore_eq_empty_of_isEmpty (X : SmoothCutCapTransition P Q D N)
    [IsEmpty Q.Carrier] : X.trace.retainedCore = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨q, -⟩
  exact isEmptyElim q

theorem retainedCoreOpens_isEmpty (X : SmoothCutCapTransition P Q D N)
    [IsEmpty Q.Carrier] : IsEmpty (X.retainedCoreOpens : Type u) := by
  refine ⟨fun x => ?_⟩
  exact Set.eq_empty_iff_forall_notMem.mp (retainedCore_eq_empty_of_isEmpty X) x.1 x.2

end SmoothCutCapTransition

namespace OrientedThreeStage

variable (P : OrientedThreeStage.{u})

def metricOfIsEmpty [IsEmpty P.Carrier] : P.Metric where
  inner := fun x => isEmptyElim x
  symm := fun x => isEmptyElim x
  pos := fun x => isEmptyElim x
  isVonNBounded := fun x => isEmptyElim x
  contMDiff := fun x => isEmptyElim x

end OrientedThreeStage


namespace TubeSystem

abbrev ofEmptyIndex (M : Type*) [TopologicalSpace M] : TubeSystem M where
  Index := PEmpty
  finiteIndex := inferInstance
  tube := fun a => PEmpty.elim a
  embedding := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

end TubeSystem

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N]

def ofEmptyTubes (h : M ≃ₜ N) (e : N ≃ₜ Q ⊕ D) (hD : Nonempty D) :
    CutCapTopology M Q D N where
  tubes := TubeSystem.ofEmptyIndex M
  capping :=
    { coreInclusion := (⟨(h : M → N), h.continuous_toFun⟩ : C(M, N)).comp
        ⟨Subtype.val, continuous_subtype_val⟩
      coreEmbedding := h.isEmbedding.comp Topology.IsEmbedding.subtypeVal
      cap := fun b => PEmpty.elim b.1
      capEmbedding := fun b => PEmpty.elim b.1
      attaching := fun b => PEmpty.elim b.1
      boundary_eq := fun b => PEmpty.elim b.1
      exhaustive := by
        rw [Set.iUnion_eq_empty.mpr (fun b => PEmpty.elim b.1), Set.union_empty]
        exact Set.range_eq_univ.mpr fun n => by
          obtain ⟨m, rfl⟩ := h.surjective n
          exact ⟨⟨m, by rw [TubeSystem.core_eq_univ_of_isEmpty]; exact Set.mem_univ m⟩, rfl⟩
      core_cap_intersection := fun b => PEmpty.elim b.1
      cap_disjoint := fun b => PEmpty.elim b.1 }
  presentation := e
  nontrivial := Or.inr hD

end CutCapTopology

def emptySumHomeomorph (α : Type*) [TopologicalSpace α] : α ≃ₜ PEmpty ⊕ α where
  toFun := Sum.inr
  invFun := Sum.elim (fun q => PEmpty.elim q) id
  left_inv := fun _ => rfl
  right_inv := by
    rintro (q | a)
    · exact PEmpty.elim q
    · rfl
  continuous_toFun := continuous_inr
  continuous_invFun :=
    Continuous.sumElim (continuous_iff_continuousAt.mpr fun x => isEmptyElim x) continuous_id

def sphereThreeExtinctTrace :
    CutCapTopology sphereThreeStage.Carrier PEmpty sphereThreeStage.Carrier
      sphereThreeStage.Carrier :=
  CutCapTopology.ofEmptyTubes (Homeomorph.refl _)
    (emptySumHomeomorph sphereThreeStage.Carrier) sphereThreeStage_nonempty

theorem sphereThreeExtinctTrace_retainedCore :
    sphereThreeExtinctTrace.retainedCore = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨q, -⟩
  exact isEmptyElim q

theorem exists_sphereThree_extinctTrace :
    ∃ E : CutCapTopology sphereThreeStage.Carrier PEmpty sphereThreeStage.Carrier
        sphereThreeStage.Carrier,
      Nonempty sphereThreeStage.Carrier ∧ E.retainedCore = ∅ :=
  ⟨sphereThreeExtinctTrace, sphereThreeStage_nonempty, sphereThreeExtinctTrace_retainedCore⟩


private theorem localFrame_eq_chartVector (P : OrientedThreeStage.{u}) (p x : P.Carrier)
    (hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (i : Fin 3) :
    (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).localFrame
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i x = P.chartVector p x i := by
  rw [Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
  change _ = (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).symmL ℝ x _
  rw [Trivialization.symmL_apply _ hx]
  simp [Trivialization.basisAt]

theorem OrientedThreeStage.MetricSmoothUpTo.of_jointSmoothOn {P : OrientedThreeStage.{u}}
    {g : ℝ → P.Metric} {J : Set ℝ}
    (h : ∀ t ∈ J, ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × P.Carrier =>
          (⟨q.2, (g q.1).inner q.2⟩ :
            TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
              (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ]
                ℝ)))
        (V ×ˢ univ)) : P.MetricSmoothUpTo g J := by
  intro p t ht
  obtain ⟨V, hV, htV, hsm⟩ := h t ht
  let e := trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hframe : ∀ i : Fin 3, ContMDiffOn ThreeModel ThreeModel.tangent ∞
      (fun x : P.Carrier =>
        (⟨x, e.localFrame b i x⟩ : TangentBundle ThreeModel P.Carrier)) e.baseSet :=
    fun i => (e.isLocalFrameOn_localFrame_baseSet ThreeModel ∞ b).contMDiffOn i
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' p, subset_rfl,
    V, hV, htV,
    (fun z i j => (g z.1).inner z.2 (e.localFrame b i z.2) (e.localFrame b j z.2)), ?_, ?_⟩
  · intro i j
    have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel.tangent ∞
        (fun q : ℝ × P.Carrier =>
          (⟨q.2, e.localFrame b i q.2⟩ : TangentBundle ThreeModel P.Carrier))
        (V ×ˢ e.baseSet) :=
      ContMDiffOn.comp (I := 𝓘(ℝ, ℝ).prod ThreeModel) (I' := ThreeModel)
        (s := V ×ˢ e.baseSet) (hframe i) contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
    have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel.tangent ∞
        (fun q : ℝ × P.Carrier =>
          (⟨q.2, e.localFrame b j q.2⟩ : TangentBundle ThreeModel P.Carrier))
        (V ×ˢ e.baseSet) :=
      ContMDiffOn.comp (I := 𝓘(ℝ, ℝ).prod ThreeModel) (I' := ThreeModel)
        (s := V ×ˢ e.baseSet) (hframe j) contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
    have hsec := ContMDiffOn.clm_bundle_apply₂
      (F₁ := ThreeSpace) (F₂ := ThreeSpace) (F₃ := ℝ)
      (E₁ := TangentSpace ThreeModel) (E₂ := TangentSpace ThreeModel)
      (E₃ := fun _ : P.Carrier => ℝ) (b := Prod.snd)
      (ψ := fun q : ℝ × P.Carrier => (g q.1).inner q.2) (v := fun q => e.localFrame b i q.2)
      (w := fun q => e.localFrame b j q.2)
      (hsm.mono (fun q hq => ⟨hq.1, mem_univ q.2⟩)) hv hw
    intro z hz
    exact (contMDiffWithinAt_totalSpace.mp (hsec z hz)).2
  · intro s _ x hx i j
    have h1 : e.localFrame b i x = P.chartVector p x i := localFrame_eq_chartVector P p x hx i
    have h2 : e.localFrame b j x = P.chartVector p x j := localFrame_eq_chartVector P p x hx j
    change (g s).inner x (e.localFrame b i x) (e.localFrame b j x) =
      (g s).inner x (P.chartVector p x i) (P.chartVector p x j)
    rw [h1, h2]

theorem OrientedThreeStage.MetricSmoothUpTo.const (P : OrientedThreeStage.{u}) (g : P.Metric)
    (J : Set ℝ) : P.MetricSmoothUpTo (fun _ => g) J := by
  intro p t _
  let e := trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hframe : ∀ i : Fin 3, ContMDiffOn ThreeModel ThreeModel.tangent ∞
      (fun x : P.Carrier =>
        (⟨x, e.localFrame b i x⟩ : TangentBundle ThreeModel P.Carrier)) e.baseSet :=
    fun i => (e.isLocalFrameOn_localFrame_baseSet ThreeModel ∞ b).contMDiffOn i
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' p, subset_rfl,
    univ, isOpen_univ, mem_univ t,
    (fun z i j => g.inner z.2 (e.localFrame b i z.2) (e.localFrame b j z.2)), ?_, ?_⟩
  · intro i j
    have hsec := ContMDiffOn.clm_bundle_apply₂
      (F₁ := ThreeSpace) (F₂ := ThreeSpace) (F₃ := ℝ)
      (E₁ := TangentSpace ThreeModel) (E₂ := TangentSpace ThreeModel)
      (E₃ := fun _ : P.Carrier => ℝ) (b := id) (ψ := g.inner)
      (v := fun x : P.Carrier => e.localFrame b i x)
      (w := fun x : P.Carrier => e.localFrame b j x)
      (g.contMDiff.contMDiffOn (s := e.baseSet)) (hframe i) (hframe j)
    have hcomp := ContMDiffOn.comp (I := 𝓘(ℝ, ℝ).prod ThreeModel) (I' := ThreeModel)
      (s := (univ : Set ℝ) ×ˢ e.baseSet)
      hsec contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
    intro z hz
    exact (contMDiffWithinAt_totalSpace.mp (hcomp z hz)).2
  · intro s _ x hx i j
    have h1 : e.localFrame b i x = P.chartVector p x i := localFrame_eq_chartVector P p x hx i
    have h2 : e.localFrame b j x = P.chartVector p x j := localFrame_eq_chartVector P p x hx j
    change g.inner x (e.localFrame b i x) (e.localFrame b j x) =
      g.inner x (P.chartVector p x i) (P.chartVector p x j)
    rw [h1, h2]


namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}}

def ClosedSlab.ofConst (g : P.Metric)
    (hric : ∀ x (v w : TangentSpace ThreeModel x),
      DifferentialGeometry.Geometry.Curvature.ricciTensor (I := ThreeModel) g x v w = 0)
    {a b : ℝ} (hab : a < b) : P.ClosedSlab a b where
  lt := hab
  flow := SolutionOn.const g
    (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed a b hab.le)
  equation := isSolutionOn_const_of_ricciTensor_eq_zero g hric _
  smoothUpTo := MetricSmoothUpTo.const P g (Icc a b)

def IncomingSlab.ofConst (g : P.Metric)
    (hric : ∀ x (v w : TangentSpace ThreeModel x),
      DifferentialGeometry.Geometry.Curvature.ricciTensor (I := ThreeModel) g x v w = 0)
    {a b : ℝ} (hab : a < b) : P.IncomingSlab a b where
  lt := hab
  flow := SolutionOn.const g
    (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen a b hab)
  equation := isSolutionOn_const_of_ricciTensor_eq_zero g hric _
  smoothUpTo := MetricSmoothUpTo.const P g (Ico a b)

theorem exists_incomingSlab_terminalLimitMetric_of_ricciTensor_eq_zero (g : P.Metric)
    (hric : ∀ x (v w : TangentSpace ThreeModel x),
      DifferentialGeometry.Geometry.Curvature.ricciTensor (I := ThreeModel) g x v w = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ G : P.IncomingSlab a b, Nonempty G.TerminalLimitMetric := by
  let G0 := OrientedThreeStage.ClosedSlab.ofConst (P := P) g hric hab
  exact ⟨G0.restrictIncoming le_rfl G0.lt le_rfl,
    ⟨OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric P G0⟩⟩

end OrientedThreeStage

namespace MetricCutCapEvent

variable {P Q D N : OrientedThreeStage.{u}} {a s : ℝ}

def ofEmptyOutput (X : SmoothCutCapTransition P Q D N) [IsEmpty Q.Carrier]
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric) (out : Q.Metric) :
    MetricCutCapEvent P Q a s :=
  let C0 : ChartedSpace (EuclideanHalfSpace 3) (↥(∅ : Set X.trace.tubes.core)) :=
    ChartedSpace.empty (EuclideanHalfSpace 3) (↥(∅ : Set X.trace.tubes.core))
  let S0 : IsManifold (𝓡∂ 3) ∞ (↥(∅ : Set X.trace.tubes.core)) :=
    { compatible := by intro e _ he _; exact he.elim }
  letI := C0
  letI := S0
  { discarded := D
    capped := N
    transition := X
    incoming := G
    terminal := L
    outputMetric := out
    old := ∅
    old_compact := isCompact_empty
    old_retained := Set.empty_subset _
    oldCharts := C0
    oldSmooth := S0
    old_induced :=
      { isImmersion :=
          ⟨PUnit, inferInstance, inferInstance,
            fun (x : ↥(∅ : Set X.trace.tubes.core)) => (x.2 : False).elim⟩
        isEmbedding := Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal }
    oldTerminal :=
      ⟨fun x => (x.2 : False).elim, continuous_iff_continuousAt.mpr fun x => (x.2 : False).elim⟩
    oldTerminal_eq := fun x => (x.2 : False).elim
    oldOutput :=
      ⟨fun x => (x.2 : False).elim, continuous_iff_continuousAt.mpr fun x => (x.2 : False).elim⟩
    oldOutput_eq := fun x => (x.2 : False).elim
    old_metric_eq := fun x => (x.2 : False).elim
    old_contains_outside := fun _ hx _ => by
      rw [SmoothCutCapTransition.retainedCore_eq_empty_of_isEmpty X] at hx
      exact hx
    every_child_meets_old := fun c => by
      obtain ⟨q, -⟩ := ConnectedComponents.surjective_coe c
      exact isEmptyElim q }

theorem nonempty_iff_of_isEmpty_output [IsEmpty Q.Carrier] :
    Nonempty (MetricCutCapEvent P Q a s) ↔
      ∃ (D N : OrientedThreeStage.{u}) (X : SmoothCutCapTransition P Q D N)
        (G : P.IncomingSlab a s),
        Nonempty G.TerminalLimitMetric ∧ X.trace.retainedCore = ∅ := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.discarded, E.capped, E.transition, E.incoming, ⟨E.terminal⟩,
      SmoothCutCapTransition.retainedCore_eq_empty_of_isEmpty E.transition⟩
  · rintro ⟨D, N, X, G, hL, -⟩
    exact ⟨ofEmptyOutput X G hL.some (OrientedThreeStage.metricOfIsEmpty Q)⟩

end MetricCutCapEvent
namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}}

theorem nonempty_metricCutCapEvent_of_isEmpty_output_of_ricciTensor_eq_zero
    {Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) [IsEmpty Q.Carrier]
    (g : P.Metric)
    (hric : ∀ x (v w : TangentSpace ThreeModel x),
      DifferentialGeometry.Geometry.Curvature.ricciTensor (I := ThreeModel) g x v w = 0)
    {a b : ℝ} (hab : a < b) : Nonempty (MetricCutCapEvent P Q a b) := by
  obtain ⟨G, hG⟩ :=
    OrientedThreeStage.exists_incomingSlab_terminalLimitMetric_of_ricciTensor_eq_zero
      (P := P) g hric hab
  exact (MetricCutCapEvent.nonempty_iff_of_isEmpty_output (P := P) (Q := Q)
    (a := a) (s := b)).mpr
    ⟨D, N, X, G, hG, SmoothCutCapTransition.retainedCore_eq_empty_of_isEmpty X⟩


end OrientedThreeStage


namespace RetainedCoreEvent

variable {P Q D N : OrientedThreeStage.{u}} {a s : ℝ}

def ofEmptyOutput (X : SmoothCutCapTransition P Q D N) [IsEmpty Q.Carrier]
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric) (out : Q.Metric) :
    RetainedCoreEvent P Q a s :=
  letI : IsEmpty (X.retainedCoreOpens : Type u) :=
    SmoothCutCapTransition.retainedCoreOpens_isEmpty X
  { discarded := D
    capped := N
    transition := X
    incoming := G
    terminal := L
    outputMetric := out
    oldTerminal :=
      ⟨fun x => isEmptyElim x, continuous_iff_continuousAt.mpr fun x => isEmptyElim x⟩
    oldTerminal_eq := fun x => isEmptyElim x
    oldOutput :=
      ⟨fun x => isEmptyElim x, continuous_iff_continuousAt.mpr fun x => isEmptyElim x⟩
    oldOutput_eq := fun x => isEmptyElim x
    old_metric_eq := fun x _ _ => isEmptyElim x
    old_contains_outside := fun _ hx _ => hx
    every_child_meets_old := fun c => by
      obtain ⟨q, -⟩ := ConnectedComponents.surjective_coe c
      exact isEmptyElim q }

theorem nonempty_iff_of_isEmpty_output [IsEmpty Q.Carrier] :
    Nonempty (RetainedCoreEvent P Q a s) ↔
      ∃ (D N : OrientedThreeStage.{u}) (X : SmoothCutCapTransition P Q D N)
        (G : P.IncomingSlab a s),
        Nonempty G.TerminalLimitMetric ∧ X.trace.retainedCore = ∅ := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.discarded, E.capped, E.transition, E.incoming, ⟨E.terminal⟩,
      SmoothCutCapTransition.retainedCore_eq_empty_of_isEmpty E.transition⟩
  · rintro ⟨D, N, X, G, hL, -⟩
    exact ⟨ofEmptyOutput X G hL.some (OrientedThreeStage.metricOfIsEmpty Q)⟩

end RetainedCoreEvent


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
