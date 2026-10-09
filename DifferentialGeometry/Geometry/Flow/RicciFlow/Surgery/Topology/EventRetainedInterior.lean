import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedMaps
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInteriorImage

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_oldTerminal_eq_of_mem_interior_old
    (x : E.incoming.terminalRegularOpen)
    (hx : x.1 ∈ interior (Subtype.val '' E.old)) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    ∃ w : E.old, E.oldTerminal w = x ∧ (𝓡∂ 3).IsInteriorPoint w ∧
      E.RegularCrossing x.1 (E.oldOutput w) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  obtain ⟨z, hz, hzx⟩ := interior_subset hx
  let w : E.old := ⟨z, hz⟩
  have hrange : Set.range (fun y : E.old => (y.1.1 : P.Carrier)) =
      Subtype.val '' E.old := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hw : (𝓡∂ 3).IsInteriorPoint w :=
    E.old_induced.isInteriorPoint_of_mem_interior_range rfl (by
      change z.1 ∈ interior _
      rw [hrange, hzx]
      exact hx) BoundarylessManifold.isInteriorPoint
  exact ⟨w, Subtype.ext ((E.oldTerminal_eq w).trans hzx), hw, w, hw, hzx, rfl⟩

theorem exists_oldTerminal_eq_of_mem_interior_retained
    (hOld : E.old = E.transition.trace.retainedCore)
    (x : E.incoming.terminalRegularOpen)
    (hx : x.1 ∈ interior (Subtype.val '' E.transition.trace.retainedCore)) :
    ∃ z : E.old, E.oldTerminal z = x ∧ E.RegularCrossing x.val (E.oldOutput z) ∧
      E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z.val) =
        Sum.inl (E.oldOutput z) := by
  rw [← hOld] at hx
  obtain ⟨z, hz, _, hcross⟩ := E.exists_oldTerminal_eq_of_mem_interior_old x hx
  exact ⟨z, hz, hcross, E.oldOutput_eq z⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set Function Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_regularCrossing_of_mem_interior_oldOutput
    (q : Q.Carrier) (hq : q ∈ interior (range E.oldOutput)) :
    ∃ p : P.Carrier, E.RegularCrossing p q := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core := E.transition.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.transition.trace.tubes.core := E.transition.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  let V : Opens Q.Carrier := ⟨interior (range E.oldOutput), isOpen_interior⟩
  let i : V → Q.Carrier ⊕ E.discarded.Carrier := fun y => Sum.inl y.val
  have hi : IsSmoothEmbedding ThreeModel ThreeModel ∞ i :=
    (IsSmoothEmbedding.sumInl (I := ThreeModel) (M := Q.Carrier)
      (M' := E.discarded.Carrier)).comp_of_boundarylessManifold_middle
        (IsSmoothEmbedding.of_opens V) (by simp)
  let z : V → E.capped.Carrier := E.transition.presentation.symm ∘ i
  have hz : IsSmoothEmbedding ThreeModel ThreeModel ∞ z :=
    hi.diffeomorph_comp E.transition.presentation.symm
  have hsub : range z ⊆ range E.transition.trace.capping.coreInclusion := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := interior_subset y.property
    refine ⟨x.val, ?_⟩
    apply E.transition.presentation.injective
    change E.transition.presentation (E.transition.trace.capping.coreInclusion x.val) =
      E.transition.presentation (E.transition.presentation.symm (i y))
    rw [E.transition.presentation.apply_symm_apply]
    exact (congrFun E.transition.presentation_eq (E.transition.trace.capping.coreInclusion x.val)).trans
      ((E.oldOutput_eq x).trans (congrArg Sum.inl hx))
  let k : V → E.transition.trace.tubes.core :=
    E.transition.core_inclusion_smooth.lift z hsub
  have hk : ContMDiff ThreeModel (𝓡∂ 3) ∞ k :=
    E.transition.core_inclusion_smooth.contMDiff_lift hz.contMDiff hsub
  have hkz : E.transition.trace.capping.coreInclusion ∘ k = z :=
    funext (E.transition.core_inclusion_smooth.comp_lift hsub)
  let f : V → P.Carrier := Subtype.val ∘ k
  have hf : ContMDiff ThreeModel ThreeModel ∞ f := E.transition.core_induced.contMDiff.comp hk
  have hkinj (y : V) : Injective (mfderiv ThreeModel (𝓡∂ 3) k y) := by
    have hinj := (hz.isImmersion.isImmersionAt y).mfderiv_injective (by simp)
    rw [← hkz, mfderiv_comp y
      (E.transition.core_inclusion_smooth.contMDiff.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))] at hinj
    exact Function.Injective.of_comp hinj
  have hfinj (y : V) : Injective (mfderiv ThreeModel ThreeModel f y) := by
    have hi := (E.transition.core_induced.isImmersion.isImmersionAt (k y)).mfderiv_injective (by simp)
    rw [show f = Subtype.val ∘ k from rfl,
      mfderiv_comp y (E.transition.core_induced.contMDiff.mdifferentiableAt (by simp))
        (hk.mdifferentiableAt (by simp))]
    exact hi.comp (hkinj y)
  have hlocal := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    f hf hfinj rfl
  have hmem (y : V) : ∃ x : E.old, f y = x.val.val ∧ E.oldOutput x = y.val := by
    obtain ⟨x, hx⟩ := interior_subset y.property
    have hkx : k y = x.val := by
      apply E.transition.core_inclusion_smooth.isEmbedding.injective
      rw [E.transition.core_inclusion_smooth.comp_lift hsub y]
      apply E.transition.presentation.injective
      change E.transition.presentation (E.transition.presentation.symm (i y)) = _
      rw [E.transition.presentation.apply_symm_apply]
      exact ((congrFun E.transition.presentation_eq
        (E.transition.trace.capping.coreInclusion x.val)).trans
          ((E.oldOutput_eq x).trans (congrArg Sum.inl hx))).symm
    exact ⟨x, congrArg Subtype.val hkx, hx⟩
  have hsubold : range f ⊆ Subtype.val '' E.old := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx, _⟩ := hmem y
    exact ⟨x.val, x.property, hx.symm⟩
  let y : V := ⟨q, hq⟩
  obtain ⟨x, hxy, hxq⟩ := hmem y
  have hpi : x.val.val ∈ interior (Subtype.val '' E.old) := by
    rw [← hxy]
    apply interior_mono hsubold
    rw [hlocal.isOpenMap.isOpen_range.interior_eq]
    exact mem_range_self y
  obtain ⟨x', hx', _, hcross⟩ :=
    E.exists_oldTerminal_eq_of_mem_interior_old (E.oldTerminal x) (by
      rw [E.oldTerminal_eq]
      exact hpi)
  have heq : x' = x := E.oldTerminal_isSmoothEmbedding.isEmbedding.injective hx'
  refine ⟨x.val.val, ?_⟩
  simpa only [heq, hxq, E.oldTerminal_eq] using hcross

theorem exists_terminal_regularCrossing_of_mem_interior_oldOutput
    (q : Q.Carrier) (hq : q ∈ interior (range E.oldOutput)) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q := by
  obtain ⟨p, x, hx, hxp, hxq⟩ := E.exists_regularCrossing_of_mem_interior_oldOutput q hq
  refine ⟨E.oldTerminal x, x, hx, ?_, hxq⟩
  exact (E.oldTerminal_eq x).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
