import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorParentInj
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.StageTransportBasic

set_option autoImplicit false

/-!
# CP1-D8 (G2b): across a regular crossing the exterior kernel can only grow (pre ⊆ post)
-/

noncomputable section
open Set Manifold DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Topology
open scoped Manifold ContDiff unitInterval

namespace GC.LongTime.CuspP1

universe u v

theorem kernel_le_exterior_of_regularCrossing_CPD8 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (OP : Set P.Carrier) (OQ : Set Q.Carrier)
    (hOP : IsOpen OP) [LocallyPathConnectedSpace ↥OPᶜ]
    (hP : ∀ p ∈ OP, ∃ q, E.RegularCrossing p q)
    (hQ : ∀ q ∈ OQ, ∃ p, E.RegularCrossing p q)
    (hQP : ∀ q ∈ OQ, ∀ p, E.RegularCrossing p q → p ∈ OP)
    {X : Type v} [TopologicalSpace X] [PreconnectedSpace X]
    (u : C(X, ↥OPᶜ)) (v : C(X, ↥OQᶜ))
    (hcross : ∀ y, E.RegularCrossing (u y).1 (v y).1) (x : X) :
    (FundamentalGroup.map u x).ker ≤ (FundamentalGroup.map v x).ker := by
  classical
  let Etr := E.transition
  let T := Etr.trace.tubes
  -- unfolding RegularCrossing
  have hcr : ∀ {p : P.Carrier} {q : Q.Carrier}, E.RegularCrossing p q →
      ∃ w : E.old, w.1.1 = p ∧ E.oldOutput w = q := by
    intro p q h
    obtain ⟨w, -, h1, h2⟩ := h
    exact ⟨w, h1, h2⟩
  have hOc : OP ⊆ T.core := by
    intro p hp
    obtain ⟨q, hq⟩ := hP p hp
    obtain ⟨w, hw, -⟩ := hcr hq
    rw [← hw]; exact w.1.2
  let pc : C(T.core, Q.Carrier ⊕ E.discarded.Carrier) :=
    ⟨fun c => Etr.trace.presentation (Etr.trace.capping.coreInclusion c),
      Etr.trace.presentation.continuous.comp Etr.trace.capping.coreInclusion.continuous⟩
  have hpcinj : Function.Injective pc := fun c c' h =>
    Etr.trace.capping.coreEmbedding.injective (Etr.trace.presentation.injective h)
  have hpcw : ∀ w : E.old, pc w.1 = Sum.inl (E.oldOutput w) := fun w => E.oldOutput_eq w
  let R : Set T.core := pc ⁻¹' range Sum.inl
  have hR : IsClopen R := ⟨isClosed_range_inl.preimage pc.continuous,
    isOpen_range_inl.preimage pc.continuous⟩
  have hu1 : ∀ y, ∃ w : E.old, w.1.1 = (u y).1 ∧ E.oldOutput w = (v y).1 := fun y => hcr (hcross y)
  have hucore : ∀ y, (u y).1 ∈ T.core := fun y => by
    obtain ⟨w, hw, -⟩ := hu1 y; rw [← hw]; exact w.1.2
  set Y := ↥OPᶜ
  let coreY : Set Y := {y | y.1 ∈ T.core}
  have hxc : u x ∈ coreY := hucore x
  let C : Set Y := connectedComponentIn coreY (u x)
  have hxC : u x ∈ C := mem_connectedComponentIn hxc
  have huC : ∀ y, u y ∈ C := by
    intro y
    have hpc : IsPreconnected (range u) := isPreconnected_range u.continuous
    have := hpc.subset_connectedComponentIn (x := u x) ⟨x, rfl⟩
      (show range u ⊆ coreY by rintro _ ⟨y, rfl⟩; exact hucore y) ⟨y, rfl⟩
    exact this
  let a' : C(X, ↥C) := ⟨fun y => ⟨u y, huC y⟩, u.continuous.subtype_mk _⟩
  have hinj : Function.Injective (FundamentalGroup.map (subsetToAmbient C) (a' x)) :=
    injective_coreComponent_exterior_CPD8 Etr (OP) hOP hOc (u x) hxc
  let jA : C(↥C, Y) := subsetToAmbient C
  have hCc : ∀ c : ↥C, c.1.1 ∈ T.core := fun c => connectedComponentIn_subset coreY (u x) c.2
  let tc : C(↥C, T.core) := ⟨fun c => ⟨c.1.1, hCc c⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hret : ∀ c : ↥C, tc c ∈ R := by
    have : ConnectedSpace ↥C :=
      isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hxc)
    have hpc : IsPreconnected (range tc) := isPreconnected_range tc.continuous
    obtain ⟨w, hw, hwo⟩ := hu1 x
    have h0 : tc (a' x) ∈ R := by
      have : tc (a' x) = w.1 := Subtype.ext hw.symm
      rw [this]
      exact ⟨_, (hpcw w).symm⟩
    have := hpc.subset_isClopen hR ⟨tc (a' x), ⟨a' x, rfl⟩, h0⟩
    intro c
    exact this ⟨c, rfl⟩
  choose q hq using fun c : ↥C => hret c
  have hqc : Continuous q := by
    rw [(Topology.IsEmbedding.inl (X := Q.Carrier) (Y := E.discarded.Carrier)).continuous_iff]
    have : (Sum.inl ∘ q : ↥C → Q.Carrier ⊕ E.discarded.Carrier) = fun c => pc (tc c) := by
      funext c; exact (hq c)
    rw [this]
    exact pc.continuous.comp tc.continuous
  have hqO : ∀ c : ↥C, q c ∈ OQᶜ := by
    intro c hc
    obtain ⟨p, hp⟩ := hQ _ hc
    obtain ⟨w, hw, hwo⟩ := hcr hp
    have h1 : pc w.1 = Sum.inl (q c) := by rw [hpcw, hwo]
    have h2 : w.1 = tc c := hpcinj (h1.trans (hq c))
    have h3 : p = c.1.1 := by rw [← hw, h2]; rfl
    exact c.1.2 (h3 ▸ hQP _ hc p hp)
  let jB : C(↥C, ↥OQᶜ) := ⟨fun c => ⟨q c, hqO c⟩, hqc.subtype_mk _⟩
  have hv : v = jB.comp a' := by
    ext y
    obtain ⟨w, hw, hwo⟩ := hu1 y
    have h1 : pc w.1 = Sum.inl (v y).1 := by rw [hpcw, hwo]
    have h2 : tc (a' y) = w.1 := Subtype.ext hw.symm
    have h3 : Sum.inl (q (a' y)) = (Sum.inl (v y).1 : Q.Carrier ⊕ E.discarded.Carrier) := by
      rw [← h1, ← h2]; exact hq _
    exact (Sum.inl.inj h3).symm
  have hu : u = jA.comp a' := rfl
  intro g hg
  have hg' : g ∈ (FundamentalGroup.map (jA.comp a') x).ker := by rw [← hu]; exact hg
  have hker := composite_kernel a' jA x hinj
  rw [hker] at hg'
  rw [hv]
  have := (composite_kernel a' jB x)
  rw [fundamentalGroup_map_comp, MonoidHom.mem_ker, MonoidHom.comp_apply]
  rw [MonoidHom.mem_ker] at hg'
  rw [hg', map_one]

end GC.LongTime.CuspP1
