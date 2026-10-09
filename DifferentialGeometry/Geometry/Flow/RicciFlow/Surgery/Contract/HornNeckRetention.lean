import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import DifferentialGeometry.Geometry.Neck.Orientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTubeIndexBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCutRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CentralNeckReparametrization

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : Finite P.HornCutIndex := by
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem cuttingSphereComponent_mem_of_central_horn_matching
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j < 1)
    (a : ∀ c, P.hornIndex c → ℝ) (ha : ∀ c e, 1 < a c e)
    (f : ∀ j, bufferedCylinder (δ j) → D.stage.Carrier)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
    (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2)
    (hmatch : ∀ j q, q ∈ controlledCylinder (δ j) →
      f j q = (P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)).val)
    (j : P.HornCutIndex) (side : Bool) :
    cuttingSphereComponent hδ f hf hd (j,side) ∈
      scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius^2)⁻¹ ↔
      side = true := by
  have hi (j : P.HornCutIndex) : 1 < (δ j)⁻¹ := (one_lt_inv₀ (hδ j)).mpr (hδ1 j)
  have hcore : cutCore f = cutCore (P.hornCutMap δ a) := by
    apply cutCore_eq_of_central_sphere_reparametrization ν
    intro j q hq
    exact hmatch j q ⟨by linarith [(hi j),hq.1],by linarith [(hi j),hq.2]⟩
  let x := cuttingSphereAttachment hδ f (fun j => (hf j).injective) hd ⟨(j,side),spherePoint⟩
  change ConnectedComponents.mk x ∈ _ ↔ _
  rw [mem_scalarSublevelComponents_of_cutCore_eq D.slab.terminalRegularOpen D.terminal.metric
    (P.coreRadius^2)⁻¹ hcore x]
  have hx : (Homeomorph.setCongr hcore x).val =
      (P.horn j.1.val j.2 (ν j spherePoint,a j.1.val j.2-cuttingSign side)).val := by
    apply hmatch j _
    cases side <;> constructor <;> norm_num [cuttingSign] <;> linarith [hi j]
  cases side
  · obtain ⟨hz,hn⟩ := (P.hornCutMap_retains_exactly_inner_side δ hδ a ha j).2 (ν j spherePoint)
    have heq : Homeomorph.setCongr hcore x =
        (⟨(P.horn j.1.val j.2 (ν j spherePoint,a j.1.val j.2+1)).val,hz⟩ : cutCore (P.hornCutMap δ a)) := by
      apply Subtype.ext
      simpa [cuttingSign] using hx
    rw [heq]
    exact iff_of_false hn (by decide)
  · obtain ⟨hz,hm⟩ := (P.hornCutMap_retains_exactly_inner_side δ hδ a ha j).1 (ν j spherePoint)
    have heq : Homeomorph.setCongr hcore x =
        (⟨(P.horn j.1.val j.2 (ν j spherePoint,a j.1.val j.2-1)).val,hz⟩ : cutCore (P.hornCutMap δ a)) := by
      apply Subtype.ext
      exact hx
    rw [heq]
    exact iff_of_true hm rfl

theorem retainedCore_terminal_of_central_horn_matching
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j < 1)
    (a : ∀ c, P.hornIndex c → ℝ) (ha : ∀ c e, 0 < a c e)
    (f : ∀ j, bufferedCylinder (δ j) → D.stage.Carrier)
    (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2)
    (hmatch : ∀ j q, q ∈ controlledCylinder (δ j) →
      f j q = (P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)).val) :
    MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
      (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
        (P.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  have hi (j : P.HornCutIndex) : 1 < (δ j)⁻¹ := (one_lt_inv₀ (hδ j)).mpr (hδ1 j)
  have hcore : cutCore f = cutCore (P.hornCutMap δ a) := by
    apply cutCore_eq_of_central_sphere_reparametrization ν
    intro j q hq
    exact hmatch j q ⟨by linarith [hi j,hq.1],by linarith [hi j,hq.2]⟩
  intro x hx
  have hret : (Homeomorph.setCongr hcore x) ∈ retainedCore (P.hornCutMap δ a)
      (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ a)
        (P.coreRadius^2)⁻¹) := by
    exact (mem_scalarSublevelComponents_of_cutCore_eq D.slab.terminalRegularOpen D.terminal.metric
      (P.coreRadius^2)⁻¹ hcore x).mp hx
  exact P.hornCutMap_retained_terminal δ hδ a ha hret


theorem retained_oriented_neck_family_of_horn_matching
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (a : ∀ c, P.hornIndex c → ℝ) (ha : ∀ c e, δ⁻¹ + 1 < a c e)
    (x : P.HornCutIndex → D.slab.terminalRegularOpen) (k : P.HornCutIndex → ℕ)
    (d : ∀ j, normalizedDatum D.terminal.metric (x j) δ (k j))
    (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2)
    (hmatch : ∀ j (q : bufferedCylinder δ),
      (d j).oriented.map q = P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)) :
    let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
    ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
      (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
      (∀ j side, cuttingSphereComponent (fun _ => hδ) f hf hd (j,side) ∈
        scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius^2)⁻¹ ↔ side = true) ∧
      MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
        (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
          (P.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
  have hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j) :=
    fun j => isOpenEmbedding_neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
  have hnonneg (j : P.HornCutIndex) (q : bufferedCylinder δ) : 0 < a j.1.val j.2-q.val.2 := by
    have hq : q.val.2 < δ⁻¹ + 1 := q.property.2
    linarith [ha j.1.val j.2]
  have hsubset (j : P.HornCutIndex) : range ((d j).oriented.map) ⊆ hornHalfRange P j.1.val j.2 := by
    rintro x ⟨q,rfl⟩
    rw [hmatch]
    exact ⟨⟨(ν j q.val.1, a j.1.val j.2 - q.val.2),(hnonneg j q).le⟩,rfl⟩
  have hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j)) := by
    intro i j hij
    rw [disjoint_left]
    rintro x ⟨q,rfl⟩ ⟨q',heq⟩
    have hindices : (⟨i.1.val,i.2⟩ : (c : ConnectedComponents D.slab.terminalRegularOpen) × P.hornIndex c) ≠
        ⟨j.1.val,j.2⟩ := by
      intro hh
      apply hij
      cases i with
      | mk c e =>
        cases j with
        | mk c' e' =>
          have hcc := congrArg Sigma.fst hh
          have hc : c = c' := Subtype.ext hcc
          subst c'
          exact congrArg (Sigma.mk c) (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)
    exact (P.hornHalfRange_pairwise_disjoint hindices).le_bot
      ⟨hsubset i ⟨q,rfl⟩,hsubset j ⟨q',Subtype.ext heq⟩⟩
  have ham (c) (e : P.hornIndex c) : 1 < a c e := by linarith [ha c e,inv_pos.mpr hδ]
  have hm (j) (q : bufferedCylinder δ) (_ : q ∈ controlledCylinder δ) :
      f j q = (P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)).val :=
    congrArg Subtype.val (hmatch j q)
  exact ⟨hf,hd,fun j side => P.cuttingSphereComponent_mem_of_central_horn_matching
    (fun _ => δ) (fun _ => hδ) (fun _ => hδ1) a ham f hf hd ν hm j side,
    P.retainedCore_terminal_of_central_horn_matching (fun _ => δ) (fun _ => hδ)
      (fun _ => hδ1) a (fun c e => zero_lt_one.trans (ham c e)) f ν hm⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
