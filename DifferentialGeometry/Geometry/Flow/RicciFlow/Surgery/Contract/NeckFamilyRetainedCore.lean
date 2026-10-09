import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NeckFamilySeparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCutRetention
import DifferentialGeometry.Topology.Manifold.ImmersionRange

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private local instance : Finite P.HornCutIndex := by
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance

theorem exists_scale_threshold_protected_neck_family_retainedCore
    (hε : ε ≤ 1 / 8646) {δ : ℝ} (hεδ : ε ≤ δ) (hδ1 : δ < 1)
    (hfit : δ⁻¹ + 1 < ε⁻¹) (r : ∀ c, P.hornIndex c → ℝ) (L : ℝ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
      ∃ (t δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
        (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
        (hδ : ∀ c e, δ₀ c e ≤ δ),
        (∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y, t c e) ∧
          (N c e).scale = Q ∧ δ₀ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
          ∃ Θ : neckBuffer δ → positiveHornDomain,
            IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
            (∀ q : neckBuffer δ,
              P.horn c e (Θ q).val = ((N c e).monoDelta (hδ c e) hδ1).chart q) ∧
            (∀ q : neckBuffer δ, r c e < (Θ q).val.2)) ∧
        let f := fun j : P.HornCutIndex => fun q : bufferedCylinder δ =>
          (((N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1).chart q).val
        let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f L
        (∀ j, _root_.Topology.IsOpenEmbedding (f j)) ∧
        Pairwise (fun j j' => Disjoint (range (f j)) (range (f j'))) ∧
        (∀ x : D.slab.terminalRegularOpen, metricScalarAt D.terminal.metric x ≤ L →
          x.val ∈ interior ((Subtype.val : cutCore f → D.stage.Carrier) '' retainedCore f R)) ∧
        (∀ C : ConnectedComponents (cutCore f),
          (∃ z : cutCore f, ConnectedComponents.mk z = C ∧ z ∈ retainedCore f R) →
          ∃ x : D.slab.terminalRegularOpen, metricScalarAt D.terminal.metric x ≤ L ∧
            ∃ hx : x.val ∈ cutCore f, ConnectedComponents.mk (⟨x.val,hx⟩ : cutCore f) = C) := by
  obtain ⟨Q₀,hQ₀,hfamily⟩ := P.exists_scale_threshold_disjoint_neck_family_in_horns
    hε hεδ hδ1 hfit r L
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ y
  obtain ⟨t,δ₀,k,N,hδ,hN,hdisjoint,hprotected⟩ := hfamily Q hQ y
  refine ⟨t,δ₀,k,N,hδ,?_,?_⟩
  · intro c e
    obtain ⟨ht,hcenter,hscale,hδ₀,hk,_,_,_,Θ,hΘ,hmap,hdepth,_⟩ := hN c e
    exact ⟨ht,hcenter,hscale,hδ₀,hk,Θ,hΘ,hmap,hdepth⟩
  · let f := fun j : P.HornCutIndex => fun q : bufferedCylinder δ =>
      (((N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1).chart q).val
    let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f L
    change (∀ j, _root_.Topology.IsOpenEmbedding (f j)) ∧ _
    have hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j) := by
      intro j
      let nj := (N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1
      have hn : _root_.Topology.IsOpenEmbedding nj.chart :=
        ⟨nj.chart_smooth.isEmbedding, Manifold.isOpen_range_of_isSmoothEmbedding
          (by simp [ThreeSpace]) nj.chart_smooth⟩
      exact D.slab.terminalRegularOpen.isOpen.isOpenEmbedding_subtypeVal.comp hn
    have hd : Pairwise (fun j j' => Disjoint (range (f j)) (range (f j'))) := by
      intro j j' hj
      rw [disjoint_left]
      rintro x ⟨q,rfl⟩ ⟨q',heq⟩
      have hindices : (⟨j.1.val,j.2⟩ : (c : ConnectedComponents D.slab.terminalRegularOpen) × P.hornIndex c) ≠
          ⟨j'.1.val,j'.2⟩ := by
        intro hh
        apply hj
        cases j with
        | mk c e =>
          cases j' with
          | mk c' e' =>
            have hcc := congrArg Sigma.fst hh
            have hcc' : c = c' := Subtype.ext hcc
            subst c'
            exact congrArg (Sigma.mk c) (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)
      have hn := hdisjoint hindices
      exact hn.le_bot ⟨subset_closure ⟨q,rfl⟩,
        subset_closure ⟨q',Subtype.ext heq⟩⟩
    let : LocallyPathConnectedSpace D.stage.Carrier :=
      DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners ThreeModel
    have hδpos : ∀ j : P.HornCutIndex, 0 < δ :=
      fun j => ((N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1).delta_pos
    have hopen := (isClopen_retained_discardedCore hδpos f hf hd R).1.isOpen
    refine ⟨hf,hd,?_,?_⟩
    · intro x hx
      have hint : x.val ∈ interior (cutCore f) := by
        apply interior_mono ?_ (hprotected x hx)
        intro z hz
        change z ∉ ⋃ j, removedSlab (f j)
        intro hcut
        obtain ⟨j,q,_,heq⟩ := mem_iUnion.mp hcut
        exact hz (mem_iUnion.mpr ⟨j.1.val,mem_iUnion.mpr ⟨j.2,q,heq⟩⟩)
      let z : cutCore f := ⟨x.val,interior_subset hint⟩
      have hz : z ∈ retainedCore f R := ⟨x,hx,z.property,rfl⟩
      exact DifferentialGeometry.Topology.mem_interior_image_val_of_isOpen hopen hz hint
    · intro C hC
      obtain ⟨z,hz,hret⟩ := hC
      change ConnectedComponents.mk z ∈ R at hret
      rw [hz] at hret
      exact hret

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
