import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarStage

set_option autoImplicit false

/-!
# CP1-D8 (G3): the exterior region is locally path connected (from the P1b bicollar)
-/

noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

open GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime

universe u

/-- local path connectedness is local: an open cover by locally path connected pieces -/
theorem locallyPathConnectedSpace_of_open_cover_CPD8 {X : Type*} [TopologicalSpace X]
    {κ : Type*} (V : κ → Set X) (hV : ∀ k, IsOpen (V k)) (hcov : ∀ x, ∃ k, x ∈ V k)
    (hlpc : ∀ k, LocallyPathConnectedSpace ↥(V k)) : LocallyPathConnectedSpace X where
  path_connected_basis x := by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨k, hk⟩ := hcov x
    have ht' : (Subtype.val ⁻¹' t : Set ↥(V k)) ∈ 𝓝 (⟨x, hk⟩ : ↥(V k)) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds ht
    obtain ⟨N, ⟨hN, hNpc⟩, hNt⟩ := ((hlpc k).path_connected_basis ⟨x, hk⟩).mem_iff.mp ht'
    refine ⟨Subtype.val '' N, ?_, hNpc.image continuous_subtype_val, ?_⟩
    · have := (hV k).isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hk⟩
      rw [← this]
      exact Filter.image_mem_map hN
    · rintro _ ⟨y, hy, rfl⟩
      exact hNt hy

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}

theorem locallyPathConnectedSpace_region_CPD8 (E : PersistentCuspExterior cores)
    (i : Fin cores.count) (q : Fin (E.truncation i).count) (t : ℝ) (ht : E.start ≤ t) :
    LocallyPathConnectedSpace ↥(E.region t) := by
  classical
  have : Nonempty (TorusIdx_LTP1 E.truncation) := ⟨⟨i, q⟩⟩
  obtain ⟨σ, hsrc, hzero, hside, hclosed, hint⟩ := exists_bicollar_of_exterior_LTP1 E t ht
  set S := (postStage F.observation t).Carrier
  have hSl : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ThreeSpace S
  set W : Set S := E.region t with hW
  set ι := TorusIdx_LTP1 E.truncation
  let σ0 : ι × Torus → S := fun x => σ (x, 0)
  have hsm : ∀ p : (ι × Torus) × ℝ, -1 < p.2 → p.2 < 1 → p ∈ σ.source := fun p h1 h2 => by
    rw [hsrc]; exact ⟨h1, h2⟩
  have hσ0c : Continuous σ0 := by
    have : Continuous fun x : ι × Torus => ((x, (0 : ℝ)) : (ι × Torus) × ℝ) :=
      continuous_id.prodMk continuous_const
    exact σ.continuousOn.comp_continuous this (fun x => hsm _ (by norm_num) (by norm_num))
  have hR0 : IsClosed (range σ0) := (isCompact_range hσ0c).isClosed
  -- piece 1: points off the boundary tori
  let V₁ : Set ↥W := {w | w.1 ∉ range σ0}
  have hV₁ : IsOpen V₁ := hR0.isOpen_compl.preimage continuous_subtype_val
  have hV₁l : LocallyPathConnectedSpace ↥V₁ := by
    let f : ↥V₁ → S := fun v => v.1.1
    have hfe : Topology.IsEmbedding f :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    have hrange : range f = interior W \ range σ0 := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨hint ⟨v.1.2, v.2⟩, v.2⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨⟨⟨y, interior_subset hy1⟩, hy2⟩, rfl⟩
    have hfo : Topology.IsOpenEmbedding f :=
      ⟨hfe, by rw [hrange]; exact isOpen_interior.sdiff hR0⟩
    exact hfo.locallyPathConnectedSpace
  -- piece 2: the collar side
  let Y₂ := (ι × Torus) × Set.Ico (0 : ℝ) 1
  have hmem : ∀ p : Y₂, σ (p.1, p.2.1) ∈ W := fun p =>
    (hside _ (hsm _ (by linarith [p.2.2.1]) p.2.2.2)).mpr p.2.2.1
  let e' : Y₂ → ↥W := fun p => ⟨σ (p.1, p.2.1), hmem p⟩
  have he' : Topology.IsEmbedding e' := by
    let ψ : Y₂ → ↥σ.source := fun p =>
      ⟨(p.1, p.2.1), hsm _ (by linarith [p.2.2.1]) p.2.2.2⟩
    have hψ : Topology.IsEmbedding ψ :=
      (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal).codRestrict _ _
    have h2 : Topology.IsEmbedding (fun p : Y₂ => σ.source.restrict σ (ψ p)) :=
      σ.isEmbedding_restrict.comp hψ
    exact Topology.IsEmbedding.of_comp (continuous_induced_rng.2 h2.continuous) continuous_subtype_val h2
  have hV₂o : IsOpen (range e') := by
    have : range e' = Subtype.val ⁻¹' σ.target := by
      ext w
      constructor
      · rintro ⟨p, rfl⟩
        exact σ.map_source (hsm _ (by linarith [p.2.2.1]) p.2.2.2)
      · intro hw
        have hs := σ.map_target hw
        have hww : σ (σ.symm w.1) = w.1 := σ.right_inv hw
        have h0 : 0 ≤ (σ.symm w.1).2 := by
          have := (hside _ hs).mp (by rw [hww]; exact w.2)
          exact this
        have h1 : (σ.symm w.1).2 < 1 := by
          have := hs; rw [hsrc] at this; exact this.2
        refine ⟨(( σ.symm w.1).1, ⟨(σ.symm w.1).2, h0, h1⟩), Subtype.ext ?_⟩
        show σ ((σ.symm w.1).1, (σ.symm w.1).2) = w.1
        exact hww
    rw [this]
    exact σ.open_target.preimage continuous_subtype_val
  have hCirc : LocallyPathConnectedSpace _root_.Circle :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) _root_.Circle
  have hIco : LocallyPathConnectedSpace (Set.Ico (0 : ℝ) 1) :=
    (convex_Ico (0 : ℝ) 1).locallyPathConnectedSpace
  have hY₂ : LocallyPathConnectedSpace Y₂ := by
    change LocallyPathConnectedSpace ((ι × (_root_.Circle × _root_.Circle)) × Set.Ico (0 : ℝ) 1)
    infer_instance
  have hV₂l : LocallyPathConnectedSpace ↥(range e') :=
    he'.toHomeomorph.locallyPathConnectedSpace
  refine locallyPathConnectedSpace_of_open_cover_CPD8 (κ := Bool)
    (fun b => if b then V₁ else range e') ?_ ?_ ?_
  · intro b; cases b
    · exact hV₂o
    · exact hV₁
  · intro w
    by_cases hw : w.1 ∈ range σ0
    · obtain ⟨x, hx⟩ := hw
      refine ⟨false, ?_⟩
      refine ⟨(x, ⟨0, by norm_num, by norm_num⟩), Subtype.ext ?_⟩
      exact hx
    · exact ⟨true, hw⟩
  · intro b; cases b
    · exact hV₂l
    · exact hV₁l

end GC.LongTime.CuspP1
