/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.CompactImageNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphNeighborhoodSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [T2Space M₁] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

theorem exists_section34_graph_cell_carrier_neighborhoods
    (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (hH : ∀ t ∈ 𝒦.complex.faces, h '' Section34CarrierSupport 𝒦 t ⊆ interior (H t))
    (C : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (hCc : ∀ w, IsCompact (C w)) (hCU : ∀ w, C w ⊆ U)
    (hCinc : ∀ w (s : Section34SimplexIndex 𝒦 3),
      (C w ∩ simplexBody 𝒦 s.1).Nonempty ↔ Section34Incident w.1 s.1)
    (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea)
    (hcar : ∀ w, car w ∈ 𝒦.complex.faces)
    (hCcar : ∀ w, C w ⊆ Section34CarrierSupport 𝒦 (car w))
    (hCtri : ∀ w (s : Section34SimplexIndex 𝒦 3), Section34Incident w.1 s.1 →
      C w ⊆ Section34CarrierSupport 𝒦 s.1)
    (V : Section34VertexIndex 𝒦 𝒦' → Set M₂) (hV : ∀ w, IsOpen (V w))
    (hCV : ∀ w, h '' C w ⊆ V w)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U)
    (hsmall : ∀ w, ∀ x ∈ C w, ∀ y ∈ C w, ∀ z ∈ C w, dist (h y) (h z) < ψ x) :
    ∃ Q : Section34VertexIndex 𝒦 𝒦' → Set M₂, ∀ w,
      IsOpen (Q w) ∧ h '' C w ⊆ Q w ∧ Q w ⊆ V w ∧ Q w ⊆ H (car w) ∧
      (∀ x ∈ C w, ∀ y ∈ Q w, ∀ z ∈ Q w, dist y z < ψ x) ∧
      (∀ s : Section34SimplexIndex 𝒦 3,
        (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty ↔ Section34Incident w.1 s.1) ∧
      ∀ s : Section34SimplexIndex 𝒦 3,
        Section34Incident w.1 s.1 → Q w ⊆ interior (H s.1) := by
  classical
  have hhc : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hhi : InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show U.domRestrict h ⟨x, hx⟩ =
      U.domRestrict h ⟨y, hy⟩ from hxy))
  have hbodyU : ∀ s ∈ 𝒦.complex.faces, simplexBody 𝒦 s ⊆ U := by
    intro s hs x hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact 𝒦.bijOn.mapsTo (𝒦.complex.convexHull_subset_space hs hp)
  have hlf : LocallyFinite fun s : Section34SimplexIndex 𝒦 3 =>
      (Subtype.val : U → M₁) ⁻¹' simplexBody 𝒦 s.1 := by
    let f : Section34SimplexIndex 𝒦 3 → 𝒦.complex.faces := fun s => ⟨s.1, s.2.1⟩
    have hf : Function.Injective f := by
      intro s t hst
      exact Subtype.ext (congrArg (fun r : 𝒦.complex.faces => r.1) hst)
    exact (locallyFinite_simplexBody_subtype 𝒦).comp_injective (g := f) hf
  have hclosed : ∀ s : Section34SimplexIndex 𝒦 3,
      IsClosed ((Subtype.val : U → M₁) ⁻¹' simplexBody 𝒦 s.1) := by
    intro s
    exact ((s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
      (𝒦.continuousOn.mono (𝒦.complex.convexHull_subset_space s.2.1))).isClosed.preimage
        continuous_subtype_val
  suffices hlocal : ∀ w : Section34VertexIndex 𝒦 𝒦', ∃ Q : Set M₂,
      IsOpen Q ∧ h '' C w ⊆ Q ∧ Q ⊆ V w ∧ Q ⊆ H (car w) ∧
      (∀ x ∈ C w, ∀ y ∈ Q, ∀ z ∈ Q, dist y z < ψ x) ∧
      (∀ s : Section34SimplexIndex 𝒦 3,
        (Q ∩ h '' simplexBody 𝒦 s.1).Nonempty ↔ Section34Incident w.1 s.1) ∧
      ∀ s : Section34SimplexIndex 𝒦 3,
        Section34Incident w.1 s.1 → Q ⊆ interior (H s.1) by
    choose Q hQ using hlocal
    exact ⟨Q, hQ⟩
  intro w
  let I : Set (Section34SimplexIndex 𝒦 3) := {s | Section34Incident w.1 s.1}
  have hcompact : IsCompact ((Subtype.val : U → M₁) ⁻¹' C w) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr (hCU w)]
    exact hCc w
  have hIfin : I.Finite := by
    refine (hlf.finite_nonempty_inter_compact hcompact).subset ?_
    intro s hs
    obtain ⟨x, hxC, hxs⟩ := (hCinc w s).mpr hs
    exact ⟨⟨x, hCU w hxC⟩, hxs, hxC⟩
  let F := {s : Section34SimplexIndex 𝒦 3 // ¬ Section34Incident w.1 s.1}
  let B : Set M₁ := U \ ⋃ s : F, simplexBody 𝒦 s.1.1
  have hB : IsOpen B := by
    apply hU.inter_preimage_val_iff.mp
    change IsOpen ((Subtype.val : U → M₁) ⁻¹' ⋃ s : F, simplexBody 𝒦 s.1.1)ᶜ
    rw [preimage_iUnion]
    exact ((hlf.comp_injective (g := fun s : F => s.1) Subtype.val_injective).isClosed_iUnion
      (fun s => hclosed s.1)).isOpen_compl
  have hCB : C w ⊆ B := by
    intro x hx
    refine ⟨hCU w hx, ?_⟩
    intro hbad
    obtain ⟨s, hs⟩ := mem_iUnion.mp hbad
    exact s.2 ((hCinc w s.1).mp ⟨x, hx, hs⟩)
  let J : Set M₂ := ⋂ s ∈ I, interior (H s.1)
  have hJ : IsOpen J := hIfin.isOpen_biInter fun s _ => isOpen_interior
  have hCJ : h '' C w ⊆ J := by
    intro y hy
    exact mem_iInter₂.mpr fun s hs => hH s.1 s.2.1 (image_mono (hCtri w s hs) hy)
  let T : Set M₂ := ((h '' B ∩ interior (H (car w))) ∩ J) ∩ V w
  have hT : IsOpen T := by
    have him : IsOpen (h '' B) :=
      isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hB
        (hhc.mono sdiff_subset) (hhi.mono sdiff_subset)
    exact ((him.inter isOpen_interior).inter hJ).inter (hV w)
  have hCT : h '' C w ⊆ T := by
    intro y hy
    exact ⟨⟨⟨image_mono hCB hy, hH _ (hcar w) (image_mono (hCcar w) hy)⟩,
      hCJ hy⟩, hCV w hy⟩
  obtain ⟨Q, hQ, hCQ, hQT, hQsmall⟩ :=
    (hCc w).exists_isOpen_image_neighborhood_dist_lt (hhc.mono (hCU w))
      (hψc.mono (hCU w)) (hsmall w) hT hCT
  refine ⟨Q, hQ, hCQ, fun y hy => (hQT hy).2,
    fun y hy => interior_subset (hQT hy).1.1.2, hQsmall, ?_, ?_⟩
  · intro s
    constructor
    · intro hs
      by_contra hnot
      obtain ⟨y, hyQ, a, ha, hay⟩ := hs
      obtain ⟨b, hb, hby⟩ := (hQT hyQ).1.1.1
      have hab : a = b := hhi (hbodyU _ s.2.1 ha) hb.1 (hay.trans hby.symm)
      exact hb.2 (mem_iUnion.mpr ⟨⟨s, hnot⟩, hab ▸ ha⟩)
    · intro hs
      obtain ⟨x, hxC, hxs⟩ := (hCinc w s).mpr hs
      exact ⟨h x, hCQ (mem_image_of_mem h hxC), mem_image_of_mem h hxs⟩
  · intro s hs y hy
    exact mem_iInter₂.mp (hQT hy).1.2 s hs

end DifferentialGeometry.Topology.PiecewiseLinear
