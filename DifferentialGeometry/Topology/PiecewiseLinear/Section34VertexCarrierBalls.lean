/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphNeighborhoodSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [T2Space M₁] [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  [HasGroupoid M₂ (plGroupoid 3)]
  {U W : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

theorem exists_section34_vertex_carrier_balls
    (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hH : ∀ t ∈ 𝒦.complex.faces, h '' Section34CarrierSupport 𝒦 t ⊆ interior (H t))
    (hW : IsOpen W)
    (hΓW : graphSkeletonSpace 𝒦 ⊆ W)
    (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea)
    (hcar : ∀ w, car w ∈ 𝒦.complex.faces)
    (hbody : ∀ w, simplexBody 𝒦' w.1 ⊆ simplexBody 𝒦 (car w))
    (V : Section34VertexIndex 𝒦 𝒦' → Set M₂) (hV : ∀ w, IsOpen (V w))
    (hmarker : ∀ w, h '' simplexBody 𝒦' w.1 ⊆ V w)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (A : Section34VertexIndex 𝒦 𝒦' → Set M₁)
      (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂), ∀ w,
      IsOpen (A w) ∧ simplexBody 𝒦' w.1 ⊆ A w ∧ A w ⊆ W ∩ U ∧
      IsPLCellOn 3 (Q w) (frontier (Q w)) ∧ h '' A w ⊆ interior (Q w) ∧
      Q w ⊆ V w ∧ Q w ⊆ H (car w) ∧
      (∀ x ∈ A w, ∀ y ∈ Q w, ∀ z ∈ Q w, dist y z < ψ x) ∧
      (∀ s : Section34SimplexIndex 𝒦 3,
        (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1) ∧
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
  have hbodyH : ∀ s ∈ 𝒦.complex.faces, h '' simplexBody 𝒦 s ⊆ interior (H s) := by
    intro s hs x hx
    obtain ⟨a, ha⟩ := 𝒦.complex.nonempty_of_mem_faces hs
    exact hH s hs (image_mono (fun y hy =>
      mem_iUnion₂.mpr ⟨a, ha, mem_iUnion₂.mpr ⟨s, ⟨hs, ha⟩, hy⟩⟩) hx)
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
  suffices hlocal : ∀ w : Section34VertexIndex 𝒦 𝒦', ∃ A : Set M₁, ∃ Q : Set M₂,
      IsOpen A ∧ simplexBody 𝒦' w.1 ⊆ A ∧ A ⊆ W ∩ U ∧
      IsPLCellOn 3 Q (frontier Q) ∧ h '' A ⊆ interior Q ∧
      Q ⊆ V w ∧ Q ⊆ H (car w) ∧
      (∀ x ∈ A, ∀ y ∈ Q, ∀ z ∈ Q, dist y z < ψ x) ∧
      (∀ s : Section34SimplexIndex 𝒦 3,
        (Q ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1) ∧
      ∀ s : Section34SimplexIndex 𝒦 3,
        Section34Incident w.1 s.1 → Q ⊆ interior (H s.1) by
    choose A Q hAQ using hlocal
    exact ⟨A, Q, hAQ⟩
  intro w
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  let x₀ := 𝒦.map p
  have hsingleton : simplexBody 𝒦' w.1 = {x₀} := by
    simp [simplexBody, hp, hmap, x₀]
  have hpoint : x₀ ∈ simplexBody 𝒦' w.1 := by simp [hsingleton]
  have hxU : x₀ ∈ U := hbodyU _ (hcar w) (hbody w hpoint)
  have hxW : x₀ ∈ W := hΓW (w.2.2.2 hpoint)
  have hpK : p ∈ 𝒦.complex.space := by
    rw [← hsub.space_eq]
    exact 𝒦'.complex.convexHull_subset_space w.2.1
      (by simp [hp])
  have hinc : ∀ s : Section34SimplexIndex 𝒦 3,
      Section34Incident w.1 s.1 ↔ x₀ ∈ simplexBody 𝒦 s.1 := by
    intro s
    change ((w.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)) ↔ _
    rw [hp, Finset.coe_singleton, singleton_subset_iff]
    constructor
    · intro hps
      exact ⟨p, hps, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      have heq : q = p := 𝒦.bijOn.injOn
        (𝒦.complex.convexHull_subset_space s.2.1 hq) hpK hqp
      exact heq ▸ hq
  let I : Set (Section34SimplexIndex 𝒦 3) := {s | Section34Incident w.1 s.1}
  have hIfin : I.Finite := (hlf.point_finite ⟨x₀, hxU⟩).subset fun s hs => (hinc s).mp hs
  let F := {s : Section34SimplexIndex 𝒦 3 // ¬ Section34Incident w.1 s.1}
  let B : Set M₁ := U \ ⋃ s : F, simplexBody 𝒦 s.1.1
  have hB : IsOpen B := by
    apply hU.inter_preimage_val_iff.mp
    change IsOpen ((Subtype.val : U → M₁) ⁻¹' ⋃ s : F, simplexBody 𝒦 s.1.1)ᶜ
    rw [preimage_iUnion]
    exact ((hlf.comp_injective (g := fun s : F => s.1) Subtype.val_injective).isClosed_iUnion
      (fun s => hclosed s.1)).isOpen_compl
  have hxB : x₀ ∈ B := by
    refine ⟨hxU, ?_⟩
    intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact s.2 ((hinc s.1).mpr hs)
  let J : Set M₂ := ⋂ s ∈ I, interior (H s.1)
  have hJ : IsOpen J := hIfin.isOpen_biInter fun s _ => isOpen_interior
  have hxJ : h x₀ ∈ J := mem_iInter₂.mpr fun s hs =>
    hbodyH s.1 s.2.1 (mem_image_of_mem h ((hinc s).mp hs))
  let T : Set M₂ := ((h '' B ∩ interior (H (car w))) ∩ J) ∩
    (V w ∩ Metric.ball (h x₀) (ψ x₀ / 8))
  have hT : IsOpen T := by
    have him : IsOpen (h '' B) :=
      isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hB
        (hhc.mono sdiff_subset) (hhi.mono sdiff_subset)
    exact ((him.inter isOpen_interior).inter hJ).inter ((hV w).inter Metric.isOpen_ball)
  have hxT : h x₀ ∈ T := by
    refine ⟨⟨⟨mem_image_of_mem h hxB,
      hbodyH _ (hcar w) (mem_image_of_mem h (hbody w hpoint))⟩, hxJ⟩,
      hmarker w (mem_image_of_mem h hpoint), ?_⟩
    exact Metric.mem_ball_self (div_pos (hψpos x₀ hxU) (by norm_num))
  obtain ⟨Q, hQcell, hxQ, hQT⟩ := exists_isPLCellOn_subset_of_mem_nhds (hT.mem_nhds hxT)
  let A : Set M₁ := (W ∩ (U ∩ h ⁻¹' interior Q)) ∩
    (U ∩ ψ ⁻¹' Ioi (ψ x₀ / 2))
  have hA : IsOpen A :=
    (hW.inter (hhc.isOpen_inter_preimage hU isOpen_interior)).inter
      (hψc.isOpen_inter_preimage hU isOpen_Ioi)
  have hxA : x₀ ∈ A := by
    refine ⟨⟨hxW, hxU, hxQ⟩, hxU, ?_⟩
    change ψ x₀ / 2 < ψ x₀
    linarith [hψpos x₀ hxU]
  refine ⟨A, Q, hA, ?_, fun x hx => ⟨hx.1.1, hx.1.2.1⟩, hQcell,
    ?_, fun y hy => (hQT hy).2.1,
    fun y hy => interior_subset (hQT hy).1.1.2, ?_, ?_, ?_⟩
  · rw [hsingleton]
    exact singleton_subset_iff.mpr hxA
  · rintro y ⟨x, hx, rfl⟩
    exact hx.1.2.2
  · intro x hx y hy z hz
    have hyd : dist y (h x₀) < ψ x₀ / 8 := (hQT hy).2.2
    have hzd : dist z (h x₀) < ψ x₀ / 8 := (hQT hz).2.2
    have hxscale : ψ x₀ / 2 < ψ x := hx.2.2
    have hpos : 0 < ψ x₀ := hψpos x₀ hxU
    have htri := dist_triangle y (h x₀) z
    rw [dist_comm (h x₀) z] at htri
    linarith
  · intro s hs
    by_contra hnot
    obtain ⟨y, hyQ, a, ha, hay⟩ := hs
    obtain ⟨b, hb, hby⟩ := (hQT hyQ).1.1.1
    have hab : a = b := hhi (hbodyU _ s.2.1 ha) hb.1 (hay.trans hby.symm)
    exact hb.2 (mem_iUnion.mpr ⟨⟨s, hnot⟩, hab ▸ ha⟩)
  · intro s hs y hy
    exact mem_iInter₂.mp (hQT hy).1.2 s hs

end DifferentialGeometry.Topology.PiecewiseLinear
