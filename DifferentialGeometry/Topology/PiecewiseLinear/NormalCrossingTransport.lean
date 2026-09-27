/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingLocality

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem mem_image_iff_of_subset_source {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {W : Set X} (hW : W ⊆ e.source) {x : X}
    (hx : x ∈ e.source) : e x ∈ e '' W ↔ x ∈ W := by
  constructor
  · rintro ⟨z, hz, hze⟩
    have hzx : z = x := e.injOn (hW hz) hx hze
    exact hzx ▸ hz
  · exact fun h => ⟨x, h, rfl⟩

theorem mem_image_source_inter_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) {x : X} (hx : x ∈ e.source) :
    e x ∈ e '' (e.source ∩ S) ↔ x ∈ S := by
  rw [mem_image_iff_of_subset_source e inter_subset_left hx, mem_inter_iff,
    and_iff_right hx]

theorem HasPLNormalDoubleCrossingAt.congr_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {P : Set E}
    {B B' : Set F} {y : F} (h : HasPLNormalDoubleCrossingAt f P B y) (hB : y ∈ B ↔ y ∈ B') :
    HasPLNormalDoubleCrossingAt f P B' y := by
  rcases h with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hB.mp hyB, Mb, hcross⟩
  · exact Or.inr ⟨fun hy => hyB (hB.mpr hy), hcross⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasPLNormalDoubleCrossingAt.of_isPiecewiseAffineOn_transition
    {D : EuclideanSpace ℝ (Fin 2) → M} {P : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {e e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {y : M}
    (h : HasPLNormalDoubleCrossingAt (e ∘ D) (P ∩ D ⁻¹' e.source)
      (e '' (e.source ∩ BdM)) (e y))
    (hD : ContinuousOn D P)
    (htpa : IsPiecewiseAffineOn (e.symm.trans e') (e.symm.trans e').source)
    (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    HasPLNormalDoubleCrossingAt (e' ∘ D) (P ∩ D ⁻¹' e'.source)
      (e' '' (e'.source ∩ BdM)) (e' y) := by
  classical
  set W := e.source ∩ e'.source with hWdef
  have hWopen : IsOpen W := e.open_source.inter e'.open_source
  have hWe : W ⊆ e.source := inter_subset_left
  have hWe' : W ⊆ e'.source := inter_subset_right
  have hyW : y ∈ W := ⟨hy, hy'⟩
  set t := e.symm.trans e' with htdef
  have htpa' : IsPiecewiseAffineOn t t.source := by
    simpa only [htdef] using htpa
  have htsource : ∀ z ∈ W, e z ∈ t.source := by
    intro z hz
    rw [htdef, OpenPartialHomeomorph.trans_source]
    refine ⟨e.map_source (hWe hz), ?_⟩
    change e.symm (e z) ∈ e'.source
    rw [e.left_inv (hWe hz)]
    exact hWe' hz
  have htapply : ∀ z ∈ W, t (e z) = e' z := by
    intro z hz
    rw [htdef, OpenPartialHomeomorph.trans_apply, e.left_inv (hWe hz)]
  have hV : IsOpen (e '' W) := e.isOpen_image_of_subset_source hWopen hWe
  have hyV : e y ∈ e '' W := mem_image_of_mem e hyW
  have h₁ := h.inter_preimage_of_isOpen hV hyV
  have hsrc : P ∩ D ⁻¹' e.source ∩ (e ∘ D) ⁻¹' (e '' W) = P ∩ D ⁻¹' W := by
    ext x
    simp only [mem_inter_iff, mem_preimage, Function.comp_apply]
    constructor
    · rintro ⟨⟨hxP, hxe⟩, hxV⟩
      exact ⟨hxP, (mem_image_iff_of_subset_source e hWe hxe).mp hxV⟩
    · rintro ⟨hxP, hxW⟩
      exact ⟨⟨hxP, hWe hxW⟩, mem_image_of_mem e hxW⟩
  rw [hsrc] at h₁
  have hmaps : MapsTo (e ∘ D) (P ∩ D ⁻¹' W) t.source := fun x hx => htsource (D x) hx.2
  have h₂ := h₁.postcomp_openPartialHomeomorph t htpa' hmaps (htsource y hyW)
  rw [htapply y hyW] at h₂
  have hV' : IsOpen (e' '' W) := e'.isOpen_image_of_subset_source hWopen hWe'
  have hyV' : e' y ∈ e' '' W := mem_image_of_mem e' hyW
  have hgc : ContinuousOn (e' ∘ D) (P ∩ D ⁻¹' e'.source) :=
    e'.continuousOn.comp (hD.mono inter_subset_left) fun _ hx => hx.2
  have hPP' : P ∩ D ⁻¹' W ∩ (t ∘ (e ∘ D)) ⁻¹' (e' '' W) =
      P ∩ D ⁻¹' e'.source ∩ (e' ∘ D) ⁻¹' (e' '' W) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, Function.comp_apply]
    constructor
    · rintro ⟨⟨hxP, hxW⟩, -⟩
      exact ⟨⟨hxP, hWe' hxW⟩, mem_image_of_mem e' hxW⟩
    · rintro ⟨⟨hxP, hxe'⟩, hxV⟩
      have hxW : D x ∈ W := (mem_image_iff_of_subset_source e' hWe' hxe').mp hxV
      refine ⟨⟨hxP, hxW⟩, ?_⟩
      rw [htapply (D x) hxW]
      exact mem_image_of_mem e' hxW
  have hfg : EqOn (t ∘ (e ∘ D)) (e' ∘ D)
      (P ∩ D ⁻¹' W ∩ (t ∘ (e ∘ D)) ⁻¹' (e' '' W)) := by
    intro x hx
    change t (e (D x)) = e' (D x)
    exact htapply (D x) hx.1.2
  have h₃ := h₂.of_eqOn_of_isOpen hgc hV' hyV' hPP' hfg
  have hleft : e' y ∈ t '' (t.source ∩ e '' (e.source ∩ BdM)) ↔ y ∈ BdM := by
    rw [← htapply y hyW, mem_image_source_inter_iff t _ (htsource y hyW)]
    exact mem_image_source_inter_iff e BdM hy
  exact h₃.congr_boundary (hleft.trans (mem_image_source_inter_iff e' BdM hy').symm)

theorem HasPLNormalDoubleCrossingAt.of_mem_maximalAtlas
    {D : EuclideanSpace ℝ (Fin 2) → M} {P : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {e e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {y : M}
    (h : HasPLNormalDoubleCrossingAt (e ∘ D) (P ∩ D ⁻¹' e.source)
      (e '' (e.source ∩ BdM)) (e y))
    (hD : ContinuousOn D P) (he : e ∈ (plGroupoid 3).maximalAtlas M)
    (he' : e' ∈ (plGroupoid 3).maximalAtlas M) (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    HasPLNormalDoubleCrossingAt (e' ∘ D) (P ∩ D ⁻¹' e'.source)
      (e' '' (e'.source ∩ BdM)) (e' y) := by
  apply h.of_isPiecewiseAffineOn_transition hD ?_ hy hy'
  exact (mem_plGroupoid_iff.mp
    (StructureGroupoid.compatible_of_mem_maximalAtlas he he')).1

theorem exists_crossing_chart_mem_atlas
    {D : EuclideanSpace ℝ (Fin 2) → M} {P : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {y : M}
    (h : HasPLNormalDoubleCrossingAt (e ∘ D) (P ∩ D ⁻¹' e.source)
      (e '' (e.source ∩ BdM)) (e y))
    (hD : ContinuousOn D P) (he : e ∈ (plGroupoid 3).maximalAtlas M) (hy : y ∈ e.source) :
    ∃ e' ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e'.source ∧
      HasPLNormalDoubleCrossingAt (e' ∘ D) (P ∩ D ⁻¹' e'.source)
        (e' '' (e'.source ∩ BdM)) (e' y) := by
  let e' := chartAt (EuclideanSpace ℝ (Fin 3)) y
  have he' : e' ∈ atlas (EuclideanSpace ℝ (Fin 3)) M := chart_mem_atlas _ y
  have hy' : y ∈ e'.source := mem_chart_source _ y
  have htpa : IsPiecewiseAffineOn (e.symm.trans e') (e.symm.trans e').source := by
    exact (mem_plGroupoid_iff.mp ((mem_maximalAtlas_iff.mp he e' he').1)).1
  exact ⟨e', he', hy', h.of_isPiecewiseAffineOn_transition hD htpa hy hy'⟩

theorem mem_doublePointSet_of_preimage_singleton_eq {G A : SingularTwoCell M}
    (hdomain : A.domain = G.domain) {y : M}
    (hfibre : (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {y} =
      (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {y})
    (hy : y ∈ doublePointSet A A.domain) : y ∈ doublePointSet G G.domain := by
  have hmem : ∀ z : EuclideanSpace ℝ (Fin 2), A z = y → G z = y := by
    intro z hz
    have hzA : z ∈ (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {y} := hz
    rw [hfibre] at hzA
    exact hzA
  obtain ⟨a, ha, b, hb, hab, hay, hby⟩ := hy
  exact ⟨a, hdomain ▸ ha, b, hdomain ▸ hb, hab, hmem a hay, hmem b hby⟩

theorem exists_crossing_chart_of_preimage_singleton_eq_off {G A : SingularTwoCell M}
    {BdM U V : Set M} (hdomain : A.domain = G.domain)
    (hfibre : ∀ z ∉ V, (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
      (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z})
    (hG : ∀ z ∈ doublePointSet G G.domain ∩ U,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, z ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e z))
    {y : M} (hy : y ∈ doublePointSet A A.domain) (hyU : y ∈ U) (hyV : y ∉ closure V) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (e ∘ A) (A.domain ∩ A ⁻¹' e.source)
        (e '' (e.source ∩ BdM)) (e y) := by
  have hyVnot : y ∉ V := fun hmem => hyV (subset_closure hmem)
  have hyG : y ∈ doublePointSet G G.domain :=
    mem_doublePointSet_of_preimage_singleton_eq hdomain (hfibre y hyVnot) hy
  obtain ⟨e, he, hye, hcross⟩ := hG y ⟨hyG, hyU⟩
  have hAcont : ContinuousOn (A : EuclideanSpace ℝ (Fin 2) → M) G.domain := by
    rw [← hdomain]
    exact A.continuousOn
  have hev : ∀ᶠ z in 𝓝 y, (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
      (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hyV] with z hz
    exact (hfibre z fun hmem => hz (subset_closure hmem)).symm
  obtain ⟨hplain, hbdry⟩ :=
    hasPLDoubleCrossingAt_comp_openPartialHomeomorph_iff_of_eventually_eq_fiber e
      G.continuousOn hAcont hye hev
  refine ⟨e, he, hye, ?_⟩
  rw [hdomain]
  rcases hcross with ⟨hyB, Mb, hb⟩ | ⟨hyB, hp⟩
  · exact Or.inl ⟨hyB, Mb, (hbdry Mb).mp hb⟩
  · exact Or.inr ⟨hyB, hplain.mp hp⟩

theorem forall_exists_crossing_chart_of_preimage_singleton_eq_off {G A : SingularTwoCell M}
    {BdM U V : Set M} (hdomain : A.domain = G.domain)
    (hfibre : ∀ z ∉ V, (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
      (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z})
    (hG : ∀ z ∈ doublePointSet G G.domain ∩ U,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, z ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e z)) :
    ∀ y ∈ doublePointSet A A.domain ∩ (U \ closure V),
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ A) (A.domain ∩ A ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y) :=
  fun _ hy => exists_crossing_chart_of_preimage_singleton_eq_off hdomain hfibre hG
    hy.1 hy.2.1 hy.2.2

theorem forall_exists_crossing_chart_of_preimage_singleton_eq {G A : SingularTwoCell M}
    {BdM U : Set M} (hdomain : A.domain = G.domain)
    (hfibre : ∀ z, (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
      (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z})
    (hG : ∀ z ∈ doublePointSet G G.domain ∩ U,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, z ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e z)) :
    ∀ y ∈ doublePointSet A A.domain ∩ U,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ A) (A.domain ∩ A ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y) := by
  intro y hy
  refine exists_crossing_chart_of_preimage_singleton_eq_off (V := (∅ : Set M)) hdomain
    (fun z _ => hfibre z) hG hy.1 hy.2 ?_
  rw [closure_empty]
  exact notMem_empty y

end DifferentialGeometry.Topology.PiecewiseLinear
