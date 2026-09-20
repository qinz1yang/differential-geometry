/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingLocality

/-!
# Transporting the normality crossing condition

The crossing condition of a normal singular two cell asks, at every double point `y` of the
cell `D`, for a chart `e` of the ambient atlas with `y ∈ e.source` and a PL normal double
crossing of `e ∘ D` at `e y`.  The general position producers of the tree do not deliver it
in that shape: they work in a chart of the maximal `plGroupoid 3` atlas, and they normalise
one double point at a time, leaving the cell unchanged outside a small set.  This file
supplies the two transports that bridge the gap.

* `exists_crossing_chart_mem_atlas` replaces a chart of the maximal atlas by a chart of the
  atlas itself, namely `chartAt` at the double point.
* `exists_crossing_chart_of_preimage_singleton_eq_off` is the step of a finite cover
  induction: a perturbation whose fibres agree with the old ones over every point outside
  `V` retains every crossing chart already available, away from `closure V`.

Neither statement produces a crossing; both only move one that is given.  The step lemma is
stated with an arbitrary comparison set `U`, so that an induction can carry the set on which
crossings are already known as an invariant.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- A point of the source of an open partial homeomorphism lies in a subset of that source
exactly when its image lies in the image of that subset. -/
theorem mem_image_iff_of_subset_source {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {W : Set X} (hW : W ⊆ e.source) {x : X}
    (hx : x ∈ e.source) : e x ∈ e '' W ↔ x ∈ W := by
  constructor
  · rintro ⟨z, hz, hze⟩
    have hzx : z = x := e.injOn (hW hz) hx hze
    exact hzx ▸ hz
  · exact fun h => ⟨x, h, rfl⟩

/-- Membership of `e x` in the image of `e.source ∩ S` is membership of `x` in `S`. -/
theorem mem_image_source_inter_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) {x : X} (hx : x ∈ e.source) :
    e x ∈ e '' (e.source ∩ S) ↔ x ∈ S := by
  rw [mem_image_iff_of_subset_source e inter_subset_left hx, mem_inter_iff,
    and_iff_right hx]

/-- The boundary set of a PL normal double crossing enters only through the membership of
the double point, so it may be replaced by any set with the same membership there. -/
theorem HasPLNormalDoubleCrossingAt.congr_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {P : Set E}
    {B B' : Set F} {y : F} (h : HasPLNormalDoubleCrossingAt f P B y) (hB : y ∈ B ↔ y ∈ B') :
    HasPLNormalDoubleCrossingAt f P B' y := by
  rcases h with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hB.mp hyB, Mb, hcross⟩
  · exact Or.inr ⟨fun hy => hyB (hB.mpr hy), hcross⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- A PL normal double crossing read in one chart of the maximal `plGroupoid 3` atlas is a
PL normal double crossing read in any other chart of that atlas around the same point.  The
source is the part of `P` lying over the chart domain and the boundary set is the image of
`BdM`, both in the shape the normality crossing condition uses. -/
theorem HasPLNormalDoubleCrossingAt.of_mem_maximalAtlas
    {D : EuclideanSpace ℝ (Fin 2) → M} {P : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {e e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {y : M}
    (h : HasPLNormalDoubleCrossingAt (e ∘ D) (P ∩ D ⁻¹' e.source)
      (e '' (e.source ∩ BdM)) (e y))
    (hD : ContinuousOn D P) (he : e ∈ (plGroupoid 3).maximalAtlas M)
    (he' : e' ∈ (plGroupoid 3).maximalAtlas M) (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    HasPLNormalDoubleCrossingAt (e' ∘ D) (P ∩ D ⁻¹' e'.source)
      (e' '' (e'.source ∩ BdM)) (e' y) := by
  classical
  set W := e.source ∩ e'.source with hWdef
  have hWopen : IsOpen W := e.open_source.inter e'.open_source
  have hWe : W ⊆ e.source := inter_subset_left
  have hWe' : W ⊆ e'.source := inter_subset_right
  have hyW : y ∈ W := ⟨hy, hy'⟩
  set t := e.symm.trans e' with htdef
  have ht : t ∈ plGroupoid 3 := by
    rw [htdef]
    exact StructureGroupoid.compatible_of_mem_maximalAtlas he he'
  have htpa : IsPiecewiseAffineOn t t.source := (mem_plGroupoid_iff.mp ht).1
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
  have h₂ := h₁.postcomp_openPartialHomeomorph t htpa hmaps (htsource y hyW)
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

/-- **Atlas transport for the normality crossing condition.**  A PL normal double crossing
available in some chart of the maximal `plGroupoid 3` atlas around `y` is available in a
chart of the atlas itself, in exactly the shape the crossing condition of a normal singular
cell asks for. -/
theorem exists_crossing_chart_mem_atlas [HasGroupoid M (plGroupoid 3)]
    {D : EuclideanSpace ℝ (Fin 2) → M} {P : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {y : M}
    (h : HasPLNormalDoubleCrossingAt (e ∘ D) (P ∩ D ⁻¹' e.source)
      (e '' (e.source ∩ BdM)) (e y))
    (hD : ContinuousOn D P) (he : e ∈ (plGroupoid 3).maximalAtlas M) (hy : y ∈ e.source) :
    ∃ e' ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e'.source ∧
      HasPLNormalDoubleCrossingAt (e' ∘ D) (P ∩ D ⁻¹' e'.source)
        (e' '' (e'.source ∩ BdM)) (e' y) :=
  ⟨chartAt (EuclideanSpace ℝ (Fin 3)) y, chart_mem_atlas _ y, mem_chart_source _ y,
    h.of_mem_maximalAtlas hD he ((plGroupoid 3).chart_mem_maximalAtlas y) hy
      (mem_chart_source _ y)⟩

/-- A double point of `A` over which `A` and `G` have the same fibre, the two cells having
the same source disk, is a double point of `G`. -/
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

/-- **The step of the finite cover normalisation.**  Let `A` be a perturbation of `G` over
the same source disk whose fibres agree with those of `G` over every point outside `V`, and
suppose every double point of `G` in `U` carries a crossing chart.  Then every double point
of `A` in `U` away from `closure V` carries one as well.

Only the fibres are compared, never the maps themselves, because that is what the locality
lemmas for the crossing predicates consume; and `closure V` rather than `V` appears because
the transfer needs the fibres to agree at every point *near* the double point.  Note that
`y ∈ doublePointSet A A.domain` together with `y ∉ V` already forces
`y ∈ doublePointSet G G.domain`, so no containment of double point sets is assumed. -/
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

/-- The step of the finite cover normalisation, in the form an induction consumes: the set
of double points carrying a crossing chart is retained outside `closure V`. -/
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

/-- Non-degeneracy of the step lemma at the extreme `V = ∅`: a perturbation with the same
fibres everywhere retains the crossing charts on all of `U`, with nothing removed.  This is
the instance that shows the conclusion is not vacuous for a nonempty `U`. -/
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
