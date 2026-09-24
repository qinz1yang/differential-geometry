/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensIsolation

/-! # Section34Lens Images -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem locallyFinite_image_of_embedding {X Y ι : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {U : Set X} {h : X → Y}
    (hh : IsEmbedding (U.domRestrict h)) {A : ι → Set X} (hAU : ∀ i, A i ⊆ U)
    (hlf : LocallyFinite fun i => {x : U | (x : X) ∈ A i}) :
    LocallyFinite fun i => {y : h '' U | (y : Y) ∈ h '' A i} := by
  let f : U → h '' U := fun x => ⟨h x, x, x.2, rfl⟩
  have hf : IsEmbedding f := hh.codRestrict (h '' U) fun x => ⟨x, x.2, rfl⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let H := hf.toHomeomorphOfSurjective hsurj
  have heq : (fun i => {y : h '' U | (y : Y) ∈ h '' A i}) =
      fun i => H.symm ⁻¹' {x : U | (x : X) ∈ A i} := by
    funext i
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hfx : H ⟨x, hAU i hx⟩ = y := Subtype.ext hxy
      have hxinv : H.symm y = ⟨x, hAU i hx⟩ := (H.symm_apply_eq).mpr hfx.symm
      change (H.symm y : X) ∈ A i
      rw [hxinv]
      exact hx
    · intro hy
      refine ⟨H.symm y, hy, ?_⟩
      exact congrArg Subtype.val (H.apply_symm_apply y)
  rw [heq]
  exact hlf.preimage_continuous H.symm.continuous

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Cp : Section34VertexIndex 𝒦 𝒦' → Set M₁}

theorem section34_lens_images [TopologicalSpace M₂] (hh : IsEmbedding (U.domRestrict h))
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hcompact : ∀ w, IsCompact (Cp w)) (hCpU : ∀ w, Cp w ⊆ U)
    (hlf : LocallyFinite fun w => {x : U | (x : M₁) ∈ Cp w})
    (hdisj : ∀ e d, e ≠ d →
      Disjoint (Cp (ends e).1 ∩ Cp (ends e).2) (Cp (ends d).1 ∩ Cp (ends d).2)) :
    (∀ w, IsCompact (h '' Cp w)) ∧ (∀ w, h '' Cp w ⊆ h '' U) ∧
      (LocallyFinite fun e => (Subtype.val : h '' U → M₂) ⁻¹'
        ((h '' Cp (ends e).1) ∩ (h '' Cp (ends e).2))) ∧
      ∀ e d, e ≠ d → Disjoint
        ((h '' Cp (ends e).1) ∩ (h '' Cp (ends e).2))
        ((h '' Cp (ends d).1) ∩ (h '' Cp (ends d).2)) := by
  have hcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h U := fun x hx y hy hxy =>
    congrArg Subtype.val (@hh.injective ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  have htarget := locallyFinite_image_of_embedding hh hCpU hlf
  have hfib : ∀ w, {e | (ends e).1 = w}.Finite := by
    intro w
    have hfin : {e | w = (ends e).1 ∨ w = (ends e).2}.Finite :=
      finite_coe_iff.mp (section34_incident_edges_finite hends w)
    exact hfin.subset fun e he => Or.inl he.symm
  have heq : ∀ e, h '' (Cp (ends e).1 ∩ Cp (ends e).2) =
      (h '' Cp (ends e).1) ∩ (h '' Cp (ends e).2) := fun e =>
    hinj.image_inter (hCpU (ends e).1) (hCpU (ends e).2)
  refine ⟨fun w => (hcompact w).image_of_continuousOn (hcont.mono (hCpU w)),
    fun w => image_mono (hCpU w), ?_, ?_⟩
  · exact locallyFinite_subtype_of_subset_of_finite_fibers
      (fun e => (h '' Cp (ends e).1) ∩ (h '' Cp (ends e).2)) (fun w => h '' Cp w)
      (fun e => (ends e).1) (fun e => inter_subset_left) hfib htarget
  · intro e d hed
    rw [← heq e, ← heq d]
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz : x = z := hinj (hCpU (ends e).1 hx.1) (hCpU (ends d).1 hz.1)
      (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (hdisj e d hed) hx (hxz.symm ▸ hz)

theorem exists_section34_overlap_isolation_scales [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hcompact : ∀ w, IsCompact (Cp w)) (hCpU : ∀ w, Cp w ⊆ U)
    (hlf : LocallyFinite fun w => {x : U | (x : M₁) ∈ Cp w})
    (hdisj : ∀ e d, e ≠ d →
      Disjoint (Cp (ends e).1 ∩ Cp (ends e).2) (Cp (ends d).1 ∩ Cp (ends d).2))
    (cap : Section34VertexIndex 𝒦 𝒦' → ℝ) (hcap : ∀ w, 0 < cap w) :
    ∃ ε : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < ε w) ∧ (∀ w, ε w < cap w) ∧
      ∀ e d, e ≠ d →
        Disjoint (section34CellThickening h Cp ε (ends e).1 ∩
          section34CellThickening h Cp ε (ends e).2)
        (section34CellThickening h Cp ε (ends d).1 ∩
          section34CellThickening h Cp ε (ends d).2) := by
  obtain ⟨hA, hAU, hAlf, hAd⟩ := section34_lens_images hh hends hcompact hCpU hlf hdisj
  have hcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h U := fun x hx y hy hxy =>
    congrArg Subtype.val (@hh.injective ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  have hΩ : IsOpen (h '' U) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hU hcont hinj
  obtain ⟨ε, hε, hεcap, -, hεdisj⟩ :=
    exists_section34_vertex_scales_with_isolated_overlaps h Cp ends hends hA hΩ hAU hAlf hAd
      cap hcap (fun _ => 1) (fun _ => zero_lt_one)
  exact ⟨ε, hε, hεcap, hεdisj⟩

end DifferentialGeometry.Topology.PiecewiseLinear
