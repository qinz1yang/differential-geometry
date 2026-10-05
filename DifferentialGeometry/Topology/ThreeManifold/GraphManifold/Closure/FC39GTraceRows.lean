import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceTop
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceSign
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# FC39 GROUP G, lane FC39-G-TRACE: HH impossible, saturation, classification of labels

External draft task 58 §二 F2 and §四 A2 (disposition D58-3; sheet
`build-logs/resume/sheet-FC39-G-TRACE.md`). All statements are about ONE `Rw : FC39RowsV2 W E`.

* the residual face equations, read from the row fields: `residualSet_subset_GTR` (R1),
  `residualFn_smoothOn_GTR` (R2), `residualFn_regular_GTR` (R3), `residualFn_nonpos_subset_GTR`
  (R4, owner side), `residualNear_subset_interior_GTR` (R5);
* **HH, different owners**: `false_of_two_owners_GTR` — at a point of the circle region over `∂C₁`
  two residual faces of different owners cannot meet: the region side (`local_faces` pulled back by
  the projection, with a common descent direction from the submersion) and the two owner sides
  (`interiors_disjoint`) contradict `false_of_three_sides_GTR`;
* `residualFace_eq_of_mem_region_GTR` (a point of the circle region lies on at most one residual
  face), `baseTrace_horizontal_disjoint_GTR` (HH impossible);
* **saturation (A2)** `mem_baseTrace_of_mem_residualSet_GTR`, `residualSet_inter_region_eq_tube_GTR`:
  a point of the circle region on a residual face has its WHOLE fibre in that face;
* **classification** `label_classification_GTR` (two labels at a point: one vertical, one horizontal,
  at a registered rim base point), `labels_rimBase_eq_GTR`, `labels_subsingleton_GTR`,
  `ncard_labels_le_two_GTR`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-! ## The residual face equations -/

/-- (R1) A residual face lies in its face neighbourhood, on the zero set of its function. -/
theorem residualSet_subset_GTR : ∀ F : Rw.slim.ResidualFace,
    Rw.slim.residualSet F ⊆
      {x | x ∈ Rw.slim.residualNear F ∧ Rw.slim.residualFn F x = 0}
  | .inl ⟨.inl ⟨i, A⟩, _⟩ => by
    intro x hx
    have hb : x ∈ pieceBoundary (Rw.zero.piece i) := image_mono A.subset hx
    rw [Rw.zero.boundary_eq i] at hb
    exact ⟨Rw.zero.zero_subset_near i hb, hb⟩
  | .inl ⟨.inr ⟨b, A, hA⟩, _⟩ => by
    intro x hx
    subst hA
    have h : x ∈ range fun t => (Rw.cusp.piece b).map (Rw.cusp.product b (t, iccEnd true)) := by
      obtain ⟨q, hq, rfl⟩ := hx
      rw [Rw.cusp.internalModelFace_eq b] at hq
      obtain ⟨t, rfl⟩ := hq
      exact ⟨t, rfl⟩
    rw [Rw.cusp.internal_eq b] at h
    exact h
  | .inr e => by
    intro x hx
    have h : x ∈ (Rw.slim.piece e.1.1.1).map '' slimModelEnd (Rw.slim.model e.1.1.1) e.1.1.2 := hx
    rw [Rw.slim.endFn_level e] at h
    exact h

/-- (R2) The defining function of a residual face is smooth on its neighbourhood. -/
theorem residualFn_smoothOn_GTR : ∀ F : Rw.slim.ResidualFace,
    ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (Rw.slim.residualFn F) (Rw.slim.residualNear F)
  | .inl ⟨.inl F, _⟩ => (Rw.zero.ratio_smooth F.1).contMDiffOn
  | .inl ⟨.inr F, _⟩ => Rw.cusp.fn_smooth F.1
  | .inr e => Rw.slim.endFn_smooth e

/-- (R3) Every zero of the defining function of a residual face on its neighbourhood is regular. -/
theorem residualFn_regular_GTR : ∀ F : Rw.slim.ResidualFace, ∀ x ∈ Rw.slim.residualNear F,
    Rw.slim.residualFn F x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (Rw.slim.residualFn F) x ≠ 0
  | .inl ⟨.inl F, _⟩ => fun x _ h => Rw.zero.ratio_regular F.1 x h
  | .inl ⟨.inr F, _⟩ => Rw.cusp.fn_regular F.1
  | .inr e => Rw.slim.endFn_regular e

/-- (R4) The nonpositive side of a residual face (on its neighbourhood) lies in its owner. -/
theorem residualFn_nonpos_subset_GTR : ∀ F : Rw.slim.ResidualFace,
    {x | x ∈ Rw.slim.residualNear F ∧ Rw.slim.residualFn F x ≤ 0} ⊆
      Rw.slim.rowSet (Rw.slim.residualOwner F)
  | .inl ⟨.inl F, _⟩ => fun x hx => by
    change x ∈ range (Rw.zero.piece F.1).map
    rw [Rw.zero.range_eq]
    exact hx.2
  | .inl ⟨.inr F, _⟩ => fun x hx => by
    change x ∈ range (Rw.cusp.piece F.1).map
    have h : x ∈ {x | x ∈ Rw.cusp.near F.1 ∧ Rw.cusp.cuspFn F.1 x ≤ 0} := hx
    rw [← Rw.cusp.near_eq] at h
    exact h.1
  | .inr e => fun x hx => by
    change x ∈ range (Rw.slim.piece e.1.1.1).map
    have h : x ∈ {x | x ∈ Rw.slim.endNear e ∧ Rw.slim.endFn e x ≤ 0} := hx
    rw [← Rw.slim.endFn_eq] at h
    exact h.1

/-- (R5) The neighbourhood of a residual face lies in the interior of `W`. -/
theorem residualNear_subset_interior_GTR : ∀ F : Rw.slim.ResidualFace,
    (Rw.slim.residualNear F : Set W.Carrier) ⊆ W.interior
  | .inl ⟨.inl F, _⟩ => Rw.zero.near_interior F.1
  | .inl ⟨.inr F, _⟩ => Rw.cusp.near_interior F.1
  | .inr e => Rw.slim.endNear_interior e

/-- A residual face lies in `∂M₂`. -/
theorem residualSet_subset_boundaryM2_GTR (F : Rw.slim.ResidualFace) :
    Rw.slim.residualSet F ⊆ Rw.slim.boundaryM2 :=
  subset_iUnion (Rw.slim.residualSet) F

/-- Two distinct residual faces of zero / cusp type are disjoint. -/
theorem residualSet_inl_disjoint_GTR
    {F F' : {F : NeighbourFace Rw.zero Rw.cusp // ∀ e, Rw.slim.endKind e ≠ some F}}
    (h : F ≠ F') :
    Disjoint (Rw.slim.residualSet (.inl F)) (Rw.slim.residualSet (.inl F')) :=
  Rw.neighbourSet_disjoint_GSAFE fun h' => h (Subtype.ext h')

/-- Two distinct new slim ends are disjoint. -/
theorem residualSet_inr_disjoint_GTR {e e' : Rw.slim.NewEnd} (h : e ≠ e') :
    Disjoint (Rw.slim.residualSet (.inr e)) (Rw.slim.residualSet (.inr e')) :=
  Rw.slim.endSet_disjoint_GSAFE fun h' => h (Subtype.ext h')

/-- A zero / cusp residual face and a new slim end have different owners. -/
theorem residualOwner_inl_ne_inr_GTR
    (F : {F : NeighbourFace Rw.zero Rw.cusp // ∀ e, Rw.slim.endKind e ≠ some F})
    (e : Rw.slim.NewEnd) :
    Rw.slim.residualOwner (.inl F) ≠ Rw.slim.residualOwner (.inr e) := by
  obtain ⟨F | F, hF⟩ := F <;> simp [SlimPiecesV2.residualOwner]

/-! ## HH for different owners: the three-sides argument -/

/-- On a `local_faces` neighbourhood, the strict negative side of the labelled functions lies in
the interior of `C₁`. -/
theorem mem_interior_cbase_of_neg_GTR {U : Set Rw.circle.Base} (hU : IsOpen U)
    {L : Finset Rw.CircleFace} {φ : Rw.CircleFace → Rw.circle.Base → ℝ}
    (hφc : ∀ f ∈ L, ContinuousOn (φ f) U)
    (hcb : Rw.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0})
    {c : Rw.circle.Base} (hcU : c ∈ U) (hneg : ∀ f ∈ L, φ f c < 0) :
    c ∈ interior Rw.circle.cbase := by
  have hopen : IsOpen (U ∩ ⋂ f ∈ L, (U ∩ φ f ⁻¹' Iio 0)) :=
    hU.inter (isOpen_biInter_finset fun f hf => (hφc f hf).isOpen_inter_preimage hU isOpen_Iio)
  refine interior_maximal ?_ hopen ⟨hcU, mem_iInter₂.2 fun f hf => ⟨hcU, hneg f hf⟩⟩
  rintro c' ⟨hc'U, hc'⟩
  have h : c' ∈ {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} :=
    ⟨hc'U, fun f hf => le_of_lt (mem_iInter₂.1 hc' f hf).2⟩
  rw [← hcb] at h
  exact h.1

/-- The tube over the interior of `C₁` lies in the interior of the circle region. -/
theorem tube_interior_subset_interior_region_GTR :
    Rw.circle.tube (interior Rw.circle.cbase) ⊆ interior Rw.circle.region :=
  interior_maximal (Rw.circle.tube_mono_GSAFE interior_subset)
    (Rw.circle.isOpen_tube_GTR isOpen_interior)

/-- The strict negative side of a residual face (on its neighbourhood) lies in the interior of its
owner. -/
theorem residualFn_neg_subset_interior_GTR (F : Rw.slim.ResidualFace) {x : W.Carrier}
    (hx : x ∈ Rw.slim.residualNear F) (hneg : Rw.slim.residualFn F x < 0) :
    x ∈ interior (Rw.slim.rowSet (Rw.slim.residualOwner F)) := by
  have hopen : IsOpen ((Rw.slim.residualNear F : Set W.Carrier) ∩
      Rw.slim.residualFn F ⁻¹' Iio 0) :=
    (Rw.residualFn_smoothOn_GTR F).continuousOn.isOpen_inter_preimage
      (Rw.slim.residualNear F).isOpen isOpen_Iio
  refine interior_maximal ?_ hopen ⟨hx, hneg⟩
  rintro y ⟨hy, hy'⟩
  exact Rw.residualFn_nonpos_subset_GTR F ⟨hy, le_of_lt hy'⟩

/-- **HH, different owners.** At a point of the circle domain over `∂C₁`, two residual faces with
different owners cannot meet. -/
theorem false_of_two_owners_GTR {x : Rw.circle.domain}
    (hc : Rw.circle.proj x ∈ frontier Rw.circle.cbase) {F F' : Rw.slim.ResidualFace}
    (hown : Rw.slim.residualOwner F ≠ Rw.slim.residualOwner F')
    (hF : (x : W.Carrier) ∈ Rw.slim.residualSet F)
    (hF' : (x : W.Carrier) ∈ Rw.slim.residualSet F') : False := by
  obtain ⟨U, hcU, L, φ, -, -, hφ, hsurj, hcb⟩ := Rw.junctions.local_faces _ hc
  have hxint : W.model.IsInteriorPoint x :=
    ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.2 (Rw.circle.domain_interior x.2)
  have hφat : ∀ f ∈ L, MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (φ f) (Rw.circle.proj x) := fun f hf =>
    ((hφ f hf).1.contMDiffAt (U.isOpen.mem_nhds hcU)).mdifferentiableAt (by decide)
  have hproj : MDifferentiableAt W.model (𝓡 2) Rw.circle.proj x :=
    (Rw.circle.proj_smooth x).mdifferentiableAt (by decide)
  obtain ⟨w, hw⟩ := hsurj (fun _ => -1)
  obtain ⟨v, hv⟩ := Rw.circle.proj_submersion x w
  have hψd : ∀ f ∈ L, MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun y => φ f (Rw.circle.proj y)) x :=
    fun f hf => (hφat f hf).comp x hproj
  have hv₀ : ∀ f ∈ L, dirDeriv_GTR W.model (fun y => φ f (Rw.circle.proj y)) x v < 0 := by
    intro f hf
    have hval : dirDeriv_GTR W.model (fun y => φ f (Rw.circle.proj y)) x v = -1 := by
      have hcomp := mfderiv_comp x (hφat f hf) hproj
      have h1 := congrFun hw ⟨f, hf⟩
      simp only at h1
      unfold dirDeriv_GTR mderivR_GTR
      change ((mfderiv W.model 𝓘(ℝ, ℝ) (φ f ∘ Rw.circle.proj) x) v : ℝ) = -1
      rw [hcomp, ContinuousLinearMap.comp_apply, hv]
      exact h1
    rw [hval]
    norm_num
  have hxN := (Rw.residualSet_subset_GTR F hF).1
  have hxN' := (Rw.residualSet_subset_GTR F' hF').1
  have had : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun y : Rw.circle.domain => Rw.slim.residualFn F y) x :=
    mdifferentiableAt_subtype_iff.2
      (((Rw.residualFn_smoothOn_GTR F).contMDiffAt
        ((Rw.slim.residualNear F).isOpen.mem_nhds hxN)).mdifferentiableAt (by decide))
  have had' : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun y : Rw.circle.domain => Rw.slim.residualFn F' y) x :=
    mdifferentiableAt_subtype_iff.2
      (((Rw.residualFn_smoothOn_GTR F').contMDiffAt
        ((Rw.slim.residualNear F').isOpen.mem_nhds hxN')).mdifferentiableAt (by decide))
  have hda : mfderiv W.model 𝓘(ℝ, ℝ) (fun y : Rw.circle.domain => Rw.slim.residualFn F y) x ≠ 0 := by
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact Rw.residualFn_regular_GTR F _ hxN (Rw.residualSet_subset_GTR F hF).2
  have hda' : mfderiv W.model 𝓘(ℝ, ℝ) (fun y : Rw.circle.domain => Rw.slim.residualFn F' y) x ≠
      0 := by
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact Rw.residualFn_regular_GTR F' _ hxN' (Rw.residualSet_subset_GTR F' hF').2
  have hR : ∀ᶠ y in 𝓝 x, (∀ f ∈ L, φ f (Rw.circle.proj y) < 0) →
      y ∈ {y : Rw.circle.domain | (y : W.Carrier) ∈ interior Rw.circle.region} := by
    filter_upwards [(U.isOpen.preimage Rw.circle.proj.continuous).mem_nhds hcU] with y hyU hneg
    have hyint := Rw.mem_interior_cbase_of_neg_GTR U.isOpen (fun f hf => (hφ f hf).1.continuousOn)
      hcb hyU hneg
    exact Rw.tube_interior_subset_interior_region_GTR ⟨y, hyint, rfl⟩
  have hA : ∀ᶠ y : Rw.circle.domain in 𝓝 x, Rw.slim.residualFn F (y : W.Carrier) < 0 →
      y ∈ {y : Rw.circle.domain |
        (y : W.Carrier) ∈ interior (Rw.slim.rowSet (Rw.slim.residualOwner F))} := by
    filter_upwards [((Rw.slim.residualNear F).isOpen.preimage continuous_subtype_val).mem_nhds hxN]
      with y hy hneg
    exact Rw.residualFn_neg_subset_interior_GTR F hy hneg
  have hA' : ∀ᶠ y : Rw.circle.domain in 𝓝 x, Rw.slim.residualFn F' (y : W.Carrier) < 0 →
      y ∈ {y : Rw.circle.domain |
        (y : W.Carrier) ∈ interior (Rw.slim.rowSet (Rw.slim.residualOwner F'))} := by
    filter_upwards [((Rw.slim.residualNear F').isOpen.preimage continuous_subtype_val).mem_nhds
      hxN'] with y hy hneg
    exact Rw.residualFn_neg_subset_interior_GTR F' hy hneg
  have hdisj : ∀ a a' : Rw.slim.RowIndex ⊕ Bool, a ≠ a' →
      Disjoint {y : Rw.circle.domain | (y : W.Carrier) ∈ interior (allPieces Rw.slim Rw.edge
          Rw.circle a)}
        {y : Rw.circle.domain | (y : W.Carrier) ∈ interior (allPieces Rw.slim Rw.edge
          Rw.circle a')} := fun a a' h =>
    Set.disjoint_left.2 fun y hy hy' =>
      Set.disjoint_left.1 (Rw.junctions.interiors_disjoint h) hy hy'
  exact false_of_three_sides_GTR hxint L (fun f y => φ f (Rw.circle.proj y)) hψd
    (fun f hf => (hφ f hf).2.1) hv₀ had (Rw.residualSet_subset_GTR F hF).2 hda had'
    (Rw.residualSet_subset_GTR F' hF').2 hda' hR hA hA'
    (hdisj (.inr false) (.inl _) (by simp)) (hdisj (.inr false) (.inl _) (by simp))
    (hdisj (.inl _) (.inl _) fun h => hown (Sum.inl_injective h))

/-- **A point of the circle region lies on at most one residual face.** -/
theorem residualFace_eq_of_mem_region_GTR {x : W.Carrier} (hx : x ∈ Rw.circle.region)
    {F F' : Rw.slim.ResidualFace} (hF : x ∈ Rw.slim.residualSet F)
    (hF' : x ∈ Rw.slim.residualSet F') : F = F' := by
  obtain ⟨y, hyc, rfl⟩ := hx
  have hfr : Rw.circle.proj y ∈ frontier Rw.circle.cbase :=
    Rw.mem_frontier_cbase_of_fibre_GTR hyc ⟨y, rfl, rfl⟩ (Rw.residualSet_subset_boundaryM2_GTR F hF)
  by_contra hne
  rcases F with F | e <;> rcases F' with F' | e'
  · exact Set.disjoint_left.1 (Rw.residualSet_inl_disjoint_GTR fun h => hne (congrArg _ h)) hF hF'
  · exact Rw.false_of_two_owners_GTR hfr (Rw.residualOwner_inl_ne_inr_GTR F e') hF hF'
  · exact Rw.false_of_two_owners_GTR hfr (Rw.residualOwner_inl_ne_inr_GTR F' e).symm hF hF'
  · exact Set.disjoint_left.1 (Rw.residualSet_inr_disjoint_GTR fun h => hne (congrArg _ h)) hF hF'

/-- **F2 (HH impossible)** Distinct residual faces have disjoint traces. -/
theorem baseTrace_horizontal_disjoint_GTR {F F' : Rw.slim.ResidualFace} (h : F ≠ F') :
    Disjoint (Rw.baseTrace (.horizontal F)) (Rw.baseTrace (.horizontal F')) := by
  refine Set.disjoint_left.2 fun c hc hc' => h ?_
  obtain ⟨x, hx⟩ := Rw.circle.fibre_nonempty_GSAFE c
  exact Rw.residualFace_eq_of_mem_region_GTR (Rw.circle.fibre_subset_region_GTR hc.1 hx)
    (hc.2 hx) (hc'.2 hx)

/-! ## Saturation (A2) -/

/-- **Saturation.** A point of the circle domain over `C₁` lying on a residual face has its whole
fibre in that face. -/
theorem mem_baseTrace_of_mem_residualSet_GTR {x : Rw.circle.domain}
    (hxc : Rw.circle.proj x ∈ Rw.circle.cbase) {G : Rw.slim.ResidualFace}
    (hxG : (x : W.Carrier) ∈ Rw.slim.residualSet G) :
    Rw.circle.proj x ∈ Rw.baseTrace (.horizontal G) := by
  have hxf : (x : W.Carrier) ∈ Rw.circle.fibre (Rw.circle.proj x) := ⟨x, rfl, rfl⟩
  have hfr := Rw.mem_frontier_cbase_of_fibre_GTR hxc hxf (Rw.residualSet_subset_boundaryM2_GTR G hxG)
  obtain ⟨f, hf⟩ := Rw.exists_mem_baseTrace_GTR hfr
  rcases f with G' | C
  · have hGG : G' = G := Rw.residualFace_eq_of_mem_region_GTR
      (Rw.circle.fibre_subset_region_GTR hxc hxf) (hf.2 hxf) hxG
    rw [← hGG]
    exact hf
  · have hv := hf
    rw [Rw.baseTrace_vertical_eq_GTR] at hv
    obtain ⟨c₂, hc₂, hc₂eq⟩ := hv
    have hc₂' : c₂ ∈ Rw.edge.cbase := C.subset hc₂
    have hxr : (x : W.Carrier) ∈ Rw.edge.rim c₂ := by
      rw [Rw.junctions.rim_fibre _ hc₂', hc₂eq]
      exact hxf
    have hxP : (x : W.Carrier) ∈ Rw.edge.edgePiece ∩ Rw.slim.residualSet G :=
      ⟨Rw.edge.disk_subset_edgePiece_GSAFE hc₂' (Rw.edge.rim_subset_disk_GSAFE _ hxr), hxG⟩
    rw [Rw.junctions.edge_faces G] at hxP
    obtain ⟨e, hxE⟩ := mem_iUnion.1 hxP
    obtain ⟨heG, hxe⟩ := mem_iUnion.1 hxE
    have hce : c₂ = e.1 := by
      by_contra hne
      exact Set.disjoint_left.1 (Rw.edge.disk_disjoint hne) (Rw.edge.rim_subset_disk_GSAFE _ hxr) hxe
    rw [← hc₂eq, hce, ← heG]
    exact Rw.rimBase_mem_baseTrace_horizontal_GTR e

/-- **Saturation (A2), set form.** The part of a residual face in the circle region is the whole
circle preimage of its trace. -/
theorem residualSet_inter_region_eq_tube_GTR (G : Rw.slim.ResidualFace) :
    Rw.slim.residualSet G ∩ Rw.circle.region = Rw.circle.tube (Rw.baseTrace (.horizontal G)) := by
  apply Subset.antisymm
  · rintro _ ⟨hxG, y, hyc, rfl⟩
    exact ⟨y, Rw.mem_baseTrace_of_mem_residualSet_GTR hyc hxG, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hyf : (y : W.Carrier) ∈ Rw.circle.fibre (Rw.circle.proj y) := ⟨y, rfl, rfl⟩
    exact ⟨hy.2 hyf, y, hy.1, rfl⟩

/-! ## Classification of the labels at a point -/

/-- **Classification.** Two distinct labels at a point: one vertical and one horizontal, and the
point is the registered rim base point of an endpoint carrying both labels. -/
theorem label_classification_GTR {c : Rw.circle.Base} {f f' : Rw.CircleFace}
    (hf : c ∈ Rw.baseTrace f) (hf' : c ∈ Rw.baseTrace f') (hne : f ≠ f') :
    ∃ e : Rw.edge.EdgeEnd, c = Rw.junctions.rimBase e.1 ∧
      ((f = .vertical e.component ∧ f' = .horizontal (Rw.junctions.horizontal e)) ∨
        (f = .horizontal (Rw.junctions.horizontal e) ∧ f' = .vertical e.component)) := by
  rcases f with F | C <;> rcases f' with F' | C'
  · exact absurd (Set.disjoint_left.1 (Rw.baseTrace_horizontal_disjoint_GTR
      fun h => hne (congrArg _ h)) hf hf') id
  · have h : c ∈ Rw.baseTrace (.vertical C') ∩ Rw.baseTrace (.horizontal F) := ⟨hf', hf⟩
    rw [Rw.baseTrace_vertical_inter_horizontal_GTR] at h
    obtain ⟨e, ⟨heC, heF⟩, rfl⟩ := h
    exact ⟨e, rfl, Or.inr ⟨heF ▸ rfl, heC ▸ rfl⟩⟩
  · have h : c ∈ Rw.baseTrace (.vertical C) ∩ Rw.baseTrace (.horizontal F') := ⟨hf, hf'⟩
    rw [Rw.baseTrace_vertical_inter_horizontal_GTR] at h
    obtain ⟨e, ⟨heC, heF⟩, rfl⟩ := h
    exact ⟨e, rfl, Or.inl ⟨heC ▸ rfl, heF ▸ rfl⟩⟩
  · exact absurd (Set.disjoint_left.1 (Rw.baseTrace_vertical_disjoint_GTR
      fun h => hne (congrArg _ h)) hf hf') id

/-- **The labels at a registered rim base point** are exactly its vertical and horizontal labels. -/
theorem labels_rimBase_eq_GTR (e : Rw.edge.EdgeEnd) :
    {f : Rw.CircleFace | Rw.junctions.rimBase e.1 ∈ Rw.baseTrace f} =
      {.vertical e.component, .horizontal (Rw.junctions.horizontal e)} := by
  ext f
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hf
    by_cases hv : f = .vertical e.component
    · exact Or.inl hv
    · obtain ⟨e', he', hcases⟩ := Rw.label_classification_GTR hf
        (Rw.rimBase_mem_baseTrace_vertical_GTR e) hv
      have hee : e = e' := Rw.rimBase_injective_GSAFE he'
      subst hee
      rcases hcases with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h (by simp)
      · exact Or.inr h
  · rintro (rfl | rfl)
    · exact Rw.rimBase_mem_baseTrace_vertical_GTR e
    · exact Rw.rimBase_mem_baseTrace_horizontal_GTR e

/-- **Away from the registered rim base points a point carries at most one label.** -/
theorem labels_subsingleton_GTR {c : Rw.circle.Base}
    (hc : ∀ e : Rw.edge.EdgeEnd, c ≠ Rw.junctions.rimBase e.1) :
    {f : Rw.CircleFace | c ∈ Rw.baseTrace f}.Subsingleton := by
  intro f hf f' hf'
  by_contra hne
  obtain ⟨e, he, -⟩ := Rw.label_classification_GTR hf hf' hne
  exact hc e he

/-- **Depth at most two:** every point carries at most two labels. -/
theorem ncard_labels_le_two_GTR (c : Rw.circle.Base) :
    {f : Rw.CircleFace | c ∈ Rw.baseTrace f}.ncard ≤ 2 := by
  by_cases hc : ∃ e : Rw.edge.EdgeEnd, c = Rw.junctions.rimBase e.1
  · obtain ⟨e, rfl⟩ := hc
    rw [Rw.labels_rimBase_eq_GTR e]
    exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])
  · push Not at hc
    have := Rw.finite_circleFace_GTR
    exact (Set.ncard_le_one_iff_subsingleton.2 (Rw.labels_subsingleton_GTR hc)).trans
      (by norm_num)

end FC39RowsV2

end GC.GraphManifold.Assembly.FC39P0
