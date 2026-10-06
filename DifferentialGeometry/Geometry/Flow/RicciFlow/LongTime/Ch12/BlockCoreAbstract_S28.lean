import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationMain
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.ConnectedInterior

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

section Sets

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)
  (W : CompactCarrier.{u}) (φ : W.Carrier → M.Carrier)

/-- The image of the open core. -/
def coreImage_S28 : Set M.Carrier := φ '' (W.interior : Set W.Carrier)

theorem coreImage_subset_interiorImage_S28
    (hc : ∀ x ∈ (W.interior : Set W.Carrier), φ x ∉ zeroSet_S12 F) :
    coreImage_S28 W φ ⊆ (interiorImage_S12 F : Set M.Carrier) := by
  rintro _ ⟨x, hx, rfl⟩
  exact hc x hx

/-- Points of `K°` mapping into the core image: they also map into the closed image. -/
theorem rmapK_mem_core_iff_S28
    (hd : ∀ x ∈ W.model.boundary W.Carrier, φ x ∈ zeroSet_S12 F)
    {x : (cutCarrier_C2a F).Carrier} (hx : x ∈ (cutCarrier_C2a F).interior) :
    rmapK_S12 F x ∈ coreImage_S28 W φ ↔ rmapK_S12 F x ∈ range φ := by
  constructor
  · rintro ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_, hy⟩
    rcases W.model.isInteriorPoint_or_isBoundaryPoint y with h | h
    · exact h
    · exfalso
      exact rmapK_interior_mem_S12 F hx (hy ▸ hd y h)

/-- **Block = core, set level.** `φ` maps the interior of a connected compact carrier `W`
as an open map into `M` (so the image `E` is open), avoiding the cut tori with interior, and
mapping the boundary into them.  Then `E` is exactly the interior of one piece of the cut
(read through `rmapK`), and every other piece interior avoids `E`. -/
theorem blockCore_sets_S28 [ConnectedSpace W.Carrier] (hφ : Continuous φ)
    (hopen : IsOpen (coreImage_S28 W φ))
    (hc : ∀ x ∈ (W.interior : Set W.Carrier), φ x ∉ zeroSet_S12 F)
    (hd : ∀ x ∈ W.model.boundary W.Carrier, φ x ∈ zeroSet_S12 F)
    (Dc : (cutCarrier_C2a F).Components) :
    ∃ j : Fin Dc.count,
      (∀ x : (cutCarrier_C2a F).Carrier,
        x ∈ (cutCarrier_C2a F).pieceInterior (Dc.piece j) ↔
          x ∈ (cutCarrier_C2a F).interior ∧ rmapK_S12 F x ∈ coreImage_S28 W φ) ∧
      (∀ e ∈ coreImage_S28 W φ, ∃ x ∈ (cutCarrier_C2a F).pieceInterior (Dc.piece j),
        rmapK_S12 F x = e) ∧
      (∀ j' : Fin Dc.count, j' ≠ j → ∀ x ∈ (cutCarrier_C2a F).pieceInterior (Dc.piece j'),
        rmapK_S12 F x ∉ coreImage_S28 W φ) := by
  classical
  have hc' : ∀ x : W.interior, φ x.1 ∈ interiorImage_S12 F := fun x => hc x.1 x.2
  let g : W.interior → (cutCarrier_C2a F).Carrier :=
    fun x => ((interiorEquiv_S12 F).symm ⟨φ x.1, hc' x⟩).1
  have hg_cont : Continuous g := by
    have h1 : Continuous (fun x : W.interior => (⟨φ x.1, hc' x⟩ : interiorImage_S12 F)) :=
      (hφ.comp continuous_subtype_val).subtype_mk _
    have h2 := (contMDiff_interiorSymm_S12 F).continuous
    exact continuous_subtype_val.comp (h2.comp h1)
  have hmem : ∀ x : (cutCarrier_C2a F).Carrier, x ∈ range g ↔
      x ∈ (cutCarrier_C2a F).interior ∧ rmapK_S12 F x ∈ coreImage_S28 W φ := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨((interiorEquiv_S12 F).symm ⟨φ y.1, hc' y⟩).2, y.1, y.2, ?_⟩
      have := congrArg Subtype.val ((interiorEquiv_S12 F).apply_symm_apply ⟨φ y.1, hc' y⟩)
      exact this.symm
    · rintro ⟨hx, y, hy, hyx⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      exact interiorEquiv_symm_val_S12 F ⟨φ y, hc' ⟨y, hy⟩⟩ x hx hyx.symm
  have : Nonempty W.Carrier := inferInstance
  have hne : (W.interior : Set W.Carrier).Nonempty :=
    (dense_manifold_interior (I := W.model) (M := W.Carrier)).nonempty
  have : Nonempty W.interior := hne.to_subtype
  have : PreconnectedSpace W.interior :=
    isPreconnected_iff_preconnectedSpace.mp
      (isPreconnected_manifold_interior (I := W.model) (M := W.Carrier))
  have hpre : IsPreconnected (range g) := isPreconnected_range hg_cont
  obtain ⟨j, hj⟩ := exists_owner_S12 F Dc hpre (range_nonempty g)
  have hrange : IsClosed (range φ) := (isCompact_range hφ).isClosed
  have hP : IsPreconnected ((cutCarrier_C2a F).pieceInterior (Dc.piece j) :
      Set (cutCarrier_C2a F).Carrier) :=
    isPreconnected_iff_preconnectedSpace.mpr (Dc.interior_connected j).toPreconnectedSpace
  have hrg : ∀ x ∈ range g, x ∈ (cutCarrier_C2a F).pieceInterior (Dc.piece j) :=
    fun x hx => ⟨hj hx, ((hmem x).mp hx).1⟩
  have key : ∀ x : (cutCarrier_C2a F).Carrier,
      x ∈ (cutCarrier_C2a F).pieceInterior (Dc.piece j) ↔
        x ∈ (cutCarrier_C2a F).interior ∧ rmapK_S12 F x ∈ coreImage_S28 W φ := by
    intro x
    constructor
    · intro hx
      refine ⟨hx.2, ?_⟩
      obtain ⟨x0, hx0⟩ := range_nonempty g
      have hcont := contMDiff_rmapK_S12 F |>.continuous
      have h := (isPreconnected_iff_subset_of_disjoint.mp hP)
        {x | rmapK_S12 F x ∈ coreImage_S28 W φ} {x | rmapK_S12 F x ∉ range φ}
        (hopen.preimage hcont) (hrange.isOpen_compl.preimage hcont)
        (fun y hy => by
          by_cases h : rmapK_S12 F y ∈ range φ
          · exact Or.inl ((rmapK_mem_core_iff_S28 F W φ hd hy.2).mpr h)
          · exact Or.inr h)
        (by
          ext y
          simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro _ h1 h2
          exact h2 (by obtain ⟨z, -, hz⟩ := h1; exact ⟨z, hz⟩))
      rcases h with h | h
      · exact h hx
      · exfalso
        have := h (hrg x0 hx0)
        obtain ⟨z, -, hz⟩ := ((hmem x0).mp hx0).2
        exact this ⟨z, hz⟩
    · intro hx
      exact hrg x ((hmem x).mpr hx)
  refine ⟨j, key, ?_, ?_⟩
  · intro e he
    have he' : e ∈ (interiorImage_S12 F : Set M.Carrier) :=
      coreImage_subset_interiorImage_S28 F W φ hc he
    have hrx : rmapK_S12 F ((interiorEquiv_S12 F).symm ⟨e, he'⟩).1 = e :=
      congrArg Subtype.val ((interiorEquiv_S12 F).apply_symm_apply ⟨e, he'⟩)
    exact ⟨_, (key _).mpr ⟨((interiorEquiv_S12 F).symm ⟨e, he'⟩).2, by rw [hrx]; exact he⟩, hrx⟩
  · intro j' hj' x hx hxE
    have h1 : x ∈ (cutCarrier_C2a F).pieceInterior (Dc.piece j) := (key x).mpr ⟨hx.2, hxE⟩
    exact Set.disjoint_left.mp (Dc.disjoint hj') hx.1 h1.1

end Sets

section Diffeo

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)
  (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] (φ : W.Carrier → M.Carrier)

/-- **Block = core (abstract form).**  Hypotheses: `φ` continuous, a local diffeomorphism on the
open core `W°` (hence an open map), injective there, sending `W°` off the cut tori and `∂W` into
them.  Conclusion: some piece of any `Components` structure of the cut carrier has interior
diffeomorphic to `W°` (through `rmapK ∘ -`), it is the only piece meeting `φ(W°)`, and
`rmapK` maps it onto `φ(W°)`. -/
theorem blockCore_diffeo_S28 (hφ : Continuous φ)
    (ha : IsLocalDiffeomorph W.model (𝓡 3) ∞ (fun x : W.interior => φ x.1))
    (hb : Injective (fun x : W.interior => φ x.1))
    (hc : ∀ x ∈ (W.interior : Set W.Carrier), φ x ∉ zeroSet_S12 F)
    (hd : ∀ x ∈ W.model.boundary W.Carrier, φ x ∈ zeroSet_S12 F)
    (Dc : (cutCarrier_C2a F).Components) :
    ∃ j : Fin Dc.count,
      Nonempty (Diffeomorph (cutCarrier_C2a F).model W.model
        ((cutCarrier_C2a F).pieceInterior (Dc.piece j)) W.interior ∞) ∧
      rmapK_S12 F '' ((cutCarrier_C2a F).pieceInterior (Dc.piece j) : Set _) =
        coreImage_S28 W φ ∧
      (∀ j' : Fin Dc.count, j' ≠ j →
        Disjoint (rmapK_S12 F '' ((cutCarrier_C2a F).pieceInterior (Dc.piece j') : Set _))
          (coreImage_S28 W φ)) := by
  have hopen : IsOpen (coreImage_S28 W φ) := by
    have h := ha.isLocalHomeomorph.isOpenMap.isOpen_range
    have : range (fun x : W.interior => φ x.1) = coreImage_S28 W φ := by
      ext y; simp [coreImage_S28]
    rwa [this] at h
  obtain ⟨j, hkey, hsurj, hdisj⟩ := blockCore_sets_S28 F W φ hφ hopen hc hd Dc
  have hc' : ∀ x : W.interior, φ x.1 ∈ interiorImage_S12 F := fun x => hc x.1 x.2
  let a : W.interior → interiorImage_S12 F := fun x => ⟨φ x.1, hc' x⟩
  have ha' : IsLocalDiffeomorph W.model (𝓡 3) ∞ a := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hc' (ha x)
  let b := (interiorDiffeomorph_S12 F).symm
  have hb' : IsLocalDiffeomorph (𝓡 3) (cutCarrier_C2a F).model ∞
      (fun z : interiorImage_S12 F => ((b z) : (cutCarrier_C2a F).interior).1) := fun z =>
    IsLocalDiffeomorphAt.comp (hf := b.isLocalDiffeomorph z)
      (hg := isLocalDiffeomorph_subtype_val (I := (cutCarrier_C2a F).model)
        (cutCarrier_C2a F).interior (b z))
  have hcomp : IsLocalDiffeomorph W.model (cutCarrier_C2a F).model ∞
      (fun x : W.interior => ((b (a x)) : (cutCarrier_C2a F).interior).1) := fun x =>
    IsLocalDiffeomorphAt.comp (hf := ha' x) (hg := hb' (a x))
  have hmemP : ∀ x : W.interior, ((b (a x)) : (cutCarrier_C2a F).interior).1 ∈
      (cutCarrier_C2a F).pieceInterior (Dc.piece j) := by
    intro x
    refine (hkey _).mpr ⟨(b (a x)).2, ⟨x.1, x.2, ?_⟩⟩
    exact (congrArg Subtype.val ((interiorEquiv_S12 F).apply_symm_apply (a x))).symm
  let f : W.interior → (cutCarrier_C2a F).pieceInterior (Dc.piece j) :=
    fun x => ⟨((b (a x)) : (cutCarrier_C2a F).interior).1, hmemP x⟩
  have hf : IsLocalDiffeomorph W.model (cutCarrier_C2a F).model ∞ f := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hmemP (hcomp x)
  have hinj : Injective f := by
    intro x y hxy
    have h0 : ((b (a x)) : (cutCarrier_C2a F).interior).1 = ((b (a y)) : (cutCarrier_C2a F).interior).1 :=
      congrArg (fun z : (cutCarrier_C2a F).pieceInterior (Dc.piece j) => z.1) hxy
    have h1 : b (a x) = b (a y) := Subtype.ext h0
    have h2 : a x = a y := b.injective h1
    exact hb (congrArg Subtype.val h2)
  have hsurj' : Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := (hkey y).mp hy |>.2
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    exact interiorEquiv_symm_val_S12 F ⟨φ x, hc' ⟨x, hx⟩⟩ y hy.2 hxy.symm
  refine ⟨j, ⟨(hf.diffeomorphOfBijective ⟨hinj, hsurj'⟩).symm⟩, ?_, ?_⟩
  · ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((hkey x).mp hx).2
    · intro he
      obtain ⟨x, hx, hxe⟩ := hsurj e he
      exact ⟨x, hx, hxe⟩
  · intro j' hj'
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩
    exact hdisj j' hj' x hx
end Diffeo

end GC.LongTime.Ch12
