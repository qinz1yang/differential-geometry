import Mathlib.Topology.UniformSpace.HeineCantor
import DifferentialGeometry.Topology.UniformConvergence
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set Filter

theorem tendstoUniformlyOn_of_chart_coordinates
    {E X ι : Type*} [UniformSpace E] [LocallyCompactSpace E] [UniformSpace X]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {l : Filter ι}
    (φ : OpenPartialHomeomorph E X) (e : ∀ i, OpenPartialHomeomorph E (Y i))
    (f : ∀ i, X → Y i) (a : ∀ i, Y i → X)
    {K : Set X} (hK : IsCompact K) (hKtarget : K ⊆ φ.target)
    (hcoord : TendstoUniformlyOn (fun i x ↦ (e i).symm (f i x)) φ.symm l K)
    (htarget : ∀ᶠ i in l, MapsTo (f i) K (e i).target)
    (hchart : ∀ L : Set E, IsCompact L → L ⊆ φ.source →
      TendstoUniformlyOn (fun i v ↦ a i (e i v)) φ l L) :
    TendstoUniformlyOn (fun i x ↦ a i (f i x)) id l K := by
  obtain ⟨L, hL, hLsource, hqL, hmaps⟩ :=
    hcoord.exists_isCompact_eventually_mapsTo_of_isCompact_image
      (hK.image_of_continuousOn (φ.symm.continuousOn.mono hKtarget))
      φ.open_source (fun x hx ↦ φ.symm.map_source (hKtarget hx))
  have hcomp := (hchart L hL hLsource).comp_of_eventually_mapsTo
    (hL.uniformContinuousOn_of_continuous (φ.continuousOn.mono hLsource))
    hcoord hmaps (fun x hx ↦ interior_subset (hqL hx))
  have hidentity : TendstoUniformlyOn
      (fun i x ↦ a i (e i ((e i).symm (f i x)))) id l K :=
    hcomp.congr_right (fun x hx ↦ φ.right_inv (hKtarget hx))
  apply hidentity.congr
  filter_upwards [htarget] with i hi x hx
  dsimp only
  rw [(e i).right_inv (hi hx)]

namespace OpenPartialHomeomorph

theorem eventually_mapsTo_inverse_coordinates_of_tendstoUniformlyOn
    {E X ι : Type*} [UniformSpace E] [TopologicalSpace X]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {l : Filter ι}
    (ψ : OpenPartialHomeomorph E X) (e : ∀ i, OpenPartialHomeomorph E (Y i))
    (f : ∀ i, X → Y i) {K : Set X} (hK : IsCompact K) (hKψ : K ⊆ ψ.target)
    {D : Set E} (hD : IsOpen D) (hKD : ψ.symm '' K ⊆ D)
    (hconv : TendstoUniformlyOn (fun i v => (e i).symm (f i (ψ v))) id l (ψ.symm '' K))
    (hmem : ∀ᶠ i in l, MapsTo (f i ∘ ψ) (ψ.symm '' K) (e i).target) :
    ∀ᶠ i in l, ∀ x ∈ K, f i x ∈ (e i).target ∧ (e i).symm (f i x) ∈ D := by
  have hcompact : IsCompact (ψ.symm '' K) :=
    hK.image_of_continuousOn (ψ.symm.continuousOn.mono hKψ)
  have hinside := hconv.eventually_mapsTo_of_isCompact hcompact continuousOn_id hD hKD
  filter_upwards [hmem, hinside] with i hi hDinside x hx
  have hxcoord : ψ.symm x ∈ ψ.symm '' K := mem_image_of_mem _ hx
  have htarget := hi hxcoord
  have hcoord := hDinside hxcoord
  simpa only [Function.comp_apply, ψ.right_inv (hKψ hx)] using And.intro htarget hcoord

end OpenPartialHomeomorph

open Topology in
theorem eventually_mapsTo_and_tendstoUniformlyOn_of_chart_cover
    {E X α ι : Type*} [UniformSpace E] [LocallyCompactSpace E] [UniformSpace X]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {l : Filter ι}
    {W K : Set X} (hK : IsCompact K) (hKW : K ⊆ W)
    (φ : α → OpenPartialHomeomorph E X)
    (e : α → ∀ i, OpenPartialHomeomorph E (Y i))
    (f : ∀ i, X → Y i) (q : ∀ i, Y i → X) (Ω : ∀ i, Set (Y i))
    (hcover : W ⊆ ⋃ a, (φ a).target)
    (hcoord : ∀ a (L : Set E), IsCompact L → L ⊆ (φ a).source ∩ φ a ⁻¹' W →
      (∀ᶠ i in l, MapsTo (f i ∘ φ a) L (e a i).target) ∧
        TendstoUniformlyOn (fun i x => (e a i).symm (f i (φ a x))) id l L)
    (hchart : ∀ a (L : Set E), IsCompact L → L ⊆ (φ a).source →
      TendstoUniformlyOn (fun i x => q i (e a i x)) (φ a) l L)
    (hvalid : ∀ a (L : Set E), IsCompact L → L ⊆ (φ a).source →
      ∀ᶠ i in l, MapsTo (e a i) L (Ω i)) :
    (∀ᶠ i in l, MapsTo (f i) K (Ω i)) ∧
      TendstoUniformlyOn (fun i x => q i (f i x)) id l K := by
  have hlocal (a : α) (C : Set X) (hC : IsCompact C) (hCW : C ⊆ W)
      (hCt : C ⊆ (φ a).target) :
      (∀ᶠ i in l, MapsTo (f i) C (Ω i)) ∧
        TendstoUniformlyOn (fun i x => q i (f i x)) id l C := by
    let L : Set E := (φ a).symm '' C
    have hL : IsCompact L :=
      hC.image_of_continuousOn ((φ a).symm.continuousOn.mono hCt)
    have hLD : L ⊆ (φ a).source ∩ φ a ⁻¹' W := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨(φ a).map_target (hCt hx), ?_⟩
      change φ a ((φ a).symm x) ∈ W
      rw [(φ a).right_inv (hCt hx)]
      exact hCW hx
    obtain ⟨hcapture, hcoordinates⟩ := hcoord a L hL hLD
    have hcaptureC : ∀ᶠ i in l, MapsTo (f i) C (e a i).target := by
      filter_upwards [hcapture] with i hi x hx
      have hm := hi (mem_image_of_mem (φ a).symm hx)
      change f i (φ a ((φ a).symm x)) ∈ (e a i).target at hm
      rwa [(φ a).right_inv (hCt hx)] at hm
    have hcoordinatesC :
        TendstoUniformlyOn (fun i x => (e a i).symm (f i x)) (φ a).symm l C := by
      have hpull := (hcoordinates.comp (φ a).symm).mono
        (fun x hx => mem_image_of_mem (φ a).symm hx)
      apply hpull.congr
      apply Eventually.of_forall
      intro i x hx
      dsimp only [Function.comp_def]
      rw [(φ a).right_inv (hCt hx)]
    obtain ⟨S, hS, hSs, _, hintoS⟩ :=
      hcoordinatesC.exists_isCompact_eventually_mapsTo_of_isCompact_image hL
        (φ a).open_source (fun _ hx => (φ a).map_target (hCt hx))
    constructor
    · filter_upwards [hcaptureC, hintoS, hvalid a S hS hSs] with i hi hSi hVi x hx
      have hm := hVi (hSi hx)
      rwa [(e a i).right_inv (hi hx)] at hm
    · exact tendstoUniformlyOn_of_chart_coordinates (φ a) (e a) f q
        hC hCt hcoordinatesC hcaptureC (hchart a)
  apply hK.induction_on
    (p := fun C => (∀ᶠ i in l, MapsTo (f i) C (Ω i)) ∧
      TendstoUniformlyOn (fun i x => q i (f i x)) id l C)
  · constructor
    · exact Eventually.of_forall fun _ _ hx => hx.elim
    · intro u _
      exact Eventually.of_forall fun _ _ hx => hx.elim
  · intro s t hst ht
    exact ⟨ht.1.mono (fun _ hi _ hx => hi (hst hx)), ht.2.mono hst⟩
  · intro s t hs ht
    constructor
    · filter_upwards [hs.1, ht.1] with i hsi hti x hx
      exact hx.elim (fun hx => hsi hx) (fun hx => hti hx)
    · intro u hu
      filter_upwards [hs.2 u hu, ht.2 u hu] with i hsi hti x hx
      exact hx.elim (fun hx => hsi x hx) (fun hx => hti x hx)
  · intro x hx
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (hcover (hKW hx))
    obtain ⟨C, hCn, hCc, hCt⟩ :=
      exists_mem_nhds_isClosed_subset ((φ a).open_target.mem_nhds hxa)
    refine ⟨K ∩ C, inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hCn), ?_⟩
    exact hlocal a (K ∩ C) (hK.inter_right hCc)
      (fun _ hy => hKW hy.1) (fun _ hy => hCt hy.2)
