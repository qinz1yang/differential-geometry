/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartSlideLong
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology
open scoped Manifold

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem injective_conjugateMap (e : _root_.OpenPartialHomeomorph X Y) {k : Y → Y}
    (hk : Function.Injective k) (hmap : MapsTo k e.target e.target) :
    Function.Injective (e.conjugateMap k) := by
  intro x y hxy
  by_cases hx : x ∈ e.source
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      have h1 : k (e x) ∈ e.target := hmap (e.map_source hx)
      have h2 : k (e y) ∈ e.target := hmap (e.map_source hy)
      have hkey : k (e x) = k (e y) := by
        have := congrArg e hxy
        rwa [e.right_inv h1, e.right_inv h2] at this
      have hex : e x = e y := hk hkey
      have := congrArg e.symm hex
      rwa [e.left_inv hx, e.left_inv hy] at this
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_notMem _ hy] at hxy
      exact absurd (hxy ▸ e.map_target (hmap (e.map_source hx))) hy
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      exact absurd (hxy.symm ▸ e.map_target (hmap (e.map_source hy))) hx
    · rwa [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_notMem _ hy] at hxy

theorem disjoint_conjugateMap_image (e : _root_.OpenPartialHomeomorph X Y) {k : Y → Y}
    (hmap : MapsTo k e.target e.target) {A B : Set Y} (hA : A ⊆ e.target) (hB : B ⊆ e.target)
    (hdisj : Disjoint (k '' A) B) :
    Disjoint (e.conjugateMap k '' (e.symm '' A)) (e.symm '' B) := by
  rw [Set.disjoint_left]
  rintro w ⟨u, ⟨p, hp, rfl⟩, rfl⟩ ⟨q, hq, hqe⟩
  have hps : e.symm p ∈ e.source := e.map_target (hA hp)
  have hval : e.conjugateMap k (e.symm p) = e.symm (k p) := by
    rw [e.conjugateMap_of_mem _ hps, e.right_inv (hA hp)]
  rw [hval] at hqe
  have h1 : k p ∈ e.target := hmap (hA hp)
  have hpq : k p = q := by
    have hcong := congrArg e hqe
    rw [e.right_inv h1, e.right_inv (hB hq)] at hcong
    exact hcong.symm
  exact Set.disjoint_left.mp hdisj ⟨p, hp, rfl⟩ (hpq ▸ hq)

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isPL_conjugateMap {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ (plGroupoid n).maximalAtlas X)
    {k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hk : IsPiecewiseAffineOn k univ) (hmap : MapsTo k e.target e.target)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsCompact C) (hCt : C ⊆ e.target)
    (hfix : EqOn k id Cᶜ) :
    IsPL n n (e.conjugateMap k) := by
  have hcont : Continuous (e.conjugateMap k) :=
    e.continuous_conjugateMap (hk.continuousOn.mono (subset_univ _)) hmap hC hCt hfix
  have hgsource : MapsTo (e.conjugateMap k) e.source e.source := by
    intro x hx
    rw [e.conjugateMap_of_mem k hx]
    exact e.map_target (hmap (e.map_source hx))
  have hcoord : EqOn (e ∘ e.conjugateMap k ∘ e.symm) k e.target := by
    intro z hz
    change e (e.conjugateMap k (e.symm z)) = k z
    rw [e.conjugateMap_of_mem k (e.map_target hz), e.right_inv hz, e.right_inv (hmap hz)]
  have hclosed : IsClosed (e.symm '' C) :=
    (hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)).isClosed
  intro x
  by_cases hx : x ∈ e.source
  · apply (isPLAt_iff_of_mem_maximalAtlas he hx he (hgsource hx)).mpr
    refine ⟨hcont.continuousAt, ?_⟩
    have hneigh : e.target ∈ 𝓝 (e x) := e.open_target.mem_nhds (e.map_source hx)
    have hlocal := (hk (e x) (mem_univ _)).inter_of_mem_nhds hneigh
    exact (hlocal.congr (fun z hz => hcoord hz.2)).of_inter_of_mem_nhds hneigh
  · have hxC : x ∉ e.symm '' C := by
      rintro ⟨y, hy, rfl⟩
      exact hx (e.map_target (hCt hy))
    apply piecewiseAffineProperty_localInvariantProp.liftPropAt_congr_of_eventuallyEq
      (isPL_id (M := X) x)
    filter_upwards [hclosed.isOpen_compl.mem_nhds hxC] with z hz
    exact e.conjugateMap_eqOn_compl hfix hz

theorem exists_separated_slide {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {BdM S W A B : Set M} {d R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target)
    (hd : 0 ≤ d) (hcR : c + 2 * d ≤ R) (hca : c - d < a)
    (hsupp : slideSupportLong R ⊆ e.target)
    (hAt : slideBandA c ⊆ e.target) (hBt : slideBandQ a b ⊆ e.target)
    (hSK : S ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hW : W ∈ 𝓝ˢ (E.symm '' (e.symm '' slideSupportLong R)))
    (hA : A ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆ E.symm '' (e.symm '' slideBandA c))
    (hB : B ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆ E.symm '' (e.symm '' slideBandQ a b))
    (hAB : A ∩ B ⊆ E.symm '' (e.symm '' slideSupportLong R)) :
    ∃ (U : Set M) (h : M → M), IsOpen U ∧ S ⊆ U ∧ closure U ⊆ W ∧
      IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧ MapsTo h U U ∧
      (∀ (Bd₁ : Set (EuclideanSpace ℝ (Fin 3))) (T : Set (ℝ × ℝ)),
        (∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁) →
        (∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).2 ∈ T) → ∀ x, h x ∈ BdM ↔ x ∈ BdM) ∧
      Disjoint (h '' A) B := by
  have hslidemap : MapsTo (slideMapLong d R) e.target e.target :=
    mapsTo_slideMapLong_of_subset hd hsupp
  have hCsub : e.symm '' slideSupportLong R ⊆ e.source := by
    rintro _ ⟨p, hp, rfl⟩
    exact e.map_target (hsupp hp)
  have hCcompact : IsCompact (e.symm '' slideSupportLong R) :=
    (isCompact_slideSupportLong R).image_of_continuousOn (e.continuousOn_symm.mono hsupp)
  have hCE : e.symm '' slideSupportLong R ⊆ E.target := hCsub.trans hesrc
  have hkfix : EqOn (e.conjugateMap (slideMapLong d R)) id (e.symm '' slideSupportLong R)ᶜ :=
    e.conjugateMap_eqOn_compl (eqOn_slideMapLong_id_compl hd)
  have hkmap : MapsTo (e.conjugateMap (slideMapLong d R)) E.target E.target := by
    intro y hy
    by_cases hys : y ∈ e.source
    · rw [e.conjugateMap_of_mem _ hys]
      exact hesrc (e.map_target (hslidemap (e.map_source hys)))
    · rw [e.conjugateMap_of_notMem _ hys]
      exact hy
  have hkpl : IsPiecewiseAffineOn (e.conjugateMap (slideMapLong d R)) univ :=
    isPiecewiseAffineOn_chartSlideLong hd e he hei hsupp
  have hkinj : Function.Injective (e.conjugateMap (slideMapLong d R)) :=
    injective_chartSlideLong hd e hsupp
  have hKcompact : IsCompact (E.symm '' (e.symm '' slideSupportLong R)) :=
    hCcompact.image_of_continuousOn (E.continuousOn_symm.mono hCE)
  have hkC : MapsTo (e.conjugateMap (slideMapLong d R)) (e.symm '' slideSupportLong R)
      (e.symm '' slideSupportLong R) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [e.conjugateMap_of_mem _ (e.map_target (hsupp hp)), e.right_inv (hsupp hp)]
    exact ⟨slideMapLong d R p, mapsTo_slideMapLong_slideSupportLong hp, rfl⟩
  have hhK : MapsTo (E.conjugateMap (e.conjugateMap (slideMapLong d R)))
      (E.symm '' (e.symm '' slideSupportLong R))
      (E.symm '' (e.symm '' slideSupportLong R)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [E.conjugateMap_of_mem _ (E.map_target (hCE hy)), E.right_inv (hCE hy)]
    exact ⟨_, hkC hy, rfl⟩
  have : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨U, hUopen, hKU, hUW⟩ := hKcompact.exists_isOpen_closure_subset hW
  refine ⟨U, E.conjugateMap (e.conjugateMap (slideMapLong d R)), hUopen, hSK.trans hKU, hUW,
    isPL_conjugateMap E hE hkpl hkmap hCcompact hCE hkfix,
    E.injective_conjugateMap hkinj hkmap, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact E.conjugateMap_eqOn_compl hkfix fun hxK => hx (hKU hxK)
  · intro x hx
    by_cases hxK : x ∈ E.symm '' (e.symm '' slideSupportLong R)
    · exact hKU (hhK hxK)
    · rw [E.conjugateMap_eqOn_compl hkfix hxK]
      exact hx
  · intro Bd₁ T hbdE hbde x
    refine E.conjugateMap_mem_iff hkmap hbdE ?_ x
    intro y _
    refine e.conjugateMap_mem_iff (B := {p : ℝ × ℝ × ℝ | p.2 ∈ T}) hslidemap hbde ?_ y
    intro p _
    simp only [mem_ofPred_eq, slideMapLong_snd]
  · have hAE : e.symm '' slideBandA c ⊆ E.target := by
      rintro _ ⟨p, hp, rfl⟩
      exact hesrc (e.map_target (hAt hp))
    have hBE : e.symm '' slideBandQ a b ⊆ E.target := by
      rintro _ ⟨p, hp, rfl⟩
      exact hesrc (e.map_target (hBt hp))
    have hdisj₀ := E.disjoint_conjugateMap_image hkmap hAE hBE
      (disjoint_chartSlideLong_image hd hcR hca e hsupp hAt hBt)
    rw [Set.disjoint_left]
    rintro y ⟨p, hpA, rfl⟩ hyB
    by_cases hpK : p ∈ E.symm '' (e.symm '' slideSupportLong R)
    · exact Set.disjoint_left.mp hdisj₀ ⟨p, hA ⟨hpA, hpK⟩, rfl⟩ (hB ⟨hyB, hhK hpK⟩)
    · have hp : E.conjugateMap (e.conjugateMap (slideMapLong d R)) p = p :=
        E.conjugateMap_eqOn_compl hkfix hpK
      exact hpK (hAB ⟨hpA, hp ▸ hyB⟩)

open Classical in
theorem isPLOn_piecewise_postcomp_of_separated {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {F : EuclideanSpace ℝ (Fin 2) → M} {P Q : Set (EuclideanSpace ℝ (Fin 2))}
    {h : M → M} {U : Set M}
    (hF : IsPLOn 2 3 F (P ∪ Q)) (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hloc : IsLocallyInjective ((P ∪ Q).domRestrict F))
    (hcard : ∀ y, ((P ∪ Q) ∩ F ⁻¹' {y}).encard ≤ 2) (hinjP : InjOn F P)
    (hh : IsPL 3 3 h) (hhinj : Function.Injective h) (hfix : EqOn h id Uᶜ)
    (hseam : ∀ x ∈ P ∩ Q, F x ∉ closure U) (hinjQ : InjOn F (Q ∩ F ⁻¹' U)) :
    IsPLOn 2 3 (P.piecewise (h ∘ F) F) (P ∪ Q) ∧
      IsLocallyInjective ((P ∪ Q).domRestrict (P.piecewise (h ∘ F) F)) ∧
      (∀ y, ((P ∪ Q) ∩ P.piecewise (h ∘ F) F ⁻¹' {y}).encard ≤ 2) ∧
      ∀ y ∉ U, P.piecewise (h ∘ F) F ⁻¹' {y} = F ⁻¹' {y} := by
  obtain ⟨g, hg, hgloc, hgcard, hgP, -, hgPc, hgfib⟩ :=
    exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective hF hP hQ hloc hcard hinjP hh
      hhinj hfix hseam hinjQ
  have hgeq : g = P.piecewise (h ∘ F) F := by
    funext x
    by_cases hx : x ∈ P
    · rw [piecewise_eq_of_mem P (h ∘ F) F hx]
      exact hgP hx
    · rw [piecewise_eq_of_notMem P (h ∘ F) F hx]
      exact hgPc hx
  rw [hgeq] at hg hgloc hgcard hgfib
  exact ⟨hg, hgloc, hgcard, hgfib⟩

open Classical in
theorem doublePointSet_piecewise_postcomp {M : Type u}
    {F : EuclideanSpace ℝ (Fin 2) → M} {P Pc Q dom : Set (EuclideanSpace ℝ (Fin 2))}
    {h : M → M} {U S : Set M} (hdom : P ∪ Pc = dom)
    (hhinj : Function.Injective h) (hfix : EqOn h id Uᶜ) (hmapU : MapsTo h U U)
    (hinjP : InjOn F P) (hinjQ : InjOn F (Q ∩ F ⁻¹' U)) (hPcQ : Pc ∩ F ⁻¹' U ⊆ Q)
    (hdisj : Disjoint (h '' (F '' P)) (F '' Q))
    (hSU : S ⊆ U) (hclean : doublePointSet F dom ∩ U ⊆ S) :
    doublePointSet (P.piecewise (h ∘ F) F) dom = doublePointSet F dom \ S := by
  have hunion : ∀ x ∈ dom, x ∉ P → x ∈ Pc := by
    intro x hx hxP
    have hxPQ : x ∈ P ∪ Pc := by rw [hdom]; exact hx
    exact hxPQ.resolve_left hxP
  have hmem : ∀ x ∈ P, P.piecewise (h ∘ F) F x = h (F x) := fun x hx =>
    piecewise_eq_of_mem P (h ∘ F) F hx
  have hnotmem : ∀ x, x ∉ P → P.piecewise (h ∘ F) F x = F x := fun x hx =>
    piecewise_eq_of_notMem P (h ∘ F) F hx
  ext y
  constructor
  · rintro ⟨x, hx, z, hz, hxz, hxy, hzy⟩
    have hmixed : ∀ u v, v ∈ dom → u ∈ P → v ∉ P → P.piecewise (h ∘ F) F u = y →
        P.piecewise (h ∘ F) F v = y → F u = y ∧ y ∉ U := by
      intro u v hv huP hvP hgu hgv
      rw [hmem u huP] at hgu
      rw [hnotmem v hvP] at hgv
      by_cases hFu : F u ∈ U
      · exfalso
        have hyU : y ∈ U := by rw [← hgu]; exact hmapU hFu
        have hvU : F v ∈ U := by rw [hgv]; exact hyU
        exact Set.disjoint_left.mp hdisj ⟨F u, ⟨u, huP, rfl⟩, hgu⟩
          ⟨v, hPcQ ⟨hunion v hv hvP, hvU⟩, hgv⟩
      · have heq : h (F u) = F u := hfix hFu
        have hFuy : F u = y := by rw [← heq]; exact hgu
        exact ⟨hFuy, fun hyU => hFu (by rw [hFuy]; exact hyU)⟩
    by_cases hxP : x ∈ P
    · by_cases hzP : z ∈ P
      · rw [hmem x hxP] at hxy
        rw [hmem z hzP] at hzy
        exact absurd (hinjP hxP hzP (hhinj (hxy.trans hzy.symm))) hxz
      · obtain ⟨hFx, hyU⟩ := hmixed x z hz hxP hzP hxy hzy
        rw [hnotmem z hzP] at hzy
        exact ⟨⟨x, hx, z, hz, hxz, hFx, hzy⟩, fun hyS => hyU (hSU hyS)⟩
    · by_cases hzP : z ∈ P
      · obtain ⟨hFz, hyU⟩ := hmixed z x hx hzP hxP hzy hxy
        rw [hnotmem x hxP] at hxy
        exact ⟨⟨x, hx, z, hz, hxz, hxy, hFz⟩, fun hyS => hyU (hSU hyS)⟩
      · rw [hnotmem x hxP] at hxy
        rw [hnotmem z hzP] at hzy
        refine ⟨⟨x, hx, z, hz, hxz, hxy, hzy⟩, ?_⟩
        intro hyS
        have hxU : F x ∈ U := by rw [hxy]; exact hSU hyS
        have hzU : F z ∈ U := by rw [hzy]; exact hSU hyS
        exact hxz (hinjQ ⟨hPcQ ⟨hunion x hx hxP, hxU⟩, hxU⟩
          ⟨hPcQ ⟨hunion z hz hzP, hzU⟩, hzU⟩ (hxy.trans hzy.symm))
  · rintro ⟨⟨x, hx, z, hz, hxz, hxy, hzy⟩, hyS⟩
    have hyU : y ∉ U := fun hyU => hyS (hclean ⟨⟨x, hx, z, hz, hxz, hxy, hzy⟩, hyU⟩)
    have hhy : h y = y := hfix hyU
    have hval : ∀ u, F u = y → P.piecewise (h ∘ F) F u = y := by
      intro u hFu
      by_cases huP : u ∈ P
      · rw [hmem u huP, hFu, hhy]
      · rw [hnotmem u huP, hFu]
    exact ⟨x, hx, z, hz, hxz, hval x hxy, hval z hzy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
