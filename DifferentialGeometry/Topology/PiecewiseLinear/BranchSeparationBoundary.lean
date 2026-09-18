import DifferentialGeometry.Topology.PiecewiseLinear.BranchSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.BranchSlideEndpoint

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_separated_slide_fwd {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {S W A B : Set M} {d R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target)
    (hd : 0 ≤ d) (hcR : c + 2 * d ≤ R) (hbd : b < d)
    (hsupp : slideSupportLong R ⊆ e.target)
    (hAt : slideBandA c ⊆ e.target) (hBt : slideBandQ a b ⊆ e.target)
    (hSK : S ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hW : W ∈ 𝓝ˢ (E.symm '' (e.symm '' slideSupportLong R)))
    (hA : A ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆ E.symm '' (e.symm '' slideBandA c))
    (hB : B ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆ E.symm '' (e.symm '' slideBandQ a b))
    (hAB : A ∩ B ⊆ E.symm '' (e.symm '' slideSupportLong R)) :
    ∃ (U : Set M) (h : M → M), IsOpen U ∧ S ⊆ U ∧ closure U ⊆ W ∧
      IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧ MapsTo h U U ∧
      (∀ (N : Set M) (N₁ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) →
        (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) → MapsTo h N N) ∧
      Disjoint (h '' A) B := by
  have hslidemap : MapsTo (slideMapFwd d R) e.target e.target :=
    mapsTo_slideMapFwd_of_subset hd hsupp
  have hCsub : e.symm '' slideSupportLong R ⊆ e.source := by
    rintro _ ⟨p, hp, rfl⟩
    exact e.map_target (hsupp hp)
  have hCcompact : IsCompact (e.symm '' slideSupportLong R) :=
    (isCompact_slideSupportLong R).image_of_continuousOn (e.continuousOn_symm.mono hsupp)
  have hCE : e.symm '' slideSupportLong R ⊆ E.target := hCsub.trans hesrc
  have hkfix : EqOn (e.conjugateMap (slideMapFwd d R)) id (e.symm '' slideSupportLong R)ᶜ :=
    eqOn_chartSlideFwd_id_compl hd e
  have hkmap : MapsTo (e.conjugateMap (slideMapFwd d R)) E.target E.target := by
    intro y hy
    by_cases hys : y ∈ e.source
    · rw [e.conjugateMap_of_mem _ hys]
      exact hesrc (e.map_target (hslidemap (e.map_source hys)))
    · rw [e.conjugateMap_of_notMem _ hys]
      exact hy
  have hkpl : IsPiecewiseAffineOn (e.conjugateMap (slideMapFwd d R)) univ :=
    isPiecewiseAffineOn_chartSlideFwd hd e he hei hsupp
  have hkinj : Function.Injective (e.conjugateMap (slideMapFwd d R)) :=
    injective_chartSlideFwd hd e hsupp
  have hKcompact : IsCompact (E.symm '' (e.symm '' slideSupportLong R)) :=
    hCcompact.image_of_continuousOn (E.continuousOn_symm.mono hCE)
  have hkC : MapsTo (e.conjugateMap (slideMapFwd d R)) (e.symm '' slideSupportLong R)
      (e.symm '' slideSupportLong R) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [e.conjugateMap_of_mem _ (e.map_target (hsupp hp)), e.right_inv (hsupp hp)]
    exact ⟨slideMapFwd d R p, mapsTo_slideMapFwd_slideSupportLong hp, rfl⟩
  have hhK : MapsTo (E.conjugateMap (e.conjugateMap (slideMapFwd d R)))
      (E.symm '' (e.symm '' slideSupportLong R))
      (E.symm '' (e.symm '' slideSupportLong R)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [E.conjugateMap_of_mem _ (E.map_target (hCE hy)), E.right_inv (hCE hy)]
    exact ⟨_, hkC hy, rfl⟩
  have : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨U, hUopen, hKU, hUW⟩ := hKcompact.exists_isOpen_closure_subset hW
  refine ⟨U, E.conjugateMap (e.conjugateMap (slideMapFwd d R)), hUopen, hSK.trans hKU, hUW,
    isPL_conjugateMap E hE hkpl hkmap hCcompact hCE hkfix,
    E.injective_conjugateMap hkinj hkmap, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact E.conjugateMap_eqOn_compl hkfix fun hxK => hx (hKU hxK)
  · intro x hx
    by_cases hxK : x ∈ E.symm '' (e.symm '' slideSupportLong R)
    · exact hKU (hhK hxK)
    · rw [E.conjugateMap_eqOn_compl hkfix hxK]
      exact hx
  · intro N N₁ hNE hN₁
    refine E.mapsTo_conjugateMap hkmap hNE ?_
    have hinner : MapsTo (e.conjugateMap (slideMapFwd d R)) N₁ N₁ :=
      mapsTo_chartSlideFwd_halfSpace hd e hsupp hN₁
    exact fun y hy => hinner hy.2
  · have hAE : e.symm '' slideBandA c ⊆ E.target := by
      rintro _ ⟨p, hp, rfl⟩
      exact hesrc (e.map_target (hAt hp))
    have hBE : e.symm '' slideBandQ a b ⊆ E.target := by
      rintro _ ⟨p, hp, rfl⟩
      exact hesrc (e.map_target (hBt hp))
    have hdisj₀ := E.disjoint_conjugateMap_image hkmap hAE hBE
      (disjoint_chartSlideFwd_image hd hcR hbd e hsupp hAt hBt)
    rw [Set.disjoint_left]
    rintro y ⟨p, hpA, rfl⟩ hyB
    by_cases hpK : p ∈ E.symm '' (e.symm '' slideSupportLong R)
    · exact Set.disjoint_left.mp hdisj₀ ⟨p, hA ⟨hpA, hpK⟩, rfl⟩ (hB ⟨hyB, hhK hpK⟩)
    · have hp : E.conjugateMap (e.conjugateMap (slideMapFwd d R)) p = p :=
        E.conjugateMap_eqOn_compl hkfix hpK
      exact hpK (hAB ⟨hpA, hp ▸ hyB⟩)

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_separated_along_boundary_branch (hD : NormalSingularCellData D BdM B)
    (cb : hD.singularSet.Branch) {W : Set M} {P Q : Set (EuclideanSpace ℝ (Fin 2))}
    {d R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target)
    (hd : 0 ≤ d) (hcR : c + 2 * d ≤ R) (hbd : b < d)
    (hsupp : slideSupportLong R ⊆ e.target)
    (hAt : slideBandA c ⊆ e.target) (hBt : slideBandQ a b ⊆ e.target)
    (hSK : hD.singularSet.branchCarrier cb ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hW : W ∈ 𝓝ˢ (E.symm '' (e.symm '' slideSupportLong R)))
    (hA : D '' P ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandA c))
    (hB : D '' Q ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandQ a b))
    (hAB : D '' P ∩ D '' Q ⊆ E.symm '' (e.symm '' slideSupportLong R)) :
    ∃ (U : Set M) (h : M → M), IsOpen U ∧ hD.singularSet.branchCarrier cb ⊆ U ∧
      closure U ⊆ W ∧ IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧ MapsTo h U U ∧
      (∀ (N : Set M) (N₁ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) →
        (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) → MapsTo h N N) ∧
      Disjoint (h '' (D '' P)) (D '' Q) :=
  exists_separated_slide_fwd E hE e he hei hesrc hd hcR hbd hsupp hAt hBt hSK hW hA hB hAB

open Classical in
theorem exists_separated_cell_along_boundary_branch (hD : NormalSingularCellData D BdM B)
    (cb : hD.singularSet.Branch) {W : Set M} {P Pc Q : Set (EuclideanSpace ℝ (Fin 2))}
    {d R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target)
    (hd : 0 ≤ d) (hcR : c + 2 * d ≤ R) (hbd : b < d)
    (hsupp : slideSupportLong R ⊆ e.target)
    (hAt : slideBandA c ⊆ e.target) (hBt : slideBandQ a b ⊆ e.target)
    (hSK : hD.singularSet.branchCarrier cb ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hW : W ∈ 𝓝ˢ (E.symm '' (e.symm '' slideSupportLong R)))
    (hA : D '' P ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandA c))
    (hB : D '' Q ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandQ a b))
    (hAB : D '' P ∩ D '' Q ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hdom : P ∪ Pc = D.domain) (hPpoly : IsPolyhedron P) (hPcpoly : IsPolyhedron Pc)
    (hinjP : InjOn D P) (hinjQ : InjOn D (Q ∩ D ⁻¹' W)) (hPcQ : Pc ∩ D ⁻¹' W ⊆ Q)
    (hseam : ∀ x ∈ P ∩ Pc, D x ∉ W)
    (hclean : doublePointSet D D.domain ∩ W ⊆ hD.singularSet.branchCarrier cb) :
    ∃ (U : Set M) (h : M → M), IsOpen U ∧ hD.singularSet.branchCarrier cb ⊆ U ∧
      closure U ⊆ W ∧ IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧ MapsTo h U U ∧
      (∀ (N : Set M) (N₁ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) →
        (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) → MapsTo h N N) ∧
      Disjoint (h '' (D '' P)) (D '' Q) ∧
      IsPLOn 2 3 (P.piecewise (h ∘ D) D) D.domain ∧
      IsLocallyInjective (D.domain.domRestrict (P.piecewise (h ∘ D) D)) ∧
      (∀ y, (D.domain ∩ P.piecewise (h ∘ D) D ⁻¹' {y}).encard ≤ 2) ∧
      (∀ y ∉ U, P.piecewise (h ∘ D) D ⁻¹' {y} = D ⁻¹' {y}) ∧
      doublePointSet (P.piecewise (h ∘ D) D) D.domain =
        doublePointSet D D.domain \ hD.singularSet.branchCarrier cb := by
  obtain ⟨U, h, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhN, hdisj⟩ :=
    hD.exists_separated_along_boundary_branch cb E hE e he hei hesrc hd hcR hbd hsupp hAt hBt
      hSK hW hA hB hAB
  have hUsub : U ⊆ W := subset_closure.trans hUW
  have hinjQU : InjOn D (Q ∩ D ⁻¹' U) :=
    hinjQ.mono (inter_subset_inter_right _ (preimage_mono hUsub))
  have hPcQU : Pc ∩ D ⁻¹' U ⊆ Q := fun x hx => hPcQ ⟨hx.1, hUsub hx.2⟩
  have hinjPcU : InjOn D (Pc ∩ D ⁻¹' U) := fun x hx z hz hxz =>
    hinjQU ⟨hPcQU hx, hx.2⟩ ⟨hPcQU hz, hz.2⟩ hxz
  have hseamU : ∀ x ∈ P ∩ Pc, D x ∉ closure U := fun x hx hmem => hseam x hx (hUW hmem)
  have hF : IsPLOn 2 3 D (P ∪ Pc) := by rw [hdom]; exact D.isPLOn
  have hloc : IsLocallyInjective ((P ∪ Pc).domRestrict D) := by
    rw [hdom]; exact hD.isLocallyInjective_domRestrict
  have hcard : ∀ y, ((P ∪ Pc) ∩ D ⁻¹' {y}).encard ≤ 2 := by
    rw [hdom]; exact hD.fiber_le_two
  obtain ⟨hgpl, hgloc, hgcard, hgfib⟩ :=
    isPLOn_piecewise_postcomp_of_separated hF hPpoly hPcpoly hloc hcard hinjP hhpl hhinj
      hhfix hseamU hinjPcU
  rw [hdom] at hgpl hgloc hgcard
  refine ⟨U, h, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhN, hdisj, hgpl, hgloc, hgcard,
    hgfib, ?_⟩
  refine doublePointSet_piecewise_postcomp hdom hhinj hhfix hhmap hinjP hinjQU hPcQU hdisj
    hSU ?_
  intro y hy
  exact hclean ⟨hy.1, hUsub hy.2⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
