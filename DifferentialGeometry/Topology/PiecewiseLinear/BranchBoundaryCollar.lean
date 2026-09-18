import DifferentialGeometry.Topology.PiecewiseLinear.BranchSeparationBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

open Classical in
theorem preimage_boundary_subset_frontier_piecewise_postcomp
    {D : SingularTwoCell M} {BdM N : Set M} {h : M → M}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, h x ∈ BdM → x ∈ BdM) :
    D.domain ∩ P.piecewise (h ∘ D) D ⁻¹' BdM ⊆ frontier D.domain := by
  rintro x ⟨hx, hmem⟩
  by_cases hxP : x ∈ P
  · rw [Set.mem_preimage, Set.piecewise_eq_of_mem _ _ _ hxP] at hmem
    exact hbdpre ⟨hx, hrefl (D x) (hDN hx) hmem⟩
  · rw [Set.mem_preimage, Set.piecewise_eq_of_notMem _ _ _ hxP] at hmem
    exact hbdpre ⟨hx, hmem⟩

open Classical in
theorem image_inter_boundary_subset_image_frontier_piecewise_postcomp
    {D : SingularTwoCell M} {BdM N : Set M} {h : M → M}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, h x ∈ BdM → x ∈ BdM) :
    P.piecewise (h ∘ D) D '' D.domain ∩ BdM ⊆
      P.piecewise (h ∘ D) D '' frontier D.domain := by
  rintro _ ⟨⟨x, hx, rfl⟩, hmem⟩
  exact ⟨x, preimage_boundary_subset_frontier_piecewise_postcomp hbdpre hDN hrefl ⟨hx, hmem⟩,
    rfl⟩

open Classical in
theorem image_inter_boundary_of_collarExtension
    {D G : SingularTwoCell M} {BdM N : Set M} {h : M → M}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, h x ∈ BdM → x ∈ BdM)
    (hext : EqOn G (P.piecewise (h ∘ D) D) D.domain)
    (houter : Set.range G.boundary ⊆ BdM)
    (hannulus : G '' (G.domain \ D.domain) ∩ BdM ⊆ Set.range G.boundary)
    (hseam : P.piecewise (h ∘ D) D '' frontier D.domain ∩ BdM ⊆ Set.range G.boundary) :
    G '' G.domain ∩ BdM = Set.range G.boundary := by
  apply Subset.antisymm
  · rintro _ ⟨⟨x, hx, rfl⟩, hmem⟩
    by_cases hxD : x ∈ D.domain
    · rw [hext hxD] at hmem ⊢
      refine hseam ⟨⟨x, ?_, rfl⟩, hmem⟩
      exact preimage_boundary_subset_frontier_piecewise_postcomp hbdpre hDN hrefl ⟨hxD, hmem⟩
    · exact hannulus ⟨⟨x, ⟨hx, hxD⟩, rfl⟩, hmem⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨⟨(z : EuclideanSpace ℝ (Fin 2)), G.frontier_subset_domain z.2, rfl⟩,
      houter ⟨z, rfl⟩⟩

theorem range_boundary_subset_of_collarExtension {G : SingularTwoCell M} {BdM B : Set M}
    (houter : Set.range G.boundary ⊆ BdM) (hBdB : BdM ⊆ B) :
    Set.range G.boundary ⊆ B :=
  houter.trans hBdB

namespace NormalSingularCellData

variable [T2Space M] [HasGroupoid M (plGroupoid 3)] {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
theorem exists_separated_cell_boundary_preimage_along_boundary_branch
    (hD : NormalSingularCellData D BdM B)
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
    (hclean : doublePointSet D D.domain ∩ W ⊆ hD.singularSet.branchCarrier cb)
    {N : Set M} {N₁ Bd₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hNE : ∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁)
    (hN₁ : ∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1)
    (hBdE : ∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁)
    (hBd₁ : ∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).1 = 0)
    (hDN : MapsTo D D.domain N)
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain) :
    ∃ (U : Set M) (h : M → M), IsOpen U ∧ hD.singularSet.branchCarrier cb ⊆ U ∧
      closure U ⊆ W ∧ IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧ MapsTo h U U ∧
      Disjoint (h '' (D '' P)) (D '' Q) ∧
      IsPLOn 2 3 (P.piecewise (h ∘ D) D) D.domain ∧
      IsLocallyInjective (D.domain.domRestrict (P.piecewise (h ∘ D) D)) ∧
      (∀ y, (D.domain ∩ P.piecewise (h ∘ D) D ⁻¹' {y}).encard ≤ 2) ∧
      (∀ y ∉ U, P.piecewise (h ∘ D) D ⁻¹' {y} = D ⁻¹' {y}) ∧
      doublePointSet (P.piecewise (h ∘ D) D) D.domain =
        doublePointSet D D.domain \ hD.singularSet.branchCarrier cb ∧
      D.domain ∩ P.piecewise (h ∘ D) D ⁻¹' BdM ⊆ frontier D.domain ∧
      P.piecewise (h ∘ D) D '' D.domain ∩ BdM ⊆
        P.piecewise (h ∘ D) D '' frontier D.domain := by
  obtain ⟨U, h, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhN, hhrefl, hdisj, hgpl, hgloc,
    hgcard, hgfib, hgdouble⟩ :=
    hD.exists_separated_cell_along_boundary_branch cb E hE e he hei hesrc hd hcR hbd hsupp
      hAt hBt hSK hW hA hB hAB hdom hPpoly hPcpoly hinjP hinjQ hPcQ hseam hclean
  have hreflM : ∀ x ∈ N, h x ∈ BdM → x ∈ BdM := hhrefl N BdM N₁ Bd₁ hNE hN₁ hBdE hBd₁
  exact ⟨U, h, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hdisj, hgpl, hgloc, hgcard,
    hgfib, hgdouble,
    preimage_boundary_subset_frontier_piecewise_postcomp hbdpre hDN hreflM,
    image_inter_boundary_subset_image_frontier_piecewise_postcomp hbdpre hDN hreflM⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
