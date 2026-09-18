import DifferentialGeometry.Topology.PiecewiseLinear.BranchSlideSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_separated_along_branch (hD : NormalSingularCellData D BdM B)
    (cb : hD.singularSet.Branch) {W : Set M} {P Q : Set (EuclideanSpace ℝ (Fin 2))}
    {d R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target)
    (hd : 0 ≤ d) (hcR : c + 2 * d ≤ R) (hca : c - d < a)
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
      (∀ (Bd₁ : Set (EuclideanSpace ℝ (Fin 3))) (T : Set (ℝ × ℝ)),
        (∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁) →
        (∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).2 ∈ T) → ∀ x, h x ∈ BdM ↔ x ∈ BdM) ∧
      Disjoint (h '' (D '' P)) (D '' Q) :=
  exists_separated_slide E hE e he hei hesrc hd hcR hca hsupp hAt hBt hSK hW hA hB hAB

omit [T2Space M] [HasGroupoid M (plGroupoid 3)] in
theorem isLocallyInjective_domRestrict (hD : NormalSingularCellData D BdM B) :
    IsLocallyInjective (D.domain.domRestrict D) := by
  rw [isLocallyInjective_iff_nhds]
  intro x
  obtain ⟨V, hV, hinj⟩ := hD.locallyInjective x x.2
  refine ⟨((↑) : D.domain → EuclideanSpace ℝ (Fin 2)) ⁻¹' V,
    preimage_coe_mem_nhds_subtype.mpr hV, ?_⟩
  intro a ha b hb hab
  exact Subtype.ext (hinj ha hb hab)

open Classical in
theorem exists_separated_cell_along_branch (hD : NormalSingularCellData D BdM B)
    (cb : hD.singularSet.Branch) {W : Set M} {P Pc Q : Set (EuclideanSpace ℝ (Fin 2))}
    {d R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target)
    (hd : 0 ≤ d) (hcR : c + 2 * d ≤ R) (hca : c - d < a)
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
      closure U ⊆ W ∧ IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧
      (∀ (Bd₁ : Set (EuclideanSpace ℝ (Fin 3))) (T : Set (ℝ × ℝ)),
        (∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁) →
        (∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).2 ∈ T) → ∀ x, h x ∈ BdM ↔ x ∈ BdM) ∧
      Disjoint (h '' (D '' P)) (D '' Q) ∧
      IsPLOn 2 3 (P.piecewise (h ∘ D) D) D.domain ∧
      IsLocallyInjective (D.domain.domRestrict (P.piecewise (h ∘ D) D)) ∧
      (∀ y, (D.domain ∩ P.piecewise (h ∘ D) D ⁻¹' {y}).encard ≤ 2) ∧
      (∀ y ∉ U, P.piecewise (h ∘ D) D ⁻¹' {y} = D ⁻¹' {y}) ∧
      doublePointSet (P.piecewise (h ∘ D) D) D.domain =
        doublePointSet D D.domain \ hD.singularSet.branchCarrier cb := by
  obtain ⟨U, h, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhbd, hdisj⟩ :=
    hD.exists_separated_along_branch cb E hE e he hei hesrc hd hcR hca hsupp hAt hBt hSK hW
      hA hB hAB
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
  refine ⟨U, h, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhbd, hdisj, hgpl, hgloc, hgcard, hgfib, ?_⟩
  refine doublePointSet_piecewise_postcomp hdom hhinj hhfix hhmap hinjP hinjQU hPcQU hdisj
    hSU ?_
  intro y hy
  exact hclean ⟨hy.1, hUsub hy.2⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
