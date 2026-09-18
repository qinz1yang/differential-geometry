import DifferentialGeometry.Topology.PiecewiseLinear.BranchSeparationBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u}

theorem eq_of_separated_fiber {Δ : Set (EuclideanSpace ℝ (Fin 2))}
    {D g : EuclideanSpace ℝ (Fin 2) → M} {S U : Set M}
    (hfib : ∀ y ∉ U, g ⁻¹' {y} = D ⁻¹' {y})
    (hdouble : doublePointSet g Δ ⊆ doublePointSet D Δ \ S)
    (hclean : doublePointSet D Δ ∩ U ⊆ S)
    {v w : EuclideanSpace ℝ (Fin 2)} (hv : v ∈ Δ) (hw : w ∈ Δ) (hvw : v ≠ w)
    (hgvw : g v = g w) : g v ∉ U ∧ D v = g v ∧ D w = g v := by
  have hmem : g v ∈ doublePointSet g Δ := ⟨v, hv, w, hw, hvw, rfl, hgvw.symm⟩
  obtain ⟨hold, hnotS⟩ := hdouble hmem
  have hnotU : g v ∉ U := fun hU => hnotS (hclean ⟨hold, hU⟩)
  have hpre := hfib (g v) hnotU
  have hv' : v ∈ g ⁻¹' {g v} := rfl
  have hw' : w ∈ g ⁻¹' {g v} := hgvw.symm
  rw [hpre] at hv' hw'
  exact ⟨hnotU, hv', hw'⟩

open Classical in
theorem vertexCollisionPairs_subset_of_doublePointSet_subset_sdiff
    {Δ : Set (EuclideanSpace ℝ (Fin 2))} {D g : EuclideanSpace ℝ (Fin 2) → M}
    {S U : Set M}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    (hKspace : K.space = Δ)
    (hfib : ∀ y ∉ U, g ⁻¹' {y} = D ⁻¹' {y})
    (hdouble : doublePointSet g Δ ⊆ doublePointSet D Δ \ S)
    (hclean : doublePointSet D Δ ∩ U ⊆ S) :
    vertexCollisionPairs K g ⊆ vertexCollisionPairs K D := by
  intro t ht
  rw [mem_vertexCollisionPairs] at ht ⊢
  obtain ⟨hsub, hcard, hninj⟩ := ht
  have hΔ : ∀ x ∈ (t : Set (EuclideanSpace ℝ (Fin 2))), x ∈ Δ := fun x hx =>
    hKspace ▸ K.vertices_subset_space (hsub hx)
  refine ⟨hsub, hcard, ?_⟩
  intro hinjD
  refine hninj ?_
  intro v hv w hw hgvw
  by_contra hvw
  obtain ⟨-, hDv, hDw⟩ :=
    eq_of_separated_fiber hfib hdouble hclean (hΔ v hv) (hΔ w hw) hvw hgvw
  exact hvw (hinjD hv hw (hDv.trans hDw.symm))

open Classical in
theorem simplicialComplexity_lt_of_doublePointSet_subset_sdiff
    {Δ : Set (EuclideanSpace ℝ (Fin 2))} {D g : EuclideanSpace ℝ (Fin 2) → M}
    {S U : Set M}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    (hKspace : K.space = Δ)
    (hfib : ∀ y ∉ U, g ⁻¹' {y} = D ⁻¹' {y})
    (hdouble : doublePointSet g Δ ⊆ doublePointSet D Δ \ S)
    (hclean : doublePointSet D Δ ∩ U ⊆ S) (hSU : S ⊆ U)
    {v w : EuclideanSpace ℝ (Fin 2)} (hv : v ∈ K.vertices) (hw : w ∈ K.vertices)
    (hvw : v ≠ w) (hDvw : D v = D w) (hDS : D v ∈ S) :
    simplicialComplexity K g < simplicialComplexity K D := by
  have hvΔ : v ∈ Δ := hKspace ▸ K.vertices_subset_space hv
  have hwΔ : w ∈ Δ := hKspace ▸ K.vertices_subset_space hw
  have hgne : g v ≠ g w := by
    intro hg
    obtain ⟨hnotU, hDv, -⟩ :=
      eq_of_separated_fiber hfib hdouble hclean hvΔ hwΔ hvw hg
    refine hnotU (hSU ?_)
    rw [← hDv]
    exact hDS
  have hsD : ({v, w} : Finset (EuclideanSpace ℝ (Fin 2))) ∈ vertexCollisionPairs K D := by
    rw [mem_vertexCollisionPairs]
    refine ⟨?_, by simp [hvw], ?_⟩
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
        mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hw
    · intro hinj
      exact hvw (hinj (by simp) (by simp) hDvw)
  have hsg : ({v, w} : Finset (EuclideanSpace ℝ (Fin 2))) ∉ vertexCollisionPairs K g := by
    rw [mem_vertexCollisionPairs]
    rintro ⟨-, -, hninj⟩
    refine hninj ?_
    intro α hα β hβ hαβ
    have hα' : α = v ∨ α = w := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
        mem_singleton_iff] using hα
    have hβ' : β = v ∨ β = w := by
      simpa only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
        mem_singleton_iff] using hβ
    rcases hα' with rfl | rfl <;> rcases hβ' with rfl | rfl
    · rfl
    · exact absurd hαβ hgne
    · exact absurd hαβ.symm hgne
    · rfl
  have hsubset := vertexCollisionPairs_subset_of_doublePointSet_subset_sdiff
    K hKspace hfib hdouble hclean
  unfold simplicialComplexity
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsubset]
  exact ⟨_, hsD, hsg⟩

open Classical in
theorem exists_simplicialComplexity_lt_of_doublePointSet_subset_sdiff
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) (g : EuclideanSpace ℝ (Fin 2) → M) {S U : Set M}
    (hfib : ∀ y ∉ U, g ⁻¹' {y} = D ⁻¹' {y})
    (hdouble : doublePointSet g D.domain ⊆ doublePointSet D D.domain \ S)
    (hclean : doublePointSet D D.domain ∩ U ⊆ S) (hSU : S ⊆ U)
    (hS : (S ∩ doublePointSet D D.domain).Nonempty) :
    ∃ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
        (hKfinite : K.faces.Finite),
      let _ : Finite K.faces := hKfinite.to_subtype
      K.space = D.domain ∧ simplicialComplexity K g < simplicialComplexity K D := by
  obtain ⟨y, hyS, x, hx, z, hz, hxz, hDx, hDz⟩ := hS
  obtain ⟨K₀, hK₀finite, hK₀space⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite K₀.faces := hK₀finite.to_subtype
  have hxK₀ : x ∈ K₀.space := by rw [hK₀space]; exact hx
  obtain ⟨K₁, hK₁, hK₁finite, hxK₁⟩ := exists_isSubdivision_singleton_mem K₀ hxK₀
  let _ : Finite K₁.faces := hK₁finite.to_subtype
  have hzK₁ : z ∈ K₁.space := by rw [hK₁.space_eq, hK₀space]; exact hz
  obtain ⟨K, hK, hKfinite, hzK⟩ := exists_isSubdivision_singleton_mem K₁ hzK₁
  let _ : Finite K.faces := hKfinite.to_subtype
  have hKspace : K.space = D.domain := hK.space_eq.trans (hK₁.space_eq.trans hK₀space)
  have hxK : x ∈ K.vertices := hK.singleton_mem hxK₁
  have hDxS : D x ∈ S := by rw [hDx]; exact hyS
  refine ⟨K, hKfinite, hKspace, ?_⟩
  exact simplicialComplexity_lt_of_doublePointSet_subset_sdiff K hKspace hfib hdouble
    hclean hSU hxK hzK hxz (hDx.trans hDz.symm) hDxS

namespace NormalSingularCellData

variable [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
  {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
theorem exists_separated_cell_simplicialComplexity_lt_along_boundary_branch
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
    (hclean : doublePointSet D D.domain ∩ W ⊆ hD.singularSet.branchCarrier cb) :
    ∃ (U : Set M) (h : M → M)
        (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
        (hKfinite : K.faces.Finite),
      let _ : Finite K.faces := hKfinite.to_subtype
      IsOpen U ∧ hD.singularSet.branchCarrier cb ⊆ U ∧
      closure U ⊆ W ∧ IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧ MapsTo h U U ∧
      (∀ (N : Set M) (N₁ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) →
        (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) → MapsTo h N N) ∧
      (∀ (N Bd : Set M) (N₁ Bd₁ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) →
        (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) →
        (∀ x ∈ E.source, x ∈ Bd ↔ E x ∈ Bd₁) →
        (∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).1 = 0) →
        ∀ x ∈ N, h x ∈ Bd → x ∈ Bd) ∧
      Disjoint (h '' (D '' P)) (D '' Q) ∧
      IsPLOn 2 3 (P.piecewise (h ∘ D) D) D.domain ∧
      IsLocallyInjective (D.domain.domRestrict (P.piecewise (h ∘ D) D)) ∧
      (∀ y, (D.domain ∩ P.piecewise (h ∘ D) D ⁻¹' {y}).encard ≤ 2) ∧
      (∀ y ∉ U, P.piecewise (h ∘ D) D ⁻¹' {y} = D ⁻¹' {y}) ∧
      doublePointSet (P.piecewise (h ∘ D) D) D.domain =
        doublePointSet D D.domain \ hD.singularSet.branchCarrier cb ∧
      K.space = D.domain ∧
      simplicialComplexity K (P.piecewise (h ∘ D) D) < simplicialComplexity K D := by
  obtain ⟨U, h, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhN, hhrefl, hdisj, hgpl, hgloc,
    hgcard, hgfib, hgdouble⟩ :=
    hD.exists_separated_cell_along_boundary_branch cb E hE e he hei hesrc hd hcR hbd hsupp
      hAt hBt hSK hW hA hB hAB hdom hPpoly hPcpoly hinjP hinjQ hPcQ hseam hclean
  have hUsub : U ⊆ W := subset_closure.trans hUW
  have hSne :
      (hD.singularSet.branchCarrier cb ∩ doublePointSet D D.domain).Nonempty := by
    obtain ⟨y, hy⟩ := (hD.singularSet.branchCarrier_isConnected cb).nonempty
    exact ⟨y, hy, hD.singularSet.branchCarrier_subset_doublePointSet cb hy⟩
  obtain ⟨K, hKfinite, hKspace, hlt⟩ :=
    exists_simplicialComplexity_lt_of_doublePointSet_subset_sdiff D
      (P.piecewise (h ∘ D) D) hgfib hgdouble.subset
      (fun y hy => hclean ⟨hy.1, hUsub hy.2⟩) hSU hSne
  exact ⟨U, h, K, hKfinite, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhN, hhrefl, hdisj,
    hgpl, hgloc, hgcard, hgfib, hgdouble, hKspace, hlt⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
