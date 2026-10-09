/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPreconnected.subset_or_disjoint_of_mem_nhdsWithin {X : Type*} [TopologicalSpace X]
    {J F Y : Set X} (hY : IsPreconnected Y) (hYJ : Y ⊆ J) (hF : IsClosed F)
    (hloc : ∀ x ∈ Y ∩ F, F ∈ 𝓝[J] x) : Y ⊆ F ∨ Disjoint Y F := by
  have hcover : Y ⊆ interior (F ∪ Jᶜ) ∪ Fᶜ := by
    intro y hy
    by_cases hyF : y ∈ F
    · left
      obtain ⟨O, hO, hyO, hOF⟩ := mem_nhdsWithin.mp (hloc y ⟨hy, hyF⟩)
      refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hO.mem_nhds hyO) ?_)
      intro z hz
      by_cases hzJ : z ∈ J
      · exact Or.inl (hOF ⟨hz, hzJ⟩)
      · exact Or.inr hzJ
    · exact Or.inr hyF
  have hdis : Y ∩ (interior (F ∪ Jᶜ) ∩ Fᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    rcases interior_subset hy.2.1 with h | h
    · exact hy.2.2 h
    · exact h (hYJ hy.1)
  rcases isPreconnected_iff_subset_of_disjoint.mp hY _ _ isOpen_interior hF.isOpen_compl
    hcover hdis with h | h
  · left
    intro y hy
    rcases interior_subset (h hy) with h' | h'
    · exact h'
    · exact absurd (hYJ hy) h'
  · exact Or.inr (Set.disjoint_left.mpr fun y hy hyF => h hy hyF)

section Circle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.eq_of_mem_nhdsWithin_of_ne {J F : Set E} (hJ : IsPLSphere 1 J)
    (hF : IsClosed F) (hFJ : F ⊆ J) {a c : E} (ha : a ∈ F) (hc : c ∈ F) (hac : a ≠ c)
    (hloc : ∀ x ∈ F, x ≠ c → F ∈ 𝓝[J] x) : F = J := by
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hAB, -⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hJ (hFJ ha) (hFJ hc) hac
  obtain ⟨O, hO, haO, hOF⟩ := mem_nhdsWithin.mp (hloc a ha hac)
  have harc : ∀ {A' : Set E} {γ' : ℝ → E}, IsPLHomeomorphOn γ' (Icc 0 1) A' → γ' 0 = a →
      γ' 1 = c → A' ⊆ J → A' ⊆ F := by
    intro A' γ' hγ' h0 h1 hA'J
    have hconn : IsConnected (A' \ {a, c}) := by
      rw [← h0, ← h1]
      exact hγ'.isConnected_sdiff_endpoints zero_lt_one
    have hcl : closure (A' \ {a, c}) = A' := by
      rw [← h0, ← h1]
      exact hγ'.closure_sdiff_endpoints zero_lt_one
    have haA' : a ∈ A' := h0 ▸ hγ'.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    rcases IsPreconnected.subset_or_disjoint_of_mem_nhdsWithin hconn.isPreconnected
      (sdiff_subset.trans hA'J) hF
      (fun x hx => hloc x hx.2 fun h => hx.1.2 (Or.inr h)) with h | h
    · intro x hx
      by_cases hxa : x = a
      · exact hxa ▸ ha
      by_cases hxc : x = c
      · exact hxc ▸ hc
      exact h ⟨hx, fun h' => Or.elim h' hxa hxc⟩
    · exfalso
      have hmem : a ∈ closure (A' \ {a, c}) := by
        rw [hcl]
        exact haA'
      obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp hmem O hO haO
      exact Set.disjoint_left.mp h hy (hOF ⟨hyO, hA'J hy.1⟩)
  have hA := harc hγ hγ0 hγ1 (subset_union_left.trans hAB.subset)
  have hB := harc hδ hδ0 hδ1 (subset_union_right.trans hAB.subset)
  exact Subset.antisymm hFJ (hAB.symm.subset.trans (union_subset hA hB))

theorem IsPLSphere.eq_pair_or_eq_or_exists_arc_of_mem_nhdsWithin {J F : Set E}
    (hJ : IsPLSphere 1 J) (hF : IsClosed F) (hFJ : F ⊆ J) {a b : E} (ha : a ∈ F) (hb : b ∈ F)
    (hab : a ≠ b) (hloc : ∀ x ∈ F, x ≠ a → x ≠ b → F ∈ 𝓝[J] x) :
    F = {a, b} ∨ F = J ∨
      ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) F ∧ γ 0 = a ∧ γ 1 = b := by
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hAB, -⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hJ (hFJ ha) (hFJ hb) hab
  have hside : ∀ {A' : Set E} {γ' : ℝ → E}, IsPLHomeomorphOn γ' (Icc 0 1) A' → γ' 0 = a →
      γ' 1 = b → A' ⊆ J → A' \ {a, b} ⊆ F ∨ Disjoint (A' \ {a, b}) F := by
    intro A' γ' hγ' h0 h1 hA'J
    have hconn : IsConnected (A' \ {a, b}) := by
      rw [← h0, ← h1]
      exact hγ'.isConnected_sdiff_endpoints zero_lt_one
    exact IsPreconnected.subset_or_disjoint_of_mem_nhdsWithin hconn.isPreconnected
      (sdiff_subset.trans hA'J) hF
      fun x hx => hloc x hx.2 (fun h => hx.1.2 (Or.inl h)) fun h => hx.1.2 (Or.inr h)
  have hends : ∀ {A' : Set E} {γ' : ℝ → E}, IsPLHomeomorphOn γ' (Icc 0 1) A' → γ' 0 = a →
      γ' 1 = b → ({a, b} : Set E) ⊆ A' := by
    intro A' γ' hγ' h0 h1
    refine pair_subset ?_ ?_
    · exact h0 ▸ hγ'.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    · exact h1 ▸ hγ'.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hAJ : A ⊆ J := subset_union_left.trans hAB.subset
  have hBJ : B ⊆ J := subset_union_right.trans hAB.subset
  have hpair : ({a, b} : Set E) ⊆ F := pair_subset ha hb
  have hsplit : ∀ x ∈ J, x ∈ ({a, b} : Set E) ∨ x ∈ A \ {a, b} ∨ x ∈ B \ {a, b} := by
    intro x hx
    by_cases hxab : x ∈ ({a, b} : Set E)
    · exact Or.inl hxab
    · rcases hAB.symm.subset hx with hxA | hxB
      · exact Or.inr (Or.inl ⟨hxA, hxab⟩)
      · exact Or.inr (Or.inr ⟨hxB, hxab⟩)
  have harcEq : ∀ {A' B' : Set E} {γ' : ℝ → E}, IsPLHomeomorphOn γ' (Icc 0 1) A' → γ' 0 = a →
      γ' 1 = b → A' \ {a, b} ⊆ F → Disjoint (B' \ {a, b}) F →
      (∀ x ∈ J, x ∈ ({a, b} : Set E) ∨ x ∈ A' \ {a, b} ∨ x ∈ B' \ {a, b}) → F = A' := by
    intro A' B' γ' hγ' h0 h1 hA' hB' hsplit'
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · rcases hsplit' x (hFJ hx) with h | h | h
      · exact hends hγ' h0 h1 h
      · exact h.1
      · exact (Set.disjoint_left.mp hB' h hx).elim
    · by_cases hxab : x ∈ ({a, b} : Set E)
      · exact hpair hxab
      · exact hA' ⟨hx, hxab⟩
  rcases hside hγ hγ0 hγ1 hAJ with hA | hA <;> rcases hside hδ hδ0 hδ1 hBJ with hB | hB
  · refine Or.inr (Or.inl (Subset.antisymm hFJ fun x hx => ?_))
    rcases hsplit x hx with h | h | h
    · exact hpair h
    · exact hA h
    · exact hB h
  · refine Or.inr (Or.inr ⟨γ, ?_, hγ0, hγ1⟩)
    rw [harcEq hγ hγ0 hγ1 hA hB hsplit]
    exact hγ
  · refine Or.inr (Or.inr ⟨δ, ?_, hδ0, hδ1⟩)
    rw [harcEq hδ hδ0 hδ1 hB hA fun x hx => (hsplit x hx).imp_right Or.symm]
    exact hδ
  · refine Or.inl (Subset.antisymm (fun x hx => ?_) hpair)
    rcases hsplit x (hFJ hx) with h | h | h
    · exact h
    · exact (Set.disjoint_left.mp hA h hx).elim
    · exact (Set.disjoint_left.mp hB h hx).elim

theorem IsPLSphere.exists_isPLHomeomorphOn_Icc_of_cycle {J : Set E} (hJ : IsPLSphere 1 J)
    {W Ed : Type*} [Finite W] {X : W → Set E} (hX : ∀ u, IsClosed (X u))
    (hXJ : ∀ u, X u ⊆ J) (hcover : J ⊆ ⋃ u, X u) (hXne : ∀ u, X u ≠ J)
    {p : Ed → E} (hp : Function.Injective p) {inc : W → Ed → Prop}
    (hpX : ∀ u e, p e ∈ X u ↔ inc u e)
    (hmeet : ∀ u u', u ≠ u' → ∀ x ∈ X u ∩ X u', ∃ e, inc u e ∧ inc u' e ∧ x = p e)
    (hdeg : ∀ u, ∃ e₁ e₂, e₁ ≠ e₂ ∧ inc u e₁ ∧ inc u e₂)
    (hdeg₃ : ∀ u e₁ e₂ e₃, inc u e₁ → inc u e₂ → inc u e₃ → e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃)
    (hend : ∀ e, ∃ u u', u ≠ u' ∧ inc u e ∧ inc u' e)
    (hend₃ : ∀ e u₁ u₂ u₃, inc u₁ e → inc u₂ e → inc u₃ e → u₁ = u₂ ∨ u₁ = u₃ ∨ u₂ = u₃)
    {u : W} {e₁ e₂ : Ed} (he : e₁ ≠ e₂) (h₁ : inc u e₁) (h₂ : inc u e₂) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) (X u) ∧ γ 0 = p e₁ ∧ γ 1 = p e₂ := by
  have hloc : ∀ {v : W} {f₁ f₂ : Ed}, f₁ ≠ f₂ → inc v f₁ → inc v f₂ →
      ∀ x ∈ X v, x ≠ p f₁ → x ≠ p f₂ → X v ∈ 𝓝[J] x := by
    intro v f₁ f₂ hf hv₁ hv₂ x hx hx₁ hx₂
    have hR : IsClosed (⋃ (v' : W) (_ : v' ≠ v), X v') :=
      isClosed_iUnion_of_finite fun v' => isClosed_iUnion_of_finite fun _ => hX v'
    have hxR : x ∉ ⋃ (v' : W) (_ : v' ≠ v), X v' := by
      intro hxR
      obtain ⟨v', hv', hxv'⟩ := mem_iUnion₂.mp hxR
      obtain ⟨g, hvg, -, hxg⟩ := hmeet v v' (Ne.symm hv') x ⟨hx, hxv'⟩
      rcases hdeg₃ v f₁ f₂ g hv₁ hv₂ hvg with h | h | h
      · exact hf h
      · exact hx₁ (hxg.trans (congrArg p h.symm))
      · exact hx₂ (hxg.trans (congrArg p h.symm))
    refine mem_nhdsWithin.mpr ⟨_, hR.isOpen_compl, hxR, fun y hy => ?_⟩
    obtain ⟨v', hyv'⟩ := mem_iUnion.mp (hcover hy.2)
    by_cases hv' : v' = v
    · rw [← hv']
      exact hyv'
    · exact absurd (mem_iUnion₂.mpr ⟨v', hv', hyv'⟩) hy.1
  have hpe : p e₁ ≠ p e₂ := fun h => he (hp h)
  rcases hJ.eq_pair_or_eq_or_exists_arc_of_mem_nhdsWithin (hX u) (hXJ u) ((hpX u e₁).mpr h₁)
    ((hpX u e₂).mpr h₂) hpe (fun x hx hx₁ hx₂ => hloc he h₁ h₂ x hx hx₁ hx₂) with
    hpair | hall | harc
  · exfalso
    obtain ⟨v, v', hvv', hv, hv'⟩ := hend e₁
    obtain ⟨u', hu'u, hu'⟩ : ∃ u', u' ≠ u ∧ inc u' e₁ := by
      by_cases hvu : v = u
      · exact ⟨v', fun h => hvv' (hvu.trans h.symm), hv'⟩
      · exact ⟨v, hvu, hv⟩
    obtain ⟨g₁, g₂, hg, hg₁, hg₂⟩ := hdeg u'
    obtain ⟨g, hge, hgu'⟩ : ∃ g, g ≠ e₁ ∧ inc u' g := by
      by_cases h : g₁ = e₁
      · exact ⟨g₂, fun h' => hg (h.trans h'.symm), hg₂⟩
      · exact ⟨g₁, h, hg₁⟩
    have hpg : p e₁ ≠ p g := fun h => hge (hp h).symm
    have hR : IsClosed (⋃ (v'' : W) (_ : v'' ≠ u ∧ v'' ≠ u'), X v'') :=
      isClosed_iUnion_of_finite fun v'' => isClosed_iUnion_of_finite fun _ => hX v''
    have hnot : p e₁ ∉ ⋃ (v'' : W) (_ : v'' ≠ u ∧ v'' ≠ u'), X v'' := by
      intro h
      obtain ⟨v'', ⟨hv''u, hv''u'⟩, hv''⟩ := mem_iUnion₂.mp h
      rcases hend₃ e₁ u u' v'' h₁ hu' ((hpX v'' e₁).mp hv'') with h' | h' | h'
      · exact hu'u h'.symm
      · exact hv''u h'.symm
      · exact hv''u' h'.symm
    have hlocu' : ∀ x ∈ X u', x ≠ p g → X u' ∈ 𝓝[J] x := by
      intro x hx hxg
      by_cases hxe : x = p e₁
      · subst hxe
        refine mem_nhdsWithin.mpr ⟨(⋃ (v'' : W) (_ : v'' ≠ u ∧ v'' ≠ u'), X v'')ᶜ ∩ {p e₂}ᶜ,
          hR.isOpen_compl.inter isOpen_compl_singleton, ⟨hnot, hpe⟩, fun y hy => ?_⟩
        obtain ⟨v'', hyv''⟩ := mem_iUnion.mp (hcover hy.2)
        by_cases hv1 : v'' = u'
        · rw [← hv1]
          exact hyv''
        by_cases hv2 : v'' = u
        · rw [hv2, hpair] at hyv''
          rcases hyv'' with h3 | h3
          · rw [h3]
            exact (hpX u' e₁).mpr hu'
          · exact absurd h3 hy.1.2
        · exact absurd (mem_iUnion₂.mpr ⟨v'', ⟨hv2, hv1⟩, hyv''⟩) hy.1.1
      · exact hloc (Ne.symm hge) hu' hgu' x hx hxe hxg
    exact hXne u' (hJ.eq_of_mem_nhdsWithin_of_ne (hX u') (hXJ u') ((hpX u' e₁).mpr hu')
      ((hpX u' g).mpr hgu') hpg hlocu')
  · exact absurd hall (hXne u)
  · exact harc

end Circle

section Model

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLCellOn_one_of_isPLHomeomorphOn_Icc {A : Set E3} {γ : ℝ → E3}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) : IsPLCellOn 1 A {γ 0, γ 1} := by
  let L : ℝ →ᵃ[ℝ] (Fin 2 → ℝ) := AffineMap.lineMap ![1, 0] ![0, 1]
  have hL0 : ∀ t : ℝ, L t 0 = 1 - t := by
    intro t
    simp only [L, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp
    ring
  have hL1 : ∀ t : ℝ, L t 1 = t := by
    intro t
    simp only [L, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp
  have hLbij : BijOn L (Icc 0 1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) := by
    refine ⟨fun t ht => ⟨fun i => ?_, ?_⟩, fun s _ t _ hst => ?_, fun x hx => ?_⟩
    · fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, hL0]
        linarith [ht.2]
      · simp only [Fin.mk_one, Fin.isValue, hL1]
        exact ht.1
    · rw [Fin.sum_univ_two, hL0, hL1]
      ring
    · have := congrFun hst 1
      rwa [hL1, hL1] at this
    · refine ⟨x 1, ⟨hx.1 1, ?_⟩, ?_⟩
      · have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
        linarith [hx.1 0]
      · funext j
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, hL0]
          have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
          linarith
        · simp only [Fin.mk_one, Fin.isValue, hL1]
  have hLpl : IsPLHomeomorphOn L (Icc 0 1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      ((isPiecewiseAffineOn_of_affine L isOpen_univ).mono_of_isPolyhedron
        isHPolytope_Icc.isPolyhedron (subset_univ _)) hLbij
  have hinv0 : Function.invFunOn L (Icc 0 1) ![1, 0] = 0 := by
    have h := hLbij.invOn_invFunOn.1 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    rwa [show L 0 = ![1, 0] from AffineMap.lineMap_apply_zero _ _] at h
  have hinv1 : Function.invFunOn L (Icc 0 1) ![0, 1] = 1 := by
    have h := hLbij.invOn_invFunOn.1 (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    rwa [show L 1 = ![0, 1] from AffineMap.lineMap_apply_one _ _] at h
  have hcell := isPLCellOn_id_of_isPLBall (hLpl.symm.trans hγ)
  rw [stdSimplexBoundary_one_eq_pair, image_pair] at hcell
  simpa only [Function.comp_apply, hinv0, hinv1] using hcell

end Model

end DifferentialGeometry.Topology.PiecewiseLinear
