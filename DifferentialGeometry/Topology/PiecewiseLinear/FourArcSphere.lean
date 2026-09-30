/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem perm_add_two_iff_eq_add_or_sub {π : Equiv.Perm (Fin 4)} :
    (∀ i, π (i + 2) = π i + 2) ↔ ∀ i, π i = π 0 + i ∨ π i = π 0 - i := by
  have hall : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  constructor
  · intro h i
    have h2 : π 2 = π 0 + 2 := by
      have hh := h 0
      rwa [(by decide : (0 : Fin 4) + 2 = 2)] at hh
    have h3 : π 3 = π 1 + 2 := by
      have hh := h 1
      rwa [(by decide : (1 : Fin 4) + 2 = 3)] at hh
    have hne0 : π 1 ≠ π 0 := fun e => absurd (π.injective e) (by decide)
    have hne2 : π 1 ≠ π 0 + 2 := fun e => absurd (π.injective (e.trans h2.symm)) (by decide)
    have hkey := (by decide : ∀ x z : Fin 4, x ≠ z → x ≠ z + 2 → x = z + 1 ∨ x = z + 3)
      (π 1) (π 0) hne0 hne2
    rcases hall i with rfl | rfl | rfl | rfl
    · exact Or.inl (by simp)
    · rcases hkey with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by rw [h1, (by decide : ∀ z : Fin 4, z - 1 = z + 3)])
    · exact Or.inl h2
    · rcases hkey with h1 | h1
      · exact Or.inl (by rw [h3, h1, (by decide : ∀ z : Fin 4, z + 1 + 2 = z + 3)])
      · exact Or.inr (by rw [h3, h1, (by decide : ∀ z : Fin 4, z + 3 + 2 = z - 3)])
  · intro hd i
    have h2 : π 2 = π 0 + 2 := by
      rcases hd 2 with h | h
      · exact h
      · rw [h, (by decide : ∀ z : Fin 4, z - 2 = z + 2)]
    have hne13 : π 1 ≠ π 3 := fun e => absurd (π.injective e) (by decide)
    have h31 : π 3 = π 1 + 2 := by
      rcases hd 1 with h1 | h1 <;> rcases hd 3 with h3 | h3
      · rw [h3, h1, (by decide : ∀ z : Fin 4, z + 1 + 2 = z + 3)]
      · exact absurd (h1.trans (by rw [h3, (by decide : ∀ z : Fin 4, z - 3 = z + 1)])) hne13
      · exact absurd (h1.trans (by rw [h3, (by decide : ∀ z : Fin 4, z - 1 = z + 3)])) hne13
      · rw [h3, h1, (by decide : ∀ z : Fin 4, z - 1 + 2 = z - 3)]
    rcases hall i with rfl | rfl | rfl | rfl
    · rw [(by decide : (0 : Fin 4) + 2 = 2)]
      exact h2
    · rw [(by decide : (1 : Fin 4) + 2 = 3)]
      exact h31
    · rw [(by decide : (2 : Fin 4) + 2 = 0), h2, (by decide : ∀ z : Fin 4, z + 2 + 2 = z)]
    · rw [(by decide : (3 : Fin 4) + 2 = 1), h31, (by decide : ∀ z : Fin 4, z + 2 + 2 = z)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLSphere_one_union_of_isPLHomeomorphOn_Icc {A B : Set E} {γ δ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hδ : IsPLHomeomorphOn δ (Icc 0 1) B)
    (hδzero : δ 0 = γ 0) (hδone : δ 1 = γ 1) (hAB : A ∩ B = {γ 0, γ 1}) :
    IsPLSphere 1 (A ∪ B) := by
  classical
  have hone : (0 : ℝ) < 1 := by norm_num
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hmem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  obtain ⟨V, hV, hVcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
    (0 : EuclideanSpace ℝ (Fin 2))
    (Filter.univ_mem : univ ∈ nhds (0 : EuclideanSpace ℝ (Fin 2)))
  have hmodel := (isPLBall_convexHull_of_affineIndependent V hV hVcard).isPLSphere_frontier
  obtain ⟨p, hp⟩ := hmodel.nonempty
  obtain ⟨q, hq⟩ := (hmodel.isConnected_sdiff_singleton_one p).nonempty
  have hpq : p ≠ q := fun h => hq.2 h.symm
  obtain ⟨A₀, B₀, α, β, hα, hβ, hαzero, hαone, hβzero, hβone, hcover, hmeet⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hmodel hp hq.1 hpq
  have hA₀ : IsPLBall 1 A₀ := (isPLBall_Icc hone).of_isPLHomeomorphOn hα
  have hB₀ : IsPLBall 1 B₀ := (isPLBall_Icc hone).of_isPLHomeomorphOn hβ
  have hαp : Function.invFunOn α (Icc 0 1) p = 0 := by
    rw [← hαzero]
    exact hα.bijOn.invOn_invFunOn.1 hmem0
  have hαq : Function.invFunOn α (Icc 0 1) q = 1 := by
    rw [← hαone]
    exact hα.bijOn.invOn_invFunOn.1 hmem1
  have hβp : Function.invFunOn β (Icc 0 1) p = 0 := by
    rw [← hβzero]
    exact hβ.bijOn.invOn_invFunOn.1 hmem0
  have hβq : Function.invFunOn β (Icc 0 1) q = 1 := by
    rw [← hβone]
    exact hβ.bijOn.invOn_invFunOn.1 hmem1
  have hu : IsPLHomeomorphOn (γ ∘ Function.invFunOn α (Icc 0 1)) A₀ A := hα.symm.trans hγ
  have hv : IsPLHomeomorphOn (δ ∘ Function.invFunOn β (Icc 0 1)) B₀ B := hβ.symm.trans hδ
  have heq : EqOn (γ ∘ Function.invFunOn α (Icc 0 1))
      (δ ∘ Function.invFunOn β (Icc 0 1)) (A₀ ∩ B₀) := by
    rw [hmeet]
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp only [Function.comp_apply, hαp, hβp, hδzero]
    · simp only [Function.comp_apply, hαq, hβq, hδone]
  have hsurj : SurjOn (γ ∘ Function.invFunOn α (Icc 0 1)) (A₀ ∩ B₀) (A ∩ B) := by
    rw [hmeet, hAB]
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨p, by simp, by simp only [Function.comp_apply, hαp]⟩
    · exact ⟨q, by simp, by simp only [Function.comp_apply, hαq]⟩
  obtain ⟨g, hg, -, -⟩ :=
    exists_isPLHomeomorphOn_union hA₀.isPolyhedron hB₀.isPolyhedron hu hv heq hsurj
  rw [hcover] at hg
  exact hmodel.of_isPLHomeomorphOn hg

theorem exists_isPLBall_pair_separating_of_isPLSphere_two {S C P Q : Set E} {a b : E}
    (hS : IsPLSphere 2 S) (hC : IsPLSphere 1 C) (hCS : C ⊆ S) (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hPC : P ∩ C = {a, b}) (hQC : Q ∩ C = {a, b})
    (hPconn : IsPreconnected (P \ {a, b})) (hPne : (P \ {a, b}).Nonempty)
    (hQconn : IsPreconnected (Q \ {a, b})) (hQne : (Q \ {a, b}).Nonempty)
    (hsep : ∀ U ⊆ S \ C, IsPreconnected U → (U ∩ P).Nonempty → (U ∩ Q).Nonempty → False) :
    ∃ (D₀ D₁ : Set E) (r₀ r₁ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
        IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
        r₀ '' stdSimplexBoundary 2 = C ∧ r₁ '' stdSimplexBoundary 2 = C ∧
        D₀ ∪ D₁ = S ∧ D₀ ∩ D₁ = C ∧ P ⊆ D₀ ∧ Q ⊆ D₁ := by
  classical
  obtain ⟨D₀, D₁, hcover, hinter, r₀, r₁, hr₀, hr₁, hb₀, hb₁⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS hC hCS
  have hD₀ : IsPLBall 2 D₀ := ⟨r₀, hr₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  have hCD₀ : C ⊆ D₀ := fun x hx => (hinter.symm.subset hx).1
  have hCD₁ : C ⊆ D₁ := fun x hx => (hinter.symm.subset hx).2
  have hD₀S : D₀ ⊆ S := fun x hx => hcover.subset (mem_union_left _ hx)
  have hD₁S : D₁ ⊆ S := fun x hx => hcover.subset (mem_union_right _ hx)
  have hconn₀ : IsPreconnected (D₀ \ C) := by
    rw [← hb₀]
    exact hr₀.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected
  have hconn₁ : IsPreconnected (D₁ \ C) := by
    rw [← hb₁]
    exact hr₁.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected
  have hsub₀ : D₀ \ C ⊆ S \ C := fun x hx => ⟨hD₀S hx.1, hx.2⟩
  have hsub₁ : D₁ \ C ⊆ S \ C := fun x hx => ⟨hD₁S hx.1, hx.2⟩
  have hsplit : ∀ s : Set E, IsPreconnected s → s ⊆ S \ C → s ⊆ D₀ ∨ s ⊆ D₁ := by
    intro s hs hsub
    by_contra hcon
    obtain ⟨x, hx, hxD₀⟩ := not_subset.mp fun h => hcon (Or.inl h)
    obtain ⟨y, hy, hyD₁⟩ := not_subset.mp fun h => hcon (Or.inr h)
    have hcov : s ⊆ D₁ᶜ ∪ D₀ᶜ := by
      intro z hz
      by_cases hzD₁ : z ∈ D₁
      · exact mem_union_right _ fun hzD₀ => (hsub hz).2 (hinter.subset ⟨hzD₀, hzD₁⟩)
      · exact mem_union_left _ hzD₁
    obtain ⟨z, hz⟩ := hs D₁ᶜ D₀ᶜ hD₁.isPolyhedron.isCompact.isClosed.isOpen_compl
      hD₀.isPolyhedron.isCompact.isClosed.isOpen_compl hcov ⟨y, hy, hyD₁⟩ ⟨x, hx, hxD₀⟩
    rcases hcover.symm.subset (hsub hz.1).1 with h | h
    · exact hz.2.2 h
    · exact hz.2.1 h
  have hab : ({a, b} : Set E) ⊆ C := fun x hx => (hPC.symm.subset hx).2
  have hPdiff : P \ {a, b} = P \ C := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hxab⟩
      exact ⟨hxP, fun hxC => hxab (hPC.subset ⟨hxP, hxC⟩)⟩
    · rintro x ⟨hxP, hxC⟩
      exact ⟨hxP, fun hxab => hxC (hab hxab)⟩
  have hQdiff : Q \ {a, b} = Q \ C := by
    apply Subset.antisymm
    · rintro x ⟨hxQ, hxab⟩
      exact ⟨hxQ, fun hxC => hxab (hQC.subset ⟨hxQ, hxC⟩)⟩
    · rintro x ⟨hxQ, hxC⟩
      exact ⟨hxQ, fun hxab => hxC (hab hxab)⟩
  have hfill : ∀ R D : Set E, C ⊆ D → R \ {a, b} ⊆ D → R ⊆ D := by
    intro R D hCD hsub x hxR
    by_cases hx : x ∈ ({a, b} : Set E)
    · exact hCD (hab hx)
    · exact hsub ⟨hxR, hx⟩
  have hPsub : P \ {a, b} ⊆ S \ C := by
    rw [hPdiff]
    exact fun x hx => ⟨hPS hx.1, hx.2⟩
  have hQsub : Q \ {a, b} ⊆ S \ C := by
    rw [hQdiff]
    exact fun x hx => ⟨hQS hx.1, hx.2⟩
  have hmeetP : ∀ D : Set E, P \ {a, b} ⊆ D → (D \ C ∩ P).Nonempty := by
    intro D hsub
    obtain ⟨x, hx⟩ := hPne
    exact ⟨x, ⟨hsub hx, (hPdiff.subset hx).2⟩, hx.1⟩
  have hmeetQ : ∀ D : Set E, Q \ {a, b} ⊆ D → (D \ C ∩ Q).Nonempty := by
    intro D hsub
    obtain ⟨x, hx⟩ := hQne
    exact ⟨x, ⟨hsub hx, (hQdiff.subset hx).2⟩, hx.1⟩
  rcases hsplit _ hPconn hPsub with hP₀ | hP₁
  · rcases hsplit _ hQconn hQsub with hQ₀ | hQ₁
    · exact (hsep (D₀ \ C) hsub₀ hconn₀ (hmeetP D₀ hP₀) (hmeetQ D₀ hQ₀)).elim
    · exact ⟨D₀, D₁, r₀, r₁, hr₀, hr₁, hb₀, hb₁, hcover, hinter,
        hfill P D₀ hCD₀ hP₀, hfill Q D₁ hCD₁ hQ₁⟩
  · rcases hsplit _ hQconn hQsub with hQ₀ | hQ₁
    · exact ⟨D₁, D₀, r₁, r₀, hr₁, hr₀, hb₁, hb₀, (union_comm D₁ D₀).trans hcover,
        (inter_comm D₁ D₀).trans hinter, hfill P D₁ hCD₁ hP₁, hfill Q D₀ hCD₀ hQ₀⟩
    · exact (hsep (D₁ \ C) hsub₁ hconn₁ (hmeetP D₁ hP₁) (hmeetQ D₁ hQ₁)).elim

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_of_fourArcSphere {S : Set E} {S' : Set F} {y₀ y₁ : E}
    {y₀' y₁' : F} {T : Fin 4 → Set E} {T' : Fin 4 → Set F} {γ : Fin 4 → ℝ → E}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i))
    (hγzero : ∀ i, γ i 0 = y₀) (hγone : ∀ i, γ i 1 = y₁)
    (hTS : ∀ i, T i ⊆ S) (hTS' : ∀ i, T' i ⊆ S')
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {y₀, y₁})
    (hTT' : ∀ i j, i ≠ j → T' i ∩ T' j = {y₀', y₁'})
    (hsep : ∀ i : Fin 4, ∀ U ⊆ S \ (T i ∪ T (i + 2)), IsPreconnected U →
      (U ∩ T (i + 1)).Nonempty → (U ∩ T (i + 3)).Nonempty → False)
    (hsep' : ∀ i : Fin 4, ∀ U ⊆ S' \ (T' i ∪ T' (i + 2)), IsPreconnected U →
      (U ∩ T' (i + 1)).Nonempty → (U ∩ T' (i + 3)).Nonempty → False)
    {π : Equiv.Perm (Fin 4)} (hπ : ∀ i, π (i + 2) = π i + 2) {t : Fin 4 → E → F}
    (ht : ∀ i, IsPLHomeomorphOn (t i) (T i) (T' (π i)))
    (htzero : ∀ i, t i y₀ = y₀') (htone : ∀ i, t i y₁ = y₁') :
    ∃ g : E → F, IsPLHomeomorphOn g S S' ∧ g y₀ = y₀' ∧ g y₁ = y₁' ∧
      (∀ i, EqOn g (t i) (T i)) ∧ ∀ i, g '' T i = T' (π i) := by
  classical
  have hone : (0 : ℝ) < 1 := by norm_num
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hmem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hall : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hTball : ∀ i, IsPLBall 1 (T i) := fun i =>
    (isPLBall_Icc hone).of_isPLHomeomorphOn (hγ i)
  have hzeromem : ∀ i, y₀ ∈ T i := by
    intro i
    rw [← hγzero i]
    exact (hγ i).bijOn.mapsTo hmem0
  have honemem : ∀ i, y₁ ∈ T i := by
    intro i
    rw [← hγone i]
    exact (hγ i).bijOn.mapsTo hmem1
  have hpolemem : ∀ i, ({y₀, y₁} : Set E) ⊆ T i := fun i => pair_subset (hzeromem i) (honemem i)
  have hTconn : ∀ i, IsConnected (T i \ {y₀, y₁}) := by
    intro i
    have h := (hγ i).isConnected_sdiff_endpoints hone
    rwa [hγzero i, hγone i] at h
  have himagepair : ∀ i, t i '' ({y₀, y₁} : Set E) = ({y₀', y₁'} : Set F) := by
    intro i
    rw [image_pair, htzero i, htone i]
  have hT'conn : ∀ i, IsConnected (T' (π i) \ {y₀', y₁'}) := by
    intro i
    have himg : t i '' (T i \ {y₀, y₁}) = T' (π i) \ {y₀', y₁'} := by
      rw [(ht i).bijOn.injOn.image_sdiff_subset (hpolemem i), (ht i).image_eq, himagepair i]
    rw [← himg]
    exact (hTconn i).image _ ((ht i).isPiecewiseAffineOn.continuousOn.mono sdiff_subset)
  have hCS : T 0 ∪ T 2 ⊆ S := union_subset (hTS 0) (hTS 2)
  have hC : IsPLSphere 1 (T 0 ∪ T 2) := by
    refine isPLSphere_one_union_of_isPLHomeomorphOn_Icc (hγ 0) (hγ 2) ?_ ?_ ?_
    · rw [hγzero 2, hγzero 0]
    · rw [hγone 2, hγone 0]
    · rw [hTT 0 2 (by decide), hγzero 0, hγone 0]
  have hT1C : T 1 ∩ (T 0 ∪ T 2) = {y₀, y₁} := by
    rw [inter_union_distrib_left, hTT 1 0 (by decide), hTT 1 2 (by decide), union_self]
  have hT3C : T 3 ∩ (T 0 ∪ T 2) = {y₀, y₁} := by
    rw [inter_union_distrib_left, hTT 3 0 (by decide), hTT 3 2 (by decide), union_self]
  have hsepS : ∀ U ⊆ S \ (T 0 ∪ T 2), IsPreconnected U →
      (U ∩ T 1).Nonempty → (U ∩ T 3).Nonempty → False := by
    have h := hsep 0
    simp only [(by decide : (0 : Fin 4) + 2 = 2), (by decide : (0 : Fin 4) + 1 = 1),
      (by decide : (0 : Fin 4) + 3 = 3)] at h
    exact h
  obtain ⟨D₀, D₁, r₀, r₁, hr₀, hr₁, hb₀, hb₁, hcover, hinter, hT1D, hT3D⟩ :=
    exists_isPLBall_pair_separating_of_isPLSphere_two hS hC hCS (hTS 1) (hTS 3) hT1C hT3C
      (hTconn 1).isPreconnected (hTconn 1).nonempty (hTconn 3).isPreconnected
      (hTconn 3).nonempty hsepS
  have hne02 : π 0 ≠ π 2 := fun e => absurd (π.injective e) (by decide)
  have hne10 : π 1 ≠ π 0 := fun e => absurd (π.injective e) (by decide)
  have hne12 : π 1 ≠ π 2 := fun e => absurd (π.injective e) (by decide)
  have hne30 : π 3 ≠ π 0 := fun e => absurd (π.injective e) (by decide)
  have hne32 : π 3 ≠ π 2 := fun e => absurd (π.injective e) (by decide)
  obtain ⟨c, hc, hc0, hc2⟩ :=
    exists_isPLHomeomorphOn_union (hTball 0).isPolyhedron (hTball 2).isPolyhedron (ht 0) (ht 2)
      (by
        rw [hTT 0 2 (by decide)]
        intro x hx
        simp only [mem_insert_iff, mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · rw [htzero 0, htzero 2]
        · rw [htone 0, htone 2])
      (by
        rw [hTT 0 2 (by decide), hTT' (π 0) (π 2) hne02, ← himagepair 0]
        exact fun y hy => hy)
  have hcC : c '' (T 0 ∪ T 2) = T' (π 0) ∪ T' (π 2) := hc.image_eq
  have hcimage : c '' ({y₀, y₁} : Set E) = ({y₀', y₁'} : Set F) := by
    rw [image_pair, hc0 (hzeromem 0), hc0 (honemem 0), htzero 0, htone 0]
  have hC' : IsPLSphere 1 (T' (π 0) ∪ T' (π 2)) := hC.of_isPLHomeomorphOn hc
  have hC'S : T' (π 0) ∪ T' (π 2) ⊆ S' := union_subset (hTS' (π 0)) (hTS' (π 2))
  have hT'1C : T' (π 1) ∩ (T' (π 0) ∪ T' (π 2)) = {y₀', y₁'} := by
    rw [inter_union_distrib_left, hTT' (π 1) (π 0) hne10, hTT' (π 1) (π 2) hne12, union_self]
  have hT'3C : T' (π 3) ∩ (T' (π 0) ∪ T' (π 2)) = {y₀', y₁'} := by
    rw [inter_union_distrib_left, hTT' (π 3) (π 0) hne30, hTT' (π 3) (π 2) hne32, union_self]
  have hsepT : ∀ U ⊆ S' \ (T' (π 0) ∪ T' (π 2)), IsPreconnected U →
      (U ∩ T' (π 1)).Nonempty → (U ∩ T' (π 3)).Nonempty → False := by
    have hπ2 : π 2 = π 0 + 2 := by
      have h := hπ 0
      rwa [(by decide : (0 : Fin 4) + 2 = 2)] at h
    have hπ3 : π 3 = π 1 + 2 := by
      have h := hπ 1
      rwa [(by decide : (1 : Fin 4) + 2 = 3)] at h
    have h := hsep' (π 0)
    rw [← hπ2] at h
    rcases (by decide : ∀ x z : Fin 4, x ≠ z → x ≠ z + 2 → x = z + 1 ∨ x = z + 3)
        (π 1) (π 0) hne10 (fun e => hne12 (e.trans hπ2.symm)) with h1 | h1
    · have h3 : π 3 = π 0 + 3 := by
        rw [hπ3, h1, (by decide : ∀ z : Fin 4, z + 1 + 2 = z + 3)]
      rw [← h1, ← h3] at h
      exact h
    · have h3 : π 3 = π 0 + 1 := by
        rw [hπ3, h1, (by decide : ∀ z : Fin 4, z + 3 + 2 = z + 1)]
      rw [← h1, ← h3] at h
      exact fun U hU hUconn hfirst hsecond => h U hU hUconn hsecond hfirst
  obtain ⟨D'₀, D'₁, r'₀, r'₁, hr'₀, hr'₁, hb'₀, hb'₁, hcover', hinter', hT'1D, hT'3D⟩ :=
    exists_isPLBall_pair_separating_of_isPLSphere_two hS' hC' hC'S (hTS' (π 1)) (hTS' (π 3))
      hT'1C hT'3C (hT'conn 1).isPreconnected (hT'conn 1).nonempty (hT'conn 3).isPreconnected
      (hT'conn 3).nonempty hsepT
  have hCpoly : IsPolyhedron (T 0 ∪ T 2) := hC.isPolyhedron
  have hhalf : ∀ (k : Fin 4) (D : Set E) (D' : Set F) (r : (Fin 3 → ℝ) → E)
      (r' : (Fin 3 → ℝ) → F), T k ∩ (T 0 ∪ T 2) = {y₀, y₁} →
      T' (π k) ∩ (T' (π 0) ∪ T' (π 2)) = {y₀', y₁'} →
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → r '' stdSimplexBoundary 2 = T 0 ∪ T 2 →
      IsPLHomeomorphOn r' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' →
      r' '' stdSimplexBoundary 2 = T' (π 0) ∪ T' (π 2) → T k ⊆ D → T' (π k) ⊆ D' →
      ∃ G : E → F, IsPLHomeomorphOn G D D' ∧ EqOn G c (T 0 ∪ T 2) ∧ EqOn G (t k) (T k) := by
    intro k D D' r r' hkC hk'C hr hrb hr' hr'b hkD hk'D
    obtain ⟨f, hf, hfc, hft⟩ :=
      exists_isPLHomeomorphOn_union hCpoly (hTball k).isPolyhedron hc (ht k)
        (by
          rw [inter_comm (T 0 ∪ T 2) (T k), hkC]
          intro x hx
          simp only [mem_insert_iff, mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · rw [hc0 (hzeromem 0), htzero 0, htzero k]
          · rw [hc0 (honemem 0), htone 0, htone k])
        (by
          rw [inter_comm (T 0 ∪ T 2) (T k), hkC,
            inter_comm (T' (π 0) ∪ T' (π 2)) (T' (π k)), hk'C, ← hcimage]
          exact fun y hy => hy)
    obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_eqOn_disk_crosscut hr hrb hr' hr'b (hγ k)
      hkD (by rw [hkC, hγzero k, hγone k]) hk'D hf (hfc.image_eq.trans hcC)
      (hft.image_eq.trans (ht k).image_eq)
    exact ⟨G, hG, fun x hx => (hGf (mem_union_left _ hx)).trans (hfc hx),
      fun x hx => (hGf (mem_union_right _ hx)).trans (hft hx)⟩
  obtain ⟨G₀, hG₀, hG₀c, hG₀t⟩ :=
    hhalf 1 D₀ D'₀ r₀ r'₀ hT1C hT'1C hr₀ hb₀ hr'₀ hb'₀ hT1D hT'1D
  obtain ⟨G₁, hG₁, hG₁c, hG₁t⟩ :=
    hhalf 3 D₁ D'₁ r₁ r'₁ hT3C hT'3C hr₁ hb₁ hr'₁ hb'₁ hT3D hT'3D
  have hCD₀ : T 0 ∪ T 2 ⊆ D₀ := fun x hx => (hinter.symm.subset hx).1
  have hD₀ : IsPLBall 2 D₀ := ⟨r₀, hr₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  obtain ⟨g, hg, hgG₀, hgG₁⟩ :=
    exists_isPLHomeomorphOn_union hD₀.isPolyhedron hD₁.isPolyhedron hG₀ hG₁
      (by
        rw [hinter]
        exact fun x hx => (hG₀c hx).trans (hG₁c hx).symm)
      (by
        rw [hinter, hinter', ← hcC, ← hG₀c.image_eq]
        exact fun y hy => hy)
  rw [hcover, hcover'] at hg
  have hgc : EqOn g c (T 0 ∪ T 2) := fun x hx => (hgG₀ (hCD₀ hx)).trans (hG₀c hx)
  have heq0 : EqOn g (t 0) (T 0) := fun x hx => (hgc (mem_union_left _ hx)).trans (hc0 hx)
  have heq2 : EqOn g (t 2) (T 2) := fun x hx => (hgc (mem_union_right _ hx)).trans (hc2 hx)
  have heq1 : EqOn g (t 1) (T 1) := fun x hx => (hgG₀ (hT1D hx)).trans (hG₀t hx)
  have heq3 : EqOn g (t 3) (T 3) := fun x hx => (hgG₁ (hT3D hx)).trans (hG₁t hx)
  have heq : ∀ i, EqOn g (t i) (T i) := by
    intro i
    rcases hall i with rfl | rfl | rfl | rfl
    · exact heq0
    · exact heq1
    · exact heq2
    · exact heq3
  refine ⟨g, hg, ?_, ?_, heq, fun i => (heq i).image_eq.trans (ht i).image_eq⟩
  · rw [heq0 (hzeromem 0), htzero 0]
  · rw [heq0 (honemem 0), htone 0]

theorem exists_isPLHomeomorphOn_fourArcSphere_of_isPLHomeomorphOn_Icc {S : Set E} {S' : Set F}
    {y₀ y₁ : E} {y₀' y₁' : F} {T : Fin 4 → Set E} {T' : Fin 4 → Set F} {γ : Fin 4 → ℝ → E}
    {γ' : Fin 4 → ℝ → F} (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i))
    (hγzero : ∀ i, γ i 0 = y₀) (hγone : ∀ i, γ i 1 = y₁)
    (hγ' : ∀ i, IsPLHomeomorphOn (γ' i) (Icc 0 1) (T' i))
    (hγ'zero : ∀ i, γ' i 0 = y₀') (hγ'one : ∀ i, γ' i 1 = y₁')
    (hTS : ∀ i, T i ⊆ S) (hTS' : ∀ i, T' i ⊆ S')
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {y₀, y₁})
    (hTT' : ∀ i j, i ≠ j → T' i ∩ T' j = {y₀', y₁'})
    (hsep : ∀ i : Fin 4, ∀ U ⊆ S \ (T i ∪ T (i + 2)), IsPreconnected U →
      (U ∩ T (i + 1)).Nonempty → (U ∩ T (i + 3)).Nonempty → False)
    (hsep' : ∀ i : Fin 4, ∀ U ⊆ S' \ (T' i ∪ T' (i + 2)), IsPreconnected U →
      (U ∩ T' (i + 1)).Nonempty → (U ∩ T' (i + 3)).Nonempty → False)
    {π : Equiv.Perm (Fin 4)} (hπ : ∀ i, π (i + 2) = π i + 2) :
    ∃ g : E → F, IsPLHomeomorphOn g S S' ∧ g y₀ = y₀' ∧ g y₁ = y₁' ∧
      ∀ i, g '' T i = T' (π i) := by
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hmem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  obtain ⟨g, hg, hg0, hg1, -, himage⟩ := exists_isPLHomeomorphOn_of_fourArcSphere hS hS' hγ
    hγzero hγone hTS hTS' hTT hTT' hsep hsep' hπ
    (t := fun i => γ' (π i) ∘ Function.invFunOn (γ i) (Icc 0 1))
    (fun i => (hγ i).symm.trans (hγ' (π i)))
    (fun i => by
      change γ' (π i) (Function.invFunOn (γ i) (Icc 0 1) y₀) = y₀'
      rw [← hγzero i, (hγ i).bijOn.invOn_invFunOn.1 hmem0, hγ'zero (π i)])
    (fun i => by
      change γ' (π i) (Function.invFunOn (γ i) (Icc 0 1) y₁) = y₁'
      rw [← hγone i, (hγ i).bijOn.invOn_invFunOn.1 hmem1, hγ'one (π i)])
  exact ⟨g, hg, hg0, hg1, himage⟩

end DifferentialGeometry.Topology.PiecewiseLinear
