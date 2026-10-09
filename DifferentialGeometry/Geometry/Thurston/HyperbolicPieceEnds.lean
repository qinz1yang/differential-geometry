import DifferentialGeometry.Topology.ThreeManifold.Geometrization.HyperbolicPieceGroupWords
import DifferentialGeometry.Topology.Connected.BallComplement
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.GraphOfGroupsIndecomposable
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.LocallyFinite

/-!
# A relative ends argument for freely indecomposable groups

Tier T4b of lane BHD (`handoffs/20261004-design-bhd-relative-hyperbolic-pieces.md`, §1, T4).
Let a group `Γ` act properly discontinuously by homeomorphisms on a proper real normed space `E`
of dimension at least two (so `E` is one-ended). Suppose `E` is covered by the translates of a
nonempty compact set `F` together with the translates of finitely many closed "cusp" sets `Z k`,
where translates of cusp sets meet only when they coincide, each point has a neighbourhood meeting
at most one translate of each `Z k`, the stabiliser `Stab k` of `Z k` is freely indecomposable and
not cyclic, and only finitely many `Stab k`-cosets of translates of `F` meet `Z k`. Then `Γ` is
freely indecomposable (`freelyIndecomposable_of_cuspedAction`), if `Γ` is infinite.

Proof. Given a splitting `Γ ≃ A ∗ B` with both factors nontrivial, Kurosh puts each `Stab k` in a
conjugate of a factor (`exists_le_conjugateSubgroup_of_freelyIndecomposable`). Sort translates of
`F` by the first letter of their label (`GC.Group.FirstLetter`), and translates of `Z k` by the
first letter of their label times the conjugator, adapted to the factor of `Stab k`, which makes
the sorting of cusps well defined. The two unions `U`, `V` are closed and cover `E`; they meet only
in finitely many translates of `F`, because the first letter is almost invariant under right
multiplication. Since the complement of a large ball is connected, one of `U`, `V` is bounded
(`isBounded_or_isBounded_of_union_eq_univ`), so one side contains finitely many labels, and then
the free product is finite (`finite_of_finite_setOf_firstIdx_ne`), a contradiction.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Monoid.CoprodI GC.Group.FirstLetter
open GraphCoveringTheory.Kurosh
open scoped Pointwise

namespace GC.Geometry.HyperbolicPiece

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBounded_or_isBounded_of_union_eq_univ (hd : 1 < Module.rank ℝ E) {U V K : Set E}
    (hU : IsClosed U) (hV : IsClosed V) (hUV : U ∪ V = univ) (hK : IsCompact K)
    (hint : U ∩ V ⊆ K) : Bornology.IsBounded U ∨ Bornology.IsBounded V := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hO := (DifferentialGeometry.Topology.isPathConnected_compl_closedBall hd 0 R).isConnected
  have hsub : (closedBall (0 : E) R)ᶜ ⊆ U ∪ V := by
    rw [hUV]
    exact subset_univ _
  have hdis : (closedBall (0 : E) R)ᶜ ∩ (U ∩ V) = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun hy hyU hyV => hy (hR (hint ⟨hyU, hyV⟩))
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hO.isPreconnected U V hU hV hsub hdis
    with h | h
  · right
    refine (isBounded_closedBall (x := (0 : E)) (r := R)).subset fun v hv => ?_
    by_contra hvb
    exact hvb (hR (hint ⟨h hvb, hv⟩))
  · left
    refine (isBounded_closedBall (x := (0 : E)) (r := R)).subset fun v hv => ?_
    by_contra hvb
    exact hvb (hR (hint ⟨hv, h hvb⟩))

variable {Γ : Type*} [Group Γ] [MulAction Γ E] [ContinuousConstSMul Γ E]
  [ProperlyDiscontinuousSMul Γ E]

omit [NormedSpace ℝ E] [ContinuousConstSMul Γ E] in
theorem finite_setOf_smul_inter_nonempty [ProperSpace E] {F L : Set E} (hF : IsCompact F)
    (hL : IsCompact L) : {γ : Γ | (γ • F ∩ L).Nonempty}.Finite :=
  ProperlyDiscontinuousSMul.finite_disjoint_inter_image hF hL

omit [NormedSpace ℝ E] [ContinuousConstSMul Γ E] in
theorem locallyFinite_smul [ProperSpace E] {F : Set E} (hF : IsCompact F) :
    LocallyFinite fun γ : Γ => γ • F := by
  intro y
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds y
  exact ⟨K, hK, finite_setOf_smul_inter_nonempty hF hKc⟩

omit [NormedSpace ℝ E] in
theorem isClosed_biUnion_smul [ProperSpace E] {F : Set E} (hF : IsCompact F) (S : Set Γ) :
    IsClosed (⋃ γ ∈ S, γ • F) := by
  have h : LocallyFinite fun γ : Γ => ⋃ (_ : γ ∈ S), γ • F :=
    (locallyFinite_smul hF).subset fun γ => iUnion_subset fun _ => subset_rfl
  have hc : ∀ γ : Γ, IsClosed (⋃ (_ : γ ∈ S), γ • F) := by
    intro γ
    by_cases hγ : γ ∈ S
    · simp only [hγ, iUnion_true]
      exact (hF.smul γ).isClosed
    · simp only [hγ, iUnion_false, isClosed_empty]
  exact h.isClosed_iUnion hc

variable {κ : Type*} [Finite κ]

omit [NormedSpace ℝ E] [ProperlyDiscontinuousSMul Γ E] in
theorem isClosed_biUnion_cusp (Z : κ → Set E) (hZ : ∀ k, IsClosed (Z k))
    (Stab : κ → Subgroup Γ) (hstabZ : ∀ k, ∀ π ∈ Stab k, π • Z k = Z k)
    (hlocfin : ∀ y : E, ∃ V ∈ 𝓝 y, ∀ k (γ γ' : Γ), (γ • Z k ∩ V).Nonempty →
      (γ' • Z k ∩ V).Nonempty → γ⁻¹ * γ' ∈ Stab k)
    (T : Set (κ × Γ)) : IsClosed (⋃ q ∈ T, q.2 • Z q.1) := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨V, hV, hloc⟩ := hlocfin y
  let C : κ → Set E := fun k =>
    if h : ∃ γ : Γ, (k, γ) ∈ T ∧ (γ • Z k ∩ V).Nonempty then h.choose • Z k else ∅
  have hC : ∀ k, (C k)ᶜ ∈ 𝓝 y := by
    intro k
    apply IsOpen.mem_nhds
    · rw [isOpen_compl_iff]
      simp only [C]
      split_ifs
      · exact (hZ k).smul _
      · exact isClosed_empty
    · simp only [C]
      split_ifs with h
      · intro hyC
        exact hy (mem_biUnion h.choose_spec.1 hyC)
      · exact notMem_empty y
  have hW : V ∩ ⋂ k, (C k)ᶜ ∈ 𝓝 y := inter_mem hV (iInter_mem.mpr hC)
  refine mem_of_superset hW ?_
  rintro z ⟨hzV, hzC⟩ hz
  obtain ⟨q, hqT, hzq⟩ := mem_iUnion₂.mp hz
  have hex : ∃ γ : Γ, (q.1, γ) ∈ T ∧ (γ • Z q.1 ∩ V).Nonempty := ⟨q.2, hqT, z, hzq, hzV⟩
  have hCq : C q.1 = hex.choose • Z q.1 := by
    simp only [C, hex, ↓reduceDIte]
  have hst := hloc q.1 hex.choose q.2 hex.choose_spec.2 ⟨z, hzq, hzV⟩
  apply mem_iInter.mp hzC q.1
  rw [hCq]
  have heq : q.2 • Z q.1 = hex.choose • Z q.1 := by
    have h := congrArg (fun A => hex.choose • A) (hstabZ q.1 _ hst)
    simp only [smul_smul, mul_inv_cancel_left] at h
    exact h
  rw [← heq]
  exact hzq

def side (i : Bool) (o : Option Bool) : Prop :=
  if i then o ≠ some false else o = some true

theorem side_none_iff (i : Bool) : side i none ↔ side i (some i) := by
  cases i <;> simp [side]

variable {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]

theorem finite_side_cross (i : Bool) (t : Monoid.CoprodI M) :
    {w : Monoid.CoprodI M | ¬ (side true (firstIdx (w * t)) ↔ side i (firstIdx w))}.Finite := by
  cases i
  · refine ((finite_setOf_firstIdx_mul_ne (side true) t).union
      (finite_singleton (1 : Monoid.CoprodI M))).subset ?_
    intro w hw
    by_cases h1 : w = 1
    · exact Or.inr h1
    left
    intro hiff
    apply hw
    refine hiff.trans ?_
    have hne : firstIdx w ≠ none := fun h => h1 ((firstIdx_eq_none_iff w).mp h)
    rcases ho : firstIdx w with _ | (_ | _)
    · exact absurd ho hne
    · simp [side]
    · simp [side]
  · exact (finite_setOf_firstIdx_mul_ne (side true) t).subset fun w hw h => hw h

variable [ProperSpace E]

omit [∀ i, DecidableEq (M i)] in
theorem false_of_cuspPartition (hd : 1 < Module.rank ℝ E) [Infinite Γ]
    (ε : Γ ≃* Monoid.CoprodI M) (a : M true) (ha : a ≠ 1) (b : M false) (hb : b ≠ 1)
    {F : Set E} (hF : IsCompact F) (hFne : F.Nonempty)
    (Z : κ → Set E) (hZ : ∀ k, IsClosed (Z k)) (Stab : κ → Subgroup Γ)
    (hstabZ : ∀ k, ∀ π ∈ Stab k, π • Z k = Z k)
    (hcover : ∀ y : E, (∃ γ : Γ, y ∈ γ • F) ∨ ∃ k, ∃ γ : Γ, y ∈ γ • Z k)
    (hdisj : ∀ k k' (γ γ' : Γ), (γ • Z k ∩ γ' • Z k').Nonempty → k = k' ∧ γ⁻¹ * γ' ∈ Stab k)
    (hlocfin : ∀ y : E, ∃ V ∈ 𝓝 y, ∀ k (γ γ' : Γ), (γ • Z k ∩ V).Nonempty →
      (γ' • Z k ∩ V).Nonempty → γ⁻¹ * γ' ∈ Stab k)
    (htype : ∀ k, ∃ H : Set Γ, H.Finite ∧ ∀ γ : Γ, (γ • F ∩ Z k).Nonempty →
      ∃ π ∈ Stab k, ∃ η ∈ H, γ = π * η)
    (idx : κ → Bool) (c : κ → Monoid.CoprodI M)
    (hstab : ∀ k, ∀ π ∈ Stab k, ∃ x : M (idx k), (c k)⁻¹ * ε π * c k = of x) : False := by
  classical
  let χ : Γ → Prop := fun γ => side true (firstIdx (ε γ))
  let ψ : κ → Γ → Prop := fun k γ => side (idx k) (firstIdx (ε γ * c k))
  have hψ : ∀ k (γ π : Γ), π ∈ Stab k → (ψ k (γ * π) ↔ ψ k γ) := by
    intro k γ π hπ
    obtain ⟨x, hx⟩ := hstab k π hπ
    have he : ε (γ * π) * c k = ε γ * c k * of x := by
      rw [← hx, map_mul]
      group
    simp only [ψ, he]
    exact firstIdx_mul_of_iff (side (idx k)) (side_none_iff (idx k)) _ x
  let U : Set E := (⋃ γ ∈ {γ | χ γ}, γ • F) ∪ ⋃ q ∈ {q : κ × Γ | ψ q.1 q.2}, q.2 • Z q.1
  let V : Set E := (⋃ γ ∈ {γ | ¬ χ γ}, γ • F) ∪ ⋃ q ∈ {q : κ × Γ | ¬ ψ q.1 q.2}, q.2 • Z q.1
  have hUc : IsClosed U := (isClosed_biUnion_smul hF _).union
    (isClosed_biUnion_cusp Z hZ Stab hstabZ hlocfin _)
  have hVc : IsClosed V := (isClosed_biUnion_smul hF _).union
    (isClosed_biUnion_cusp Z hZ Stab hstabZ hlocfin _)
  have hUV : U ∪ V = univ := by
    refine eq_univ_of_forall fun y => ?_
    rcases hcover y with ⟨γ, hy⟩ | ⟨k, γ, hy⟩
    · by_cases hχ : χ γ
      · exact Or.inl (Or.inl (mem_biUnion hχ hy))
      · exact Or.inr (Or.inl (mem_biUnion hχ hy))
    · by_cases hq : ψ k γ
      · exact Or.inl (Or.inr (mem_biUnion (x := (k, γ)) hq hy))
      · exact Or.inr (Or.inr (mem_biUnion (x := (k, γ)) hq hy))
  let S : Set Γ := {s | (s • F ∩ F).Nonempty}
  have hS : S.Finite := finite_setOf_smul_inter_nonempty hF hF
  let X₁ : Set Γ := ⋃ s ∈ S, {γ | ¬ (χ (γ * s) ↔ χ γ)}
  have hX₁ : X₁.Finite := by
    refine hS.biUnion fun s _ => ?_
    have h := (finite_setOf_firstIdx_mul_ne (side true) (ε s)).preimage
      (ε.injective.injOn (s := ε ⁻¹' _))
    refine h.subset fun γ hγ => ?_
    simpa only [χ, mem_ofPred_eq, mem_preimage, map_mul] using hγ
  choose H hHfin hH using htype
  let X₂ : Set Γ := ⋃ k, ⋃ η ∈ H k, ε.symm ''
    ((fun w => w * ((c k)⁻¹ * ε η)) ''
      {w | ¬ (side true (firstIdx (w * ((c k)⁻¹ * ε η))) ↔ side (idx k) (firstIdx w))})
  have hX₂ : X₂.Finite :=
    finite_iUnion fun k => (hHfin k).biUnion fun η _ =>
      ((finite_side_cross (idx k) _).image _).image _
  let K : Set E := ⋃ γ ∈ X₁ ∪ X₂, γ • F
  have hK : IsCompact K := (hX₁.union hX₂).isCompact_biUnion fun γ _ => hF.smul γ
  have hcross : ∀ (k : κ) (γ γ' : Γ) (y : E), y ∈ γ • F → y ∈ γ' • Z k →
      ¬ (χ γ ↔ ψ k γ') → γ ∈ X₂ := by
    intro k γ γ' y hyF hyZ hne
    have hmeet : ((γ'⁻¹ * γ) • F ∩ Z k).Nonempty := by
      refine ⟨γ'⁻¹ • y, ?_, ?_⟩
      · rw [mul_smul]
        exact smul_mem_smul_set hyF
      · obtain ⟨z, hz, rfl⟩ := hyZ
        rw [inv_smul_smul]
        exact hz
    obtain ⟨π, hπ, η, hη, heq⟩ := hH k _ hmeet
    have hγ : γ = γ' * π * η := by
      rw [mul_assoc, ← heq, mul_inv_cancel_left]
    let w := ε (γ' * π) * c k
    refine mem_iUnion.mpr ⟨k, mem_iUnion₂.mpr ⟨η, hη, ε γ, ?_, ε.symm_apply_apply γ⟩⟩
    refine ⟨w, ?_, ?_⟩
    · change ¬ (side true (firstIdx (w * ((c k)⁻¹ * ε η))) ↔ side (idx k) (firstIdx w))
      have hw : w * ((c k)⁻¹ * ε η) = ε γ := by
        simp only [w, hγ, map_mul]
        group
      rw [hw]
      have hψ' : ψ k (γ' * π) ↔ ψ k γ' := hψ k γ' π hπ
      intro hiff
      exact hne (hiff.trans hψ')
    · simp only [w, hγ, map_mul]
      group
  have hint : U ∩ V ⊆ K := by
    rintro y ⟨hyU, hyV⟩
    rcases hyU with hyU | hyU <;> rcases hyV with hyV | hyV
    · obtain ⟨γ, hχ, hy⟩ := mem_iUnion₂.mp hyU
      obtain ⟨γ', hχ', hy'⟩ := mem_iUnion₂.mp hyV
      refine mem_biUnion (Or.inl ?_) hy
      refine mem_iUnion₂.mpr ⟨γ⁻¹ * γ', ?_, ?_⟩
      · refine ⟨γ⁻¹ • y, ?_, ?_⟩
        · rw [mul_smul]
          exact smul_mem_smul_set hy'
        · obtain ⟨z, hz, rfl⟩ := hy
          rw [inv_smul_smul]
          exact hz
      · change ¬ (χ (γ * (γ⁻¹ * γ')) ↔ χ γ)
        rw [mul_inv_cancel_left]
        exact fun h => hχ' (h.mpr hχ)
    · obtain ⟨γ, hχ, hy⟩ := mem_iUnion₂.mp hyU
      obtain ⟨q, hq, hy'⟩ := mem_iUnion₂.mp hyV
      refine mem_biUnion (Or.inr (hcross q.1 γ q.2 y hy hy' fun h => hq (h.mp hχ))) hy
    · obtain ⟨q, hq, hy⟩ := mem_iUnion₂.mp hyU
      obtain ⟨γ, hχ, hy'⟩ := mem_iUnion₂.mp hyV
      refine mem_biUnion (Or.inr (hcross q.1 γ q.2 y hy' hy fun h => hχ (h.mpr hq))) hy'
    · obtain ⟨q, hq, hy⟩ := mem_iUnion₂.mp hyU
      obtain ⟨q', hq', hy'⟩ := mem_iUnion₂.mp hyV
      obtain ⟨hk, hst⟩ := hdisj q.1 q'.1 q.2 q'.2 ⟨y, hy, hy'⟩
      exfalso
      apply hq'
      have h := (hψ q.1 q.2 _ hst).mpr hq
      rw [mul_inv_cancel_left] at h
      change ψ q'.1 q'.2
      rw [← hk]
      exact h
  have hfin : ∀ (P : Γ → Prop) (W : Set E), Bornology.IsBounded W →
      (⋃ γ ∈ {γ | P γ}, γ • F) ⊆ W → {γ | P γ}.Finite := by
    intro P W hW hsub
    obtain ⟨R, hR⟩ := hW.subset_closedBall 0
    refine (finite_setOf_smul_inter_nonempty (Γ := Γ) hF (isCompact_closedBall (0 : E) R)).subset ?_
    intro γ hγ
    obtain ⟨f, hf⟩ := hFne
    exact ⟨γ • f, smul_mem_smul_set hf, hR (hsub (mem_biUnion hγ (smul_mem_smul_set hf)))⟩
  have hcop : Finite (Monoid.CoprodI M) := by
    apply finite_of_finite_setOf_firstIdx_ne a ha b hb
    rcases isBounded_or_isBounded_of_union_eq_univ hd hUc hVc hUV hK hint with h | h
    · left
      have h1 := hfin χ U h subset_union_left
      refine (h1.image ε).subset fun w hw => ⟨ε.symm w, ?_, ε.apply_symm_apply w⟩
      change side true (firstIdx (ε (ε.symm w)))
      rw [ε.apply_symm_apply]
      simpa [side] using hw
    · right
      have h1 := hfin (fun γ => ¬ χ γ) V h subset_union_left
      refine (h1.image ε).subset fun w hw => ⟨ε.symm w, ?_, ε.apply_symm_apply w⟩
      change ¬ side true (firstIdx (ε (ε.symm w)))
      rw [ε.apply_symm_apply]
      simpa [side] using hw
  have : Finite Γ := Finite.of_equiv _ ε.symm.toEquiv
  exact not_finite Γ

omit [∀ i, Group (M i)] [∀ i, DecidableEq (M i)] in
theorem freelyIndecomposable_of_cuspedAction (hd : 1 < Module.rank ℝ E) [Infinite Γ]
    {F : Set E} (hF : IsCompact F) (hFne : F.Nonempty)
    (Z : κ → Set E) (hZ : ∀ k, IsClosed (Z k)) (Stab : κ → Subgroup Γ)
    (hstabZ : ∀ k, ∀ π ∈ Stab k, π • Z k = Z k)
    (hcover : ∀ y : E, (∃ γ : Γ, y ∈ γ • F) ∨ ∃ k, ∃ γ : Γ, y ∈ γ • Z k)
    (hdisj : ∀ k k' (γ γ' : Γ), (γ • Z k ∩ γ' • Z k').Nonempty → k = k' ∧ γ⁻¹ * γ' ∈ Stab k)
    (hlocfin : ∀ y : E, ∃ V ∈ 𝓝 y, ∀ k (γ γ' : Γ), (γ • Z k ∩ V).Nonempty →
      (γ' • Z k ∩ V).Nonempty → γ⁻¹ * γ' ∈ Stab k)
    (htype : ∀ k, ∃ H : Set Γ, H.Finite ∧ ∀ γ : Γ, (γ • F ∩ Z k).Nonempty →
      ∃ π ∈ Stab k, ∃ η ∈ H, γ = π * η)
    (hstab : ∀ k, GC.Group.FreelyIndecomposable (Stab k) ∧ ¬ IsCyclic (Stab k)) :
    GC.Group.FreelyIndecomposable Γ := by
  classical
  intro A B _ _ he
  obtain ⟨e⟩ := he
  by_contra hAB
  rw [not_or, not_subsingleton_iff_nontrivial, not_subsingleton_iff_nontrivial] at hAB
  obtain ⟨hA, hB⟩ := hAB
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  let ε : Γ ≃* Monoid.CoprodI (DifferentialGeometry.Algebra.Group.boolCoprodFamily A B) :=
    e.trans (DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod A B).symm
  have hkur : ∀ k, ∃ (i : Bool) (g : Monoid.CoprodI
      (DifferentialGeometry.Algebra.Group.boolCoprodFamily A B)),
      (Stab k).map ε.toMonoidHom ≤ conjugateSubgroup
        (MonoidHom.range (factorInclusion _ i)) g := by
    intro k
    have eS : Stab k ≃* (Stab k).map ε.toMonoidHom :=
      (Stab k).equivMapOfInjective ε.toMonoidHom ε.injective
    exact GC.Group.exists_le_conjugateSubgroup_of_freelyIndecomposable _ _
      ((hstab k).1.of_mulEquiv eS)
      fun hc => (hstab k).2 (eS.isCyclic.mpr hc)
  choose idx c hc using hkur
  refine false_of_cuspPartition hd ε (ULift.up b) (fun h => hb (congrArg ULift.down h))
    (ULift.up a) (fun h => ha (congrArg ULift.down h)) hF hFne Z hZ Stab hstabZ hcover hdisj
    hlocfin htype idx c fun k π hπ => ?_
  have hmem := hc k (Subgroup.mem_map_of_mem ε.toMonoidHom hπ)
  rw [mem_conjugateSubgroup_iff] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, hx.symm⟩

end GC.Geometry.HyperbolicPiece
