import DifferentialGeometry.Topology.PlanarJordan.BoundaryFan
import DifferentialGeometry.Topology.PlanarJordan.VertexArcs

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_homeomorph_extending_two_vertex_arcs
    {C A B A' B' : Set Plane} {v w p q : Plane}
    (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C)
    (hA : IsArcBetween A v p) (hB : IsArcBetween B v q)
    (hA' : IsArcBetween A' w p) (hB' : IsArcBetween B' w q)
    (hmeet : ∀ x ∈ A, x ∈ B → x = v)
    (hmeet' : ∀ x ∈ A', x ∈ B' → x = w)
    (hAI : A \ {p} ⊆ inside C) (hBI : B \ {q} ⊆ inside C)
    (hAI' : A' \ {p} ⊆ inside C) (hBI' : B' \ {q} ⊆ inside C)
    (f : ArcHomeo A A' v p w p) (g : ArcHomeo B B' v q w q) :
    ∃ e : Plane ≃ₜ Plane, EqOn e f.toFun A ∧ EqOn e g.toFun B ∧
      EqOn e id (inside C)ᶜ ∧ ∀ x, dist (e x) x ≤ Metric.diam (C ∪ inside C) := by
  classical
  have hagree : EqOn f.toFun g.toFun (A ∩ B) := by
    intro x hx
    rw [hmeet x hx.1 hx.2, f.map_left, g.map_left]
  have hsurj : SurjOn f.toFun (A ∩ B) (A' ∩ B') := by
    intro y hy
    rw [hmeet' y hy.1 hy.2]
    exact ⟨v, ⟨hA.left_mem, hB.left_mem⟩, f.map_left⟩
  obtain ⟨d, hdA, hdB⟩ := Homeomorph.exists_gluing_of_isCompact
    hA.isArc.isCompact hB.isArc.isCompact f.continuousOn_toFun g.continuousOn_toFun
    ⟨f.mapsTo, f.injOn, fun _ hy => f.image_eq.symm ▸ hy⟩
    ⟨g.mapsTo, g.injOn, fun _ hy => g.image_eq.symm ▸ hy⟩ hagree hsurj
  let φ : Plane → Plane := fun x => if hx : x ∈ A ∪ B then (d ⟨x, hx⟩ : Plane) else x
  let ψ : Plane → Plane := fun y => if hy : y ∈ A' ∪ B' then (d.symm ⟨y, hy⟩ : Plane) else y
  have hφ (x : Plane) (hx : x ∈ A ∪ B) : φ x = (d ⟨x, hx⟩ : Plane) := by
    simp only [φ, dif_pos hx]
  have hψ (y : Plane) (hy : y ∈ A' ∪ B') : ψ y = (d.symm ⟨y, hy⟩ : Plane) := by
    simp only [ψ, dif_pos hy]
  have hφcont : ContinuousOn φ (A ∪ B) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp d.continuous).congr (fun x => (hφ x x.property).symm)
  have hψcont : ContinuousOn ψ (A' ∪ B') := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp d.symm.continuous).congr
      (fun y => (hψ y y.property).symm)
  have hφimage : φ '' (A ∪ B) = A' ∪ B' := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hφ x hx]
      exact (d ⟨x, hx⟩).property
    · intro y hy
      refine ⟨d.symm ⟨y, hy⟩, (d.symm ⟨y, hy⟩).property, ?_⟩
      rw [hφ _ (d.symm ⟨y, hy⟩).property]
      exact congrArg Subtype.val (d.apply_symm_apply ⟨y, hy⟩)
  let F : ArcHomeo (A ∪ B) (A' ∪ B') p q p q := {
    toFun := φ
    invFun := ψ
    continuousOn_toFun := hφcont
    continuousOn_invFun := hψcont
    leftInvOn := by
      intro x hx
      rw [hφ x hx, hψ _ (d ⟨x, hx⟩).property]
      exact congrArg Subtype.val (d.symm_apply_apply ⟨x, hx⟩)
    rightInvOn := by
      intro y hy
      rw [hψ y hy, hφ _ (d.symm ⟨y, hy⟩).property]
      exact congrArg Subtype.val (d.apply_symm_apply ⟨y, hy⟩)
    image_eq := hφimage
    map_left := (hφ p (Or.inl hA.right_mem)).trans ((hdA p hA.right_mem).trans f.map_right)
    map_right := (hφ q (Or.inr hB.right_mem)).trans ((hdB q hB.right_mem).trans g.map_right) }
  have hP := hA.reverse.concatenate hB hmeet
  have hQ := hA'.reverse.concatenate hB' hmeet'
  have hPI : (A ∪ B) \ {p, q} ⊆ inside C := by
    rintro x ⟨hx, hends⟩
    rcases hx with hx | hx
    · exact hAI ⟨hx, fun hxp => hends (Or.inl hxp)⟩
    · exact hBI ⟨hx, fun hxq => hends (Or.inr hxq)⟩
  have hQI : (A' ∪ B') \ {p, q} ⊆ inside C := by
    rintro x ⟨hx, hends⟩
    rcases hx with hx | hx
    · exact hAI' ⟨hx, fun hxp => hends (Or.inl hxp)⟩
    · exact hBI' ⟨hx, fun hxq => hends (Or.inr hxq)⟩
  obtain ⟨e, he, hfix, hdist⟩ :=
    exists_homeomorph_extending_crosscut hC hP hQ hp hq hPI hQI F
  refine ⟨e, ?_, ?_, hfix, hdist⟩
  · intro x hx
    exact (he (Or.inl hx)).trans ((hφ x (Or.inl hx)).trans (hdA x hx))
  · intro x hx
    exact (he (Or.inr hx)).trans ((hφ x (Or.inr hx)).trans (hdB x hx))

theorem exists_homeomorph_image_two_vertex_arcs
    {C A B A' B' : Set Plane} {v w p q : Plane}
    (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C)
    (hA : IsArcBetween A v p) (hB : IsArcBetween B v q)
    (hA' : IsArcBetween A' w p) (hB' : IsArcBetween B' w q)
    (hmeet : ∀ x ∈ A, x ∈ B → x = v)
    (hmeet' : ∀ x ∈ A', x ∈ B' → x = w)
    (hAI : A \ {p} ⊆ inside C) (hBI : B \ {q} ⊆ inside C)
    (hAI' : A' \ {p} ⊆ inside C) (hBI' : B' \ {q} ⊆ inside C) :
    ∃ e : Plane ≃ₜ Plane, e '' A = A' ∧ e '' B = B' ∧ e v = w ∧
      EqOn e id (inside C)ᶜ ∧ ∀ x, dist (e x) x ≤ Metric.diam (C ∪ inside C) := by
  obtain ⟨f⟩ := exists_arcHomeo hA hA'
  obtain ⟨g⟩ := exists_arcHomeo hB hB'
  obtain ⟨e, heA, heB, hfix, hdist⟩ := exists_homeomorph_extending_two_vertex_arcs
    hC hp hq hA hB hA' hB' hmeet hmeet' hAI hBI hAI' hBI' f g
  exact ⟨e, heA.image_eq.trans f.image_eq, heB.image_eq.trans g.image_eq,
    (heA hA.left_mem).trans f.map_left, hfix, hdist⟩

theorem exists_homeomorph_image_vertex_fan_of_nontrivial {ι : Type*} (s : Finset ι)
    (hs : s.Nontrivial) {C : Set Plane} {v : Plane} {p : ι → Plane} {A B : ι → Set Plane}
    (hC : IsJordanCurve C) (hp : ∀ i ∈ s, p i ∈ C)
    (hA : ∀ i ∈ s, IsArcBetween (A i) v (p i))
    (hB : ∀ i ∈ s, IsArcBetween (B i) v (p i))
    (hAI : ∀ i ∈ s, A i \ {p i} ⊆ inside C)
    (hBI : ∀ i ∈ s, B i \ {p i} ⊆ inside C)
    (hAA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → A i ∩ A j = {v})
    (hBB : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B i ∩ B j = {v}) :
    ∃ e : Plane ≃ₜ Plane, (∀ i ∈ s, e '' A i = B i) ∧
      e v = v ∧ EqOn e id (inside C)ᶜ := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := hs
  have hpv : ∀ k ∈ s, p k ≠ v := by
    intro k hk hpk
    obtain ⟨f, _, hfi, _, hf0, hf1⟩ := hA k hk
    exact zero_ne_one (hfi zero_mem_I one_mem_I (hf0.trans (hpk.symm.trans hf1.symm)))
  have hpinj : InjOn p (s : Set ι) := by
    intro k hk l hl hkl
    by_contra hne
    exact hpv k hk ((hAA k hk l hl hne).subset
      ⟨(hA k hk).right_mem, hkl.symm ▸ (hA l hl).right_mem⟩)
  obtain ⟨e₀, he₀i, he₀j, he₀v, hfix₀, _⟩ := exists_homeomorph_image_two_vertex_arcs
    hC (hp i hi) (hp j hj) (hA i hi) (hA j hj) (hB i hi) (hB j hj)
    (fun _ hx hy => (hAA i hi j hj hij).subset ⟨hx, hy⟩)
    (fun _ hx hy => (hBB i hi j hj hij).subset ⟨hx, hy⟩)
    (hAI i hi) (hAI j hj) (hBI i hi) (hBI j hj)
  have he₀p : ∀ k ∈ s, e₀ (p k) = p k :=
    fun k hk => hfix₀ (fun hx => hx.1 (hp k hk))
  have he₀C : e₀ '' C = C := by
    have heq : EqOn e₀ id C := fun _ hx => hfix₀ (fun hinside => hinside.1 hx)
    exact heq.image_eq.trans (image_id C)
  have hA₀ : ∀ k ∈ s, IsArcBetween (e₀ '' A k) v (p k) := by
    intro k hk
    simpa only [he₀v, he₀p k hk] using isArcBetween_image e₀ (hA k hk)
  have hAA₀ : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (e₀ '' A k) ∩ (e₀ '' A l) = {v} := by
    intro k hk l hl hkl
    rw [← image_inter e₀.injective, hAA k hk l hl hkl, image_singleton, he₀v]
  have hA₀I : ∀ k ∈ s, (e₀ '' A k) \ {p k} ⊆ inside C := by
    intro k hk x hx
    obtain ⟨y, hy, rfl⟩ := hx.1
    have hyp : y ≠ p k := by
      rintro rfl
      exact hx.2 (he₀p k hk)
    have hmem : e₀ y ∈ e₀ '' inside C := ⟨y, hAI k hk ⟨hy, hyp⟩, rfl⟩
    rwa [image_inside, he₀C] at hmem
  let P := B i ∪ B j
  have hP : IsArcBetween P (p i) (p j) := (hB i hi).reverse.concatenate (hB j hj)
    (fun _ hx hy => (hBB i hi j hj hij).subset ⟨hx, hy⟩)
  have hvP : v ∈ P := Or.inl (hB i hi).left_mem
  have hPI : P \ {p i, p j} ⊆ inside C := by
    rintro x ⟨hx, hends⟩
    rcases hx with hx | hx
    · exact hBI i hi ⟨hx, fun hxp => hends (Or.inl hxp)⟩
    · exact hBI j hj ⟨hx, fun hxq => hends (Or.inr hxq)⟩
  obtain ⟨L, R, hcut⟩ := exists_isCutPair hC (hp i hi) (hp j hj)
    (fun heq => hij (hpinj hi hj heq))
  let t := (s.erase i).erase j
  let T (U : Set Plane) := t.filter (fun k => p k ∈ U)
  have hts : ∀ k ∈ t, k ∈ s := fun _ hk => (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
  have htne : ∀ k ∈ t, k ≠ i ∧ k ≠ j := fun _ hk =>
    ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1, (Finset.mem_erase.mp hk).1⟩
  have hpends : ∀ k ∈ t, p k ∉ ({p i, p j} : Set Plane) := by
    intro k hk
    rintro (heq | heq)
    · exact (htne k hk).1 (hpinj (hts k hk) hi heq)
    · exact (htne k hk).2 (hpinj (hts k hk) hj heq)
  have hAavoid : ∀ k ∈ t, (e₀ '' A k) \ {v, p k} ⊆ inside C \ P := by
    intro k hk x hx
    refine ⟨hA₀I k (hts k hk) ⟨hx.1, fun heq => hx.2 (Or.inr heq)⟩, ?_⟩
    rintro (hxi | hxj)
    · exact hx.2 (Or.inl ((hAA₀ k (hts k hk) i hi (htne k hk).1).subset
        ⟨hx.1, he₀i.symm ▸ hxi⟩))
    · exact hx.2 (Or.inl ((hAA₀ k (hts k hk) j hj (htne k hk).2).subset
        ⟨hx.1, he₀j.symm ▸ hxj⟩))
  have hBavoid : ∀ k ∈ t, B k \ {v, p k} ⊆ inside C \ P := by
    intro k hk x hx
    refine ⟨hBI k (hts k hk) ⟨hx.1, fun heq => hx.2 (Or.inr heq)⟩, ?_⟩
    rintro (hxi | hxj)
    · exact hx.2 (Or.inl ((hBB k (hts k hk) i hi (htne k hk).1).subset ⟨hx.1, hxi⟩))
    · exact hx.2 (Or.inl ((hBB k (hts k hk) j hj (htne k hk).2).subset ⟨hx.1, hxj⟩))
  have hsideA {U V : Set Plane} (hc : IsCutPair C (p i) (p j) U V) :
      ∀ k ∈ T U, (e₀ '' A k) \ {v, p k} ⊆ inside (U ∪ P) := by
    intro k hk
    obtain ⟨hkt, hkp⟩ := Finset.mem_filter.mp hk
    exact arc_diff_subset_crosscut_side hC hP hc hPI (hA₀ k (hts k hkt))
      (hAavoid k hkt) ⟨hkp, hpends k hkt⟩
  have hsideB {U V : Set Plane} (hc : IsCutPair C (p i) (p j) U V) :
      ∀ k ∈ T U, B k \ {v, p k} ⊆ inside (U ∪ P) := by
    intro k hk
    obtain ⟨hkt, hkp⟩ := Finset.mem_filter.mp hk
    exact arc_diff_subset_crosscut_side hC hP hc hPI (hB k (hts k hkt))
      (hBavoid k hkt) ⟨hkp, hpends k hkt⟩
  have hside {U V : Set Plane} (hc : IsCutPair C (p i) (p j) U V) :
      ∃ e : Plane ≃ₜ Plane, (∀ k ∈ T U, e '' (e₀ '' A k) = B k) ∧
        EqOn e id (inside (U ∪ P))ᶜ := by
    have hsub : ∀ k ∈ T U, k ∈ s := fun k hk => hts k (Finset.mem_filter.mp hk).1
    exact exists_homeomorph_image_boundary_fan (T U)
      (isJordanCurve_cut_arc_union hP hc hPI) (Or.inr hvP)
      (fun _ hk => Or.inl (Finset.mem_filter.mp hk).2)
      (fun k hk => hA₀ k (hsub k hk)) (fun k hk => hB k (hsub k hk))
      (hsideA hc) (hsideB hc)
      (fun k hk l hl hkl => hAA₀ k (hsub k hk) l (hsub l hl) hkl)
      (fun k hk l hl hkl => hBB k (hsub k hk) l (hsub l hl) hkl)
  obtain ⟨e₁, he₁, hfix₁⟩ := hside hcut
  obtain ⟨e₂, he₂, hfix₂⟩ := hside hcut.symm
  obtain ⟨hcover, hdis, _, _⟩ := crosscut_regions hC hP hcut hPI
  have hsmall₁ : inside (L ∪ P) ⊆ inside C \ P := fun _ hx => hcover.symm.subset (Or.inl hx)
  have hsmall₂ : inside (R ∪ P) ⊆ inside C \ P := fun _ hx => hcover.symm.subset (Or.inr hx)
  have hsep₁ := jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut hPI)
  have hsep₂ := jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut.symm hPI)
  have hfixP₁ : EqOn e₁ id P := fun _ hx => hfix₁ (fun hy => (hsmall₁ hy).2 hx)
  have hfixP₂ : EqOn e₂ id P := fun _ hx => hfix₂ (fun hy => (hsmall₂ hy).2 hx)
  have hfixOther₁ : EqOn e₁ id (closure (inside (R ∪ P))) := fun _ hx =>
    hfix₁ (fun hy => disjoint_left.mp (hdis.closure_right hsep₁.isOpen_inside) hy hx)
  have hfixOther₂ : EqOn e₂ id (closure (inside (L ∪ P))) := fun _ hx =>
    hfix₂ (fun hy => disjoint_left.mp (hdis.closure_left hsep₂.isOpen_inside) hx hy)
  have hclose {D U : Set Plane} {a b : Plane} (hD : IsArcBetween D a b)
      (hDU : D \ {a, b} ⊆ U) : D ⊆ closure U := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      exact closure_mono hDU hD.left_mem_closure_diff
    by_cases hxb : x = b
    · subst x
      exact closure_mono hDU hD.right_mem_closure_diff
    exact subset_closure (hDU ⟨hx, fun hends => hends.elim hxa hxb⟩)
  refine ⟨(e₀.trans e₁).trans e₂, ?_, ?_, ?_⟩
  · intro k hk
    change (e₂ ∘ e₁ ∘ e₀) '' A k = B k
    rw [image_comp, image_comp]
    by_cases hki : k = i
    · subst k
      rw [he₀i, (hfixP₁.mono subset_union_left).image_eq, image_id]
      exact (hfixP₂.mono subset_union_left).image_eq.trans (image_id (B i))
    by_cases hkj : k = j
    · subst k
      rw [he₀j, (hfixP₁.mono subset_union_right).image_eq, image_id]
      exact (hfixP₂.mono subset_union_right).image_eq.trans (image_id (B j))
    have hkt : k ∈ t := Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩
    by_cases hkp : p k ∈ L
    · have hkL : k ∈ T L := Finset.mem_filter.mpr ⟨hkt, hkp⟩
      rw [he₁ k hkL]
      exact (hfixOther₂.mono (hclose (hB k hk) (hsideB hcut k hkL))).image_eq.trans (image_id (B k))
    · have hkpR : p k ∈ R := (hcut.union_eq.symm ▸ hp k hk).resolve_left hkp
      have hkR : k ∈ T R := Finset.mem_filter.mpr ⟨hkt, hkpR⟩
      rw [(hfixOther₁.mono (hclose (hA₀ k hk) (hsideA hcut.symm k hkR))).image_eq, image_id]
      exact he₂ k hkR
  · change e₂ (e₁ (e₀ v)) = v
    rw [he₀v, hfixP₁ hvP, id_eq, hfixP₂ hvP]
    rfl
  · intro x hx
    change e₂ (e₁ (e₀ x)) = x
    rw [hfix₀ hx, id_eq, hfix₁ (fun hy => hx (hsmall₁ hy).1), id_eq]
    exact hfix₂ (fun hy => hx (hsmall₂ hy).1)

theorem exists_homeomorph_radial_vertex_fan {ι : Type*} (s : Finset ι)
    (hs : s.Nontrivial) {A : ι → Set Plane} {v : Plane} {p : ι → Plane} {r : ℝ}
    (hr : 0 < r) (hp : ∀ i ∈ s, p i ∈ frontier (Plane.closedSquare v r))
    (hA : ∀ i ∈ s, IsArcBetween (A i) v (p i))
    (hAI : ∀ i ∈ s, A i \ {p i} ⊆ Plane.openSquare v r)
    (hAA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → A i ∩ A j = {v}) :
    ∃ e : Plane ≃ₜ Plane, (∀ i ∈ s, e '' A i = segment ℝ v (p i)) ∧
      e v = v ∧ EqOn e id (Plane.openSquare v r)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  have hpdist : ∀ i ∈ s, Plane.supDist (p i) v = r := by
    intro i hi
    simpa only [Plane.frontier_closedSquare, mem_ofPred_eq] using hp i hi
  have hne : ∀ i ∈ s, v ≠ p i := by
    intro i hi heq
    have hd := hpdist i hi
    rw [← heq, Plane.supDist_self] at hd
    exact hr.ne' hd.symm
  have hpinj : InjOn p (s : Set ι) := by
    intro i hi j hj heq
    by_contra hij
    exact hne i hi ((hAA i hi j hj hij).subset
      ⟨(hA i hi).right_mem, heq.symm ▸ (hA j hj).right_mem⟩).symm
  have hradial : ∀ i ∈ s, segment ℝ v (p i) \ {p i} ⊆ Plane.openSquare v r := by
    intro i hi x hx
    change Plane.supDist x v < r
    rw [← hpdist i hi]
    exact Plane.supDist_lt_of_mem_segment (by rwa [hpdist i hi]) hx.1 hx.2
  have hrmeet : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      segment ℝ v (p i) ∩ segment ℝ v (p j) = {v} := by
    intro i hi j hj hij
    apply Subset.antisymm
    · intro x hx
      exact Plane.radial_meet hr (hpdist i hi) (hpdist j hj)
        (fun heq => hij (hpinj hi hj heq)) (fun h => (h rfl).elim) hx.1 hx.2
    · exact singleton_subset_iff.mpr ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  obtain ⟨e, he, hev, hfix⟩ := exists_homeomorph_image_vertex_fan_of_nontrivial s hs
    (isJordanCurve_frontier_closedSquare v hr) hp hA
    (fun i hi => isArcBetween_segment (hne i hi))
    (by simpa only [inside_frontier_closedSquare] using hAI)
    (by simpa only [inside_frontier_closedSquare] using hradial) hAA hrmeet
  have hfix' : EqOn e id (Plane.openSquare v r)ᶜ := by
    simpa only [inside_frontier_closedSquare] using hfix
  refine ⟨e, he, hev, hfix', fun x => ?_⟩
  by_cases hx : x ∈ Plane.openSquare v r
  · have hex : e x ∈ Plane.openSquare v r := by
      by_contra hnot
      have heq : e x = x := e.injective (hfix' hnot)
      exact hnot (heq.symm ▸ hx)
    exact Metric.dist_le_diam_of_mem (Plane.isBounded_closedSquare v r)
      (Plane.openSquare_subset_closedSquare v r hex) (Plane.openSquare_subset_closedSquare v r hx)
  · rw [hfix' hx, id_eq, dist_self]
    exact Metric.diam_nonneg

theorem exists_homeomorph_image_two_vertex_arcs_radial
    {A B : Set Plane} {v p q : Plane} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ frontier (Plane.closedSquare v r))
    (hq : q ∈ frontier (Plane.closedSquare v r))
    (hA : IsArcBetween A v p) (hB : IsArcBetween B v q)
    (hmeet : ∀ x ∈ A, x ∈ B → x = v)
    (hAI : A \ {p} ⊆ Plane.openSquare v r) (hBI : B \ {q} ⊆ Plane.openSquare v r) :
    ∃ e : Plane ≃ₜ Plane, e '' A = segment ℝ v p ∧ e '' B = segment ℝ v q ∧
      e v = v ∧ EqOn e id (Plane.openSquare v r)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  let F : Bool → Set Plane | false => A | true => B
  let ends : Bool → Plane | false => p | true => q
  have hAB : A ∩ B = {v} := Subset.antisymm
    (fun x hx => hmeet x hx.1 hx.2)
    (singleton_subset_iff.mpr ⟨hA.left_mem, hB.left_mem⟩)
  obtain ⟨e, he, hev, hfix, hdist⟩ := exists_homeomorph_radial_vertex_fan
    (Finset.univ : Finset Bool)
    ⟨false, Finset.mem_univ _, true, Finset.mem_univ _, Bool.false_ne_true⟩
    (A := F) (p := ends) hr
    (by intro i _; cases i <;> assumption)
    (by intro i _; cases i <;> assumption)
    (by intro i _; cases i <;> assumption)
    (by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact hAB
      · exact (inter_comm B A).trans hAB
      · exact (hij rfl).elim)
  exact ⟨e, he false (Finset.mem_univ _), he true (Finset.mem_univ _), hev, hfix, hdist⟩

end DifferentialGeometry.Topology.PlanarJordan

namespace Graph

open Schoenflies DifferentialGeometry.Topology.PlanarJordan
open scoped Graph

theorem IsDrawing.exists_homeomorph_radial_vertex_fan
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {v : Plane} (hincident : (G.incidenceSet v).Nontrivial)
    {N : Set Plane} (hN : N ∈ nhds v) :
    ∃ r > 0, Plane.closedSquare v r ⊆ N ∧
      (∀ d ∈ E(G), ¬ G.Inc d v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing d)) ∧
      ∃ (A : {d // G.Inc d v} → Set Plane) (p : {d // G.Inc d v} → Plane)
        (e : Plane ≃ₜ Plane),
        (∀ d, A d ⊆ edgeArc drawing d ∧ IsArcBetween (A d) v (p d) ∧
          p d ∈ frontier (Plane.closedSquare v r) ∧ A d \ {p d} ⊆ Plane.openSquare v r) ∧
        (∀ d, e '' A d = segment ℝ v (p d)) ∧ e v = v ∧
        EqOn e id (Plane.openSquare v r)ᶜ ∧
        ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hincident
  have hfinite : ({d | G.Inc d v} : Set β).Finite := finite_incidenceSet v
  let _ : Fintype {d // G.Inc d v} := hfinite.fintype
  have hnontrivial : (Finset.univ : Finset {d // G.Inc d v}).Nontrivial :=
    ⟨⟨a, ha⟩, Finset.mem_univ _, ⟨b, hb⟩, Finset.mem_univ _,
      fun heq => hab (congrArg Subtype.val heq)⟩
  obtain ⟨r, hr, hN', hedge, A, p, hall, hmeet, _⟩ :=
    h.exists_vertex_arcs_in_square ha.vertex_mem hN
  have hp : ∀ d, p d ∈ frontier (Plane.closedSquare v r) :=
    fun d => Plane.frontier_openSquare_subset v r (hall d).2.2.1
  obtain ⟨e, he, hev, hfix, hdist⟩ :=
    DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_radial_vertex_fan
      Finset.univ hnontrivial hr (fun d _ => hp d) (fun d _ => (hall d).2.1)
      (fun d _ => (hall d).2.2.2) (fun d _ f _ hdf => hmeet d f hdf)
  exact ⟨r, hr, hN', hedge, A, p, e,
    fun d => ⟨(hall d).1, (hall d).2.1, hp d, (hall d).2.2.2⟩,
    fun d => he d (Finset.mem_univ _), hev, hfix, hdist⟩

theorem IsDrawing.exists_homeomorph_radial_vertex_arc_pair
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {v : Plane} {a b : β}
    (ha : G.Inc a v) (hb : G.Inc b v) (hab : a ≠ b)
    {N : Set Plane} (hN : N ∈ nhds v) :
    ∃ (r : ℝ) (A B : Set Plane) (p q : Plane) (e : Plane ≃ₜ Plane),
      0 < r ∧ Plane.closedSquare v r ⊆ N ∧
      (∀ d ∈ E(G), ¬ G.Inc d v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing d)) ∧
      A ⊆ edgeArc drawing a ∧ B ⊆ edgeArc drawing b ∧
      IsArcBetween A v p ∧ IsArcBetween B v q ∧
      p ∈ frontier (Plane.closedSquare v r) ∧ q ∈ frontier (Plane.closedSquare v r) ∧
      e '' A = segment ℝ v p ∧ e '' B = segment ℝ v q ∧ e v = v ∧
      EqOn e id (Plane.openSquare v r)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (Plane.closedSquare v r) := by
  obtain ⟨r, hr, hN', hedge, A, p, e, hall, he, hev, hfix, hdist⟩ :=
    h.exists_homeomorph_radial_vertex_fan ⟨a, ha, b, hb, hab⟩ hN
  let a' : {d // G.Inc d v} := ⟨a, ha⟩
  let b' : {d // G.Inc d v} := ⟨b, hb⟩
  exact ⟨r, A a', A b', p a', p b', e, hr, hN', hedge, (hall a').1, (hall b').1,
    (hall a').2.1, (hall b').2.1, (hall a').2.2.1, (hall b').2.2.1,
    he a', he b', hev, hfix, hdist⟩

end Graph
