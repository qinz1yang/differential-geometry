/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section MarkedArc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_adjacent_marks_of_arc {Q A B : Set E} {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hB : IsClosed B) (hAB : A ∪ B = Q)
    (hAiB : A ∩ B = {γ 0, γ 1}) {n : ℕ} (q : Fin n → E) {i₀ j₀ : Fin n}
    (hi₀ : γ 0 = q i₀) (hj₀ : γ 1 = q j₀) {s : E} (hsA : s ∈ A) (hsq : ∀ k, q k ≠ s) :
    ∃ (i j : Fin n) (β : ℝ → E), i ≠ j ∧ IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1) ∧
      β 0 = q i ∧ β 1 = q j ∧ β '' Icc 0 1 ⊆ Q ∧ s ∈ β '' Ioo 0 1 ∧
      (∀ k, q k ∉ β '' Ioo 0 1) ∧ IsClosed (Q \ β '' Ioo 0 1) := by
  obtain ⟨t₀, ht₀, rfl⟩ := hγ.bijOn.surjOn hsA
  have hinjγ : InjOn γ (Icc 0 1) := hγ.bijOn.injOn
  have hcont : ContinuousOn γ (Icc 0 1) := hγ.isPiecewiseAffineOn.continuousOn
  let T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ∃ k, q k = γ t}
  have hTfin : T.Finite := by
    refine Set.Finite.of_finite_image ((Set.finite_range q).subset ?_)
      (hinjγ.mono fun t ht => ht.1)
    rintro _ ⟨t, ⟨-, k, hk⟩, rfl⟩
    exact ⟨k, hk⟩
  have h0T : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, i₀, hi₀.symm⟩
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, j₀, hj₀.symm⟩
  have ht0 : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · exact (hsq i₀ (by rw [← hi₀, h])).elim
    · exact h
  have ht1 : t₀ < 1 := by
    rcases eq_or_lt_of_le ht₀.2 with h | h
    · exact (hsq j₀ (by rw [← hj₀, h])).elim
    · exact h
  obtain ⟨a, ⟨haT, hat⟩, hamax⟩ := Set.exists_max_image {t | t ∈ T ∧ t < t₀} id
    (hTfin.subset fun t ht => ht.1) ⟨0, h0T, ht0⟩
  obtain ⟨b, ⟨hbT, hbt⟩, hbmin⟩ := Set.exists_min_image {t | t ∈ T ∧ t₀ < t} id
    (hTfin.subset fun t ht => ht.1) ⟨1, h1T, ht1⟩
  obtain ⟨i, hi⟩ := haT.2
  obtain ⟨j, hj⟩ := hbT.2
  have hab : a < b := hat.trans hbt
  have hij : i ≠ j := by
    intro h
    subst h
    have hab' : a = b := hinjγ haT.1 hbT.1 (hi.symm.trans hj)
    linarith
  have hsubI : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc haT.1.1 hbT.1.2
  obtain ⟨σ, hσ, hσ0, hσ1⟩ :=
    exists_isPLHomeomorphOn_Icc_map_endpoints (by norm_num : (0 : ℝ) < 1) hab
  have hγab := hγ.restrict (isHPolytope_Icc (a := a) (b := b)).isPolyhedron hsubI
  have hβ := hσ.trans hγab
  have hβIoo : (γ ∘ σ) '' Ioo 0 1 = γ '' Ioo a b := by
    rw [hβ.image_Ioo_eq_sdiff_endpoints (by norm_num : (0 : ℝ) < 1),
      hγab.image_Ioo_eq_sdiff_endpoints hab]
    simp only [Function.comp_apply, hσ0, hσ1]
  refine ⟨i, j, γ ∘ σ, hij, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hβ.image_eq]
    exact hβ
  · simp only [Function.comp_apply, hσ0]
    exact hi.symm
  · simp only [Function.comp_apply, hσ1]
    exact hj.symm
  · rw [hβ.image_eq, ← hAB]
    exact (image_mono hsubI).trans (hγ.image_eq.subset.trans subset_union_left)
  · rw [hβIoo]
    exact ⟨t₀, ⟨hat, hbt⟩, rfl⟩
  · intro k hk
    rw [hβIoo] at hk
    obtain ⟨t, ht, hkt⟩ := hk
    have htT : t ∈ T := ⟨hsubI (Ioo_subset_Icc_self ht), k, hkt.symm⟩
    rcases lt_trichotomy t t₀ with h | h | h
    · have hta : t ≤ a := hamax t ⟨htT, h⟩
      linarith [ht.1]
    · exact hsq k (by rw [← hkt, h])
    · have hbt' : b ≤ t := hbmin t ⟨htT, h⟩
      linarith [ht.2]
  · have heq : Q \ (γ ∘ σ) '' Ioo 0 1 = B ∪ γ '' Icc 0 a ∪ γ '' Icc b 1 := by
      rw [hβIoo]
      ext z
      constructor
      · rintro ⟨hzQ, hzn⟩
        rw [← hAB] at hzQ
        rcases hzQ with hzA | hzB
        · obtain ⟨t, ht, rfl⟩ := hγ.bijOn.surjOn hzA
          by_cases hta : t ≤ a
          · exact Or.inl (Or.inr ⟨t, ⟨ht.1, hta⟩, rfl⟩)
          · by_cases htb : b ≤ t
            · exact Or.inr ⟨t, ⟨htb, ht.2⟩, rfl⟩
            · exact (hzn ⟨t, ⟨lt_of_not_ge hta, lt_of_not_ge htb⟩, rfl⟩).elim
        · exact Or.inl (Or.inl hzB)
      · rintro ((hzB | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
        · refine ⟨by rw [← hAB]; exact Or.inr hzB, ?_⟩
          rintro ⟨t, ht, rfl⟩
          have htI : t ∈ Icc (0 : ℝ) 1 := hsubI (Ioo_subset_Icc_self ht)
          have hmem : γ t ∈ A ∩ B := ⟨hγ.bijOn.mapsTo htI, hzB⟩
          rw [hAiB] at hmem
          rcases hmem with h0 | h1
          · have ht0' : t = 0 := hinjγ htI ⟨le_rfl, zero_le_one⟩ h0
            linarith [ht.1, haT.1.1]
          · have ht1' : t = 1 := hinjγ htI ⟨zero_le_one, le_rfl⟩ h1
            linarith [ht.2, hbT.1.2]
        · have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans haT.1.2⟩
          refine ⟨by rw [← hAB]; exact Or.inl (hγ.bijOn.mapsTo htI), ?_⟩
          rintro ⟨t', ht', hγt⟩
          have htt : t' = t := hinjγ (hsubI (Ioo_subset_Icc_self ht')) htI hγt
          linarith [ht'.1, ht.2]
        · have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hbT.1.1.trans ht.1, ht.2⟩
          refine ⟨by rw [← hAB]; exact Or.inl (hγ.bijOn.mapsTo htI), ?_⟩
          rintro ⟨t', ht', hγt⟩
          have htt : t' = t := hinjγ (hsubI (Ioo_subset_Icc_self ht')) htI hγt
          linarith [ht'.2, ht.1]
    rw [heq]
    refine (hB.union ?_).union ?_
    · exact (isCompact_Icc.image_of_continuousOn
        (hcont.mono (Icc_subset_Icc le_rfl haT.1.2))).isClosed
    · exact (isCompact_Icc.image_of_continuousOn
        (hcont.mono (Icc_subset_Icc hbT.1.1 le_rfl))).isClosed

theorem IsPLSphere.exists_arc_between_adjacent_marks {Q : Set E} (hQ : IsPLSphere 1 Q) {n : ℕ}
    (hn : 1 < n) (q : Fin n → E) (hq : ∀ i, q i ∈ Q) (hinj : Function.Injective q) {s : E}
    (hs : s ∈ Q) (hsq : ∀ k, q k ≠ s) :
    ∃ (i j : Fin n) (β : ℝ → E), i ≠ j ∧ IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1) ∧
      β 0 = q i ∧ β 1 = q j ∧ β '' Icc 0 1 ⊆ Q ∧ s ∈ β '' Ioo 0 1 ∧
      (∀ k, q k ∉ β '' Ioo 0 1) ∧ IsClosed (Q \ β '' Ioo 0 1) := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, hn⟩ := fun h => by simp [Fin.ext_iff] at h
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hAB, hAiB⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hQ (hq ⟨0, by omega⟩) (hq ⟨1, hn⟩) (hinj.ne h01)
  have hAc : IsClosed A :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ).isPolyhedron.isClosed
  have hBc : IsClosed B :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hδ).isPolyhedron.isClosed
  rw [← hAB] at hs
  rcases hs with hsA | hsB
  · exact exists_adjacent_marks_of_arc hγ hBc hAB (by rw [hγ0, hγ1]; exact hAiB) q hγ0 hγ1
      hsA hsq
  · exact exists_adjacent_marks_of_arc hδ hAc (by rw [union_comm]; exact hAB)
      (by rw [inter_comm, hδ0, hδ1]; exact hAiB) q hδ0 hδ1 hsB hsq

end MarkedArc

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_annulus_parametrization_of_product_circle_cut
    {J Q X : Set E3} (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : E3 × E3 → E3} (hf : IsPLHomeomorphOn f (J ×ˢ Q) X)
    {n : ℕ} (hn : 1 < n) (q : Fin n → E3) (hq : ∀ i, q i ∈ Q)
    (hinj : Function.Injective q) {x : E3}
    (hx : x ∈ X \ (⋃ i, f '' (J ×ˢ {q i}))) :
    ∃ i j : Fin n, i ≠ j ∧ ∃ ρ : E3 × ℝ → E3,
      IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1)
        (closure (connectedComponentIn (X \ ⋃ k, f '' (J ×ˢ {q k})) x)) ∧
      f '' (J ×ˢ {q i}) = ρ '' (J ×ˢ {(0 : ℝ)}) ∧
      f '' (J ×ˢ {q j}) = ρ '' (J ×ˢ {(1 : ℝ)}) := by
  obtain ⟨⟨y, s⟩, ⟨hyJ, hsQ⟩, rfl⟩ := hf.bijOn.surjOn hx.1
  have hsq : ∀ k, q k ≠ s := by
    intro k hk
    exact hx.2 (mem_iUnion.mpr ⟨k, ⟨(y, s), ⟨hyJ, hk.symm⟩, rfl⟩⟩)
  obtain ⟨i, j, β, hij, hβ, hβ0, hβ1, hβQ, hsβ, hmarks, hclosed⟩ :=
    hQ.exists_arc_between_adjacent_marks hn q hq hinj hsQ hsq
  have hJpoly : IsPolyhedron J := hJ.isPolyhedron
  have hβpoly : IsPolyhedron (β '' Icc 0 1) :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hβ).isPolyhedron
  have hm : IsPLHomeomorphOn (Prod.map id β) (J ×ˢ Icc 0 1) (J ×ˢ (β '' Icc 0 1)) :=
    hJpoly.isPLHomeomorphOn_id.prodMap hβ
  have hfr := hf.restrict (hJpoly.prod hβpoly) (prod_mono subset_rfl hβQ)
  have hρ : IsPLHomeomorphOn (f ∘ Prod.map id β) (J ×ˢ Icc 0 1)
      (f '' (J ×ˢ (β '' Icc 0 1))) := hm.trans hfr
  have hfiber : ∀ (z : E3) (t : ℝ) (k : Fin n), z ∈ J → β t = q k →
      (f ∘ Prod.map id β) (z, t) ∈ ⋃ k, f '' (J ×ˢ {q k}) := by
    intro z t k hz htk
    refine mem_iUnion.mpr ⟨k, ⟨(z, q k), ⟨hz, rfl⟩, ?_⟩⟩
    change f (z, q k) = f (z, β t)
    rw [htk]
  have hVW : (f ∘ Prod.map id β) '' (J ×ˢ Ioo 0 1) ⊆ X \ ⋃ k, f '' (J ×ˢ {q k}) := by
    rintro _ ⟨⟨z, u⟩, ⟨hz, hu⟩, rfl⟩
    have hβu : β u ∈ Q := hβQ ⟨u, Ioo_subset_Icc_self hu, rfl⟩
    refine ⟨hf.bijOn.mapsTo ⟨hz, hβu⟩, ?_⟩
    intro hmem
    obtain ⟨k, ⟨⟨z', c⟩, ⟨hz', hc⟩, heq⟩⟩ := mem_iUnion.mp hmem
    have hc' : c = q k := hc
    have hcQ : c ∈ Q := by
      rw [hc']
      exact hq k
    have hpair := hf.bijOn.injOn (show (z', c) ∈ J ×ˢ Q from ⟨hz', hcQ⟩)
      (show (z, β u) ∈ J ×ˢ Q from ⟨hz, hβu⟩) heq
    have hcu : c = β u := congrArg Prod.snd hpair
    exact hmarks k ⟨u, hu, by rw [← hc', hcu]⟩
  have hxV : f (y, s) ∈ (f ∘ Prod.map id β) '' (J ×ˢ Ioo 0 1) := by
    obtain ⟨u, hu, hus⟩ := hsβ
    refine ⟨(y, u), ⟨hyJ, hu⟩, ?_⟩
    change f (y, β u) = f (y, s)
    rw [hus]
  have hVconn : IsConnected ((f ∘ Prod.map id β) '' (J ×ˢ Ioo 0 1)) :=
    (hJ.isConnected.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image _
      (hρ.isPiecewiseAffineOn.continuousOn.mono (prod_mono subset_rfl Ioo_subset_Icc_self))
  have hcomp : connectedComponentIn (X \ ⋃ k, f '' (J ×ˢ {q k})) (f (y, s)) =
      (f ∘ Prod.map id β) '' (J ×ˢ Ioo 0 1) := by
    apply Subset.antisymm
    · have hCW := connectedComponentIn_subset (X \ ⋃ k, f '' (J ×ˢ {q k})) (f (y, s))
      have hK₁ : IsClosed ((f ∘ Prod.map id β) '' (J ×ˢ Icc 0 1)) :=
        ((hJpoly.isCompact.prod isCompact_Icc).image_of_continuousOn
          hρ.isPiecewiseAffineOn.continuousOn).isClosed
      have hK₂ : IsClosed (f '' (J ×ˢ (Q \ β '' Ioo 0 1))) :=
        ((hJpoly.isCompact.prod (hQ.isPolyhedron.isCompact.of_isClosed_subset hclosed
          sdiff_subset)).image_of_continuousOn (hf.isPiecewiseAffineOn.continuousOn.mono
            (prod_mono subset_rfl sdiff_subset))).isClosed
      have hcover : connectedComponentIn (X \ ⋃ k, f '' (J ×ˢ {q k})) (f (y, s)) ⊆
          (f ∘ Prod.map id β) '' (J ×ˢ Icc 0 1) ∪ f '' (J ×ˢ (Q \ β '' Ioo 0 1)) := by
        intro w hw
        obtain ⟨⟨z, c⟩, ⟨hz, hc⟩, rfl⟩ := hf.bijOn.surjOn (hCW hw).1
        by_cases hcβ : c ∈ β '' Ioo 0 1
        · obtain ⟨u, hu, rfl⟩ := hcβ
          exact Or.inl ⟨(z, u), ⟨hz, Ioo_subset_Icc_self hu⟩, rfl⟩
        · exact Or.inr ⟨(z, c), ⟨hz, hc, hcβ⟩, rfl⟩
      have hends : ∀ z ∈ J, ∀ u ∈ Icc (0 : ℝ) 1, u ∉ Ioo (0 : ℝ) 1 →
          (f ∘ Prod.map id β) (z, u) ∈ ⋃ k, f '' (J ×ˢ {q k}) := by
        intro z hz u hu hu'
        rcases eq_or_lt_of_le hu.1 with hu0 | hu0
        · exact hfiber z u i hz (by rw [← hu0, hβ0])
        · rcases eq_or_lt_of_le hu.2 with hu1 | hu1
          · exact hfiber z u j hz (by rw [hu1, hβ1])
          · exact (hu' ⟨hu0, hu1⟩).elim
      have hdisj : connectedComponentIn (X \ ⋃ k, f '' (J ×ˢ {q k})) (f (y, s)) ∩
          ((f ∘ Prod.map id β) '' (J ×ˢ Icc 0 1) ∩ f '' (J ×ˢ (Q \ β '' Ioo 0 1))) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro w ⟨hwC, ⟨⟨z, u⟩, ⟨hz, hu⟩, hw1⟩, ⟨⟨z', c⟩, ⟨hz', hcQ, hcβ⟩, hw2⟩⟩
        have hβu : β u ∈ Q := hβQ ⟨u, hu, rfl⟩
        have hpair := hf.bijOn.injOn (show (z', c) ∈ J ×ˢ Q from ⟨hz', hcQ⟩)
          (show (z, β u) ∈ J ×ˢ Q from ⟨hz, hβu⟩) (hw2.trans hw1.symm)
        have hcu : c = β u := congrArg Prod.snd hpair
        apply (hCW hwC).2
        rw [← hw1]
        exact hends z hz u hu fun h => hcβ ⟨u, h, hcu.symm⟩
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn)
        _ _ hK₁ hK₂ hcover hdisj with hC | hC
      · intro w hw
        obtain ⟨⟨z, u⟩, ⟨hz, hu⟩, hwz⟩ := hC hw
        by_cases hu' : u ∈ Ioo (0 : ℝ) 1
        · exact ⟨(z, u), ⟨hz, hu'⟩, hwz⟩
        · exact ((hCW hw).2 (hwz ▸ hends z hz u hu hu')).elim
      · exfalso
        obtain ⟨⟨z, c⟩, ⟨hz, hcQ, hcβ⟩, heq⟩ :=
          hC (mem_connectedComponentIn hx)
        have hpair := hf.bijOn.injOn (show (z, c) ∈ J ×ˢ Q from ⟨hz, hcQ⟩)
          (show (y, s) ∈ J ×ˢ Q from ⟨hyJ, hsQ⟩) heq
        have hcs : c = s := congrArg Prod.snd hpair
        exact hcβ (hcs ▸ hsβ)
    · exact hVconn.isPreconnected.subset_connectedComponentIn hxV hVW
  have hclosure : closure (connectedComponentIn (X \ ⋃ k, f '' (J ×ˢ {q k})) (f (y, s))) =
      f '' (J ×ˢ (β '' Icc 0 1)) := by
    rw [hcomp, ← hρ.image_closure (hJpoly.isCompact.prod isCompact_Icc)
      (prod_mono subset_rfl Ioo_subset_Icc_self), closure_prod_eq, hJpoly.isClosed.closure_eq,
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), hρ.image_eq]
  have hslice : ∀ (t : ℝ) (c : E3), β t = c →
      f '' (J ×ˢ {c}) = (f ∘ Prod.map id β) '' (J ×ˢ {t}) := by
    intro t c htc
    ext w
    constructor
    · rintro ⟨⟨z, c'⟩, ⟨hz, hc'⟩, rfl⟩
      have hc'' : c' = c := hc'
      refine ⟨(z, t), ⟨hz, rfl⟩, ?_⟩
      change f (z, β t) = f (z, c')
      rw [htc, hc'']
    · rintro ⟨⟨z, t'⟩, ⟨hz, ht'⟩, rfl⟩
      have ht'' : t' = t := ht'
      refine ⟨(z, c), ⟨hz, rfl⟩, ?_⟩
      change f (z, c) = f (z, β t')
      rw [ht'', htc]
  refine ⟨i, j, hij, f ∘ Prod.map id β, ?_, hslice 0 (q i) hβ0, hslice 1 (q j) hβ1⟩
  rw [hclosure]
  exact hρ

end DifferentialGeometry.Topology.PiecewiseLinear
