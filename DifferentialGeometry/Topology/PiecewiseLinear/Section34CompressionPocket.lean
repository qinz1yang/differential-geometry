/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.BicollaredComplement
import DifferentialGeometry.Topology.Connected.CompactRegion
import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isConnected_compl_of_isPLBall_three {B : Set E3} (hB : IsPLBall 3 B) :
    IsConnected Bᶜ := by
  have hc : IsClosed B := hB.isPolyhedron.isClosed
  have hcomp : IsCompact B := hB.isPolyhedron.isCompact
  exact isConnected_compl_of_isBicollared_frontier hc
    (hcomp.of_isClosed_subset isClosed_frontier hc.frontier_subset)
    hB.isPLSphere_frontier.isConnected hB.interior_nonempty
    (nonempty_compl.mpr hcomp.ne_univ) hB.isBicollared_frontier

theorem IsPLBall.subset_of_isCompact_frontier_subset {A B : Set E3} (hB : IsPLBall 3 B)
    (hA : IsCompact A) (h : frontier A ⊆ B) : A ⊆ B :=
  subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl hA hB.isPolyhedron.isCompact
    (isConnected_compl_of_isPLBall_three hB).isPreconnected h

theorem IsPLBall.subset_of_disjoint_interior_frontier {A B : Set E3} (hB : IsPLBall 3 B)
    (hA : IsClosed A) (hfr : Disjoint (interior B) (frontier A))
    (hne : (interior B ∩ A).Nonempty) : B ⊆ A := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hsub : interior B ⊆ A :=
    IsPreconnected.subset_of_disjoint_frontier
      (hB.isConnected_interior_of_finrank hdim).isPreconnected hne hfr
  rw [← hB.closure_interior_of_finrank hdim]
  exact closure_minimal hsub hA

theorem subset_interior_or_subset_compl_of_disjoint_frontier {A X : Set E3} (hX : IsClosed X)
    (hA : IsPreconnected A) (hAX : Disjoint A (frontier X)) : A ⊆ interior X ∨ A ⊆ Xᶜ := by
  by_cases hne : (A ∩ interior X).Nonempty
  · exact Or.inl (subset_interior_of_isPreconnected_of_disjoint_frontier hA hAX hne)
  · refine Or.inr fun z hz hzX => hne ⟨z, hz, ?_⟩
    by_contra hzi
    exact Set.disjoint_left.mp hAX hz ⟨hX.closure_eq.symm ▸ hzX, hzi⟩

theorem mem_interior_union_of_inter_frontier_eq {P Y O : Set E3} (hP : IsPLBall 3 P)
    (hY : IsPLBall 3 Y) (hO : IsOpen O) (hPY : O ∩ frontier P = O ∩ frontier Y)
    (hint : Disjoint (interior P) (interior Y)) {y : E3} (hyO : y ∈ O)
    (hy : y ∈ frontier P) : y ∈ interior (P ∪ Y) := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hYc : IsClosed Y := hY.isPolyhedron.isClosed
  have hyY : y ∈ frontier Y := (hPY.subset ⟨hyO, hy⟩).2
  set S := frontier P with hSdef
  have hSP : S ⊆ P := hPc.frontier_subset
  have : LocallyConnectedSpace S := hP.isPLSphere_frontier.isPolyhedron.locallyConnectedSpace
  obtain ⟨Φ, hΦ, hΦ0⟩ :=
    (isBicollared_iff_exists_isOpenEmbedding S).mp hP.isBicollared_frontier
  set y' : S := ⟨y, hy⟩ with hy'def
  have hmem : Φ ⁻¹' O ∈ 𝓝 (y', (0 : ℝ)) := by
    apply hΦ.continuous.continuousAt.preimage_mem_nhds
    rw [hΦ0 y']
    exact hO.mem_nhds hyO
  rw [nhds_prod_eq] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp hmem
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.mp hv
  obtain ⟨N, ⟨hNo, hyN, hNc⟩, hNu⟩ :=
    (LocallyConnectedSpace.open_connected_basis y').mem_iff.mp hu
  have hoff : ∀ (n : S) (t : ℝ), Φ (n, t) ∈ S → t = 0 := by
    intro n t h
    have h2 : Φ (n, t) = Φ (⟨Φ (n, t), h⟩, 0) := (hΦ0 ⟨Φ (n, t), h⟩).symm
    exact congrArg Prod.snd (hΦ.injective h2)
  have hbox : ∀ n ∈ N, ∀ t : ℝ, t ∈ Ioo (-δ) δ → Φ (n, t) ∈ O := by
    intro n hn t ht
    refine huv ⟨hNu hn, hδv ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ht
  set Ap := Φ '' (N ×ˢ Ioo 0 δ) with hApdef
  set Am := Φ '' (N ×ˢ Ioo (-δ) 0) with hAmdef
  set Nb := Φ '' (N ×ˢ Ioo (-δ) δ) with hNbdef
  have hNb : IsOpen Nb := hΦ.isOpenMap _ (hNo.prod isOpen_Ioo)
  have hyNb : y ∈ Nb := ⟨(y', 0), ⟨hyN, neg_lt_zero.mpr hδ, hδ⟩, hΦ0 y'⟩
  have hNbO : Nb ⊆ O := by
    rintro _ ⟨⟨n, t⟩, ⟨hn, ht⟩, rfl⟩
    exact hbox n hn t ht
  have hsplit : Nb ⊆ Ap ∪ Am ∪ S := by
    rintro _ ⟨⟨n, t⟩, ⟨hn, ht⟩, rfl⟩
    rcases lt_trichotomy t 0 with h | rfl | h
    · exact Or.inl (Or.inr ⟨(n, t), ⟨hn, ht.1, h⟩, rfl⟩)
    · refine Or.inr ?_
      rw [hΦ0 n]
      exact n.2
    · exact Or.inl (Or.inl ⟨(n, t), ⟨hn, h, ht.2⟩, rfl⟩)
  have hApc : IsPreconnected Ap :=
    (hNc.isPreconnected.prod isPreconnected_Ioo).image _ hΦ.continuous.continuousOn
  have hAmc : IsPreconnected Am :=
    (hNc.isPreconnected.prod isPreconnected_Ioo).image _ hΦ.continuous.continuousOn
  have hApne : Ap.Nonempty :=
    ⟨Φ (y', δ / 2), (y', δ / 2), ⟨hyN, by linarith, by linarith⟩, rfl⟩
  have hAmne : Am.Nonempty :=
    ⟨Φ (y', -(δ / 2)), (y', -(δ / 2)), ⟨hyN, by linarith, by linarith⟩, rfl⟩
  have hApS : ∀ X : Set E3, O ∩ frontier X = O ∩ S → Disjoint Ap (frontier X) := by
    intro X hX
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨n, t⟩, ⟨hn, ht⟩, rfl⟩ hfr
    have hO' : Φ (n, t) ∈ O := hbox n hn t ⟨by linarith [ht.1], ht.2⟩
    exact (ne_of_gt ht.1) (hoff n t (hX.subset ⟨hO', hfr⟩).2)
  have hAmS : ∀ X : Set E3, O ∩ frontier X = O ∩ S → Disjoint Am (frontier X) := by
    intro X hX
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨n, t⟩, ⟨hn, ht⟩, rfl⟩ hfr
    have hO' : Φ (n, t) ∈ O := hbox n hn t ⟨ht.1, by linarith [ht.2]⟩
    exact (ne_of_lt ht.2) (hoff n t (hX.subset ⟨hO', hfr⟩).2)
  have hexcl : ∀ X : Set E3, IsClosed X → closure (interior X) = X → y ∈ frontier X →
      Nb ⊆ Ap ∪ Am ∪ frontier X →
      ¬(Ap ⊆ interior X ∧ Am ⊆ interior X) ∧ ¬(Ap ⊆ Xᶜ ∧ Am ⊆ Xᶜ) := by
    intro X hX hXreg hyX hNbX
    constructor
    · rintro ⟨h1, h2⟩
      have hsub : Nb ⊆ X := by
        intro z hz
        rcases hNbX hz with (h | h) | h
        · exact interior_subset (h1 h)
        · exact interior_subset (h2 h)
        · exact hX.frontier_subset h
      exact hyX.2 (mem_interior.mpr ⟨Nb, hsub, hNb, hyNb⟩)
    · rintro ⟨h1, h2⟩
      have hyc : y ∈ closure (interior X) := by
        rw [hXreg]
        exact hX.frontier_subset hyX
      obtain ⟨z, hzNb, hzi⟩ := mem_closure_iff.mp hyc Nb hNb hyNb
      rcases hNbX hzNb with (h | h) | h
      · exact h1 h (interior_subset hzi)
      · exact h2 h (interior_subset hzi)
      · exact h.2 hzi
  have hNbP : Nb ⊆ Ap ∪ Am ∪ frontier P := hsplit
  have hNbY : Nb ⊆ Ap ∪ Am ∪ frontier Y := by
    intro z hz
    rcases hsplit hz with h | h
    · exact Or.inl h
    · exact Or.inr (hPY.subset ⟨hNbO hz, h⟩).2
  obtain ⟨hPi, hPo⟩ := hexcl P hPc (hP.closure_interior_of_finrank hdim) hy hNbP
  obtain ⟨hYi, hYo⟩ := hexcl Y hYc (hY.closure_interior_of_finrank hdim) hyY hNbY
  have hflip : ∀ A : Set E3, A.Nonempty → A ⊆ interior P → IsPreconnected A →
      Disjoint A (frontier Y) → A ⊆ Yᶜ := by
    intro A hAne hAP hAc hAY
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hAc hAY with h | h
    · obtain ⟨z, hz⟩ := hAne
      exact (Set.disjoint_left.mp hint (hAP hz) (h hz)).elim
    · exact h
  have hNbPY : Nb ⊆ P ∪ Y := by
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hPc hApc (hApS P rfl) with
      hApP | hApP <;>
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hPc hAmc (hAmS P rfl) with
      hAmP | hAmP
    · exact absurd ⟨hApP, hAmP⟩ hPi
    · have hApY := hflip Ap hApne hApP hApc (hApS Y hPY.symm)
      have hAmY : Am ⊆ interior Y := by
        rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hAmc
          (hAmS Y hPY.symm) with h | h
        · exact h
        · exact absurd ⟨hApY, h⟩ hYo
      intro z hz
      rcases hsplit hz with (h | h) | h
      · exact Or.inl (interior_subset (hApP h))
      · exact Or.inr (interior_subset (hAmY h))
      · exact Or.inl (hSP h)
    · have hAmY := hflip Am hAmne hAmP hAmc (hAmS Y hPY.symm)
      have hApY : Ap ⊆ interior Y := by
        rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hApc
          (hApS Y hPY.symm) with h | h
        · exact h
        · exact absurd ⟨h, hAmY⟩ hYo
      intro z hz
      rcases hsplit hz with (h | h) | h
      · exact Or.inr (interior_subset (hApY h))
      · exact Or.inl (interior_subset (hAmP h))
      · exact Or.inl (hSP h)
    · exact absurd ⟨hApP, hAmP⟩ hPo
  exact mem_interior.mpr ⟨Nb, hNbPY, hNb, hyNb⟩

theorem frontier_union_subset_of_theta {P D Ea Eb Ya J : Set E3} (hP : IsPLBall 3 P)
    (hYa : IsPLBall 3 Ya) (hE : Ea ∪ Eb = frontier P) (hEab : Ea ∩ Eb = J)
    (hDP : D ∩ P = J) (hYaf : frontier Ya = D ∪ Ea) (hEbc : IsClosed Eb) (hDc : IsClosed D)
    (hPa : Disjoint (interior P) Ya) : frontier (P ∪ Ya) ⊆ D ∪ Eb := by
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hYac : IsClosed Ya := hYa.isPolyhedron.isClosed
  have hEaP : Ea ⊆ P := fun z hz => hPc.frontier_subset (hE ▸ Or.inl hz)
  have hside : ∀ z ∈ Ea, z ∉ J → z ∈ interior (P ∪ Ya) := by
    intro z hz hzJ
    have hO : IsOpen (D ∪ Eb)ᶜ := (hDc.union hEbc).isOpen_compl
    have hzO : z ∈ (D ∪ Eb)ᶜ := by
      rintro (hzD | hzE)
      · exact hzJ (hDP ▸ ⟨hzD, hEaP hz⟩)
      · exact hzJ (hEab ▸ ⟨hz, hzE⟩)
    have hfr : (D ∪ Eb)ᶜ ∩ frontier P = (D ∪ Eb)ᶜ ∩ frontier Ya := by
      rw [← hE, hYaf]
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_union]
      tauto
    exact mem_interior_union_of_inter_frontier_eq hP hYa hO hfr
      (hPa.mono_right interior_subset) hzO (hE ▸ Or.inl hz)
  intro z hz
  have hzU : z ∈ P ∪ Ya := (hPc.union hYac).frontier_subset hz
  have hzJ : ∀ w ∈ J, w ∈ D ∪ Eb := fun w hw => Or.inr (hEab ▸ hw).2
  have hEa : z ∈ Ea → z ∈ D ∪ Eb := by
    intro hzE
    by_cases hzJ' : z ∈ J
    · exact hzJ z hzJ'
    · exact absurd (hside z hzE hzJ') hz.2
  rcases hzU with hzP | hzY
  · have hzf : z ∈ frontier P := by
      refine ⟨subset_closure hzP, fun hzi => hz.2 ?_⟩
      exact interior_mono subset_union_left hzi
    rw [← hE] at hzf
    rcases hzf with h | h
    · exact hEa h
    · exact Or.inr h
  · have hzf : z ∈ frontier Ya := by
      refine ⟨subset_closure hzY, fun hzi => hz.2 ?_⟩
      exact interior_mono subset_union_right hzi
    rw [hYaf] at hzf
    rcases hzf with h | h
    · exact Or.inl h
    · exact hEa h

theorem union_eq_and_disjoint_or_of_theta {P D E₁ E₂ Y₁ Y₂ J : Set E3} (hP : IsPLBall 3 P)
    (hY₁ : IsPLBall 3 Y₁) (hY₂ : IsPLBall 3 Y₂) (hE : E₁ ∪ E₂ = frontier P)
    (hE₁₂ : E₁ ∩ E₂ = J) (hDP : D ∩ P = J) (hY₁f : frontier Y₁ = D ∪ E₁)
    (hY₂f : frontier Y₂ = D ∪ E₂) (hE₁c : IsClosed E₁) (hE₂c : IsClosed E₂)
    (hDc : IsClosed D) (hE₁J : (E₁ \ J).Nonempty) :
    (P ∪ Y₁ = Y₂ ∧ Disjoint (interior P) Y₁) ∨ (P ∪ Y₂ = Y₁ ∧ Disjoint (interior P) Y₂) := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hY₁c : IsClosed Y₁ := hY₁.isPolyhedron.isClosed
  have hY₂c : IsClosed Y₂ := hY₂.isPolyhedron.isClosed
  have hPreg : closure (interior P) = P := hP.closure_interior_of_finrank hdim
  have hPi : IsConnected (interior P) := hP.isConnected_interior_of_finrank hdim
  have hE₁P : E₁ ⊆ P := fun z hz => hPc.frontier_subset (hE ▸ Or.inl hz)
  have hJD : J ⊆ D := fun z hz => (hDP ▸ hz : z ∈ D ∩ P).1
  have hdz : ∀ Ei : Set E3, Ei ⊆ frontier P → Disjoint (interior P) (D ∪ Ei) := by
    intro Ei hEi
    refine Set.disjoint_left.mpr fun z hzi hz => ?_
    rcases hz with hzD | hzE
    · have hzJ : z ∈ J := hDP ▸ ⟨hzD, interior_subset hzi⟩
      have hzfr : z ∈ frontier P := hE ▸ Or.inl (hE₁₂ ▸ hzJ : z ∈ E₁ ∩ E₂).1
      exact hzfr.2 hzi
    · exact (hEi hzE).2 hzi
  have hcase : ∀ Yi : Set E3, IsClosed Yi → ∀ Ei : Set E3, Ei ⊆ frontier P →
      frontier Yi = D ∪ Ei → interior P ⊆ Yi ∨ Disjoint (interior P) Yi := by
    intro Yi hYi Ei hEi hYif
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hYi hPi.isPreconnected
      (hYif ▸ hdz Ei hEi) with h | h
    · exact Or.inl (h.trans interior_subset)
    · exact Or.inr (Set.disjoint_left.mpr fun z hz hzY => h hz hzY)
  have hfill : ∀ (Ea Eb Ya Yb : Set E3), IsPLBall 3 Ya → IsPLBall 3 Yb →
      Ea ∪ Eb = frontier P → Ea ∩ Eb = J → frontier Ya = D ∪ Ea → frontier Yb = D ∪ Eb →
      IsClosed Eb → Disjoint (interior P) Ya → P ∪ Ya ⊆ Yb ∧ (interior P ⊆ Yb → Yb ⊆ P ∪ Ya) := by
    intro Ea Eb Ya Yb hYa hYb hEab hEabJ hYaf hYbf hEbc hPa
    have hfr := frontier_union_subset_of_theta hP hYa hEab hEabJ hDP hYaf hEbc hDc hPa
    have hYbc : IsClosed Yb := hYb.isPolyhedron.isClosed
    refine ⟨hYb.subset_of_isCompact_frontier_subset
      (hP.isPolyhedron.isCompact.union hYa.isPolyhedron.isCompact)
      (hfr.trans (by rw [← hYbf]; exact hYbc.frontier_subset)), fun hPb => ?_⟩
    refine hYb.subset_of_disjoint_interior_frontier (hPc.union hYa.isPolyhedron.isClosed)
      (disjoint_interior_frontier.mono_right (hfr.trans hYbf.symm.subset)) ?_
    obtain ⟨z, hz⟩ := hPi.nonempty
    exact ⟨z, interior_maximal hPb isOpen_interior hz, Or.inl (interior_subset hz)⟩
  have hE₁fr : E₁ ⊆ frontier P := hE ▸ subset_union_left
  have hE₂fr : E₂ ⊆ frontier P := hE ▸ subset_union_right
  rcases hcase Y₁ hY₁c E₁ hE₁fr hY₁f with h1 | h1 <;>
  rcases hcase Y₂ hY₂c E₂ hE₂fr hY₂f with h2 | h2
  · exfalso
    have hPY₁ : P ⊆ Y₁ := hPreg ▸ closure_minimal h1 hY₁c
    have hPY₂ : P ⊆ Y₂ := hPreg ▸ closure_minimal h2 hY₂c
    have hin : ∀ (Ea Eb Ya : Set E3), frontier Ya = D ∪ Ea → P ⊆ Ya → Ea ∩ Eb = J →
        Eb ⊆ frontier P → ∀ z ∈ Eb, z ∉ J → z ∈ interior Ya := by
      intro Ea Eb Ya hYaf hPYa hEabJ hEb z hz hzJ
      have hzP : z ∈ P := hPc.frontier_subset (hEb hz)
      refine (mem_interior_iff_notMem_frontier (hPYa hzP)).mpr ?_
      rw [hYaf]
      rintro (hzD | hzE)
      · exact hzJ (hDP ▸ ⟨hzD, hzP⟩)
      · exact hzJ (hEabJ ▸ ⟨hzE, hz⟩)
    have h21 := hin E₁ E₂ Y₁ hY₁f hPY₁ hE₁₂ hE₂fr
    have h12 := hin E₂ E₁ Y₂ hY₂f hPY₂ (by rw [inter_comm]; exact hE₁₂) hE₁fr
    have hfrD : frontier (Y₁ ∪ Y₂) ⊆ D := by
      intro z hz
      have hzU : z ∈ Y₁ ∪ Y₂ := (hY₁c.union hY₂c).frontier_subset hz
      have hnot1 : z ∉ interior Y₁ := fun h => hz.2 (interior_mono subset_union_left h)
      have hnot2 : z ∉ interior Y₂ := fun h => hz.2 (interior_mono subset_union_right h)
      rcases hzU with hzY | hzY
      · have hzf : z ∈ D ∪ E₁ := hY₁f ▸ ⟨subset_closure hzY, hnot1⟩
        rcases hzf with hzD | hzE
        · exact hzD
        · by_cases hzJ : z ∈ J
          · exact hJD hzJ
          · exact absurd (h12 z hzE hzJ) hnot2
      · have hzf : z ∈ D ∪ E₂ := hY₂f ▸ ⟨subset_closure hzY, hnot2⟩
        rcases hzf with hzD | hzE
        · exact hzD
        · by_cases hzJ : z ∈ J
          · exact hJD hzJ
          · exact absurd (h21 z hzE hzJ) hnot1
    have hcomp : IsCompact (Y₁ ∪ Y₂) :=
      hY₁.isPolyhedron.isCompact.union hY₂.isPolyhedron.isCompact
    have hDY₁ : D ⊆ Y₁ := fun w hw => hY₁c.frontier_subset (hY₁f ▸ Or.inl hw)
    have hDY₂ : D ⊆ Y₂ := fun w hw => hY₂c.frontier_subset (hY₂f ▸ Or.inl hw)
    have hs1 := hY₁.subset_of_isCompact_frontier_subset hcomp (hfrD.trans hDY₁)
    have hs2 := hY₂.subset_of_isCompact_frontier_subset hcomp (hfrD.trans hDY₂)
    have heq : Y₁ = Y₂ :=
      subset_antisymm (subset_union_left.trans hs2) (subset_union_right.trans hs1)
    obtain ⟨e, heE, heJ⟩ := hE₁J
    have he : e ∈ D ∪ E₂ := by
      rw [← hY₂f, ← heq, hY₁f]
      exact Or.inr heE
    rcases he with heD | heE2
    · exact heJ (hDP ▸ ⟨heD, hE₁P heE⟩)
    · exact heJ (hE₁₂ ▸ ⟨heE, heE2⟩)
  · exact Or.inr ⟨subset_antisymm
      (hfill E₂ E₁ Y₂ Y₁ hY₂ hY₁ (by rw [union_comm]; exact hE) (by rw [inter_comm]; exact hE₁₂)
        hY₂f hY₁f hE₁c h2).1
      ((hfill E₂ E₁ Y₂ Y₁ hY₂ hY₁ (by rw [union_comm]; exact hE)
        (by rw [inter_comm]; exact hE₁₂) hY₂f hY₁f hE₁c h2).2 h1), h2⟩
  · exact Or.inl ⟨subset_antisymm
      (hfill E₁ E₂ Y₁ Y₂ hY₁ hY₂ hE hE₁₂ hY₁f hY₂f hE₂c h1).1
      ((hfill E₁ E₂ Y₁ Y₂ hY₁ hY₂ hE hE₁₂ hY₁f hY₂f hE₂c h1).2 h2), h1⟩
  · exfalso
    obtain ⟨z, hz⟩ := hPi.nonempty
    have hsub := (hfill E₁ E₂ Y₁ Y₂ hY₁ hY₂ hE hE₁₂ hY₁f hY₂f hE₂c h1).1
    exact Set.disjoint_left.mp h2 hz (hsub (Or.inl (interior_subset hz)))

theorem bentSide_of_chart {P Y U : Set E3} {φ : E3 → ℝ × ℝ × ℝ} {r ε : ℝ} {p : E3}
    (hU : IsOpen U) (hpU : p ∈ U) (hr : 0 < r) (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 r))
    (hφp : φ p = 0) (hε : ε = 1 ∨ ε = -1) (hY : IsPLBall 3 Y)
    (hYU : ∀ y ∈ U, y ∈ frontier Y ↔
      ((φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) ∨ ((φ y).2.1 = 0 ∧ 0 ≤ ε * (φ y).2.2))
    (hPU : ∀ y ∈ U, 0 < (φ y).2.1 → y ∈ interior P) :
    (Disjoint (interior P) Y → ∀ y ∈ U, (φ y).2.1 < 0 → 0 < ε * (φ y).2.2 →
      y ∈ interior Y) ∧
    (interior P ⊆ Y → ∀ y ∈ U, (φ y).2.1 < 0 → 0 < ε * (φ y).2.2 → y ∉ Y) := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hYc : IsClosed Y := hY.isPolyhedron.isClosed
  have hYreg : closure (interior Y) = Y := hY.closure_interior_of_finrank hdim
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  set ψ := Function.invFunOn φ U with hψdef
  have hψc : ContinuousOn ψ (Metric.ball 0 r) := hφ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hψU : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r, ψ z ∈ U ∧ φ (ψ z) = z := fun z hz =>
    ⟨hφ.bijOn.surjOn.mapsTo_invFunOn hz, hφ.bijOn.invOn_invFunOn.2 hz⟩
  have hφU : ∀ y ∈ U, φ y ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r ∧ ψ (φ y) = y := fun y hy =>
    ⟨hφ.bijOn.mapsTo hy, hφ.bijOn.invOn_invFunOn.1 hy⟩
  have hl1 : IsLinearMap ℝ (fun z : ℝ × ℝ × ℝ => z.2.1) :=
    { map_add := fun _ _ => rfl
      map_smul := fun _ _ => rfl }
  have hl2 : IsLinearMap ℝ (fun z : ℝ × ℝ × ℝ => ε * z.2.2) :=
    { map_add := fun x y => by simp only [Prod.snd_add]; ring
      map_smul := fun c x => by simp only [Prod.smul_snd, smul_eq_mul]; ring }
  set Qb : Set (ℝ × ℝ × ℝ) := Metric.ball 0 r ∩ ({z | z.2.1 < 0} ∩ {z | 0 < ε * z.2.2})
    with hQbdef
  set R₁ : Set (ℝ × ℝ × ℝ) := Metric.ball 0 r ∩ {z | 0 < z.2.1} with hR₁def
  set R₂ : Set (ℝ × ℝ × ℝ) := Metric.ball 0 r ∩ {z | ε * z.2.2 < 0} with hR₂def
  have hQb : Convex ℝ Qb := (convex_ball 0 r).inter
    ((convex_halfSpace_lt hl1 0).inter (convex_halfSpace_gt hl2 0))
  have hR₁ : Convex ℝ R₁ := (convex_ball 0 r).inter (convex_halfSpace_gt hl1 0)
  have hR₂ : Convex ℝ R₂ := (convex_ball 0 r).inter (convex_halfSpace_lt hl2 0)
  have hball : ∀ a b c : ℝ, |a| < r → |b| < r → |c| < r →
      ((a, b, c) : ℝ × ℝ × ℝ) ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r := by
    intro a b c ha hb hc
    simp only [mem_ball_zero_iff, Prod.norm_def, Real.norm_eq_abs]
    exact max_lt ha (max_lt hb hc)
  set z₀ : ℝ × ℝ × ℝ := (0, r / 2, 0) with hz₀def
  set z₁ : ℝ × ℝ × ℝ := (0, r / 4, -(ε * (r / 4))) with hz₁def
  have hr0 : |(0 : ℝ)| < r := by rw [abs_zero]; exact hr
  have hz₀R : z₀ ∈ R₁ := ⟨hball _ _ _ hr0 (by rw [abs_lt]; constructor <;> linarith) hr0,
    show (0 : ℝ) < r / 2 by linarith⟩
  have hz₁b : z₁ ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r := by
    refine hball _ _ _ hr0 (by rw [abs_lt]; constructor <;> linarith) ?_
    rcases hε with rfl | rfl <;> rw [abs_lt] <;> constructor <;> linarith
  have hz₁R₁ : z₁ ∈ R₁ := ⟨hz₁b, show (0 : ℝ) < r / 4 by linarith⟩
  have hz₁R₂ : z₁ ∈ R₂ := by
    refine ⟨hz₁b, show ε * -(ε * (r / 4)) < 0 from ?_⟩
    rcases hε with rfl | rfl <;> linarith
  have hQc : IsPreconnected (ψ '' Qb) :=
    hQb.isPreconnected.image ψ (hψc.mono inter_subset_left)
  have hRc : IsPreconnected (ψ '' (R₁ ∪ R₂)) :=
    (IsPreconnected.union z₁ hz₁R₁ hz₁R₂ hR₁.isPreconnected hR₂.isPreconnected).image ψ
      (hψc.mono (union_subset inter_subset_left inter_subset_left))
  have hQfr : Disjoint (ψ '' Qb) (frontier Y) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z, ⟨hzb, hz1, hz2⟩, rfl⟩ hfr
    have hz1' : z.2.1 < 0 := hz1
    have hz2' : 0 < ε * z.2.2 := hz2
    obtain ⟨hzU, hφz⟩ := hψU z hzb
    rcases (hYU _ hzU).mp hfr with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hφz] at h1
      rw [h1, mul_zero] at hz2'
      exact lt_irrefl 0 hz2'
    · rw [hφz] at h1
      exact (ne_of_lt hz1') h1
  have hRfr : Disjoint (ψ '' (R₁ ∪ R₂)) (frontier Y) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z, hz, rfl⟩ hfr
    obtain ⟨hzU, hφz⟩ := hψU z (union_subset inter_subset_left inter_subset_left hz)
    have h := (hYU _ hzU).mp hfr
    rw [hφz] at h
    rcases hz with ⟨-, hz1⟩ | ⟨-, hz2⟩
    · have hz1' : 0 < z.2.1 := hz1
      rcases h with ⟨-, h1⟩ | ⟨h1, -⟩
      · linarith
      · linarith
    · have hz2' : ε * z.2.2 < 0 := hz2
      rcases h with ⟨h1, -⟩ | ⟨-, h1⟩
      · rw [h1, mul_zero] at hz2'
        exact lt_irrefl 0 hz2'
      · linarith
  have hcover : ∀ y ∈ U, y ∈ ψ '' Qb ∨ y ∈ ψ '' (R₁ ∪ R₂) ∨ y ∈ frontier Y := by
    intro y hy
    obtain ⟨hyb, hψy⟩ := hφU y hy
    by_cases h1 : 0 < (φ y).2.1
    · exact Or.inr (Or.inl ⟨φ y, Or.inl ⟨hyb, h1⟩, hψy⟩)
    by_cases h2 : ε * (φ y).2.2 < 0
    · exact Or.inr (Or.inl ⟨φ y, Or.inr ⟨hyb, h2⟩, hψy⟩)
    push Not at h1 h2
    by_cases h3 : (φ y).2.1 < 0 ∧ 0 < ε * (φ y).2.2
    · exact Or.inl ⟨φ y, ⟨hyb, h3.1, h3.2⟩, hψy⟩
    · refine Or.inr (Or.inr ((hYU y hy).mpr ?_))
      rcases lt_or_eq_of_le h1 with h1' | h1'
      · have h4 : ε * (φ y).2.2 = 0 := le_antisymm (not_lt.mp fun h => h3 ⟨h1', h⟩) h2
        rcases mul_eq_zero.mp h4 with h | h
        · exact absurd h hε0
        · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h1', h2⟩
  obtain ⟨hy₀U, hφy₀⟩ := hψU z₀ hz₀R.1
  have hy₀P : ψ z₀ ∈ interior P := hPU _ hy₀U (by rw [hφy₀]; exact hz₀R.2)
  have hy₀R : ψ z₀ ∈ ψ '' (R₁ ∪ R₂) := ⟨z₀, Or.inl hz₀R, rfl⟩
  have hpY : p ∈ frontier Y := (hYU p hpU).mpr (Or.inl ⟨by simp [hφp], by simp [hφp]⟩)
  have hpYY : p ∈ Y := hYc.frontier_subset hpY
  constructor
  · intro hdis y hy hy1 hy2
    have hR : ψ '' (R₁ ∪ R₂) ⊆ Yᶜ := by
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hRc hRfr with h | h
      · exact (Set.disjoint_left.mp hdis hy₀P (interior_subset (h hy₀R))).elim
      · exact h
    have hQ : ψ '' Qb ⊆ interior Y := by
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hQc hQfr with h | h
      · exact h
      · exfalso
        have hpc : p ∈ closure (interior Y) := hYreg.symm ▸ hpYY
        obtain ⟨w, hwU, hwi⟩ := mem_closure_iff.mp hpc U hU hpU
        rcases hcover w hwU with hw | hw | hw
        · exact h hw (interior_subset hwi)
        · exact hR hw (interior_subset hwi)
        · exact hw.2 hwi
    obtain ⟨hyb, hψy⟩ := hφU y hy
    exact hQ ⟨φ y, ⟨hyb, hy1, hy2⟩, hψy⟩
  · intro hPY y hy hy1 hy2 hyY
    have hR : ψ '' (R₁ ∪ R₂) ⊆ interior Y := by
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hRc hRfr with h | h
      · exact h
      · exact (h hy₀R (hPY hy₀P)).elim
    obtain ⟨hyb, hψy⟩ := hφU y hy
    have hyQ : y ∈ ψ '' Qb := ⟨φ y, ⟨hyb, hy1, hy2⟩, hψy⟩
    have hQ : ψ '' Qb ⊆ interior Y := by
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hQc hQfr with h | h
      · exact h
      · exact (h hyQ hyY).elim
    have hUY : U ⊆ Y := by
      intro w hw
      rcases hcover w hw with h | h | h
      · exact interior_subset (hQ h)
      · exact interior_subset (hR h)
      · exact hYc.frontier_subset h
    exact hpY.2 (mem_interior.mpr ⟨U, hUY, hU, hpU⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
