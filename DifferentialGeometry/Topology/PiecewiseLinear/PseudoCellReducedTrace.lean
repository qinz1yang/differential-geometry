/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskCircleComplement
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellDiskPatchPush
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellInnermostTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_reduced_disk_of_finite_trace
    {Ec Eint Ebd Dc Dcint Ω J : Set E3} {P : E3} (hE : IsPseudoCell Ec Eint Ebd P)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint)
    (hDcΩ : Dc ⊆ Ω) (hΩ : IsOpen Ω)
    (hcentral : ∃ D I : Set E3, IsTopologicalCellWithInterior 2 D I ∧ D ⊆ Dc ∧
      D \ I = J ∧ P ∈ I) {n : ℕ} {G : Fin n → Set E3} {Δ : Set E3}
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hΔΩ : Δ ⊆ Ω) (hrim : r '' stdSimplexBoundary 2 = J)
    (hG : ∀ i, IsPLSphere 1 (G i)) (hdisj : Pairwise fun i j => Disjoint (G i) (G j))
    (htrace : Δ ∩ Ec = ⋃ i, G i) (hGD : ∀ i, G i ⊆ Dc) (hGP : ∀ i, P ∉ G i)
    (hJfamily : ∃ i, G i = J)
    (hnoncentral : ∀ i, G i ≠ J →
      ¬ ∃ D I : Set E3, IsTopologicalCellWithInterior 2 D I ∧ D ⊆ Dc ∧
        D \ I = G i ∧ P ∈ I) :
    ∃ (Δ' : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ' ∧
      q '' stdSimplexBoundary 2 = J ∧ Δ' ⊆ Ω ∧ Δ' ∩ Ec = J := by
  classical
  induction n using Nat.strong_induction_on generalizing Δ r with
  | h n ih =>
    have hGΔ : ∀ i, G i ⊆ Δ := by
      intro i x hx
      have hxtr : x ∈ Δ ∩ Ec := htrace.symm ▸ mem_iUnion.mpr ⟨i, hx⟩
      exact hxtr.1
    obtain ⟨b, hb⟩ := hJfamily
    by_cases hall : ∀ i, G i = J
    · refine ⟨Δ, r, hr, hrim, hΔΩ, htrace.trans ?_⟩
      apply Subset.antisymm
      · intro x hx
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        exact hall i ▸ hxi
      · intro x hx
        exact mem_iUnion.mpr ⟨b, hb.symm ▸ hx⟩
    push Not at hall
    obtain ⟨a, ha⟩ := hall
    obtain ⟨j, D, s, hs, hsbd, hDDc, hDE, hDΔ, hjnot⟩ :=
      hE.exists_innermost_disk_of_noncentral_trace hDc hDcE hG hdisj htrace hGD hGP
        (hnoncentral a ha)
    have hjJ : G j ≠ J := by
      intro heq
      exact hjnot (heq.symm ▸ hcentral)
    have hjb : j ≠ b := fun heq => hjJ (heq ▸ hb)
    have hJbd : Disjoint (G j) (r '' stdSimplexBoundary 2) := by
      rw [hrim, ← hb]
      exact hdisj hjb
    have hDG : ∀ i, i ≠ j → Disjoint D (G i) := by
      intro i hij
      refine disjoint_left.mpr fun x hxD hxi => ?_
      have hxj := hDΔ.subset ⟨hxD, hGΔ i hxi⟩
      exact disjoint_left.mp (hdisj hij) hxi hxj
    have hDJ : Disjoint D J := hb ▸ hDG b hjb.symm
    obtain ⟨R, Q, t, hR, ht, hcover, hRQ, htbd, hbdR⟩ :=
      hr.exists_disk_complement_of_circle (hG j) (hGΔ j) hJbd
    have hRΔ : R ⊆ Δ := subset_union_left.trans hcover.subset
    have hRD : R ∩ D = G j := by
      apply Subset.antisymm
      · exact fun x hx => hDΔ.subset ⟨hx.2, hRΔ hx.1⟩
      · intro x hx
        exact ⟨(hRQ.symm.subset hx).1, (hDΔ.symm.subset hx).1⟩
    obtain ⟨F, hF, hFid⟩ :=
      exists_isPLHomeomorphOn_replace_ball hR ht hs htbd hsbd hRQ hRD
    rw [hcover] at hF
    let Γ := R ∪ D
    have hp : IsPLHomeomorphOn (F ∘ r) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ := hr.trans hF
    have hpbd : (F ∘ r) '' stdSimplexBoundary 2 = J := by
      rw [image_comp, (hFid.mono hbdR).image_eq, image_id, hrim]
    have hDΓ : D ⊆ (F ∘ r) '' openSimplex (stdVertices 1) := by
      rw [hp.image_openSimplex_stdVertices, hpbd]
      exact subset_inter subset_union_right (disjoint_left.mp hDJ)
    let T := ⋃ i : {i : Fin n | i ≠ j}, G i.1
    have hT : IsClosed T := isClosed_iUnion_of_finite fun i => (hG i.1).isPolyhedron.isClosed
    have hDT : Disjoint D T := by
      refine disjoint_left.mpr ?_
      rintro x hxD hxT
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxT
      exact disjoint_left.mp (hDG i.1 i.property) hxD hxi
    have hΓE : Γ ∩ Ec ⊆ D ∪ T := by
      rintro x ⟨hxΓ, hxE⟩
      rcases hxΓ with hxR | hxD
      · have hxtr : x ∈ ⋃ i, G i := htrace ▸ (show x ∈ Δ ∩ Ec from ⟨hRΔ hxR, hxE⟩)
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hxtr
        by_cases hij : i = j
        · exact Or.inl ((hDΔ.symm.subset (hij ▸ hxi)).1)
        · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hij⟩, hxi⟩)
      · exact Or.inl hxD
    have hΓΩ : Γ ⊆ Ω := union_subset (hRΔ.trans hΔΩ) (hDDc.trans hDcΩ)
    obtain ⟨Γ', q, hq, hqbd, hΓ'Ω, hΓ'trace⟩ :=
      hE.exists_disk_push_of_coincident_patch hp ⟨s, hs⟩ hDΓ hDE hT hDT hΓE hΩ hΓΩ
    have hside : ∀ i, i ≠ j → G i ⊆ R ∨ Disjoint (G i) R := by
      intro i hij
      have hc : G i ⊆ R ∪ Q := (hGΔ i).trans hcover.symm.subset
      have hd : G i ∩ (R ∩ Q) = ∅ := by
        rw [hRQ]
        exact (hdisj hij).inter_eq
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hG i).isConnected.isPreconnected
          R Q hR.isClosed (show IsPLBall 2 Q from ⟨t, ht⟩).isPolyhedron.isClosed hc hd with
        hsub | hsub
      · exact Or.inl hsub
      · refine Or.inr (disjoint_left.mpr fun x hxi hxR => ?_)
        exact disjoint_left.mp (hdisj hij) hxi (hRQ.subset ⟨hxR, hsub hxi⟩)
    let S := {i : Fin n | i ≠ j ∧ G i ⊆ R}
    have hΓ'S : Γ' ∩ Ec = ⋃ i : S, G i.1 := by
      rw [hΓ'trace]
      ext x
      constructor
      · rintro ⟨⟨hxΓ, hxD⟩, hxE⟩
        have hxR : x ∈ R := hxΓ.resolve_right hxD
        have hxtr : x ∈ ⋃ i, G i := htrace ▸ (show x ∈ Δ ∩ Ec from ⟨hRΔ hxR, hxE⟩)
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hxtr
        have hij : i ≠ j := fun heq => hxD ((hDΔ.symm.subset (heq ▸ hxi)).1)
        rcases hside i hij with hsub | hd
        · exact mem_iUnion.mpr ⟨⟨i, hij, hsub⟩, hxi⟩
        · exact (disjoint_left.mp hd hxi hxR).elim
      · intro hx
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        have hxEc : x ∈ Ec := by
          have hxtr : x ∈ Δ ∩ Ec := htrace.symm ▸ mem_iUnion.mpr ⟨i.1, hxi⟩
          exact hxtr.2
        exact ⟨⟨Or.inl (i.property.2 hxi),
          fun hxD => disjoint_left.mp (hDG i.1 i.property.1) hxD hxi⟩, hxEc⟩
    let m := Fintype.card S
    let e : Fin m ≃ S := (Fintype.equivFin S).symm
    have hmn : m < n := by
      have h := Fintype.card_lt_of_injective_of_notMem (fun i : S => i.1)
        Subtype.val_injective (b := j) (by rintro ⟨i, hi⟩; exact i.property.1 hi)
      simpa only [Fintype.card_fin] using h
    let H : Fin m → Set E3 := fun i => G (e i).1
    have hHtrace : Γ' ∩ Ec = ⋃ i, H i := by
      rw [hΓ'S]
      exact (e.surjective.iUnion_comp fun i : S => G i.1).symm
    have hHfamily : ∃ i, H i = J := by
      have hbR : G b ⊆ R := hb.symm ▸ (hrim ▸ hbdR)
      let b' : S := ⟨b, hjb.symm, hbR⟩
      refine ⟨e.symm b', ?_⟩
      simpa only [H, Equiv.apply_symm_apply] using hb
    exact ih m hmn hq hΓ'Ω (hqbd.trans hpbd) (fun i => hG (e i).1)
      (fun i k hik => hdisj fun heq => hik (e.injective (Subtype.ext heq))) hHtrace
      (fun i => hGD (e i).1) (fun i => hGP (e i).1) hHfamily
      (fun i hi => hnoncentral (e i).1 hi)

end DifferentialGeometry.Topology.PiecewiseLinear
