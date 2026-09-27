/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Subpath
import DifferentialGeometry.Topology.PiecewiseLinear.SquareHomotopyToSurface

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_surface_path_homotopic_of_sides {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W S O₁ O₂ : Set E} (hW : IsOpen W) (hS : IsCompact S) (hSW : S ⊆ W)
    [LocallyPathConnectedSpace S] (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hO : Disjoint O₁ O₂)
    (hWS : W \ S ⊆ O₁ ∪ O₂)
    (h₁ : ∀ (a b : S) (p : Path (Set.inclusion hSW a) (Set.inclusion hSW b)),
      (∀ s, (p s : E) ∈ O₁ ∪ S) → ∃ τ : Path a b, p.Homotopic (τ.map (continuous_inclusion hSW)))
    (h₂ : ∀ (a b : S) (p : Path (Set.inclusion hSW a) (Set.inclusion hSW b)),
      (∀ s, (p s : E) ∈ O₂ ∪ S) → ∃ τ : Path a b, p.Homotopic (τ.map (continuous_inclusion hSW)))
    {a b : S} (γ : Path (Set.inclusion hSW a) (Set.inclusion hSW b)) :
    ∃ τ : Path a b, γ.Homotopic (τ.map (continuous_inclusion hSW)) := by
  classical
  have hinc := continuous_inclusion hSW
  let Good : (t : unitInterval) → ((γ t : E) ∈ S) → Prop := fun t hS' =>
    ∃ σ : Path a ⟨γ t, hS'⟩, (γ.subpath 0 t).Homotopic ((σ.map hinc).cast γ.source rfl)
  have hext : ∀ (t t' : unitInterval) (hS₀ : (γ t : E) ∈ S) (hS₁ : (γ t' : E) ∈ S),
      Good t hS₀ → (∃ τ : Path (⟨γ t, hS₀⟩ : S) ⟨γ t', hS₁⟩,
        (γ.subpath t t').Homotopic (τ.map hinc)) → Good t' hS₁ := by
    rintro t t' hS₀ hS₁ ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨σ.trans τ, ?_⟩
    have h1 : (γ.subpath 0 t').Homotopic ((γ.subpath 0 t).trans (γ.subpath t t')) :=
      ⟨(Path.Homotopy.subpathTransSubpath γ 0 t t').symm⟩
    have h2 := hσ.hcomp hτ
    have h3 : ((σ.map hinc).cast γ.source rfl).trans (τ.map hinc) =
        ((σ.trans τ).map hinc).cast γ.source rfl := by
      ext s
      rw [Path.cast_coe, Path.map_trans, Path.trans_apply, Path.trans_apply]
      split_ifs <;> rfl
    rw [h3] at h2
    exact h1.trans h2
  have hγc : IsCompact (range fun t : unitInterval => (γ t : E)) :=
    isCompact_range (continuous_subtype_val.comp γ.continuous)
  obtain ⟨ρ, hρ, hρW⟩ := hγc.exists_thickening_subset_open hW (by
    rintro _ ⟨t, rfl⟩
    exact (γ t).2)
  have hball : ∀ t : unitInterval, Metric.ball (γ t : E) ρ ⊆ W := fun t =>
    (Metric.ball_subset_thickening (mem_range_self t) ρ).trans hρW
  obtain ⟨δ₂, hδ₂, hS2⟩ := exists_pos_forall_exists_path_dist_lt hS (half_pos hρ)
  obtain ⟨κ, hκ, hunif⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (continuous_subtype_val.comp γ.continuous))
    (min (ρ / 2) δ₂) (lt_min (half_pos hρ) hδ₂)
  have hsmall : ∀ (t t' : unitInterval) (hS₀ : (γ t : E) ∈ S) (hS₁ : (γ t' : E) ∈ S),
      dist t t' < κ → Good t hS₀ → Good t' hS₁ := by
    intro t t' hS₀ hS₁ htt' hgood
    refine hext t t' hS₀ hS₁ hgood ?_
    obtain ⟨τ, hτ⟩ := hS2 ⟨γ t, hS₀⟩ ⟨γ t', hS₁⟩ (by
      change dist (γ t : E) (γ t' : E) < δ₂
      exact (hunif htt').trans_le (min_le_right _ _))
    refine ⟨τ, path_homotopic_of_forall_mem_convex (convex_ball (γ t : E) ρ) (hball t) _ _
      (fun s => ?_) (fun s => ?_)⟩
    · have hmem : (γ.subpath t t' s : W) ∈ range (γ.subpath t t') := mem_range_self s
      rw [Path.range_subpath] at hmem
      obtain ⟨u, hu, hus⟩ := hmem
      rw [← hus, Metric.mem_ball]
      have hut : dist u t < κ := by
        rw [Subtype.dist_eq, Real.dist_eq]
        have hu' : (u : ℝ) ∈ uIcc (t : ℝ) (t' : ℝ) := by
          rcases mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact mem_uIcc.mpr (Or.inl ⟨h1, h2⟩)
          · exact mem_uIcc.mpr (Or.inr ⟨h1, h2⟩)
        calc |(u : ℝ) - t| ≤ |(t' : ℝ) - t| := abs_sub_left_of_mem_uIcc hu'
          _ = dist t t' := by rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
          _ < κ := htt'
      exact ((hunif hut).trans_le (min_le_left _ _)).trans (half_lt_self hρ)
    · change ((τ s : S) : E) ∈ Metric.ball (γ t : E) ρ
      rw [Metric.mem_ball]
      exact (hτ s).trans (half_lt_self hρ)
  have hgap : ∀ (t t' : unitInterval) (hS₀ : (γ t : E) ∈ S) (hS₁ : (γ t' : E) ∈ S), t < t' →
      (∀ u : unitInterval, t < u → u < t' → (γ u : E) ∉ S) → Good t hS₀ → Good t' hS₁ := by
    intro t t' hS₀ hS₁ htt' hno hgood
    refine hext t t' hS₀ hS₁ hgood ?_
    have hIoo : IsPreconnected ((fun r : ℝ => (γ.extend r : E)) '' Ioo (t : ℝ) (t' : ℝ)) :=
      isPreconnected_Ioo.image _ (continuous_subtype_val.comp γ.continuous_extend).continuousOn
    have hsub : (fun r : ℝ => (γ.extend r : E)) '' Ioo (t : ℝ) (t' : ℝ) ⊆ O₁ ∪ O₂ := by
      rintro _ ⟨r, hr, rfl⟩
      have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨t.2.1.trans hr.1.le, hr.2.le.trans t'.2.2⟩
      have hext' : γ.extend r = γ ⟨r, hr01⟩ := Path.extend_extends' γ ⟨r, hr01⟩
      simp only
      rw [hext']
      exact hWS ⟨(γ ⟨r, hr01⟩).2, hno ⟨r, hr01⟩ hr.1 hr.2⟩
    have hside : ∀ O : Set E, (fun r : ℝ => (γ.extend r : E)) '' Ioo (t : ℝ) (t' : ℝ) ⊆ O →
        ∀ s, ((γ.subpath t t' s : W) : E) ∈ O ∪ S := by
      intro O hOs s
      have hmem : (γ.subpath t t' s : W) ∈ range (γ.subpath t t') := mem_range_self s
      rw [Path.range_subpath_of_le _ _ _ htt'.le] at hmem
      obtain ⟨u, hu, hus⟩ := hmem
      rw [← hus]
      rcases eq_or_lt_of_le hu.1 with h | h
      · right
        rw [← h]
        exact hS₀
      rcases eq_or_lt_of_le hu.2 with h' | h'
      · right
        rw [h']
        exact hS₁
      left
      apply hOs
      exact ⟨(u : ℝ), ⟨h, h'⟩, congrArg Subtype.val (Path.extend_extends' γ u)⟩
    rcases hIoo.subset_or_subset hO₁ hO₂ hO hsub with h | h
    · exact h₁ ⟨γ t, hS₀⟩ ⟨γ t', hS₁⟩ (γ.subpath t t') (hside O₁ h)
    · exact h₂ ⟨γ t, hS₀⟩ ⟨γ t', hS₁⟩ (γ.subpath t t') (hside O₂ h)
  have hS0 : ((γ 0 : W) : E) ∈ S := by
    rw [γ.source]
    exact a.2
  have hgood0 : Good 0 hS0 := by
    refine ⟨(Path.refl a).cast rfl (Subtype.ext (congrArg (fun w : W => (w : E)) γ.source)), ?_⟩
    rw [Path.subpath_self]
    refine path_homotopic_of_forall_mem_convex (convex_singleton ((γ 0 : W) : E))
      (singleton_subset_iff.mpr (γ 0).2) _ _ (fun s => rfl) (fun s => ?_)
    change (a : E) = ((γ 0 : W) : E)
    rw [γ.source]
  let Tr : Set ℝ := {r | r ∈ Icc (0 : ℝ) 1 ∧ (γ.extend r : E) ∈ S}
  have hTr : IsClosed Tr :=
    isClosed_Icc.inter (hS.isClosed.preimage (continuous_subtype_val.comp γ.continuous_extend))
  let A : Set ℝ := {r | ∃ hr : r ∈ Icc (0 : ℝ) 1, ∃ hS' : ((γ ⟨r, hr⟩ : W) : E) ∈ S,
    Good ⟨r, hr⟩ hS'}
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, zero_le_one⟩, hS0, hgood0⟩
  have hAbdd : BddAbove A := ⟨1, fun r hr => hr.1.2⟩
  have hATr : A ⊆ Tr := by
    rintro r ⟨hr, hS', -⟩
    refine ⟨hr, ?_⟩
    rw [show γ.extend r = γ ⟨r, hr⟩ from Path.extend_extends' γ ⟨r, hr⟩]
    exact hS'
  have hs0 : 0 ≤ sSup A := le_csSup hAbdd hA0
  have hs1 : sSup A ≤ 1 := csSup_le ⟨0, hA0⟩ fun r hr => hr.1.2
  have hsTr : sSup A ∈ Tr :=
    hTr.closure_subset (closure_mono hATr (csSup_mem_closure ⟨0, hA0⟩ hAbdd))
  have hmemS : ∀ r (hr : r ∈ Icc (0 : ℝ) 1), r ∈ Tr → ((γ ⟨r, hr⟩ : W) : E) ∈ S := by
    intro r hr hrT
    have h := hrT.2
    rwa [show γ.extend r = γ ⟨r, hr⟩ from Path.extend_extends' γ ⟨r, hr⟩] at h
  have hsA : sSup A ∈ A := by
    obtain ⟨r, hrA, hr⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ (show sSup A - κ < sSup A by linarith)
    obtain ⟨hr01, hrS, hrgood⟩ := hrA
    have hrs : r ≤ sSup A := le_csSup hAbdd ⟨hr01, hrS, hrgood⟩
    refine ⟨⟨hs0, hs1⟩, hmemS _ ⟨hs0, hs1⟩ hsTr,
      hsmall ⟨r, hr01⟩ ⟨sSup A, hs0, hs1⟩ hrS _ ?_ hrgood⟩
    rw [Subtype.dist_eq, Real.dist_eq]
    change |r - sSup A| < κ
    exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have hsone : sSup A = 1 := by
    by_contra hne
    have hlt : sSup A < 1 := lt_of_le_of_ne hs1 hne
    let D : Set ℝ := {r | r ∈ Tr ∧ sSup A < r}
    have hb1 : (1 : ℝ) ∈ Tr := by
      refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [Path.extend_one]
      exact b.2
    have hDne : D.Nonempty := ⟨1, hb1, hlt⟩
    have hDbdd : BddBelow D := ⟨sSup A, fun r hr => hr.2.le⟩
    have hsd : sSup A ≤ sInf D := le_csInf hDne fun r hr => hr.2.le
    have hdTr : sInf D ∈ Tr :=
      hTr.closure_subset (closure_mono (fun r hr => hr.1) (csInf_mem_closure hDne hDbdd))
    by_cases hdD : sInf D ∈ D
    · have hd01 := hdTr.1
      have hgd := hgap ⟨sSup A, hs0, hs1⟩ ⟨sInf D, hd01⟩ (hmemS _ ⟨hs0, hs1⟩ hsTr)
        (hmemS _ hd01 hdTr) hdD.2 (fun u hu1 hu2 huS => ?_) hsA.2.2
      · have hdA : sInf D ∈ A := ⟨hd01, hmemS _ hd01 hdTr, hgd⟩
        exact absurd (le_csSup hAbdd hdA) (not_le.mpr hdD.2)
      · have huD : (u : ℝ) ∈ D := by
          refine ⟨⟨u.2, ?_⟩, hu1⟩
          rw [show γ.extend (u : ℝ) = γ u from Path.extend_extends' γ u]
          exact huS
        exact absurd (csInf_le hDbdd huD) (not_le.mpr hu2)
    · have hdeq : sInf D = sSup A := by
        refine le_antisymm ?_ hsd
        by_contra hgt
        exact hdD ⟨hdTr, not_le.mp hgt⟩
      obtain ⟨r, hrD, hr⟩ := exists_lt_of_csInf_lt hDne (show sInf D < sSup A + κ by linarith)
      have hr01 := hrD.1.1
      have hrgood := hsmall ⟨sSup A, hs0, hs1⟩ ⟨r, hr01⟩ (hmemS _ ⟨hs0, hs1⟩ hsTr)
        (hmemS _ hr01 hrD.1) (by
          rw [Subtype.dist_eq, Real.dist_eq]
          change |sSup A - r| < κ
          exact abs_sub_lt_iff.mpr ⟨by linarith [hrD.2], by linarith [hrD.2]⟩) hsA.2.2
      have hrA : r ∈ A := ⟨hr01, hmemS _ hr01 hrD.1, hrgood⟩
      exact absurd (le_csSup hAbdd hrA) (not_le.mpr hrD.2)
  have h1A : (1 : ℝ) ∈ A := hsone ▸ hsA
  obtain ⟨hr1, hS1, σ, hσ⟩ := h1A
  have hb : b = ⟨((γ ⟨1, hr1⟩ : W) : E), hS1⟩ :=
    Subtype.ext (congrArg Subtype.val γ.target).symm
  refine ⟨σ.cast rfl hb, ?_⟩
  have e1 : γ.subpath 0 ⟨1, hr1⟩ = γ.cast γ.source γ.target := γ.subpath_zero_one
  rw [e1] at hσ
  have hfin := hσ.pathCast γ.source.symm γ.target.symm
  have hL : (γ.cast γ.source γ.target).cast γ.source.symm γ.target.symm = γ := by
    ext s
    rfl
  have hR : ((σ.map hinc).cast γ.source rfl).cast γ.source.symm γ.target.symm =
      (σ.cast rfl hb).map hinc := by
    ext s
    rfl
  rw [hL, hR] at hfin
  exact hfin

end DifferentialGeometry.Topology.PiecewiseLinear
