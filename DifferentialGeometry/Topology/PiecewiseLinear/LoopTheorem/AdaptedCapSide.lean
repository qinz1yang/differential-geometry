/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneMarkedChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem exists_mem_Ioo_of_eventually_nhdsWithin_Icc {P : ℝ → Prop}
    (h : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] 0, P s) : ∀ ε > 0, ∃ s ∈ Ioo (0 : ℝ) ε, P s := by
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp h
  have hm : 0 < min (min ε δ) 1 := lt_min (lt_min hε hδ) one_pos
  refine ⟨min (min ε δ) 1 / 2, ⟨half_pos hm, ?_⟩, hsub ⟨?_, ?_, ?_⟩⟩
  · linarith [min_le_left (min ε δ) 1, min_le_left ε δ]
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hm)]
    linarith [min_le_left (min ε δ) 1, min_le_right ε δ]
  · exact (half_pos hm).le
  · linarith [min_le_right (min ε δ) 1]

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_isPreconnected_sideGerm_of_isTwoSidedBranchCollar [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : ¬hD.singularSet.IsBoundaryBranch c) {J T Q E C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c (J ∪ T) τ)
    (hρ : hD.IsTwoSidedBranchCollar c (J ∪ T) (Q ∪ E) C ρ) (hJT : Disjoint J T)
    (hT : IsCompact T) (hQ : IsCompact Q) (hQdom : Q ⊆ D.domain) (hJQ : J ⊆ Q)
    (hinj : InjOn (⇑D) Q) {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) {W₀ : Set M}
    (hW₀ : IsOpen W₀) (haW₀ : ⇑D a ∈ W₀) :
    ∃ O : Set M, O ⊆ W₀ ∧ IsPreconnected O ∧
      Disjoint O (⇑D '' (Q ∪ ρ '' (T ×ˢ Icc (-1 : ℝ) 0))) ∧
        (∀ ε > 0, ∃ s ∈ Ioo (0 : ℝ) ε, ⇑D (ρ (a, -s)) ∈ O) ∧
          ∃ b ∈ T, ∀ ε > 0, ∃ s ∈ Ioo (0 : ℝ) ε, ⇑D (ρ (b, s)) ∈ O := by
  classical
  obtain ⟨e, he⟩ := hD.exists_isMarkedCrossingChartAt hc hτ hρ (Or.inl ha)
  obtain ⟨hpre, -, hCint, hJTC, hCnhds, hρpl, hρ0, -, hCQ, -, -, -, -⟩ := id hρ
  obtain ⟨-, -, -, hτmaps, -, hτne, -, -, hτfib⟩ := id hτ
  obtain ⟨-, hpe, hep, Pa, Pb, haPa, hτPb, -, -, -, hPa, hPb, -, -, -, -, hsheetA, hsheetB,
    hcarrier, hsignA, hsignB⟩ := he
  set p := ⇑D a with hpdef
  have hCdom : C ⊆ D.domain := hCint.trans interior_subset
  have hρmaps : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (w, u) ∈ C := fun w hw u hu =>
    hρpl.bijOn.mapsTo ⟨hw, hu⟩
  have hρinj : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ w' ∈ J ∪ T, ∀ u' ∈ Icc (-1 : ℝ) 1,
      ρ (w, u) = ρ (w', u') → w = w' ∧ u = u' := by
    intro w hw u hu w' hw' u' hu' h
    have h' := hρpl.bijOn.injOn ⟨hw, hu⟩ ⟨hw', hu'⟩ h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hρJT : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (w, u) ∈ J ∪ T → u = 0 := by
    intro w hw u hu hmem
    have h := hρinj (ρ (w, u)) hmem 0 ⟨by norm_num, by norm_num⟩ w hw u hu
      (hρ0 _ hmem)
    exact h.2.symm
  have hcarrier_pre : ∀ x ∈ D.domain, ⇑D x ∈ hD.singularSet.branchCarrier c → x ∈ J ∪ T := by
    intro x hx hxc
    have hmem : x ∈ hD.branchPreimage c := ⟨hx, hxc⟩
    rwa [hpre] at hmem
  have hcarrier_img : ∀ w ∈ J ∪ T, ⇑D w ∈ hD.singularSet.branchCarrier c := by
    intro w hw
    have hmem : w ∈ hD.branchPreimage c := hpre.symm.subset hw
    exact hmem.2
  have haJT : a ∈ J ∪ T := Or.inl ha
  have hτa : τ a ∈ T := by
    rcases hτmaps haJT with h | h
    · exact absurd (hinj (hJQ h) (hJQ ha) (hτfib a haJT (τ a) (hτmaps haJT) |>.mpr
        (Or.inr rfl)).symm) (hτne a haJT)
    · exact h
  have hτaJT : τ a ∈ J ∪ T := Or.inr hτa
  set Oa := interior (Pa ∩ C) with hOadef
  set Ob := interior (Pb ∩ C) with hObdef
  have haOa : a ∈ Oa := mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hPa (hCnhds a haJT))
  have hτOb : τ a ∈ Ob :=
    mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hPb (hCnhds (τ a) hτaJT))
  have hIcc10 : Icc (-1 : ℝ) 0 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc le_rfl (by norm_num)
  have hTρcomp : IsCompact (ρ '' (T ×ˢ Icc (-1 : ℝ) 0)) :=
    (hT.prod isCompact_Icc).image_of_continuousOn
      (hρpl.isPiecewiseAffineOn.continuousOn.mono
        (prod_mono subset_union_right hIcc10))
  have hTρC : ρ '' (T ×ˢ Icc (-1 : ℝ) 0) ⊆ C := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    exact hρmaps t (Or.inr ht) u (hIcc10 hu)
  set K₁ := ⇑D '' (Q \ Oa) with hK₁def
  set K₂ := ⇑D '' (ρ '' (T ×ˢ Icc (-1 : ℝ) 0) \ Ob) with hK₂def
  have hK₁closed : IsClosed K₁ :=
    ((hQ.diff isOpen_interior).image_of_continuousOn
      (D.continuousOn.mono (sdiff_subset.trans hQdom))).isClosed
  have hK₂closed : IsClosed K₂ :=
    ((hTρcomp.diff isOpen_interior).image_of_continuousOn
      (D.continuousOn.mono (sdiff_subset.trans (hTρC.trans hCdom)))).isClosed
  have hpK₁ : p ∉ K₁ := by
    rintro ⟨x, ⟨hxQ, hxOa⟩, hx⟩
    exact hxOa (hinj hxQ (hJQ ha) hx ▸ haOa)
  have hpK₂ : p ∉ K₂ := by
    rintro ⟨x, ⟨⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩, hxOb⟩, hx⟩
    have hxC := hρmaps t (Or.inr ht) u (hIcc10 hu)
    have hxJT : ρ (t, u) ∈ J ∪ T := by
      refine hcarrier_pre _ (hCdom hxC) ?_
      rw [hx]
      exact hcarrier_img a haJT
    have hu0 := hρJT t (Or.inr ht) u (hIcc10 hu) hxJT
    rw [hu0, hρ0 t (Or.inr ht)] at hx hxOb
    rcases (hτfib a haJT t (Or.inr ht)).mp hx.symm with h | h
    · exact Set.disjoint_left.mp hJT ha (h ▸ ht)
    · exact hxOb (h ▸ hτOb)
  set G : Set M := {z | z ∈ W₀ ∧ z ∉ K₁ ∧ z ∉ K₂ ∧ z ∈ e.source ∧
    (z ∈ ⇑D '' Pa ↔ (e z).2.2 = 0) ∧ (z ∈ ⇑D '' Pb ↔ (e z).2.1 = 0) ∧
      (z ∈ hD.singularSet.branchCarrier c ↔ (e z).2 = 0)} with hGdef
  have hG : G ∈ 𝓝 p := by
    filter_upwards [hW₀.mem_nhds haW₀, hK₁closed.isOpen_compl.mem_nhds hpK₁,
      hK₂closed.isOpen_compl.mem_nhds hpK₂, e.open_source.mem_nhds hpe, hsheetA, hsheetB,
      hcarrier] with z h₁ h₂ h₃ h₄ h₅ h₆ h₇
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  have hS : e.target ∩ e.symm ⁻¹' G ∈ 𝓝 (0 : ℝ × ℝ × ℝ) := by
    rw [← hep]
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hpe)) ?_
    refine (e.continuousAt_symm (e.map_source hpe)).preimage_mem_nhds ?_
    rw [e.left_inv hpe]
    exact hG
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hS
  set H : Set (ℝ × ℝ × ℝ) := {q | q.2.1 < 0 ∨ 0 < q.2.2} with hHdef
  have hfst : IsLinearMap ℝ fun q : ℝ × ℝ × ℝ => q.2.1 :=
    ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).isLinear
  have hsnd : IsLinearMap ℝ fun q : ℝ × ℝ × ℝ => q.2.2 :=
    ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).isLinear
  have hHball : Metric.ball (0 : ℝ × ℝ × ℝ) r ∩ H =
      (Metric.ball (0 : ℝ × ℝ × ℝ) r ∩ {q | q.2.1 < 0}) ∪
        (Metric.ball (0 : ℝ × ℝ × ℝ) r ∩ {q | 0 < q.2.2}) := by
    rw [hHdef, ofPred_or, inter_union_distrib_left]
  have hq₀ : ((0 : ℝ), -(r / 2), r / 2) ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r := by
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt (norm_prod_le_iff.mpr ⟨by simp [(half_pos hr).le],
      norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩) (half_lt_self hr)
    · rw [norm_neg, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    · rw [Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  have hpcH : IsPreconnected (Metric.ball (0 : ℝ × ℝ × ℝ) r ∩ H) := by
    rw [hHball]
    refine IsPreconnected.union ((0 : ℝ), -(r / 2), r / 2)
      ⟨hq₀, show -(r / 2) < 0 by linarith⟩ ⟨hq₀, show (0 : ℝ) < r / 2 by linarith⟩
      ((convex_ball _ _).inter (convex_halfSpace_lt hfst 0)).isPreconnected
      ((convex_ball _ _).inter (convex_halfSpace_gt hsnd 0)).isPreconnected
  have hmemG : ∀ q ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r,
      q ∈ e.target ∧ e.symm q ∈ G := fun q hq => hball hq
  refine ⟨e.symm '' (Metric.ball (0 : ℝ × ℝ × ℝ) r ∩ H), ?_, ?_, ?_, ?_, ⟨τ a, hτa, ?_⟩⟩
  · rintro _ ⟨q, ⟨hq, -⟩, rfl⟩
    exact (hmemG q hq).2.1
  · exact hpcH.image _ (e.continuousOn_symm.mono fun q hq => (hmemG q hq.1).1)
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨q, ⟨hq, hqH⟩, rfl⟩ ⟨x, hx, hxz⟩
    obtain ⟨hqt, hGz⟩ := hmemG q hq
    obtain ⟨-, hzK₁, hzK₂, -, hzA, hzB, hzC⟩ := hGz
    have heq : e (e.symm q) = q := e.right_inv hqt
    rcases hx with hxQ | hxT
    · have hxOa : x ∈ Oa := by
        by_contra hxOa
        exact hzK₁ ⟨x, ⟨hxQ, hxOa⟩, hxz⟩
      have hxPaC := interior_subset hxOa
      have hw0 : q.2.2 = 0 := by
        rw [← heq]
        exact hzA.mp ⟨x, hxPaC.1, hxz⟩
      have hxCQ : x ∈ C ∩ (Q ∪ E) := ⟨hxPaC.2, Or.inl hxQ⟩
      rw [hCQ] at hxCQ
      obtain ⟨⟨w, u⟩, ⟨hw, hu⟩, hwu⟩ := hxCQ
      have hv : 0 ≤ q.2.1 := by
        rcases eq_or_lt_of_le hu.1 with h | h
        · have hxw : x = w := by rw [← hwu, show u = 0 from h.symm, hρ0 w hw]
          have hzcar : e.symm q ∈ hD.singularSet.branchCarrier c := by
            rw [← hxz, hxw]
            exact hcarrier_img w hw
          have hz0 := hzC.mp hzcar
          rw [heq] at hz0
          exact le_of_eq (congrArg Prod.fst hz0).symm
        · have hpos := (hsignA x hxPaC.1).mpr ⟨u, ⟨h, hu.2⟩, w, hw, hwu.symm⟩
          rw [hxz, heq] at hpos
          exact hpos.le
      rcases hqH with h | h
      · linarith
      · rw [hw0] at h
        exact lt_irrefl _ h
    · have hxOb : x ∈ Ob := by
        by_contra hxOb
        exact hzK₂ ⟨x, ⟨hxT, hxOb⟩, hxz⟩
      have hxPbC := interior_subset hxOb
      have hv0 : q.2.1 = 0 := by
        rw [← heq]
        exact hzB.mp ⟨x, hxPbC.1, hxz⟩
      obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, hxtu⟩ := hxT
      have hnotpos : ¬0 < q.2.2 := by
        intro hpos
        rw [← heq, ← hxz] at hpos
        obtain ⟨s, hs, w, hw, hxw⟩ := (hsignB x hxPbC.1).mp hpos
        have h := hρinj t (Or.inr ht) u (hIcc10 hu) w hw s ⟨by linarith [hs.1], hs.2⟩
          (hxtu.trans hxw)
        linarith [hu.2, hs.1, h.2]
      rcases hqH with h | h
      · rw [hv0] at h
        exact lt_irrefl _ h
      · exact hnotpos h
  · have hmapsA : MapsTo (fun s : ℝ => (a, -s)) (Icc (0 : ℝ) 1)
        ((J ∪ T) ×ˢ Icc (-1 : ℝ) 1) :=
      fun s hs => ⟨haJT, by linarith [hs.2], by linarith [hs.1]⟩
    have hρA : ContinuousOn (fun s : ℝ => ρ (a, -s)) (Icc (0 : ℝ) 1) :=
      hρpl.isPiecewiseAffineOn.continuousOn.comp (by fun_prop) hmapsA
    have hφA : ContinuousOn (fun s : ℝ => ⇑D (ρ (a, -s))) (Icc (0 : ℝ) 1) :=
      D.continuousOn.comp hρA fun s hs => hCdom (hρpl.bijOn.mapsTo (hmapsA hs))
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hρA0 : ρ (a, -0) = a := by rw [neg_zero, hρ0 a haJT]
    have hW₁ : IsOpen (e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    have hpW₁ : p ∈ e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r :=
      ⟨hpe, by rw [mem_preimage, hep]; exact Metric.mem_ball_self hr⟩
    have hevent : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] 0, s ∈ Icc (0 : ℝ) 1 ∧
        ⇑D (ρ (a, -s)) ∈ e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r ∧ ρ (a, -s) ∈ Pa := by
      refine Filter.inter_mem self_mem_nhdsWithin (Filter.inter_mem ?_ ?_)
      · exact (hφA 0 h0).preimage_mem_nhdsWithin (by
          change e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r ∈ 𝓝 (⇑D (ρ (a, -0)))
          rw [hρA0]
          exact hW₁.mem_nhds hpW₁)
      · exact (hρA 0 h0).preimage_mem_nhdsWithin (by
          rw [hρA0]
          exact hPa)
    intro ε hε
    obtain ⟨s, hs, hsI, ⟨hse, hsb⟩, hsPa⟩ :=
      exists_mem_Ioo_of_eventually_nhdsWithin_Icc hevent ε hε
    refine ⟨s, hs, e (⇑D (ρ (a, -s))), ⟨hsb, ?_⟩, e.left_inv hse⟩
    obtain ⟨-, hGz⟩ := hmemG _ hsb
    rw [e.left_inv hse] at hGz
    obtain ⟨-, -, -, -, hzA, -, hzC⟩ := hGz
    have hsI' : -s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hsI.2], by linarith [hs.1]⟩
    have hw0 : (e (⇑D (ρ (a, -s)))).2.2 = 0 := hzA.mp ⟨_, hsPa, rfl⟩
    have hnotpos : ¬0 < (e (⇑D (ρ (a, -s)))).2.1 := by
      intro hpos
      obtain ⟨s', hs', w, hw, hxw⟩ := (hsignA _ hsPa).mp hpos
      have h := hρinj a haJT (-s) hsI' w hw s' ⟨by linarith [hs'.1], hs'.2⟩ hxw
      linarith [hs.1, hs'.1, h.2]
    have hne : (e (⇑D (ρ (a, -s)))).2.1 ≠ 0 := by
      intro hv0
      have hz0 : (e (⇑D (ρ (a, -s)))).2 = 0 := Prod.ext hv0 hw0
      have hmemJT := hcarrier_pre _ (hCdom (hρmaps a haJT (-s) hsI')) (hzC.mpr hz0)
      have := hρJT a haJT (-s) hsI' hmemJT
      linarith [hs.1]
    exact Or.inl (lt_of_le_of_ne (not_lt.mp hnotpos) hne)
  · have hmapsB : MapsTo (fun s : ℝ => (τ a, s)) (Icc (0 : ℝ) 1)
        ((J ∪ T) ×ˢ Icc (-1 : ℝ) 1) :=
      fun s hs => ⟨hτaJT, by linarith [hs.1], hs.2⟩
    have hρB : ContinuousOn (fun s : ℝ => ρ (τ a, s)) (Icc (0 : ℝ) 1) :=
      hρpl.isPiecewiseAffineOn.continuousOn.comp (by fun_prop) hmapsB
    have hφB : ContinuousOn (fun s : ℝ => ⇑D (ρ (τ a, s))) (Icc (0 : ℝ) 1) :=
      D.continuousOn.comp hρB fun s hs => hCdom (hρpl.bijOn.mapsTo (hmapsB hs))
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hρB0 : ρ (τ a, 0) = τ a := hρ0 (τ a) hτaJT
    have hDτ : ⇑D (τ a) = p := ((hτfib a haJT (τ a) hτaJT).mpr (Or.inr rfl)).symm
    have hW₁ : IsOpen (e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    have hpW₁ : p ∈ e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r :=
      ⟨hpe, by rw [mem_preimage, hep]; exact Metric.mem_ball_self hr⟩
    have hevent : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] 0, s ∈ Icc (0 : ℝ) 1 ∧
        ⇑D (ρ (τ a, s)) ∈ e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r ∧
          ρ (τ a, s) ∈ Pb := by
      refine Filter.inter_mem self_mem_nhdsWithin (Filter.inter_mem ?_ ?_)
      · exact (hφB 0 h0).preimage_mem_nhdsWithin (by
          change e.source ∩ e ⁻¹' Metric.ball (0 : ℝ × ℝ × ℝ) r ∈ 𝓝 (⇑D (ρ (τ a, 0)))
          rw [hρB0, hDτ]
          exact hW₁.mem_nhds hpW₁)
      · exact (hρB 0 h0).preimage_mem_nhdsWithin (by
          rw [hρB0]
          exact hPb)
    intro ε hε
    obtain ⟨s, hs, hsI, ⟨hse, hsb⟩, hsPb⟩ :=
      exists_mem_Ioo_of_eventually_nhdsWithin_Icc hevent ε hε
    refine ⟨s, hs, e (⇑D (ρ (τ a, s))), ⟨hsb, ?_⟩, e.left_inv hse⟩
    exact Or.inr ((hsignB _ hsPb).mpr ⟨s, ⟨hs.1, hsI.2⟩, τ a, hτaJT, rfl⟩)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
