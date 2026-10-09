/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.FiniteIntervalCuts
import DifferentialGeometry.Topology.PiecewiseLinear.ArcBoundaryCuts
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelIntersection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_model_subarc_of_finite_boundary_intersection
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {u v : E3 → M} {P Q A D : Set E3} {T J : Set M} {η : ℝ → E3}
    (hu : IsPLHomeomorphInto 3 u P) (hv : IsPLHomeomorphInto 3 v Q)
    (hη : IsPLHomeomorphOn η (Icc 0 1) A) (hAQ : A ⊆ Q)
    (hAT : v '' A ⊆ T) (hD : IsPolyhedron D) (hDP : D ⊆ P)
    (hboundary : u '' D ∩ closure (T \ u '' D) = J)
    (hfinite : (v '' A ∩ J).Finite)
    (h0 : v (η 0) ∈ J ∨ v (η 0) ∉ u '' D)
    (h1 : v (η 1) ∈ J ∨ v (η 1) ∉ u '' D)
    (hmeet : (v '' A ∩ (u '' D \ J)).Nonempty) :
    ∃ (B : Set E3) (γ : ℝ → E3), IsPLHomeomorphOn γ (Icc 0 1) B ∧
      B ⊆ D ∧ u '' B ⊆ v '' A ∧
      u (γ 0) ∈ J ∧ u (γ 1) ∈ J ∧ B ∩ u ⁻¹' J = {γ 0, γ 1} := by
  classical
  obtain ⟨x, ⟨y, hyA, hyx⟩, hxD, hxJ⟩ := hmeet
  obtain ⟨t, ht, hty⟩ := hη.bijOn.surjOn hyA
  have hηt : v (η t) = x := congrArg v hty |>.trans hyx
  have ht0 : t ≠ 0 := by
    intro heq
    have htx : v (η 0) = x := heq ▸ hηt
    exact h0.elim (fun h => hxJ (htx ▸ h)) (fun h => h (htx.symm ▸ hxD))
  have ht1 : t ≠ 1 := by
    intro heq
    have htx : v (η 1) = x := heq ▸ hηt
    exact h1.elim (fun h => hxJ (htx ▸ h)) (fun h => h (htx.symm ▸ hxD))
  have hηQ : MapsTo η (Icc 0 1) Q := fun s hs => hAQ (hη.bijOn.mapsTo hs)
  have hc : ContinuousOn (v ∘ η) (Icc 0 1) :=
    hv.continuousOn.comp hη.isPiecewiseAffineOn.continuousOn hηQ
  have hi : InjOn (v ∘ η) (Icc 0 1) := hv.injOn.comp hη.bijOn.injOn hηQ
  have hM : (Icc (0 : ℝ) 1 ∩ (v ∘ η) ⁻¹' J).Finite := by
    apply Set.Finite.of_finite_image (f := v ∘ η) (hfinite.subset ?_)
      (hi.mono inter_subset_left)
    rintro z ⟨r, hr, rfl⟩
    exact ⟨⟨η r, hη.bijOn.mapsTo hr.1, rfl⟩, hr.2⟩
  have hDc : IsClosed (u '' D) :=
    (hD.isCompact.image_of_continuousOn (hu.continuousOn.mono hDP)).isClosed
  obtain ⟨a, b, ha0, hat, htb, hb1, haJ, hbJ, hinside⟩ :=
    exists_subinterval_of_finite_boundary_preimage hc
      (fun r hr => hAT ⟨η r, hη.bijOn.mapsTo hr, rfl⟩) hDc hboundary hM h0 h1
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      (by change v (η t) ∈ u '' D \ J; rw [hηt]; exact ⟨hxD, hxJ⟩)
  have hab : a < b := hat.trans htb
  have hIcc : Icc a b ⊆ Icc (0 : ℝ) 1 := fun r hr =>
    ⟨ha0.trans hr.1, hr.2.trans hb1⟩
  have hIoo : Ioo a b ⊆ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self.trans hIcc
  have hclosed : ∀ r ∈ Icc a b, v (η r) ∈ u '' D := by
    intro r hr
    have hrcl : r ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hr
    have hcl := ((hc r (hIcc hr)).mono hIoo).mem_closure_image hrcl
    have hsub : (v ∘ η) '' Ioo a b ⊆ u '' D := by
      rintro z ⟨s, hs, rfl⟩
      exact (hinside hs).1
    exact closure_minimal hsub hDc hcl
  let C := η '' Icc a b
  have hηab : IsPLHomeomorphOn η (Icc a b) C :=
    hη.restrict (isPLBall_Icc hab).isPolyhedron hIcc
  have hCA : C ⊆ A := (image_mono hIcc).trans hη.image_eq.subset
  have hC : IsPolyhedron C := ((isPLBall_Icc hab).of_isPLHomeomorphOn hηab).isPolyhedron
  have hCD : v '' C ⊆ u '' D := by
    rintro _ ⟨z, ⟨r, hr, rfl⟩, rfl⟩
    exact hclosed r hr
  let g := Function.invFunOn u P
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn g u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hcomp : IsPLHomeomorphOn (g ∘ v) C ((g ∘ v) '' C) :=
    (hv.mono_of_polyhedron hC (hCA.trans hAQ)).isPLHomeomorphOn_invFunOn_comp hC hu
      (hCD.trans (image_mono hDP))
  have hval : ∀ z ∈ C, u (g (v z)) = v z :=
    fun z hz => hright (image_mono hDP (hCD ⟨z, hz, rfl⟩))
  obtain ⟨φ, hφ, hφ0, hφ1⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints
    (by norm_num : (0 : ℝ) < 1) hab
  let γ := (g ∘ v) ∘ η ∘ φ
  have hγ : IsPLHomeomorphOn γ (Icc 0 1) ((g ∘ v) '' C) :=
    (hφ.trans hηab).trans hcomp
  have hγ0 : γ 0 = g (v (η a)) := by simp only [γ, Function.comp_apply, hφ0]
  have hγ1 : γ 1 = g (v (η b)) := by simp only [γ, Function.comp_apply, hφ1]
  have haC : η a ∈ C := ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
  have hbC : η b ∈ C := ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩
  have h0J : u (γ 0) ∈ J := by rw [hγ0, hval _ haC]; exact haJ
  have h1J : u (γ 1) ∈ J := by rw [hγ1, hval _ hbC]; exact hbJ
  refine ⟨(g ∘ v) '' C, γ, hγ, ?_, ?_, h0J, h1J, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hCD ⟨y, hy, rfl⟩
    change g (v y) ∈ D
    rw [← hzy, hleft (hDP hz)]
    exact hz
  · rintro z ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hCA hr, (hval r hr).symm⟩
  · apply Subset.antisymm
    · rintro z ⟨⟨y, ⟨r, hr, rfl⟩, rfl⟩, hzJ⟩
      by_cases hra : r = a
      · exact Or.inl (by rw [hra]; exact hγ0.symm)
      by_cases hrb : r = b
      · exact Or.inr (by rw [hrb]; exact hγ1.symm)
      have hr' : r ∈ Ioo a b :=
        ⟨lt_of_le_of_ne hr.1 (Ne.symm hra), lt_of_le_of_ne hr.2 hrb⟩
      have hrJ : (v ∘ η) r ∈ J := by
        change u (g (v (η r))) ∈ J at hzJ
        rwa [hval _ ⟨r, hr, rfl⟩] at hzJ
      exact ((hinside hr').2 hrJ).elim
    · intro z hz
      refine ⟨(pair_subset (hγ.bijOn.mapsTo (by norm_num))
        (hγ.bijOn.mapsTo (by norm_num))) hz, ?_⟩
      rcases hz with rfl | rfl
      · exact h0J
      · exact h1J

end DifferentialGeometry.Topology.PiecewiseLinear
