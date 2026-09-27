/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import DifferentialGeometry.Topology.PiecewiseLinear.CircleHomotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsCylindricalDiagram.isPLHomeomorphOn_slice {P : Set E} {S : Set F}
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsPLHomeomorphOn (fun x => f (x, t)) P (f '' (P ×ˢ {t})) := by
  have hsep : 0 < t ∨ t < 1 := by
    by_cases h : 0 < t
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hs : IsPLHomeomorphOn f (P ×ˢ {t}) (f '' (P ×ˢ {t})) := by
    simpa only [Icc_self] using hf.isPLHomeomorphOn_strip hP ht.1 ht.2 hsep
  exact (hP.isPLHomeomorphOn_prod_const t).trans hs

omit [FiniteDimensional ℝ F] in
theorem IsCylindricalDiagram.not_nullhomotopic_slice {J : Set E} (hJ : IsPLSphere 1 J)
    {S : Set F} {f : E × ℝ → F} (hf : IsCylindricalDiagram f J S)
    (hends : ∀ x ∈ J, f (x, 0) = f (x, 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ¬ (⟨fun x => ⟨f (x, t), hf.image_eq ▸ ⟨(x, t), ⟨x.property, ht⟩, rfl⟩⟩,
      (hf.isPiecewiseAffineOn.continuousOn.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun x => ⟨x.property, ht⟩)).subtype_mk _⟩ : C(J, S)).Nullhomotopic := by
  let i : C(J, S) := ⟨fun x =>
    ⟨f (x, t), hf.image_eq ▸ ⟨(x, t), ⟨x.property, ht⟩, rfl⟩⟩,
    (hf.isPiecewiseAffineOn.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun x => ⟨x.property, ht⟩)).subtype_mk _⟩
  change ¬ i.Nullhomotopic
  intro h
  obtain ⟨e, he⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends hJ.isPolyhedron.isCompact hends
  let r : C(S, J) := ⟨fun z => (e z).1, continuous_fst.comp e.continuous⟩
  have hri : r.comp i = ContinuousMap.id J := by
    apply ContinuousMap.ext
    intro x
    have he' : e.symm (x, (t : loopCircle)) = i x :=
      Subtype.ext (he x ⟨t, ht⟩)
    change (e (i x)).1 = x
    rw [← he', e.apply_symm_apply]
  have hid : (ContinuousMap.id J).Nullhomotopic := hri ▸ h.comp_right r
  let _ : ContractibleSpace J := (contractible_iff_id_nullhomotopic J).mpr hid
  exact hJ.not_simplyConnectedSpace_one inferInstance

omit [FiniteDimensional ℝ F] in
theorem IsCylindricalDiagram.isConnected_sdiff_slice {P : Set E} {S : Set F}
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f P S) (hP : IsConnected P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsConnected (S \ f '' (P ×ˢ {t})) := by
  have hzero : IsConnected (S \ f '' (P ×ˢ {(0 : ℝ)})) := by
    have hset : S \ f '' (P ×ˢ {(0 : ℝ)}) = f '' (P ×ˢ Ioo (0 : ℝ) 1) := by
      apply Subset.antisymm
      · rintro z ⟨hz, hnot⟩
        obtain ⟨x, hx, rfl⟩ := hf.image_eq.symm ▸ hz
        have hx0 : x.2 ≠ 0 := fun h => hnot ⟨x, ⟨hx.1, h⟩, rfl⟩
        have hx1 : x.2 ≠ 1 := fun h => hnot
          (hf.image_top_eq_bottom ▸ ⟨x, ⟨hx.1, h⟩, rfl⟩)
        exact ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2.1 hx0.symm,
          lt_of_le_of_ne hx.2.2 hx1⟩, rfl⟩
      · rintro z ⟨x, hx, rfl⟩
        refine ⟨hf.image_eq ▸ ⟨x, ⟨hx.1, hx.2.1.le, hx.2.2.le⟩, rfl⟩, ?_⟩
        rintro ⟨y, hy, hyx⟩
        rcases hf.eq_or_endpoints x ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
          y ⟨hy.1, hy.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩ hyx.symm with hxy | hend | hend
        · exact hx.2.1.ne' ((congrArg Prod.snd hxy).trans hy.2)
        · exact hx.2.1.ne' hend.1
        · exact hx.2.2.ne hend.1
    rw [hset]
    exact (hP.prod (isConnected_Ioo zero_lt_one)).image _
      (hf.isPiecewiseAffineOn.continuousOn.mono (prod_mono Subset.rfl Ioo_subset_Icc_self))
  by_cases ht0 : t = 0
  · subst t
    exact hzero
  by_cases ht1 : t = 1
  · subst t
    rw [hf.image_top_eq_bottom]
    exact hzero
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have hset : S \ f '' (P ×ˢ {t}) =
      f '' (P ×ˢ Ico 0 t) ∪ f '' (P ×ˢ Ioc t 1) := by
    apply Subset.antisymm
    · rintro z ⟨hz, hznot⟩
      obtain ⟨x, hx, rfl⟩ := hf.image_eq.symm ▸ hz
      have hxt : x.2 ≠ t := fun h => hznot ⟨x, ⟨hx.1, h⟩, rfl⟩
      rcases lt_or_gt_of_ne hxt with hlt | hgt
      · exact Or.inl ⟨x, ⟨hx.1, hx.2.1, hlt⟩, rfl⟩
      · exact Or.inr ⟨x, ⟨hx.1, hgt, hx.2.2⟩, rfl⟩
    · rintro z (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · have hxI : x ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.1, hx.2.2.le.trans ht.2.le⟩
        refine ⟨hf.image_eq ▸ ⟨x, hxI, rfl⟩, ?_⟩
        rintro ⟨y, hy, hyx⟩
        rcases hf.eq_or_endpoints x hxI y ⟨hy.1, hy.2.symm ▸ ⟨ht.1.le, ht.2.le⟩⟩
          hyx.symm with hxy | hend | hend
        · have hs := congrArg Prod.snd hxy
          exact hx.2.2.ne (hs.trans hy.2)
        · exact ht.2.ne (hy.2.symm.trans hend.2)
        · exact ht.1.ne' (hy.2.symm.trans hend.2)
      · have hxI : x ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hx.1, ht.1.le.trans hx.2.1.le, hx.2.2⟩
        refine ⟨hf.image_eq ▸ ⟨x, hxI, rfl⟩, ?_⟩
        rintro ⟨y, hy, hyx⟩
        rcases hf.eq_or_endpoints x hxI y ⟨hy.1, hy.2.symm ▸ ⟨ht.1.le, ht.2.le⟩⟩
          hyx.symm with hxy | hend | hend
        · have hs := congrArg Prod.snd hxy
          exact hx.2.1.ne' (hs.trans hy.2)
        · exact ht.2.ne (hy.2.symm.trans hend.2)
        · exact ht.1.ne' (hy.2.symm.trans hend.2)
  rw [hset]
  apply IsConnected.union
  · obtain ⟨x, hx⟩ := hP.nonempty
    have htop : f (x, 0) ∈ f '' (P ×ˢ {1}) :=
      hf.image_top_eq_bottom.symm ▸ ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
    obtain ⟨y, hy, heq⟩ := htop
    exact ⟨f (x, 0), ⟨(x, 0), ⟨hx, le_rfl, ht.1⟩, rfl⟩,
      ⟨y, ⟨hy.1, hy.2.symm ▸ ⟨ht.2, le_rfl⟩⟩, heq⟩⟩
  · exact (hP.prod ((convex_Ico (0 : ℝ) t).isConnected ⟨0, le_rfl, ht.1⟩)).image _
      (hf.isPiecewiseAffineOn.continuousOn.mono
        (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.le.trans ht.2.le⟩))
  · exact (hP.prod ((convex_Ioc t (1 : ℝ)).isConnected ⟨1, ht.2, le_rfl⟩)).image _
      (hf.isPiecewiseAffineOn.continuousOn.mono
        (fun _ hz => ⟨hz.1, ht.1.le.trans hz.2.1.le, hz.2.2⟩))

end DifferentialGeometry.Topology.PiecewiseLinear
