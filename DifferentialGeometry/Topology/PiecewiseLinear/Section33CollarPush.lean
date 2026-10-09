/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeRayChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsTube.bijective_fundamentalGroup_map_interior_sdiff
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
    {D Dbd : Finset E3 → Set E3} {h : E3 → E3} (ht : IsTube K N C D Dbd h N')
    (hWM : interior N' \ h '' K.space ⊆ N' \ h '' K.space)
    (x : ↥(interior N' \ h '' K.space)) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hWM, continuous_inclusion hWM⟩ :
        C(↥(interior N' \ h '' K.space), ↥(N' \ h '' K.space))) x) := by
  obtain ⟨Y, Φ, -, hΦc, hΦN, -, hΦnK, hΦint, hΦ0, -, β, τ, hβc, hτc, hinv⟩ :=
    ht.exists_rayChart
  have hlev : ∀ z ∈ N' \ h '' K.space, ∀ s ∈ Icc (0 : ℝ) 1,
      max (τ z) (s / 2) ∈ Ico (0 : ℝ) 1 := by
    intro z hz s hs
    obtain ⟨-, hτ, -⟩ := hinv z hz
    refine ⟨le_max_of_le_left hτ.1, max_lt hτ.2 ?_⟩
    linarith [hs.2]
  have hGM : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ N' \ h '' K.space,
      Φ (β z) (max (τ z) (s / 2)) ∈ N' \ h '' K.space := by
    intro s hs z hz
    have hl := hlev z hz s hs
    exact ⟨hΦN _ (hinv z hz).1 _ ⟨hl.1, hl.2.le⟩, hΦnK _ (hinv z hz).1 _ hl⟩
  have hGint : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ N' \ h '' K.space, 0 < max (τ z) (s / 2) →
      Φ (β z) (max (τ z) (s / 2)) ∈ interior N' \ h '' K.space := by
    intro s hs z hz hpos
    have hl := hlev z hz s hs
    exact ⟨hΦint _ (hinv z hz).1 _ ⟨hpos, hl.2⟩, hΦnK _ (hinv z hz).1 _ hl⟩
  have hτpos : ∀ z ∈ interior N' \ h '' K.space, 0 < τ z := by
    intro z hz
    obtain ⟨hβ, hτ, heq⟩ := hinv z (hWM hz)
    rcases eq_or_lt_of_le hτ.1 with h0 | h0
    · exfalso
      have h1 : Φ (β z) 0 = z := by
        rw [h0]
        exact heq
      apply hΦ0 _ hβ
      rw [h1]
      exact hz.1
    · exact h0
  have hG0 : ∀ z ∈ N' \ h '' K.space, Φ (β z) (max (τ z) ((0 : ℝ) / 2)) = z := by
    intro z hz
    rw [zero_div, max_eq_left (hinv z hz).2.1.1]
    exact (hinv z hz).2.2
  have hGc : ContinuousOn (fun q : ℝ × E3 => Φ (β q.2) (max (τ q.2) (q.1 / 2)))
      (Icc (0 : ℝ) 1 ×ˢ (N' \ h '' K.space)) := by
    have h1 : ContinuousOn (fun q : ℝ × E3 => β q.2) (Icc (0 : ℝ) 1 ×ˢ (N' \ h '' K.space)) :=
      hβc.comp continuous_snd.continuousOn fun q hq => hq.2
    have h2 : ContinuousOn (fun q : ℝ × E3 => τ q.2) (Icc (0 : ℝ) 1 ×ˢ (N' \ h '' K.space)) :=
      hτc.comp continuous_snd.continuousOn fun q hq => hq.2
    have h3 : ContinuousOn (fun q : ℝ × E3 => max (τ q.2) (q.1 / 2))
        (Icc (0 : ℝ) 1 ×ˢ (N' \ h '' K.space)) :=
      h2.sup (continuous_fst.div_const 2).continuousOn
    have hin : ContinuousOn (fun q : ℝ × E3 => (β q.2, max (τ q.2) (q.1 / 2)))
        (Icc (0 : ℝ) 1 ×ˢ (N' \ h '' K.space)) := h1.prodMk h3
    exact hΦc.comp hin fun q hq => ⟨(hinv q.2 hq.2).1, (hlev q.2 hq.2 q.1 hq.1).1,
      (hlev q.2 hq.2 q.1 hq.1).2.le⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  let ρ : C(↥(N' \ h '' K.space), ↥(interior N' \ h '' K.space)) :=
    ⟨fun z => ⟨Φ (β z) (max (τ z) (1 / 2)), hGint 1 hone z z.2
      (lt_max_of_lt_right (by norm_num))⟩,
      (hGc.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        fun z => ⟨hone, z.2⟩).subtype_mk _⟩
  let ι : C(↥(interior N' \ h '' K.space), ↥(N' \ h '' K.space)) :=
    ⟨Set.inclusion hWM, continuous_inclusion hWM⟩
  have hsI : ∀ s : unitInterval, (1 - (s : ℝ)) ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨sub_nonneg.mpr s.2.2, sub_le_self _ s.2.1⟩
  let HL : ContinuousMap.Homotopy (ρ.comp ι) (ContinuousMap.id _) :=
    { toFun := fun q => ⟨Φ (β q.2) (max (τ q.2) ((1 - (q.1 : ℝ)) / 2)),
        hGint _ (hsI q.1) q.2 (hWM q.2.2) (lt_max_of_lt_left (hτpos q.2 q.2.2))⟩
      continuous_toFun := (hGc.comp_continuous
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))
        fun q => ⟨hsI q.1, hWM q.2.2⟩).subtype_mk _
      map_zero_left := fun w => by
        apply Subtype.ext
        simp only [Set.Icc.coe_zero, sub_zero]
        rfl
      map_one_left := fun w => by
        apply Subtype.ext
        simp only [Set.Icc.coe_one, sub_self]
        exact hG0 w (hWM w.2) }
  let HR : ContinuousMap.Homotopy (ι.comp ρ) (ContinuousMap.id _) :=
    { toFun := fun q => ⟨Φ (β q.2) (max (τ q.2) ((1 - (q.1 : ℝ)) / 2)),
        hGM _ (hsI q.1) q.2 q.2.2⟩
      continuous_toFun := (hGc.comp_continuous
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))
        fun q => ⟨hsI q.1, q.2.2⟩).subtype_mk _
      map_zero_left := fun z => by
        apply Subtype.ext
        simp only [Set.Icc.coe_zero, sub_zero]
        rfl
      map_one_left := fun z => by
        apply Subtype.ext
        simp only [Set.Icc.coe_one, sub_self]
        exact hG0 z z.2 }
  let e : ContinuousMap.HomotopyEquiv ↥(interior N' \ h '' K.space) ↥(N' \ h '' K.space) :=
    { toFun := ι
      invFun := ρ
      left_inv := ⟨HL⟩
      right_inv := ⟨HR⟩ }
  have hbase : e.toFun x = e.toFun x := rfl
  have hbij := fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv e x (e.toFun x) hbase
  have hmaps : FundamentalGroup.mapOfEq e.toFun hbase = FundamentalGroup.map ι x := by
    ext g
    rw [FundamentalGroup.mapOfEq_apply]
    rw [show hbase = rfl from Subsingleton.elim _ _, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rw [hmaps] at hbij
  exact hbij

end DifferentialGeometry.Topology.PiecewiseLinear
