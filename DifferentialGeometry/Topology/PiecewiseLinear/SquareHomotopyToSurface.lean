/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Homotopy.Path
import DifferentialGeometry.Topology.PiecewiseLinear.SquareCrossingChain

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_pos_forall_exists_path_dist_lt {α : Type*} [MetricSpace α] {S : Set α}
    (hS : IsCompact S) [LocallyPathConnectedSpace S] {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ x y : S, dist x y < δ → ∃ γ : Path x y, ∀ t, dist (γ t) x < ρ := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hV : ∀ x : S, ∃ V : Set S, V ∈ 𝓝 x ∧ IsPathConnected V ∧
      V ⊆ Metric.ball x (ρ / 2) := fun x => by
    obtain ⟨V, ⟨hVn, hVp⟩, hVs⟩ :=
      (path_connected_basis x).mem_iff.mp (Metric.ball_mem_nhds x (half_pos hρ))
    exact ⟨V, hVn, hVp, hVs⟩
  choose V hVn hVp hVs using hV
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set S))
    (c := fun x => interior (V x)) isCompact_univ (fun x => isOpen_interior)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hVn x)⟩)
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  obtain ⟨z, hz⟩ := hleb x (mem_univ x)
  have hx : x ∈ V z := interior_subset (hz (Metric.mem_ball_self hδ))
  have hy : y ∈ V z := interior_subset (hz (by rw [Metric.mem_ball, dist_comm]; exact hxy))
  obtain ⟨γ, hγ⟩ := (hVp z).joinedIn x hx y hy
  refine ⟨γ, fun t => ?_⟩
  have h1 := hVs z (hγ t)
  have h2 := hVs z hx
  rw [Metric.mem_ball] at h1 h2
  calc dist (γ t) x ≤ dist (γ t) z + dist z x := dist_triangle _ _ _
    _ < ρ / 2 + ρ / 2 := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = ρ := by ring

theorem path_homotopic_of_forall_mem_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W B : Set E} (hB : Convex ℝ B) (hBW : B ⊆ W) {a b : W}
    (α β : Path a b) (hα : ∀ t, (α t : E) ∈ B) (hβ : ∀ t, (β t : E) ∈ B) : α.Homotopic β := by
  refine ⟨{
    toFun := fun q => ⟨(1 - (q.1 : ℝ)) • (α q.2 : E) + (q.1 : ℝ) • (β q.2 : E),
      hBW (hB (hα q.2) (hβ q.2) (sub_nonneg.mpr q.1.2.2) q.1.2.1 (sub_add_cancel 1 _))⟩
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp (α.continuous.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp (β.continuous.comp continuous_snd)))
    map_zero_left := fun t => by
      apply Subtype.ext
      simp
    map_one_left := fun t => by
      apply Subtype.ext
      simp
    prop' := fun s x hx => by
      apply Subtype.ext
      rcases hx with rfl | hx
      · simp only [ContinuousMap.coe_mk, Path.coe_toContinuousMap, Path.source]
        rw [← add_smul, sub_add_cancel, one_smul]
      · rw [mem_singleton_iff] at hx
        subst hx
        simp only [ContinuousMap.coe_mk, Path.coe_toContinuousMap, Path.target]
        rw [← add_smul, sub_add_cancel, one_smul] }⟩

theorem exists_surface_path_homotopic_of_square {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W S O₁ O₂ : Set E} (hW : IsOpen W) (hS : IsCompact S) (hSW : S ⊆ W)
    [LocallyPathConnectedSpace S] (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hO : Disjoint O₁ O₂)
    (hWS : W \ S ⊆ O₁ ∪ O₂) {Ψ : ℝ × ℝ → E}
    (hΨc : ContinuousOn Ψ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hΨW : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Ψ q ∈ W) {x₀ : S}
    (hΨL : ∀ u ∈ Icc (0 : ℝ) 1, Ψ (0, u) = x₀) (hΨR : ∀ u ∈ Icc (0 : ℝ) 1, Ψ (1, u) = x₀)
    (hbot : ∀ s ∈ Icc (0 : ℝ) 1, Ψ (s, 0) ∈ O₁ ∪ S)
    (htop : ∀ s ∈ Icc (0 : ℝ) 1, Ψ (s, 1) ∈ O₂ ∪ S)
    (γ : Path (Set.inclusion hSW x₀) (Set.inclusion hSW x₀))
    (hγ : ∀ t : unitInterval, (γ t : E) = Ψ ((t : ℝ), 0)) :
    ∃ σ : Path x₀ x₀, γ.Homotopic (σ.map (continuous_inclusion hSW)) := by
  classical
  have hQconv : Convex ℝ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := (convex_Icc 0 1).prod (convex_Icc 0 1)
  have hQc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hq₀ : ((0 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := ⟨h01, h01⟩
  have hq₁ : ((1 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := ⟨h11, h01⟩
  let ΨQ : C(↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), W) :=
    ⟨fun q => ⟨Ψ q, hΨW q q.2⟩,
      (hΨc.comp_continuous continuous_subtype_val fun q => q.2).subtype_mk _⟩
  let inclS : C(S, W) := ⟨Set.inclusion hSW, continuous_inclusion hSW⟩
  have : ContractibleSpace ↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hQconv.contractibleSpace ⟨_, hq₀⟩
  let segQ : ∀ p q : ↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), Path p q := fun p q =>
    { toFun := fun t => ⟨(1 - (t : ℝ)) • (p : ℝ × ℝ) + (t : ℝ) • (q : ℝ × ℝ),
        hQconv p.2 q.2 (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 _)⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
          (continuous_subtype_val.smul continuous_const)
      source' := by
        apply Subtype.ext
        simp
      target' := by
        apply Subtype.ext
        simp }
  have hsegQ : ∀ (p q : ↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) (t : unitInterval),
      dist ((segQ p q t : ℝ × ℝ)) (p : ℝ × ℝ) ≤ dist (q : ℝ × ℝ) (p : ℝ × ℝ) := by
    intro p q t
    change dist ((1 - (t : ℝ)) • (p : ℝ × ℝ) + (t : ℝ) • (q : ℝ × ℝ)) (p : ℝ × ℝ) ≤ _
    rw [dist_eq_norm, dist_eq_norm]
    have heq : (1 - (t : ℝ)) • (p : ℝ × ℝ) + (t : ℝ) • (q : ℝ × ℝ) - (p : ℝ × ℝ) =
        (t : ℝ) • ((q : ℝ × ℝ) - (p : ℝ × ℝ)) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    rw [heq, norm_smul, Real.norm_of_nonneg t.2.1]
    exact mul_le_of_le_one_left (norm_nonneg _) t.2.2
  obtain ⟨ρ, hρ, hρW⟩ := (hQc.image_of_continuousOn hΨc).exists_thickening_subset_open hW
    (image_subset_iff.mpr hΨW)
  have hball : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Metric.ball (Ψ q) ρ ⊆ W := fun q hq =>
    (Metric.ball_subset_thickening (mem_image_of_mem Ψ hq) ρ).trans hρW
  obtain ⟨δ₂, hδ₂, hS2⟩ := exists_pos_forall_exists_path_dist_lt hS (half_pos hρ)
  obtain ⟨δ₁, hδ₁, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hQc.uniformContinuousOn_of_continuous hΨc) (min (ρ / 2) δ₂) (lt_min (half_pos hρ) hδ₂)
  have hno : ∀ c : Set (ℝ × ℝ), IsPreconnected c →
      c ⊆ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \
        {q | q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∧ Ψ q ∈ S} →
      ∀ a ∈ c, ∀ b ∈ c, a.2 = 0 → b.2 = 1 → False := by
    intro c hc hcQ a ha b hb ha0 hb1
    have hcQ' : c ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun z hz => (hcQ hz).1
    have hcS : ∀ z ∈ c, Ψ z ∉ S := fun z hz hS' => (hcQ hz).2 ⟨(hcQ hz).1, hS'⟩
    have hΨc' : IsPreconnected (Ψ '' c) := hc.image Ψ (hΨc.mono hcQ')
    have hsub : Ψ '' c ⊆ O₁ ∪ O₂ := by
      rintro _ ⟨z, hz, rfl⟩
      exact hWS ⟨hΨW z (hcQ' hz), hcS z hz⟩
    have haO : Ψ a ∈ O₁ := by
      have ha' : a = (a.1, 0) := Prod.ext rfl ha0
      have hbot' := hbot a.1 (hcQ' ha).1
      rw [← ha'] at hbot'
      exact hbot'.resolve_right (hcS a ha)
    have hbO : Ψ b ∈ O₂ := by
      have hb' : b = (b.1, 1) := Prod.ext rfl hb1
      have htop' := htop b.1 (hcQ' hb).1
      rw [← hb'] at htop'
      exact htop'.resolve_right (hcS b hb)
    rcases hΨc'.subset_or_subset hO₁ hO₂ hO hsub with h | h
    · exact disjoint_left.mp hO (h ⟨b, hb, rfl⟩) hbO
    · exact disjoint_left.mp hO haO (h ⟨a, ha, rfl⟩)
  obtain ⟨m, g, hg0, hgm, hgG, hgd⟩ := exists_chain_left_right_of_no_crossing
    (G := {q | q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∧ Ψ q ∈ S}) (fun q hq => hq.1)
    (fun u hu => ⟨⟨h01, hu⟩, by rw [hΨL u hu]; exact x₀.2⟩)
    (fun u hu => ⟨⟨h11, hu⟩, by rw [hΨR u hu]; exact x₀.2⟩) hno hδ₁
  have hstep : ∀ k < m, ∀ w w' : ↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), (w : ℝ × ℝ) = g k →
      (w' : ℝ × ℝ) = g (k + 1) → ∀ t : unitInterval,
        dist (Ψ (segQ w w' t)) (Ψ w) < min (ρ / 2) δ₂ := by
    intro k hk w w' hw hw' t
    apply hunif _ (segQ w w' t).2 _ w.2
    calc dist (segQ w w' t : ℝ × ℝ) w ≤ dist (w' : ℝ × ℝ) w := hsegQ w w' t
      _ = dist (g (k + 1)) (g k) := by rw [hw, hw']
      _ < δ₁ := by
        rw [dist_comm]
        exact hgd k hk
  have hs₀ : Ψ (0, 0) ∈ S := by
    rw [hΨL 0 h01]
    exact x₀.2
  have claim : ∀ k ≤ m, ∀ w : ↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), (w : ℝ × ℝ) = g k →
      ∀ hwS : Ψ w ∈ S, ∃ (P : Path (⟨(0, 0), hq₀⟩ : ↥(Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) w)
        (σ : Path (⟨Ψ (0, 0), hs₀⟩ : S) ⟨Ψ w, hwS⟩),
        (P.map ΨQ.continuous).Homotopic (σ.map inclS.continuous) := by
    intro k
    induction k with
    | zero =>
      intro _ w hw hwS
      have hw0 : (w : ℝ × ℝ) = (0, 0) := hw.trans hg0
      obtain ⟨τ, hτ⟩ := hS2 ⟨Ψ (0, 0), hs₀⟩ ⟨Ψ w, hwS⟩ (by
        change dist (Ψ (0, 0)) (Ψ w) < δ₂
        rw [hw0, dist_self]
        exact hδ₂)
      refine ⟨segQ ⟨(0, 0), hq₀⟩ w, τ, ?_⟩
      apply path_homotopic_of_forall_mem_convex (convex_ball (Ψ (0, 0)) ρ) (hball _ hq₀)
      · intro t
        change Ψ (segQ ⟨(0, 0), hq₀⟩ w t) ∈ Metric.ball (Ψ (0, 0)) ρ
        have hpt : (segQ ⟨(0, 0), hq₀⟩ w t : ℝ × ℝ) = (0, 0) := by
          change (1 - (t : ℝ)) • ((0 : ℝ), (0 : ℝ)) + (t : ℝ) • (w : ℝ × ℝ) = (0, 0)
          rw [hw0]
          simp
        rw [hpt, Metric.mem_ball, dist_self]
        exact hρ
      · intro t
        change ((τ t : S) : E) ∈ Metric.ball (Ψ (0, 0)) ρ
        rw [Metric.mem_ball]
        exact (hτ t).trans (half_lt_self hρ)
    | succ k ih =>
      intro hk w' hw' hw'S
      have hkQ : g k ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := (hgG k (by omega)).1
      have hkS : Ψ (g k) ∈ S := (hgG k (by omega)).2
      obtain ⟨P, σ, hPσ⟩ := ih (by omega) ⟨g k, hkQ⟩ rfl hkS
      have hd := hstep k (by omega) ⟨g k, hkQ⟩ w' rfl hw'
      obtain ⟨τ, hτ⟩ := hS2 ⟨Ψ (g k), hkS⟩ ⟨Ψ w', hw'S⟩ (by
        have h1 := hd 1
        rw [Path.target] at h1
        change dist (Ψ (g k)) (Ψ w') < δ₂
        rw [dist_comm]
        exact h1.trans_le (min_le_right _ _))
      refine ⟨P.trans (segQ ⟨g k, hkQ⟩ w'), σ.trans τ, ?_⟩
      rw [Path.map_trans, Path.map_trans]
      refine hPσ.hcomp ?_
      apply path_homotopic_of_forall_mem_convex (convex_ball (Ψ (g k)) ρ) (hball _ hkQ)
      · intro t
        change Ψ (segQ ⟨g k, hkQ⟩ w' t) ∈ Metric.ball (Ψ (g k)) ρ
        rw [Metric.mem_ball]
        exact ((hd t).trans_le (min_le_left _ _)).trans (half_lt_self hρ)
      · intro t
        change ((τ t : S) : E) ∈ Metric.ball (Ψ (g k)) ρ
        rw [Metric.mem_ball]
        exact (hτ t).trans (half_lt_self hρ)
  have hs₁ : Ψ (1, 0) ∈ S := by
    rw [hΨR 0 h01]
    exact x₀.2
  obtain ⟨P, σ, hPσ⟩ := claim m le_rfl ⟨(1, 0), hq₁⟩ hgm.symm hs₁
  have hBP := SimplyConnectedSpace.paths_homotopic (segQ ⟨(0, 0), hq₀⟩ ⟨(1, 0), hq₁⟩) P
  have hmap := hBP.map ΨQ
  have e0 : Set.inclusion hSW x₀ = ΨQ ⟨(0, 0), hq₀⟩ := Subtype.ext (hΨL 0 h01).symm
  have e1 : Set.inclusion hSW x₀ = ΨQ ⟨(1, 0), hq₁⟩ := Subtype.ext (hΨR 0 h01).symm
  have hγeq : γ = ((segQ ⟨(0, 0), hq₀⟩ ⟨(1, 0), hq₁⟩).map ΨQ.continuous).cast e0 e1 := by
    ext t
    change (γ t : E) = Ψ ((1 - (t : ℝ)) • ((0 : ℝ), (0 : ℝ)) + (t : ℝ) • ((1 : ℝ), (0 : ℝ)))
    rw [hγ t]
    congr 1
    ext
    · simp
    · simp
  have f0 : x₀ = (⟨Ψ (0, 0), hs₀⟩ : S) := Subtype.ext (hΨL 0 h01).symm
  have f1 : x₀ = (⟨Ψ (1, 0), hs₁⟩ : S) := Subtype.ext (hΨR 0 h01).symm
  refine ⟨σ.cast f0 f1, ?_⟩
  have hfin : (σ.cast f0 f1).map (continuous_inclusion hSW) =
      (σ.map inclS.continuous).cast e0 e1 := by
    ext t
    rfl
  rw [hγeq, hfin]
  exact (hmap.trans hPσ).pathCast e0 e1

end DifferentialGeometry.Topology.PiecewiseLinear
