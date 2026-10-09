/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RadialBandPush
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskLocalExtension
import DifferentialGeometry.Topology.Homeomorph.ConjugateFamily
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Set Metric Topology Schoenflies

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem conjugateMap_localExtension_apply
    {S : Type*} [TopologicalSpace S] {e : closedBall (0 : Plane) 1 → S}
    {κ : OpenPartialHomeomorph Plane S}
    (hκe : ∀ v : closedBall (0 : Plane) 1, v.val ∈ κ.source → κ v.val = e v)
    (hκc : ∀ v : closedBall (0 : Plane) 1, e v ∈ κ.target → v.val ∈ κ.source)
    (σ : Plane ≃ₜ Plane) {C : Set Plane} (hCs : C ⊆ κ.source) (hσ : EqOn σ id Cᶜ)
    (v : closedBall (0 : Plane) 1) (hv : σ v.val ∈ closedBall (0 : Plane) 1) :
    κ.symm.conjugateMap σ (e v) = e ⟨σ v.val, hv⟩ := by
  by_cases h : e v ∈ κ.target
  · have hvs := hκc v h
    have hsymm : κ.symm (e v) = v.val := by
      rw [← hκe v hvs, κ.left_inv hvs]
    have hσs : σ v.val ∈ κ.source := by
      by_contra hn
      have hnC : σ v.val ∉ C := fun hc => hn (hCs hc)
      have heq : σ (σ v.val) = σ v.val := hσ hnC
      rw [σ.injective heq] at hn
      exact hn hvs
    rw [κ.symm.conjugateMap_of_mem _ (by rwa [κ.symm_source]), hsymm]
    change κ (σ v.val) = _
    exact hκe ⟨σ v.val, hv⟩ hσs
  · have hvs : v.val ∉ κ.source := fun hs => h (by rw [← hκe v hs]; exact κ.map_source hs)
    have hσv : σ v.val = v.val := hσ (fun hc => hvs (hCs hc))
    rw [κ.symm.conjugateMap_of_notMem _ (by rwa [κ.symm_source])]
    congr 1
    exact Subtype.ext hσv.symm

theorem exists_isotopy_shrink_closedBall_embedding
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (e : closedBall (0 : Plane) 1 → S) (he : Continuous e) (hinj : Function.Injective e)
    {W : Set S} (hW : IsOpen W) (hDW : range e ⊆ W) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ G : ℝ → S ≃ₜ S,
      Continuous (fun p : ℝ × S => G p.1 p.2) ∧
      Continuous (fun p : ℝ × S => (G p.1).symm p.2) ∧
      G 0 = Homeomorph.refl S ∧
      (∃ K : Set S, IsCompact K ∧ K ⊆ W ∧ ∀ t, EqOn (G t) id Kᶜ) ∧
      G 1 '' range e = e '' {v | ‖v.val‖ ≤ s} := by
  classical
  have hloc : ∀ u : {u : Plane // ‖u‖ = 1}, ∃ κ : OpenPartialHomeomorph Plane S,
      u.val ∈ κ.source ∧ κ.target ⊆ W ∧
      (∀ v : closedBall (0 : Plane) 1, v.val ∈ κ.source → κ v.val = e v) ∧
      ∀ v : closedBall (0 : Plane) 1, e v ∈ κ.target → v.val ∈ κ.source :=
    fun u => exists_localExtension_of_closedBall_embedding e he hinj hW hDW u.val u.2
  choose κ hκu hκW hκe hκc using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_sphere (0 : Plane) 1)
    (fun u => (κ u).open_source) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, mem_sphere_zero_iff_norm.mp hx⟩, hκu _⟩)
  set ε : ℝ := min (δ / 4) (1 / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  set a : ℝ := 1 - ε with hadef
  set b : ℝ := 1 + ε with hbdef
  set c : ℝ := ε / 2 with hcdef
  have ha : 0 < a := by linarith
  have hc : 0 < c := by linarith
  let β : Plane → Plane → ℝ := fun u y => max 0 (min 1 (2 - 2 * dist y u / ε))
  have hβc : ∀ u, Continuous (β u) := fun u =>
    continuous_const.max (continuous_const.min (continuous_const.sub
      ((continuous_const.mul (continuous_id.dist continuous_const)).div_const _)))
  have hβ01 : ∀ u y, 0 ≤ β u y ∧ β u y ≤ 1 := fun u y =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hβone : ∀ u y, dist y u < ε / 2 → β u y = 1 := by
    intro u y h
    have h1 : 2 * dist y u / ε ≤ 1 := by
      rw [div_le_one₀ hε]
      linarith
    have h2 : 1 ≤ 2 - 2 * dist y u / ε := by linarith
    change max 0 (min 1 (2 - 2 * dist y u / ε)) = 1
    rw [min_eq_left h2, max_eq_right zero_le_one]
  have hβpos : ∀ u y, 0 < β u y → dist y u < ε := by
    intro u y h
    by_contra hn
    have hn' : ε ≤ dist y u := not_lt.mp hn
    have h1 : 2 ≤ 2 * dist y u / ε := by
      rw [le_div_iff₀ hε]
      linarith
    have h0 : β u y = 0 := max_eq_left ((min_le_right _ _).trans (by linarith))
    linarith
  have hrange : ∀ m : ℝ, 0 ≤ m → m ≤ 1 → a < 1 - c * m ∧ 1 - c * m < b := by
    intro m h0 h1
    constructor <;> nlinarith
  have hdist : ∀ x : Plane, a < ‖x‖ → dist x (radialBandDirection a x) = |‖x‖ - 1| := by
    intro x hx
    have hxpos : 0 < ‖x‖ := ha.trans hx
    have hid : ‖x‖ - 1 = (1 - ‖x‖⁻¹) * ‖x‖ := by
      rw [sub_mul, one_mul, inv_mul_cancel₀ hxpos.ne']
    rw [radialBandDirection_of_lt hx, dist_eq_norm,
      show x - ‖x‖⁻¹ • x = (1 - ‖x‖⁻¹) • x by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs, hid, abs_mul, abs_of_pos hxpos]
  have key : ∀ L : List Plane, (∀ u ∈ L, ‖u‖ = 1) →
      ∃ M : Plane → ℝ, Continuous M ∧ (∀ y, 0 ≤ M y ∧ M y ≤ 1) ∧
        (∀ u ∈ L, ∀ y, β u y ≤ M y) ∧ ∃ G : ℝ → S ≃ₜ S,
          Continuous (fun p : ℝ × S => G p.1 p.2) ∧
          Continuous (fun p : ℝ × S => (G p.1).symm p.2) ∧
          G 0 = Homeomorph.refl S ∧
          (∃ K : Set S, IsCompact K ∧ K ⊆ W ∧ ∀ t, EqOn (G t) id Kᶜ) ∧
          G 1 '' range e =
            e '' {v | ‖v.val‖ ≤ 1 - c * M (radialBandDirection a v.val)} := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨fun _ => 0, continuous_const, fun _ => ⟨le_rfl, zero_le_one⟩,
        fun u hu => by simp at hu, fun _ => Homeomorph.refl S, continuous_snd, continuous_snd,
        rfl, ⟨∅, isCompact_empty, empty_subset _, fun _ _ _ => rfl⟩, ?_⟩
      ext y
      simp only [mem_range, mem_image, Set.mem_ofPred_eq, mul_zero, sub_zero]
      constructor
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        exact ⟨v, mem_closedBall_zero_iff.mp v.2, rfl⟩
      · rintro ⟨v, -, rfl⟩
        exact ⟨e v, ⟨v, rfl⟩, rfl⟩
    | cons u L ih =>
      intro hL
      have hu : ‖u‖ = 1 := hL u (by simp)
      obtain ⟨M', hM'c, hM'01, hM'β, G', hG'c, hG'ci, hG'0, ⟨K', hK'c, hK'W, hK'fix⟩,
        hG'img⟩ := ih (fun w hw => hL w (by simp [hw]))
      obtain ⟨w, hw⟩ := hleb u (mem_sphere_zero_iff_norm.mpr hu)
      let P : ℝ × Plane → ℝ := fun z => 1 - c * M' z.2
      let Q : ℝ × Plane → ℝ := fun z => 1 - c * max (M' z.2) (max 0 (min 1 z.1) * β u z.2)
      have hQm : ∀ z : ℝ × Plane, 0 ≤ max (M' z.2) (max 0 (min 1 z.1) * β u z.2) ∧
          max (M' z.2) (max 0 (min 1 z.1) * β u z.2) ≤ 1 := by
        intro z
        have h1 : 0 ≤ max 0 (min 1 z.1) := le_max_left _ _
        have h2 : max 0 (min 1 z.1) ≤ 1 := max_le zero_le_one (min_le_left _ _)
        refine ⟨(hM'01 _).1.trans (le_max_left _ _), max_le (hM'01 _).2 ?_⟩
        nlinarith [hβ01 u z.2]
      have hP : ∀ z, a < P z ∧ P z < b := fun z => hrange _ (hM'01 _).1 (hM'01 _).2
      have hQ : ∀ z, a < Q z ∧ Q z < b := fun z => hrange _ (hQm z).1 (hQm z).2
      have hPc : Continuous P :=
        continuous_const.sub (continuous_const.mul (hM'c.comp continuous_snd))
      have hQc : Continuous Q :=
        continuous_const.sub (continuous_const.mul ((hM'c.comp continuous_snd).max
          ((continuous_const.max (continuous_const.min continuous_fst)).mul
            ((hβc u).comp continuous_snd))))
      obtain ⟨σ, hσc, hσci, hσeq⟩ := exists_radialBandPush_family ha hPc hQc hP hQ
      set C : Set Plane := closedBall u (δ / 2) with hCdef
      have hCs : C ⊆ (κ w).source := (closedBall_subset_ball (by linarith)).trans hw
      have hCc : IsCompact C := isCompact_closedBall _ _
      have hfix : ∀ t, EqOn (σ t) id Cᶜ ∧ EqOn (σ t).symm id Cᶜ := by
        intro t
        have hpt : ∀ x : Plane, x ∉ C →
            radialBandPush a b (fun y => P (t, y)) (fun y => Q (t, y)) x = x ∧
            radialBandPush a b (fun y => Q (t, y)) (fun y => P (t, y)) x = x := by
          intro x hx
          rcases le_or_gt ‖x‖ a with hxa | hxa
          · exact ⟨radialBandPush_of_norm_le (fun y => (hP (t, y)).1) hxa,
              radialBandPush_of_norm_le (fun y => (hQ (t, y)).1) hxa⟩
          rcases le_or_gt b ‖x‖ with hxb | hxb
          · exact ⟨radialBandPush_of_le_norm (fun y => (hP (t, y)).2) hxb,
              radialBandPush_of_le_norm (fun y => (hQ (t, y)).2) hxb⟩
          have hβ0 : β u (radialBandDirection a x) = 0 := by
            by_contra hne
            have hlt := hβpos u _ (lt_of_le_of_ne (hβ01 u _).1 (Ne.symm hne))
            apply hx
            rw [mem_closedBall]
            have h1 := hdist x hxa
            have h2 : |‖x‖ - 1| < ε := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
            calc dist x u ≤ dist x (radialBandDirection a x) +
                  dist (radialBandDirection a x) u := dist_triangle _ _ _
              _ ≤ δ / 2 := by rw [h1]; linarith
          have hPQ : P (t, radialBandDirection a x) = Q (t, radialBandDirection a x) := by
            change 1 - c * M' (radialBandDirection a x) = 1 - c * max (M' (radialBandDirection a x))
              (max 0 (min 1 t) * β u (radialBandDirection a x))
            rw [hβ0, mul_zero, max_eq_left (hM'01 _).1]
          exact ⟨radialBandPush_of_eq hPQ, radialBandPush_of_eq hPQ.symm⟩
        exact ⟨fun x hx => by rw [(hσeq t x).1]; exact (hpt x hx).1,
          fun x hx => by rw [(hσeq t x).2]; exact (hpt x hx).2⟩
      obtain ⟨J, hJc, hJci, hJeq, hJfix⟩ := (κ w).symm.exists_conjugate_homeomorph_family σ
        hσc hσci hCc (by rw [OpenPartialHomeomorph.symm_target]; exact hCs) hfix
      let G : ℝ → S ≃ₜ S := fun t => (G' t).trans (J t)
      have hGc : Continuous (fun p : ℝ × S => G p.1 p.2) :=
        hJc.comp (continuous_fst.prodMk hG'c)
      have hGci : Continuous (fun p : ℝ × S => (G p.1).symm p.2) :=
        hG'ci.comp (continuous_fst.prodMk hJci)
      have hσ0 : ∀ x, σ 0 x = x := by
        intro x
        rw [(hσeq 0 x).1]
        apply radialBandPush_of_eq
        change 1 - c * M' _ = 1 - c * max (M' _) (max 0 (min 1 0) * β u _)
        rw [min_eq_right zero_le_one, max_self, zero_mul, max_eq_left (hM'01 _).1]
      have hG0 : G 0 = Homeomorph.refl S := by
        ext y
        change J 0 (G' 0 y) = y
        rw [hG'0, (hJeq 0 _).1]
        change (κ w).symm.conjugateMap (σ 0) y = y
        by_cases hy : y ∈ (κ w).symm.source
        · rw [(κ w).symm.conjugateMap_of_mem _ hy, hσ0]
          exact (κ w).symm.left_inv hy
        · exact (κ w).symm.conjugateMap_of_notMem _ hy
      have hKc : IsCompact (K' ∪ κ w '' C) :=
        hK'c.union (hCc.image_of_continuousOn ((κ w).continuousOn.mono hCs))
      have hKW : K' ∪ κ w '' C ⊆ W := union_subset hK'W (by
        rintro _ ⟨x, hx, rfl⟩
        exact hκW w ((κ w).map_source (hCs hx)))
      have hKfix : ∀ t, EqOn (G t) id (K' ∪ κ w '' C)ᶜ := by
        intro t y hy
        rw [mem_compl_iff, mem_union, not_or] at hy
        have hyC : y ∉ (κ w).symm.symm '' C := by
          rw [OpenPartialHomeomorph.symm_symm]
          exact hy.2
        change J t (G' t y) = y
        rw [hK'fix t hy.1]
        exact (hJfix t).1 hyC
      have hQ1 : ∀ y, Q (1, y) = 1 - c * max (M' y) (β u y) := by
        intro y
        change 1 - c * max (M' y) (max 0 (min 1 1) * β u y) = _
        rw [min_self, max_eq_right zero_le_one, one_mul]
      have hJ1 : ∀ v : closedBall (0 : Plane) 1, ∀ hv : σ 1 v.val ∈ closedBall (0 : Plane) 1,
          J 1 (e v) = e ⟨σ 1 v.val, hv⟩ := by
        intro v hv
        rw [(hJeq 1 _).1]
        exact conjugateMap_localExtension_apply (hκe w) (hκc w) (σ 1) hCs (hfix 1).1 v hv
      refine ⟨fun y => max (M' y) (β u y), hM'c.max (hβc u), fun y =>
        ⟨(hM'01 y).1.trans (le_max_left _ _), max_le (hM'01 y).2 (hβ01 u y).2⟩, ?_, G, hGc,
        hGci, hG0, ⟨_, hKc, hKW, hKfix⟩, ?_⟩
      · intro u' hu' y
        rcases List.mem_cons.mp hu' with rfl | hu'
        · exact le_max_right _ _
        · exact (hM'β u' hu' y).trans (le_max_left _ _)
      have himg : G 1 '' range e = J 1 '' (G' 1 '' range e) := by
        rw [← image_comp]
        rfl
      rw [himg, hG'img]
      ext y
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        have hle : Q (1, radialBandDirection a v.val) ≤ P (1, radialBandDirection a v.val) := by
          rw [hQ1]
          change _ ≤ 1 - c * M' _
          nlinarith [le_max_left (M' (radialBandDirection a v.val))
            (β u (radialBandDirection a v.val))]
        have hnorm : ‖σ 1 v.val‖ ≤ ‖v.val‖ := by
          rw [(hσeq 1 _).1]
          exact norm_radialBandPush_le_norm ha (fun y => hP (1, y)) (fun y => hQ (1, y)) hle
        have hv1 : σ 1 v.val ∈ closedBall (0 : Plane) 1 :=
          mem_closedBall_zero_iff.mpr (hnorm.trans (mem_closedBall_zero_iff.mp v.2))
        refine ⟨⟨σ 1 v.val, hv1⟩, ?_, (hJ1 v hv1).symm⟩
        change ‖σ 1 v.val‖ ≤ 1 - c * max (M' (radialBandDirection a (σ 1 v.val)))
          (β u (radialBandDirection a (σ 1 v.val)))
        rw [(hσeq 1 _).1, radialBandDirection_radialBandPush ha (fun y => hP (1, y))
          (fun y => hQ (1, y)), ← hQ1]
        exact norm_radialBandPush_le ha (fun y => hP (1, y)) (fun y => hQ (1, y)) hv
      · rintro ⟨v', hv', rfl⟩
        have hv'Q : ‖v'.val‖ ≤ Q (1, radialBandDirection a v'.val) :=
          le_of_le_of_eq hv' (hQ1 _).symm
        have hxn : ‖(σ 1).symm v'.val‖ ≤ 1 - c * M' (radialBandDirection a v'.val) := by
          rw [(hσeq 1 _).2]
          exact norm_radialBandPush_le ha (fun y => hQ (1, y)) (fun y => hP (1, y)) hv'Q
        have hxd : radialBandDirection a ((σ 1).symm v'.val) =
            radialBandDirection a v'.val := by
          rw [(hσeq 1 _).2]
          exact radialBandDirection_radialBandPush ha (fun y => hQ (1, y)) (fun y => hP (1, y)) _
        have hx1 : (σ 1).symm v'.val ∈ closedBall (0 : Plane) 1 :=
          mem_closedBall_zero_iff.mpr (hxn.trans (by
            nlinarith [hM'01 (radialBandDirection a v'.val)]))
        have hσx : σ 1 ((σ 1).symm v'.val) = v'.val := (σ 1).apply_symm_apply _
        refine ⟨e ⟨(σ 1).symm v'.val, hx1⟩, ⟨⟨(σ 1).symm v'.val, hx1⟩, ?_, rfl⟩, ?_⟩
        · change ‖(σ 1).symm v'.val‖ ≤ 1 - c * M' (radialBandDirection a ((σ 1).symm v'.val))
          rw [hxd]
          exact hxn
        · have hv1 : σ 1 ((σ 1).symm v'.val) ∈ closedBall (0 : Plane) 1 := by
            rw [hσx]
            exact v'.2
          rw [hJ1 ⟨(σ 1).symm v'.val, hx1⟩ hv1]
          congr 1
          exact Subtype.ext hσx
  obtain ⟨T, hTs, hTf, hTcov⟩ :=
    finite_cover_balls_of_compact (isCompact_sphere (0 : Plane) 1) (half_pos hε)
  obtain ⟨M, -, hM01, hMβ, G, hGc, hGci, hG0, hK, hGimg⟩ := key hTf.toFinset.toList (by
    intro u hu
    rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hu
    exact mem_sphere_zero_iff_norm.mp (hTs hu))
  refine ⟨1 - c, by linarith, by linarith, G, hGc, hGci, hG0, hK, ?_⟩
  rw [hGimg]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hv
    rcases le_or_gt ‖v.val‖ a with hva | hva
    · linarith
    · have hn1 : ‖radialBandDirection a v.val‖ = 1 := by
        rw [radialBandDirection_of_lt hva, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (ha.trans hva).ne']
      obtain ⟨u, huT, hud⟩ := mem_iUnion₂.mp (hTcov (mem_sphere_zero_iff_norm.mpr hn1))
      have hM1 : M (radialBandDirection a v.val) = 1 := by
        refine le_antisymm (hM01 _).2 ?_
        calc (1 : ℝ) = β u (radialBandDirection a v.val) :=
              (hβone u _ (mem_ball.mp hud)).symm
          _ ≤ M (radialBandDirection a v.val) := hMβ u (by simpa using huT) _
      rw [hM1, mul_one] at hv
      exact hv
  · intro hv
    have := (hM01 (radialBandDirection a v.val)).2
    nlinarith

end DifferentialGeometry.Topology.PiecewiseLinear
