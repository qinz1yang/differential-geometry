/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskShrink

open Set Metric Topology Schoenflies

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_localExtension_of_halfAnnulus_embedding
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (e : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} → S) (he : Continuous e)
    (hinj : Function.Injective e) (u : Plane) (hu : ‖u‖ = 1) :
    ∃ κ : OpenPartialHomeomorph Plane S, u ∈ κ.source ∧
      (∀ v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, v.val ∈ κ.source → κ v.val = e v) ∧
      ∀ v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, e v ∈ κ.target → v.val ∈ κ.source := by
  classical
  set L : Set Plane := closedBall 0 1 ∩ closedBall u (1 / 4) with hLdef
  have hLA : ∀ x ∈ L, 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 := by
    intro x hx
    refine ⟨?_, mem_closedBall_zero_iff.mp hx.1⟩
    have h1 := norm_sub_norm_le u x
    have h2 : ‖u - x‖ ≤ 1 / 4 := by
      rw [← dist_eq_norm, dist_comm]
      exact mem_closedBall.mp hx.2
    linarith
  have hLc : Convex ℝ L := (convex_closedBall _ _).inter (convex_closedBall _ _)
  have hLb : Bornology.IsBounded L := isBounded_closedBall.subset inter_subset_left
  have hLcl : IsClosed L := isClosed_closedBall.inter isClosed_closedBall
  have hLi : (interior L).Nonempty := by
    refine ⟨(7 / 8 : ℝ) • u, ?_⟩
    have hsub : ball (0 : Plane) 1 ∩ ball u (1 / 4) ⊆ L :=
      inter_subset_inter ball_subset_closedBall ball_subset_closedBall
    refine interior_maximal hsub (isOpen_ball.inter isOpen_ball) ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, hu, Real.norm_of_nonneg (by norm_num)]
      norm_num
    · have h78 : (7 / 8 : ℝ) • u - u = (-(1 / 8) : ℝ) • u := by
        rw [show (-(1 / 8) : ℝ) = 7 / 8 - 1 by norm_num, sub_smul, one_smul]
      rw [mem_ball, dist_eq_norm, h78, norm_smul, hu]
      norm_num
  obtain ⟨Γ, -, hΓc, hΓf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hLc hLi hLb
  rw [hLcl.closure_eq] at hΓc
  have hΓL : ∀ x ∈ L, Γ x ∈ closedBall (0 : Plane) 1 := fun x hx => hΓc ▸ ⟨x, hx, rfl⟩
  have hΓLs : ∀ w ∈ closedBall (0 : Plane) 1, Γ.symm w ∈ L := by
    intro w hw
    rw [← hΓc] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rwa [Γ.symm_apply_apply]
  have huL : u ∈ L := ⟨mem_closedBall_zero_iff.mpr hu.le, mem_closedBall_self (by norm_num)⟩
  have huf : u ∈ frontier L := by
    rw [hLcl.frontier_eq]
    refine ⟨huL, fun hi => ?_⟩
    have h1 : interior L ⊆ ball (0 : Plane) 1 := by
      calc interior L ⊆ interior (closedBall (0 : Plane) 1) := interior_mono inter_subset_left
        _ = ball 0 1 := interior_closedBall _ one_ne_zero
    have := mem_ball_zero_iff.mp (h1 hi)
    rw [hu] at this
    exact lt_irrefl 1 this
  have hΓu : ‖Γ u‖ = 1 := by
    have h : Γ u ∈ Γ '' frontier L := ⟨u, huf, rfl⟩
    rw [hΓf] at h
    exact mem_sphere_zero_iff_norm.mp h
  let eL : closedBall (0 : Plane) 1 → S := fun w => e ⟨Γ.symm w.val, hLA _ (hΓLs w.val w.2)⟩
  have heLc : Continuous eL :=
    he.comp ((Γ.symm.continuous.comp continuous_subtype_val).subtype_mk _)
  have heLi : Function.Injective eL := by
    intro w w' h
    have h1 := congrArg Subtype.val (hinj h)
    exact Subtype.ext (Γ.symm.injective h1)
  obtain ⟨κ', hκ'u, -, hκ'e, hκ'c⟩ := exists_localExtension_of_closedBall_embedding eL heLc
    heLi isOpen_univ (subset_univ _) (Γ u) hΓu
  let κ₁ : OpenPartialHomeomorph Plane S := Γ.toOpenPartialHomeomorph.trans κ'
  have hκ₁s : κ₁.source = Γ ⁻¹' κ'.source := by
    rw [OpenPartialHomeomorph.trans_source]
    simp
  have hκ₁app : ∀ x, κ₁ x = κ' (Γ x) := fun x => rfl
  have hκ₁e : ∀ x (hx : x ∈ L), x ∈ κ₁.source → κ₁ x = e ⟨x, hLA x hx⟩ := by
    intro x hx hxs
    rw [hκ₁app]
    have hΓx : Γ x ∈ κ'.source := by
      rw [hκ₁s] at hxs
      exact hxs
    rw [hκ'e ⟨Γ x, hΓL x hx⟩ hΓx]
    change e ⟨Γ.symm (Γ x), _⟩ = _
    congr 1
    exact Subtype.ext (Γ.symm_apply_apply x)
  have hAc : CompactSpace {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} := by
    refine isCompact_iff_compactSpace.mp ?_
    exact (isCompact_closedBall (0 : Plane) 1).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun x hx => mem_closedBall_zero_iff.mpr hx.2
  set K : Set S := e '' {v | 1 / 8 ≤ dist v.val u} with hKdef
  have hKc : IsClosed K := by
    refine (IsCompact.image ?_ he).isClosed
    exact (isClosed_le continuous_const
      (continuous_subtype_val.dist continuous_const)).isCompact
  have hus : u ∈ κ₁.source := by
    rw [hκ₁s]
    exact hκ'u
  have huK : κ₁ u ∉ K := by
    rw [hκ₁e u huL hus]
    rintro ⟨v, hv, hve⟩
    have := hinj hve
    rw [this] at hv
    change 1 / 8 ≤ dist u u at hv
    rw [dist_self] at hv
    norm_num at hv
  set O : Set Plane := ball u (1 / 8) ∩ (κ₁.source ∩ κ₁ ⁻¹' Kᶜ) with hOdef
  have hOo : IsOpen O := isOpen_ball.inter (κ₁.isOpen_inter_preimage hKc.isOpen_compl)
  have huO : u ∈ O := ⟨mem_ball_self (by norm_num), hus, huK⟩
  have hOL : ∀ x ∈ O, ‖x‖ ≤ 1 → x ∈ L := fun x hx h2 =>
    ⟨mem_closedBall_zero_iff.mpr h2, ball_subset_closedBall
      (ball_subset_ball (by norm_num) hx.1)⟩
  let κ := κ₁.restr O
  have hκs : κ.source = O := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hOo]
    exact inter_eq_right.mpr fun x hx => hx.2.1
  have hκapp : ∀ x, κ x = κ₁ x := fun x => rfl
  refine ⟨κ, hκs ▸ huO, fun v hv => ?_, fun v hv => ?_⟩
  · rw [hκs] at hv
    rw [hκapp, hκ₁e v.val (hOL v.val hv v.2.2) hv.2.1]
  · have hy : κ.symm (e v) ∈ κ.source := κ.map_target hv
    have hyv : κ (κ.symm (e v)) = e v := κ.right_inv hv
    rw [hκs] at hy
    rw [hκapp] at hyv
    have hvK : e v ∉ K := by
      rw [← hyv]
      exact hy.2.2
    have hvd : dist v.val u < 1 / 8 := by
      by_contra hn
      exact hvK ⟨v, not_lt.mp hn, rfl⟩
    have hvL : v.val ∈ L := ⟨mem_closedBall_zero_iff.mpr v.2.2,
      mem_closedBall.mpr (by linarith)⟩
    have hvt : eL ⟨Γ v.val, hΓL _ hvL⟩ ∈ κ'.target := by
      have h1 : eL ⟨Γ v.val, hΓL _ hvL⟩ = e v := by
        change e ⟨Γ.symm (Γ v.val), _⟩ = e v
        congr 1
        exact Subtype.ext (Γ.symm_apply_apply _)
      have h2 : κ.symm (e v) ∈ κ₁.source := hy.2.1
      rw [hκ₁s] at h2
      rw [h1, ← hyv, hκ₁app]
      exact κ'.map_source h2
    have hvs : v.val ∈ κ₁.source := by
      rw [hκ₁s]
      exact hκ'c _ hvt
    have hvy : v.val = κ.symm (e v) := by
      refine κ₁.injOn hvs hy.2.1 ?_
      rw [hκ₁e v.val hvL hvs, hyv]
    rw [hκs, hvy]
    exact hy

theorem conjugateMap_halfAnnulus_apply
    {S : Type*} [TopologicalSpace S] {e : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} → S}
    {κ : OpenPartialHomeomorph Plane S}
    (hκe : ∀ v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, v.val ∈ κ.source → κ v.val = e v)
    (hκc : ∀ v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, e v ∈ κ.target → v.val ∈ κ.source)
    (σ : Plane ≃ₜ Plane) {C : Set Plane} (hCs : C ⊆ κ.source) (hσ : EqOn σ id Cᶜ)
    (v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}) (hv : 1 / 2 ≤ ‖σ v.val‖ ∧ ‖σ v.val‖ ≤ 1) :
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

theorem half_le_norm_radialBandPush {a b : ℝ} {P Q : Plane → ℝ} (ha : 1 / 2 ≤ a)
    (hP : ∀ u, a < P u ∧ P u < b) (hQ : ∀ u, a < Q u ∧ Q u < b) {x : Plane}
    (hx : 1 / 2 ≤ ‖x‖) : 1 / 2 ≤ ‖radialBandPush a b P Q x‖ := by
  rcases le_or_gt ‖x‖ a with hxa | hxa
  · rw [radialBandPush_of_norm_le (fun u => (hP u).1) hxa]
    exact hx
  · rw [norm_radialBandPush (by linarith) hP hQ hxa]
    have := lt_radialProfile (hP (radialBandDirection a x)).1 (hP (radialBandDirection a x)).2
      (hQ (radialBandDirection a x)).1 (hQ (radialBandDirection a x)).2 hxa
    linarith

theorem exists_isotopy_shrink_halfAnnulus_outer
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (e : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} → S) (he : Continuous e)
    (hinj : Function.Injective e) :
    ∃ s : ℝ, 1 / 2 < s ∧ s < 1 ∧ ∃ G : ℝ → S ≃ₜ S,
      Continuous (fun p : ℝ × S => G p.1 p.2) ∧
      Continuous (fun p : ℝ × S => (G p.1).symm p.2) ∧
      G 0 = Homeomorph.refl S ∧
      G 1 '' range e = e '' {v | ‖v.val‖ ≤ s} := by
  classical
  have hloc : ∀ u : {u : Plane // ‖u‖ = 1}, ∃ κ : OpenPartialHomeomorph Plane S,
      u.val ∈ κ.source ∧
      (∀ v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, v.val ∈ κ.source → κ v.val = e v) ∧
      ∀ v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, e v ∈ κ.target → v.val ∈ κ.source :=
    fun u => exists_localExtension_of_halfAnnulus_embedding e he hinj u.val u.2
  choose κ hκu hκe hκc using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_sphere (0 : Plane) 1)
    (fun u => (κ u).open_source) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, mem_sphere_zero_iff_norm.mp hx⟩, hκu _⟩)
  set ε : ℝ := min (δ / 4) (1 / 4) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hε1 : ε ≤ 1 / 4 := min_le_right _ _
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
          G 1 '' range e =
            e '' {v | ‖v.val‖ ≤ 1 - c * M (radialBandDirection a v.val)} := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨fun _ => 0, continuous_const, fun _ => ⟨le_rfl, zero_le_one⟩,
        fun u hu => by simp at hu, fun _ => Homeomorph.refl S, continuous_snd, continuous_snd,
        rfl, ?_⟩
      ext y
      simp only [mem_range, mem_image, Set.mem_ofPred_eq, mul_zero, sub_zero]
      constructor
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        exact ⟨v, v.2.2, rfl⟩
      · rintro ⟨v, -, rfl⟩
        exact ⟨e v, ⟨v, rfl⟩, rfl⟩
    | cons u L ih =>
      intro hL
      have hu : ‖u‖ = 1 := hL u (by simp)
      obtain ⟨M', hM'c, hM'01, hM'β, G', hG'c, hG'ci, hG'0, hG'img⟩ :=
        ih (fun w hw => hL w (by simp [hw]))
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
      have hQ1 : ∀ y, Q (1, y) = 1 - c * max (M' y) (β u y) := by
        intro y
        change 1 - c * max (M' y) (max 0 (min 1 1) * β u y) = _
        rw [min_self, max_eq_right zero_le_one, one_mul]
      have hJ1 : ∀ v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1},
          ∀ hv : 1 / 2 ≤ ‖σ 1 v.val‖ ∧ ‖σ 1 v.val‖ ≤ 1,
          J 1 (e v) = e ⟨σ 1 v.val, hv⟩ := by
        intro v hv
        rw [(hJeq 1 _).1]
        exact conjugateMap_halfAnnulus_apply (hκe w) (hκc w) (σ 1) hCs (hfix 1).1 v hv
      refine ⟨fun y => max (M' y) (β u y), hM'c.max (hβc u), fun y =>
        ⟨(hM'01 y).1.trans (le_max_left _ _), max_le (hM'01 y).2 (hβ01 u y).2⟩, ?_, G, hGc,
        hGci, hG0, ?_⟩
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
        have hv1 : 1 / 2 ≤ ‖σ 1 v.val‖ ∧ ‖σ 1 v.val‖ ≤ 1 := by
          refine ⟨?_, hnorm.trans v.2.2⟩
          rw [(hσeq 1 _).1]
          exact half_le_norm_radialBandPush (by linarith) (fun y => hP (1, y))
            (fun y => hQ (1, y)) v.2.1
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
        have hx1 : 1 / 2 ≤ ‖(σ 1).symm v'.val‖ ∧ ‖(σ 1).symm v'.val‖ ≤ 1 := by
          refine ⟨?_, hxn.trans (by nlinarith [hM'01 (radialBandDirection a v'.val)])⟩
          rw [(hσeq 1 _).2]
          exact half_le_norm_radialBandPush (by linarith) (fun y => hQ (1, y))
            (fun y => hP (1, y)) v'.2.1
        have hσx : σ 1 ((σ 1).symm v'.val) = v'.val := (σ 1).apply_symm_apply _
        refine ⟨e ⟨(σ 1).symm v'.val, hx1⟩, ⟨⟨(σ 1).symm v'.val, hx1⟩, ?_, rfl⟩, ?_⟩
        · change ‖(σ 1).symm v'.val‖ ≤ 1 - c * M' (radialBandDirection a ((σ 1).symm v'.val))
          rw [hxd]
          exact hxn
        · have hv1 : 1 / 2 ≤ ‖σ 1 ((σ 1).symm v'.val)‖ ∧ ‖σ 1 ((σ 1).symm v'.val)‖ ≤ 1 := by
            rw [hσx]
            exact v'.2
          rw [hJ1 ⟨(σ 1).symm v'.val, hx1⟩ hv1]
          congr 1
          exact Subtype.ext hσx
  obtain ⟨T, hTs, hTf, hTcov⟩ :=
    finite_cover_balls_of_compact (isCompact_sphere (0 : Plane) 1) (half_pos hε)
  obtain ⟨M, -, hM01, hMβ, G, hGc, hGci, hG0, hGimg⟩ := key hTf.toFinset.toList (by
    intro u hu
    rw [Finset.mem_toList, Set.Finite.mem_toFinset] at hu
    exact mem_sphere_zero_iff_norm.mp (hTs hu))
  refine ⟨1 - c, by linarith, by linarith, G, hGc, hGci, hG0, ?_⟩
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

theorem exists_isotopy_shrink_halfAnnulus
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (e : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} → S) (he : Continuous e)
    (hinj : Function.Injective e) :
    ∃ a b : ℝ, 1 / 2 < a ∧ a < b ∧ b < 1 ∧ ∃ G : ℝ → S ≃ₜ S,
      Continuous (fun p : ℝ × S => G p.1 p.2) ∧
      Continuous (fun p : ℝ × S => (G p.1).symm p.2) ∧ G 0 = Homeomorph.refl S ∧
      G 1 '' range e = e '' {v | a ≤ ‖v.val‖ ∧ ‖v.val‖ ≤ b} := by
  obtain ⟨s₁, hs₁, hs₁', G₁, hG₁c, hG₁i, hG₁0, hG₁img⟩ :=
    exists_isotopy_shrink_halfAnnulus_outer e he hinj
  set ℓ : ℝ → ℝ := fun r => s₁ - (s₁ - 1 / 2) * (2 * r - 1) with hℓ
  have hℓA : ∀ r, 1 / 2 ≤ r → r ≤ 1 → 1 / 2 ≤ ℓ r ∧ ℓ r ≤ s₁ := by
    intro r h1 h2
    constructor
    · change 1 / 2 ≤ s₁ - (s₁ - 1 / 2) * (2 * r - 1)
      nlinarith
    · change s₁ - (s₁ - 1 / 2) * (2 * r - 1) ≤ s₁
      nlinarith
  have hnorm : ∀ x : Plane, 1 / 2 ≤ ‖x‖ → ‖x‖ ≤ 1 → ‖(ℓ ‖x‖ / ‖x‖) • x‖ = ℓ ‖x‖ := by
    intro x h1 h2
    have hx : 0 < ‖x‖ := by linarith
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by linarith [(hℓA _ h1 h2).1]) hx.le),
      div_mul_cancel₀ _ hx.ne']
  let e₂ : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} → S := fun v =>
    e ⟨(ℓ ‖v.val‖ / ‖v.val‖) • v.val, by
      rw [hnorm _ v.2.1 v.2.2]
      exact ⟨(hℓA _ v.2.1 v.2.2).1, (hℓA _ v.2.1 v.2.2).2.trans hs₁'.le⟩⟩
  have he₂c : Continuous e₂ := by
    refine he.comp (Continuous.subtype_mk ?_ _)
    have hn : Continuous fun v : {x : Plane // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} => ‖v.val‖ :=
      continuous_norm.comp continuous_subtype_val
    have hℓc : Continuous ℓ := continuous_const.sub (continuous_const.mul
      ((continuous_const.mul continuous_id).sub continuous_const))
    exact ((hℓc.comp hn).div hn fun v => by linarith [v.2.1]).smul continuous_subtype_val
  have hℓinj : ∀ r r', ℓ r = ℓ r' → r = r' := by
    intro r r' h
    change s₁ - (s₁ - 1 / 2) * (2 * r - 1) = s₁ - (s₁ - 1 / 2) * (2 * r' - 1) at h
    have h2 : (s₁ - 1 / 2) * (r - r') = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  have he₂i : Function.Injective e₂ := by
    intro v w h
    have h1 := congrArg Subtype.val (hinj h)
    change (ℓ ‖v.val‖ / ‖v.val‖) • v.val = (ℓ ‖w.val‖ / ‖w.val‖) • w.val at h1
    have hn := congrArg norm h1
    rw [hnorm _ v.2.1 v.2.2, hnorm _ w.2.1 w.2.2] at hn
    have hvw := hℓinj _ _ hn
    rw [hvw] at h1
    have hne : ℓ ‖w.val‖ / ‖w.val‖ ≠ 0 := by
      have := (hℓA _ w.2.1 w.2.2).1
      have : 0 < ‖w.val‖ := by linarith [w.2.1]
      positivity
    exact Subtype.ext (smul_right_injective Plane hne h1)
  have himg : ∀ s, 1 / 2 ≤ s → s ≤ 1 →
      e₂ '' {v | ‖v.val‖ ≤ s} = e '' {w | ℓ s ≤ ‖w.val‖ ∧ ‖w.val‖ ≤ s₁} := by
    intro s hs hs'
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨_, ?_, rfl⟩
      change ℓ s ≤ ‖(ℓ ‖v.val‖ / ‖v.val‖) • v.val‖ ∧ ‖(ℓ ‖v.val‖ / ‖v.val‖) • v.val‖ ≤ s₁
      rw [hnorm _ v.2.1 v.2.2]
      refine ⟨?_, (hℓA _ v.2.1 v.2.2).2⟩
      change s₁ - (s₁ - 1 / 2) * (2 * s - 1) ≤ s₁ - (s₁ - 1 / 2) * (2 * ‖v.val‖ - 1)
      have hv' : ‖v.val‖ ≤ s := hv
      nlinarith
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      have hwpos : 0 < ‖w.val‖ := by linarith [w.2.1]
      set r : ℝ := 1 / 2 + (s₁ - ‖w.val‖) / (2 * (s₁ - 1 / 2)) with hrdef
      have hden : 0 < 2 * (s₁ - 1 / 2) := by linarith
      have hℓr : ℓ r = ‖w.val‖ := by
        change s₁ - (s₁ - 1 / 2) * (2 * (1 / 2 + (s₁ - ‖w.val‖) / (2 * (s₁ - 1 / 2))) - 1) = _
        have hne : s₁ - 1 / 2 ≠ 0 := by linarith
        have h2 : 2 * (1 / 2 + (s₁ - ‖w.val‖) / (2 * (s₁ - 1 / 2))) - 1 =
            (s₁ - ‖w.val‖) / (s₁ - 1 / 2) := by
          field_simp
          ring
        rw [h2, mul_div_cancel₀ _ hne]
        ring
      have hr1 : 1 / 2 ≤ r := by
        have : 0 ≤ (s₁ - ‖w.val‖) / (2 * (s₁ - 1 / 2)) := div_nonneg (by linarith) hden.le
        linarith
      have hrs : r ≤ s := by
        have h1 : ℓ s ≤ ℓ r := by rw [hℓr]; exact hw1
        change s₁ - (s₁ - 1 / 2) * (2 * s - 1) ≤ s₁ - (s₁ - 1 / 2) * (2 * r - 1) at h1
        nlinarith
      have hrpos : 0 < r := by linarith
      have hvn : ‖(r / ‖w.val‖) • w.val‖ = r := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg hrpos.le hwpos.le),
          div_mul_cancel₀ _ hwpos.ne']
      refine ⟨⟨(r / ‖w.val‖) • w.val, by rw [hvn]; exact ⟨hr1, hrs.trans hs'⟩⟩, ?_, ?_⟩
      · change ‖(r / ‖w.val‖) • w.val‖ ≤ s
        rw [hvn]
        exact hrs
      · change e ⟨(ℓ ‖(r / ‖w.val‖) • w.val‖ / ‖(r / ‖w.val‖) • w.val‖) •
          (r / ‖w.val‖) • w.val, _⟩ = e w
        congr 1
        apply Subtype.ext
        change (ℓ ‖(r / ‖w.val‖) • w.val‖ / ‖(r / ‖w.val‖) • w.val‖) •
          (r / ‖w.val‖) • w.val = w.val
        rw [hvn, hℓr, smul_smul]
        have : ‖w.val‖ / r * (r / ‖w.val‖) = 1 := by field_simp
        rw [this, one_smul]
  have hrange : range e₂ = e '' {v | ‖v.val‖ ≤ s₁} := by
    have h1 : range e₂ = e₂ '' {v | ‖v.val‖ ≤ 1} := by
      rw [← image_univ]
      congr 1
      ext v
      simp only [mem_univ, true_iff]
      exact v.2.2
    rw [h1, himg 1 (by norm_num) le_rfl]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq]
    have hℓ1 : ℓ 1 = 1 / 2 := by
      change s₁ - (s₁ - 1 / 2) * (2 * 1 - 1) = 1 / 2
      ring
    rw [hℓ1]
    exact ⟨fun h => h.2, fun h => ⟨v.2.1, h⟩⟩
  obtain ⟨s₂, hs₂, hs₂', G₂, hG₂c, hG₂i, hG₂0, hG₂img⟩ :=
    exists_isotopy_shrink_halfAnnulus_outer e₂ he₂c he₂i
  refine ⟨ℓ s₂, s₁, ?_, ?_, hs₁', fun t => (G₁ t).trans (G₂ t),
    hG₂c.comp (continuous_fst.prodMk hG₁c), hG₁i.comp (continuous_fst.prodMk hG₂i), ?_, ?_⟩
  · change 1 / 2 < s₁ - (s₁ - 1 / 2) * (2 * s₂ - 1)
    nlinarith
  · change s₁ - (s₁ - 1 / 2) * (2 * s₂ - 1) < s₁
    nlinarith
  · refine Homeomorph.ext fun y => ?_
    change G₂ 0 (G₁ 0 y) = y
    rw [hG₁0, hG₂0]
    rfl
  · have hcomp : ((fun t => (G₁ t).trans (G₂ t)) 1 : S ≃ₜ S) '' range e =
        G₂ 1 '' (G₁ 1 '' range e) := by
      rw [← image_comp]
      rfl
    rw [hcomp, hG₁img, ← hrange, hG₂img, himg s₂ hs₂.le hs₂'.le]

end DifferentialGeometry.Topology.PiecewiseLinear
