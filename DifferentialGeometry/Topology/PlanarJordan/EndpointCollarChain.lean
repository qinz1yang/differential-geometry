import DifferentialGeometry.Topology.PlanarJordan.ArcCollar
import DifferentialGeometry.Topology.PlanarJordan.ArcSubdivisionStraightening
import DifferentialGeometry.Topology.Embedding.RealParameter
import DifferentialGeometry.Topology.MetricSpace.Diameter
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology

namespace Schoenflies

theorem exists_shrinking_open_chain_compl_of_polygonal_subarcs
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hpoly : ∀ a b : ℝ, 0 < a → a < b → b ≤ r → IsPolygonal (f '' Icc a b))
    {U : Set Plane} (hU : U ∈ 𝓝 (f 0)) :
    ∃ O : ℕ → Set Plane,
      (∀ n, IsOpen (O n) ∧ IsConnected (O n) ∧ O n ⊆ U \ f '' unitInterval) ∧
      (∀ n, (O n ∩ O (n + 1)).Nonempty) ∧
      (∀ n m, n + 1 < m → Disjoint (O n) (O m)) ∧
      Tendsto O atTop (𝓝 (f 0)).smallSets := by
  obtain ⟨W, hWU, hW, h0W⟩ := mem_nhds_iff.mp hU
  have hpre : f ⁻¹' W ∈ 𝓝[unitInterval] (0 : ℝ) := (hf 0 zero_mem_I) (hW.mem_nhds h0W)
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let c := min (r / 2) (δ / 2)
  have hc : 0 < c := lt_min (half_pos hr) (half_pos hδ)
  have hcr : c < r := (min_le_left _ _).trans_lt (by linarith)
  have hcδ : c < δ := (min_le_right _ _).trans_lt (by linarith)
  have hc1 : c < 1 := hcr.trans_le hr1
  have hprefixW : f '' Icc 0 c ⊆ W := by
    rintro x ⟨s, hs, rfl⟩
    apply hδW
    refine ⟨?_, hs.1, hs.2.trans hc1.le⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1] using hs.2.trans_lt hcδ
  let s (n : ℕ) := c * (1 / 2 : ℝ) ^ n
  have hspos (n : ℕ) : 0 < s n := mul_pos hc (pow_pos (by norm_num) n)
  have hsc (n : ℕ) : s n ≤ c := by
    calc
      s n ≤ c * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hc.le
      _ = c := mul_one _
  have hsI (n : ℕ) : s n ∈ unitInterval := ⟨(hspos n).le, (hsc n).trans hc1.le⟩
  have hsanti : StrictAnti s := by
    apply strictAnti_nat_of_succ_lt
    intro n
    have hp := hspos n
    dsimp [s] at hp ⊢
    rw [pow_succ]
    nlinarith
  have hslim : Tendsto s atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [s, mul_zero] using hp.const_mul c
  let m (n : ℕ) := (s n + s (n + 1)) / 2
  have hm (n : ℕ) : s (n + 1) < m n ∧ m n < s n := by
    have hlt : s (n + 1) < s n := hsanti (Nat.lt_succ_self n)
    dsimp [m]
    constructor <;> linarith
  have hmI (n : ℕ) : m n ∈ unitInterval :=
    ⟨(hspos (n + 1)).le.trans (hm n).1.le, (hm n).2.le.trans (hsI n).2⟩
  have hmstep (n : ℕ) : m (n + 1) < m n := (hm (n + 1)).2.trans (hm n).1
  let K (n : ℕ) := f '' Icc (m (n + 1)) (m n)
  have hKarc (n : ℕ) : IsArcBetween (K n) (f (m (n + 1))) (f (m n)) := by
    simpa only [K, uIcc_of_le (hmstep n).le] using
      isArcBetween_subarc_of_injOn_I hf hi (hmI (n + 1)) (hmI n) (hmstep n).ne
  let R (n : ℕ) := Metric.diam (f '' Icc 0 (s n)) + (1 / 2 : ℝ) ^ n
  have htail (n : ℕ) : Icc 0 (s n) ⊆ unitInterval := Icc_subset_Icc_right (hsI n).2
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have hd := (hf 0 zero_mem_I).tendsto_diam_image_Icc tendsto_const_nhds hslim
      (Eventually.of_forall htail)
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [R, zero_add] using hd.add hp
  have htailBall (n : ℕ) : f '' Icc 0 (s n) ⊆ Metric.ball (f 0) (R n) := by
    intro x hx
    have hbound := (isCompact_Icc.image_of_continuousOn (hf.mono (htail n))).isBounded
    have hdist := Metric.dist_le_diam_of_mem hbound hx
      (mem_image_of_mem f (show 0 ∈ Icc 0 (s n) from ⟨le_rfl, (hspos n).le⟩))
    exact hdist.trans_lt (lt_add_of_pos_right _ (pow_pos (by norm_num) n))
  obtain ⟨g, hg, hgf⟩ := isCompact_I.exists_continuous_leftInvOn hf hi
  let N (n : ℕ) := g ⁻¹' Ioo (s (n + 2)) (s n) ∩ (W ∩ Metric.ball (f 0) (R n))
  have hNopen (n : ℕ) : IsOpen (N n) :=
    (isOpen_Ioo.preimage hg).inter (hW.inter Metric.isOpen_ball)
  have hNP (n : ℕ) : f '' Ioo (s (n + 2)) (s n) ⊆ N n := by
    rintro x ⟨t, ht, rfl⟩
    have htI : t ∈ unitInterval := ⟨(hspos (n + 2)).le.trans ht.1.le, ht.2.le.trans (hsI n).2⟩
    refine ⟨?_, hprefixW (mem_image_of_mem f ⟨htI.1, ht.2.le.trans (hsc n)⟩),
      htailBall n (mem_image_of_mem f ⟨htI.1, ht.2.le⟩)⟩
    change g (f t) ∈ Ioo (s (n + 2)) (s n)
    rwa [hgf htI]
  have hne (n : ℕ) : s (n + 2) < s n := hsanti (by omega)
  choose V hV hVN hPV _ hcollar using fun n =>
    exists_hasArcCollars_of_polygonal_subarc hf hi (hsI (n + 2)) (hsI n) (hne n)
      (hpoly _ _ (hspos (n + 2)) (hne n) ((hsc n).trans hcr.le)) (hNopen n) (hNP n)
  have hKP (n : ℕ) : K n ⊆ f '' Ioo (s (n + 2)) (s n) := by
    apply image_mono
    intro t ht
    exact ⟨(hm (n + 1)).1.trans_le ht.1, ht.2.trans_lt (hm n).2⟩
  have hKsub (n : ℕ) : K n ⊆ V n ∩ f '' unitInterval := fun x hx =>
    ⟨hPV n (hKP n hx),
      image_mono (Icc_subset_Icc (hmI (n + 1)).1 (hmI n).2) hx⟩
  have hKnt (n : ℕ) : (K n).Nontrivial :=
    ⟨f (m (n + 1)), (hKarc n).left_mem, f (m n), (hKarc n).right_mem,
      fun heq => (hmstep n).ne (hi (hmI (n + 1)) (hmI n) heq)⟩
  let C (n : ℕ) := Classical.choice (hcollar n (K n) (hKsub n) (hKarc n).isArc.isCompact
    (hKarc n).isArc.isConnected.isPreconnected (hKnt n))
  have hKmeet (n : ℕ) : (K n ∩ K (n + 1)).Nonempty :=
    ⟨f (m (n + 1)), (hKarc n).left_mem, (hKarc (n + 1)).right_mem⟩
  have hAclosed : IsClosed (f '' unitInterval) := (isCompact_I.image_of_continuousOn hf).isClosed
  obtain ⟨O, hO, hOmeet⟩ := ArcCollar.exists_isOpen_connected_chain hAclosed hV C hKmeet
  have hON (n : ℕ) : O n ⊆ N n := fun _ hx => hVN n ((hO n).2.2.1 hx).1
  refine ⟨O, ?_, hOmeet, ?_, ?_⟩
  · intro n
    exact ⟨(hO n).1, (hO n).2.1, fun x hx => ⟨hWU (hON n hx).2.1, ((hO n).2.2.1 hx).2⟩⟩
  · intro n k hnk
    refine disjoint_left.mpr fun x hx hy => ?_
    have hn : g x ∈ Ioo (s (n + 2)) (s n) := (hON n hx).1
    have hk : g x ∈ Ioo (s (k + 2)) (s k) := (hON k hy).1
    have hle := hsanti.antitone (show n + 2 ≤ k by omega)
    linarith [hn.1, hk.2]
  · exact ((tendsto_closedBall_smallSets (f 0)).comp hRlim).smallSets_mono
      (Eventually.of_forall fun n x hx => Metric.ball_subset_closedBall (hON n hx).2.2)

theorem exists_shrinking_open_chain_compl_arc
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {U : Set Plane} (hU : U ∈ 𝓝 (f 0)) :
    ∃ O : ℕ → Set Plane,
      (∀ n, IsOpen (O n) ∧ IsConnected (O n) ∧ O n ⊆ U \ f '' unitInterval) ∧
      (∀ n, (O n ∩ O (n + 1)).Nonempty) ∧
      (∀ n m, n + 1 < m → Disjoint (O n) (O m)) ∧
      Tendsto O atTop (𝓝 (f 0)).smallSets := by
  obtain ⟨e, hpoly, _, _, _, _⟩ :=
    DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_subarcs_away_from_endpoint
      hf hi (r := 1 / 2) (by norm_num) isOpen_univ (subset_univ _)
  let F := e ∘ f
  have hF : ContinuousOn F unitInterval := e.continuous.comp_continuousOn hf
  have hFi : InjOn F unitInterval := fun x hx y hy hxy => hi hx hy (e.injective hxy)
  have hFpoly (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2) :
      IsPolygonal (F '' Icc a b) := by
    simpa only [F, image_image, Function.comp_def] using hpoly a b ha hab hb
  have hU' : e.symm ⁻¹' U ∈ 𝓝 (F 0) :=
    (e.symm.continuous.tendsto (F 0)) (by simpa only [F, Function.comp_def, e.symm_apply_apply] using hU)
  obtain ⟨O, hO, hmeet, hdis, hlim⟩ := exists_shrinking_open_chain_compl_of_polygonal_subarcs
    hF hFi (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hFpoly hU'
  refine ⟨fun n => e.symm '' O n, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨e.symm.isOpenMap _ (hO n).1,
      (hO n).2.1.image _ e.symm.continuous.continuousOn, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    refine ⟨((hO n).2.2 hy).1, ?_⟩
    rintro ⟨t, ht, heq⟩
    apply ((hO n).2.2 hy).2
    refine ⟨t, ht, ?_⟩
    change e (f t) = y
    rw [heq, e.apply_symm_apply]
  · intro n
    obtain ⟨x, hx, hx'⟩ := hmeet n
    exact ⟨e.symm x, mem_image_of_mem e.symm hx, mem_image_of_mem e.symm hx'⟩
  · intro n m hnm
    refine disjoint_left.mpr ?_
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz := e.symm.injective (hyx.trans hzx.symm)
    exact disjoint_left.mp (hdis n m hnm) hy (hyz.symm ▸ hz)
  · simpa only [F, Function.comp_def, e.symm_apply_apply] using
      ((e.symm.continuous.tendsto (F 0)).image_smallSets.comp hlim)
end Schoenflies
