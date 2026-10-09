/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothedRampPath
import DifferentialGeometry.Topology.PlanarJordan.StripExtension
import DifferentialGeometry.Topology.PlanarJordan.PlanarLocalAffine
import DifferentialGeometry.External.Schoenflies.PolyArcRealize
import DifferentialGeometry.External.Schoenflies.SimpleArc

open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rampPath_max_eq_partial {T : ℕ → ℝ} (hT : Monotone T) (P w₀ : E) (d : ℕ → E)
    {M k : ℕ} (hkM : k ≤ M) {t : ℝ} (hkt : T k ≤ t) (htk : k < M → t ≤ T (k + 1)) :
    rampPath (fun r => max r 0) P T w₀ d M t =
      P + (t - T 0) • w₀ + ∑ j ∈ Finset.range (k + 1), (t - T j) • d j := by
  unfold rampPath
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ M + 1)]
  have h1 : ∑ j ∈ Finset.range (k + 1), max (t - T j) 0 • d j =
      ∑ j ∈ Finset.range (k + 1), (t - T j) • d j :=
    Finset.sum_congr rfl fun j hj => by
      have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [max_eq_left (by linarith [hT hj'])]
  have h2 : ∑ j ∈ Finset.Ico (k + 1) (M + 1), max (t - T j) 0 • d j = 0 :=
    Finset.sum_eq_zero fun j hj => by
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hTj : T (k + 1) ≤ T j := hT hj1
      rw [max_eq_right (by linarith [htk (by omega)]), zero_smul]
  rw [h1, h2, add_zero]

theorem rampPath_partial_telescope (P : E) (T : ℕ → ℝ) (W : ℕ → E) (t : ℝ) (k : ℕ) :
    P + (t - T 0) • W 0 + ∑ j ∈ Finset.range (k + 1), (t - T j) • (W (j + 1) - W j) =
      (P + ∑ j ∈ Finset.range k, (T (j + 1) - T j) • W (j + 1)) + (t - T k) • W (k + 1) := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Finset.range_zero,
      Finset.sum_empty, add_zero, smul_sub]
    abel
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, Finset.sum_range_succ]
    simp only [smul_sub, sub_smul]
    abel

omit [NormedSpace ℝ E] in
theorem sum_range_telescope (W : ℕ → E) (K : ℕ) :
    W 0 + ∑ k ∈ Finset.range K, (W (k + 1) - W k) = W K := by
  rw [Finset.sum_range_sub]
  abel

theorem combination_ne_zero_of_det_ne_zero {x y : Plane} (hxy : Schoenflies.Plane.det x y ≠ 0)
    (μ : ℝ) : (1 - μ) • x + μ • y ≠ 0 := by
  intro h
  have h1 : Schoenflies.Plane.det x ((1 - μ) • x + μ • y) = 0 := by
    rw [h]
    simp [Schoenflies.Plane.det]
  rw [Schoenflies.Plane.det_add_right, Schoenflies.Plane.det_smul_right,
    Schoenflies.Plane.det_smul_right, Schoenflies.Plane.det_self, mul_zero, zero_add] at h1
  have hμ : μ = 0 := (mul_eq_zero.mp h1).resolve_right hxy
  rw [hμ, sub_zero, one_smul, zero_smul, add_zero] at h
  rw [h] at hxy
  simp [Schoenflies.Plane.det] at hxy

theorem isOpen_planeOpenRect (a b c d : ℝ) : IsOpen (planeOpenRect a b c d) :=
  (Schoenflies.Plane.isOpen_coord_gt 0 a).inter ((Schoenflies.Plane.isOpen_coord_lt 0 b).inter
    ((Schoenflies.Plane.isOpen_coord_gt 1 c).inter (Schoenflies.Plane.isOpen_coord_lt 1 d)))

theorem convex_planeOpenRect (a b c d : ℝ) : Convex ℝ (planeOpenRect a b c d) :=
  (Schoenflies.Plane.convex_coord_gt 0 a).inter ((Schoenflies.Plane.convex_coord_lt 0 b).inter
    ((Schoenflies.Plane.convex_coord_gt 1 c).inter (Schoenflies.Plane.convex_coord_lt 1 d)))

theorem mem_planeRect_core {α β W t : ℝ} (hW : 0 < W) (ht : t ∈ Icc α β) :
    Plane.mk t 0 ∈ planeRect α β (-W) W := by
  have h0 : (Plane.mk t 0) 0 = t := by simp
  have h1 : (Plane.mk t 0) 1 = 0 := by simp
  exact ⟨by rw [h0]; exact ht.1, by rw [h0]; exact ht.2, by rw [h1]; linarith,
    by rw [h1]; linarith⟩

theorem exists_core_polyArc {e : Plane → Plane} {α β W τa τb ρ : ℝ}
    (hW : 0 < W) (hρ : 0 < ρ) (hαa : α ≤ τa - 2 * ρ) (hab : τa + 2 * ρ < τb - 2 * ρ)
    (hbβ : τb + 2 * ρ ≤ β)
    (hcont : ContinuousOn e (planeRect α β (-W) W)) (hinj : InjOn e (planeRect α β (-W) W))
    {va vb : Plane}
    (hea : ∀ t, |t - τa| < 2 * ρ → e (Plane.mk t 0) = e (Plane.mk τa 0) + (t - τa) • va)
    (heb : ∀ t, |t - τb| < 2 * ρ → e (Plane.mk t 0) = e (Plane.mk τb 0) + (t - τb) • vb) :
    ∃ (m : ℕ) (B : Schoenflies.PolyArc m),
      B.vertex 0 = e (Plane.mk τa 0) ∧ B.vertex (m + 1) = e (Plane.mk τb 0) ∧
      (∃ c : ℝ, 0 < c ∧ B.vertex 1 - B.vertex 0 = c • va) ∧
      (∃ c : ℝ, 0 < c ∧ B.vertex (m + 1) - B.vertex m = c • vb) ∧
      B.carrier ⊆ e '' planeOpenRect (τa - ρ) (τb + ρ) (-W) W ∧
      ∀ t ∈ Icc α β, (t < τa ∨ τb < t) → e (Plane.mk t 0) ∉ B.carrier := by
  classical
  set R := planeRect α β (-W) W with hR
  have hcore : ∀ t ∈ Icc α β, Plane.mk t 0 ∈ R := fun t ht => mem_planeRect_core hW ht
  have hopenR : ∀ a b : ℝ, α ≤ a → b ≤ β → planeOpenRect a b (-W) W ⊆ R := by
    intro a b ha hb x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2.1.le, hx.2.2.2.le⟩
  set Pa := e (Plane.mk τa 0) with hPa
  set Pb := e (Plane.mk τb 0) with hPb
  have hτa : τa ∈ Icc α β := ⟨by linarith, by linarith⟩
  have hτb : τb ∈ Icc α β := ⟨by linarith, by linarith⟩
  set Ω := e '' planeOpenRect (τa + ρ / 2) (τb - ρ / 2) (-W) W with hΩ
  have hΩsub : planeOpenRect (τa + ρ / 2) (τb - ρ / 2) (-W) W ⊆ R :=
    hopenR _ _ (by linarith) (by linarith)
  have hΩopen : IsOpen Ω := DifferentialGeometry.Topology.invariance_of_domain_isOpen_image
    (isOpen_planeOpenRect _ _ _ _) (hcont.mono hΩsub) (hinj.mono hΩsub)
  have hΩconn : IsPreconnected Ω :=
    (convex_planeOpenRect _ _ _ _).isPreconnected.image e (hcont.mono hΩsub)
  have hmid : ∀ t, τa + ρ / 2 < t → t < τb - ρ / 2 →
      Plane.mk t 0 ∈ planeOpenRect (τa + ρ / 2) (τb - ρ / 2) (-W) W := by
    intro t ht1 ht2
    have h0 : (Plane.mk t 0) 0 = t := by simp
    have h1 : (Plane.mk t 0) 1 = 0 := by simp
    exact ⟨by rw [h0]; exact ht1, by rw [h0]; exact ht2, by rw [h1]; linarith,
      by rw [h1]; linarith⟩
  set a₁ := e (Plane.mk (τa + ρ) 0) with ha₁
  set b₁ := e (Plane.mk (τb - ρ) 0) with hb₁
  have ha₁Ω : a₁ ∈ Ω := ⟨_, hmid _ (by linarith) (by linarith), rfl⟩
  have hb₁Ω : b₁ ∈ Ω := ⟨_, hmid _ (by linarith) (by linarith), rfl⟩
  have hmk_inj : ∀ s t : ℝ, s ∈ Icc α β → t ∈ Icc α β →
      e (Plane.mk s 0) = e (Plane.mk t 0) → s = t := by
    intro s t hs ht h
    have := hinj (hcore s hs) (hcore t ht) h
    have h0 := congrArg (fun x : Plane => x 0) this
    simpa using h0
  have ha₁b₁ : a₁ ≠ b₁ := fun h => by
    have := hmk_inj _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h
    linarith
  obtain ⟨vs, hvs, -, -, hvsΩ, hvsarc⟩ :=
    Schoenflies.exists_simple_poly_of_isPreconnected hΩopen hΩconn ha₁Ω hb₁Ω ha₁b₁
  have ha₁' : a₁ = Pa + ρ • va := by
    rw [ha₁, hea (τa + ρ) (by rw [add_sub_cancel_left, abs_of_pos hρ]; linarith)]
    congr 2
    ring
  have hb₁' : b₁ = Pb + (-ρ) • vb := by
    rw [hb₁, heb (τb - ρ) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hρ]; linarith)]
    congr 2
    ring
  have hsegA : ∀ w ∈ segment ℝ Pa a₁, ∃ t ∈ Icc τa (τa + ρ), w = e (Plane.mk t 0) := by
    intro w hw
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨l, hl, rfl⟩ := hw
    have habs : |τa + l * ρ - τa| < 2 * ρ := by
      rw [add_sub_cancel_left, abs_of_nonneg (by nlinarith [hl.1])]
      nlinarith [hl.2]
    refine ⟨τa + l * ρ, ⟨by nlinarith [hl.1], by nlinarith [hl.2]⟩, ?_⟩
    rw [hea _ habs, AffineMap.lineMap_apply_module', ha₁']
    simp only [add_sub_cancel_left, smul_smul]
    abel
  have hsegB : ∀ w ∈ segment ℝ b₁ Pb, ∃ t ∈ Icc (τb - ρ) τb, w = e (Plane.mk t 0) := by
    intro w hw
    rw [segment_symm, segment_eq_image_lineMap] at hw
    obtain ⟨l, hl, rfl⟩ := hw
    have habs : |τb - l * ρ - τb| < 2 * ρ := by
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by nlinarith [hl.1])]
      nlinarith [hl.2]
    refine ⟨τb - l * ρ, ⟨by nlinarith [hl.2], by nlinarith [hl.1]⟩, ?_⟩
    rw [heb _ habs, AffineMap.lineMap_apply_module', hb₁']
    simp only [add_sub_cancel_left, smul_smul]
    rw [show τb - l * ρ - τb = l * -ρ by ring]
    abel
  set Z := segment ℝ Pa a₁ ∪ Schoenflies.poly vs ∪ segment ℝ b₁ Pb with hZ
  have hZlist : (⋃ A ∈ [segment ℝ Pa a₁, Schoenflies.poly vs, segment ℝ b₁ Pb], A) = Z := by
    ext x
    simp [hZ, or_assoc]
  have hpolyL : ∀ A ∈ [segment ℝ Pa a₁, Schoenflies.poly vs, segment ℝ b₁ Pb],
      Schoenflies.IsPolygonal A := by
    intro A hA
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hA
    rcases hA with rfl | rfl | rfl
    · exact Schoenflies.isPolygonal_segment _ _
    · exact ⟨vs, rfl⟩
    · exact Schoenflies.isPolygonal_segment _ _
  have hZconn : IsPreconnected Z := by
    have h1 : IsPreconnected (segment ℝ Pa a₁ ∪ Schoenflies.poly vs) :=
      (convex_segment Pa a₁).isPreconnected.union a₁ (right_mem_segment ℝ Pa a₁)
        hvsarc.left_mem hvsarc.isArc.isConnected.isPreconnected
    exact h1.union b₁ (Or.inr hvsarc.right_mem) (left_mem_segment ℝ b₁ Pb)
      (convex_segment b₁ Pb).isPreconnected
  have hPaPb : Pa ≠ Pb := fun h => by
    have := hmk_inj _ _ hτa hτb h
    linarith
  obtain ⟨ws, -, -, -, hwsZ, hwsarc⟩ := Schoenflies.exists_simple_poly_of_union hpolyL
    (by rw [hZlist]; exact hZconn) hPaPb (by rw [hZlist]; exact Or.inl (Or.inl
      (left_mem_segment ℝ Pa a₁))) (by rw [hZlist]; exact Or.inr (right_mem_segment ℝ b₁ Pb))
  rw [hZlist] at hwsZ
  obtain ⟨n, A₀, hA₀c, hA₀0, hA₀n⟩ := Schoenflies.exists_preArc_of_isArcBetween hwsarc ⟨ws, rfl⟩
  obtain ⟨m, B, hBc, hB0, hBm⟩ := Schoenflies.PreArc.exists_polyArc n A₀
  have hBZ : B.carrier ⊆ Z := by
    rw [hBc, hA₀c]
    exact hwsZ
  have hB0' : B.vertex 0 = Pa := hB0.trans hA₀0
  have hBm' : B.vertex (m + 1) = Pb := hBm.trans hA₀n
  have hPaΩ : Pa ∉ Ω := by
    rintro ⟨x, hx, hxe⟩
    have := hinj (hΩsub hx) (hcore τa hτa) hxe
    have h0 := hx.1
    rw [this] at h0
    simp at h0
    linarith
  have hPbΩ : Pb ∉ Ω := by
    rintro ⟨x, hx, hxe⟩
    have := hinj (hΩsub hx) (hcore τb hτb) hxe
    have h0 := hx.2.1
    rw [this] at h0
    simp at h0
    linarith
  have hPa_B : Pa ∉ Schoenflies.poly vs ∪ segment ℝ b₁ Pb := by
    rintro (h | h)
    · exact hPaΩ (hvsΩ h)
    · obtain ⟨t, ht, hte⟩ := hsegB Pa h
      have := hmk_inj _ _ hτa ⟨by linarith [ht.1], by linarith [ht.2]⟩ hte
      linarith [ht.1]
  have hPb_A : Pb ∉ segment ℝ Pa a₁ ∪ Schoenflies.poly vs := by
    rintro (h | h)
    · obtain ⟨t, ht, hte⟩ := hsegA Pb h
      have := hmk_inj _ _ hτb ⟨by linarith [ht.1], by linarith [ht.2]⟩ hte
      linarith [ht.2]
    · exact hPbΩ (hvsΩ h)
  have hclA : IsClosed (Schoenflies.poly vs ∪ segment ℝ b₁ Pb) :=
    ((Schoenflies.isCompact_poly vs).union (Schoenflies.isCompact_segment b₁ Pb)).isClosed
  have hclB : IsClosed (segment ℝ Pa a₁ ∪ Schoenflies.poly vs) :=
    ((Schoenflies.isCompact_segment Pa a₁).union (Schoenflies.isCompact_poly vs)).isClosed
  obtain ⟨da, hda, hdaA⟩ := Metric.isOpen_iff.mp hclA.isOpen_compl Pa hPa_B
  obtain ⟨db, hdb, hdbB⟩ := Metric.isOpen_iff.mp hclB.isOpen_compl Pb hPb_A
  have hedge : ∀ (i : ℕ) (s : ℝ), i ≤ m → s ∈ Icc (0 : ℝ) 1 →
      B.vertex i + s • (B.vertex (i + 1) - B.vertex i) ∈ B.carrier := by
    intro i s hi hs
    refine Schoenflies.PolyArc.mem_carrier_iff.mpr ⟨i, hi, ?_⟩
    rw [Schoenflies.PolyArc.edge, segment_eq_image_lineMap]
    exact ⟨s, hs, by rw [AffineMap.lineMap_apply_module', add_comm]⟩
  have hfirst : ∃ c : ℝ, 0 < c ∧ B.vertex 1 - B.vertex 0 = c • va := by
    set u := B.vertex 1 - B.vertex 0 with hu
    have hu0 : u ≠ 0 := sub_ne_zero.mpr (Schoenflies.PolyArc.vertex_ne (A := B) (i := 0)).symm
    set s := min (1 / 2) (da / (2 * (‖u‖ + 1))) with hs
    have hs0 : 0 < s := lt_min (by norm_num) (div_pos hda (by positivity))
    have hs1 : s ≤ 1 / 2 := min_le_left _ _
    have hs2 : s ≤ da / (2 * (‖u‖ + 1)) := min_le_right _ _
    have hw : Pa + s • u ∈ B.carrier := by
      have h := hedge 0 s (Nat.zero_le _) ⟨hs0.le, by linarith⟩
      rw [zero_add] at h
      rw [← hB0']
      exact h
    have hwZ := hBZ hw
    have hdist : dist (Pa + s • u) Pa < da := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
      calc s * ‖u‖ ≤ da / (2 * (‖u‖ + 1)) * ‖u‖ :=
            mul_le_mul_of_nonneg_right hs2 (norm_nonneg u)
        _ < da := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u]
    have hwA : Pa + s • u ∈ segment ℝ Pa a₁ := by
      rcases hwZ with (h | h) | h
      · exact h
      · exact absurd (Or.inl h) (hdaA (mem_ball.mpr hdist))
      · exact absurd (Or.inr h) (hdaA (mem_ball.mpr hdist))
    rw [segment_eq_image_lineMap] at hwA
    obtain ⟨l, hl, hle⟩ := hwA
    rw [AffineMap.lineMap_apply_module', ha₁', add_sub_cancel_left, smul_smul] at hle
    have hsu : s • u = (l * ρ) • va := by
      rw [add_comm] at hle
      exact (add_left_cancel hle).symm
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_smul] at hsu
      exact hu0 ((smul_eq_zero.mp hsu).resolve_left hs0.ne')
    refine ⟨l * ρ / s, div_pos (mul_pos (lt_of_le_of_ne hl.1 (Ne.symm hl0)) hρ) hs0, ?_⟩
    have : u = s⁻¹ • ((l * ρ) • va) := by
      rw [← hsu, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
    rw [this, smul_smul]
    congr 1
    ring
  have hlast : ∃ c : ℝ, 0 < c ∧ B.vertex (m + 1) - B.vertex m = c • vb := by
    set u := B.vertex (m + 1) - B.vertex m with hu
    have hu0 : u ≠ 0 := sub_ne_zero.mpr (Schoenflies.PolyArc.vertex_ne (A := B) (i := m)).symm
    set s := min (1 / 2) (db / (2 * (‖u‖ + 1))) with hs
    have hs0 : 0 < s := lt_min (by norm_num) (div_pos hdb (by positivity))
    have hs1 : s ≤ 1 / 2 := min_le_left _ _
    have hs2 : s ≤ db / (2 * (‖u‖ + 1)) := min_le_right _ _
    have hw := hedge m (1 - s) le_rfl ⟨by linarith, by linarith⟩
    have hweq : B.vertex m + (1 - s) • (B.vertex (m + 1) - B.vertex m) = Pb - s • u := by
      rw [hu, ← hBm']
      simp only [sub_smul, one_smul]
      abel
    rw [hweq] at hw
    have hwZ := hBZ hw
    have hdist : dist (Pb - s • u) Pb < db := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hs0.le]
      calc s * ‖u‖ ≤ db / (2 * (‖u‖ + 1)) * ‖u‖ :=
            mul_le_mul_of_nonneg_right hs2 (norm_nonneg u)
        _ < db := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u]
    have hwB : Pb - s • u ∈ segment ℝ b₁ Pb := by
      rcases hwZ with (h | h) | h
      · exact absurd (Or.inl h) (hdbB (mem_ball.mpr hdist))
      · exact absurd (Or.inr h) (hdbB (mem_ball.mpr hdist))
      · exact h
    rw [segment_symm, segment_eq_image_lineMap] at hwB
    obtain ⟨l, hl, hle⟩ := hwB
    rw [AffineMap.lineMap_apply_module', hb₁', add_sub_cancel_left, smul_smul] at hle
    have hsu : s • u = (l * ρ) • vb := by
      have h1 : (l * -ρ) • vb = -(s • u) := by
        rw [sub_eq_add_neg, add_comm] at hle
        exact add_left_cancel hle
      rw [← neg_neg (s • u), ← h1, ← neg_smul]
      congr 1
      ring
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_smul] at hsu
      exact hu0 ((smul_eq_zero.mp hsu).resolve_left hs0.ne')
    refine ⟨l * ρ / s, div_pos (mul_pos (lt_of_le_of_ne hl.1 (Ne.symm hl0)) hρ) hs0, ?_⟩
    have : u = s⁻¹ • ((l * ρ) • vb) := by
      rw [← hsu, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
    rw [this, smul_smul]
    congr 1
    ring
  refine ⟨m, B, hB0', hBm', hfirst, hlast, ?_, ?_⟩
  · intro w hw
    rcases hBZ hw with (h | h) | h
    · obtain ⟨t, ht, rfl⟩ := hsegA w h
      exact ⟨_, ⟨by simp; linarith [ht.1], by simp; linarith [ht.2], by simp; linarith,
        by simp; linarith⟩, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hvsΩ h
      exact ⟨x, ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2.1, hx.2.2.2⟩, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := hsegB w h
      exact ⟨_, ⟨by simp; linarith [ht.1], by simp; linarith [ht.2], by simp; linarith,
        by simp; linarith⟩, rfl⟩
  · intro t ht hout hmem
    rcases hBZ hmem with (h | h) | h
    · obtain ⟨t', ht', hte⟩ := hsegA _ h
      have := hmk_inj _ _ ht ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ hte
      rcases hout with h1 | h1 <;> linarith [ht'.1, ht'.2]
    · obtain ⟨x, hx, hxe⟩ := hvsΩ h
      have := hinj (hΩsub hx) (hcore t ht) hxe
      rw [this] at hx
      have h1 := hx.1
      have h2 := hx.2.1
      simp at h1 h2
      rcases hout with h3 | h3 <;> linarith
    · obtain ⟨t', ht', hte⟩ := hsegB _ h
      have := hmk_inj _ _ ht ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ hte
      rcases hout with h1 | h1 <;> linarith [ht'.1, ht'.2]

theorem exists_index_of_mem_Icc {τa h t : ℝ} (hh : 0 < h) {m : ℕ}
    (ht : t ∈ Icc τa (τa + (m + 1) * h)) :
    ∃ k ≤ m, τa + k * h ≤ t ∧ t ≤ τa + (k + 1) * h := by
  set q := ⌊(t - τa) / h⌋₊ with hq
  have hq0 : 0 ≤ (t - τa) / h := div_nonneg (by linarith [ht.1]) hh.le
  have hqle : (q : ℝ) ≤ (t - τa) / h := Nat.floor_le hq0
  have hqlt : (t - τa) / h < q + 1 := Nat.lt_floor_add_one _
  have hdiv : (t - τa) / h ≤ m + 1 := by
    rw [div_le_iff₀ hh]
    linarith [ht.2]
  by_cases hqm : q ≤ m
  · refine ⟨q, hqm, ?_, ?_⟩
    · have := (le_div_iff₀ hh).mp hqle
      linarith
    · have := (div_lt_iff₀ hh).mp hqlt
      linarith
  · push Not at hqm
    have hqm' : (m : ℝ) + 1 ≤ q := by exact_mod_cast hqm
    refine ⟨m, le_rfl, ?_, by linarith [ht.2]⟩
    have : (m : ℝ) + 1 ≤ (t - τa) / h := hqm'.trans hqle
    have := (le_div_iff₀ hh).mp this
    nlinarith

theorem injOn_mapsTo_polyArc_path {m : ℕ} (B : Schoenflies.PolyArc m) {τa h : ℝ} (hh : 0 < h)
    {p : ℝ → Plane} (hp : ∀ k ≤ m, ∀ t, τa + k * h ≤ t → t ≤ τa + (k + 1) * h →
      p t = B.vertex k + ((t - (τa + k * h)) / h) • (B.vertex (k + 1) - B.vertex k)) :
    InjOn p (Icc τa (τa + (m + 1) * h)) ∧ MapsTo p (Icc τa (τa + (m + 1) * h)) B.carrier := by
  have hedge : ∀ k ≤ m, ∀ t, τa + k * h ≤ t → t ≤ τa + (k + 1) * h →
      p t ∈ segment ℝ (B.vertex k) (B.vertex (k + 1)) := by
    intro k hk t h1 h2
    rw [hp k hk t h1 h2, segment_eq_image_lineMap]
    refine ⟨(t - (τa + k * h)) / h, ⟨div_nonneg (by linarith) hh.le, ?_⟩, ?_⟩
    · rw [div_le_one hh]
      linarith
    · rw [AffineMap.lineMap_apply_module', add_comm]
  refine ⟨?_, fun t ht => ?_⟩
  · have hkey : ∀ s ∈ Icc τa (τa + (m + 1) * h), ∀ t ∈ Icc τa (τa + (m + 1) * h), s < t →
        p s ≠ p t := by
      intro s hs t ht hst heq
      obtain ⟨i, hi, hs1, hs2⟩ := exists_index_of_mem_Icc hh hs
      obtain ⟨j, hj, ht1, ht2⟩ := exists_index_of_mem_Icc hh ht
      have hvinj := B.vertex_inj
      rcases lt_trichotomy i j with hij | rfl | hij
      · have hx1 := hedge i hi s hs1 hs2
        have hx2 := hedge j hj t ht1 ht2
        rw [heq] at hx1
        have hm1 := B.edges_meet i hi j hj hij.ne ⟨hx1, hx2⟩
        have hm2 := B.edges_meet j hj i hi hij.ne' ⟨hx2, hx1⟩
        simp only [mem_insert_iff, mem_singleton_iff] at hm1 hm2
        have hji : j = i + 1 ∧ p t = B.vertex j := by
          rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
          · exact absurd (hvinj (h1.symm.trans h2)) (by omega)
          · exact absurd (hvinj (h1.symm.trans h2)) (by omega)
          · exact ⟨(hvinj (h1.symm.trans h2)).symm, h2⟩
          · exact absurd (hvinj (h1.symm.trans h2)) (by omega)
        obtain ⟨hj1, hpt⟩ := hji
        have hvne : B.vertex (j + 1) - B.vertex j ≠ 0 :=
          sub_ne_zero.mpr (Schoenflies.PolyArc.vertex_ne (A := B) (i := j)).symm
        have hvne' : B.vertex (i + 1) - B.vertex i ≠ 0 :=
          sub_ne_zero.mpr (Schoenflies.PolyArc.vertex_ne (A := B) (i := i)).symm
        rw [hp j hj t ht1 ht2] at hpt
        have hlt : (t - (τa + j * h)) / h = 0 := by
          have : ((t - (τa + j * h)) / h) • (B.vertex (j + 1) - B.vertex j) = 0 := by
            have := congrArg (fun x => x - B.vertex j) hpt
            simpa using this
          exact (smul_eq_zero.mp this).resolve_right hvne
        have hps : p s = B.vertex (i + 1) := by
          rw [heq, hp j hj t ht1 ht2, hlt, zero_smul, add_zero, hj1]
        rw [hp i hi s hs1 hs2] at hps
        have hls : (s - (τa + i * h)) / h = 1 := by
          have h3 : ((s - (τa + i * h)) / h - 1) • (B.vertex (i + 1) - B.vertex i) = 0 := by
            rw [sub_smul, one_smul]
            have := congrArg (fun x => x - B.vertex i) hps
            simp only [add_sub_cancel_left] at this
            rw [this, sub_self]
          have := (smul_eq_zero.mp h3).resolve_right hvne'
          linarith
        have ht0 : t = τa + j * h := by
          have := (div_eq_zero_iff.mp hlt).resolve_right hh.ne'
          linarith
        have hs0 : s = τa + (i + 1) * h := by
          rw [div_eq_one_iff_eq hh.ne'] at hls
          linarith
        rw [hj1] at ht0
        push_cast at ht0
        linarith
      · have h1 := hp i hi s hs1 hs2
        have h2 := hp i hi t ht1 ht2
        rw [heq, h2] at h1
        have hvne : B.vertex (i + 1) - B.vertex i ≠ 0 :=
          sub_ne_zero.mpr (Schoenflies.PolyArc.vertex_ne (A := B) (i := i)).symm
        have h3 : ((t - (τa + i * h)) / h - (s - (τa + i * h)) / h) •
            (B.vertex (i + 1) - B.vertex i) = 0 := by
          rw [sub_smul]
          have := congrArg (fun x => x - B.vertex i) h1
          simp only [add_sub_cancel_left] at this
          rw [this, sub_self]
        have h4 := (smul_eq_zero.mp h3).resolve_right hvne
        rw [← sub_div, div_eq_zero_iff] at h4
        rcases h4 with h4 | h4
        · linarith
        · exact hh.ne' h4
      · have hsi : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij
        nlinarith
    intro s hs t ht heq
    rcases lt_trichotomy s t with h | h | h
    · exact absurd heq (hkey s hs t ht h)
    · exact h
    · exact absurd heq.symm (hkey t ht s hs h)
  · obtain ⟨k, hk, h1, h2⟩ := exists_index_of_mem_Icc hh ht
    exact Schoenflies.PolyArc.mem_carrier_iff.mpr ⟨k, hk, hedge k hk t h1 h2⟩

theorem planeDet_neg_left (x y : Plane) :
    Schoenflies.Plane.det (-x) y = -Schoenflies.Plane.det x y := by
  simp only [Schoenflies.Plane.det, PiLp.neg_apply]
  ring

theorem continuousOn_core_switch {f g : ℝ → Plane} {α β a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc α β))
    (hfa : f a = g a) (hfb : f b = g b) :
    ContinuousOn (fun t => if t ∈ Icc a b then f t else g t) (Icc α β) := by
  apply ContinuousOn.if
  · intro t ⟨_, ht⟩
    have hfr : frontier {t : ℝ | t ∈ Icc a b} ⊆ {a, b} := by
      change frontier (Icc a b) ⊆ {a, b}
      exact (frontier_Icc hab).subset
    rcases hfr ht with rfl | rfl
    · exact hfa
    · exact hfb
  · exact hf.mono fun t ht => by
      have := ht.2
      change t ∈ closure (Icc a b) at this
      rwa [closure_Icc] at this
  · exact hg.mono fun t ht => ht.1

theorem exists_smooth_core_curve {e : Plane → Plane} {α β W τa τb ρ : ℝ}
    (hW : 0 < W) (hρ : 0 < ρ) (hαa : α ≤ τa - 2 * ρ) (hab : τa + 2 * ρ < τb - 2 * ρ)
    (hbβ : τb + 2 * ρ ≤ β)
    (hcont : ContinuousOn e (planeRect α β (-W) W)) (hinj : InjOn e (planeRect α β (-W) W))
    {va vb : Plane} (hva : va ≠ 0) (hvb : vb ≠ 0)
    (hea : ∀ t, |t - τa| < 2 * ρ → e (Plane.mk t 0) = e (Plane.mk τa 0) + (t - τa) • va)
    (heb : ∀ t, |t - τb| < 2 * ρ → e (Plane.mk t 0) = e (Plane.mk τb 0) + (t - τb) • vb) :
    ∃ γ : ℝ → Plane, ContDiff ℝ ∞ γ ∧ (∀ t, deriv γ t ≠ 0) ∧
      (∀ t ≤ τa - ρ / 2, γ t = e (Plane.mk τa 0) + (t - τa) • va) ∧
      (∀ t, τb + ρ / 2 ≤ t → γ t = e (Plane.mk τb 0) + (t - τb) • vb) ∧
      InjOn (fun t => if t ∈ Icc (τa - ρ) (τb + ρ) then γ t else e (Plane.mk t 0))
        (Icc α β) ∧
      ∀ t ∈ Icc (τa - ρ) (τb + ρ), γ t ∈ e '' planeOpenRect (τa - 2 * ρ) (τb + 2 * ρ) (-W) W := by
  classical
  obtain ⟨m, B, hB0, hBm, ⟨c₁, hc₁, hv1⟩, ⟨c₂, hc₂, hvm⟩, hBO, hBex⟩ :=
    exists_core_polyArc hW hρ hαa hab hbβ hcont hinj hea heb
  set Pa := e (Plane.mk τa 0) with hPa
  set Pb := e (Plane.mk τb 0) with hPb
  set h : ℝ := (τb - τa) / (m + 1) with hhdef
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hh : 0 < h := div_pos (by linarith) hm1
  have hmh : τa + ((m : ℝ) + 1) * h = τb := by
    rw [hhdef]
    field_simp
    ring
  set T : ℕ → ℝ := fun k => τa + k * h with hT
  have hTstep : ∀ j, T (j + 1) - T j = h := fun j => by
    simp only [hT]
    push_cast
    ring
  have hTgap : ∀ j, h ≤ T (j + 1) - T j := fun j => (hTstep j).ge
  have hTmono : Monotone T := fun i j hij => by
    simp only [hT]
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  have hT0 : T 0 = τa := by simp [hT]
  have hTm : T (m + 1) = τb := by
    simp only [hT]
    push_cast
    exact hmh
  let Vel : ℕ → Plane := fun k => match k with
    | 0 => va
    | k + 1 => if k ≤ m then h⁻¹ • (B.vertex (k + 1) - B.vertex k) else vb
  let d : ℕ → Plane := fun k => Vel (k + 1) - Vel k
  have hW0 : Vel 0 = va := rfl
  have hWs : ∀ k ≤ m, Vel (k + 1) = h⁻¹ • (B.vertex (k + 1) - B.vertex k) := fun k hk => by
    simp [Vel, hk]
  have hWlast : Vel (m + 1 + 1) = vb := by simp [Vel]
  have hhW : ∀ k ≤ m, h • Vel (k + 1) = B.vertex (k + 1) - B.vertex k := fun k hk => by
    rw [hWs k hk, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  have hV : ∀ k ≤ m + 1,
      Pa + ∑ j ∈ Finset.range k, (T (j + 1) - T j) • Vel (j + 1) = B.vertex k := by
    intro k
    induction k with
    | zero => intro _; simp [hB0]
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, ← add_assoc, ih (by omega), hTstep k, hhW k (by omega)]
      abel
  set p := rampPath (fun r => max r 0) Pa T va d (m + 1) with hp
  have hpk : ∀ k ≤ m, ∀ t, T k ≤ t → t ≤ T (k + 1) →
      p t = B.vertex k + ((t - T k) / h) • (B.vertex (k + 1) - B.vertex k) := by
    intro k hk t h1 h2
    rw [hp, rampPath_max_eq_partial hTmono Pa va d (by omega : k ≤ m + 1) h1 (fun _ => h2)]
    refine (rampPath_partial_telescope Pa T Vel t k).trans ?_
    rw [hV k (by omega), hWs k hk, smul_smul, div_eq_mul_inv]
  have hpleft : ∀ t ≤ T 0, p t = Pa + (t - τa) • va := by
    intro t ht
    rw [hp]
    unfold rampPath
    rw [hT0, Finset.sum_eq_zero fun j _ => by
      change max (t - T j) 0 • d j = 0
      rw [max_eq_right (by linarith [hTmono (Nat.zero_le j)]), zero_smul], add_zero]
  have hpright : ∀ t, T (m + 1) ≤ t → p t = Pb + (t - τb) • vb := by
    intro t ht
    rw [hp, rampPath_max_eq_partial hTmono Pa va d (le_refl (m + 1)) ht (fun h' => absurd h'
      (lt_irrefl _))]
    refine (rampPath_partial_telescope Pa T Vel t (m + 1)).trans ?_
    rw [hV (m + 1) le_rfl, hWlast, hTm, hBm]
  have hcomb : ∀ K ≤ m + 1, ∀ μ ∈ Icc (0 : ℝ) 1,
      va + ∑ k ∈ Finset.range K, d k + μ • d K ≠ 0 := by
    intro K hK μ hμ
    have htel : va + ∑ k ∈ Finset.range K, d k = Vel K := sum_range_telescope Vel K
    rw [htel]
    have hsplit : Vel K + μ • d K = (1 - μ) • Vel K + μ • Vel (K + 1) := by
      change Vel K + μ • (Vel (K + 1) - Vel K) = _
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [hsplit]
    rcases Nat.eq_zero_or_pos K with rfl | hK0
    · rw [hW0, hWs 0 (Nat.zero_le _), zero_add, hv1, smul_smul, smul_smul, ← add_smul]
      refine smul_ne_zero ?_ hva
      have : 0 ≤ μ * h⁻¹ * c₁ := mul_nonneg (mul_nonneg hμ.1 (inv_nonneg.mpr hh.le)) hc₁.le
      have h2 : 0 < 1 - μ + μ * h⁻¹ * c₁ := by
        rcases eq_or_lt_of_le hμ.2 with h1 | h1
        · rw [h1]
          simp only [sub_self, one_mul, zero_add]
          exact mul_pos (inv_pos.mpr hh) hc₁
        · linarith
      exact h2.ne'
    · rcases lt_or_eq_of_le hK with hKm | rfl
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK0.ne'
        rw [hWs k (by omega), hWs (k + 1) (by omega)]
        apply combination_ne_zero_of_det_ne_zero
        rw [Schoenflies.Plane.det_smul_left, Schoenflies.Plane.det_smul_right]
        have hc := B.corner k (by omega)
        have hneg : B.vertex (k + 1) - B.vertex k = -(B.vertex k - B.vertex (k + 1)) :=
          (neg_sub _ _).symm
        rw [hneg, planeDet_neg_left]
        refine mul_ne_zero (inv_ne_zero hh.ne') (mul_ne_zero (inv_ne_zero hh.ne') ?_)
        exact neg_ne_zero.mpr hc
      · rw [hWs m le_rfl, hWlast, hvm, smul_smul, smul_smul, ← add_smul]
        refine smul_ne_zero ?_ hvb
        have : 0 ≤ (1 - μ) * h⁻¹ * c₂ :=
          mul_nonneg (mul_nonneg (by linarith [hμ.2]) (inv_nonneg.mpr hh.le)) hc₂.le
        have h2 : 0 < (1 - μ) * h⁻¹ * c₂ + μ := by
          rcases eq_or_lt_of_le hμ.1 with h1 | h1
          · rw [← h1]
            simp only [sub_zero, one_mul, add_zero]
            exact mul_pos (inv_pos.mpr hh) hc₂
          · linarith
        exact h2.ne'
  have hray_a : ∀ t, |t - τa| < 2 * ρ → t ≤ τa → p t = e (Plane.mk t 0) := by
    intro t ht1 ht2
    rw [hpleft t (by rw [hT0]; exact ht2), hea t ht1]
  have hray_b : ∀ t, |t - τb| < 2 * ρ → τb ≤ t → p t = e (Plane.mk t 0) := by
    intro t ht1 ht2
    rw [hpright t (by rw [hTm]; exact ht2), heb t ht1]
  have hpcont : Continuous p := by
    rw [hp]
    unfold rampPath
    refine (continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)).add
      (continuous_finsetSum _ fun k _ =>
        ((continuous_id.sub continuous_const).max continuous_const).smul continuous_const)
  have hcore : ∀ t ∈ Icc α β, Plane.mk t 0 ∈ planeRect α β (-W) W :=
    fun t ht => mem_planeRect_core hW ht
  have hecont : ContinuousOn (fun t => e (Plane.mk t 0)) (Icc α β) := by
    refine hcont.comp ?_ hcore
    have : Continuous (fun t : ℝ => Plane.mk t 0) := by
      have h1 : (fun t : ℝ => Plane.mk t 0) = fun t => t • EuclideanSpace.single 0 1 := by
        funext t
        ext i
        fin_cases i <;> simp
      rw [h1]
      exact continuous_id.smul continuous_const
    exact this.continuousOn
  have hmk_inj : ∀ s t : ℝ, s ∈ Icc α β → t ∈ Icc α β →
      e (Plane.mk s 0) = e (Plane.mk t 0) → s = t := by
    intro s t hs ht h'
    have := hinj (hcore s hs) (hcore t ht) h'
    have h0 := congrArg (fun x : Plane => x 0) this
    simpa using h0
  have hmh' : τa + ((m : ℝ) + 1) * h = τb := hmh
  obtain ⟨hpinj, hpmaps⟩ := injOn_mapsTo_polyArc_path B hh (p := p) (τa := τa) (fun k hk t h1 h2 =>
    by
      have := hpk k hk t (by simpa [hT] using h1) (by simpa [hT] using h2)
      simpa [hT] using this)
  rw [hmh'] at hpinj hpmaps
  set pf : ℝ → Plane := fun t => if t ∈ Icc (τa - ρ) (τb + ρ) then p t else e (Plane.mk t 0)
    with hpfdef
  have hpf_out : ∀ t ∈ Icc α β, (t ≤ τa ∨ τb ≤ t) → pf t = e (Plane.mk t 0) := by
    intro t ht hout
    simp only [hpfdef]
    split_ifs with hin
    · rcases hout with h1 | h1
      · refine hray_a t ?_ h1
        rw [abs_lt]
        constructor <;> linarith [hin.1]
      · refine hray_b t ?_ h1
        rw [abs_lt]
        constructor <;> linarith [hin.2]
    · rfl
  have hpf_in : ∀ t ∈ Icc τa τb, pf t = p t := by
    intro t ht
    simp only [hpfdef]
    rw [ite_eq_left ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  have hpfcont : ContinuousOn pf (Icc α β) :=
    continuousOn_core_switch (by linarith) hpcont.continuousOn hecont
      (hray_a _ (by rw [abs_lt]; constructor <;> linarith) (by linarith))
      (hray_b _ (by rw [abs_lt]; constructor <;> linarith) (by linarith))
  have hpfinj : InjOn pf (Icc α β) := by
    intro s hs t ht hst
    by_cases hsm : s ∈ Icc τa τb <;> by_cases htm : t ∈ Icc τa τb
    · rw [hpf_in s hsm, hpf_in t htm] at hst
      exact hpinj hsm htm hst
    · have htout : t < τa ∨ τb < t := by
        by_contra hc
        push Not at hc
        exact htm ⟨hc.1, hc.2⟩
      rw [hpf_in s hsm, hpf_out t ht (htout.imp le_of_lt le_of_lt)] at hst
      exact absurd (hst ▸ hpmaps hsm) (hBex t ht htout)
    · have hsout : s < τa ∨ τb < s := by
        by_contra hc
        push Not at hc
        exact hsm ⟨hc.1, hc.2⟩
      rw [hpf_in t htm, hpf_out s hs (hsout.imp le_of_lt le_of_lt)] at hst
      exact absurd (hst.symm ▸ hpmaps htm) (hBex s hs hsout)
    · have hsout : s ≤ τa ∨ τb ≤ s := by
        by_contra hc
        push Not at hc
        exact hsm ⟨hc.1.le, hc.2.le⟩
      have htout : t ≤ τa ∨ τb ≤ t := by
        by_contra hc
        push Not at hc
        exact htm ⟨hc.1.le, hc.2.le⟩
      rw [hpf_out s hs hsout, hpf_out t ht htout] at hst
      exact hmk_inj s t hs ht hst
  set η₀ : ℝ := min (ρ / 4) (h / 2) with hη₀
  have hη₀pos : 0 < η₀ := lt_min (by linarith) (by linarith)
  obtain ⟨κ, hκ, hκsep⟩ := exists_pos_le_norm_sub_of_injOn hpfcont hpfinj hη₀pos
  set O := e '' planeOpenRect (τa - 2 * ρ) (τb + 2 * ρ) (-W) W with hOdef
  have hOsub : planeOpenRect (τa - 2 * ρ) (τb + 2 * ρ) (-W) W ⊆ planeRect α β (-W) W :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2.1.le, hx.2.2.2.le⟩
  have hOopen : IsOpen O := DifferentialGeometry.Topology.invariance_of_domain_isOpen_image
    (isOpen_planeOpenRect _ _ _ _) (hcont.mono hOsub) (hinj.mono hOsub)
  have hpO : p '' Icc (τa - ρ) (τb + ρ) ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    have hmem : ∀ t, τa - 2 * ρ < t → t < τb + 2 * ρ →
        Plane.mk t 0 ∈ planeOpenRect (τa - 2 * ρ) (τb + 2 * ρ) (-W) W := by
      intro t h1 h2
      have h0 : (Plane.mk t 0) 0 = t := by simp
      have h1' : (Plane.mk t 0) 1 = 0 := by simp
      exact ⟨by rw [h0]; exact h1, by rw [h0]; exact h2, by rw [h1']; linarith,
        by rw [h1']; linarith⟩
    by_cases h1 : t ≤ τa
    · rw [hray_a t (by rw [abs_lt]; constructor <;> linarith [ht.1]) h1]
      exact ⟨_, hmem t (by linarith [ht.1]) (by linarith), rfl⟩
    by_cases h2 : τb ≤ t
    · rw [hray_b t (by rw [abs_lt]; constructor <;> linarith [ht.2]) h2]
      exact ⟨_, hmem t (by linarith) (by linarith [ht.2]), rfl⟩
    push Not at h1 h2
    obtain ⟨x, hx, hxe⟩ := hBO (hpmaps ⟨h1.le, h2.le⟩)
    exact ⟨x, ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2.1, hx.2.2.2⟩, hxe⟩
  obtain ⟨rO, hrO, hthick⟩ :=
    (isCompact_Icc.image hpcont).exists_thickening_subset_open hOopen hpO
  set Csum : ℝ := ∑ k ∈ Finset.range (m + 1 + 1), ‖d k‖ with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun k _ => norm_nonneg _
  set ε : ℝ := min (min (ρ / 4) (h / 8)) (min κ rO / (4 * (Csum + 1))) with hεdef
  have hε : 0 < ε := lt_min (lt_min (by linarith) (by linarith))
    (div_pos (lt_min hκ hrO) (by positivity))
  have hερ : ε ≤ ρ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hεh : ε ≤ h / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hεC : ε * Csum < min κ rO / 2 := by
    have h1 : ε ≤ min κ rO / (4 * (Csum + 1)) := min_le_right _ _
    have h2 : 0 < min κ rO := lt_min hκ hrO
    calc ε * Csum ≤ min κ rO / (4 * (Csum + 1)) * Csum :=
          mul_le_mul_of_nonneg_right h1 hCsum0
      _ < min κ rO / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  set γ := rampPath (smoothRamp ε) Pa T va d (m + 1) with hγdef
  have hγp : ∀ t, ‖γ t - p t‖ ≤ ε * Csum := fun t =>
    norm_rampPath_smoothRamp_sub_le hε Pa T va d (m + 1) t
  have hγleft : ∀ t ≤ τa - ρ / 2, γ t = Pa + (t - τa) • va := by
    intro t ht
    have hk : ∀ k ≤ m + 1, ε ≤ |t - T k| := fun k _ => by
      have := hTmono (Nat.zero_le k)
      rw [hT0] at this
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    rw [hγdef, rampPath_smoothRamp_eq hε Pa T va d (m + 1) hk]
    exact hpleft t (by rw [hT0]; linarith)
  have hγright : ∀ t, τb + ρ / 2 ≤ t → γ t = Pb + (t - τb) • vb := by
    intro t ht
    have hk : ∀ k ≤ m + 1, ε ≤ |t - T k| := fun k hk => by
      have := hTmono hk
      rw [hTm] at this
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [hγdef, rampPath_smoothRamp_eq hε Pa T va d (m + 1) hk]
    exact hpright t (by rw [hTm]; linarith)
  refine ⟨γ, contDiff_rampPath_smoothRamp ε Pa T va d (m + 1), fun t => ?_, hγleft, hγright,
    ?_, ?_⟩
  · rw [hγdef, (hasDerivAt_rampPath_smoothRamp ε Pa T va d (m + 1) t).deriv]
    exact deriv_rampPath_smoothRamp_ne_zero hε hh hTgap (by linarith) hcomb t
  · set Cf : ℝ → Plane := fun t => if t ∈ Icc (τa - ρ) (τb + ρ) then γ t else e (Plane.mk t 0)
    have hCf_left : ∀ t ∈ Icc α β, t ≤ τa - ρ / 2 → Cf t = e (Plane.mk t 0) := by
      intro t ht h1
      simp only [Cf]
      split_ifs with hin
      · rw [hγleft t h1, hea t (by rw [abs_lt]; constructor <;> linarith [hin.1])]
      · rfl
    have hCf_right : ∀ t ∈ Icc α β, τb + ρ / 2 ≤ t → Cf t = e (Plane.mk t 0) := by
      intro t ht h1
      simp only [Cf]
      split_ifs with hin
      · rw [hγright t h1, heb t (by rw [abs_lt]; constructor <;> linarith [hin.2])]
      · rfl
    refine injOn_of_near_injOn (p := pf) (η := η₀) (κ := κ) hκsep (fun t ht => ?_) ?_
    · simp only [Cf, hpfdef]
      split_ifs with hin
      · exact (hγp t).trans_lt (hεC.trans_le (by linarith [min_le_left κ rO]))
      · rw [sub_self, norm_zero]
        exact half_pos hκ
    · intro s hs t ht hst hshort hCeq
      by_cases hin : s ∈ Icc (τa - ρ) (τb + ρ) ∧ t ∈ Icc (τa - ρ) (τb + ρ)
      · simp only [Cf, ite_eq_left hin.1, ite_eq_left hin.2] at hCeq
        exact rampPath_smoothRamp_ne_of_lt hε hh hTgap hcomb hst
          (by linarith [min_le_right (ρ / 4) (h / 2)]) hCeq
      · have hcase : (t ≤ τa - ρ / 2) ∨ (τb + ρ / 2 ≤ s) := by
          by_contra hc
          push Not at hc
          apply hin
          have hη : η₀ ≤ ρ / 4 := min_le_left _ _
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        rcases hcase with h1 | h1
        · rw [hCf_left s hs (by linarith), hCf_left t ht h1] at hCeq
          exact (hst.ne (hmk_inj s t hs ht hCeq)).elim
        · rw [hCf_right s hs h1, hCf_right t ht (by linarith)] at hCeq
          exact (hst.ne (hmk_inj s t hs ht hCeq)).elim
  · intro t ht
    refine hthick ?_
    rw [Metric.mem_thickening_iff]
    exact ⟨p t, ⟨t, ht, rfl⟩, by
      rw [dist_eq_norm]
      exact (hγp t).trans_lt (hεC.trans_le (by linarith [min_le_right κ rO]))⟩

end DifferentialGeometry.Topology.PlanarJordan
