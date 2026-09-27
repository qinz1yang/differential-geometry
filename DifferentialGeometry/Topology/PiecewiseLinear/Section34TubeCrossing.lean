/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TubePrism
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionPocket
import DifferentialGeometry.Topology.PiecewiseLinear.ChartComplexPiece
import DifferentialGeometry.Topology.PiecewiseLinear.FiberBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem frontier_inter_ball_eq_of_flat {W : Set E3} {b nb : E3} {ρ : ℝ} (hWc : IsClosed W)
    (hnb : nb ≠ 0) (hflat : W ∩ ball b ρ = {x | inner ℝ nb (x - b) ≤ 0} ∩ ball b ρ) :
    frontier W ∩ ball b ρ = {x | inner ℝ nb (x - b) = 0} ∩ ball b ρ := by
  have hcont : Continuous fun x : E3 => inner ℝ nb (x - b) :=
    continuous_const.inner (continuous_id.sub continuous_const)
  ext x
  constructor
  · rintro ⟨hxf, hxb⟩
    have hxW : x ∈ W := hWc.frontier_subset hxf
    have hle := (hflat.subset ⟨hxW, hxb⟩).1
    refine ⟨le_antisymm hle ?_, hxb⟩
    by_contra hlt
    push Not at hlt
    apply hxf.2
    have hO : IsOpen ({y : E3 | inner ℝ nb (y - b) < 0} ∩ ball b ρ) :=
      (isOpen_lt hcont continuous_const).inter isOpen_ball
    refine interior_maximal (fun y hy => (hflat.symm.subset
      ⟨(show inner ℝ nb (y - b) < 0 from hy.1).le, hy.2⟩).1) hO ⟨hlt, hxb⟩
  · rintro ⟨h0, hxb⟩
    have hxW : x ∈ W := (hflat.symm.subset ⟨h0.le, hxb⟩).1
    refine ⟨⟨subset_closure hxW, ?_⟩, hxb⟩
    have hnn : 0 < inner ℝ nb nb := real_inner_self_pos.mpr hnb
    have hdx : 0 < ρ - dist x b := sub_pos.mpr (mem_ball.mp hxb)
    refine notMem_interior_of_forall_add_smul (v := nb) (ε₀ := (ρ - dist x b) / (‖nb‖ + 1))
      (div_pos hdx (by positivity)) fun ε hε hεlt hmem => ?_
    have hmemb : x + ε • nb ∈ ball b ρ := by
      rw [mem_ball]
      calc dist (x + ε • nb) b ≤ dist (x + ε • nb) x + dist x b := dist_triangle _ _ _
        _ = ε * ‖nb‖ + dist x b := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        _ < ρ := by
          rw [lt_div_iff₀ (by positivity)] at hεlt
          nlinarith [norm_nonneg nb]
    have hle := (hflat.subset ⟨hmem, hmemb⟩).1
    change inner ℝ nb (x + ε • nb - b) ≤ 0 at hle
    have : x + ε • nb - b = (x - b) + ε • nb := by abel
    rw [this, inner_add_right, h0, real_inner_smul_right] at hle
    nlinarith

theorem exists_mem_frontier_eq_sub_smul {W : Set E3} {u d : E3}
    (hWb : Bornology.IsBounded W) (hWc : IsClosed W) (hu : u ∈ W) (hd : d ≠ 0) :
    ∃ f ∈ frontier W, ∃ t : ℝ, 0 ≤ t ∧ f = u - t • d := by
  by_cases hfu : u ∈ frontier W
  · exact ⟨u, hfu, 0, le_rfl, by simp⟩
  have huint : u ∈ interior W := by
    by_contra h
    exact hfu ⟨subset_closure hu, h⟩
  by_contra hno
  push Not at hno
  set R := (fun t : ℝ => u - t • d) '' Ici 0 with hR
  have hRc : IsPreconnected R :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hRsub : R ⊆ interior W ∪ Wᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases hW : u - t • d ∈ W
    · left
      by_contra hint
      exact hno _ ⟨subset_closure hW, hint⟩ t ht rfl
    · exact Or.inr hW
  have hRint : R ⊆ interior W := IsPreconnected.subset_left_of_subset_union isOpen_interior
    hWc.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hRsub
    ⟨u, ⟨0, self_mem_Ici, by simp⟩, huint⟩ hRc
  obtain ⟨D, hD⟩ := hWb.subset_closedBall u
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  set t := (|D| + 1) / ‖d‖ with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) hdn.le
  have hmem := hD (interior_subset (hRint ⟨t, ht0, rfl⟩))
  rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht0, ht, div_mul_cancel₀ _ hdn.ne'] at hmem
  have := le_abs_self D
  linarith

theorem frontier_inter_interior_nonempty_of_subset_ball {W Q : Set E3} {b : E3} {ρ : ℝ}
    (hW : IsPLBall 3 W) (hQc : IsClosed Q) (hQint : (interior W ∩ interior Q).Nonempty)
    (hWQ : frontier W ∩ Q ⊆ ball b ρ) (hf : ∃ f ∈ frontier W, f ∉ ball b ρ) :
    (frontier Q ∩ interior W).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hconn := (hW.isConnected_interior_of_finrank hdim).isPreconnected
  have hsub : interior W ⊆ interior Q ∪ Qᶜ := by
    intro x hx
    by_cases hxQ : x ∈ Q
    · left
      by_contra hint
      have : x ∈ frontier Q ∩ interior W := ⟨⟨subset_closure hxQ, hint⟩, hx⟩
      rw [hne] at this
      exact this
    · exact Or.inr hxQ
  have hWQ' : interior W ⊆ interior Q := IsPreconnected.subset_left_of_subset_union
    isOpen_interior hQc.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hsub
    hQint hconn
  have hWsub : W ⊆ Q := by
    rw [← hW.closure_interior_of_finrank hdim]
    exact closure_minimal (hWQ'.trans interior_subset) hQc
  obtain ⟨f, hfW, hfb⟩ := hf
  exact hfb (hWQ ⟨hfW, hWsub (hW.isPolyhedron.isClosed.frontier_subset hfW)⟩)

theorem notMem_of_flat_of_mem_segment {W : Set E3} {u v b nb : E3} {ρ : ℝ} (hWc : IsClosed W)
    (hρ : 0 < ρ) (hflat : W ∩ ball b ρ = {x | inner ℝ nb (x - b) ≤ 0} ∩ ball b ρ)
    (hb : b ∈ openSegment ℝ u v) (hnb : 0 < inner ℝ nb (v - u))
    (hsegW : ∀ x ∈ segment ℝ u v, x ∈ frontier W → x = b) : v ∉ W := by
  rw [openSegment_eq_image'] at hb
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hb
  set b := u + s • (v - u) with hbdef
  have hvb : v - b = (1 - s) • (v - u) := by rw [hbdef, sub_smul, one_smul]; abel
  set A := (fun t : ℝ => b + t • (v - b)) '' Ioc 0 1 with hA
  have hAc : IsPreconnected A := isPreconnected_Ioc.image _ (by fun_prop)
  have hAseg : A ⊆ segment ℝ u v := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rw [segment_eq_image']
    refine ⟨s + t * (1 - s), ⟨by nlinarith, by nlinarith⟩, ?_⟩
    change u + (s + t * (1 - s)) • (v - u) = b + t • (v - b)
    rw [hvb, hbdef, smul_smul, add_smul, add_assoc]
  have hAdisj : Disjoint A (frontier W) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ hf
    have heq := hsegW _ (hAseg ⟨t, ⟨ht0, ht1⟩, rfl⟩) hf
    have hne : t • (v - b) ≠ 0 := by
      rw [hvb, smul_smul]
      refine smul_ne_zero (by nlinarith) ?_
      intro h0
      rw [h0, inner_zero_right] at hnb
      exact lt_irrefl _ hnb
    exact hne (add_eq_left.mp heq)
  have hvb0 : 0 < inner ℝ nb (v - b) := by
    rw [hvb, real_inner_smul_right]
    exact mul_pos (by linarith) hnb
  have hvbn : 0 < ‖v - b‖ := norm_pos_iff.mpr (by
    intro h0
    rw [h0, inner_zero_right] at hvb0
    exact lt_irrefl _ hvb0)
  set t := min 1 (ρ / (2 * ‖v - b‖)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hρ (by positivity))
  have hpA : b + t • (v - b) ∈ A := ⟨t, ⟨ht0, min_le_left _ _⟩, rfl⟩
  have hpW : b + t • (v - b) ∉ W := by
    intro hpW
    have hpb : b + t • (v - b) ∈ ball b ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0]
      calc t * ‖v - b‖ ≤ ρ / (2 * ‖v - b‖) * ‖v - b‖ := by
            gcongr
            exact min_le_right _ _
        _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
    have hle := (hflat.subset ⟨hpW, hpb⟩).1
    change inner ℝ nb (b + t • (v - b) - b) ≤ 0 at hle
    rw [add_sub_cancel_left, real_inner_smul_right] at hle
    nlinarith
  rcases subset_interior_or_subset_compl_of_disjoint_frontier hWc hAc hAdisj with hAW | hAW
  · exact absurd (interior_subset (hAW hpA)) hpW
  · have hvA : v ∈ A := ⟨1, ⟨one_pos, le_rfl⟩, by simp⟩
    exact hAW hvA

theorem isPolyhedralSphere_of_isPLSphere_one {S : Set E3} (hS : IsPLSphere 1 S) :
    IsPolyhedralSphere (n := 3) 1 S := by
  have h := isPolyhedralSphere_chart_symm_image
    (chartAt (EuclideanSpace ℝ (Fin 3)) (0 : EuclideanSpace ℝ (Fin 3)))
    (chart_mem_atlas _ _) hS (by rw [chartAt_self_eq]; exact subset_univ S)
  simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, image_id] using h

theorem isPLBall_sdiff_interior_union_prism {W Y V : Set E3} {u v b nY nb : E3} {ρY ρb : ℝ}
    (hW : IsPLBall 3 W) (hY : IsPLBall 3 Y) (hYW : Y ⊆ interior W) (hρY : 0 < ρY)
    (hflatY : Y ∩ ball u ρY = {x | inner ℝ nY (x - u) ≤ 0} ∩ ball u ρY) (hρb : 0 < ρb)
    (hflatW : W ∩ ball b ρb = {x | inner ℝ nb (x - b) ≤ 0} ∩ ball b ρb)
    (hb : b ∈ openSegment ℝ u v) (hnY : 0 < inner ℝ nY (v - u)) (hnb : 0 < inner ℝ nb (v - u))
    (hsegY : ∀ x ∈ segment ℝ u v, x ≠ u → x ∉ Y)
    (hsegW : ∀ x ∈ segment ℝ u v, x ∈ frontier W → x = b)
    (hV : IsOpen V) (hsegV : segment ℝ u v ⊆ V) :
    ∃ C : Set E3, IsCompact C ∧ C ⊆ V ∧ IsPLBall 3 (W \ interior (Y ∪ C)) := by
  have hWc : IsClosed W := hW.isPolyhedron.isClosed
  have hYc : IsCompact Y := hY.isPolyhedron.isCompact
  have hnb0 : nb ≠ 0 := by
    rintro rfl
    rw [inner_zero_left] at hnb
    exact lt_irrefl _ hnb
  have hvu : v - u ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right] at hnb
    exact lt_irrefl _ hnb
  have hb' := hb
  rw [openSegment_eq_image'] at hb'
  obtain ⟨s₀, ⟨hs0, hs1⟩, hbeq⟩ := hb'
  have hfrW := frontier_inter_ball_eq_of_flat hWc hnb0 hflatW
  have hbW : b ∈ frontier W :=
    (hfrW.symm.subset ⟨by simp, mem_ball_self hρb⟩).1
  have hbY : b ∉ Y := fun h => hbW.2 (hYW h)
  obtain ⟨rY, hrY, hrYsub⟩ := Metric.isOpen_iff.mp hYc.isClosed.isOpen_compl b hbY
  have hbu : b - u = s₀ • (v - u) := by rw [← hbeq, add_sub_cancel_left]
  have hdub : dist u b = s₀ * ‖v - u‖ := by
    rw [dist_comm, dist_eq_norm, hbu, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have hvun : 0 < ‖v - u‖ := norm_pos_iff.mpr hvu
  have hnYb : 0 < inner ℝ nY (b - u) := by
    rw [hbu, real_inner_smul_right]
    exact mul_pos hs0 hnY
  set ρ₁ := min (min ρb (rY / 2))
    (min (s₀ * ‖v - u‖ / 2) (inner ℝ nY (b - u) / (2 * ‖nY‖ + 1))) with hρ₁def
  have hρ₁ : 0 < ρ₁ := lt_min (lt_min hρb (half_pos hrY))
    (lt_min (half_pos (mul_pos hs0 hvun)) (div_pos hnYb (by positivity)))
  have hρ₁b : ρ₁ ≤ ρb := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₁Y : ρ₁ ≤ rY / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₁u : ρ₁ ≤ s₀ * ‖v - u‖ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₁n : ρ₁ ≤ inner ℝ nY (b - u) / (2 * ‖nY‖ + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  set P := {x : E3 | innerₗ E3 nb x = inner ℝ nb b} with hPdef
  have hPc : IsClosed P := isClosed_eq (innerₗ E3 nb).continuous_of_finiteDimensional
    continuous_const
  set V' := V ∩ (frontier W \ ball b ρ₁)ᶜ ∩ (P \ ball b ρ₁)ᶜ with hV'
  have hV'o : IsOpen V' :=
    (hV.inter (isClosed_frontier.sdiff isOpen_ball).isOpen_compl).inter
      (hPc.sdiff isOpen_ball).isOpen_compl
  have hsegP : ∀ x ∈ segment ℝ u v, x ∈ P → x = b := by
    intro x hx hxP
    rw [segment_eq_image'] at hx
    obtain ⟨t, -, rfl⟩ := hx
    change inner ℝ nb (u + t • (v - u)) = inner ℝ nb b at hxP
    rw [← hbeq, inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right] at hxP
    have ht : t = s₀ := by
      have h' : (t - s₀) * inner ℝ nb (v - u) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h'' | h''
      · linarith
      · exact absurd h'' hnb.ne'
    rw [ht, hbeq]
  have hsegV' : segment ℝ u v ⊆ V' := by
    intro x hx
    refine ⟨⟨hsegV hx, fun h => h.2 ?_⟩, fun h => h.2 ?_⟩
    · rw [hsegW x hx h.1]
      exact mem_ball_self hρ₁
    · rw [hsegP x hx h.1]
      exact mem_ball_self hρ₁
  obtain ⟨C, hCpoly, hCV', -, hCint, hQ, ⟨ρ', hρ', hflatQ⟩, hsec⟩ :=
    exists_isPLBall_union_prism hY hρY hflatY hnY hnb hsegY hV'o hsegV'
  have hQc : IsClosed (Y ∪ C) := hQ.isPolyhedron.isClosed
  have hCball : ∀ x ∈ C, x ∈ frontier W → x ∈ ball b ρ₁ := by
    intro x hx hxW
    by_contra hxb
    exact (hCV' hx).1.2 ⟨hxW, hxb⟩
  have hCP : ∀ x ∈ C, x ∈ P → x ∈ ball b ρ₁ := by
    intro x hx hxP
    by_contra hxb
    exact (hCV' hx).2 ⟨hxP, hxb⟩
  have hℓ : innerₗ E3 nb ≠ 0 := by
    intro h
    have h' := congrArg (fun f : E3 →ₗ[ℝ] ℝ => f (v - u)) h
    simp only [innerₗ_apply_apply, LinearMap.zero_apply] at h'
    linarith
  have hbC : b ∈ interior C := hCint hb
  obtain ⟨g, hg⟩ := hCpoly.isPLBall_inter_fiber (n := 2) (by simp) (innerₗ E3 nb) hℓ
    (r := inner ℝ nb b) ⟨b, hbC, rfl⟩
  have hWQ : frontier W ∩ (Y ∪ C) = C ∩ P := by
    ext x
    constructor
    · rintro ⟨hxW, hxY | hxC⟩
      · exact absurd (hYW hxY) hxW.2
      · have hxb := hCball x hxC hxW
        have h0 := (hfrW.subset ⟨hxW, ball_subset_ball hρ₁b hxb⟩).1
        change inner ℝ nb (x - b) = 0 at h0
        refine ⟨hxC, ?_⟩
        change inner ℝ nb x = inner ℝ nb b
        rw [inner_sub_right] at h0
        linarith
    · rintro ⟨hxC, hxP⟩
      have hxb := hCP x hxC hxP
      have h0 : inner ℝ nb (x - b) = 0 := by
        change inner ℝ nb x = inner ℝ nb b at hxP
        rw [inner_sub_right, hxP, sub_self]
      exact ⟨(hfrW.symm.subset ⟨h0, ball_subset_ball hρ₁b hxb⟩).1, Or.inr hxC⟩
  have hintQ : ∀ q ∈ ball b ρ₁, q ∈ interior (Y ∪ C) → q ∈ interior C := by
    intro q hq hqQ
    rw [mem_interior_iff_mem_nhds] at hqQ ⊢
    refine Filter.mem_of_superset (Filter.inter_mem hqQ (ball_mem_nhds q hρ₁)) ?_
    rintro y ⟨hyQ | hyC, hyb⟩
    · exfalso
      apply hrYsub _ hyQ
      rw [mem_ball] at hq hyb ⊢
      have := dist_triangle y q b
      linarith
    · exact hyC
  have hiff : ∀ q ∈ C ∩ P, (C ∩ P ∈ 𝓝[P] q ↔ q ∉ g '' stdSimplexBoundary (1 + 1)) := fun q hq =>
    hg.mem_nhdsWithin_fiber_iff_notMem_image_boundary (n := 1) (by simp) (innerₗ E3 nb) hℓ
      inter_subset_right hq
  have hcirc : frontier W ∩ frontier (Y ∪ C) = g '' stdSimplexBoundary 2 := by
    ext q
    constructor
    · rintro ⟨hqW, hqQ⟩
      have hqS : q ∈ C ∩ P := hWQ.subset ⟨hqW, hQc.frontier_subset hqQ⟩
      have hqb := hCP q hqS.1 hqS.2
      have hqC : q ∉ interior C := fun h => hqQ.2 (interior_mono subset_union_right h)
      by_contra hnot
      apply hqC
      have hnhds := ((hiff q hqS).mpr hnot)
      have hqr : inner ℝ nb q = inner ℝ nb b := hqS.2
      have hbot : 0 < inner ℝ nY (q - u) := by
        have hsplit : inner ℝ nY (q - u) = inner ℝ nY (b - u) + inner ℝ nY (q - b) := by
          rw [← inner_add_right]
          congr 1
          abel
        have h1 := abs_real_inner_le_norm nY (q - b)
        have h2 : ‖q - b‖ < ρ₁ := by rw [← dist_eq_norm]; exact hqb
        have h3 : ‖nY‖ * ‖q - b‖ ≤ ‖nY‖ * (inner ℝ nY (b - u) / (2 * ‖nY‖ + 1)) := by
          gcongr
          exact h2.le.trans hρ₁n
        have h4 : ‖nY‖ * (inner ℝ nY (b - u) / (2 * ‖nY‖ + 1)) < inner ℝ nY (b - u) := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg nY]
        have h5 := neg_abs_le (inner ℝ nY (q - b))
        linarith
      have htop : inner ℝ nb (q - v) < 0 := by
        have hvb : v - b = (1 - s₀) • (v - u) := by
          have h' : v - b = (v - u) - (b - u) := by abel
          rw [h', hbu, sub_smul, one_smul]
        have : inner ℝ nb (q - v) = -((1 - s₀) * inner ℝ nb (v - u)) := by
          rw [inner_sub_right, hqr, ← neg_sub, ← inner_sub_right, hvb, real_inner_smul_right]
        rw [this]
        have : 0 < (1 - s₀) * inner ℝ nb (v - u) := mul_pos (by linarith) hnb
        linarith
      exact hsec nb (inner ℝ nb b) hnb.ne' q hqS.1 hqr hbot htop hnhds
    · intro hq
      have hqS : q ∈ C ∩ P := by
        rw [← hg.image_eq]
        exact image_mono (fun x hx => hx.1) hq
      have hnot : ¬ (C ∩ P ∈ 𝓝[P] q) := fun h => (hiff q hqS).mp h hq
      have hqC : q ∉ interior C := fun h =>
        hnot (by rw [inter_comm]; exact inter_mem_nhdsWithin P (mem_interior_iff_mem_nhds.mp h))
      have hqb := hCP q hqS.1 hqS.2
      have hqW := (hWQ.symm.subset hqS)
      exact ⟨hqW.1, subset_closure hqW.2, fun h => hqC (hintQ q hqb h)⟩
  have hsph : IsPLSphere 1 (g '' stdSimplexBoundary 2) :=
    ⟨g, hg.restrict isPolyhedron_stdSimplexBoundary_two fun x hx => hx.1⟩
  have huY : u ∈ Y := (hflatY.symm.subset ⟨by simp, mem_ball_self hρY⟩).1
  have hin : (frontier (Y ∪ C) ∩ interior W).Nonempty := by
    refine frontier_inter_interior_nonempty_of_subset_ball hW hQc ?_
      (fun x hx => hCP x ((hWQ.subset hx).1) ((hWQ.subset hx).2)) ?_
    · obtain ⟨y, hy⟩ := hY.interior_nonempty
      exact ⟨y, hYW (interior_subset hy), interior_mono subset_union_left hy⟩
    · obtain ⟨f, hf, t, ht, rfl⟩ := exists_mem_frontier_eq_sub_smul
        hW.isPolyhedron.isCompact.isBounded hWc (interior_subset (hYW huY)) hvu
      refine ⟨_, hf, fun hfb => ?_⟩
      rw [mem_ball, dist_eq_norm] at hfb
      have heq : u - t • (v - u) - b = -((t + s₀) • (v - u)) := by
        have h' : u - t • (v - u) - b = -(t • (v - u) + (b - u)) := by abel
        rw [h', hbu, add_smul]
      rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at hfb
      nlinarith
  have hvW : v ∉ W := notMem_of_flat_of_mem_segment hWc hρb hflatW hb hnb hsegW
  have hvQ : v ∈ frontier (Y ∪ C) := by
    have hvQ' : v ∈ Y ∪ C := (hflatQ.symm.subset ⟨by simp, mem_ball_self hρ'⟩).1
    refine ⟨subset_closure hvQ', notMem_interior_of_forall_add_smul (v := nb)
      (ε₀ := ρ' / (‖nb‖ + 1)) (div_pos hρ' (by positivity)) fun ε hε hεlt hmem => ?_⟩
    have hnn : 0 < inner ℝ nb nb := real_inner_self_pos.mpr hnb0
    have hmb : v + ε • nb ∈ ball v ρ' := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hε]
      rw [lt_div_iff₀ (by positivity)] at hεlt
      nlinarith [norm_nonneg nb]
    have hle := (hflatQ.subset ⟨hmem, hmb⟩).1
    change inner ℝ nb (v + ε • nb - v) ≤ 0 at hle
    rw [add_sub_cancel_left, real_inner_smul_right] at hle
    nlinarith
  have hcap := IsPLCellOn.sdiff_interior_of_frontier_inter (M := E3) hW.isPLCellOn_frontier
    hQ.isPLCellOn_frontier (isPolyhedralSphere_of_isPLSphere_one hsph) hcirc hin
    fun h => hvW (h hvQ)
  exact ⟨C, hCpoly.isCompact, fun x hx => (hCV' hx).1.1, hcap.1.isPLBall_three⟩

end DifferentialGeometry.Topology.PiecewiseLinear
