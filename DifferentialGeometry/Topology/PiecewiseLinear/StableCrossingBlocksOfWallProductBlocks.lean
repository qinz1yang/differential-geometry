/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.WallChartTransition
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlockRecentre
import DifferentialGeometry.Topology.PiecewiseLinear.GluedCellGlobalInvariants

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem AffineMap.eq_add_smul_of_eqOn_plane (H : ℝ × ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ × ℝ)
    {w₀ : ℝ × ℝ × ℝ} (hw₀ : w₀.2.2 = 0) {δ : ℝ} (hδ : 0 < δ)
    (hfix : ∀ w ∈ ball w₀ δ, w.2.2 = 0 → H w = w) (w : ℝ × ℝ × ℝ) :
    H w = w + w.2.2 • (H.linear (0, 0, 1) - (0, 0, 1)) := by
  have hH0 : H w₀ = w₀ := hfix w₀ (mem_ball_self hδ) hw₀
  have hsmall : ∀ v : ℝ × ℝ × ℝ, v.2.2 = 0 → ‖v‖ < δ → H.linear v = v := by
    intro v hv hvn
    have hm : v + w₀ ∈ ball w₀ δ := by rwa [mem_ball, dist_eq_norm, add_sub_cancel_right]
    have h1 := hfix (v + w₀) hm (by simp [hv, hw₀])
    have h2 : H (v + w₀) = H.linear v + H w₀ := H.map_vadd w₀ v
    rw [h2, hH0] at h1
    exact add_right_cancel h1
  have hplane : ∀ v : ℝ × ℝ × ℝ, v.2.2 = 0 → H.linear v = v := by
    intro v hv
    rcases eq_or_ne v 0 with h0 | h0
    · rw [h0, map_zero]
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr h0
      have hs : 0 < δ / (2 * ‖v‖) := by positivity
      have hsv : ‖(δ / (2 * ‖v‖)) • v‖ < δ := by
        rw [norm_smul, Real.norm_of_nonneg hs.le]
        have : δ / (2 * ‖v‖) * ‖v‖ = δ / 2 := by field_simp
        linarith
      have h1 := hsmall ((δ / (2 * ‖v‖)) • v) (by simp [hv]) hsv
      rw [map_smul] at h1
      exact smul_right_injective _ hs.ne' h1
  have hz : (w - w₀ - w.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ)).2.2 = 0 := by simp [hw₀]
  have hHw : H w = H.linear (w - w₀) + w₀ := by
    have h1 := H.map_vadd w₀ (w - w₀)
    rw [vadd_eq_add, vadd_eq_add, sub_add_cancel, hH0] at h1
    exact h1
  have hdec : w - w₀ = (w - w₀ - w.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ)) +
      w.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ) := by abel
  rw [hHw, hdec, map_add, map_smul, hplane _ hz, smul_sub]
  abel

theorem AffineMap.eq_mul_of_eq_zero_on_plane (G : ℝ × ℝ × ℝ →ᵃ[ℝ] ℝ)
    {w₀ : ℝ × ℝ × ℝ} (hw₀ : w₀.2.2 = 0) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ w ∈ ball w₀ δ, w.2.2 = 0 → G w = 0) (w : ℝ × ℝ × ℝ) :
    G w = G.linear (0, 0, 1) * w.2.2 := by
  have hG0 : G w₀ = 0 := hzero w₀ (mem_ball_self hδ) hw₀
  have hsmall : ∀ v : ℝ × ℝ × ℝ, v.2.2 = 0 → ‖v‖ < δ → G.linear v = 0 := by
    intro v hv hvn
    have hm : v + w₀ ∈ ball w₀ δ := by rwa [mem_ball, dist_eq_norm, add_sub_cancel_right]
    have h1 := hzero (v + w₀) hm (by simp [hv, hw₀])
    have h2 : G (v + w₀) = G.linear v + G w₀ := G.map_vadd w₀ v
    rw [h2, hG0, add_zero] at h1
    exact h1
  have hplane : ∀ v : ℝ × ℝ × ℝ, v.2.2 = 0 → G.linear v = 0 := by
    intro v hv
    rcases eq_or_ne v 0 with h0 | h0
    · rw [h0, map_zero]
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr h0
      have hs : 0 < δ / (2 * ‖v‖) := by positivity
      have hsv : ‖(δ / (2 * ‖v‖)) • v‖ < δ := by
        rw [norm_smul, Real.norm_of_nonneg hs.le]
        have : δ / (2 * ‖v‖) * ‖v‖ = δ / 2 := by field_simp
        linarith
      have h1 := hsmall ((δ / (2 * ‖v‖)) • v) (by simp [hv]) hsv
      rw [map_smul, smul_eq_mul] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hs.ne'
      · exact h2
  have hz : (w - w₀ - w.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ)).2.2 = 0 := by simp [hw₀]
  have hGw : G w = G.linear (w - w₀) := by
    have h1 := G.map_vadd w₀ (w - w₀)
    rw [vadd_eq_add, vadd_eq_add, sub_add_cancel, hG0, add_zero] at h1
    exact h1
  have hdec : w - w₀ = (w - w₀ - w.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ)) +
      w.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ) := by abel
  rw [hGw, hdec, map_add, map_smul, hplane _ hz, zero_add, smul_eq_mul, mul_comm]

theorem neg_add_eq_kink_zero (w₀ w : ℝ × ℝ × ℝ) :
    -w₀ + w = (w.1 + kinkOffset (-w₀.1) 0 w₀.2.2 w.2.2, w.2.1 + kinkOffset (-w₀.2.1) 0 w₀.2.2 w.2.2,
      kinkHeight w₀.2.2 0 w.2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_add, Prod.fst_neg, kinkOffset, zero_mul, add_zero]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, Prod.fst_add, Prod.fst_neg, kinkOffset, zero_mul,
      add_zero]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, kinkHeight, zero_mul, add_zero]
    ring

theorem neg_add_eq_kink_of_nonpos {w₀ q : ℝ × ℝ × ℝ} (v : ℝ × ℝ × ℝ) (hw₀ : w₀.2.2 = 0)
    (hq : q.2.2 ≤ 0) :
    -w₀ + q = (q.1 + kinkOffset (-w₀.1) v.1 w₀.2.2 q.2.2,
      q.2.1 + kinkOffset (-w₀.2.1) v.2.1 w₀.2.2 q.2.2, kinkHeight w₀.2.2 v.2.2 q.2.2) := by
  have hm : max (q.2.2 - w₀.2.2) 0 = 0 := by
    rw [hw₀, sub_zero]
    exact max_eq_right hq
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_add, Prod.fst_neg, kinkOffset, hm, mul_zero, add_zero]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, Prod.fst_add, Prod.fst_neg, kinkOffset, hm, mul_zero,
      add_zero]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, kinkHeight, hm, mul_zero, add_zero]
    ring

theorem neg_add_add_smul_eq_kink {w₀ q : ℝ × ℝ × ℝ} (v : ℝ × ℝ × ℝ) (hw₀ : w₀.2.2 = 0)
    (hq : 0 ≤ q.2.2) :
    -w₀ + (q + q.2.2 • v) = (q.1 + kinkOffset (-w₀.1) v.1 w₀.2.2 q.2.2,
      q.2.1 + kinkOffset (-w₀.2.1) v.2.1 w₀.2.2 q.2.2, kinkHeight w₀.2.2 v.2.2 q.2.2) := by
  have hm : max (q.2.2 - w₀.2.2) 0 = q.2.2 := by
    rw [hw₀, sub_zero]
    exact max_eq_left hq
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, smul_eq_mul, kinkOffset, hm]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, Prod.fst_add, Prod.fst_neg, Prod.smul_snd,
      Prod.smul_fst, smul_eq_mul, kinkOffset, hm]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, Prod.smul_snd, smul_eq_mul, kinkHeight, hw₀,
      sub_zero, max_eq_left hq]
    ring

theorem neg_add_scale_eq_kink {w₀ q : ℝ × ℝ × ℝ} (μ : ℝ) (hw₀ : w₀.2.2 = 0)
    (hq : 0 ≤ q.2.2) :
    -(w₀.1, w₀.2.1, (0 : ℝ)) + (q.1, q.2.1, μ * q.2.2) =
      (q.1 + kinkOffset (-w₀.1) 0 w₀.2.2 q.2.2, q.2.1 + kinkOffset (-w₀.2.1) 0 w₀.2.2 q.2.2,
        kinkHeight w₀.2.2 (μ - 1) q.2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_add, Prod.fst_neg, kinkOffset, zero_mul, add_zero]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, Prod.fst_add, Prod.fst_neg, kinkOffset, zero_mul,
      add_zero]
    ring
  · simp only [Prod.snd_add, Prod.snd_neg, kinkHeight, hw₀, sub_zero, max_eq_left hq,
      neg_zero, zero_add]
    ring

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem WallProductBlock.exists_isStableCrossingBlock_at [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M} {BdM C N : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ} {y : M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') {j i₀ : ι}
    (h : WallProductBlock f S (ec j) (ℓ j) BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hE : chartBlock (ec j) A r tlo ⊆ Eb j) (hyd : y ∈ doublePointSet f S)
    (hy : y ∈ innerChartBlock (ec j) A r tlo) (hy' : y ∈ Eb i₀) (hN : IsOpen N)
    (hyN : y ∈ N) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ)
      (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ),
      IsStableCrossingBlock f S (ec i₀) (ℓ i₀) BdM A' r' tlo' SA' SB' a' b' La Lb η ∧
        A' (ec i₀ y) = 0 ∧ chartBlock (ec i₀) A' r' tlo' ⊆ N := by
  classical
  obtain ⟨hstab, -, htype⟩ := h
  obtain ⟨hr, -, -, -, -, -, -, hside0, -⟩ := id hstab
  set w₀ := A (ec j y) with hw₀
  have htlo : tlo = -r ∨ tlo = 0 := hside0.imp (fun h => h.1) (fun h => h.1)
  have htle : tlo ≤ 0 := by
    rcases htlo with h | h
    · linarith
    · exact h.le
  have hyB : y ∈ chartBlock (ec j) A r tlo := chartBlock_mono_of_half (ec j) A hr.le htle hy
  have hyj : y ∈ (ec j).source := hyB.1
  have hyi₀ : y ∈ (ec i₀).source := hsys.layerSource i₀ (hsys.layerSubset i₀ hy')
  have hyEj : y ∈ Eb j := hE hyB
  have hw₀in : w₀ ∈ blockBox (r / 2) (tlo / 2) := hy.2
  have hw₀1 : |w₀.1| ≤ r / 2 := hw₀in.1
  have hw₀2 : |w₀.2.1| ≤ r / 2 := hw₀in.2.1
  have hw₀3 : tlo / 2 ≤ w₀.2.2 := hw₀in.2.2.1
  have hw₀4 : w₀.2.2 ≤ r / 2 := hw₀in.2.2.2
  have hcoord : ContinuousOn (fun z => A (ec j z)) (ec j).source :=
    A.toAffineMap.continuous_of_finiteDimensional.comp_continuousOn (ec j).continuousOn
  let OV : Set (ℝ × ℝ × ℝ) → Set M := fun V =>
    (ec j).source ∩ (fun z => A (ec j z)) ⁻¹' V ∩ (ec i₀).source ∩ N
  have hOVo : ∀ V, IsOpen V → IsOpen (OV V) := fun V hV =>
    ((hcoord.isOpen_inter_preimage (ec j).open_source hV).inter (ec i₀).open_source).inter hN
  have hOVsrc : ∀ V, OV V ⊆ (ec j).source ∩ (ec i₀).source :=
    fun V z hz => ⟨hz.1.1.1, hz.1.2⟩
  have hOVN : ∀ V, OV V ⊆ N := fun V z hz => hz.2
  let Bx : Set (ℝ × ℝ × ℝ) := {w | |w.1| < r ∧ |w.2.1| < r ∧ |w.2.2| < r}
  have hBxo : IsOpen Bx :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_snd.snd) continuous_const))
  have hw₀Bx : w₀ ∈ Bx := by
    have h3 : |w₀.2.2| ≤ r / 2 := by
      rw [abs_le]
      constructor
      · rcases htlo with ht | ht
        · rw [ht] at hw₀3
          linarith
        · rw [ht] at hw₀3
          linarith
      · exact hw₀4
    exact ⟨by linarith, by linarith, by linarith⟩
  have hinB : ∀ z ∈ OV Bx, (tlo = 0 → 0 ≤ (A (ec j z)).2.2) → z ∈ chartBlock (ec j) A r tlo := by
    intro z hz hprem
    obtain ⟨⟨⟨hzs, h1, h2, h3⟩, -⟩, -⟩ := hz
    refine ⟨hzs, ?_⟩
    change |(A (ec j z)).1| ≤ r ∧ |(A (ec j z)).2.1| ≤ r ∧ tlo ≤ (A (ec j z)).2.2 ∧
      (A (ec j z)).2.2 ≤ r
    rw [abs_lt] at h3
    refine ⟨h1.le, h2.le, ?_, h3.2.le⟩
    rcases htlo with ht | ht
    · rw [ht]
      exact h3.1.le
    · rw [ht]
      exact hprem ht
  have hcellSC : ∀ c ∈ wallSystemCells Q, y ∈ wallSystemCell ρ c →
      ∀ V : Set (ℝ × ℝ × ℝ), IsOpen V → w₀ ∈ V → V ⊆ Bx →
      (∀ z ∈ OV V, (tlo = 0 → 0 ≤ (A (ec j z)).2.2) → z ∈ wallSystemCell ρ c) →
      (∀ z ∈ OV V, tlo = 0 → w₀.2.2 ≠ 0 → 0 < (A (ec j z)).2.2) → (tlo = 0 → w₀.2.2 ≠ 0) →
      ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ)
        (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ),
        IsStableCrossingBlock f S (ec i₀) (ℓ i₀) BdM A' r' tlo' SA' SB' a' b' La Lb η ∧
          A' (ec i₀ y) = 0 ∧ chartBlock (ec i₀) A' r' tlo' ⊆ N := by
    intro c hc hyc V hV hw₀V hVBx hcellV hposV hnb
    have hcj : wallSystemCell ρ c ⊆ Eb' j := hsys.starLayer j c hc ⟨y, hyc, hyEj⟩
    have hci : wallSystemCell ρ c ⊆ Eb' i₀ := hsys.starLayer i₀ c hc ⟨y, hyc, hy'⟩
    obtain ⟨T, hT⟩ := hsys.exists_transition hc hcj hci
    let A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
      T.symm.trans (A.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-w₀)))
    have hA'app : ∀ x, A' x = -w₀ + A (T.symm x) := fun x => rfl
    have hyO : y ∈ OV V := ⟨⟨⟨hyj, hw₀V⟩, hyi₀⟩, hyN⟩
    have hA'y : A' (ec i₀ y) = 0 := by
      rw [hA'app, hT y hyc, T.symm_apply_apply, neg_add_cancel]
    obtain ⟨r', tlo', a', b', -, hblk, hsubO⟩ :=
      IsStableCrossingBlock.exists_kink_recentre (α₁ := 0) (β₁ := 0) (κ := 0) (ℓ' := ℓ i₀)
        (A' := A') hstab (hsys.chartBd j) hyd hy (by norm_num) (hOVo V hV) hyO (hOVsrc V)
        hposV hA'y
        (fun z hz hprem => by
          rw [hA'app, hT z (hcellV z hz hprem), T.symm_apply_apply]
          exact neg_add_eq_kink_zero w₀ _)
        (fun ht hw0 => absurd hw0 (hnb ht))
    exact ⟨A', r', tlo', _, _, a', b', hblk, hA'y, hsubO.trans (hOVN V)⟩
  have hOVmono : ∀ V, V ⊆ Bx → OV V ⊆ OV Bx :=
    fun V hV z hz => ⟨⟨⟨hz.1.1.1, hV hz.1.1.2⟩, hz.1.2⟩, hz.2⟩
  have hU₀ : ∀ V, IsOpen V → IsOpen ((fun z => A (ec j z)) '' OV V) := by
    intro V hV
    have h1 : IsOpen ((ec j) '' OV V) :=
      (ec j).isOpen_image_of_subset_source (hOVo V hV) (fun z hz => (hOVsrc V hz).1)
    have heq : (fun z => A (ec j z)) '' OV V = A.symm ⁻¹' ((ec j) '' OV V) := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, (A.symm_apply_apply _).symm⟩
      · rintro ⟨z, hz, hzq⟩
        exact ⟨z, hz, by simp only [hzq, A.apply_symm_apply]⟩
    rw [heq]
    exact h1.preimage A.symm.toAffineMap.continuous_of_finiteDimensional
  have hyO : y ∈ OV Bx := ⟨⟨⟨hyj, hw₀Bx⟩, hyi₀⟩, hyN⟩
  rcases htype with ⟨c, hc, htl, hcell⟩ |
      ⟨w, hw, cm, hcm, cp, hcp, htl, -, hwm, hwp, hcov, -, -, -, hzero, hsm, hsp⟩ |
      ⟨c, hc, w, -, htl, -, hheight, hCc, -, -, -⟩
  · have ht0 : tlo ≠ 0 := by
      rw [htl]
      exact (neg_neg_of_pos hr).ne
    exact hcellSC c hc (openSimplex_subset_convexHull c (hcell hyB)) Bx hBxo hw₀Bx subset_rfl
      (fun z hz hprem => openSimplex_subset_convexHull c (hcell (hinB z hz hprem)))
      (fun z _ ht => absurd ht ht0) (fun ht => absurd ht ht0)
  · have ht0 : tlo ≠ 0 := by
      rw [htl]
      exact (neg_neg_of_pos hr).ne
    have hOB : ∀ z ∈ OV Bx, z ∈ chartBlock (ec j) A r tlo :=
      fun z hz => hinB z hz (fun ht => absurd ht ht0)
    have hOm : ∀ z ∈ OV Bx, (A (ec j z)).2.2 ≤ 0 → z ∈ wallSystemCell ρ cm := by
      intro z hz ht
      rcases hcov (hOB z hz) with h1 | h1
      · exact h1
      · have h2 := hsp z ⟨hOB z hz, h1⟩
        have h3 : (A (ec j z)).2.2 = 0 := le_antisymm ht h2
        exact convexHull_mono (Finset.coe_subset.mpr hwm) ((hzero z (hOB z hz)).2 h3)
    have hOp : ∀ z ∈ OV Bx, 0 ≤ (A (ec j z)).2.2 → z ∈ wallSystemCell ρ cp := by
      intro z hz ht
      rcases hcov (hOB z hz) with h1 | h1
      · have h2 := hsm z ⟨hOB z hz, h1⟩
        have h3 : (A (ec j z)).2.2 = 0 := le_antisymm h2 ht
        exact convexHull_mono (Finset.coe_subset.mpr hwp) ((hzero z (hOB z hz)).2 h3)
      · exact h1
    rcases lt_trichotomy w₀.2.2 0 with hw0 | hw0 | hw0
    · have hVo : IsOpen (Bx ∩ {q : ℝ × ℝ × ℝ | q.2.2 < 0}) :=
        hBxo.inter (isOpen_lt continuous_snd.snd continuous_const)
      exact hcellSC cm hcm (hOm y hyO hw0.le) _ hVo ⟨hw₀Bx, hw0⟩ inter_subset_left
        (fun z hz _ => hOm z (hOVmono _ inter_subset_left hz) hz.1.1.2.2.le)
        (fun z _ ht => absurd ht ht0) (fun ht => absurd ht ht0)
    · have hyw : y ∈ wallSystemCell ρ w := (hzero y hyB).2 hw0
      have hycm : y ∈ wallSystemCell ρ cm := convexHull_mono (Finset.coe_subset.mpr hwm) hyw
      have hycp : y ∈ wallSystemCell ρ cp := convexHull_mono (Finset.coe_subset.mpr hwp) hyw
      obtain ⟨Tm, hTm⟩ := hsys.exists_transition hcm (hsys.starLayer j cm hcm ⟨y, hycm, hyEj⟩)
        (hsys.starLayer i₀ cm hcm ⟨y, hycm, hy'⟩)
      obtain ⟨Tp, hTp⟩ := hsys.exists_transition hcp (hsys.starLayer j cp hcp ⟨y, hycp, hyEj⟩)
        (hsys.starLayer i₀ cp hcp ⟨y, hycp, hy'⟩)
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hU₀ Bx hBxo) w₀ ⟨y, hyO, rfl⟩
      let H : ℝ × ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ × ℝ :=
        (A.symm.trans (Tp.trans (Tm.symm.trans A))).toAffineMap
      have hHapp : ∀ q, H q = A (Tm.symm (Tp (A.symm q))) := fun q => rfl
      have hHz : ∀ z ∈ OV Bx, 0 ≤ (A (ec j z)).2.2 →
          H (A (ec j z)) = A (Tm.symm (ec i₀ z)) := by
        intro z hz ht
        rw [hHapp, A.symm_apply_apply, ← hTp z (hOp z hz ht)]
      have hfix : ∀ q ∈ ball w₀ δ, q.2.2 = 0 → H q = q := by
        intro q hq hq0
        obtain ⟨z, hz, rfl⟩ := hball hq
        beta_reduce at hq0 ⊢
        rw [hHz z hz hq0.symm.le, hTm z (hOm z hz hq0.le), Tm.symm_apply_apply]
      have hform := AffineMap.eq_add_smul_of_eqOn_plane H hw0 hδ hfix
      set v₃ : ℝ × ℝ × ℝ := H.linear (0, 0, 1) - (0, 0, 1) with hv₃
      have hκ : -1 < v₃.2.2 := by
        by_contra hle
        rw [not_lt] at hle
        have hn : 0 < ‖H.linear (0, 0, 1)‖ + 1 := by positivity
        set δ' : ℝ := δ / (2 * (‖H.linear (0, 0, 1)‖ + 1)) with hδ'
        have hδ'pos : 0 < δ' := by positivity
        have hδ'n : δ' * (‖H.linear (0, 0, 1)‖ + 1) = δ / 2 := by
          rw [hδ']
          field_simp
        have he₃ : ‖((0, 0, 1) : ℝ × ℝ × ℝ)‖ = 1 := by simp
        have hq₁ : w₀ + δ' • ((0, 0, 1) : ℝ × ℝ × ℝ) ∈ ball w₀ δ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hδ'pos.le, he₃, mul_one]
          nlinarith [norm_nonneg (H.linear (0, 0, 1))]
        obtain ⟨z₁, hz₁, hq₁'⟩ := hball hq₁
        beta_reduce at hq₁'
        have ht₁ : (A (ec j z₁)).2.2 = δ' := by
          rw [hq₁']
          simp [hw0]
        have hHq₁ : H (A (ec j z₁)) = w₀ + δ' • H.linear (0, 0, 1) := by
          rw [hform, ht₁, hq₁', hv₃, smul_sub]
          abel
        have hq₂ : H (A (ec j z₁)) ∈ ball w₀ δ := by
          rw [hHq₁, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hδ'pos.le]
          nlinarith [norm_nonneg (H.linear (0, 0, 1))]
        obtain ⟨z₂, hz₂, hq₂'⟩ := hball hq₂
        beta_reduce at hq₂'
        have ht₂ : (A (ec j z₂)).2.2 = δ' * (1 + v₃.2.2) := by
          rw [hq₂', hform, ht₁]
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hq₁']
          simp [hw0]
          ring
        have ht₂le : (A (ec j z₂)).2.2 ≤ 0 := by
          rw [ht₂]
          nlinarith
        have h1 : A (ec j z₂) = A (Tm.symm (ec i₀ z₁)) := by
          rw [hq₂', hHz z₁ hz₁ (by rw [ht₁]; exact hδ'pos.le)]
        have h2 : ec j z₂ = Tm.symm (ec i₀ z₁) := A.injective h1
        have h3 : ec i₀ z₂ = ec i₀ z₁ := by
          rw [hTm z₂ (hOm z₂ hz₂ ht₂le), h2, Tm.apply_symm_apply]
        have h4 : z₂ = z₁ := (ec i₀).injOn (hOVsrc Bx hz₂).2 (hOVsrc Bx hz₁).2 h3
        rw [h4, ht₁] at ht₂
        have : δ' * v₃.2.2 = 0 := by linarith
        rcases mul_eq_zero.mp this with h5 | h5
        · linarith
        · linarith
      let A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
        Tm.symm.trans (A.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-w₀)))
      have hA'app : ∀ x, A' x = -w₀ + A (Tm.symm x) := fun x => rfl
      have hA'y : A' (ec i₀ y) = 0 := by
        rw [hA'app, hTm y hycm, Tm.symm_apply_apply, neg_add_cancel]
      obtain ⟨r', tlo', a', b', -, hblk, hsubO⟩ :=
        IsStableCrossingBlock.exists_kink_recentre (α₁ := v₃.1) (β₁ := v₃.2.1) (κ := v₃.2.2)
          (ℓ' := ℓ i₀) (A' := A') hstab (hsys.chartBd j) hyd hy hκ (hOVo Bx hBxo) hyO
          (hOVsrc Bx) (fun z _ ht => absurd ht ht0) hA'y
          (fun z hz _ => by
            rw [hA'app]
            rcases le_total (A (ec j z)).2.2 0 with ht | ht
            · rw [hTm z (hOm z hz ht), Tm.symm_apply_apply]
              exact neg_add_eq_kink_of_nonpos v₃ hw0 ht
            · rw [← hHz z hz ht, hform]
              exact neg_add_add_smul_eq_kink v₃ hw0 ht)
          (fun ht => absurd ht ht0)
      exact ⟨A', r', tlo', _, _, a', b', hblk, hA'y, hsubO.trans (hOVN Bx)⟩
    · have hVo : IsOpen (Bx ∩ {q : ℝ × ℝ × ℝ | 0 < q.2.2}) :=
        hBxo.inter (isOpen_lt continuous_const continuous_snd.snd)
      exact hcellSC cp hcp (hOp y hyO hw0.le) _ hVo ⟨hw₀Bx, hw0⟩ inter_subset_left
        (fun z hz _ => hOp z (hOVmono _ inter_subset_left hz) hz.1.1.2.2.le)
        (fun z _ ht => absurd ht ht0) (fun ht => absurd ht ht0)
  · have hw0nn : 0 ≤ w₀.2.2 := by
      rw [htl] at hw₀3
      linarith
    have hCiff : ∀ z ∈ (ec j).source, z ∈ C ↔ 0 ≤ (A (ec j z)).2.2 := by
      intro z hz
      rw [hheight]
      exact hsys.chartC j z hz
    have hBdiff : ∀ z ∈ (ec j).source, z ∈ BdM ↔ (A (ec j z)).2.2 = 0 := by
      intro z hz
      rw [hheight]
      exact hsys.chartBd j z hz
    rcases hw0nn.lt_or_eq with hw0 | hw0
    · have hVo : IsOpen (Bx ∩ {q : ℝ × ℝ × ℝ | 0 < q.2.2}) :=
        hBxo.inter (isOpen_lt continuous_const continuous_snd.snd)
      have hVc : ∀ z ∈ OV (Bx ∩ {q : ℝ × ℝ × ℝ | 0 < q.2.2}), z ∈ wallSystemCell ρ c := by
        intro z hz
        have hz' := hOVmono _ inter_subset_left hz
        have ht : 0 < (A (ec j z)).2.2 := hz.1.1.2.2
        exact hCc ⟨hinB z hz' (fun _ => ht.le), (hCiff z hz.1.1.1).2 ht.le⟩
      exact hcellSC c hc (hVc y ⟨⟨⟨hyj, hw₀Bx, hw0⟩, hyi₀⟩, hyN⟩) _ hVo ⟨hw₀Bx, hw0⟩
        inter_subset_left (fun z hz _ => hVc z hz) (fun z hz _ _ => hz.1.1.2.2)
        (fun _ => hw0.ne')
    · have hw0' : w₀.2.2 = 0 := hw0.symm
      have hOt : ∀ z ∈ OV Bx, 0 ≤ (A (ec j z)).2.2 → z ∈ wallSystemCell ρ c ∧ z ∈ C := by
        intro z hz ht
        have hzC : z ∈ C := (hCiff z hz.1.1.1).2 ht
        exact ⟨hCc ⟨hinB z hz (fun _ => ht), hzC⟩, hzC⟩
      have hyc : y ∈ wallSystemCell ρ c := (hOt y hyO hw0'.symm.le).1
      obtain ⟨T, hT⟩ := hsys.exists_transition hc (hsys.starLayer j c hc ⟨y, hyc, hyEj⟩)
        (hsys.starLayer i₀ c hc ⟨y, hyc, hy'⟩)
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hU₀ Bx hBxo) w₀ ⟨y, hyO, rfl⟩
      let G : ℝ × ℝ × ℝ →ᵃ[ℝ] ℝ :=
        (ℓ i₀).toAffineMap.comp (T.toAffineMap.comp A.symm.toAffineMap)
      have hGapp : ∀ q, G q = ℓ i₀ (T (A.symm q)) := fun q => rfl
      have hGz : ∀ z ∈ OV Bx, 0 ≤ (A (ec j z)).2.2 → G (A (ec j z)) = ℓ i₀ (ec i₀ z) := by
        intro z hz ht
        rw [hGapp, A.symm_apply_apply, ← hT z (hOt z hz ht).1]
      have hzero : ∀ q ∈ ball w₀ δ, q.2.2 = 0 → G q = 0 := by
        intro q hq hq0
        obtain ⟨z, hz, rfl⟩ := hball hq
        beta_reduce at hq0 ⊢
        rw [hGz z hz hq0.symm.le]
        exact (hsys.chartBd i₀ z (hOVsrc Bx hz).2).1 ((hBdiff z hz.1.1.1).2 hq0)
      have hGform := AffineMap.eq_mul_of_eq_zero_on_plane G hw0' hδ hzero
      set μ : ℝ := G.linear (0, 0, 1) with hμ
      have hμpos : 0 < μ := by
        have he₃ : ‖((0, 0, 1) : ℝ × ℝ × ℝ)‖ = 1 := by simp
        have hq₁ : w₀ + (δ / 2) • ((0, 0, 1) : ℝ × ℝ × ℝ) ∈ ball w₀ δ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg (by positivity), he₃, mul_one]
          linarith
        obtain ⟨z₁, hz₁, hq₁'⟩ := hball hq₁
        beta_reduce at hq₁'
        have ht₁ : (A (ec j z₁)).2.2 = δ / 2 := by
          rw [hq₁']
          simp [hw0']
        have hz₁C : z₁ ∈ C := (hOt z₁ hz₁ (by rw [ht₁]; positivity)).2
        have hz₁B : z₁ ∉ BdM := by
          rw [hBdiff z₁ hz₁.1.1.1, ht₁]
          positivity
        have hsrc₁ := (hOVsrc Bx hz₁).2
        have h1 : 0 ≤ ℓ i₀ (ec i₀ z₁) := (hsys.chartC i₀ z₁ hsrc₁).1 hz₁C
        have h2 : ℓ i₀ (ec i₀ z₁) ≠ 0 := fun h0 => hz₁B ((hsys.chartBd i₀ z₁ hsrc₁).2 h0)
        have h3 : ℓ i₀ (ec i₀ z₁) = μ * (δ / 2) := by
          rw [← hGz z₁ hz₁ (by rw [ht₁]; positivity), hGform, ht₁]
        have h4 : 0 < μ * (δ / 2) := by
          rw [← h3]
          exact lt_of_le_of_ne h1 (Ne.symm h2)
        exact pos_of_mul_pos_left h4 (by positivity)
      have hheight' : ∀ x, ℓ i₀ x = μ * (A (T.symm x)).2.2 := by
        intro x
        have h1 := hGform (A (T.symm x))
        rw [hGapp, A.symm_apply_apply, T.apply_symm_apply] at h1
        exact h1
      let D : ℝ × ℝ × ℝ ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
        ((LinearEquiv.refl ℝ ℝ).prodCongr ((LinearEquiv.refl ℝ ℝ).prodCongr
          (LinearEquiv.smulOfNeZero ℝ ℝ μ hμpos.ne'))).toAffineEquiv.trans
          (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-(w₀.1, w₀.2.1, (0 : ℝ))))
      have hDapp : ∀ q : ℝ × ℝ × ℝ,
          D q = -(w₀.1, w₀.2.1, (0 : ℝ)) + (q.1, q.2.1, μ * q.2.2) := fun q => rfl
      let A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ := T.symm.trans (A.trans D)
      have hA'app : ∀ x, A' x = D (A (T.symm x)) := fun x => rfl
      have hA'h : ∀ x, (A' x).2.2 = ℓ i₀ x := by
        intro x
        rw [hA'app, hDapp, hheight' x]
        simp
      have hA'y : A' (ec i₀ y) = 0 := by
        rw [hA'app, hT y hyc, T.symm_apply_apply, hDapp]
        rw [← hw₀, hw0']
        simp
      have hμ1 : -1 < μ - 1 := by linarith
      obtain ⟨r', tlo', a', b', -, hblk, hsubO⟩ :=
        IsStableCrossingBlock.exists_kink_recentre (α₁ := 0) (β₁ := 0) (κ := μ - 1)
          (ℓ' := ℓ i₀) (A' := A') hstab (hsys.chartBd j) hyd hy hμ1 (hOVo Bx hBxo) hyO
          (hOVsrc Bx) (fun z _ _ h0 => absurd hw0' h0) hA'y
          (fun z hz hprem => by
            have ht := hprem htl
            rw [hA'app, hT z (hOt z hz ht).1, T.symm_apply_apply, hDapp]
            exact neg_add_scale_eq_kink μ hw0' ht)
          (fun _ _ => ⟨hA'h, fun z hz => by
            rw [hA'h, ← hCiff z hz.1.1.1]
            exact hsys.chartC i₀ z (hOVsrc Bx hz).2⟩)
      exact ⟨A', r', tlo', _, _, a', b', hblk, hA'y, hsubO.trans (hOVN Bx)⟩

theorem hasStableCrossingBlocks_of_wallProductBlocks [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M}
    {BdM C Z Z' : Set M} {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {Cf Bf : Set (Finset Ea)} {η κ : ℝ}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb')
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η)
    (hScpt : IsCompact S) (hcont : ContinuousOn f S) (hmapC : MapsTo f S C)
    (hκ : 0 < κ) (hinj : UniformInjectivityScale S f κ)
    (i₀ : ι) (hZ'cpt : IsCompact Z') (hZ'Z : Z' ⊆ Z) (hZ'E : Z' ⊆ interior (Eb i₀)) :
    HasStableCrossingBlocks f S (ec i₀) (ℓ i₀) BdM Z' η := by
  obtain ⟨hη, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, -, hZN, hcov, hE, hblk⟩ := h
  have hloc : IsLocallyInjective (S.domRestrict f) := by
    intro x
    refine ⟨ball x (κ / 2), isOpen_ball, mem_ball_self (half_pos hκ), ?_⟩
    intro x₁ hx₁ x₂ hx₂ heq
    apply Subtype.ext
    refine hinj x₁ x₁.2 x₂ x₂.2 ?_ heq
    have h1 : dist x₁ x₂ < κ := by
      calc dist x₁ x₂ ≤ dist x₁ x + dist x x₂ := dist_triangle _ _ _
        _ < κ / 2 + κ / 2 := by
          rw [dist_comm x x₂]
          exact add_lt_add (mem_ball.mp hx₁) (mem_ball.mp hx₂)
        _ = κ := by ring
    exact h1
  have hK : IsCompact (doublePointSet f S ∩ Z') :=
    (isCompact_doublePointSet_of_isLocallyInjective hScpt hcont hloc).inter_right
      hZ'cpt.isClosed
  have key : ∀ y : ↥(doublePointSet f S ∩ Z'),
      ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ)
        (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ) (La' Lb' : ℝ),
        IsStableCrossingBlock f S (ec i₀) (ℓ i₀) BdM A' r' tlo' SA' SB' a' b' La' Lb' η ∧
          (y : M) ∈ (ec i₀).source ∩ (fun z => A' (ec i₀ z)) ⁻¹'
            {w | |w.1| < r' / 2 ∧ |w.2.1| < r' / 2 ∧ |w.2.2| < r' / 2} := by
    rintro ⟨y, hyd, hyZ'⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov ⟨hyd, hZN (hZ'Z hyZ')⟩)
    have hy' : y ∈ Eb i₀ := interior_subset (hZ'E hyZ')
    obtain ⟨A', r', tlo', SA', SB', a', b', hblk', hA'y, -⟩ :=
      WallProductBlock.exists_isStableCrossingBlock_at hsys (hblk k) (hE k) hyd hk hy'
        isOpen_univ (mem_univ y)
    have hr' : 0 < r' := hblk'.1
    refine ⟨A', r', tlo', SA', SB', a', b', La k, Lb k, hblk', ?_, ?_⟩
    · exact hsys.layerSource i₀ (hsys.layerSubset i₀ hy')
    · change |(A' (ec i₀ y)).1| < r' / 2 ∧ |(A' (ec i₀ y)).2.1| < r' / 2 ∧
        |(A' (ec i₀ y)).2.2| < r' / 2
      rw [hA'y]
      simp only [Prod.fst_zero, Prod.snd_zero, abs_zero]
      exact ⟨half_pos hr', half_pos hr', half_pos hr'⟩
  choose A' r' tlo' SA' SB' a' b' La' Lb' hblk' hmem using key
  let W : ↥(doublePointSet f S ∩ Z') → Set M := fun y => (ec i₀).source ∩
    (fun z => A' y (ec i₀ z)) ⁻¹' {w | |w.1| < r' y / 2 ∧ |w.2.1| < r' y / 2 ∧ |w.2.2| < r' y / 2}
  have hWo : ∀ y, IsOpen (W y) := by
    intro y
    have hc : ContinuousOn (fun z => A' y (ec i₀ z)) (ec i₀).source :=
      (A' y).toAffineMap.continuous_of_finiteDimensional.comp_continuousOn (ec i₀).continuousOn
    exact hc.isOpen_inter_preimage (ec i₀).open_source
      ((isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
          (isOpen_lt (continuous_abs.comp continuous_snd.snd) continuous_const)))
  have hWin : ∀ y, ∀ z ∈ doublePointSet f S ∩ W y,
      z ∈ innerChartBlock (ec i₀) (A' y) (r' y) (tlo' y) := by
    rintro y z ⟨hzd, hzs, hz1, hz2, hz3⟩
    beta_reduce at hz1 hz2 hz3
    obtain ⟨hr, -, -, -, -, -, -, hside, -⟩ := id (hblk' y)
    refine ⟨hzs, ?_⟩
    change |(A' y (ec i₀ z)).1| ≤ r' y / 2 ∧ |(A' y (ec i₀ z)).2.1| ≤ r' y / 2 ∧
      tlo' y / 2 ≤ (A' y (ec i₀ z)).2.2 ∧ (A' y (ec i₀ z)).2.2 ≤ r' y / 2
    rw [abs_lt] at hz3
    refine ⟨hz1.le, hz2.le, ?_, hz3.2.le⟩
    rcases hside with ⟨ht, -⟩ | ⟨ht, hheight, -⟩
    · rw [ht]
      linarith [hz3.1]
    · rw [ht, zero_div, hheight]
      obtain ⟨x, hx, -, -, -, hfx, -⟩ := hzd
      have hzC : z ∈ C := hfx ▸ hmapC hx
      exact (hsys.chartC i₀ z hzs).1 hzC
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover W hWo fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hmem _⟩
  let p : Fin t.card → ↥(doublePointSet f S ∩ Z') := fun i => (t.equivFin.symm i : ↥t)
  refine ⟨hη, t.card, fun i => A' (p i), fun i => r' (p i), fun i => tlo' (p i),
    fun i => SA' (p i), fun i => SB' (p i), fun i => a' (p i), fun i => b' (p i),
    fun i => La' (p i), fun i => Lb' (p i), ?_, fun i => hblk' (p i)⟩
  intro z hz
  obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.mp (ht hz)
  refine mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
  have hp : p (t.equivFin ⟨y, hyt⟩) = y := by
    exact congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨y, hyt⟩)
  change z ∈ innerChartBlock (ec i₀) (A' (p (t.equivFin ⟨y, hyt⟩)))
    (r' (p (t.equivFin ⟨y, hyt⟩))) (tlo' (p (t.equivFin ⟨y, hyt⟩)))
  rw [hp]
  exact hWin y z ⟨hz.1, hzy⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
