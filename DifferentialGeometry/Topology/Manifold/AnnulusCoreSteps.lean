/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.PolarBandChart
import DifferentialGeometry.Topology.Manifold.SurfaceChartSmoothing
import DifferentialGeometry.Topology.Homeomorph.DisjointFamily
import Mathlib.Analysis.Real.Pi.Bounds

open Set Metric Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Manifold

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

theorem exists_polarStrip_chart {S : Type*} [TopologicalSpace S]
    (F : OpenPartialHomeomorph Plane S) (hF : {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆ F.source)
    (p : Plane) (hp : p 1 = 0) :
    ∃ κ : OpenPartialHomeomorph Plane S, κ.source = planeOpenRect (-1) 3 (-(1 / 2)) (1 / 2) ∧
      ∀ v ∈ κ.source, κ v = F (polarStripMap (p + v)) := by
  set R := planeOpenRect (-1) 3 (-(1 / 2)) (1 / 2) with hR
  have hg : ContinuousOn (fun v => polarStripMap (p + v)) R :=
    (contDiff_polarStripMap.continuous.comp (continuous_const.add continuous_id)).continuousOn
  have hinj : InjOn (fun v => polarStripMap (p + v)) R := by
    intro v hv w hw hvw
    have h1 : |(p + v) 1| < 3 / 2 := by
      rw [PiLp.add_apply, hp, zero_add, abs_lt]
      exact ⟨by linarith [hv.2.2.1], by linarith [hv.2.2.2]⟩
    have h2 : |(p + w) 1| < 3 / 2 := by
      rw [PiLp.add_apply, hp, zero_add, abs_lt]
      exact ⟨by linarith [hw.2.2.1], by linarith [hw.2.2.2]⟩
    have h3 : |(p + v) 0 - (p + w) 0| < 2 * Real.pi := by
      rw [PiLp.add_apply, PiLp.add_apply, add_sub_add_left_eq_sub, abs_lt]
      constructor <;> linarith [hv.1, hv.2.1, hw.1, hw.2.1, Real.pi_gt_three]
    exact add_left_cancel (polarStripMap_injective_of_abs_sub_lt h1 h2 h3 hvw)
  obtain ⟨κ₀, hκ₀s, hκ₀e⟩ :=
    exists_openPartialHomeomorph_of_continuousOn_injOn (isOpen_planeOpenRect _ _ _ _) hg hinj
  refine ⟨κ₀.trans F, ?_, fun v hv => ?_⟩
  · rw [OpenPartialHomeomorph.trans_source, hκ₀s]
    refine inter_eq_left.mpr fun v hv => hF ?_
    rw [hκ₀e (hκ₀s ▸ hv)]
    change 1 < ‖polarStripMap (p + v)‖ ∧ ‖polarStripMap (p + v)‖ < 2
    rw [norm_polarStripMap, PiLp.add_apply, hp, zero_add,
      abs_of_pos (by linarith [hv.2.2.1] : 0 < 3 / 2 + v 1)]
    exact ⟨by linarith [hv.2.2.1], by linarith [hv.2.2.2]⟩
  · have hv' : v ∈ κ₀.source := by
      rw [OpenPartialHomeomorph.trans_source] at hv
      exact hv.1
    change F (κ₀ v) = _
    rw [hκ₀e (hκ₀s ▸ hv')]

theorem eq_and_eq_zero_of_abs_sub_lt {n j k : ℕ} (hj : j < n) (hk : k < n) {m : ℤ}
    (h : |(j : ℝ) - k - n * m| < 1) : j = k ∧ m = 0 := by
  have hz : ((j : ℤ) - k - n * m : ℤ) = 0 := by
    rw [abs_lt] at h
    have h1 : (((j : ℤ) - k - n * m : ℤ) : ℝ) < 1 := by push_cast; linarith
    have h2 : (-1 : ℝ) < (((j : ℤ) - k - n * m : ℤ) : ℝ) := by push_cast; linarith
    have h1' : ((j : ℤ) - k - n * m : ℤ) < 1 := by exact_mod_cast h1
    have h2' : (-1 : ℤ) < ((j : ℤ) - k - n * m : ℤ) := by exact_mod_cast h2
    omega
  have hn : (0 : ℤ) < n := by omega
  have hm1 : (n : ℤ) * m < n * 1 := by
    have : (n : ℤ) * m = j - k := by linarith
    rw [this]
    omega
  have hm2 : (n : ℤ) * (-1) < n * m := by
    have : (n : ℤ) * m = j - k := by linarith
    rw [this]
    omega
  have hm1' := (mul_lt_mul_iff_right₀ hn).mp hm1
  have hm2' := (mul_lt_mul_iff_right₀ hn).mp hm2
  have hm : m = 0 := by omega
  subst hm
  constructor
  · omega
  · rfl

theorem homeomorph_mem_of_eqOn_compl {X : Type*} (a : X ≃ X) {K : Set X}
    (ha : EqOn a id Kᶜ) {y : X} (hy : y ∈ K) : a y ∈ K := by
  by_contra hn
  have h1 : a (a y) = a y := ha hn
  have h2 : a y = y := a.injective h1
  apply hn
  rw [h2]
  exact hy

theorem exists_isotopy_smooth_polar_junctions {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Plane S] [IsManifold 𝓘(ℝ, Plane) ∞ S] (Φ : OpenPartialHomeomorph Plane S)
    (hΦ : {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆ Φ.source) {n : ℕ} (hn : 0 < n) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hr₀α : r₀ ≤ 2 * Real.pi / n / 8) (hr₀1 : r₀ ≤ 1 / 4) :
    ∃ J : ℝ → S ≃ₜ S, Continuous (fun p : ℝ × S => J p.1 p.2) ∧
      Continuous (fun p : ℝ × S => (J p.1).symm p.2) ∧ J 0 = Homeomorph.refl S ∧
      (∀ y : Plane, |y 1| < 1 / 2 → ∃ y' : Plane, dist y' y < 2 * r₀ ∧ |y' 1| < 1 / 2 ∧
        J 1 (Φ (polarStripMap y)) = Φ (polarStripMap y')) ∧
      ∃ r > 0, ∀ k : Fin n, ∃ c : OpenPartialHomeomorph Plane S,
        c.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S ∧ ball 0 r ⊆ c.source ∧
        ∀ v ∈ ball (0 : Plane) r,
          J 1 (Φ (polarStripMap (Plane.mk (2 * Real.pi / n * k) 0 + v))) = c v := by
  classical
  set α : ℝ := 2 * Real.pi / n with hαdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hα : 0 < α := div_pos Real.two_pi_pos hnR
  have hnα : (n : ℝ) * α = 2 * Real.pi := by
    rw [hαdef]
    field_simp
  let p : Fin n → Plane := fun k => Plane.mk (α * k) 0
  have hp1 : ∀ k, p k 1 = 0 := fun k => rfl
  have hchart : ∀ k : Fin n, ∃ κ : OpenPartialHomeomorph Plane S,
      κ.source = planeOpenRect (-1) 3 (-(1 / 2)) (1 / 2) ∧
        ∀ v ∈ κ.source, κ v = Φ (polarStripMap (p k + v)) :=
    fun k => exists_polarStrip_chart Φ hΦ (p k) (hp1 k)
  choose κ hκs hκe using hchart
  have hballs : ball (0 : Plane) r₀ ⊆ planeOpenRect (-1) 3 (-(1 / 2)) (1 / 2) := by
    intro v hv
    have h0 := (planeAbsSub_le_dist v 0 0).trans (mem_ball.mp hv).le
    have h1 := (planeAbsSub_le_dist v 0 1).trans (mem_ball.mp hv).le
    simp only [PiLp.zero_apply, sub_zero] at h0 h1
    rw [abs_le] at h0 h1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hsep : ∀ j k : Fin n, ∀ v ∈ ball (0 : Plane) r₀, ∀ w ∈ ball (0 : Plane) r₀,
      κ j v = κ k w → j = k := by
    intro j k v hv w hw hjk
    rw [hκe j v (hκs j ▸ hballs hv), hκe k w (hκs k ▸ hballs hw)] at hjk
    have hann : ∀ u ∈ ball (0 : Plane) r₀, ∀ i : Fin n,
        polarStripMap (p i + u) ∈ Φ.source := by
      intro u hu i
      apply hΦ
      change 1 < ‖polarStripMap (p i + u)‖ ∧ ‖polarStripMap (p i + u)‖ < 2
      have hu1 := (planeAbsSub_le_dist u 0 1).trans (mem_ball.mp hu).le
      simp only [PiLp.zero_apply, sub_zero] at hu1
      rw [abs_le] at hu1
      rw [norm_polarStripMap, PiLp.add_apply, hp1, zero_add,
        abs_of_pos (by linarith : 0 < 3 / 2 + u 1)]
      exact ⟨by linarith, by linarith⟩
    have hPi := Φ.injOn (hann v hv j) (hann w hw k) hjk
    have hv1 := (planeAbsSub_le_dist v 0 1).trans (mem_ball.mp hv).le
    have hw1 := (planeAbsSub_le_dist w 0 1).trans (mem_ball.mp hw).le
    have hv0 := (planeAbsSub_le_dist v 0 0).trans (mem_ball.mp hv).le
    have hw0 := (planeAbsSub_le_dist w 0 0).trans (mem_ball.mp hw).le
    simp only [PiLp.zero_apply, sub_zero] at hv1 hw1 hv0 hw0
    rw [abs_le] at hv1 hw1 hv0 hw0
    obtain ⟨-, m, hm⟩ := polarStripMap_eq_polarStripMap
      (by rw [PiLp.add_apply, hp1, zero_add, abs_lt]; constructor <;> linarith)
      (by rw [PiLp.add_apply, hp1, zero_add, abs_lt]; constructor <;> linarith) hPi
    simp only [PiLp.add_apply] at hm
    change α * j + v 0 = α * k + w 0 + 2 * Real.pi * m at hm
    have hkey : |(j : ℝ) - k - n * m| < 1 := by
      have heq : α * ((j : ℝ) - k - n * m) = w 0 - v 0 := by
        rw [← hnα] at hm
        linarith
      have hb : |α * ((j : ℝ) - k - n * m)| < α := by
        rw [heq, abs_lt]
        have : r₀ * 8 ≤ α := by linarith [hr₀α]
        constructor <;> linarith
      rw [abs_mul, abs_of_pos hα] at hb
      nlinarith [abs_nonneg ((j : ℝ) - k - n * m)]
    exact Fin.ext (eq_and_eq_zero_of_abs_sub_lt j.2 k.2 hkey).1
  have hT1 : ∀ k : Fin n, ∃ K : Set Plane, IsCompact K ∧ K ⊆ ball 0 r₀ ∧
      ∃ a : ℝ → Plane ≃ₜ Plane, (∀ t, EqOn (a t) id Kᶜ) ∧
        ∃ J' : ℝ → S ≃ₜ S, Continuous (fun q : ℝ × S => J' q.1 q.2) ∧
          Continuous (fun q : ℝ × S => (J' q.1).symm q.2) ∧ J' 0 = Homeomorph.refl S ∧
          (∀ t, EqOn (J' t) id (κ k '' K)ᶜ) ∧
          (∀ t q, q ∈ (κ k).source → J' t (κ k q) = κ k (a t q)) ∧
          ∃ r > 0, ∃ c : OpenPartialHomeomorph Plane S, c.source = ball 0 r ∧
            ball (0 : Plane) r ⊆ ball (0 : Plane) r₀ ∧ (∀ q, c q = κ k (a 1 q)) ∧
            c.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S := by
    intro k
    obtain ⟨K, hK, hKU, -, a, -, -, -, -, hafix, J', hJ'c, hJ'i, hJ'0, hJ'fix, hframe, r, hr, c,
      hcs, hcU, hca, -, hcmax, -⟩ := exists_isotopy_smoothing_surface_chart (κ k) isOpen_ball
      (mem_ball_self hr₀) (hκs k ▸ hballs)
    exact ⟨K, hK, hKU, a, fun t => (hafix t).1, J', hJ'c, hJ'i, hJ'0, fun t => (hJ'fix t).1,
      fun t q hq => (hframe t q hq).1, r, hr, c, hcs, hcU, hca, hcmax⟩
  choose K hK hKU a hafix J' hJ'c hJ'i hJ'0 hJ'fix hframe r hr c hcs hcU hca hcmax using hT1
  have hdis : Pairwise fun i j => Disjoint (κ i '' K i) (κ j '' K j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
    exact hij (hsep j i w (hKU j hw) v (hKU i hv) hvw).symm
  obtain ⟨Jg, hJgc, hJgi, hJgeq, hJgfix, hJgrefl⟩ :=
    Homeomorph.exists_gluing_family_of_pairwise_disjoint J' (fun k => κ k '' K k) hJ'c hJ'i
      (fun k t => hJ'fix k t) hdis
  have hJg0 : Jg 0 = Homeomorph.refl S := hJgrefl 0 fun k => hJ'0 k
  have hJgκ : ∀ k : Fin n, ∀ v ∈ ball (0 : Plane) r₀, Jg 1 (κ k v) = J' k 1 (κ k v) := by
    intro k v hv
    by_cases hin : κ k v ∈ κ k '' K k
    · exact hJgeq k 1 hin
    · have hout : κ k v ∉ ⋃ i, κ i '' K i := by
        rw [mem_iUnion]
        rintro ⟨i, w, hw, hwv⟩
        have hik := hsep i k w (hKU i hw) v hv hwv
        subst hik
        exact hin ⟨w, hw, hwv⟩
      rw [(hJgfix 1).1 hout, hJ'fix k 1 hin]
  have hannu : ∀ u : Plane, |u 1| < 1 / 2 → polarStripMap u ∈ Φ.source := by
    intro u hu
    apply hΦ
    change 1 < ‖polarStripMap u‖ ∧ ‖polarStripMap u‖ < 2
    rw [abs_lt] at hu
    rw [norm_polarStripMap, abs_of_pos (by linarith : 0 < 3 / 2 + u 1)]
    exact ⟨by linarith, by linarith⟩
  have hsmall1 : ∀ u ∈ ball (0 : Plane) r₀, |u 1| < r₀ := by
    intro u hu
    have h := planeAbsSub_le_dist u 0 1
    simp only [PiLp.zero_apply, sub_zero] at h
    exact lt_of_le_of_lt h (mem_ball.mp hu)
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set rmin : ℝ := Finset.univ.inf' hne r with hrmin
  have hrmin_pos : 0 < rmin := (Finset.lt_inf'_iff hne).mpr fun k _ => hr k
  have hrmin_le : ∀ k, rmin ≤ r k := fun k => Finset.inf'_le _ (Finset.mem_univ k)
  refine ⟨Jg, hJgc, hJgi, hJg0, ?_, rmin, hrmin_pos, fun k => ⟨c k, hcmax k, ?_, ?_⟩⟩
  · intro y hy
    by_cases hin : Φ (polarStripMap y) ∈ ⋃ i, κ i '' K i
    · obtain ⟨k, v, hv, hvy⟩ := mem_iUnion.mp hin
      have hvb := hKU k hv
      have havK : a k 1 v ∈ K k := homeomorph_mem_of_eqOn_compl (a k 1).toEquiv (hafix k 1) hv
      have havb := hKU k havK
      have hvs : v ∈ (κ k).source := hκs k ▸ hballs hvb
      have havs : a k 1 v ∈ (κ k).source := hκs k ▸ hballs havb
      have hpv1 : (p k + v) 1 = v 1 := by rw [PiLp.add_apply, hp1, zero_add]
      have hpa1 : (p k + a k 1 v) 1 = a k 1 v 1 := by rw [PiLp.add_apply, hp1, zero_add]
      have hv1 := hsmall1 v hvb
      have hav1 := hsmall1 _ havb
      have hPi : polarStripMap (p k + v) = polarStripMap y := by
        rw [hκe k v hvs] at hvy
        exact Φ.injOn (hannu _ (by rw [hpv1]; linarith)) (hannu y hy) hvy
      obtain ⟨hy1, m, hm⟩ := polarStripMap_eq_polarStripMap
        (by rw [hpv1]; rw [abs_lt] at hv1 ⊢; constructor <;> linarith)
        (by rw [abs_lt] at hy ⊢; constructor <;> linarith) hPi
      set y' : Plane := Plane.mk ((p k + a k 1 v) 0 - 2 * Real.pi * m) (a k 1 v 1) with hy'
      have hy'P : polarStripMap y' = polarStripMap (p k + a k 1 v) := by
        have h1 : y' = Plane.mk ((p k + a k 1 v) 0 + 2 * Real.pi * ((-m : ℤ) : ℝ))
            ((p k + a k 1 v) 1) := by
          rw [hy', hpa1]
          push_cast
          ring_nf
        have h2 : Plane.mk ((p k + a k 1 v) 0) ((p k + a k 1 v) 1) = p k + a k 1 v := by
          ext i
          fin_cases i <;> rfl
        rw [h1, polarStripMap_add_two_pi_mul, h2]
      have hdist : dist y' y = dist (a k 1 v) v := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        ext i
        fin_cases i
        · change (p k + a k 1 v) 0 - 2 * Real.pi * m - y 0 = a k 1 v 0 - v 0
          simp only [PiLp.add_apply] at hm ⊢
          linarith
        · change a k 1 v 1 - y 1 = a k 1 v 1 - v 1
          rw [← hy1, hpv1]
      refine ⟨y', ?_, ?_, ?_⟩
      · rw [hdist]
        calc dist (a k 1 v) v ≤ dist (a k 1 v) 0 + dist v 0 := dist_triangle_right _ _ _
          _ < r₀ + r₀ := add_lt_add (mem_ball.mp havb) (mem_ball.mp hvb)
          _ = 2 * r₀ := by ring
      · change |a k 1 v 1| < 1 / 2
        linarith
      · rw [← hvy, hJgκ k v hvb, hframe k 1 v hvs, hκe k _ havs, hy'P]
    · exact ⟨y, by rw [dist_self]; exact mul_pos two_pos hr₀, hy, (hJgfix 1).1 hin⟩
  · exact (ball_subset_ball (hrmin_le k)).trans (hcs k).symm.subset
  · intro v hv
    have hvk : v ∈ ball (0 : Plane) (r k) := ball_subset_ball (hrmin_le k) hv
    have hv0 : v ∈ ball (0 : Plane) r₀ := hcU k hvk
    have hvs : v ∈ (κ k).source := hκs k ▸ hballs hv0
    change Jg 1 (Φ (polarStripMap (p k + v))) = c k v
    rw [← hκe k v hvs, hJgκ k v hv0, hframe k 1 v hvs, hca]

theorem exists_isotopy_smooth_arc_chart {S : Type*} [TopologicalSpace S] [T2Space S]
    (κ : OpenPartialHomeomorph Plane S) (b : OpenPartialHomeomorph S Plane)
    {τa τb ρ₀ W : ℝ} (hρ₀ : 0 < ρ₀) (hW : 0 < W) (hab : τa + 2 * ρ₀ < τb - 2 * ρ₀)
    (hR : planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W ⊆ κ.source)
    (hRb : ∀ v ∈ planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W, κ v ∈ b.source)
    (hsa : ContDiffOn ℝ ∞ (fun v => b (κ v)) (ball (Plane.mk τa 0) ρ₀))
    (hsb : ContDiffOn ℝ ∞ (fun v => b (κ v)) (ball (Plane.mk τb 0) ρ₀))
    (hda : ∀ v ∈ ball (Plane.mk τa 0) ρ₀,
      LinearMap.det (fderiv ℝ (fun v => b (κ v)) v : Plane →ₗ[ℝ] Plane) ≠ 0)
    (hdb : ∀ v ∈ ball (Plane.mk τb 0) ρ₀,
      LinearMap.det (fderiv ℝ (fun v => b (κ v)) v : Plane →ₗ[ℝ] Plane) ≠ 0) :
    ∃ ρ > 0, ρ ≤ ρ₀ ∧ ∃ δ > 0, δ < W ∧ ∃ h : Plane ≃ₜ Plane,
      (∀ v : Plane, |v 1| < δ → (v 0 ≤ τa - ρ ∨ τb + ρ ≤ v 0) → h v = v) ∧
      (∀ v ∈ planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ, κ (h v) ∈ b.source) ∧
      ContDiffOn ℝ ∞ (fun v => b (κ (h v))) (planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ) ∧
      (∀ v ∈ planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ,
        LinearMap.det (fderiv ℝ (fun v => b (κ (h v))) v : Plane →ₗ[ℝ] Plane) ≠ 0) ∧
      ∃ G : ℝ → S ≃ₜ S, Continuous (fun q : ℝ × S => G q.1 q.2) ∧
        Continuous (fun q : ℝ × S => (G q.1).symm q.2) ∧ G 0 = Homeomorph.refl S ∧
        (∀ t, EqOn (G t) id (κ '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W)ᶜ) ∧
        ∀ v ∈ κ.source, G 1 (κ v) = κ (h v) := by
  set R₀ := planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W with hR₀
  have hcont : ContinuousOn (fun v => b (κ v)) R₀ :=
    b.continuousOn.comp (κ.continuousOn.mono hR) hRb
  have hinj : InjOn (fun v => b (κ v)) R₀ := fun x hx y hy hxy =>
    κ.injOn (hR hx) (hR hy) (b.injOn (hRb x hx) (hRb y hy) hxy)
  obtain ⟨ρ, hρ, hρρ₀, h, hhid, δ, hδ, hδW, hends, hsm, hdet⟩ :=
    exists_homeomorph_smooth_arc hρ₀ hW hab hcont hinj isOpen_ball isOpen_ball
      (mem_ball_self hρ₀) (mem_ball_self hρ₀) hsa hsb hda hdb
  have hab' : τa - 3 * ρ < τb + 3 * ρ := by linarith
  have hsubR : planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W ⊆ R₀ := fun v hv =>
    ⟨by linarith [hv.1], by linarith [hv.2.1], hv.2.2.1, hv.2.2.2⟩
  have hopenC : planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W ⊆
      planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W := fun v hv =>
    ⟨hv.1.le, hv.2.1.le, hv.2.2.1.le, hv.2.2.2.le⟩
  have hmaps : ∀ v ∈ planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ, κ (h v) ∈ b.source := by
    intro v hv
    have hv' : v ∈ planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W :=
      ⟨hv.1, hv.2.1, by linarith [hv.2.2.1], by linarith [hv.2.2.2]⟩
    exact hRb _ (hsubR (hopenC (homeomorph_mem_of_eqOn_compl h.toEquiv hhid hv')))
  obtain ⟨D, hDc, hDi, hD0, hD1, hDfix⟩ :=
    exists_isotopy_eqOn_compl_planeOpenRect hab' (by linarith : -W < W) h hhid
  set C := planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W with hC
  have hCc : IsCompact C := isCompact_planeRect hab' (by linarith)
  have hCt : C ⊆ κ.symm.target := by
    rw [OpenPartialHomeomorph.symm_target]
    exact hsubR.trans hR
  have hfix : ∀ t, EqOn (D t) id Cᶜ ∧ EqOn (D t).symm id Cᶜ := fun t =>
    ⟨(hDfix t).1.mono (compl_subset_compl.mpr hopenC),
      (hDfix t).2.mono (compl_subset_compl.mpr hopenC)⟩
  obtain ⟨G, hGc, hGi, hGe, hGfix⟩ :=
    κ.symm.exists_conjugate_homeomorph_family D hDc hDi hCc hCt hfix
  have hG0 : G 0 = Homeomorph.refl S := by
    refine Homeomorph.ext fun y => ?_
    rw [(hGe 0 y).1, hD0]
    by_cases hy : y ∈ κ.target
    · rw [κ.symm.conjugateMap_of_mem _ hy]
      exact κ.right_inv hy
    · exact κ.symm.conjugateMap_of_notMem _ hy
  refine ⟨ρ, hρ, hρρ₀, δ, hδ, hδW, h, hends, hmaps, hsm, hdet, G, hGc, hGi, hG0,
    fun t y hy => ?_, fun v hv => ?_⟩
  · refine (hGfix t).1 fun hy' => hy ?_
    rw [OpenPartialHomeomorph.symm_symm] at hy'
    exact image_mono hsubR hy'
  · rw [(hGe 1 (κ v)).1, κ.symm.conjugateMap_of_mem _ (κ.map_source hv)]
    change κ (D 1 (κ.symm (κ v))) = κ (h v)
    rw [κ.left_inv hv, hD1]

end DifferentialGeometry.Manifold
