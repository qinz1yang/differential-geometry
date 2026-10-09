/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.AnnulusCoreSteps

open Set Metric Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Manifold

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

theorem det_fderiv_ne_zero_of_eventually_leftInverse {f g : Plane → Plane} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x))
    (h : ∀ᶠ y in 𝓝 x, g (f y) = y) :
    LinearMap.det (fderiv ℝ f x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  have h1 : fderiv ℝ (g ∘ f) x = ContinuousLinearMap.id ℝ Plane := by
    have hev : g ∘ f =ᶠ[𝓝 x] id := h
    rw [hev.fderiv_eq, fderiv_id]
  rw [fderiv_comp x hg hf] at h1
  have hd : LinearMap.det (((fderiv ℝ g (f x)).comp (fderiv ℝ f x) : Plane →L[ℝ] Plane) :
      Plane →ₗ[ℝ] Plane) = 1 := by
    rw [h1, ContinuousLinearMap.coe_id, LinearMap.det_id]
  change LinearMap.det ((fderiv ℝ g (f x) : Plane →ₗ[ℝ] Plane).comp
    (fderiv ℝ f x : Plane →ₗ[ℝ] Plane)) = 1 at hd
  rw [LinearMap.det_comp] at hd
  intro h0
  rw [h0, mul_zero] at hd
  exact zero_ne_one hd

theorem contDiffOn_chart_comp_of_mem_maximalAtlas {S : Type*} [TopologicalSpace S]
    [ChartedSpace Plane S] {c : OpenPartialHomeomorph Plane S}
    (hc : c.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S) {b : OpenPartialHomeomorph S Plane}
    (hb : b ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S) :
    ContDiffOn ℝ ∞ (fun v => b (c v)) (c.source ∩ c ⁻¹' b.source) ∧
      ∀ v ∈ c.source ∩ c ⁻¹' b.source,
        LinearMap.det (fderiv ℝ (fun v => b (c v)) v : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  have hcs : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ c c.source := by
    have := contMDiffOn_symm_of_mem_maximalAtlas hc
    rwa [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target] at this
  have hcsi : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ c.symm c.target :=
    contMDiffOn_of_mem_maximalAtlas hc
  have hb1 : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ b b.source :=
    contMDiffOn_of_mem_maximalAtlas hb
  have hb2 : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ b.symm b.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hb
  have hU : IsOpen (c.source ∩ c ⁻¹' b.source) := c.isOpen_inter_preimage b.open_source
  have hf : ContDiffOn ℝ ∞ (fun v => b (c v)) (c.source ∩ c ⁻¹' b.source) :=
    contMDiffOn_iff_contDiffOn.mp (hb1.comp (hcs.mono inter_subset_left) fun v hv => hv.2)
  refine ⟨hf, fun v hv => ?_⟩
  have hg : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ (fun w => c.symm (b.symm w)) (b (c v)) := by
    have h1 : b.symm (b (c v)) = c v := b.left_inv hv.2
    have h2 := hcsi.contMDiffAt (c.open_target.mem_nhds (c.map_source hv.1))
    rw [← h1] at h2
    exact h2.comp _ (hb2.contMDiffAt (b.open_target.mem_nhds (b.map_source hv.2)))
  refine det_fderiv_ne_zero_of_eventually_leftInverse
    ((hf.contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp))
    ((contMDiffAt_iff_contDiffAt.mp hg).differentiableAt (by simp)) ?_
  filter_upwards [hU.mem_nhds hv] with w hw
  rw [b.left_inv hw.2, c.left_inv hw.1]

theorem contDiffOn_comp_sub_const_of_det {φ : Plane → Plane} {U V : Set Plane} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ ∞ φ U)
    (hdet : ∀ w ∈ U, LinearMap.det (fderiv ℝ φ w : Plane →ₗ[ℝ] Plane) ≠ 0) (q : Plane)
    (hV : ∀ z ∈ V, z - q ∈ U) :
    ContDiffOn ℝ ∞ (fun z => φ (z - q)) V ∧
      ∀ z ∈ V, LinearMap.det (fderiv ℝ (fun z => φ (z - q)) z : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  refine ⟨hφ.comp (contDiff_id.sub contDiff_const).contDiffOn hV, fun z hz => ?_⟩
  have hg : DifferentiableAt ℝ (fun z : Plane => z - q) z :=
    differentiableAt_id.sub_const q
  have hdg : LinearMap.det (fderiv ℝ (fun z : Plane => z - q) z : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    rw [fderiv_sub_const, fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact one_ne_zero
  exact det_fderiv_comp_ne_zero (f := φ) (g := fun z : Plane => z - q) hg
    ((hφ.contDiffAt (hU.mem_nhds (hV z hz))).differentiableAt (by simp)) hdg (hdet _ (hV z hz))

theorem contDiffOn_det_congr {f g : Plane → Plane} {V : Set Plane} (hV : IsOpen V)
    (hfg : ∀ z ∈ V, f z = g z) (hg : ContDiffOn ℝ ∞ g V)
    (hdet : ∀ z ∈ V, LinearMap.det (fderiv ℝ g z : Plane →ₗ[ℝ] Plane) ≠ 0) :
    ContDiffOn ℝ ∞ f V ∧ ∀ z ∈ V, LinearMap.det (fderiv ℝ f z : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  refine ⟨hg.congr hfg, fun z hz => ?_⟩
  have hev : f =ᶠ[𝓝 z] g := Filter.eventuallyEq_of_mem (hV.mem_nhds hz) hfg
  rw [hev.fderiv_eq]
  exact hdet z hz

theorem planeAbs_lt_of_mem_ball {z x : Plane} {ε : ℝ} (hz : z ∈ ball x ε) :
    |z 0 - x 0| < ε ∧ |z 1 - x 1| < ε :=
  ⟨lt_of_le_of_lt (planeAbsSub_le_dist z x 0) (mem_ball.mp hz),
    lt_of_le_of_lt (planeAbsSub_le_dist z x 1) (mem_ball.mp hz)⟩

theorem mem_ball_of_abs_add_abs_lt {w q : Plane} {r : ℝ} (hw : |w 0 - q 0| + |w 1 - q 1| < r) :
    w ∈ ball q r := by
  rw [mem_ball]
  exact lt_of_le_of_lt (planeDist_le_abs_add_abs _ _) hw

theorem polarStripMap_mk_add_shift {n : ℕ} {α : ℝ} (hnα : (n : ℝ) * α = 2 * Real.pi) {k : ℕ}
    (hk : k < n) (v : Plane) :
    polarStripMap (Plane.mk (α * k) 0 + v) =
      polarStripMap (Plane.mk (α * ((k + 1) % n : ℕ)) 0 + (v - Plane.mk α 0)) := by
  rcases lt_or_ge (k + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    congr 1
    ext i
    fin_cases i
    · change α * (k : ℝ) + v 0 = α * ((k + 1 : ℕ) : ℝ) + (v 0 - α)
      push_cast
      ring
    · change (0 : ℝ) + v 1 = 0 + (v 1 - 0)
      ring
  · have hk1 : k + 1 = n := by omega
    rw [hk1, Nat.mod_self]
    have hkR : (k : ℝ) + 1 = n := by exact_mod_cast hk1
    have e1 : Plane.mk (α * k) 0 + v =
        Plane.mk ((v 0 - α) + 2 * Real.pi * ((1 : ℤ) : ℝ)) (v 1) := by
      ext i
      fin_cases i
      · change α * (k : ℝ) + v 0 = (v 0 - α) + 2 * Real.pi * ((1 : ℤ) : ℝ)
        push_cast
        rw [← hnα, ← hkR]
        ring
      · change (0 : ℝ) + v 1 = v 1
        ring
    have e2 : Plane.mk (α * ((0 : ℕ) : ℝ)) 0 + (v - Plane.mk α 0) = Plane.mk (v 0 - α) (v 1) := by
      ext i
      fin_cases i
      · change α * ((0 : ℕ) : ℝ) + (v 0 - α) = v 0 - α
        simp
      · change (0 : ℝ) + (v 1 - 0) = v 1
        ring
    rw [e1, e2, polarStripMap_add_two_pi_mul]

theorem exists_isotopy_smooth_polar_arc {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Plane S] (Φ : OpenPartialHomeomorph Plane S)
    (hΦ : {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆ Φ.source) (J₁ : S ≃ₜ S) {a α r₀ r₁ lam : ℝ}
    (hα1 : α < 1) (hr₁ : 0 < r₁) (hr₁α : r₁ * 8 ≤ α) (hr₀lam : r₀ * 8 ≤ lam)
    (hαlam : α * 4 ≤ lam)
    (hmove : ∀ y : Plane, |y 1| < 1 / 2 → ∃ y' : Plane, dist y' y < 2 * r₀ ∧ |y' 1| < 1 / 2 ∧
      J₁ (Φ (polarStripMap y)) = Φ (polarStripMap y'))
    (b : OpenPartialHomeomorph S Plane) (hb : b ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S)
    (hbleb : ∀ y ∈ ball (Plane.mk (a + α / 2) 0) lam, Φ (polarStripMap y) ∈ b.source)
    (cL cR : OpenPartialHomeomorph Plane S)
    (hcL : cL.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S)
    (hcR : cR.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S)
    (hcLs : ball (0 : Plane) r₁ ⊆ cL.source) (hcRs : ball (0 : Plane) r₁ ⊆ cR.source)
    (hcLe : ∀ v ∈ ball (0 : Plane) r₁, J₁ (Φ (polarStripMap (Plane.mk a 0 + v))) = cL v)
    (hcRe : ∀ v ∈ ball (Plane.mk α 0) r₁,
      J₁ (Φ (polarStripMap (Plane.mk a 0 + v))) = cR (v - Plane.mk α 0)) :
    ∃ κ : OpenPartialHomeomorph Plane S,
      planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16)) (r₁ / 16) ⊆
        κ.source ∧
      (∀ v ∈ κ.source, κ v = J₁ (Φ (polarStripMap (Plane.mk a 0 + v)))) ∧
      ∃ ρ > 0, ρ ≤ r₁ / 16 ∧ ∃ δ > 0, δ < r₁ / 16 ∧ ∃ h : Plane ≃ₜ Plane,
        (∀ v : Plane, |v 1| < δ → (v 0 ≤ r₁ / 2 - ρ ∨ α - r₁ / 2 + ρ ≤ v 0) → h v = v) ∧
        (∀ v ∈ planeOpenRect (r₁ / 2 - 3 * ρ) (α - r₁ / 2 + 3 * ρ) (-δ) δ, κ (h v) ∈ b.source) ∧
        ContDiffOn ℝ ∞ (fun v => b (κ (h v)))
          (planeOpenRect (r₁ / 2 - 3 * ρ) (α - r₁ / 2 + 3 * ρ) (-δ) δ) ∧
        (∀ v ∈ planeOpenRect (r₁ / 2 - 3 * ρ) (α - r₁ / 2 + 3 * ρ) (-δ) δ,
          LinearMap.det (fderiv ℝ (fun v => b (κ (h v))) v : Plane →ₗ[ℝ] Plane) ≠ 0) ∧
        ∃ G : ℝ → S ≃ₜ S, Continuous (fun q : ℝ × S => G q.1 q.2) ∧
          Continuous (fun q : ℝ × S => (G q.1).symm q.2) ∧ G 0 = Homeomorph.refl S ∧
          (∀ t, EqOn (G t) id (κ '' planeRect (r₁ / 2 - 3 * (r₁ / 16))
            (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16)) (r₁ / 16))ᶜ) ∧
          ∀ v ∈ κ.source, G 1 (κ v) = κ (h v) := by
  have hannu : ∀ u : Plane, |u 1| < 1 / 2 → polarStripMap u ∈ Φ.source := by
    intro u hu
    apply hΦ
    change 1 < ‖polarStripMap u‖ ∧ ‖polarStripMap u‖ < 2
    rw [abs_lt] at hu
    rw [norm_polarStripMap, abs_of_pos (by linarith : 0 < 3 / 2 + u 1)]
    exact ⟨by linarith, by linarith⟩
  let Φ₁ := Φ.trans J₁.toOpenPartialHomeomorph
  have hΦ₁s : {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆ Φ₁.source := by
    intro x hx
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hΦ hx, mem_univ _⟩
  obtain ⟨κ, hκs, hκe⟩ := exists_polarStrip_chart Φ₁ hΦ₁s (Plane.mk a 0) rfl
  have hκJ : ∀ v ∈ κ.source, κ v = J₁ (Φ (polarStripMap (Plane.mk a 0 + v))) := hκe
  have hp1 : ∀ v : Plane, (Plane.mk a 0 + v) 1 = v 1 := fun v => by
    change 0 + v 1 = v 1
    rw [zero_add]
  have hR₀κ : planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16))
      (r₁ / 16) ⊆ κ.source := by
    intro v hv
    rw [hκs]
    exact ⟨by linarith [hv.1], by linarith [hv.2.1], by linarith [hv.2.2.1],
      by linarith [hv.2.2.2]⟩
  have hRb : ∀ v ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16))
      (-(r₁ / 16)) (r₁ / 16), κ v ∈ b.source := by
    intro v hv
    have hv0 : r₁ / 2 - 3 * (r₁ / 16) ≤ v 0 := hv.1
    have hv0' : v 0 ≤ α - r₁ / 2 + 3 * (r₁ / 16) := hv.2.1
    have hv1 : |v 1| ≤ r₁ / 16 := abs_le.mpr ⟨hv.2.2.1, hv.2.2.2⟩
    have hy1 : |(Plane.mk a 0 + v) 1| < 1 / 2 := by
      rw [hp1]
      linarith
    obtain ⟨y', hy'd, -, hy'e⟩ := hmove (Plane.mk a 0 + v) hy1
    rw [hκJ v (hR₀κ hv), hy'e]
    refine hbleb y' ?_
    rw [mem_ball]
    have hc : dist (Plane.mk a 0 + v) (Plane.mk (a + α / 2) 0) ≤ α / 2 + r₁ / 16 := by
      refine (planeDist_le_abs_add_abs _ _).trans ?_
      have e0 : (Plane.mk a 0 + v) 0 - (Plane.mk (a + α / 2) 0) 0 = v 0 - α / 2 := by
        change a + v 0 - (a + α / 2) = v 0 - α / 2
        ring
      have e1 : (Plane.mk a 0 + v) 1 - (Plane.mk (a + α / 2) 0) 1 = v 1 := by
        rw [hp1]
        change v 1 - 0 = v 1
        ring
      rw [e0, e1]
      have : |v 0 - α / 2| ≤ α / 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith
    calc dist y' (Plane.mk (a + α / 2) 0)
        ≤ dist y' (Plane.mk a 0 + v) + dist (Plane.mk a 0 + v) (Plane.mk (a + α / 2) 0) :=
          dist_triangle _ _ _
      _ < 2 * r₀ + (α / 2 + r₁ / 16) := add_lt_add_of_lt_of_le hy'd hc
      _ ≤ lam := by linarith
  have hinR : ∀ τ : ℝ, 5 * r₁ / 16 ≤ τ - r₁ / 16 → τ + r₁ / 16 ≤ α - 5 * r₁ / 16 →
      ∀ v ∈ ball (Plane.mk τ 0) (r₁ / 16), v ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16))
        (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16)) (r₁ / 16) := by
    intro τ h1 h2 v hv
    obtain ⟨hv0, hv1⟩ := planeAbs_lt_of_mem_ball hv
    change |v 0 - τ| < r₁ / 16 at hv0
    change |v 1 - 0| < r₁ / 16 at hv1
    rw [sub_zero, abs_lt] at hv1
    rw [abs_lt] at hv0
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hleft : ContDiffOn ℝ ∞ (fun v => b (κ v)) (ball (Plane.mk (r₁ / 2) 0) (r₁ / 16)) ∧
      ∀ v ∈ ball (Plane.mk (r₁ / 2) 0) (r₁ / 16),
        LinearMap.det (fderiv ℝ (fun v => b (κ v)) v : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    obtain ⟨hTs, hTd⟩ := contDiffOn_chart_comp_of_mem_maximalAtlas hcL hb
    have hball : ∀ v ∈ ball (Plane.mk (r₁ / 2) 0) (r₁ / 16), v ∈ ball (0 : Plane) r₁ := by
      intro v hv
      obtain ⟨hv0, hv1⟩ := planeAbs_lt_of_mem_ball hv
      change |v 0 - r₁ / 2| < r₁ / 16 at hv0
      change |v 1 - 0| < r₁ / 16 at hv1
      refine mem_ball_of_abs_add_abs_lt ?_
      change |v 0 - 0| + |v 1 - 0| < r₁
      simp only [sub_zero] at hv1 ⊢
      rw [abs_lt] at hv0
      rw [abs_of_pos (by linarith : (0 : ℝ) < v 0)]
      linarith
    have hmem : ∀ v ∈ ball (Plane.mk (r₁ / 2) 0) (r₁ / 16), v ∈ cL.source ∩ cL ⁻¹' b.source := by
      intro v hv
      have hvR := hinR (r₁ / 2) (by linarith) (by linarith) v hv
      refine ⟨hcLs (hball v hv), ?_⟩
      have := hRb v hvR
      rw [hκJ v (hR₀κ hvR), hcLe v (hball v hv)] at this
      exact this
    refine contDiffOn_det_congr isOpen_ball (fun v hv => ?_) (hTs.mono hmem)
      fun v hv => hTd v (hmem v hv)
    have hvR := hinR (r₁ / 2) (by linarith) (by linarith) v hv
    change b (κ v) = b (cL v)
    rw [hκJ v (hR₀κ hvR), hcLe v (hball v hv)]
  have hright : ContDiffOn ℝ ∞ (fun v => b (κ v)) (ball (Plane.mk (α - r₁ / 2) 0) (r₁ / 16)) ∧
      ∀ v ∈ ball (Plane.mk (α - r₁ / 2) 0) (r₁ / 16),
        LinearMap.det (fderiv ℝ (fun v => b (κ v)) v : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    obtain ⟨hTs, hTd⟩ := contDiffOn_chart_comp_of_mem_maximalAtlas hcR hb
    have hUo : IsOpen (cR.source ∩ cR ⁻¹' b.source) := cR.isOpen_inter_preimage b.open_source
    have hball : ∀ v ∈ ball (Plane.mk (α - r₁ / 2) 0) (r₁ / 16),
        v ∈ ball (Plane.mk α 0) r₁ ∧ v - Plane.mk α 0 ∈ ball (0 : Plane) r₁ := by
      intro v hv
      obtain ⟨hv0, hv1⟩ := planeAbs_lt_of_mem_ball hv
      change |v 0 - (α - r₁ / 2)| < r₁ / 16 at hv0
      change |v 1 - 0| < r₁ / 16 at hv1
      rw [sub_zero] at hv1
      rw [abs_lt] at hv0
      have hb0 : |v 0 - α| < 9 * r₁ / 16 := by
        rw [abs_lt]
        constructor <;> linarith
      constructor
      · refine mem_ball_of_abs_add_abs_lt ?_
        change |v 0 - α| + |v 1 - 0| < r₁
        rw [sub_zero]
        linarith
      · refine mem_ball_of_abs_add_abs_lt ?_
        change |v 0 - α - 0| + |v 1 - 0 - 0| < r₁
        simp only [sub_zero]
        linarith
    have hform : ∀ v ∈ ball (Plane.mk (α - r₁ / 2) 0) (r₁ / 16), κ v = cR (v - Plane.mk α 0) := by
      intro v hv
      have hvR := hinR (α - r₁ / 2) (by linarith) (by linarith) v hv
      rw [hκJ v (hR₀κ hvR)]
      exact hcRe v (hball v hv).1
    have hmem : ∀ v ∈ ball (Plane.mk (α - r₁ / 2) 0) (r₁ / 16),
        v - Plane.mk α 0 ∈ cR.source ∩ cR ⁻¹' b.source := by
      intro v hv
      have hvR := hinR (α - r₁ / 2) (by linarith) (by linarith) v hv
      refine ⟨hcRs (hball v hv).2, ?_⟩
      have := hRb v hvR
      rw [hform v hv] at this
      exact this
    obtain ⟨h1, h2⟩ := contDiffOn_comp_sub_const_of_det hUo hTs hTd (Plane.mk α 0) hmem
    exact contDiffOn_det_congr isOpen_ball (fun v hv => by rw [hform v hv]) h1 h2
  obtain ⟨ρ, hρ, hρr, δ, hδ, hδW, h, hends, hmaps, hsm, hdet, G, hGc, hGi, hG0, hGfix, hGκ⟩ :=
    exists_isotopy_smooth_arc_chart κ b (by positivity : (0 : ℝ) < r₁ / 16)
      (by positivity : (0 : ℝ) < r₁ / 16) (by linarith) hR₀κ hRb hleft.1 hright.1 hleft.2
      hright.2
  exact ⟨κ, hR₀κ, hκJ, ρ, hρ, hρr, δ, hδ, hδW, h, hends, hmaps, hsm, hdet, G, hGc, hGi, hG0,
    hGfix, hGκ⟩

theorem fin_eq_of_mul_add_eq {n : ℕ} {α : ℝ} (hα : 0 < α) (hnα : (n : ℝ) * α = 2 * Real.pi)
    (j k : Fin n) (m : ℤ) (s : ℝ) (hs : |s| < α)
    (h : α * (j : ℕ) + s = α * (k : ℕ) + 2 * Real.pi * m) : j = k ∧ m = 0 := by
  have hkey : |((j : ℕ) : ℝ) - (k : ℕ) - n * m| < 1 := by
    have heq : α * (((j : ℕ) : ℝ) - (k : ℕ) - n * m) = -s := by
      rw [← hnα] at h
      linarith
    have hb : |α * (((j : ℕ) : ℝ) - (k : ℕ) - n * m)| < α := by
      rw [heq, abs_neg]
      exact hs
    rw [abs_mul, abs_of_pos hα] at hb
    nlinarith [abs_nonneg (((j : ℕ) : ℝ) - (k : ℕ) - n * m)]
  obtain ⟨h1, h2⟩ := eq_and_eq_zero_of_abs_sub_lt j.2 k.2 hkey
  exact ⟨Fin.ext h1, h2⟩

theorem polarBand_exists_local_chart {S : Type*} [TopologicalSpace S] [ChartedSpace Plane S]
    (F : OpenPartialHomeomorph Plane S) (E : Plane → S) (A : S → S)
    (hFE : ∀ z, F (polarStripMap z) = A (E z)) {n : ℕ} {α r₁ δ : ℝ} (hα : 0 < α)
    (hnα : (n : ℝ) * α = 2 * Real.pi) (hr₁α : r₁ * 8 ≤ α) (hδr : δ ≤ r₁ / 8)
    (cJ : Fin n → OpenPartialHomeomorph Plane S)
    (hcJmax : ∀ k, (cJ k).symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S)
    (hcJs : ∀ k, ball (0 : Plane) r₁ ⊆ (cJ k).source)
    (hcJe : ∀ (k : Fin n), ∀ v ∈ ball (0 : Plane) r₁,
      E (Plane.mk (α * (k : ℕ)) 0 + v) = cJ k v)
    (hshift : ∀ (k : Fin n) (v : Plane), E (Plane.mk (α * (k : ℕ)) 0 + v) =
      E (Plane.mk (α * (((k : ℕ) + 1) % n : ℕ)) 0 + (v - Plane.mk α 0)))
    (κ : Fin n → Plane → S) (b : Fin n → OpenPartialHomeomorph S Plane)
    (hbmax : ∀ k, b k ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S) (ρ δa : Fin n → ℝ)
    (h : Fin n → Plane → Plane) (hρ : ∀ k, 0 < ρ k) (hρr : ∀ k, ρ k ≤ r₁ / 16)
    (hδa : ∀ k, δ ≤ δa k) (hδaW : ∀ k, δa k < r₁ / 16)
    (hκE : ∀ (k : Fin n), ∀ v ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16))
      (-(r₁ / 16)) (r₁ / 16), κ k v = E (Plane.mk (α * (k : ℕ)) 0 + v))
    (hAκ : ∀ (k : Fin n), ∀ v ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16))
      (-(r₁ / 16)) (r₁ / 16), A (κ k v) = κ k (h k v))
    (hends : ∀ (k : Fin n) (v : Plane), |v 1| < δa k →
      (v 0 ≤ r₁ / 2 - ρ k ∨ α - r₁ / 2 + ρ k ≤ v 0) → h k v = v)
    (hmaps : ∀ (k : Fin n), ∀ v ∈ planeOpenRect (r₁ / 2 - 3 * ρ k) (α - r₁ / 2 + 3 * ρ k)
      (-δa k) (δa k), κ k (h k v) ∈ (b k).source)
    (hsm : ∀ k : Fin n, ContDiffOn ℝ ∞ (fun v => b k (κ k (h k v)))
      (planeOpenRect (r₁ / 2 - 3 * ρ k) (α - r₁ / 2 + 3 * ρ k) (-δa k) (δa k)))
    (hdet : ∀ (k : Fin n), ∀ v ∈ planeOpenRect (r₁ / 2 - 3 * ρ k) (α - r₁ / 2 + 3 * ρ k)
      (-δa k) (δa k), LinearMap.det
        (fderiv ℝ (fun v => b k (κ k (h k v))) v : Plane →ₗ[ℝ] Plane) ≠ 0)
    (hfix : ∀ z : Plane, |z 1| < δ → (∀ (j : Fin n) (v : Plane),
      v ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16))
        (r₁ / 16) → |v 1| < δ → ∀ m : ℤ, α * (j : ℕ) + v 0 = z 0 + 2 * Real.pi * m →
          h j v = v) → A (E z) = E z) :
    ∀ x : Plane, x 0 ∈ Ico 0 (2 * Real.pi) → |x 1| < δ → ∃ V : Set Plane, IsOpen V ∧
      x ∈ V ∧ (∀ z ∈ V, |z 1| < δ) ∧ ∃ bb ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S,
        (∀ z ∈ V, F (polarStripMap z) ∈ bb.source) ∧
        ContDiffOn ℝ ∞ (fun z => bb (F (polarStripMap z))) V ∧
        ∀ z ∈ V, LinearMap.det
          (fderiv ℝ (fun z => bb (F (polarStripMap z))) z : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  intro x hx0 hx1
  have hxa : 0 ≤ x 0 / α := div_nonneg hx0.1 hα.le
  obtain ⟨kF, hkx, hxk⟩ : ∃ kF : Fin n, α * (kF : ℕ) ≤ x 0 ∧ x 0 < α * (kF : ℕ) + α := by
    refine ⟨⟨⌊x 0 / α⌋₊, ?_⟩, ?_, ?_⟩
    · rw [Nat.floor_lt hxa, div_lt_iff₀ hα, hnα]
      exact hx0.2
    · have := Nat.floor_le hxa
      rw [le_div_iff₀ hα] at this
      change α * (⌊x 0 / α⌋₊ : ℝ) ≤ x 0
      linarith
    · have := Nat.lt_floor_add_one (x 0 / α)
      rw [div_lt_iff₀ hα] at this
      change x 0 < α * (⌊x 0 / α⌋₊ : ℝ) + α
      linarith
  have hρk := hρ kF
  have hρkr := hρr kF
  have hδkF := hδa kF
  have hδaWk := hδaW kF
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hx1.le
  have hαr : r₁ * 8 ≤ α := hr₁α
  have hr₁ : 0 ≤ r₁ := by
    have := hδ0.trans hδr
    linarith
  have hVδ : ∀ ε, ε ≤ δ - |x 1| → ∀ z ∈ ball x ε, |z 1| < δ := by
    intro ε hε z hz
    have h1 := (planeAbs_lt_of_mem_ball hz).2
    have h2 := abs_sub_abs_le_abs_sub (z 1) (x 1)
    linarith
  set q : Plane := Plane.mk (α * (kF : ℕ)) 0 with hqdef
  have hq0 : ∀ z : Plane, (z - q) 0 = z 0 - α * (kF : ℕ) := fun z => rfl
  have hq1 : ∀ z : Plane, (z - q) 1 = z 1 := fun z => by
    change z 1 - 0 = z 1
    rw [sub_zero]
  have hE : ∀ z : Plane, E z = E (q + (z - q)) := fun z => by rw [add_sub_cancel]
  have hR₀ : ∀ v ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16))
      (-(r₁ / 16)) (r₁ / 16), 5 * r₁ / 16 ≤ v 0 ∧ v 0 ≤ α - 5 * r₁ / 16 := fun v hv =>
    ⟨by linarith [hv.1], by linarith [hv.2.1]⟩
  rcases lt_or_ge (x 0 - α * (kF : ℕ)) (r₁ / 2 - ρ kF) with hA | hA
  · obtain ⟨ε, hε, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ r₁ / 2 - ρ kF - (x 0 - α * (kF : ℕ)) ∧
        ε ≤ r₁ / 8 ∧ ε ≤ δ - |x 1| :=
      ⟨min (r₁ / 2 - ρ kF - (x 0 - α * (kF : ℕ))) (min (r₁ / 8) (δ - |x 1|)),
        lt_min (by linarith) (lt_min (by linarith) (by linarith)), min_le_left _ _,
        (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    have hzs : ∀ z ∈ ball x ε, z - q ∈ ball (0 : Plane) r₁ ∧
        F (polarStripMap z) = cJ kF (z - q) := by
      intro z hz
      obtain ⟨hz0, -⟩ := planeAbs_lt_of_mem_ball hz
      have hzδ := hVδ ε hε3 z hz
      rw [abs_lt] at hz0
      have hzr : z - q ∈ ball (0 : Plane) r₁ := by
        refine mem_ball_of_abs_add_abs_lt ?_
        change |(z - q) 0 - 0| + |(z - q) 1 - 0| < r₁
        rw [hq0, hq1, sub_zero, sub_zero]
        have : |z 0 - α * (kF : ℕ)| < r₁ / 2 := by
          rw [abs_lt]
          constructor <;> linarith
        linarith
      refine ⟨hzr, ?_⟩
      rw [hFE, hfix z hzδ ?_, hE z]
      · exact hcJe kF _ hzr
      · intro j v hv hv1 m hm
        obtain ⟨hv0, hv0'⟩ := hR₀ v hv
        obtain ⟨hjk, hm0⟩ := fin_eq_of_mul_add_eq hα hnα j kF m (v 0 - (z 0 - α * (kF : ℕ)))
          (by
            rw [abs_lt]
            constructor
            · linarith only [hv0, hv0', hz0.1, hz0.2, hkx, hA, hε1, hε2, hε, hρk, hr₁, hαr]
            · linarith only [hv0, hv0', hz0.1, hz0.2, hkx, hA, hε1, hε2, hε, hρk, hr₁, hαr])
          (by linear_combination hm)
        rw [hjk]
        rw [hjk, hm0, Int.cast_zero, mul_zero, add_zero] at hm
        refine hends kF v (lt_of_lt_of_le hv1 hδkF) (Or.inl ?_)
        linarith only [hm, hz0.2, hε1]
    refine ⟨ball x ε, isOpen_ball, mem_ball_self hε, hVδ ε hε3, (cJ kF).symm, hcJmax kF,
      fun z hz => ?_, ?_⟩
    · rw [(hzs z hz).2]
      exact (cJ kF).map_source (hcJs kF (hzs z hz).1)
    · have hc : ContDiffOn ℝ ∞ (fun z : Plane => z - q) (ball x ε) :=
        (contDiff_id.sub contDiff_const).contDiffOn
      refine contDiffOn_det_congr isOpen_ball (fun z hz => ?_) hc fun z _ => ?_
      · change (cJ kF).symm (F (polarStripMap z)) = z - q
        rw [(hzs z hz).2]
        exact (cJ kF).left_inv (hcJs kF (hzs z hz).1)
      · rw [fderiv_sub_const, fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
        exact one_ne_zero
  rcases lt_or_ge (α - r₁ / 2 + ρ kF) (x 0 - α * (kF : ℕ)) with hB | hB
  · obtain ⟨k', hk'⟩ : ∃ k' : Fin n, (k' : ℕ) = ((kF : ℕ) + 1) % n :=
      ⟨⟨((kF : ℕ) + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by
        have := kF.2
        omega)⟩, rfl⟩
    obtain ⟨ε, hε, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧
        ε ≤ (x 0 - α * (kF : ℕ)) - (α - r₁ / 2 + ρ kF) ∧ ε ≤ r₁ / 8 ∧ ε ≤ δ - |x 1| :=
      ⟨min ((x 0 - α * (kF : ℕ)) - (α - r₁ / 2 + ρ kF)) (min (r₁ / 8) (δ - |x 1|)),
        lt_min (by linarith) (lt_min (by linarith) (by linarith)), min_le_left _ _,
        (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    have hzs : ∀ z ∈ ball x ε, z - q - Plane.mk α 0 ∈ ball (0 : Plane) r₁ ∧
        F (polarStripMap z) = cJ k' (z - q - Plane.mk α 0) := by
      intro z hz
      obtain ⟨hz0, -⟩ := planeAbs_lt_of_mem_ball hz
      have hzδ := hVδ ε hε3 z hz
      rw [abs_lt] at hz0
      have hzr : z - q - Plane.mk α 0 ∈ ball (0 : Plane) r₁ := by
        refine mem_ball_of_abs_add_abs_lt ?_
        change |(z - q) 0 - α - 0| + |(z - q) 1 - 0 - 0| < r₁
        rw [hq0, hq1, sub_zero, sub_zero, sub_zero]
        have : |z 0 - α * (kF : ℕ) - α| < r₁ / 2 := by
          rw [abs_lt]
          constructor <;> linarith
        linarith
      refine ⟨hzr, ?_⟩
      rw [hFE, hfix z hzδ ?_, hE z, hshift kF]
      · have := hcJe k' _ hzr
        rw [hk'] at this
        exact this
      · intro j v hv hv1 m hm
        obtain ⟨hv0, hv0'⟩ := hR₀ v hv
        obtain ⟨hjk, hm0⟩ := fin_eq_of_mul_add_eq hα hnα j kF m (v 0 - (z 0 - α * (kF : ℕ)))
          (by
            rw [abs_lt]
            constructor
            · linarith only [hv0, hv0', hz0.1, hz0.2, hxk, hB, hε1, hε2, hε, hρk, hr₁, hαr]
            · linarith only [hv0, hv0', hz0.1, hz0.2, hxk, hB, hε1, hε2, hε, hρk, hr₁, hαr])
          (by linear_combination hm)
        rw [hjk]
        rw [hjk, hm0, Int.cast_zero, mul_zero, add_zero] at hm
        refine hends kF v (lt_of_lt_of_le hv1 hδkF) (Or.inr ?_)
        linarith only [hm, hz0.1, hε1]
    refine ⟨ball x ε, isOpen_ball, mem_ball_self hε, hVδ ε hε3, (cJ k').symm, hcJmax k',
      fun z hz => ?_, ?_⟩
    · rw [(hzs z hz).2]
      exact (cJ k').map_source (hcJs k' (hzs z hz).1)
    · have hc : ContDiffOn ℝ ∞ (fun z : Plane => z - (q + Plane.mk α 0)) (ball x ε) :=
        (contDiff_id.sub contDiff_const).contDiffOn
      refine contDiffOn_det_congr isOpen_ball (fun z hz => ?_) hc fun z _ => ?_
      · change (cJ k').symm (F (polarStripMap z)) = z - (q + Plane.mk α 0)
        rw [(hzs z hz).2, ← sub_sub]
        exact (cJ k').left_inv (hcJs k' (hzs z hz).1)
      · rw [fderiv_sub_const, fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
        exact one_ne_zero
  obtain ⟨ε, hε, hε1, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ kF ∧ ε ≤ δ - |x 1| :=
    ⟨min (ρ kF) (δ - |x 1|), lt_min hρk (by linarith), min_le_left _ _, min_le_right _ _⟩
  have hzT : ∀ z ∈ ball x ε, z - q ∈ planeOpenRect (r₁ / 2 - 3 * ρ kF)
      (α - r₁ / 2 + 3 * ρ kF) (-δa kF) (δa kF) ∧ z - q ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16))
        (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16)) (r₁ / 16) := by
    intro z hz
    obtain ⟨hz0, -⟩ := planeAbs_lt_of_mem_ball hz
    have hzδ := hVδ ε hε3 z hz
    rw [abs_lt] at hz0 hzδ
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hq0]; linarith
    · rw [hq0]; linarith
    · rw [hq1]; linarith
    · rw [hq1]; linarith
    · rw [hq0]; linarith
    · rw [hq0]; linarith
    · rw [hq1]; linarith
    · rw [hq1]; linarith
  have hform : ∀ z ∈ ball x ε, F (polarStripMap z) = κ kF (h kF (z - q)) := by
    intro z hz
    rw [hFE, hE z, ← hκE kF _ (hzT z hz).2, hAκ kF _ (hzT z hz).2]
  obtain ⟨h1, h2⟩ := contDiffOn_comp_sub_const_of_det (isOpen_planeOpenRect _ _ _ _)
    (hsm kF) (hdet kF) q fun z hz => (hzT z hz).1
  refine ⟨ball x ε, isOpen_ball, mem_ball_self hε, hVδ ε hε3, b kF, hbmax kF,
    fun z hz => ?_, contDiffOn_det_congr isOpen_ball (fun z hz => ?_) h1 h2⟩
  · rw [hform z hz]
    exact hmaps kF _ (hzT z hz).1
  · change b kF (F (polarStripMap z)) = b kF (κ kF (h kF (z - q)))
    rw [hform z hz]

theorem exists_isotopy_smooth_annulus_core {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Plane S] [IsManifold 𝓘(ℝ, Plane) ∞ S] (Φ : OpenPartialHomeomorph Plane S)
    (hΦ : {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆ Φ.source) :
    ∃ G : ℝ → S ≃ₜ S, Continuous (fun p : ℝ × S => G p.1 p.2) ∧
      Continuous (fun p : ℝ × S => (G p.1).symm p.2) ∧ G 0 = Homeomorph.refl S ∧
      ∃ δ > 0, δ < 1 / 2 ∧ ∃ c : OpenPartialHomeomorph Plane S,
        c.source = {x : Plane | |‖x‖ - 3 / 2| < δ} ∧ (∀ x ∈ c.source, c x = G 1 (Φ x)) ∧
        c.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S := by
  classical
  have hannu : ∀ u : Plane, |u 1| < 1 / 2 → polarStripMap u ∈ Φ.source := by
    intro u hu
    apply hΦ
    change 1 < ‖polarStripMap u‖ ∧ ‖polarStripMap u‖ < 2
    rw [abs_lt] at hu
    rw [norm_polarStripMap, abs_of_pos (by linarith : 0 < 3 / 2 + u 1)]
    exact ⟨by linarith, by linarith⟩
  have hc1 := Schoenflies.Plane.continuous_coord 1
  have hStro : IsOpen {z : Plane | |z 1| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp hc1) continuous_const
  have hEc : ContinuousOn (fun z => Φ (polarStripMap z)) {z : Plane | |z 1| < 1 / 2} :=
    Φ.continuousOn.comp contDiff_polarStripMap.continuous.continuousOn fun z hz => hannu z hz
  have hOo : ∀ x : Plane, IsOpen ({z : Plane | |z 1| < 1 / 2} ∩ (fun z => Φ (polarStripMap z)) ⁻¹'
      (chartAt Plane (Φ (polarStripMap x))).source) := fun x =>
    hEc.isOpen_inter_preimage hStro (chartAt Plane _).open_source
  have hmkc : Continuous (fun t : ℝ => Plane.mk t 0) := by
    have h1 : (fun t : ℝ => Plane.mk t 0) =
        fun t => t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
      funext t
      ext i
      fin_cases i <;> simp
    rw [h1]
    exact continuous_id.smul continuous_const
  have hK₀c : IsCompact ((fun t : ℝ => Plane.mk t 0) '' Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.image hmkc
  have hK₀O : (fun t : ℝ => Plane.mk t 0) '' Icc 0 (2 * Real.pi) ⊆
      ⋃ x : Plane, {z : Plane | |z 1| < 1 / 2} ∩ (fun z => Φ (polarStripMap z)) ⁻¹'
        (chartAt Plane (Φ (polarStripMap x))).source := by
    rintro _ ⟨t, -, rfl⟩
    refine mem_iUnion.mpr ⟨Plane.mk t 0, ?_, mem_chart_source Plane _⟩
    change |(0 : ℝ)| < 1 / 2
    norm_num
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric hK₀c hOo hK₀O
  obtain ⟨n, hn, α, hα, hnα, hα1, hαlam⟩ : ∃ n : ℕ, 0 < n ∧ ∃ α : ℝ, 0 < α ∧
      (n : ℝ) * α = 2 * Real.pi ∧ α < 1 ∧ α * 4 ≤ lam := by
    refine ⟨⌈8 * Real.pi / lam⌉₊ + 9, by omega, 2 * Real.pi / (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ),
      ?_, ?_, ?_, ?_⟩
    · have : (0 : ℝ) < (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ) := by positivity
      positivity
    · have : (0 : ℝ) < (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ) := by positivity
      field_simp
    · have h9 : (9 : ℝ) ≤ (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ) := by
        exact_mod_cast Nat.le_add_left 9 _
      rw [div_lt_one (by linarith)]
      linarith [Real.pi_lt_four]
    · have hnlam : 8 * Real.pi / lam ≤ (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_add_right _ _)
      have hpos : (0 : ℝ) < (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ) := by positivity
      rw [div_le_iff₀ hlam] at hnlam
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      calc 2 * Real.pi * 4 = 8 * Real.pi := by ring
        _ ≤ (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ) * lam := hnlam
        _ = lam * (⌈8 * Real.pi / lam⌉₊ + 9 : ℕ) := mul_comm _ _
  have hαeq : 2 * Real.pi / n = α := by
    rw [← hnα]
    field_simp
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀ : ℝ, r₀ = min (α / 8) (min (lam / 8) (1 / 4)) := ⟨_, rfl⟩
  have hr₀ : 0 < r₀ := by
    rw [hr₀def]
    exact lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hr₀α : r₀ ≤ α / 8 := by
    rw [hr₀def]
    exact min_le_left _ _
  have hr₀lam : r₀ * 8 ≤ lam := by
    have : r₀ ≤ lam / 8 := by
      rw [hr₀def]
      exact (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hr₀1 : r₀ ≤ 1 / 4 := by
    rw [hr₀def]
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨J, hJc, hJi, hJ0, hmove, r, hr, hcJ⟩ :=
    exists_isotopy_smooth_polar_junctions Φ hΦ hn hr₀ (by rw [hαeq]; exact hr₀α) hr₀1
  choose cJ hcJmax hcJs hcJe using hcJ
  rw [hαeq] at hcJe
  obtain ⟨r₁, hr₁, hr₁r, hr₁α⟩ : ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r ∧ r₁ * 8 ≤ α :=
    ⟨min r r₀, lt_min hr hr₀, min_le_left _ _, by linarith [min_le_right r r₀]⟩
  have hcJs' : ∀ k, ball (0 : Plane) r₁ ⊆ (cJ k).source := fun k =>
    (ball_subset_ball hr₁r).trans (hcJs k)
  have hcJe' : ∀ (k : Fin n), ∀ v ∈ ball (0 : Plane) r₁,
      J 1 (Φ (polarStripMap (Plane.mk (α * (k : ℕ)) 0 + v))) = cJ k v := fun k v hv =>
    hcJe k v (ball_subset_ball hr₁r hv)
  have hsuccn : ∀ k : Fin n, ((k : ℕ) + 1) % n < n := fun k => Nat.mod_lt _ hn
  have hcRe : ∀ (k : Fin n), ∀ v ∈ ball (Plane.mk α 0) r₁,
      J 1 (Φ (polarStripMap (Plane.mk (α * (k : ℕ)) 0 + v))) =
        cJ ⟨((k : ℕ) + 1) % n, hsuccn k⟩ (v - Plane.mk α 0) := by
    intro k v hv
    rw [polarStripMap_mk_add_shift hnα k.2 v]
    refine hcJe' ⟨((k : ℕ) + 1) % n, hsuccn k⟩ _ ?_
    rw [mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact hv
  have hcenter : ∀ k : Fin n, Plane.mk (α * (k : ℕ) + α / 2) 0 ∈
      (fun t : ℝ => Plane.mk t 0) '' Icc 0 (2 * Real.pi) := by
    intro k
    refine ⟨α * (k : ℕ) + α / 2, ⟨by positivity, ?_⟩, rfl⟩
    have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.2
    nlinarith
  have hbex : ∀ k : Fin n, ∃ x' : Plane, ball (Plane.mk (α * (k : ℕ) + α / 2) 0) lam ⊆
      {z : Plane | |z 1| < 1 / 2} ∩ (fun z => Φ (polarStripMap z)) ⁻¹'
        (chartAt Plane (Φ (polarStripMap x'))).source :=
    fun k => hleb _ (hcenter k)
  choose xb hxb using hbex
  have harc := fun k : Fin n => exists_isotopy_smooth_polar_arc Φ hΦ (J 1) (a := α * (k : ℕ))
    hα1 hr₁ hr₁α hr₀lam hαlam hmove (chartAt Plane (Φ (polarStripMap (xb k))))
    (IsManifold.chart_mem_maximalAtlas _) (fun y hy => (hxb k hy).2) (cJ k)
    (cJ ⟨((k : ℕ) + 1) % n, hsuccn k⟩) (hcJmax k) (hcJmax _) (hcJs' k) (hcJs' _) (hcJe' k)
    (hcRe k)
  choose κ hR₀κ hκJ ρ hρ hρr δa hδa hδaW h hhends hhmaps hhsm hhdet G hGc hGi hG0 hGfix hGκ
    using harc
  have hPinj : ∀ a b : Plane, |a 1| < 1 / 2 → |b 1| < 1 / 2 →
      J 1 (Φ (polarStripMap a)) = J 1 (Φ (polarStripMap b)) →
        polarStripMap a = polarStripMap b := fun a b ha hb hab =>
    Φ.injOn (hannu a ha) (hannu b hb) ((J 1).injective hab)
  have hp1 : ∀ (k : ℕ) (v : Plane), (Plane.mk (α * k) 0 + v) 1 = v 1 := fun k v => by
    change 0 + v 1 = v 1
    rw [zero_add]
  have hdisA : Pairwise fun i j => Disjoint (κ i '' planeRect (r₁ / 2 - 3 * (r₁ / 16))
      (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16)) (r₁ / 16)) (κ j '' planeRect
        (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16)) (r₁ / 16)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hwv⟩
    apply hij
    have hv1 : |v 1| ≤ r₁ / 16 := abs_le.mpr ⟨hv.2.2.1, hv.2.2.2⟩
    have hw1 : |w 1| ≤ r₁ / 16 := abs_le.mpr ⟨hw.2.2.1, hw.2.2.2⟩
    rw [hκJ i v (hR₀κ i hv), hκJ j w (hR₀κ j hw)] at hwv
    have hPi := hPinj _ _ (by rw [hp1]; linarith) (by rw [hp1]; linarith) hwv
    obtain ⟨-, m, hm⟩ := polarStripMap_eq_polarStripMap
      (by rw [hp1, abs_lt]; constructor <;> linarith [abs_le.mp hw1])
      (by rw [hp1, abs_lt]; constructor <;> linarith [abs_le.mp hv1]) hPi
    change α * (j : ℕ) + w 0 = α * (i : ℕ) + v 0 + 2 * Real.pi * m at hm
    have := fin_eq_of_mul_add_eq hα hnα j i m (w 0 - v 0)
      (by rw [abs_lt]; constructor <;> linarith [hv.1, hv.2.1, hw.1, hw.2.1])
      (by linear_combination hm)
    exact this.1.symm
  obtain ⟨Ga, hGac, hGai, hGaeq, hGafix, hGarefl⟩ :=
    Homeomorph.exists_gluing_family_of_pairwise_disjoint G _ hGc hGi (fun k t => hGfix k t)
      hdisA
  have hGa0 : Ga 0 = Homeomorph.refl S := hGarefl 0 fun k => hG0 k
  let Gt : ℝ → S ≃ₜ S := fun t => (J t).trans (Ga t)
  have hGtc : Continuous (fun q : ℝ × S => Gt q.1 q.2) :=
    hGac.comp (continuous_fst.prodMk hJc)
  have hGti : Continuous (fun q : ℝ × S => (Gt q.1).symm q.2) :=
    hJi.comp (continuous_fst.prodMk hGai)
  have hGt0 : Gt 0 = Homeomorph.refl S := by
    refine Homeomorph.ext fun y => ?_
    change Ga 0 (J 0 y) = y
    rw [hJ0, hGa0]
    rfl
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨δ, hδpos, hδk, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ (∀ k, δ ≤ δa k) ∧ δ ≤ r₁ / 8 :=
    ⟨min (Finset.univ.inf' hne δa) (r₁ / 8),
      lt_min ((Finset.lt_inf'_iff hne).mpr fun k _ => hδa k) (by positivity),
      fun k => (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ k)),
      min_le_right _ _⟩
  have hδ12 : δ < 1 / 2 := by linarith
  let F : OpenPartialHomeomorph Plane S := Φ.trans (Gt 1).toOpenPartialHomeomorph
  have hsrc : {x : Plane | |‖x‖ - 3 / 2| < δ} ⊆ F.source := by
    intro x hx
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hΦ ?_, mem_univ _⟩
    have hx' : |‖x‖ - 3 / 2| < δ := hx
    rw [abs_lt] at hx'
    exact ⟨by linarith, by linarith⟩
  have hfix : ∀ z : Plane, |z 1| < δ → (∀ (j : Fin n) (v : Plane),
      v ∈ planeRect (r₁ / 2 - 3 * (r₁ / 16)) (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16))
        (r₁ / 16) → |v 1| < δ → ∀ m : ℤ, α * (j : ℕ) + v 0 = z 0 + 2 * Real.pi * m →
          h j v = v) → Ga 1 (J 1 (Φ (polarStripMap z))) = J 1 (Φ (polarStripMap z)) := by
    intro z hz hyp
    by_cases hin : J 1 (Φ (polarStripMap z)) ∈ ⋃ j, κ j '' planeRect (r₁ / 2 - 3 * (r₁ / 16))
        (α - r₁ / 2 + 3 * (r₁ / 16)) (-(r₁ / 16)) (r₁ / 16)
    · obtain ⟨j, v, hv, hvz⟩ := mem_iUnion.mp hin
      have hvs := hR₀κ j hv
      have hv1 : |v 1| ≤ r₁ / 16 := abs_le.mpr ⟨hv.2.2.1, hv.2.2.2⟩
      have hPi : polarStripMap (Plane.mk (α * (j : ℕ)) 0 + v) = polarStripMap z := by
        rw [hκJ j v hvs] at hvz
        exact hPinj _ _ (by rw [hp1]; linarith) (by linarith) hvz
      obtain ⟨h1, m, hm⟩ := polarStripMap_eq_polarStripMap
        (by rw [hp1, abs_lt]; constructor <;> linarith [abs_le.mp hv1])
        (by rw [abs_lt]; constructor <;> linarith [abs_lt.mp hz]) hPi
      rw [hp1] at h1
      change α * (j : ℕ) + v 0 = z 0 + 2 * Real.pi * m at hm
      rw [← hvz, hGaeq j 1 ⟨v, hv, rfl⟩, hGκ j v hvs, hyp j v hv (by rw [h1]; exact hz) m hm]
    · exact (hGafix 1).1 hin
  have hsm := polarBand_exists_local_chart F (fun z => J 1 (Φ (polarStripMap z))) (Ga 1)
    (fun z => rfl) hα hnα hr₁α hδr cJ hcJmax hcJs' hcJe'
    (fun k v => congrArg (fun y => J 1 (Φ y)) (polarStripMap_mk_add_shift hnα k.2 v))
    (fun k v => κ k v)
    (fun k => chartAt Plane (Φ (polarStripMap (xb k))))
    (fun k => IsManifold.chart_mem_maximalAtlas _) ρ δa (fun k v => h k v) hρ hρr hδk
    hδaW (fun k v hv => hκJ k v (hR₀κ k hv))
    (fun k v hv => hGaeq k 1 ⟨v, hv, rfl⟩ |>.trans (hGκ k v (hR₀κ k hv))) hhends hhmaps hhsm
    hhdet hfix
  have hBo : IsOpen {x : Plane | |‖x‖ - 3 / 2| < δ} :=
    isOpen_lt (continuous_abs.comp (continuous_norm.sub continuous_const)) continuous_const
  refine ⟨Gt, hGtc, hGti, hGt0, δ, hδpos, hδ12, F.restr {x : Plane | |‖x‖ - 3 / 2| < δ}, ?_,
    fun x _ => rfl, symm_restr_polarBand_mem_maximalAtlas F hδ12 hsrc hsm⟩
  rw [OpenPartialHomeomorph.restr_source' _ _ hBo, inter_eq_right.mpr hsrc]

end DifferentialGeometry.Manifold
