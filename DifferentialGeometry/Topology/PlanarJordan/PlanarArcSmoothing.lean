/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.PolarStrip
import DifferentialGeometry.Topology.Homeomorph.Alexander
import Mathlib.Analysis.Convex.GaugeRescale

open Set Metric Filter
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem det_fderiv_comp_ne_zero {f g : Plane → Plane} {x : Plane} (hg : DifferentiableAt ℝ g x)
    (hf : DifferentiableAt ℝ f (g x))
    (h1 : LinearMap.det (fderiv ℝ g x : Plane →ₗ[ℝ] Plane) ≠ 0)
    (h2 : LinearMap.det (fderiv ℝ f (g x) : Plane →ₗ[ℝ] Plane) ≠ 0) :
    LinearMap.det (fderiv ℝ (f ∘ g) x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  rw [fderiv_comp x hf hg]
  change LinearMap.det ((fderiv ℝ f (g x) : Plane →ₗ[ℝ] Plane).comp
    (fderiv ℝ g x : Plane →ₗ[ℝ] Plane)) ≠ 0
  rw [LinearMap.det_comp]
  exact mul_ne_zero h2 h1

theorem det_fderiv_diffeomorph_ne_zero
    (J : Diffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane Plane ∞) (x : Plane) :
    LinearMap.det (fderiv ℝ J x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  have hJ : ContDiff ℝ ∞ J := contMDiff_iff_contDiff.mp J.contMDiff
  have hJs : ContDiff ℝ ∞ J.symm := contMDiff_iff_contDiff.mp J.symm.contMDiff
  have hc : (J.symm : Plane → Plane) ∘ J = id := funext fun y => J.symm_apply_apply y
  have h := fderiv_comp x (hJs.differentiable (by simp) (J x)) (hJ.differentiable (by simp) x)
  rw [hc, fderiv_id] at h
  have hd : LinearMap.det (((fderiv ℝ J.symm (J x)).comp (fderiv ℝ J x) : Plane →L[ℝ] Plane) :
      Plane →ₗ[ℝ] Plane) = 1 := by
    rw [← h, ContinuousLinearMap.coe_id, LinearMap.det_id]
  change LinearMap.det ((fderiv ℝ J.symm (J x) : Plane →ₗ[ℝ] Plane).comp
    (fderiv ℝ J x : Plane →ₗ[ℝ] Plane)) = 1 at hd
  rw [LinearMap.det_comp] at hd
  intro h0
  rw [h0, mul_zero] at hd
  exact zero_ne_one hd

theorem planeAbsSub_le_dist (x y : Plane) (i : Fin 2) : |x i - y i| ≤ dist x y := by
  rw [EuclideanSpace.dist_eq, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.single_le_sum (f := fun j => dist (x j) (y j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [Real.dist_eq, sq_abs] at h
  exact h

theorem exists_isotopy_eqOn_compl_planeOpenRect {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (h : Plane ≃ₜ Plane) (hh : EqOn h id (planeOpenRect a b c d)ᶜ) :
    ∃ D : ℝ → Plane ≃ₜ Plane, Continuous (fun q : ℝ × Plane => D q.1 q.2) ∧
      Continuous (fun q : ℝ × Plane => (D q.1).symm q.2) ∧ D 0 = Homeomorph.refl Plane ∧
      D 1 = h ∧ ∀ t, EqOn (D t) id (planeOpenRect a b c d)ᶜ ∧
        EqOn (D t).symm id (planeOpenRect a b c d)ᶜ := by
  set s := planeOpenRect a b c d with hs
  have hso : IsOpen s := isOpen_planeOpenRect a b c d
  have hne : (interior s).Nonempty := by
    rw [hso.interior_eq]
    exact ⟨Plane.mk ((a + b) / 2) ((c + d) / 2),
      show a < (a + b) / 2 ∧ (a + b) / 2 < b ∧ c < (c + d) / 2 ∧ (c + d) / 2 < d from
        ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  have hbd : Bornology.IsBounded s := (isCompact_planeRect hab hcd).isBounded.subset
    fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩
  obtain ⟨Γ, hΓi, -, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall (convex_planeOpenRect a b c d)
      hne hbd
  rw [hso.interior_eq] at hΓi
  have hout : ∀ y, y ∉ ball (0 : Plane) 1 → Γ.symm y ∉ s := by
    intro y hy hs'
    apply hy
    rw [← hΓi]
    exact ⟨Γ.symm y, hs', Γ.apply_symm_apply y⟩
  have hin : ∀ x, x ∉ s → Γ x ∉ ball (0 : Plane) 1 := by
    intro x hx hb
    rw [← hΓi] at hb
    obtain ⟨z, hz, hzx⟩ := hb
    rw [Γ.injective hzx] at hz
    exact hx hz
  let f : Plane ≃ₜ Plane := Γ.symm.trans (h.trans Γ)
  have hf : EqOn f id (ball (0 : Plane) 1)ᶜ := by
    intro y hy
    change Γ (h (Γ.symm y)) = y
    rw [hh (hout y hy), id, Γ.apply_symm_apply]
  obtain ⟨H, hHc, hHi, hH0, hH1, hHfix, -, -⟩ := Homeomorph.alexander_trick f zero_le_one hf
  refine ⟨fun t => Γ.trans ((H t).trans Γ.symm), ?_, ?_, ?_, ?_,
    fun t => ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
  · exact Γ.symm.continuous.comp
      (hHc.comp (continuous_fst.prodMk (Γ.continuous.comp continuous_snd)))
  · exact Γ.symm.continuous.comp
      (hHi.comp (continuous_fst.prodMk (Γ.continuous.comp continuous_snd)))
  · refine Homeomorph.ext fun x => ?_
    change Γ.symm (H 0 (Γ x)) = x
    rw [hH0]
    exact Γ.symm_apply_apply x
  · refine Homeomorph.ext fun x => ?_
    change Γ.symm (H 1 (Γ x)) = h x
    rw [hH1]
    change Γ.symm (Γ (h (Γ.symm (Γ x)))) = h x
    rw [Γ.symm_apply_apply, Γ.symm_apply_apply]
  · change Γ.symm (H t (Γ x)) = x
    rw [(hHfix t).1 (hin x hx), id, Γ.symm_apply_apply]
  · change Γ.symm ((H t).symm (Γ x)) = x
    rw [(hHfix t).2 (hin x hx), id, Γ.symm_apply_apply]

theorem exists_homeomorph_smooth_arc {e : Plane → Plane} {τa τb ρ₀ W : ℝ} (hρ₀ : 0 < ρ₀)
    (hW : 0 < W) (hab : τa + 2 * ρ₀ < τb - 2 * ρ₀)
    (hcont : ContinuousOn e (planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W))
    (hinj : InjOn e (planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W))
    {Va Vb : Set Plane} (hVa : IsOpen Va) (hVb : IsOpen Vb) (hpa : Plane.mk τa 0 ∈ Va)
    (hpb : Plane.mk τb 0 ∈ Vb) (hsa : ContDiffOn ℝ ∞ e Va) (hsb : ContDiffOn ℝ ∞ e Vb)
    (hda : ∀ x ∈ Va, LinearMap.det (fderiv ℝ e x : Plane →ₗ[ℝ] Plane) ≠ 0)
    (hdb : ∀ x ∈ Vb, LinearMap.det (fderiv ℝ e x : Plane →ₗ[ℝ] Plane) ≠ 0) :
    ∃ ρ > 0, ρ ≤ ρ₀ ∧ ∃ h : Plane ≃ₜ Plane,
      EqOn h id (planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W)ᶜ ∧
      ∃ δ > 0, δ < W ∧ (∀ x : Plane, |x 1| < δ → (x 0 ≤ τa - ρ ∨ τb + ρ ≤ x 0) → h x = x) ∧
        ContDiffOn ℝ ∞ (e ∘ h) (planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ) ∧
        ∀ x ∈ planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ,
          LinearMap.det (fderiv ℝ (e ∘ h) x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  classical
  set pa : Plane := Plane.mk τa 0 with hpadef
  set pb : Plane := Plane.mk τb 0 with hpbdef
  set R₀ := planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W with hR₀
  have hinvOf : ∀ (L : Plane →L[ℝ] Plane), LinearMap.det (L : Plane →ₗ[ℝ] Plane) ≠ 0 →
      L.IsInvertible := fun L hL =>
    ⟨L.toContinuousLinearEquivOfDetNeZero hL, by simp⟩
  obtain ⟨Ja, -, -, -, -, ra, hra, hJa⟩ := exists_diffeomorph_affine_near hVa hsa
    (fun x hx => hinvOf _ (hda x hx)) hpa isOpen_univ (mem_univ _)
  set r₁ : ℝ := min ra (min ρ₀ W) / 2 with hr₁
  have hr₁pos : 0 < r₁ := by positivity
  have hr₁a : r₁ < ra := by
    have : min ra (min ρ₀ W) ≤ ra := min_le_left _ _
    linarith
  have hr₁ρ : r₁ ≤ ρ₀ / 2 := by
    have : min ra (min ρ₀ W) ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hr₁W : r₁ ≤ W / 2 := by
    have : min ra (min ρ₀ W) ≤ W := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hballR : ∀ x ∈ closedBall pa r₁, x ∈ R₀ := by
    intro x hx
    have h0 := (planeAbsSub_le_dist x pa 0).trans (mem_closedBall.mp hx)
    have h1 := (planeAbsSub_le_dist x pa 1).trans (mem_closedBall.mp hx)
    rw [abs_le] at h0 h1
    simp only [hpadef, Schoenflies.Plane.mk_zero, Schoenflies.Plane.mk_one] at h0 h1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hpbR : pb ∈ R₀ :=
    show τa - 3 * ρ₀ ≤ τb ∧ τb ≤ τb + 3 * ρ₀ ∧ -W ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ W from
      ⟨by linarith, by linarith, by linarith, hW.le⟩
  have hJas : ContDiff ℝ ∞ (Ja.symm : Plane → Plane) := contMDiff_iff_contDiff.mp Ja.symm.contMDiff
  have hJa' : ContDiff ℝ ∞ (Ja : Plane → Plane) := contMDiff_iff_contDiff.mp Ja.contMDiff
  set e₁ : Plane → Plane := fun x => Ja.symm (e x) with he₁
  have he₁c : ContinuousOn e₁ R₀ := Ja.symm.continuous.comp_continuousOn hcont
  have he₁i : InjOn e₁ R₀ := fun x hx y hy hxy => hinj hx hy (Ja.symm.injective hxy)
  set N : Set Plane := (e₁ '' closedBall pa r₁)ᶜ with hNdef
  have hNopen : IsOpen N :=
    ((isCompact_closedBall pa r₁).image_of_continuousOn
      (he₁c.mono hballR)).isClosed.isOpen_compl
  have hpbN : e₁ pb ∈ N := by
    rintro ⟨z, hz, hze⟩
    have := he₁i (hballR z hz) hpbR hze
    have hd : dist pb pa ≤ r₁ := by rw [← this]; exact mem_closedBall.mp hz
    have h0 := (planeAbsSub_le_dist pb pa 0).trans hd
    simp only [hpadef, hpbdef, Schoenflies.Plane.mk_zero] at h0
    rw [abs_of_pos (by linarith)] at h0
    linarith
  have hsb₁ : ContDiffOn ℝ ∞ e₁ Vb := hJas.comp_contDiffOn hsb
  have hdb₁ : ∀ x ∈ Vb, LinearMap.det (fderiv ℝ e₁ x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    intro x hx
    exact det_fderiv_comp_ne_zero (f := Ja.symm) (g := e)
      ((hsb.contDiffAt (hVb.mem_nhds hx)).differentiableAt (by simp))
      (hJas.differentiable (by simp) _) (hdb x hx) (det_fderiv_diffeomorph_ne_zero Ja.symm _)
  obtain ⟨Jb, Kb, -, hKbN, hJbfix, rb, hrb, hJb⟩ := exists_diffeomorph_affine_near hVb hsb₁
    (fun x hx => hinvOf _ (hdb₁ x hx)) hpb hNopen hpbN
  have hJbs : ContDiff ℝ ∞ (Jb.symm : Plane → Plane) := contMDiff_iff_contDiff.mp Jb.symm.contMDiff
  have hJb' : ContDiff ℝ ∞ (Jb : Plane → Plane) := contMDiff_iff_contDiff.mp Jb.contMDiff
  set e' : Plane → Plane := fun x => Jb.symm (e₁ x) with he'
  set ρ : ℝ := min ρ₀ (min (r₁ / 4) (rb / 4)) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀ (lt_min (by linarith) (by linarith))
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρr₁ : ρ ≤ r₁ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρrb : ρ ≤ rb / 4 := (min_le_right _ _).trans (min_le_right _ _)
  set A : Plane →L[ℝ] Plane := fderiv ℝ e pa with hAdef
  set B : Plane →L[ℝ] Plane := fderiv ℝ e₁ pb with hBdef
  have he₁a : ∀ x ∈ ball pa ra, e₁ x = e pa + A (x - pa) := fun x hx => hJa x hx
  have hea' : ∀ x ∈ ball pa (4 * ρ), e' x = e' pa + A (x - pa) := by
    have hfixa : ∀ x ∈ ball pa (4 * ρ), e' x = e₁ x := by
      intro x hx
      have hxc : x ∈ closedBall pa r₁ :=
        ball_subset_closedBall (ball_subset_ball (by linarith) hx)
      have hnot : e₁ x ∉ Kb := fun hk => hKbN hk ⟨x, hxc, rfl⟩
      exact (hJbfix _ hnot).2
    intro x hx
    have hpa4 : pa ∈ ball pa (4 * ρ) := mem_ball_self (by linarith)
    rw [hfixa x hx, hfixa pa hpa4, he₁a x (ball_subset_ball (by linarith) hx),
      he₁a pa (mem_ball_self hra), sub_self, map_zero, add_zero]
  have heb' : ∀ x ∈ ball pb (4 * ρ), e' x = e' pb + B (x - pb) := by
    intro x hx
    have hx' : x ∈ ball pb rb := ball_subset_ball (by linarith) hx
    change Jb.symm (e₁ x) = Jb.symm (e₁ pb) + B (x - pb)
    rw [hJb x hx', hJb pb (mem_ball_self hrb), sub_self, map_zero, add_zero]
  have hA : LinearMap.det (A : Plane →ₗ[ℝ] Plane) ≠ 0 := hda pa hpa
  have hB : LinearMap.det (B : Plane →ₗ[ℝ] Plane) ≠ 0 := hdb₁ pb hpb
  have hRρ : planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W ⊆ R₀ := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2.1, hx.2.2.2⟩
  have he'c : ContinuousOn e' (planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W) :=
    Jb.symm.continuous.comp_continuousOn (he₁c.mono hRρ)
  have he'i : InjOn e' (planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W) := fun x hx y hy hxy =>
    he₁i (hRρ hx) (hRρ hy) (Jb.symm.injective hxy)
  obtain ⟨h, hhid, δ, hδ, hends, hsm, hdet⟩ := exists_homeomorph_smooth_tube hρpos hW
    (by linarith [hρρ₀]) he'c he'i hA hB hea' heb'
  set δ' : ℝ := min δ (W / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'W : δ' < W := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hTsub : planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ') δ' ⊆
      planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ := fun x hx =>
    ⟨hx.1, hx.2.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  have hcomp : e ∘ h = (fun y => Ja (Jb y)) ∘ (e' ∘ h) := by
    funext x
    change e (h x) = Ja (Jb (Jb.symm (Ja.symm (e (h x)))))
    rw [Jb.apply_symm_apply, Ja.apply_symm_apply]
  have hJJ : ContDiff ℝ ∞ (fun y => Ja (Jb y)) := hJa'.comp hJb'
  refine ⟨ρ, hρpos, hρρ₀, h, hhid, δ', hδ'pos, hδ'W,
    fun x hx h' => hends x (lt_of_lt_of_le hx hδ'δ) h', ?_, fun x hx => ?_⟩
  · rw [hcomp]
    exact hJJ.comp_contDiffOn (hsm.mono hTsub)
  · have hxT := hTsub hx
    have hopen : IsOpen (planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ) :=
      isOpen_planeOpenRect _ _ _ _
    have hdiff : DifferentiableAt ℝ (e' ∘ h) x :=
      (hsm.contDiffAt (hopen.mem_nhds hxT)).differentiableAt (by simp)
    rw [hcomp]
    refine det_fderiv_comp_ne_zero hdiff (hJJ.differentiable (by simp) _) (hdet x hxT) ?_
    have hJJ' : (fun y => Ja (Jb y)) = (Ja : Plane → Plane) ∘ Jb := rfl
    rw [hJJ']
    exact det_fderiv_comp_ne_zero (hJb'.differentiable (by simp) _)
      (hJa'.differentiable (by simp) _) (det_fderiv_diffeomorph_ne_zero Jb _)
      (det_fderiv_diffeomorph_ne_zero Ja _)

end DifferentialGeometry.Topology.PlanarJordan
