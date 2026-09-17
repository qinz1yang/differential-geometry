import DifferentialGeometry.Topology.PlanarJordan.RegularCurve
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle
import DifferentialGeometry.Topology.PlanarJordan.Regions
import DifferentialGeometry.Topology.Connected.ComponentIn

open Set Schoenflies
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem mem_closure_outside_inter_of_continuous_chord
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
    {γ : ℝ → Schoenflies.Plane} (hγ : ContinuousOn γ (Icc 0 1))
    (hend : γ 1 ∈ Schoenflies.outside C)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ C)
    {W : Set Schoenflies.Plane} (hW : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ W) :
    γ 0 ∈ closure (Schoenflies.outside C ∩ W) := by
  have hsub : MapsTo γ (Ioc (0 : ℝ) 1) Cᶜ := by
    intro t ht
    rcases ht.2.eq_or_lt with rfl | ht1
    · exact hend.1
    · exact havoid t ⟨ht.1, ht1⟩
  have h := hγ.mem_closure_connectedComponentIn_inter zero_lt_one hsub hW
  rwa [hC.connectedComponentIn_eq_outside hend] at h


private theorem mem_closure_outside_saddle_sublevel_of_vertical_chord
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane) {u v s c a : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) (hv : v ≠ 0)
    (hlevel : c + (1 - u ^ 2) * (v ^ 2 + 2 * s) / 2 = a)
    (hcurve : ∀ y ∈ Icc (-|v|) |v|, B (u, y) ∈ C →
      c + (1 - u ^ 2) * (y ^ 2 + 2 * s) / 2 = a)
    (hopp : B (u, -v) ∉ closure (Schoenflies.inside C)) :
    B (u, v) ∈ closure (Schoenflies.outside C ∩
      {p | c + (1 - (B.symm p).1 ^ 2) * ((B.symm p).2 ^ 2 + 2 * s) / 2 < a}) := by
  let γ : ℝ → Schoenflies.Plane := fun t => B (u, (1 - 2 * t) * v)
  have hγ : Continuous γ := B.continuous.comp
    (continuous_const.prodMk ((continuous_const.sub (continuous_const.mul continuous_id)).mul
      continuous_const))
  have hγ0 : γ 0 = B (u, v) := by simp [γ]
  have hγ1 : γ 1 = B (u, -v) := by norm_num [γ]
  have hden : 0 < 1 - u ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < u + 1)]
  have hstrict (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      c + (1 - u ^ 2) * (((1 - 2 * t) * v) ^ 2 + 2 * s) / 2 < a := by
    have hcoeff : (1 - 2 * t) ^ 2 < 1 := by
      nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
    have hsq : ((1 - 2 * t) * v) ^ 2 < v ^ 2 := by
      rw [mul_pow]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hcoeff (sq_pos_of_ne_zero hv)
    have hh := mul_lt_mul_of_pos_left (add_lt_add_right hsq (2 * s)) hden
    linarith
  have hbound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : (1 - 2 * t) * v ∈ Icc (-|v|) |v| := by
    apply abs_le.mp
    rw [abs_mul]
    have hcoeff : |1 - 2 * t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff (abs_nonneg v)
  rw [← hγ0]
  apply mem_closure_outside_inter_of_continuous_chord hC hγ.continuousOn
  · rw [hγ1, hC.outside_eq_compl_closure_inside]
    exact hopp
  · intro t ht hmem
    exact (hstrict t ht).ne (hcurve _ (hbound t ht) hmem)
  · intro t ht
    change c + (1 - (B.symm (B (u, (1 - 2 * t) * v))).1 ^ 2) *
      ((B.symm (B (u, (1 - 2 * t) * v))).2 ^ 2 + 2 * s) / 2 < a
    rw [B.symm_apply_apply]
    exact hstrict t ht


private theorem mem_closure_outside_saddle_sublevel_of_saddleBandLevelCurve
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane) {s τ σ u c R : ℝ}
    (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1)
    (hR : |(saddleBandLevelCurve s τ σ u).2| ≤ R)
    (hcurve : ∀ y ∈ Icc (-R) R, B (u, y) ∈ C →
      c + (1 - u ^ 2) * (y ^ 2 + 2 * s) / 2 = c + s + τ)
    (hopp : B (saddleBandLevelCurve s τ (-σ) u) ∉ closure (Schoenflies.inside C)) :
    B (saddleBandLevelCurve s τ σ u) ∈ closure (Schoenflies.outside C ∩
      {p | c + (1 - (B.symm p).1 ^ 2) * ((B.symm p).2 ^ 2 + 2 * s) / 2 < c + s + τ}) := by
  have hσne : σ ≠ 0 := by intro hz; rw [hz] at hσ; norm_num at hσ
  have hv := right_ne_zero_of_mul (saddleBandLevelCurve_regular hs hτ hσne hu)
  apply mem_closure_outside_saddle_sublevel_of_vertical_chord hC B hu hv
    (saddleBandLevelCurve_height hs hτ hσ hu c)
  · intro y hy
    exact hcurve y ⟨by linarith [hy.1], hy.2.trans hR⟩
  · simpa only [saddleBandLevelCurve, neg_mul] using hopp


private theorem fderiv_comp_inverse_ne_zero
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (c s a : ℝ) {z : ℝ × ℝ}
    (hz : (1 - z.1 ^ 2) * z.2 ≠ 0) :
    fderiv ℝ (fun x : Plane => c + (1 - (B.symm x).1 ^ 2) *
      ((B.symm x).2 ^ 2 + 2 * s) / 2 - a) (B z) ≠ 0 := by
  let q : ℝ × ℝ → ℝ := fun z => c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - a
  let f : Plane → ℝ := fun x => q (B.symm x)
  change fderiv ℝ f (B z) ≠ 0
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hf : ContDiff ℝ ∞ f := hq.comp B.symm.contDiff
  have heq : f ∘ B = q := by funext z; simp [f]
  have hd := fderiv_comp z (hf.differentiable (by simp) (B z))
    (B.contDiff.differentiable (by simp) z)
  rw [heq] at hd
  intro hzero
  rw [hzero, ContinuousLinearMap.zero_comp] at hd
  apply hz
  have happly := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hd
  simpa only [q, fderiv_sub_const, fderiv_saddle_band_apply_vertical, zero_apply] using happly

private theorem eq_saddleBandLevelCurve_of_height
    {s τ σ c : ℝ} (hσ : σ ^ 2 = 1)
    {z : ℝ × ℝ} (hz : z.1 ∈ Ioo (-1 : ℝ) 1) (hzsign : 0 < σ * z.2)
    (hheight : c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = c + s + τ) :
    z = saddleBandLevelCurve s τ σ z.1 := by
  have hden : 0 < 1 - z.1 ^ 2 := by nlinarith [hz.1, hz.2]
  have hsq : z.2 ^ 2 = 2 * (τ + s * z.1 ^ 2) / (1 - z.1 ^ 2) := by
    apply (eq_div_iff hden.ne').mpr
    nlinarith [hheight]
  apply Prod.ext
  · rfl
  change z.2 = σ * Real.sqrt (2 * (τ + s * z.1 ^ 2) / (1 - z.1 ^ 2))
  rw [← hsq, Real.sqrt_sq_eq_abs]
  rcases sq_eq_one_iff.mp hσ with rfl | rfl
  · simp only [one_mul, abs_of_pos (by simpa using hzsign)]
  · have hzneg : z.2 < 0 := by simpa only [neg_one_mul, neg_pos] using hzsign
    rw [abs_of_neg hzneg]
    ring


private theorem exists_open_side_neighborhood_of_saddleBandLevelCurve_of_mem_closure
    {C : Set Plane} (hC : IsSeparating C) (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    {s τ σ c k : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1) (hk : k < 1)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hcurve : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ U)
    (hselected : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈ C)
    (hlevel : ∀ z ∈ U, B z ∈ C →
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = c + s + τ)
    (houtside : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈
      closure (outside C ∩ {x | c + (1 - (B.symm x).1 ^ 2) *
        ((B.symm x).2 ^ 2 + 2 * s) / 2 < c + s + τ})) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧
      saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V ∧ V ⊆ U ∧
      (∀ z ∈ V, B z ∈ inside C ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
      (∀ z ∈ V, B z ∈ closure (inside C) ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) := by
  classical
  let f : Plane → ℝ := fun x => c + (1 - (B.symm x).1 ^ 2) *
    ((B.symm x).2 ^ 2 + 2 * s) / 2 - (c + s + τ)
  let W : Set (ℝ × ℝ) := U ∩ {z | z.1 ∈ Ioo (-k) k ∧ 0 < σ * z.2}
  have hW : IsOpen W := hU.inter ((isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_snd)))
  have hBW : IsOpen (B '' W) := B.toHomeomorph.isOpenMap _ hW
  have hinterval : Ioo (-k) k ⊆ Ioo (-1 : ℝ) 1 :=
    fun u hu => ⟨by linarith [hu.1], hu.2.trans hk⟩
  have hσne : σ ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  have hmem (u : ℝ) (hu : u ∈ Ioo (-k) k) : saddleBandLevelCurve s τ σ u ∈ W := by
    refine ⟨hcurve ⟨u, hu, rfl⟩, hu, ?_⟩
    change 0 < σ * (σ * Real.sqrt (2 * (τ + s * u ^ 2) / (1 - u ^ 2)))
    rw [← mul_assoc, ← pow_two, hσ, one_mul]
    apply Real.sqrt_pos.mpr
    exact div_pos (mul_pos (by norm_num)
      (add_pos_of_pos_of_nonneg hτ (mul_nonneg hs (sq_nonneg u))))
      (by have := hinterval hu; nlinarith [this.1, this.2])
  have hf : ContDiff ℝ ∞ f := by
    have hB := B.symm.contDiff
    dsimp [f]
    fun_prop
  have hzero : ∀ x ∈ B '' W, x ∈ C ↔ f x = 0 := by
    rintro x ⟨z, hz, rfl⟩
    simp only [f, B.symm_apply_apply]
    constructor
    · intro h
      exact sub_eq_zero.mpr (hlevel z hz.1 h)
    · intro h
      have heq := eq_saddleBandLevelCurve_of_height hσ (hinterval hz.2.1) hz.2.2
        (sub_eq_zero.mp h)
      rw [heq]
      exact hselected z.1 hz.2.1
  have hlocal (u : Ioo (-k) k) :
      ∃ N : Set Plane, IsOpen N ∧ B (saddleBandLevelCurve s τ σ u) ∈ N ∧
        N ⊆ B '' W ∧ (∀ x ∈ N, fderiv ℝ f x ≠ 0) ∧
        (∀ x ∈ N, x ∈ inside C ↔ 0 < f x) ∧
        (∀ x ∈ N, x ∈ closure (inside C) ↔ 0 ≤ f x) := by
    apply exists_neighborhood_inside_iff_pos_of_regular_defining_function hC hBW
      (hselected u u.property) ⟨_, hmem u u.property, rfl⟩ hf.contDiffOn hzero
    · exact fderiv_comp_inverse_ne_zero B c s (c + s + τ)
        (saddleBandLevelCurve_regular hs hτ hσne (hinterval u.property))
    · simpa only [f, sub_neg] using houtside u u.property
  choose N hNo hNmem hNW hNreg hNin hNcl using hlocal
  let V := B ⁻¹' ⋃ u, N u
  have hVU : V ⊆ U := by
    intro z hz
    obtain ⟨u, hu⟩ := mem_iUnion.mp hz
    obtain ⟨w, hw, heq⟩ := hNW u hu
    have hwz := B.injective heq
    exact hwz ▸ hw.1
  refine ⟨V, (isOpen_iUnion hNo).preimage B.continuous, ?_, hVU, ?_, ?_⟩
  · rintro z ⟨u, hu, rfl⟩
    exact mem_iUnion.mpr ⟨⟨u, hu⟩, hNmem ⟨u, hu⟩⟩
  · intro z hz
    obtain ⟨u, hu⟩ := mem_iUnion.mp hz
    simpa only [f, B.symm_apply_apply, sub_pos] using hNin u (B z) hu
  · intro z hz
    obtain ⟨u, hu⟩ := mem_iUnion.mp hz
    simpa only [f, B.symm_apply_apply, sub_nonneg] using hNcl u (B z) hu


private theorem exists_open_side_neighborhood_of_saddleBandLevelCurve_local
    {C : Set Plane} (hC : IsSeparating C) (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    {s τ σ c k R : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1) (hk : k < 1)
    (hR : ∀ u ∈ Ioo (-k) k, |(saddleBandLevelCurve s τ σ u).2| < R)
    (hselected : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈ C)
    (hopp : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ (-σ) u) ∉ closure (inside C))
    (hlevel : ∀ z ∈ Icc (-k) k ×ˢ Icc (-R) R, B z ∈ C →
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = c + s + τ) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧
      saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V ∧
      V ⊆ Ioo (-k) k ×ˢ Ioo (-R) R ∧
      (∀ z ∈ V, B z ∈ inside C ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
      (∀ z ∈ V, B z ∈ closure (inside C) ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) := by
  apply exists_open_side_neighborhood_of_saddleBandLevelCurve_of_mem_closure hC B hs hτ hσ hk
    (isOpen_Ioo.prod isOpen_Ioo)
  · rintro z ⟨u, hu, rfl⟩
    exact ⟨hu, abs_lt.mp (hR u hu)⟩
  · exact hselected
  · intro z hz
    exact hlevel z ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
  · intro u hu
    apply mem_closure_outside_saddle_sublevel_of_saddleBandLevelCurve hC B.toHomeomorph
      hs hτ hσ ⟨by linarith [hu.1], hu.2.trans hk⟩ (hR u hu).le
    · intro y hy
      exact hlevel (u, y) ⟨⟨hu.1.le, hu.2.le⟩, hy⟩
    · exact hopp u hu

theorem mem_inside_and_closure_inside_iff_of_saddleBandLevelCurve
    {C : Set Plane} (hC : IsSeparating C) (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    {s τ σ c k R : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1) (hk : k < 1)
    (hR : ∀ u ∈ Ioo (-k) k, |(saddleBandLevelCurve s τ σ u).2| < R)
    (hselected : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈ C)
    (hopp : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ (-σ) u) ∉ closure (inside C))
    (hlevel : ∀ z ∈ Icc (-k) k ×ˢ Icc (-R) R, B z ∈ C →
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = c + s + τ)
    {z : ℝ × ℝ} (hz : z ∈ Ioo (-k) k ×ˢ Ioo (-R) R) :
    (B z ∈ inside C ↔
      c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
    (B z ∈ closure (inside C) ↔
      c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) := by
  obtain ⟨V, hV, hcurveV, _, hVin, _⟩ :=
    exists_open_side_neighborhood_of_saddleBandLevelCurve_local hC B hs hτ hσ hk
      hR hselected hopp hlevel
  let u := z.1
  let ρ := Real.sqrt (2 * (τ + s * u ^ 2) / (1 - u ^ 2))
  let γ₀ : ℝ → ℝ × ℝ := fun t => (u, σ * t)
  let γ : ℝ → Plane := B ∘ γ₀
  have hu : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1.1], hz.1.2.trans hk⟩
  have hden : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hρ : 0 < ρ := Real.sqrt_pos.mpr
    (div_pos (mul_pos (by norm_num)
      (add_pos_of_pos_of_nonneg hτ (mul_nonneg hs (sq_nonneg u)))) hden)
  have hσabs : |σ| = 1 := by
    rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> norm_num
  have hsquare (t : ℝ) : (σ * t) ^ 2 = t ^ 2 := by rw [mul_pow, hσ, one_mul]
  have hρR : ρ < R := by
    have h := hR u hz.1
    change |σ * ρ| < R at h
    rwa [abs_mul, hσabs, one_mul, abs_of_pos hρ] at h
  have hRpos : 0 < R := hρ.trans hρR
  have hγ₀ : Continuous γ₀ := continuous_const.prodMk (continuous_const.mul continuous_id)
  have hγ : Continuous γ := B.continuous.comp hγ₀
  have hroot : c + (1 - u ^ 2) * (ρ ^ 2 + 2 * s) / 2 = c + s + τ := by
    have h := saddleBandLevelCurve_height hs hτ hσ hu c
    simpa only [saddleBandLevelCurve, hsquare] using h
  have hγroot : γ ρ ∈ C := hselected u hz.1
  have hγopp : γ (-ρ) ∈ outside C := by
    rw [hC.outside_eq_compl_closure_inside]
    change B (u, σ * (-ρ)) ∉ closure (inside C)
    simpa only [saddleBandLevelCurve, mul_neg, neg_mul, ρ] using hopp u hz.1
  have hcoord {t : ℝ} (ht : t ∈ Ioo (-R) R) : σ * t ∈ Ioo (-R) R := by
    apply abs_lt.mp
    rw [abs_mul, hσabs, one_mul]
    exact abs_lt.mpr ht
  have hcross {t : ℝ} (ht : t ∈ Ioo (-R) R) : γ t ∈ C ↔ t = ρ := by
    constructor
    · intro htC
      have ht' := hcoord ht
      have hh := hlevel (u, σ * t) ⟨⟨hz.1.1.le, hz.1.2.le⟩, ht'.1.le, ht'.2.le⟩ htC
      simp only [hsquare] at hh
      have hsq : t ^ 2 = ρ ^ 2 := by nlinarith [hden]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
      · exact heq
      · exact False.elim (hγopp.1 (heq ▸ htC))
    · rintro rfl
      exact hγroot
  have hlow : γ '' Ioo (-R) ρ ⊆ outside C := by
    have h := (isPreconnected_Ioo.image γ hγ.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem γ (show -ρ ∈ Ioo (-R) ρ from ⟨by linarith, by linarith⟩))
      (F := Cᶜ) ?_
    · rwa [hC.connectedComponentIn_eq_outside hγopp] at h
    · rintro _ ⟨t, ht, rfl⟩ hCmem
      exact ht.2.ne ((hcross ⟨ht.1, ht.2.trans hρR⟩).mp hCmem)
  have hseed : ∃ t ∈ Ioo ρ R, γ t ∈ inside C := by
    have hc : γ₀ ρ ∈ closure (γ₀ '' Ioo ρ R) :=
      hγ₀.continuousAt.continuousWithinAt.mem_closure_image (by
        rw [closure_Ioo hρR.ne]
        exact ⟨le_rfl, hρR.le⟩)
    obtain ⟨w, hwV, t, ht, rfl⟩ := mem_closure_iff.mp hc V hV (hcurveV ⟨u, hz.1, rfl⟩)
    refine ⟨t, ht, (hVin _ hwV).mpr ?_⟩
    change c + s + τ < c + (1 - u ^ 2) * ((σ * t) ^ 2 + 2 * s) / 2
    rw [hsquare]
    have hsq : ρ ^ 2 < t ^ 2 := by nlinarith [ht.1]
    nlinarith [mul_pos hden (sub_pos.mpr hsq)]
  have hhigh : γ '' Ioo ρ R ⊆ inside C := by
    obtain ⟨t, ht, htC⟩ := hseed
    have h := (isPreconnected_Ioo.image γ hγ.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem γ ht) (F := Cᶜ) ?_
    · rwa [hC.connectedComponentIn_eq_inside htC] at h
    · rintro _ ⟨w, hw, rfl⟩ hCmem
      have hwR : w ∈ Ioo (-R) R := ⟨by linarith [hw.1], hw.2⟩
      exact hw.1.ne' ((hcross hwR).mp hCmem)
  let w := σ * z.2
  have hw : w ∈ Ioo (-R) R := hcoord hz.2
  have hγw : γ w = B z := by
    change B (u, σ * (σ * z.2)) = B z
    rw [← mul_assoc, ← pow_two, hσ, one_mul]
  have hin : B z ∈ inside C ↔ ρ < w := by
    rw [← hγw]
    constructor
    · intro h
      rcases lt_trichotomy w ρ with hlt | heq | hgt
      · exact False.elim (disjoint_left.mp disjoint_inside_outside h
          (hlow ⟨w, ⟨hw.1, hlt⟩, rfl⟩))
      · exact False.elim (h.1 ((hcross hw).mpr heq))
      · exact hgt
    · intro h
      exact hhigh ⟨w, ⟨h, hw.2⟩, rfl⟩
  have hclosed : B z ∈ closure (inside C) ↔ ρ ≤ w := by
    rw [(IsRegionOf.inside C).closure_eq hC, mem_union, hin, ← hγw, hcross hw]
    constructor
    · rintro (h | h)
      · exact h.le
      · exact h.symm.le
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
  have hdiff : c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - (c + s + τ) =
      (1 - u ^ 2) * (w ^ 2 - ρ ^ 2) / 2 := by
    dsimp [w]
    rw [hsquare]
    dsimp [u] at hroot ⊢
    nlinarith [hroot]
  rw [hin, hclosed]
  constructor
  · constructor
    · intro h
      have hsq : ρ ^ 2 < w ^ 2 := by nlinarith
      exact ⟨by nlinarith [mul_pos hden (sub_pos.mpr hsq)], hρ.trans h⟩
    · rintro ⟨hheight, hsign⟩
      by_contra h
      have hsq : w ^ 2 ≤ ρ ^ 2 := by
        have hwρ : w ≤ ρ := le_of_not_gt h
        change 0 < w at hsign
        nlinarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hden.le (sub_nonpos.mpr hsq)]
  · constructor
    · intro h
      have hsq : ρ ^ 2 ≤ w ^ 2 := by nlinarith
      exact ⟨by nlinarith [mul_nonneg hden.le (sub_nonneg.mpr hsq)], hρ.trans_le h⟩
    · rintro ⟨hheight, hsign⟩
      by_contra h
      have hsq : w ^ 2 < ρ ^ 2 := by
        have hwρ : w < ρ := lt_of_not_ge h
        change 0 < w at hsign
        nlinarith
      nlinarith [mul_neg_of_pos_of_neg hden (sub_neg.mpr hsq)]

theorem exists_open_side_neighborhood_of_saddleBandLevelCurve
    {C : Set Plane} (hC : IsSeparating C) (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    {s τ σ c k R : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1) (hk : k < 1)
    (hR : ∀ u ∈ Ioo (-k) k, |(saddleBandLevelCurve s τ σ u).2| < R)
    (hselected : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈ C)
    (hopp : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ (-σ) u) ∉ closure (inside C))
    (hlevel : ∀ z ∈ Icc (-k) k ×ˢ Icc (-R) R, B z ∈ C →
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = c + s + τ) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧
      saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V ∧
      V ⊆ Ioo (-k) k ×ˢ Ioo (-R) R ∧
      (∀ z ∈ V, B z ∈ inside C ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
      (∀ z ∈ V, B z ∈ closure (inside C) ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) := by
  let V := (Ioo (-k) k ×ˢ Ioo (-R) R) ∩ {z : ℝ × ℝ | 0 < σ * z.2}
  refine ⟨V, (isOpen_Ioo.prod isOpen_Ioo).inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_snd)), ?_, inter_subset_left,
    ?_, ?_⟩
  · rintro z ⟨u, hu, rfl⟩
    refine ⟨⟨hu, abs_lt.mp (hR u hu)⟩, ?_⟩
    change 0 < σ * (σ * Real.sqrt (2 * (τ + s * u ^ 2) / (1 - u ^ 2)))
    rw [← mul_assoc, ← pow_two, hσ, one_mul]
    apply Real.sqrt_pos.mpr
    have hu' : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans hk⟩
    exact div_pos (mul_pos (by norm_num)
      (add_pos_of_pos_of_nonneg hτ (mul_nonneg hs (sq_nonneg u))))
      (by nlinarith [hu'.1, hu'.2])
  · intro z hz
    exact (mem_inside_and_closure_inside_iff_of_saddleBandLevelCurve
      hC B hs hτ hσ hk hR hselected hopp hlevel hz.1).1.trans (and_iff_left hz.2)
  · intro z hz
    exact (mem_inside_and_closure_inside_iff_of_saddleBandLevelCurve
      hC B hs hτ hσ hk hR hselected hopp hlevel hz.1).2.trans (and_iff_left hz.2)

open Metric in
theorem eq_saddleBandLevelCurve_of_mem_image_sphere
    (B : ℝ × ℝ → Plane) (G : Plane ≃ₜ Plane)
    {s τ σ c k R r : ℝ} (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hside : ∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
      (B z ∈ interior (G '' closedBall 0 r) ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
      (B z ∈ G '' closedBall 0 r ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2))
    {z : ℝ × ℝ} (hz : z ∈ Ioo (-k) k ×ˢ Ioo (-R) R)
    (hcircle : B z ∈ G '' sphere 0 r) :
    z = saddleBandLevelCurve s τ σ z.1 := by
  have hclosed : B z ∈ G '' closedBall 0 r := image_mono sphere_subset_closedBall hcircle
  have hninter : B z ∉ interior (G '' closedBall 0 r) := by
    rw [← G.image_interior, interior_closedBall _ hr.ne']
    rintro ⟨x, hx, hxe⟩
    obtain ⟨y, hy, hye⟩ := hcircle
    have hxy := G.injective (hxe.trans hye.symm)
    subst y
    exact (mem_ball.mp hx).ne (mem_sphere.mp hy)
  have hsign := ((hside z hz).2.mp hclosed).2
  have hge := ((hside z hz).2.mp hclosed).1
  have hle : c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ c + s + τ := by
    by_contra h
    exact hninter ((hside z hz).1.mpr ⟨lt_of_not_ge h, hsign⟩)
  exact eq_saddleBandLevelCurve_of_height hσ
    ⟨by linarith [hz.1.1], hz.1.2.trans hk⟩ hsign (hle.antisymm hge)

open Metric in
theorem image_sphere_diff_saddleBandLevelCurve_subset
    (B : ℝ × ℝ → Plane) (G : Plane ≃ₜ Plane)
    {s τ σ c k R r b Q : ℝ} (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hb : b < k) (hQ : Q < R) (J : Set ℝ)
    (hside : ∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
      (B z ∈ interior (G '' closedBall 0 r) ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
      (B z ∈ G '' closedBall 0 r ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2)) :
    (G '' sphere 0 r) \ B '' (saddleBandLevelCurve s τ σ '' J) ⊆
      (B '' (Icc (-b) b ×ˢ Icc (-Q) Q))ᶜ ∪
        B '' (saddleBandLevelCurve s τ σ '' (Icc (-b) b \ J)) := by
  intro y hy
  by_cases hbox : y ∈ B '' (Icc (-b) b ×ˢ Icc (-Q) Q)
  · right
    obtain ⟨z, hz, rfl⟩ := hbox
    have hzopen : z ∈ Ioo (-k) k ×ˢ Ioo (-R) R := by
      constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    have heq := eq_saddleBandLevelCurve_of_mem_image_sphere B G hσ hk hr hside hzopen hy.1
    have houtside : z.1 ∉ J := by
      intro hmem
      exact hy.2 ⟨z, ⟨z.1, hmem, heq.symm⟩, rfl⟩
    exact ⟨z, ⟨z.1, ⟨hz.1, houtside⟩, heq.symm⟩, rfl⟩
  · exact Or.inl hbox

end DifferentialGeometry.Topology.PlanarJordan
