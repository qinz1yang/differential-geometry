import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentPairs

/-!
# Normal form of the cone-fold descent: reduction and classification

Every point `y` of the descent domain is `FoldRel`-related to a point over the closed triangle
with fibre coordinate in `[0, 1)` (`exists_foldRel_triangle`): points with `x < 0` by the flip,
points of the wall bands outside the triangle by `wallOneLift`, `wallTwoLift (q/p)`, points of
the apex disc by a screw `ω ↦ e^{-2πik/p} ω` bringing `arg ω` into `[0, 2π/p)`, followed if needed
by the reflection `ω ↦ ω̄` and the screw by `2π/p`, so that `arg ω ∈ [0, θ₁]`, which is the
triangle near the apex (`mem_triangle_of_disc_sector`), and finally an integer fibre
translation. Over the triangle, `conePoint ∘ mirrorMap = f` (`conePoint_mirrorMap_of_mem_triangle`);
`f` is injective there and real only on the walls (`exists_wallSide_eq_zero`, open mapping at
interior points), so two points over the triangle whose images differ by a twist are related
(`foldRel_of_mirrorMap_eq`): equal images give an integer fibre translation or, over the apex, a
screw (`tubeOf_eq_tubeOf_iff`); conjugate images lie over a wall point and a wall lift reduces to
equal images. Consequently two points of the domain with the same image are related with trivial
twist (`foldRel_of_mirrorMap_eq_of_mem`), which is the pairing hypothesis of
`metricFiberCompatible_of_foldPairs` for `foldMap` (`foldMap_pairs`).
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

private theorem conj_ofReal_mul_exp (r ψ : ℝ) :
    conj ((r : ℂ) * exp (ψ * I)) = r * exp (((-ψ : ℝ) : ℂ) * I) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast
  ring

private theorem circleExp_mul_ofReal_mul_exp (t r ψ : ℝ) :
    (Circle.exp t : ℂ) * ((r : ℂ) * exp (ψ * I)) = r * exp (((ψ + t : ℝ) : ℂ) * I) := by
  rw [Circle.coe_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

private theorem theta_eq (hθ : σ.θ₁ * c.p = Real.pi) : σ.θ₁ = Real.pi / c.p := by
  rw [← hθ]
  field_simp [c.p_ne_zero]

theorem mem_triangle_of_disc_sector {z : ℂ} (hz : z ∈ D.patchDisc c hθ) {r ψ : ℝ} (hr : 0 ≤ r)
    (hω : coneDisc σ.vertexOne z = r * exp (ψ * I)) (h0 : 0 ≤ ψ) (h1 : ψ ≤ σ.θ₁) :
    z ∈ σ.triangle := by
  have hz0 := hz.1
  have hv := σ.vertexOne_im_pos
  have hN := normSq_sub_conj_pos hv hz0
  have hθpi : σ.θ₁ ≤ Real.pi := by linarith [σ.θ₁_le, Real.pi_pos]
  refine ⟨hz0, fun i => ?_⟩
  fin_cases i
  · exact (D.re_pos_of_mem_patchDisc c hθ hz).le
  · have h := σ.im_coneDisc_vertexOne_mul z
    rw [hω, im_ofReal_mul_cexp_ofReal_mul_I] at h
    have hs : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
    have : 2 * σ.vertexOne.im * 0 ≤ 2 * σ.vertexOne.im * σ.wallSide 1 z := by
      rw [mul_zero, ← h]
      positivity
    exact le_of_mul_le_mul_left this (by positivity)
  · have h := σ.im_rot_coneDisc_vertexOne_mul z
    have he : exp (-(σ.θ₁ * I)) * ((r : ℂ) * exp (ψ * I)) =
        r * exp (((ψ - σ.θ₁ : ℝ) : ℂ) * I) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [hω, he, im_ofReal_mul_cexp_ofReal_mul_I] at h
    have hs : Real.sin (ψ - σ.θ₁) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    have hsθ := σ.sin_θ₁_pos
    have : Real.sin σ.θ₁ * 0 ≤ Real.sin σ.θ₁ * σ.wallSide 2 z := by
      have h2 : r * Real.sin (ψ - σ.θ₁) * normSq (z - conj σ.vertexOne) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr hs) hN.le
      linarith
    exact le_of_mul_le_mul_left this hsθ

theorem mem_of_foldRel_left {b : Bool} {y y' : ModelCoordinates} (h : D.FoldRel.{u} c hθ b y y') :
    y ∈ D.descentDomain c hθ := by
  obtain ⟨γ, -, -, U, -, hyU, hUN, -, -⟩ := h
  exact hUN hyU

theorem mem_of_foldRel_right {b : Bool} {y y' : ModelCoordinates} (h : D.FoldRel.{u} c hθ b y y') :
    y' ∈ D.descentDomain c hθ := by
  obtain ⟨γ, -, hγ, U, -, hyU, -, hmaps, -⟩ := h
  rw [← hγ]
  exact hmaps hyU

theorem mirrorMap_of_foldRel {b : Bool} {y y' : ModelCoordinates} (h : D.FoldRel.{u} c hθ b y y') :
    D.mirrorMap.{u} c y' = twistMap b (D.mirrorMap c y) := by
  obtain ⟨γ, -, hγ, U, -, hyU, -, -, hid⟩ := h
  rw [← hγ]
  exact hid y hyU

theorem exists_foldRel_triangle_of_disc {y : ModelCoordinates}
    (hy : (logPoint y : ℂ) ∈ D.patchDisc c hθ) :
    ∃ b y₁, (logPoint y₁ : ℂ) ∈ σ.triangle ∧ D.FoldRel.{u} c hθ b y y₁ := by
  set w0 := coneDisc σ.vertexOne (logPoint y) with hwdef
  set r := ‖w0‖
  set φ := arg w0
  have hwe : w0 = r * exp (φ * I) := (Complex.norm_mul_exp_arg_mul_I w0).symm
  have hp : (0 : ℝ) < c.p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c.p)
  have hθ' := theta_eq c hθ
  set k : ℤ := ⌊φ * c.p / (2 * Real.pi)⌋
  set ψ : ℝ := φ - 2 * Real.pi * k / c.p
  have hk1 : (k : ℝ) ≤ φ * c.p / (2 * Real.pi) := Int.floor_le _
  have hk2 : φ * c.p / (2 * Real.pi) < k + 1 := Int.lt_floor_add_one _
  have hpi := Real.pi_pos
  have hψ0 : 0 ≤ ψ := by
    have : 2 * Real.pi * k / c.p ≤ φ := by
      rw [div_le_iff₀ hp]
      rw [le_div_iff₀ (by positivity)] at hk1
      linarith
    simp only [ψ]
    linarith
  have hψ1 : ψ < 2 * Real.pi / c.p := by
    have : φ < 2 * Real.pi * (k + 1) / c.p := by
      rw [lt_div_iff₀ hp]
      rw [div_lt_iff₀ (by positivity)] at hk2
      linarith
    simp only [ψ]
    have e : 2 * Real.pi * (k + 1) / c.p = 2 * Real.pi * k / c.p + 2 * Real.pi / c.p := by ring
    linarith
  have hr : 0 ≤ r := norm_nonneg _
  set y₂ := screwLift σ.vertexOne σ.vertexOne_im_pos (Real.pi * ((-k : ℤ) : ℝ) / c.p)
    (((-k : ℤ) : ℝ) * c.q / c.p + ((0 : ℤ) : ℝ)) y with hy₂
  have h₂ : D.FoldRel.{u} c hθ false y y₂ := D.foldRel_screw c hθ (-k) 0 hy
  have hd₂ : (logPoint y₂ : ℂ) ∈ D.patchDisc c hθ := D.screw_mem_patchDisc c hθ (-k) _ hy
  have hw₂ : coneDisc σ.vertexOne (logPoint y₂) = r * exp (ψ * I) := by
    rw [hy₂, coneDisc_screw (σ := σ) c, ← hwdef, hwe, circleExp_mul_ofReal_mul_exp]
    congr 3
    simp only [ψ]
    push_cast
    ring
  by_cases hcase : ψ ≤ σ.θ₁
  · exact ⟨false, y₂, D.mem_triangle_of_disc_sector c hθ hd₂ hr hw₂ hψ0 hcase, h₂⟩
  · push Not at hcase
    set y₃ := σ.wallOneLift y₂ with hy₃
    have h₃ : D.FoldRel.{u} c hθ true y₂ y₃ := D.foldRel_wallOne c hθ (Or.inr hd₂)
    have hd₃ : (logPoint y₃ : ℂ) ∈ D.patchDisc c hθ := by
      rw [hy₃, σ.coe_logPoint_wallOneLift]
      exact D.refl_one_mem_patchDisc c hθ hd₂
    have hw₃ : coneDisc σ.vertexOne (logPoint y₃) = r * exp (((-ψ : ℝ) : ℂ) * I) := by
      rw [hy₃, σ.coe_logPoint_wallOneLift, σ.coneDisc_vertexOne_refl_one, hw₂,
        conj_ofReal_mul_exp]
    set y₄ := screwLift σ.vertexOne σ.vertexOne_im_pos (Real.pi * ((1 : ℤ) : ℝ) / c.p)
      (((1 : ℤ) : ℝ) * c.q / c.p + ((0 : ℤ) : ℝ)) y₃ with hy₄
    have h₄ : D.FoldRel.{u} c hθ false y₃ y₄ := D.foldRel_screw c hθ 1 0 hd₃
    have hd₄ : (logPoint y₄ : ℂ) ∈ D.patchDisc c hθ := D.screw_mem_patchDisc c hθ 1 _ hd₃
    have hw₄ : coneDisc σ.vertexOne (logPoint y₄) =
        r * exp (((2 * Real.pi / c.p - ψ : ℝ) : ℂ) * I) := by
      rw [hy₄, coneDisc_screw (σ := σ) c, hw₃, circleExp_mul_ofReal_mul_exp]
      congr 3
      push_cast
      ring
    refine ⟨xor false (xor true false), y₄, D.mem_triangle_of_disc_sector c hθ hd₄ hr hw₄
      (by linarith) ?_, D.foldRel_trans c hθ h₂ (D.foldRel_trans c hθ h₃ h₄)⟩
    rw [hθ'] at hcase ⊢
    have e : 2 * Real.pi / c.p = Real.pi / c.p + Real.pi / c.p := by ring
    linarith

theorem mem_patchOne_of_wallSide_one {z : ℂ} (hz : z ∈ σ.triangle) (h1 : σ.wallSide 1 z = 0)
    (hv : z ≠ σ.vertexOne) : z ∈ D.patchOne := by
  have hz0 := hz.1
  have hx : z.re = σ.width := by
    simp only [wallSide] at h1
    linarith
  have hw2 : 0 < σ.wallSide 2 z := σ.wallSide_two_pos_of_re_eq hz0 hx (hz.2 2) hv
  have hfix : σ.refl 1 z = z := σ.refl_of_wallSide_eq_zero hz0 h1
  have hfar : z ∈ σ.foldFar := σ.mem_foldFar_of_le_re hz0 hx.ge
  exact ⟨hz0, by rw [hx]; exact σ.width_pos, by rw [hx]; linarith [σ.width_pos], hw2,
    by rwa [hfix], D.foldWall_subset_V 1 ⟨hz, h1⟩, hfar, by rwa [hfix]⟩

theorem mem_patchTwo_of_wallSide_two (hσ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.wallSide 2 z = 0) (hv : z ≠ σ.vertexOne) : z ∈ D.patchTwo := by
  have hz0 := hz.1
  have hc := σ.cusp_centre hσ
  have hfix : σ.refl 2 z = z := σ.refl_of_wallSide_eq_zero hz0 h2
  have hx0 : 0 ≤ z.re := hz.2 0
  have hxW : z.re ≤ σ.width := by have := hz.2 1; simp only [wallSide] at this; linarith
  have hxpos : 0 < z.re := by
    rcases hx0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h2' := h2
      simp only [wallSide, ← h, hc] at h2'
      nlinarith
  have hxlt : z.re < σ.width := by
    rcases hxW.lt_or_eq with h | h
    · exact h
    · exact absurd (σ.eq_vertexOne_of_re_eq hz0 h h2) hv
  have hfar : z ∈ σ.foldFar := σ.mem_foldFar_of_wallSide_two hσ hz0 h2
  exact ⟨hz0, hxpos, hxlt, by rwa [hfix], by rwa [hfix], D.foldWall_subset_V 2 ⟨hz, h2⟩, hfar,
    by rwa [hfix]⟩

theorem exists_foldRel_triangle_of_patches (hσ : σ.θ₂ = 0) {y : ModelCoordinates}
    (hz : (logPoint y : ℂ) ∈ D.patches c hθ) (hre : 0 ≤ (logPoint y : ℂ).re) :
    ∃ b y₁, (logPoint y₁ : ℂ) ∈ σ.triangle ∧ D.FoldRel.{u} c hθ b y y₁ := by
  have hyN : y ∈ D.descentDomain c hθ := D.mem_descentDomain_of_patches c hθ hz
  rcases hz with (((h | h) | h) | h) | h
  · exact ⟨false, y, σ.patchInt_subset_triangle h, D.foldRel_refl c hθ hyN⟩
  · exact ⟨false, y, D.mem_triangle_of_mem_patchZero h hre, D.foldRel_refl c hθ hyN⟩
  · rcases le_total (logPoint y : ℂ).re σ.width with hx | hx
    · exact ⟨false, y, D.mem_triangle_of_mem_patchOne h hx, D.foldRel_refl c hθ hyN⟩
    · refine ⟨true, σ.wallOneLift y, ?_, D.foldRel_wallOne c hθ (Or.inl h)⟩
      rw [σ.coe_logPoint_wallOneLift]
      exact D.refl_mem_triangle_of_mem_patchOne h hx
  · rcases le_total 0 (σ.wallSide 2 (logPoint y)) with hw | hw
    · exact ⟨false, y, D.mem_triangle_of_mem_patchTwo h hw, D.foldRel_refl c hθ hyN⟩
    · refine ⟨true, ConeShape.wallTwoLift (c.q / c.p) y, ?_, D.foldRel_wallTwo c hθ hσ h⟩
      rw [σ.coe_logPoint_wallTwoLift hσ]
      exact D.refl_mem_triangle_of_mem_patchTwo h hw
  · exact D.exists_foldRel_triangle_of_disc c hθ h

theorem exists_foldRel_triangle (hσ : σ.θ₂ = 0) {y : ModelCoordinates}
    (hy : y ∈ D.descentDomain c hθ) :
    ∃ b y₀, (logPoint y₀ : ℂ) ∈ σ.triangle ∧ 0 ≤ y₀ 2 ∧ y₀ 2 < 1 ∧
      D.FoldRel.{u} c hθ b y y₀ := by
  have hy' : (logPoint y : ℂ) ∈ D.descentBase c hθ := hy
  obtain ⟨b₁, y₁, hT, h₁⟩ : ∃ b y₁, (logPoint y₁ : ℂ) ∈ σ.triangle ∧
      D.FoldRel.{u} c hθ b y y₁ := by
    by_cases h : y 0 < 0
    · have hz : (logPoint (flipMap y) : ℂ) ∈ D.patches c hθ := by
        rw [coe_logPoint_flipMap]
        exact D.refl_mem_patches_of_mem_descentBase c hθ hy'
          (by rw [logPoint_re_eq']; exact h.le)
      have hre : 0 ≤ (logPoint (flipMap y) : ℂ).re := by
        rw [logPoint_re_eq', flipMap_zero]
        linarith
      obtain ⟨b, y₁, hT, h₁⟩ := D.exists_foldRel_triangle_of_patches c hθ hσ hz hre
      exact ⟨xor true b, y₁, hT, D.foldRel_trans c hθ (D.foldRel_flip c hθ hy) h₁⟩
    · have hre : 0 ≤ (logPoint y : ℂ).re := by rw [logPoint_re_eq']; exact not_lt.1 h
      exact D.exists_foldRel_triangle_of_patches c hθ hσ
        (D.mem_patches_of_mem_descentBase c hθ hy' hre) hre
  set n : ℤ := ⌊y₁ 2⌋
  have hn1 : (n : ℝ) ≤ y₁ 2 := Int.floor_le _
  have hn2 : y₁ 2 < n + 1 := Int.lt_floor_add_one _
  refine ⟨xor b₁ false, fibreShift ((-n : ℤ) : ℝ) y₁, by rw [logPoint_fibreShift]; exact hT,
    ?_, ?_, D.foldRel_trans c hθ h₁ (D.foldRel_fibreShift c hθ
      (D.mem_of_foldRel_right c hθ h₁) (-n))⟩
  · rw [fibreShift_two]
    push_cast
    linarith
  · rw [fibreShift_two]
    push_cast
    linarith

theorem conePoint_mirrorMap_of_mem_triangle (hθ : σ.θ₁ * c.p = Real.pi) {p : ModelCoordinates}
    (hp : (logPoint p : ℂ) ∈ σ.triangle) :
    c.conePoint (D.mirrorMap.{u} c p) = D.f (logPoint p) := by
  have hre : 0 ≤ p 0 := by rw [← logPoint_re_eq']; exact hp.2 0
  rw [D.mirrorMap_of_nonneg c hre]
  by_cases hv : (logPoint p : ℂ) = σ.vertexOne
  · rw [totalMap, ite_eq_left hv, conePoint_tubeMap, hv,
      σ.coneApexOne_vertexOne (NeZero.ne c.p), D.f_vertexOne c hθ]
  · rw [totalMap, ite_eq_right hv, D.conePoint_liftMap c (D.f_ne_of_mem_triangle c hθ hp hv)]

theorem exists_wallSide_eq_zero (hσ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.triangle)
    (him : (D.f z).im = 0) : ∃ i, σ.wallSide i z = 0 := by
  by_contra hne
  push Not at hne
  have hpos : ∀ i, 0 < σ.wallSide i z := fun i => lt_of_le_of_ne (hz.2 i) (hne i).symm
  have hT : σ.triangle ∈ 𝓝 z := σ.interior_mem_of_wallSide_pos hz hpos
  have hv : z ≠ σ.vertexOne := by
    rintro rfl
    exact hne 1 σ.wallSide_one_vertexOne_eq_zero
  have hv2 : z ≠ σ.vertexTwo := by
    rw [σ.cusp_vertexTwo hσ]
    exact ConeShape.ne_zero_of_im_pos hz.1
  have hU := D.triangle_subset_U hz
  have hdet := (D.det_fderiv_pos z hU hv hv2).ne'
  have hcd : ContDiffAt ℝ ∞ D.f z := D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds hU)
  have himg : D.f '' σ.triangle ∈ 𝓝 (D.f z) := by
    have hstrict := hcd.hasStrictFDerivAt (by decide)
    have hrange : LinearMap.range (fderiv ℝ D.f z : ℂ →ₗ[ℝ] ℂ) = ⊤ := by
      have hu : IsUnit ((fderiv ℝ D.f z) : ℂ →ₗ[ℝ] ℂ) :=
        (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      exact (LinearMap.isUnit_iff_range_eq_top _).1 hu
    rw [← hstrict.map_nhds_eq_of_surj hrange]
    exact Filter.image_mem_map hT
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 himg
  have hmem : D.f z - ((ε / 2 : ℝ) : ℂ) * I ∈ Metric.ball (D.f z) ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  obtain ⟨t, ht, hft⟩ := hball hmem
  have h1 := (D.f_mem_basePlus ht).2.1
  rw [hft] at h1
  simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
    him] at h1
  linarith

theorem foldRel_of_mirrorMap_eq_false (hσ : σ.θ₂ = 0) {y y' : ModelCoordinates}
    (hy : (logPoint y : ℂ) ∈ σ.triangle) (hy' : (logPoint y' : ℂ) ∈ σ.triangle)
    (h : D.mirrorMap.{u} c y' = D.mirrorMap c y) : D.FoldRel.{u} c hθ false y y' := by
  have hyN : y ∈ D.descentDomain c hθ :=
    D.mem_descentDomain_of_patches c hθ (D.triangle_subset_patches c hθ hσ hy)
  have hf : D.f (logPoint y') = D.f (logPoint y) := by
    rw [← D.conePoint_mirrorMap_of_mem_triangle c hθ hy,
      ← D.conePoint_mirrorMap_of_mem_triangle c hθ hy', h]
  have hz : (logPoint y' : ℂ) = logPoint y := D.bijOn_f.injOn hy' hy hf
  have hre : 0 ≤ y 0 := by rw [← logPoint_re_eq']; exact hy.2 0
  have hre' : 0 ≤ y' 0 := by rw [← logPoint_re_eq']; exact hy'.2 0
  rw [D.mirrorMap_of_nonneg c hre, D.mirrorMap_of_nonneg c hre'] at h
  by_cases hv : (logPoint y : ℂ) = σ.vertexOne
  · have hv' : (logPoint y' : ℂ) = σ.vertexOne := hz.trans hv
    have hd : (logPoint y : ℂ) ∈ D.patchDisc c hθ := by
      rw [hv]
      exact D.vertexOne_mem_patchDisc c hθ
    rw [totalMap, totalMap, ite_eq_left hv, ite_eq_left hv', tubeMap_eq_coneTube,
      tubeMap_eq_coneTube] at h
    obtain ⟨k, n, -, hs⟩ := (c.coneTube_eq_coneTube_iff _ _ _ _ _).1 h.symm
    have hrel := D.foldRel_screw c hθ k n hd
    convert hrel using 1
    apply eq_of_coe_logPoint_eq_of_two_eq
    · rw [hv']
      symm
      apply eq_vertex_of_coneDisc_eq_zero σ.vertexOne_im_pos (logPoint_im_pos _)
      rw [coneDisc_screw (σ := σ) c, hv, coneDisc_self, mul_zero]
    · rw [screwLift_two, hs]
      ring
  · have hv' : (logPoint y' : ℂ) ≠ σ.vertexOne := by rw [hz]; exact hv
    rw [totalMap, totalMap, ite_eq_right hv, ite_eq_right hv', liftMap, liftMap] at h
    have hsrc : ∀ q : ModelCoordinates, (logPoint q : ℂ) = logPoint y →
        (D.baseMap.{u} c q).1.down ≠ ((3 / 2 : ℝ) : ℂ) := by
      intro q hq
      rw [baseMap_fst, hq]
      push_cast
      exact D.f_ne_of_mem_triangle c hθ hy hv
    have hb : D.baseMap.{u} c y' = D.baseMap c y := by
      rw [← c.coneChart_coneLift _ (hsrc y' hz), h, c.coneChart_coneLift _ (hsrc y rfl)]
    have h2 := congrArg Prod.snd hb
    rw [baseMap_snd, baseMap_snd, UpperHalfPlane.ext hz, mul_left_inj] at h2
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
    have hs : y' 2 = y 2 + m := by
      have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      apply mul_left_cancel₀ h2π
      linear_combination hm
    have hrel := D.foldRel_fibreShift c hθ hyN m
    convert hrel using 1
    apply eq_of_coe_logPoint_eq_of_two_eq
    · rw [logPoint_fibreShift, hz]
    · rw [fibreShift_two, hs]

theorem foldRel_of_mirrorMap_eq (hσ : σ.θ₂ = 0) {b : Bool} {y y' : ModelCoordinates}
    (hy : (logPoint y : ℂ) ∈ σ.triangle) (hy' : (logPoint y' : ℂ) ∈ σ.triangle)
    (h : D.mirrorMap.{u} c y' = twistMap b (D.mirrorMap c y)) : D.FoldRel.{u} c hθ b y y' := by
  cases b
  · exact D.foldRel_of_mirrorMap_eq_false c hθ hσ hy hy' h
  have hyN : y ∈ D.descentDomain c hθ :=
    D.mem_descentDomain_of_patches c hθ (D.triangle_subset_patches c hθ hσ hy)
  have hf : D.f (logPoint y') = conj (D.f (logPoint y)) := by
    rw [← D.conePoint_mirrorMap_of_mem_triangle c hθ hy,
      ← D.conePoint_mirrorMap_of_mem_triangle c hθ hy', h, twistMap_true, conePoint_conjMap]
  have h1 := (D.f_mem_basePlus hy).2.1
  have h2 := (D.f_mem_basePlus hy').2.1
  have him : (D.f (logPoint y)).im = 0 := by
    rw [hf, Complex.conj_im] at h2
    linarith
  have hreal : conj (D.f (logPoint y)) = D.f (logPoint y) := Complex.conj_eq_iff_im.2 him
  rw [hreal] at hf
  have hz : (logPoint y' : ℂ) = logPoint y := D.bijOn_f.injOn hy' hy hf
  obtain ⟨ρ, hρ, hρT⟩ : ∃ ρ : ModelCoordinates, D.FoldRel.{u} c hθ true y ρ ∧
      (logPoint ρ : ℂ) = logPoint y := by
    obtain ⟨i, hi⟩ := D.exists_wallSide_eq_zero hσ hy him
    have hfix := σ.refl_of_wallSide_eq_zero hy.1 hi
    fin_cases i
    · exact ⟨flipMap y, D.foldRel_flip c hθ hyN, by rw [coe_logPoint_flipMap]; exact hfix⟩
    · refine ⟨σ.wallOneLift y, D.foldRel_wallOne c hθ ?_, by
        rw [σ.coe_logPoint_wallOneLift]; exact hfix⟩
      by_cases hv : (logPoint y : ℂ) = σ.vertexOne
      · exact Or.inr (by rw [hv]; exact D.vertexOne_mem_patchDisc c hθ)
      · exact Or.inl (D.mem_patchOne_of_wallSide_one hy hi hv)
    · by_cases hv : (logPoint y : ℂ) = σ.vertexOne
      · refine ⟨σ.wallOneLift y, D.foldRel_wallOne c hθ
          (Or.inr (by rw [hv]; exact D.vertexOne_mem_patchDisc c hθ)), ?_⟩
        rw [σ.coe_logPoint_wallOneLift, hv]
        exact σ.refl_of_wallSide_eq_zero σ.vertexOne_im_pos σ.wallSide_one_vertexOne_eq_zero
      · exact ⟨ConeShape.wallTwoLift (c.q / c.p) y,
          D.foldRel_wallTwo c hθ hσ (D.mem_patchTwo_of_wallSide_two hσ hy hi hv),
          by rw [σ.coe_logPoint_wallTwoLift hσ]; exact hfix⟩
  have hρF := D.mirrorMap_of_foldRel c hθ hρ
  have h' : D.mirrorMap.{u} c y' = D.mirrorMap c ρ := by rw [h, hρF]
  have hρ' := D.foldRel_of_mirrorMap_eq_false c hθ hσ (by rw [hρT]; exact hy) hy' h'
  exact D.foldRel_trans c hθ hρ hρ'

theorem foldRel_of_mirrorMap_eq_of_mem (hσ : σ.θ₂ = 0) {y y' : ModelCoordinates}
    (hy : y ∈ D.descentDomain c hθ) (hy' : y' ∈ D.descentDomain c hθ)
    (h : D.mirrorMap.{u} c y = D.mirrorMap c y') : D.FoldRel.{u} c hθ false y y' := by
  obtain ⟨b₁, y₀, hT, -, -, h₁⟩ := D.exists_foldRel_triangle c hθ hσ hy
  obtain ⟨b₂, y₀', hT', -, -, h₂⟩ := D.exists_foldRel_triangle c hθ hσ hy'
  have e1 := D.mirrorMap_of_foldRel c hθ h₁
  have e2 := D.mirrorMap_of_foldRel c hθ h₂
  have e3 : D.mirrorMap.{u} c y₀' = twistMap (xor b₁ b₂) (D.mirrorMap c y₀) := by
    rw [e2, ← h, ← twistMap_twistMap, e1, twistMap_invol]
  have h₀ := D.foldRel_of_mirrorMap_eq c hθ hσ hT hT' e3
  have := D.foldRel_trans c hθ (D.foldRel_trans c hθ h₁ h₀) (D.foldRel_symm c hθ h₂)
  have hb : xor (xor b₁ (xor b₁ b₂)) b₂ = false := by cases b₁ <;> cases b₂ <;> rfl
  rwa [hb] at this

theorem foldMap_pairs (hσ : σ.θ₂ = 0) (y y' : D.descentDomain c hθ)
    (hyy : D.foldMap.{u} c hθ hσ y = D.foldMap c hθ hσ y') :
    ∃ γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates,
      Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) γ =
        coordinateModelMetric .hyperbolicProduct ∧ γ (y : ModelCoordinates) = y' ∧
        ∃ U : TopologicalSpace.Opens ModelCoordinates, (y : ModelCoordinates) ∈ U ∧
          ∃ hUN : (U : Set ModelCoordinates) ⊆ D.descentDomain c hθ,
          ∃ hmaps : MapsTo γ (U : Set ModelCoordinates) (D.descentDomain c hθ),
            ∀ z : U, D.foldMap.{u} c hθ hσ ⟨γ (z : ModelCoordinates), hmaps z.property⟩ =
              D.foldMap c hθ hσ ⟨(z : ModelCoordinates), hUN z.property⟩ := by
  have h : D.mirrorMap.{u} c y = D.mirrorMap c y' := congrArg c.descentIncl hyy
  obtain ⟨γ, hγ, hy, U, hU, hyU, hUN, hmaps, hid⟩ :=
    D.foldRel_of_mirrorMap_eq_of_mem c hθ hσ y.2 y'.2 h
  refine ⟨γ, hγ, hy, ⟨U, hU⟩, hyU, hUN, hmaps, fun z => c.descentIncl_injective ?_⟩
  exact hid z z.2

end ConeShape.FoldData

end GC.Seifert
