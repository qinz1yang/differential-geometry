/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.PlanarSmoothCore
import DifferentialGeometry.Topology.LocalDegree.InjectiveDeterminantSign
import DifferentialGeometry.Topology.Homeomorph.PlanarExtension

open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem planeMk_eq_smul_add (a b : ℝ) :
    Plane.mk a b = a • EuclideanSpace.single 0 1 + b • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp

theorem planeDist_le_abs_add_abs (x y : Plane) : dist x y ≤ |x 0 - y 0| + |x 1 - y 1| := by
  have h0 := abs_nonneg (x 0 - y 0)
  have h1 := abs_nonneg (x 1 - y 1)
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sqrt_le_iff, Real.dist_eq, Real.dist_eq]
  refine ⟨by positivity, ?_⟩
  nlinarith

theorem contDiff_planePerp : ContDiff ℝ ∞ Schoenflies.Plane.perp := by
  have h : Schoenflies.Plane.perp = fun u : Plane =>
      (-(EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) u) • EuclideanSpace.single (0 : Fin 2) 1 +
        ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) u) •
          EuclideanSpace.single (1 : Fin 2) 1 := by
    funext u
    rw [Schoenflies.Plane.perp, planeMk_eq_smul_add]
    rfl
  rw [h]
  exact ((EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).contDiff.neg.smul contDiff_const).add
    ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).contDiff.smul contDiff_const)

theorem hasFDerivAt_of_eqOn_ball_affine {e : Plane → Plane} {p c : Plane}
    {A : Plane →L[ℝ] Plane} {r : ℝ} (he : ∀ x ∈ ball p r, e x = c + A (x - p)) {x : Plane}
    (hx : x ∈ ball p r) : HasFDerivAt e A x := by
  have h1 : HasFDerivAt (fun y : Plane => c + A (y - p)) A x := by
    have h2 := A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2.const_add c
  exact h1.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) he)

theorem det_mul_det_pos_of_injOn_affine {e : Plane → Plane} {U : Set Plane} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hcont : ContinuousOn e U) (hinj : InjOn e U) {p q : Plane}
    (hp : p ∈ U) (hq : q ∈ U) {A B : Plane →L[ℝ] Plane}
    (hA : LinearMap.det (A : Plane →ₗ[ℝ] Plane) ≠ 0)
    (hB : LinearMap.det (B : Plane →ₗ[ℝ] Plane) ≠ 0) {r : ℝ} (hr : 0 < r)
    (hea : ∀ x ∈ ball p r, e x = e p + A (x - p))
    (heb : ∀ x ∈ ball q r, e x = e q + B (x - q)) :
    0 < LinearMap.det (A : Plane →ₗ[ℝ] Plane) * LinearMap.det (B : Plane →ₗ[ℝ] Plane) := by
  have hpA := hasFDerivAt_of_eqOn_ball_affine hea (mem_ball_self hr)
  have hqB := hasFDerivAt_of_eqOn_ball_affine heb (mem_ball_self hr)
  have hs := DifferentialGeometry.LocalDegree.sign_det_fderiv_eq_of_injOn (d := 1) hU hUc hcont
    hinj hp hq hpA.differentiableAt hqB.differentiableAt (by rw [hpA.fderiv]; exact hA)
    (by rw [hqB.fderiv]; exact hB)
  rw [hpA.fderiv, hqB.fderiv] at hs
  rcases lt_or_gt_of_ne hA with h | h
  · have hB' : LinearMap.det (B : Plane →ₗ[ℝ] Plane) < 0 := by
      rw [← sign_eq_neg_one_iff, ← hs, sign_eq_neg_one_iff]
      exact h
    exact mul_pos_of_neg_of_neg h hB'
  · have hB' : 0 < LinearMap.det (B : Plane →ₗ[ℝ] Plane) := by
      rw [← sign_eq_one_iff, ← hs, sign_eq_one_iff]
      exact h
    exact mul_pos h hB'

theorem pos_convexCombination_of_pos {a b μ : ℝ} (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ μ)
    (h1 : μ ≤ 1) : 0 < μ * a + (1 - μ) * b := by
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]
    simpa using hb
  · exact add_pos_of_pos_of_nonneg (mul_pos h ha) (mul_nonneg (by linarith) hb.le)

theorem exists_transverse_field {γ : ℝ → Plane} (hγ : ContDiff ℝ ∞ γ) {τa τb ρ : ℝ}
    (hρ : 0 < ρ) (hab : τa < τb) {va vb na nb : Plane}
    (hγa : ∀ t < τa - ρ / 2, deriv γ t = va) (hγb : ∀ t, τb + ρ / 2 < t → deriv γ t = vb)
    (hd : ∀ t, deriv γ t ≠ 0)
    (hs : 0 < Schoenflies.Plane.det va na * Schoenflies.Plane.det vb nb) :
    ∃ ν : ℝ → Plane, ContDiff ℝ ∞ ν ∧ (∀ t ≤ τa - ρ, ν t = na) ∧
      (∀ t, τb + ρ ≤ t → ν t = nb) ∧ ∀ t, Schoenflies.Plane.det (deriv γ t) (ν t) ≠ 0 := by
  set s := Schoenflies.Plane.det va na with hsdef
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hs
    exact lt_irrefl 0 hs
  have hss : 0 < s * s := mul_self_pos.mpr hs0
  let lam : ℝ → ℝ := fun t => Real.smoothTransition ((τa - 3 * ρ / 4 - t) / (ρ / 4))
  let mu : ℝ → ℝ := fun t => Real.smoothTransition ((t - (τb + 3 * ρ / 4)) / (ρ / 4))
  have hlam1 : ∀ t ≤ τa - ρ, lam t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hlam0 : ∀ t, τa - 3 * ρ / 4 ≤ t → lam t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by linarith))
  have hmu1 : ∀ t, τb + ρ ≤ t → mu t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hmu0 : ∀ t ≤ τb + 3 * ρ / 4, mu t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by linarith))
  have hderiv : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  let ν : ℝ → Plane := fun t => lam t • na + mu t • nb +
    (1 - lam t - mu t) • (s • Schoenflies.Plane.perp (deriv γ t))
  have hlams : ContDiff ℝ ∞ lam := Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const _)
  have hmus : ContDiff ℝ ∞ mu := Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)
  have hνs : ContDiff ℝ ∞ ν := by
    have hp : ContDiff ℝ ∞ (fun t => s • Schoenflies.Plane.perp (deriv γ t)) :=
      (contDiff_planePerp.comp hderiv).const_smul s
    have h1 : ContDiff ℝ ∞ (fun t => lam t • na) := hlams.smul contDiff_const
    have h2 : ContDiff ℝ ∞ (fun t => mu t • nb) := hmus.smul contDiff_const
    have h3 : ContDiff ℝ ∞ (fun t => 1 - lam t - mu t) := (contDiff_const.sub hlams).sub hmus
    exact (h1.add h2).add (h3.smul hp)
  refine ⟨ν, hνs, fun t ht => ?_, fun t ht => ?_, fun t => ?_⟩
  · change lam t • na + mu t • nb + (1 - lam t - mu t) • _ = na
    rw [hlam1 t ht, hmu0 t (by linarith)]
    simp
  · change lam t • na + mu t • nb + (1 - lam t - mu t) • _ = nb
    rw [hlam0 t (by linarith), hmu1 t ht]
    simp
  have hdet : Schoenflies.Plane.det (deriv γ t) (ν t) =
      lam t * Schoenflies.Plane.det (deriv γ t) na +
        mu t * Schoenflies.Plane.det (deriv γ t) nb +
          (1 - lam t - mu t) * (s * ‖deriv γ t‖ ^ 2) := by
    change Schoenflies.Plane.det (deriv γ t) (lam t • na + mu t • nb +
      (1 - lam t - mu t) • (s • Schoenflies.Plane.perp (deriv γ t))) = _
    rw [Schoenflies.Plane.det_add_right, Schoenflies.Plane.det_add_right,
      Schoenflies.Plane.det_smul_right, Schoenflies.Plane.det_smul_right,
      Schoenflies.Plane.det_smul_right, Schoenflies.Plane.det_smul_right,
      Schoenflies.Plane.det_perp_self]
  have hlam01 : 0 ≤ lam t ∧ lam t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hmu01 : 0 ≤ mu t ∧ mu t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hn : 0 < ‖deriv γ t‖ ^ 2 := by
    have := norm_pos_iff.mpr (hd t)
    positivity
  rw [hdet]
  intro h0
  rcases lt_or_ge t (τa - ρ / 2) with h1 | h1
  · rw [hγa t h1, hmu0 t (by linarith), ← hsdef] at h0
    rw [hγa t h1] at hn
    have hc := pos_convexCombination_of_pos hss (mul_pos hss hn) hlam01.1 hlam01.2
    have h3 : s * (lam t * s + 0 * Schoenflies.Plane.det va nb +
        (1 - lam t - 0) * (s * ‖va‖ ^ 2)) =
          lam t * (s * s) + (1 - lam t) * (s * s * ‖va‖ ^ 2) := by ring
    rw [h0, mul_zero] at h3
    linarith
  rcases lt_or_ge (τb + ρ / 2) t with h2 | h2
  · rw [hγb t h2, hlam0 t (by linarith)] at h0
    rw [hγb t h2] at hn
    have hc := pos_convexCombination_of_pos hs (mul_pos hss hn) hmu01.1 hmu01.2
    have h3 : s * (0 * Schoenflies.Plane.det vb na + mu t * Schoenflies.Plane.det vb nb +
        (1 - 0 - mu t) * (s * ‖vb‖ ^ 2)) =
          mu t * (s * Schoenflies.Plane.det vb nb) + (1 - mu t) * (s * s * ‖vb‖ ^ 2) := by ring
    rw [h0, mul_zero] at h3
    linarith
  · rw [hlam0 t (by linarith), hmu0 t (by linarith)] at h0
    have : s * ‖deriv γ t‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · exact hs0 h3
    · exact hn.ne' h3

def planeTube (γ ν : ℝ → Plane) (x : Plane) : Plane := γ (x 0) + x 1 • ν (x 0)

theorem planeTube_mk (γ ν : ℝ → Plane) (t : ℝ) : planeTube γ ν (Plane.mk t 0) = γ t := by
  simp [planeTube]

theorem contDiff_planeTube {γ ν : ℝ → Plane} (hγ : ContDiff ℝ ∞ γ) (hν : ContDiff ℝ ∞ ν) :
    ContDiff ℝ ∞ (planeTube γ ν) := by
  change ContDiff ℝ ∞ (fun x : Plane => γ ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) +
    (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) x •
      ν ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x))
  have h0 : ContDiff ℝ ∞ fun x : Plane => (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x :=
    ContinuousLinearMap.contDiff _
  have h1 : ContDiff ℝ ∞ fun x : Plane => (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) x :=
    ContinuousLinearMap.contDiff _
  have hγ' : ContDiff ℝ ∞ fun x : Plane =>
      γ ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) := hγ.comp h0
  have hν' : ContDiff ℝ ∞ fun x : Plane =>
      ν ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) := hν.comp h0
  exact hγ'.add (h1.smul hν')

theorem det_fderiv_planeTube {γ ν : ℝ → Plane} (hγ : Differentiable ℝ γ)
    (hν : Differentiable ℝ ν) (x : Plane) :
    LinearMap.det (fderiv ℝ (planeTube γ ν) x : Plane →ₗ[ℝ] Plane) =
      Schoenflies.Plane.det (deriv γ (x 0) + x 1 • deriv ν (x 0)) (ν (x 0)) := by
  let π₀ : Plane →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
  let π₁ : Plane →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 2)
  have h1 := (hasDerivAt_iff_hasFDerivAt.mp (hγ (π₀ x)).hasDerivAt).comp x π₀.hasFDerivAt
  have h2 := (hasDerivAt_iff_hasFDerivAt.mp (hν (π₀ x)).hasDerivAt).comp x π₀.hasFDerivAt
  have h3 := h1.add (π₁.hasFDerivAt.smul h2)
  have h4 : HasFDerivAt (planeTube γ ν)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv γ (π₀ x))).comp π₀ +
        (π₁ x • ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv ν (π₀ x))).comp π₀ +
          π₁.smulRight (ν (π₀ x)))) x := h3
  rw [h4.fderiv, det_eq_planeDet]
  congr 1
  · simp [π₀, π₁]
  · simp [π₀, π₁]

theorem exists_homeomorph_smooth_tube {e : Plane → Plane} {τa τb ρ W : ℝ} (hρ : 0 < ρ)
    (hW : 0 < W) (hab : τa + 2 * ρ < τb - 2 * ρ)
    (hcont : ContinuousOn e (planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W))
    (hinj : InjOn e (planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W))
    {A B : Plane →L[ℝ] Plane} (hA : LinearMap.det (A : Plane →ₗ[ℝ] Plane) ≠ 0)
    (hB : LinearMap.det (B : Plane →ₗ[ℝ] Plane) ≠ 0)
    (hea : ∀ x ∈ ball (Plane.mk τa 0) (4 * ρ),
      e x = e (Plane.mk τa 0) + A (x - Plane.mk τa 0))
    (heb : ∀ x ∈ ball (Plane.mk τb 0) (4 * ρ),
      e x = e (Plane.mk τb 0) + B (x - Plane.mk τb 0)) :
    ∃ h : Plane ≃ₜ Plane, EqOn h id (planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W)ᶜ ∧
      ∃ δ > 0, (∀ x : Plane, |x 1| < δ → (x 0 ≤ τa - ρ ∨ τb + ρ ≤ x 0) → h x = x) ∧
        ContDiffOn ℝ ∞ (e ∘ h) (planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ) ∧
        ∀ x ∈ planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ,
          LinearMap.det (fderiv ℝ (e ∘ h) x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  classical
  set pa : Plane := Plane.mk τa 0 with hpa
  set pb : Plane := Plane.mk τb 0 with hpb
  set e₀ : Plane := EuclideanSpace.single 0 1 with he₀
  set e₁ : Plane := EuclideanSpace.single 1 1 with he₁
  set Ro := planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W with hRo
  have hRoR : Ro ⊆ planeRect (τa - 3 * ρ) (τb + 3 * ρ) (-W) W :=
    fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩
  have hRoopen : IsOpen Ro := isOpen_planeOpenRect _ _ _ _
  have hpaRo : pa ∈ Ro := show τa - 3 * ρ < τa ∧ τa < τb + 3 * ρ ∧ -W < (0 : ℝ) ∧ (0 : ℝ) < W
    from ⟨by linarith, by linarith, by linarith, hW⟩
  have hpbRo : pb ∈ Ro := show τa - 3 * ρ < τb ∧ τb < τb + 3 * ρ ∧ -W < (0 : ℝ) ∧ (0 : ℝ) < W
    from ⟨by linarith, by linarith, by linarith, hW⟩
  have hAB := det_mul_det_pos_of_injOn_affine hRoopen
    (convex_planeOpenRect _ _ _ _).isPreconnected (hcont.mono hRoR) (hinj.mono hRoR) hpaRo hpbRo
    hA hB (by linarith : (0 : ℝ) < 4 * ρ) hea heb
  have hdecomp : ∀ (x : Plane) (τ : ℝ), x - Plane.mk τ 0 = (x 0 - τ) • e₀ + x 1 • e₁ := by
    intro x τ
    ext i
    fin_cases i <;> simp [he₀, he₁]
  have hball : ∀ (x : Plane) (τ : ℝ), |x 0 - τ| + |x 1| < 4 * ρ →
      x ∈ ball (Plane.mk τ 0) (4 * ρ) := by
    intro x τ hx
    rw [mem_ball]
    refine lt_of_le_of_lt (planeDist_le_abs_add_abs _ _) ?_
    simpa using hx
  have he₀ne : e₀ ≠ 0 := by
    intro h0
    have := congrArg (fun v : Plane => v 0) h0
    simp [he₀] at this
  have hva : A e₀ ≠ 0 := fun h0 =>
    he₀ne ((A.toContinuousLinearEquivOfDetNeZero hA).map_eq_zero_iff.mp h0)
  have hvb : B e₀ ≠ 0 := fun h0 =>
    he₀ne ((B.toContinuousLinearEquivOfDetNeZero hB).map_eq_zero_iff.mp h0)
  have hlinA : ∀ x : Plane, x ∈ ball pa (4 * ρ) →
      e x = e pa + ((x 0 - τa) • A e₀ + x 1 • A e₁) := by
    intro x hx
    rw [hea x hx, hdecomp x τa, map_add, map_smul, map_smul]
  have hlinB : ∀ x : Plane, x ∈ ball pb (4 * ρ) →
      e x = e pb + ((x 0 - τb) • B e₀ + x 1 • B e₁) := by
    intro x hx
    rw [heb x hx, hdecomp x τb, map_add, map_smul, map_smul]
  have hcoreA : ∀ t, |t - τa| < 4 * ρ → e (Plane.mk t 0) = e pa + (t - τa) • A e₀ := by
    intro t ht
    rw [hlinA _ (hball _ _ (by simpa using ht))]
    simp
  have hcoreB : ∀ t, |t - τb| < 4 * ρ → e (Plane.mk t 0) = e pb + (t - τb) • B e₀ := by
    intro t ht
    rw [hlinB _ (hball _ _ (by simpa using ht))]
    simp
  obtain ⟨γ, hγs, hγd, hγl, hγr, hγsw, hγO⟩ := exists_smooth_core_curve
    (α := τa - 3 * ρ) (β := τb + 3 * ρ) hW hρ (by linarith) hab (by linarith) hcont hinj hva hvb
    (fun t ht => hcoreA t (by linarith)) (fun t ht => hcoreB t (by linarith))
  have hγe : ∀ t ∈ Icc (τa - 3 * ρ) (τb + 3 * ρ), (t ≤ τa - ρ / 2 ∨ τb + ρ / 2 ≤ t) →
      γ t = e (Plane.mk t 0) := by
    intro t ht h
    rcases h with h | h
    · rw [hγl t h, hcoreA t (by rw [abs_lt]; constructor <;> linarith [ht.1])]
    · rw [hγr t h, hcoreB t (by rw [abs_lt]; constructor <;> linarith [ht.2])]
  have hγinj : InjOn γ (Icc (τa - 3 * ρ) (τb + 3 * ρ)) := by
    have hsw : ∀ t ∈ Icc (τa - 3 * ρ) (τb + 3 * ρ),
        (if t ∈ Icc (τa - ρ) (τb + ρ) then γ t else e (Plane.mk t 0)) = γ t := by
      intro t ht
      split_ifs with h
      · rfl
      · refine (hγe t ht ?_).symm
        simp only [mem_Icc, not_and_or, not_le] at h
        rcases h with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
    intro s hs t ht hst
    refine hγsw hs ht ?_
    change (if s ∈ Icc (τa - ρ) (τb + ρ) then γ s else e (Plane.mk s 0)) =
      (if t ∈ Icc (τa - ρ) (τb + ρ) then γ t else e (Plane.mk t 0))
    rw [hsw s hs, hsw t ht, hst]
  have hγda : ∀ t < τa - ρ / 2, deriv γ t = A e₀ := by
    intro t ht
    have hev : γ =ᶠ[𝓝 t] fun s => e pa + (s - τa) • A e₀ :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) fun s hs => hγl s (le_of_lt hs)
    rw [hev.deriv_eq]
    have := (((hasDerivAt_id' t).sub_const τa).smul_const (A e₀)).const_add (e pa)
    rw [this.deriv, one_smul]
  have hγdb : ∀ t, τb + ρ / 2 < t → deriv γ t = B e₀ := by
    intro t ht
    have hev : γ =ᶠ[𝓝 t] fun s => e pb + (s - τb) • B e₀ :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => hγr s (le_of_lt hs)
    rw [hev.deriv_eq]
    have := (((hasDerivAt_id' t).sub_const τb).smul_const (B e₀)).const_add (e pb)
    rw [this.deriv, one_smul]
  obtain ⟨ν, hνs, hνa, hνb, hνt⟩ := exists_transverse_field hγs hρ (by linarith) hγda hγdb hγd
    (na := A e₁) (nb := B e₁) (by rw [← det_eq_planeDet, ← det_eq_planeDet]; exact hAB)
  set σ := planeTube γ ν with hσdef
  have hσs : ContDiff ℝ ∞ σ := contDiff_planeTube hγs hνs
  have hγdiff : Differentiable ℝ γ := hγs.differentiable (by simp)
  have hνdiff : Differentiable ℝ ν := hνs.differentiable (by simp)
  have hσdet := det_fderiv_planeTube hγdiff hνdiff
  have hσea : ∀ x : Plane, x 0 ≤ τa - ρ → x ∈ ball pa (4 * ρ) → σ x = e x := by
    intro x hx0 hx
    rw [hlinA x hx]
    change γ (x 0) + x 1 • ν (x 0) = _
    rw [hγl _ (by linarith), hνa _ hx0, add_assoc]
  have hσeb : ∀ x : Plane, τb + ρ ≤ x 0 → x ∈ ball pb (4 * ρ) → σ x = e x := by
    intro x hx0 hx
    rw [hlinB x hx]
    change γ (x 0) + x 1 • ν (x 0) = _
    rw [hγr _ (by linarith), hνb _ hx0, add_assoc]
  obtain ⟨κe, hκes, hκee⟩ :=
    exists_openPartialHomeomorph_of_continuousOn_injOn hRoopen (hcont.mono hRoR) (hinj.mono hRoR)
  set P := planeOpenRect (τa - 2 * ρ) (τb + 2 * ρ) (-W) W with hP
  have hPRo : P ⊆ Ro := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2.1, hx.2.2.2⟩
  have hOeq : e '' P = κe '' P := (hκee.mono hPRo).image_eq.symm
  have hOopen : IsOpen (e '' P) := by
    rw [hOeq]
    exact κe.isOpen_image_of_subset_source (isOpen_planeOpenRect _ _ _ _) (hκes ▸ hPRo)
  have hOt : e '' P ⊆ κe.target := by
    rw [hOeq]
    rintro _ ⟨y, hy, rfl⟩
    exact κe.map_source (hκes ▸ hPRo hy)
  set α₂ : ℝ := τa - 5 * ρ / 2 with hα₂
  set β₂ : ℝ := τb + 5 * ρ / 2 with hβ₂
  set s : Set Plane := (fun t : ℝ => Plane.mk t 0) '' Icc α₂ β₂ with hsdef
  have hmkc : Continuous (fun t : ℝ => Plane.mk t 0) := by
    have h1 : (fun t : ℝ => Plane.mk t 0) = fun t => t • e₀ := by
      funext t
      ext i
      fin_cases i <;> simp [he₀]
    rw [h1]
    exact continuous_id.smul continuous_const
  have hsc : IsCompact s := isCompact_Icc.image hmkc
  have hσmk : ∀ t, σ (Plane.mk t 0) = γ t := planeTube_mk γ ν
  have hsinj : InjOn σ s := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    rw [hσmk, hσmk] at huv
    have := hγinj ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by linarith [hv.1], by linarith [hv.2]⟩
      huv
    rw [this]
  have hdetcore : ∀ t, LinearMap.det (fderiv ℝ σ (Plane.mk t 0) : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    intro t
    rw [hσdet]
    simpa using hνt t
  have hloc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn σ u := by
    rintro _ ⟨t, -, rfl⟩
    have hstrict : HasStrictFDerivAt σ
        (((fderiv ℝ σ (Plane.mk t 0)).toContinuousLinearEquivOfDetNeZero (hdetcore t) :
          Plane ≃L[ℝ] Plane) : Plane →L[ℝ] Plane) (Plane.mk t 0) := by
      rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      exact hσs.contDiffAt.hasStrictFDerivAt (by simp)
    refine ⟨(hstrict.toOpenPartialHomeomorph σ).source,
      (hstrict.toOpenPartialHomeomorph σ).open_source.mem_nhds
        hstrict.mem_toOpenPartialHomeomorph_source, ?_⟩
    have := (hstrict.toOpenPartialHomeomorph σ).injOn
    rwa [hstrict.toOpenPartialHomeomorph_coe] at this
  obtain ⟨U₁, hU₁, hsU₁, hU₁inj⟩ := hsinj.exists_isOpen_superset hsc
    (fun x _ => hσs.continuous.continuousAt) hloc
  set U₂ : Set Plane := {x | Schoenflies.Plane.det (deriv γ (x 0) + x 1 • deriv ν (x 0))
    (ν (x 0)) ≠ 0} with hU₂
  have hU₂open : IsOpen U₂ := by
    have hc0 := Schoenflies.Plane.continuous_coord 0
    have hc1 := Schoenflies.Plane.continuous_coord 1
    have hdγ : Continuous (deriv γ) := (contDiff_infty_iff_deriv.mp hγs).2.continuous
    have hdν : Continuous (deriv ν) := (contDiff_infty_iff_deriv.mp hνs).2.continuous
    have hv1 : Continuous fun x : Plane => deriv γ (x 0) + x 1 • deriv ν (x 0) :=
      (hdγ.comp hc0).add (hc1.smul (hdν.comp hc0))
    have hv2 : Continuous fun x : Plane => ν (x 0) := hνs.continuous.comp hc0
    have hf : Continuous fun x : Plane =>
        Schoenflies.Plane.det (deriv γ (x 0) + x 1 • deriv ν (x 0)) (ν (x 0)) := by
      unfold Schoenflies.Plane.det
      exact ((hc0.comp hv1).mul (hc1.comp hv2)).sub ((hc1.comp hv1).mul (hc0.comp hv2))
    exact isOpen_ne_fun hf continuous_const
  have hsU₂ : s ⊆ U₂ := by
    rintro _ ⟨t, -, rfl⟩
    change Schoenflies.Plane.det _ _ ≠ 0
    simpa using hνt t
  set U₃ : Set Plane := σ ⁻¹' κe.target with hU₃
  have hU₃open : IsOpen U₃ := hσs.continuous.isOpen_preimage _ κe.open_target
  set U₄ : Set Plane := {x | x 0 < τa - ρ} ∪ {x | τb + ρ < x 0} ∪ σ ⁻¹' (e '' P) with hU₄
  have hU₄open : IsOpen U₄ :=
    ((isOpen_lt (Schoenflies.Plane.continuous_coord 0) continuous_const).union
      (isOpen_lt continuous_const (Schoenflies.Plane.continuous_coord 0))).union
      (hσs.continuous.isOpen_preimage _ hOopen)
  have hmkRo : ∀ t, τa - 3 * ρ < t → t < τb + 3 * ρ → Plane.mk t 0 ∈ Ro := fun t h1 h2 =>
    show τa - 3 * ρ < t ∧ t < τb + 3 * ρ ∧ -W < (0 : ℝ) ∧ (0 : ℝ) < W
    from ⟨h1, h2, by linarith, hW⟩
  have hsU₃₄ : s ⊆ U₃ ∩ U₄ := by
    rintro _ ⟨t, ht, rfl⟩
    rcases lt_or_ge t (τa - ρ) with h1 | h1
    · have hmem := hmkRo t (by linarith [ht.1]) (by linarith)
      have hσe : σ (Plane.mk t 0) = κe (Plane.mk t 0) := by
        rw [hσea _ (show t ≤ τa - ρ from h1.le) (hball _ _ (show |t - τa| + |(0 : ℝ)| < 4 * ρ by
          rw [abs_zero, add_zero, abs_lt]; constructor <;> linarith [ht.1])), hκee hmem]
      refine ⟨?_, Or.inl (Or.inl (show t < τa - ρ from h1))⟩
      change σ (Plane.mk t 0) ∈ κe.target
      rw [hσe]
      exact κe.map_source (hκes ▸ hmem)
    rcases lt_or_ge (τb + ρ) t with h2 | h2
    · have hmem := hmkRo t (by linarith) (by linarith [ht.2])
      have hσe : σ (Plane.mk t 0) = κe (Plane.mk t 0) := by
        rw [hσeb _ (show τb + ρ ≤ t from h2.le) (hball _ _ (show |t - τb| + |(0 : ℝ)| < 4 * ρ by
          rw [abs_zero, add_zero, abs_lt]; constructor <;> linarith [ht.2])), hκee hmem]
      refine ⟨?_, Or.inl (Or.inr (show τb + ρ < t from h2))⟩
      change σ (Plane.mk t 0) ∈ κe.target
      rw [hσe]
      exact κe.map_source (hκes ▸ hmem)
    · have hγP : σ (Plane.mk t 0) ∈ e '' P := by
        rw [hσmk]
        exact hγO t ⟨h1, h2⟩
      exact ⟨hOt hγP, Or.inr hγP⟩
  set V : Set Plane := U₁ ∩ U₂ ∩ (U₃ ∩ U₄) with hV
  have hVopen : IsOpen V := (hU₁.inter hU₂open).inter (hU₃open.inter hU₄open)
  have hsV : s ⊆ V := fun x hx => ⟨⟨hsU₁ hx, hsU₂ hx⟩, hsU₃₄ hx⟩
  obtain ⟨δ₀, hδ₀, hthick⟩ := hsc.exists_thickening_subset_open hVopen hsV
  set δ : ℝ := min (δ₀ / 2) (min (ρ / 2) (W / 2)) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδδ₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδρ : δ ≤ ρ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδW : δ ≤ W / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set T := planeRect α₂ β₂ (-δ) δ with hT
  have hTV : T ⊆ V := by
    intro x hx
    refine hthick (Metric.mem_thickening_iff.mpr ⟨Plane.mk (x 0) 0, ⟨x 0, ⟨hx.1, hx.2.1⟩, rfl⟩,
      lt_of_le_of_lt (planeDist_le_abs_add_abs _ _) ?_⟩)
    change |x 0 - x 0| + |x 1 - 0| < δ₀
    rw [sub_self, abs_zero, zero_add, sub_zero]
    have : |x 1| ≤ δ := abs_le.mpr ⟨hx.2.2.1, hx.2.2.2⟩
    linarith
  have hTRo : T ⊆ Ro := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2.1], by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  let g : Plane → Plane := fun x => κe.symm (σ x)
  have hgc : ContinuousOn g V :=
    κe.continuousOn_symm.comp hσs.continuous.continuousOn fun x hx => hx.2.1
  have hginj : InjOn g V := by
    intro x hx y hy hxy
    have h1 : σ x = σ y := κe.symm.injOn hx.2.1 hy.2.1 hxy
    exact hU₁inj hx.1.1 hy.1.1 h1
  obtain ⟨κg, hκgs, hκgg⟩ := exists_openPartialHomeomorph_of_continuousOn_injOn hVopen hgc hginj
  have hαβ₂ : α₂ < β₂ := by linarith
  have hTc : IsCompact T := isCompact_planeRect hαβ₂ (by linarith)
  have hTint : (interior T).Nonempty := by
    rw [hT, interior_planeRect hαβ₂ (by linarith)]
    exact ⟨Plane.mk ((α₂ + β₂) / 2) 0, show α₂ < (α₂ + β₂) / 2 ∧ (α₂ + β₂) / 2 < β₂ ∧
      -δ < (0 : ℝ) ∧ (0 : ℝ) < δ from ⟨by linarith, by linarith, by linarith, hδpos⟩⟩
  obtain ⟨F, hFκ⟩ := OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isJordanCurve_frontier κg hTc
    (isJordanCurve_frontier_planeRect hαβ₂ (by linarith)) hTint (hκgs ▸ hTV)
  have hFg : ∀ x ∈ T, F x = κe.symm (σ x) := fun x hx => (hFκ hx).trans (hκgg (hTV hx))
  have hFid : ∀ x ∈ T, (x 0 ≤ τa - ρ ∨ τb + ρ ≤ x 0) → F x = x := by
    intro x hx h
    have hxRo := hTRo hx
    have hx1 : |x 1| ≤ δ := abs_le.mpr ⟨hx.2.2.1, hx.2.2.2⟩
    rw [hFg x hx]
    rcases h with h | h
    · have hxb : x ∈ ball pa (4 * ρ) := hball _ _ (by
        rw [abs_of_nonpos (by linarith)]
        linarith [hx.1])
      rw [hσea x h hxb, ← hκee hxRo]
      exact κe.left_inv (hκes ▸ hxRo)
    · have hxb : x ∈ ball pb (4 * ρ) := hball _ _ (by
        rw [abs_of_nonneg (by linarith)]
        linarith [hx.2.1])
      rw [hσeb x h hxb, ← hκee hxRo]
      exact κe.left_inv (hκes ▸ hxRo)
  have hFmid : ∀ x ∈ T, τa - ρ ≤ x 0 → x 0 ≤ τb + ρ → F x ∈ P := by
    intro x hx h1 h2
    rw [hFg x hx]
    rcases (hTV hx).2.2 with (h3 | h3) | h3
    · exact absurd h3 (not_lt.mpr h1)
    · exact absurd h3 (not_lt.mpr h2)
    · obtain ⟨y, hy, hye⟩ := h3
      rw [← hye, ← hκee (hPRo hy), κe.left_inv (hκes ▸ hPRo hy)]
      exact hy
  obtain ⟨H, hHF, hHid⟩ := exists_homeomorph_eqOn_strip (α := α₂) (β := β₂) (δ := δ) (W := W)
    (η := ρ / 2) (by linarith) (by linarith) hδpos (by linarith) F
    (fun x hx h => hFid x hx (by
      rcases h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)))
    (fun x hx h1 h2 => by
      rcases lt_or_ge (x 0) (τa - ρ) with h3 | h3
      · rw [hFid x hx (Or.inl h3.le)]
        exact ⟨h1, h2, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
      rcases lt_or_ge (τb + ρ) (x 0) with h4 | h4
      · rw [hFid x hx (Or.inr h4.le)]
        exact ⟨h1, h2, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
      have := hFmid x hx h3 h4
      exact ⟨by linarith [this.1], by linarith [this.2.1], this.2.2.1, this.2.2.2⟩)
    (fun x hx h1 h2 => by
      rcases lt_or_ge (x 0) (τa - ρ) with h3 | h3
      · rw [hFid x hx (Or.inl h3.le)]
        linarith
      rcases lt_or_ge (τb + ρ) (x 0) with h4 | h4
      · rw [hFid x hx (Or.inr h4.le)]
        linarith
      have := hFmid x hx h3 h4
      linarith [this.1])
  have hends : ∀ x : Plane, |x 1| < δ → (x 0 ≤ τa - ρ ∨ τb + ρ ≤ x 0) → H x = x := by
    intro x hx1 h
    by_cases hx : x ∈ planeOpenRect α₂ β₂ (-W) W
    · have hxT : x ∈ T := ⟨hx.1.le, hx.2.1.le, by linarith [(abs_lt.mp hx1).1],
        by linarith [(abs_lt.mp hx1).2]⟩
      rw [hHF hxT]
      exact hFid x hxT h
    · exact hHid hx
  refine ⟨H, fun x hx => hHid fun hx' => hx ⟨by linarith [hx'.1], by linarith [hx'.2.1],
    hx'.2.2.1, hx'.2.2.2⟩, δ, hδpos, hends, ?_⟩
  have key : ∀ x ∈ planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ, ∃ φ : Plane → Plane,
      (e ∘ H) =ᶠ[𝓝 x] φ ∧ ContDiffAt ℝ ∞ φ x ∧
        LinearMap.det (fderiv ℝ φ x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    intro x hx
    rcases lt_or_ge (x 0) (τa - ρ) with h1 | h1
    · refine ⟨fun y => e pa + A (y - pa), ?_,
        (contDiff_const.add (A.contDiff.comp (contDiff_id.sub contDiff_const))).contDiffAt, ?_⟩
      · have hN : IsOpen (planeOpenRect (τa - 3 * ρ) (τa - ρ) (-δ) δ) :=
          isOpen_planeOpenRect _ _ _ _
        refine Filter.eventuallyEq_of_mem (hN.mem_nhds ⟨hx.1, h1, hx.2.2.1, hx.2.2.2⟩) ?_
        intro y hy
        have hy1 : |y 1| < δ := abs_lt.mpr ⟨hy.2.2.1, hy.2.2.2⟩
        change e (H y) = _
        rw [hends y hy1 (Or.inl hy.2.1.le)]
        refine hea y (hball _ _ ?_)
        rw [abs_of_nonpos (by linarith [hy.2.1])]
        linarith [hy.1]
      · have hd : HasFDerivAt (fun y : Plane => e pa + A (y - pa)) A x := by
          have h3 := A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const pa)
          rw [ContinuousLinearMap.comp_id] at h3
          exact h3.const_add _
        rw [hd.fderiv]
        exact hA
    rcases lt_or_ge (τb + ρ) (x 0) with h2 | h2
    · refine ⟨fun y => e pb + B (y - pb), ?_,
        (contDiff_const.add (B.contDiff.comp (contDiff_id.sub contDiff_const))).contDiffAt, ?_⟩
      · have hN : IsOpen (planeOpenRect (τb + ρ) (τb + 3 * ρ) (-δ) δ) :=
          isOpen_planeOpenRect _ _ _ _
        refine Filter.eventuallyEq_of_mem (hN.mem_nhds ⟨h2, hx.2.1, hx.2.2.1, hx.2.2.2⟩) ?_
        intro y hy
        have hy1 : |y 1| < δ := abs_lt.mpr ⟨hy.2.2.1, hy.2.2.2⟩
        change e (H y) = _
        rw [hends y hy1 (Or.inr hy.1.le)]
        refine heb y (hball _ _ ?_)
        rw [abs_of_nonneg (by linarith [hy.1])]
        linarith [hy.2.1]
      · have hd : HasFDerivAt (fun y : Plane => e pb + B (y - pb)) B x := by
          have h3 := B.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const pb)
          rw [ContinuousLinearMap.comp_id] at h3
          exact h3.const_add _
        rw [hd.fderiv]
        exact hB
    · have hN : IsOpen (planeOpenRect α₂ β₂ (-δ) δ) := isOpen_planeOpenRect _ _ _ _
      have hxN : x ∈ planeOpenRect α₂ β₂ (-δ) δ :=
        ⟨by linarith, by linarith, hx.2.2.1, hx.2.2.2⟩
      have hNT : planeOpenRect α₂ β₂ (-δ) δ ⊆ T :=
        fun y hy => ⟨hy.1.le, hy.2.1.le, hy.2.2.1.le, hy.2.2.2.le⟩
      refine ⟨σ, Filter.eventuallyEq_of_mem (hN.mem_nhds hxN) fun y hy => ?_,
        hσs.contDiffAt, ?_⟩
      · change e (H y) = σ y
        have hyT := hNT hy
        have hyt : σ y ∈ κe.target := (hTV hyT).2.1
        rw [hHF hyT, hFg y hyT, ← hκee (hκes ▸ κe.map_target hyt), κe.right_inv hyt]
      · rw [hσdet]
        exact (hTV (hNT hxN)).1.2
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨φ, h1, h2, -⟩ := key x hx
    exact (h2.congr_of_eventuallyEq h1).contDiffWithinAt
  · obtain ⟨φ, h1, -, h3⟩ := key x hx
    rw [h1.fderiv_eq]
    exact h3

end DifferentialGeometry.Topology.PlanarJordan
