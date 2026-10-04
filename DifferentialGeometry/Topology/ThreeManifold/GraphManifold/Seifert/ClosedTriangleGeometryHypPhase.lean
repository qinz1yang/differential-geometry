import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryPhase

/-!
# The fibre phase of a closed triangle block with abstract local gauges

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3–4, with
review 33 §4.1 and §5.4: the phase algebra is reused, but curvature-free, with the local gauges
as data). A `HypPhase` collects the twists `kⱼ`, a nonzero signed fibre step `ℓ` and two local
gauges `ψ₁ ψ₂ : ℂ → ℝ`; its phase is B3's phase with connection curvature `0` (`base`) plus the
blended gauge term `(2π/ℓ)(χ₁(u) ψ₁ z + χ₂(u) ψ₂ z)`. The wall rules become
`theta_wallOne` (if `ψ₁ z' = -ψ₁ z`), `theta_wallZero` (if `ψ₂ z' = -ψ₂ z`) and `theta_wallTwo`:
on the wall-2 region (`χ = 0`, `η = 1`) the sum of the phases at `z` and `z'` is
`2πk₁ + (2π/ℓ)(ψ₂ z + ψ₂ z') + (2π/ℓ) step(u) E`, `E = (ψ₁ - ψ₂)(z) + (ψ₁ - ψ₂)(z') - ℓ e`
(`theta_wallTwo_error`, the error formula of review 33 §5.4), which is `2πk₁ + (2π/ℓ)(ψ₂ z + ψ₂ z')`
exactly when the real period identity `E = 0` holds (`theta_wallTwo`). Near the vertices the
gauge of the vertex enters with weight one (`theta_vertexOne`, `theta_vertexTwo`), at the outer
cone not at all (`theta_outer`), and the phase is smooth where the gauges are (`contDiffAt_theta`).
For `ψ₁ = ψ₂ = 0` this is the `H² × ℝ` phase; for `SL₂~` the gauges are the recentring gauges.
-/

set_option autoImplicit false

noncomputable section

open Complex GC.Geometry
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open PhaseData

structure HypPhase where
  k₁ : ℝ
  k₂ : ℝ
  k₃ : ℝ
  ℓ : ℝ
  ψ₁ : ℂ → ℝ
  ψ₂ : ℂ → ℝ

namespace HypPhase

variable (H : HypPhase)

def base : PhaseData := ⟨H.k₁, H.k₂, H.k₃, 0, H.ℓ, 0, 0⟩

def e : ℝ := -(H.k₁ + H.k₂ + H.k₃)

def gauge (z u : ℂ) : ℝ := chiOne u * H.ψ₁ z + chiTwo u * H.ψ₂ z

def theta (z u : ℂ) : ℝ := H.base.theta z u + 2 * Real.pi / H.ℓ * H.gauge z u

theorem base_e : H.base.e = H.e := rfl

theorem base_psi (v z : ℂ) : H.base.psi v z = 0 := by
  simp [PhaseData.psi, base]

theorem theta_wallOne {z z' u : ℂ} (h : 3 / 2 < u.re) (hψ : H.ψ₁ z' = -H.ψ₁ z) :
    H.theta z u + H.theta z' (conj u) = -(2 * Real.pi * H.e) := by
  have hb := H.base.theta_wallOne (z := z) (z' := z') h (by rw [base_psi, base_psi, neg_zero])
  have hs : step u = 1 := step_eq_one (by linarith)
  have h2 : chiTwo u = 0 := by simp [chiTwo, hs]
  unfold theta gauge
  rw [chiOne_conj, chiTwo_conj, h2, hψ]
  rw [base_e] at hb
  linear_combination hb

theorem theta_wallZero {z z' u : ℂ} (h : u.re < -(3 / 2)) (hψ : H.ψ₂ z' = -H.ψ₂ z) :
    H.theta z u + H.theta z' (conj u) = 2 * Real.pi * (H.k₁ + H.k₂) := by
  have hb := H.base.theta_wallZero (z := z) (z' := z') h (by rw [base_psi, base_psi, neg_zero])
  have hs : step u = 0 := step_eq_zero (by linarith)
  have h1 : chiOne u = 0 := by simp [chiOne, hs]
  unfold theta gauge
  rw [chiOne_conj, chiTwo_conj, h1, hψ]
  rw [show H.base.k₁ = H.k₁ from rfl, show H.base.k₂ = H.k₂ from rfl] at hb
  linear_combination hb

theorem theta_wallTwo_error {z z' u : ℂ} (h1 : -(3 / 2) < u.re) (h2 : u.re < 3 / 2)
    (h3 : normSq u ≤ 25 / 4) (hℓ : H.ℓ ≠ 0) :
    H.theta z u + H.theta z' (conj u) =
      2 * Real.pi * H.k₁ + 2 * Real.pi / H.ℓ * (H.ψ₂ z + H.ψ₂ z') +
        2 * Real.pi / H.ℓ * step u *
          ((H.ψ₁ z - H.ψ₂ z) + (H.ψ₁ z' - H.ψ₂ z') - H.ℓ * H.e) := by
  have he : PhaseData.eta u = 1 := eta_eq_one h3
  have hc : chi u = 0 := chi_eq_zero (by linarith)
  have hl : lam u = -Real.pi * step u := by simp [lam, hc]
  have hc1 : chiOne u = step u := by simp [chiOne, he]
  have hc2 : chiTwo u = 1 - step u := by simp [chiTwo, he]
  unfold theta gauge PhaseData.theta
  rw [chi_conj, chiOne_conj, chiTwo_conj, lam_conj, hc, hl, hc1, hc2,
    phaseArg_conj_of_gt (show u.re < ((3 / 2 : ℝ) : ℝ) by linarith),
    phaseArg_conj_of_lt (show (-(3 / 2) : ℝ) < u.re by linarith)]
  simp only [base_psi, base_e]
  simp only [base]
  field_simp
  ring

theorem theta_wallTwo {z z' u : ℂ} (h1 : -(3 / 2) < u.re) (h2 : u.re < 3 / 2)
    (h3 : normSq u ≤ 25 / 4) (hℓ : H.ℓ ≠ 0)
    (hW : (H.ψ₁ z - H.ψ₂ z) + (H.ψ₁ z' - H.ψ₂ z') = H.ℓ * H.e) :
    H.theta z u + H.theta z' (conj u) =
      2 * Real.pi * H.k₁ + 2 * Real.pi / H.ℓ * (H.ψ₂ z + H.ψ₂ z') := by
  rw [H.theta_wallTwo_error h1 h2 h3 hℓ, hW, sub_self, mul_zero, add_zero]

theorem chi_vertexOne {u w : ℂ} {p : ℕ} (hu : u = 3 / 2 + w ^ p / 2) (hwn : ‖w‖ ^ p ≤ 1) :
    chiOne u = 1 ∧ chiTwo u = 0 := by
  have hnorm : ‖u - 3 / 2‖ ≤ 1 / 2 := by
    rw [hu, add_sub_cancel_left, norm_div, norm_pow]
    norm_num
    linarith
  have hre : 1 ≤ u.re := by
    have := abs_re_le_norm (u - 3 / 2)
    rw [sub_re] at this
    norm_num at this
    linarith [abs_le.mp (this.trans hnorm)]
  have hns : normSq u ≤ 25 / 4 := by
    rw [normSq_eq_norm_sq]
    have := norm_le_norm_add_norm_sub' u (3 / 2)
    have e : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    rw [e] at this
    nlinarith [norm_nonneg u]
  have hs : step u = 1 := step_eq_one hre
  have he : PhaseData.eta u = 1 := eta_eq_one hns
  exact ⟨by simp [chiOne, hs, he], by simp [chiTwo, hs]⟩

theorem chi_vertexTwo {u w : ℂ} {p : ℕ} (hu : u = -(3 / 2) + w ^ p / 2) (hwn : ‖w‖ ^ p ≤ 1) :
    chiOne u = 0 ∧ chiTwo u = 1 := by
  have hnorm : ‖u + 3 / 2‖ ≤ 1 / 2 := by
    rw [hu, show -(3 / 2 : ℂ) + w ^ p / 2 + 3 / 2 = w ^ p / 2 by ring, norm_div, norm_pow]
    norm_num
    linarith
  have hre : u.re ≤ -1 := by
    have := abs_re_le_norm (u + 3 / 2)
    rw [add_re] at this
    norm_num at this
    linarith [abs_le.mp (this.trans hnorm)]
  have hns : normSq u ≤ 25 / 4 := by
    rw [normSq_eq_norm_sq]
    have := norm_le_norm_add_norm_sub' u (-(3 / 2))
    have e : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
    rw [e, sub_neg_eq_add] at this
    nlinarith [norm_nonneg u]
  have hs : step u = 0 := step_eq_zero hre
  have he : PhaseData.eta u = 1 := eta_eq_one hns
  exact ⟨by simp [chiOne, hs], by simp [chiTwo, hs, he]⟩

theorem theta_vertexOne {z u w : ℂ} {p : ℕ} (hu : u = 3 / 2 + w ^ p / 2) (hw : w ≠ 0)
    (hwn : ‖w‖ ^ p ≤ 1) (h1 : -(Real.pi / 2) < p * arg w) (h2 : p * arg w ≤ 3 * Real.pi / 2) :
    H.theta z u = H.k₁ * (p * arg w) + 2 * Real.pi / H.ℓ * H.ψ₁ z +
      H.k₂ * phaseArg (-(3 / 2)) u - Real.pi * H.e := by
  have hb := H.base.theta_vertexOne (z := z) hu hw hwn h1 h2
  obtain ⟨c1, c2⟩ := chi_vertexOne hu hwn
  unfold theta gauge
  rw [hb, c1, c2, base_psi, base_e]
  simp only [base]
  ring

theorem theta_vertexTwo {z u w : ℂ} {p : ℕ} (hu : u = -(3 / 2) + w ^ p / 2) (hw : w ≠ 0)
    (hwn : ‖w‖ ^ p ≤ 1) (h1 : -(Real.pi / 2) < p * arg w) (h2 : p * arg w ≤ 3 * Real.pi / 2) :
    H.theta z u = H.k₂ * (p * arg w) + 2 * Real.pi / H.ℓ * H.ψ₂ z +
      H.k₁ * phaseArg (3 / 2) u := by
  have hb := H.base.theta_vertexTwo (z := z) hu hw hwn h1 h2
  obtain ⟨c1, c2⟩ := chi_vertexTwo hu hwn
  unfold theta gauge
  rw [hb, c1, c2, base_psi]
  simp only [base]
  ring

theorem theta_outer {z u : ℂ} (h : 9 ≤ normSq u) :
    H.theta z u = -(H.k₃ * phaseArg 0 u) - Real.pi * H.e := by
  have hb := H.base.theta_outer (z := z) h
  have he : PhaseData.eta u = 0 := eta_eq_zero (by linarith)
  rw [show H.base.k₃ = H.k₃ from rfl, base_e] at hb
  unfold theta gauge
  rw [hb]
  simp [chiOne, chiTwo, he]

theorem contDiffAt_theta {z₀ u₀ : ℂ} (h1 : u₀ ∈ phaseDomain (3 / 2))
    (h2 : u₀ ∈ phaseDomain (-(3 / 2))) (h3 : u₀ ∈ phaseDomain 0 ∨ normSq u₀ < 121 / 16)
    (hψ₁ : ContDiffAt ℝ ∞ H.ψ₁ z₀) (hψ₂ : ContDiffAt ℝ ∞ H.ψ₂ z₀) :
    ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => H.theta x.1 x.2) (z₀, u₀) := by
  have hb := H.base.contDiffAt_theta (z₀ := z₀) h1 h2 h3
  have hs := contDiff_step.contDiffAt.comp (z₀, u₀) contDiff_snd.contDiffAt
  have he := contDiff_eta.contDiffAt.comp (z₀, u₀) contDiff_snd.contDiffAt
  have hp1 := hψ₁.comp (z₀, u₀) contDiff_fst.contDiffAt
  have hp2 := hψ₂.comp (z₀, u₀) contDiff_fst.contDiffAt
  have key : (fun x : ℂ × ℂ => H.theta x.1 x.2) = fun x =>
      H.base.theta x.1 x.2 + 2 * Real.pi / H.ℓ * (PhaseData.eta x.2 * step x.2 * H.ψ₁ x.1 +
        PhaseData.eta x.2 * (1 - step x.2) * H.ψ₂ x.1) := by
    funext x
    simp only [theta, gauge, chiOne, chiTwo]
  rw [key]
  have hs' : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => step x.2) (z₀, u₀) := hs
  have he' : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => PhaseData.eta x.2) (z₀, u₀) := he
  exact hb.add (contDiffAt_const.mul (((he'.mul hs').mul hp1).add
    ((he'.mul (contDiffAt_const.sub hs')).mul hp2)))

end HypPhase

end Hyp

end ClosedTriangle

end GC.Seifert
