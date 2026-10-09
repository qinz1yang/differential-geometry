import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryPhase
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphMoebius
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphData

/-!
# The fibre phase of a closed triangle block on a spherical base

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §4, with
review 32 §5). The spherical gauge at a vertex `v` is the real function
`psi v z = -arg (1 + v̄ z)`, the fibre shift of the recentring isometry of the round sphere
(`recentreInvS3`); it is smooth where `1 + v̄ z` lies in the slit plane. The phase of a
`SphPhaseData` (twists `kⱼ`, signed fibre step `ℓ`, inner vertices `v₁`, `v₂`) is the flat phase
of B3 with connection curvature `0` (`flatPart`, the cut-offs and `φ` terms) plus the gauge term
`(2π/ℓ)(χ₁ ψ₁ + χ₂ ψ₂)`. The wall rules are exact identities: walls `1`, `0` from the reflection
rules of the gauge (`theta_wallOne`, `theta_wallZero`), wall `2` from the real closing identity
`ψ₁ z + ψ₁ z' - ψ₂ z - ψ₂ z' = ℓ e` taken as a hypothesis (`theta_wallTwo`); the vertex formulas
`theta_vertexOne`, `theta_vertexTwo`, `theta_outer` carry the gauge of their vertex only.

For a spherical shape the excess formula `1 + v₂ v₁ = (sin θ₃ / cos (S - θ₃)) e^{i(S - π/2)}`,
`S = (θ₁ + θ₂ + θ₃)/2`, gives `2 arg (1 + v₂ v₁) = θ₁ + θ₂ + θ₃ - π`
(`two_mul_arg_one_add_vertexTwo_mul_vertexOne`): the value of the closing identity.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry GC.Geometry
open scoped ContDiff ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

def psiS (v z : ℂ) : ℝ := -arg (1 + conj v * z)

theorem psiS_conj_of_real {v : ℂ} (hv : conj v = v) {z : ℂ} (hz : 1 + conj v * z ∈ slitPlane) :
    psiS v (conj z) = -psiS v z := by
  unfold psiS
  have h : 1 + conj v * conj z = conj (1 + conj v * z) := by
    rw [map_add, map_one, map_mul, conj_conj, hv]
  have hne : arg (1 + conj v * z) ≠ Real.pi := (mem_slitPlane_iff_arg.1 hz).1
  rw [h, arg_conj]
  simp [hne]

theorem psiS_refl_one {v z : ℂ} {r θ : ℝ} (hv : v = r * exp (θ * I))
    (hz : 1 + conj v * z ∈ slitPlane) :
    psiS v (exp (2 * θ * I) * conj z) = -psiS v z := by
  unfold psiS
  set E := exp ((θ : ℂ) * I) with hEdef
  have hE : conj E * E = 1 := by
    rw [mul_comm, mul_conj, normSq_eq_norm_sq, hEdef, norm_exp_ofReal_mul_I]
    norm_num
  have h2 : exp (2 * (θ : ℂ) * I) = E * E := by
    rw [hEdef, ← exp_add]
    ring_nf
  have h : 1 + conj v * (exp (2 * θ * I) * conj z) = conj (1 + conj v * z) := by
    rw [hv, h2]
    simp only [map_add, map_one, map_mul, conj_ofReal, conj_conj]
    linear_combination ((r : ℂ) * E * conj z) * hE
  have hne : arg (1 + conj v * z) ≠ Real.pi := (mem_slitPlane_iff_arg.1 hz).1
  rw [h, arg_conj]
  simp [hne]

theorem contDiffAt_psiS (v : ℂ) {z : ℂ} (hz : 1 + conj v * z ∈ slitPlane) :
    ContDiffAt ℝ ∞ (psiS v) z := by
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => 1 + conj v * z) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  exact ((GC.Geometry.contDiffAt_arg hz).comp z h1.contDiffAt).neg

structure SphPhaseData where
  k₁ : ℝ
  k₂ : ℝ
  k₃ : ℝ
  ℓ : ℝ
  v₁ : ℂ
  v₂ : ℂ

namespace SphPhaseData

variable (P : SphPhaseData)

def e : ℝ := -(P.k₁ + P.k₂ + P.k₃)

def flatPart : PhaseData := ⟨P.k₁, P.k₂, P.k₃, 0, P.ℓ, P.v₁, P.v₂⟩

def gauge (z u : ℂ) : ℝ :=
  2 * Real.pi / P.ℓ * (PhaseData.chiOne u * psiS P.v₁ z + PhaseData.chiTwo u * psiS P.v₂ z)

def theta (z u : ℂ) : ℝ := P.flatPart.theta z u + P.gauge z u

theorem flatPart_e : P.flatPart.e = P.e := rfl

theorem flatPart_psi (v z : ℂ) : P.flatPart.psi v z = 0 := by
  simp [flatPart, PhaseData.psi]

theorem theta_wallOne {z z' u : ℂ} (h : 3 / 2 < u.re) (hψ : psiS P.v₁ z' = -psiS P.v₁ z) :
    P.theta z u + P.theta z' (conj u) = -(2 * Real.pi * P.e) := by
  have hf := P.flatPart.theta_wallOne (z := z) (z' := z') h (by rw [flatPart_psi, flatPart_psi,
    neg_zero])
  have hs : PhaseData.step u = 1 := PhaseData.step_eq_one (by linarith)
  have h2 : PhaseData.chiTwo u = 0 := by simp [PhaseData.chiTwo, hs]
  unfold theta gauge
  rw [PhaseData.chiOne_conj, PhaseData.chiTwo_conj, h2, hψ]
  rw [flatPart_e] at hf
  linear_combination hf

theorem theta_wallZero {z z' u : ℂ} (h : u.re < -(3 / 2)) (hψ : psiS P.v₂ z' = -psiS P.v₂ z) :
    P.theta z u + P.theta z' (conj u) = 2 * Real.pi * (P.k₁ + P.k₂) := by
  have hf := P.flatPart.theta_wallZero (z := z) (z' := z') h (by rw [flatPart_psi, flatPart_psi,
    neg_zero])
  have hs : PhaseData.step u = 0 := PhaseData.step_eq_zero (by linarith)
  have h1 : PhaseData.chiOne u = 0 := by simp [PhaseData.chiOne, hs]
  unfold theta gauge
  rw [PhaseData.chiOne_conj, PhaseData.chiTwo_conj, h1, hψ]
  have hf' : P.flatPart.theta z u + P.flatPart.theta z' (conj u) =
      2 * Real.pi * (P.k₁ + P.k₂) := hf
  linear_combination hf'

theorem flat_theta (z u : ℂ) : P.flatPart.theta z u =
    (1 - PhaseData.chi u) * (P.k₁ * phaseArg (3 / 2) u + P.k₂ * phaseArg (-(3 / 2)) u) -
      PhaseData.chi u * P.k₃ * phaseArg 0 u + P.e * PhaseData.lam u := by
  unfold PhaseData.theta
  rw [flatPart_psi, flatPart_psi, flatPart_e]
  simp only [flatPart]
  ring

theorem theta_wallTwo {z z' u : ℂ} (h1 : -(3 / 2) < u.re) (h2 : u.re < 3 / 2)
    (h3 : normSq u ≤ 25 / 4) (hℓ : P.ℓ ≠ 0)
    (hclose : psiS P.v₁ z + psiS P.v₁ z' - psiS P.v₂ z - psiS P.v₂ z' = P.ℓ * P.e) :
    P.theta z u + P.theta z' (conj u) =
      2 * Real.pi * P.k₁ + 2 * Real.pi / P.ℓ * (psiS P.v₂ z + psiS P.v₂ z') := by
  have he : PhaseData.eta u = 1 := PhaseData.eta_eq_one h3
  have hc : PhaseData.chi u = 0 := PhaseData.chi_eq_zero (by linarith)
  have hc1 : PhaseData.chiOne u = PhaseData.step u := by simp [PhaseData.chiOne, he]
  have hc2 : PhaseData.chiTwo u = 1 - PhaseData.step u := by simp [PhaseData.chiTwo, he]
  have hl : PhaseData.lam u = -Real.pi * PhaseData.step u := by simp [PhaseData.lam, hc]
  unfold theta gauge
  rw [flat_theta, flat_theta, PhaseData.chi_conj, PhaseData.chiOne_conj, PhaseData.chiTwo_conj,
    PhaseData.lam_conj, hc, hl, hc1, hc2,
    phaseArg_conj_of_gt (show u.re < ((3 / 2 : ℝ) : ℝ) by linarith),
    phaseArg_conj_of_lt (show (-(3 / 2) : ℝ) < u.re by linarith)]
  have key : psiS P.v₁ z' = P.ℓ * P.e - psiS P.v₁ z + psiS P.v₂ z + psiS P.v₂ z' := by
    linarith
  rw [key]
  field_simp
  ring

theorem theta_vertexOne {z u w : ℂ} {p : ℕ} (hu : u = 3 / 2 + w ^ p / 2) (hw : w ≠ 0)
    (hwn : ‖w‖ ^ p ≤ 1) (h1 : -(Real.pi / 2) < p * arg w) (h2 : p * arg w ≤ 3 * Real.pi / 2) :
    P.theta z u = P.k₁ * (p * arg w) + 2 * Real.pi / P.ℓ * psiS P.v₁ z +
      P.k₂ * phaseArg (-(3 / 2)) u - Real.pi * P.e := by
  have hf := P.flatPart.theta_vertexOne (z := z) hu hw hwn h1 h2
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
  have hs : PhaseData.step u = 1 := PhaseData.step_eq_one hre
  have he : PhaseData.eta u = 1 := PhaseData.eta_eq_one hns
  unfold theta gauge
  rw [hf, flatPart_psi, flatPart_e]
  simp only [PhaseData.chiOne, PhaseData.chiTwo, hs, he]
  change P.k₁ * (p * arg w) + 2 * Real.pi / P.ℓ * 0 + P.k₂ * phaseArg (-(3 / 2)) u -
    Real.pi * P.e + _ = _
  ring

theorem theta_vertexTwo {z u w : ℂ} {p : ℕ} (hu : u = -(3 / 2) + w ^ p / 2) (hw : w ≠ 0)
    (hwn : ‖w‖ ^ p ≤ 1) (h1 : -(Real.pi / 2) < p * arg w) (h2 : p * arg w ≤ 3 * Real.pi / 2) :
    P.theta z u = P.k₂ * (p * arg w) + 2 * Real.pi / P.ℓ * psiS P.v₂ z +
      P.k₁ * phaseArg (3 / 2) u := by
  have hf := P.flatPart.theta_vertexTwo (z := z) hu hw hwn h1 h2
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
  have hs : PhaseData.step u = 0 := PhaseData.step_eq_zero hre
  have he : PhaseData.eta u = 1 := PhaseData.eta_eq_one hns
  unfold theta gauge
  rw [hf, flatPart_psi]
  simp only [PhaseData.chiOne, PhaseData.chiTwo, hs, he]
  change P.k₂ * (p * arg w) + 2 * Real.pi / P.ℓ * 0 + P.k₁ * phaseArg (3 / 2) u + _ = _
  ring

theorem theta_outer {z u : ℂ} (h : 9 ≤ normSq u) :
    P.theta z u = -(P.k₃ * phaseArg 0 u) - Real.pi * P.e := by
  have hf := P.flatPart.theta_outer (z := z) h
  have he : PhaseData.eta u = 0 := PhaseData.eta_eq_zero (by linarith)
  unfold theta gauge
  rw [hf, flatPart_e]
  simp only [PhaseData.chiOne, PhaseData.chiTwo, he]
  change -(P.k₃ * phaseArg 0 u) - Real.pi * P.e + _ = _
  ring

theorem contDiffAt_theta {z₀ u₀ : ℂ} (h1 : u₀ ∈ phaseDomain (3 / 2))
    (h2 : u₀ ∈ phaseDomain (-(3 / 2))) (h3 : u₀ ∈ phaseDomain 0 ∨ normSq u₀ < 121 / 16)
    (hz1 : 1 + conj P.v₁ * z₀ ∈ slitPlane) (hz2 : 1 + conj P.v₂ * z₀ ∈ slitPlane) :
    ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => P.theta x.1 x.2) (z₀, u₀) := by
  have hf := P.flatPart.contDiffAt_theta (z₀ := z₀) h1 h2 h3
  have he := PhaseData.contDiff_eta.contDiffAt.comp (z₀, u₀) contDiff_snd.contDiffAt
  have hs := PhaseData.contDiff_step.contDiffAt.comp (z₀, u₀) contDiff_snd.contDiffAt
  have hψ1 := (contDiffAt_psiS P.v₁ hz1).comp (z₀, u₀) contDiff_fst.contDiffAt
  have hψ2 := (contDiffAt_psiS P.v₂ hz2).comp (z₀, u₀) contDiff_fst.contDiffAt
  have he' : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => PhaseData.eta x.2) (z₀, u₀) := he
  have hs' : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => PhaseData.step x.2) (z₀, u₀) := hs
  have hg : ContDiffAt ℝ ∞ (fun x : ℂ × ℂ => P.gauge x.1 x.2) (z₀, u₀) := by
    unfold gauge PhaseData.chiOne PhaseData.chiTwo
    exact contDiffAt_const.mul (((he'.mul hs').mul hψ1).add
      ((he'.mul (contDiffAt_const.sub hs')).mul hψ2))
  exact hf.add hg

end SphPhaseData

theorem θ_pos_le (p : ℕ) (hp : 2 ≤ p) : 0 < Real.pi / p ∧ Real.pi / p ≤ Real.pi / 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  refine ⟨div_pos Real.pi_pos (by linarith), ?_⟩
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hp'

section Excess

variable (σ : CompactShape)

theorem sum_θ_gt_of_sph (hσ : σ.curv = .spherical) : Real.pi < σ.θ₁ + σ.θ₂ + σ.θ₃ := by
  have hs : 1 < (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃ : ℝ) := by
    rcases σ.angle_cond with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, hs⟩
    · rw [hσ] at h'
      exact absurd h' (by decide)
    · rw [hσ] at h'
      exact absurd h' (by decide)
    · exact hs
  have e : σ.θ₁ + σ.θ₂ + σ.θ₃ = Real.pi * (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃) := by
    simp only [CompactShape.θ₁, CompactShape.θ₂, CompactShape.θ₃]
    ring
  rw [e]
  nlinarith [Real.pi_pos]

theorem sideTan_sq_sph (hσ : σ.curv = .spherical) (a b c : ℝ) (ha : 0 < a)
    (ha' : a ≤ Real.pi / 2) (hb : 0 < b) (hb' : b ≤ Real.pi / 2) (hc : 0 < c)
    (hc' : c ≤ Real.pi / 2) :
    σ.sideTan a b c =
      Real.sqrt (-(Real.cos ((a + b + c) / 2) * Real.cos ((a + b + c) / 2 - c)) /
        (Real.cos ((a + b + c) / 2 - a) * Real.cos ((a + b + c) / 2 - b))) := by
  set S := (a + b + c) / 2 with hS
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb (by linarith)
  have hca : 0 < Real.cos (S - a) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcb : 0 < Real.cos (S - b) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have P1 : 2 * Real.cos S * Real.cos (S - c) = Real.cos c + Real.cos (a + b) := by
    have h := Real.cos_add S (S - c)
    have h' := Real.cos_sub S (S - c)
    rw [show S + (S - c) = a + b by rw [hS]; ring] at h
    rw [show S - (S - c) = c by ring] at h'
    linear_combination -h - h'
  have P2 : 2 * Real.cos (S - a) * Real.cos (S - b) = Real.cos c + Real.cos (a - b) := by
    have h := Real.cos_add (S - a) (S - b)
    have h' := Real.cos_sub (S - b) (S - a)
    rw [show S - a + (S - b) = c by rw [hS]; ring] at h
    rw [show S - b - (S - a) = a - b by ring] at h'
    linear_combination -h - h'
  have hM : 0 < Real.sin a * Real.sin b := mul_pos hsa hsb
  have hMN : Real.sin a * Real.sin b + (Real.cos c + Real.cos a * Real.cos b) =
      2 * Real.cos (S - a) * Real.cos (S - b) := by
    rw [P2, Real.cos_sub]
    ring
  have hMN' : Real.sin a * Real.sin b - (Real.cos c + Real.cos a * Real.cos b) =
      -(2 * Real.cos S * Real.cos (S - c)) := by
    rw [P1, Real.cos_add]
    ring
  have hpos : 0 < 2 * Real.cos (S - a) * Real.cos (S - b) := by positivity
  have e : (1 - (Real.cos c + Real.cos a * Real.cos b) / (Real.sin a * Real.sin b)) /
      (1 + (Real.cos c + Real.cos a * Real.cos b) / (Real.sin a * Real.sin b)) =
      (Real.sin a * Real.sin b - (Real.cos c + Real.cos a * Real.cos b)) /
        (Real.sin a * Real.sin b + (Real.cos c + Real.cos a * Real.cos b)) := by
    have hN : Real.sin a * Real.sin b + (Real.cos c + Real.cos a * Real.cos b) ≠ 0 := by
      rw [hMN]
      exact hpos.ne'
    field_simp
  unfold CompactShape.sideTan CompactShape.sideCos
  rw [hσ]
  dsimp only
  rw [e, hMN, hMN']
  congr 1
  field_simp

theorem two_mul_arg_one_add_vertexTwo_mul_vertexOne (hσ : σ.curv = .spherical) :
    2 * arg (1 + σ.vertexTwo * σ.vertexOne) = σ.θ₁ + σ.θ₂ + σ.θ₃ - Real.pi := by
  obtain ⟨h1, h1'⟩ := θ_pos_le σ.p₁ σ.two_le_p₁
  obtain ⟨h2, h2'⟩ := θ_pos_le σ.p₂ σ.two_le_p₂
  obtain ⟨h3, h3'⟩ := θ_pos_le σ.p₃ σ.two_le_p₃
  change 0 < σ.θ₁ at h1
  change σ.θ₁ ≤ Real.pi / 2 at h1'
  change 0 < σ.θ₂ at h2
  change σ.θ₂ ≤ Real.pi / 2 at h2'
  change 0 < σ.θ₃ at h3
  change σ.θ₃ ≤ Real.pi / 2 at h3'
  have hsum := sum_θ_gt_of_sph σ hσ
  set S := (σ.θ₁ + σ.θ₂ + σ.θ₃) / 2 with hS
  have hcS : Real.cos S < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
  have hc1 : 0 < Real.cos (S - σ.θ₁) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc2 : 0 < Real.cos (S - σ.θ₂) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc3 : 0 < Real.cos (S - σ.θ₃) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hv2 : σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁ = Real.sqrt (-(Real.cos S * Real.cos (S - σ.θ₁)) /
      (Real.cos (S - σ.θ₂) * Real.cos (S - σ.θ₃))) := by
    rw [sideTan_sq_sph σ hσ _ _ _ h2 h2' h3 h3' h1 h1',
      show (σ.θ₂ + σ.θ₃ + σ.θ₁) / 2 = S by rw [hS]; ring]
  have hv1 : σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂ = Real.sqrt (-(Real.cos S * Real.cos (S - σ.θ₂)) /
      (Real.cos (S - σ.θ₁) * Real.cos (S - σ.θ₃))) := by
    rw [sideTan_sq_sph σ hσ _ _ _ h1 h1' h3 h3' h2 h2',
      show (σ.θ₁ + σ.θ₃ + σ.θ₂) / 2 = S by rw [hS]; ring]
  have hQ1 : 0 ≤ -(Real.cos S * Real.cos (S - σ.θ₁)) /
      (Real.cos (S - σ.θ₂) * Real.cos (S - σ.θ₃)) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  have hprod : σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁ * σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂ =
      -(Real.cos S / Real.cos (S - σ.θ₃)) := by
    rw [hv2, hv1, ← Real.sqrt_mul hQ1]
    have e : -(Real.cos S * Real.cos (S - σ.θ₁)) / (Real.cos (S - σ.θ₂) * Real.cos (S - σ.θ₃)) *
        (-(Real.cos S * Real.cos (S - σ.θ₂)) / (Real.cos (S - σ.θ₁) * Real.cos (S - σ.θ₃))) =
          (Real.cos S / Real.cos (S - σ.θ₃)) ^ 2 := by
      field_simp
    rw [e, Real.sqrt_sq_eq_abs, abs_of_neg (div_neg_of_neg_of_pos hcS hc3)]
  set K := Real.sin σ.θ₃ / Real.cos (S - σ.θ₃) with hK
  have hK0 : 0 < K := div_pos (Real.sin_pos_of_pos_of_lt_pi h3 (by linarith)) hc3
  have hc3' : Real.cos (S - σ.θ₃) = Real.cos S * Real.cos σ.θ₃ + Real.sin S * Real.sin σ.θ₃ :=
    Real.cos_sub S σ.θ₃
  have key : 1 + σ.vertexTwo * σ.vertexOne = (K : ℂ) * exp (((S - Real.pi / 2 : ℝ) : ℂ) * I) := by
    rw [CompactShape.vertexTwo, CompactShape.vertexOne,
      show (1 : ℂ) + (σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁ : ℂ) * ((σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂ : ℂ) *
        exp ((σ.θ₃ : ℂ) * I)) = 1 + ((σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁ * σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂ : ℝ) :
          ℂ) * exp ((σ.θ₃ : ℂ) * I) by push_cast; ring, hprod]
    apply Complex.ext
    · simp only [add_re, one_re, re_ofReal_mul, exp_ofReal_mul_I_re]
      rw [Real.cos_sub_pi_div_two, hK]
      field_simp
      linear_combination hc3'
    · simp only [add_im, one_im, im_ofReal_mul, exp_ofReal_mul_I_im, zero_add]
      rw [Real.sin_sub_pi_div_two, hK]
      field_simp
  rw [key, arg_real_mul _ hK0, exp_mul_I,
    arg_cos_add_sin_mul_I ⟨by linarith, by linarith [Real.pi_pos]⟩]
  ring

end Excess

end Sph

end ClosedTriangle

end GC.Seifert
