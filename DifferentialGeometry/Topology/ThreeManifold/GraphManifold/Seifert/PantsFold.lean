import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldDomain
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The fold map of the ideal triangle onto the pants

Packet K16d, tier 2. On the ideal triangle `(0, 1/2, ∞)` of `Seifert/IdealTriangle.lean` the
cusp `i` is the vertex opposite `wall i`, with coordinate `cuspCoord i` (`-1/(4z - 2)`,
`-1/(4z)` and `-z̄`), height `cuspHeight i` (its imaginary part) and polar model
`cuspModel i`: `3/2 + r(Y) e^{2πiX}`, `-3/2 - r(Y) e^{2πiX}` and `-R(y) e^{-2πix}`, with
`r = holeRadius` decreasing to `1/2` and `R = outerRadius` increasing to `3`, the radii of the
holes and of the outer circle of `planarModel 3`. `foldCore` glues the three models with the
weights `foldWeight (cuspHeight i)` (a smooth step from height `3/10` to `6/10`); their sum is
positive on the triangle (`foldDenom_pos`), so `foldCore` is smooth near it
(`contDiffAt_foldCore`).

Each wall reflection acts on the two other cusp coordinates by `ζ ↦ n - ζ̄`
(`cuspCoord_wallReflection`), which conjugates their models and fixes their heights, while the
weight of the opposite cusp vanishes on `wallNbhd i`, a neighbourhood of `wall i`. Hence
`foldCore (σᵢ • z) = conj (foldCore z)` near `wall i` (`foldCore_wallReflection`), exactly, and
`foldCore` is real on the walls. The models have nonnegative imaginary part on the triangle and
positive imaginary part inside it (`cuspModel_im_nonneg`, `cuspModel_im_pos`), so the same holds
for `foldCore`.

`pantsFold z = κ(w) (foldCore (w • z))` for any `w` of the reflection group with `w • z` in the
triangle, `κ(w)` the identity or complex conjugation according to the sign of `det w`, is well
defined (`pantsFold_eq`), satisfies `pantsFold (σᵢ • z) = conj (pantsFold z)` and is invariant
under `pantsGroup` (`pantsFold_smul`). Near every point it is given by one such formula
(`pantsFold_eventuallyEq`; across a wall the reflected formula agrees by the exact symmetry),
so it is smooth (`contDiffOn_pantsFold`). If `foldCore` is injective on the triangle, two points
with the same value of `pantsFold` are in one `pantsGroup` orbit
(`exists_mem_pantsGroup_smul_eq_of_pantsFold_eq`): equal values with opposite signs of `κ` are
real, hence come from a wall, where the wall reflection corrects the sign.
-/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Matrix
open scoped MatrixGroups ComplexConjugate ContDiff Topology

namespace GC.Seifert

def outerRadius (t : ℝ) : ℝ := 3 / (1 + Real.exp Real.pi / 5 * Real.exp (-(2 * Real.pi * t)))

def holeRadius (t : ℝ) : ℝ := 1 / 2 + Real.exp Real.pi / 2 * Real.exp (-(2 * Real.pi * t))

def foldWeight (t : ℝ) : ℝ := Real.smoothTransition ((t - 3 / 10) / (3 / 10))

def polarModel (c s : ℝ) (ρ : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  c + s * ρ ζ.im * Complex.exp ((2 * Real.pi * ζ.re : ℝ) * Complex.I)

def cuspCoord : Fin 3 → ℂ → ℂ
  | 0 => fun z => -1 / (4 * z - 2)
  | 1 => fun z => -1 / (4 * z)
  | 2 => fun z => -conj z

def cuspCenter : Fin 3 → ℝ
  | 0 => 3 / 2
  | 1 => -(3 / 2)
  | 2 => 0

def cuspSign : Fin 3 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => -1

def cuspRadius : Fin 3 → ℝ → ℝ
  | 0 => holeRadius
  | 1 => holeRadius
  | 2 => outerRadius

def cuspModel (j : Fin 3) (z : ℂ) : ℂ :=
  polarModel (cuspCenter j) (cuspSign j) (cuspRadius j) (cuspCoord j z)

def cuspHeight (j : Fin 3) (z : ℂ) : ℝ := (cuspCoord j z).im

def foldDenom (z : ℂ) : ℝ := ∑ j, foldWeight (cuspHeight j z)

def foldNumer (z : ℂ) : ℂ := ∑ j, (foldWeight (cuspHeight j z) : ℂ) * cuspModel j z

def foldCore (z : ℂ) : ℂ := foldNumer z / foldDenom z

theorem foldWeight_eq_zero {t : ℝ} (ht : t ≤ 3 / 10) : foldWeight t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

theorem foldWeight_pos {t : ℝ} (ht : 3 / 10 < t) : 0 < foldWeight t :=
  Real.smoothTransition.pos_of_pos (div_pos (by linarith) (by norm_num))

theorem foldWeight_nonneg (t : ℝ) : 0 ≤ foldWeight t :=
  Real.smoothTransition.nonneg _

theorem polarModel_intCast_sub_conj (c s : ℝ) (ρ : ℝ → ℝ) (n : ℤ) (ζ : ℂ) :
    polarModel c s ρ (n - conj ζ) = conj (polarModel c s ρ ζ) := by
  simp only [polarModel, Complex.sub_re, Complex.intCast_re, Complex.conj_re, Complex.sub_im,
    Complex.intCast_im, Complex.conj_im, zero_sub, neg_neg, map_add, map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    show (((2 * Real.pi * (n - ζ.re) : ℝ)) : ℂ) * Complex.I =
      ((2 * Real.pi * ζ.re : ℝ) : ℂ) * -Complex.I + n * (2 * Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cuspCoord_zero_re (z : ℂ) :
    (cuspCoord 0 z).re = -(4 * z.re - 2) / ((4 * z.re - 2) ^ 2 + (4 * z.im) ^ 2) := by
  simp [cuspCoord, Complex.div_re, Complex.normSq_apply]
  ring

theorem cuspCoord_zero_im (z : ℂ) :
    (cuspCoord 0 z).im = 4 * z.im / ((4 * z.re - 2) ^ 2 + (4 * z.im) ^ 2) := by
  simp [cuspCoord, Complex.div_im, Complex.normSq_apply]
  ring

theorem cuspCoord_one_re (z : ℂ) :
    (cuspCoord 1 z).re = -(4 * z.re) / ((4 * z.re) ^ 2 + (4 * z.im) ^ 2) := by
  simp [cuspCoord, Complex.div_re, Complex.normSq_apply]
  ring

theorem cuspCoord_one_im (z : ℂ) :
    (cuspCoord 1 z).im = 4 * z.im / ((4 * z.re) ^ 2 + (4 * z.im) ^ 2) := by
  simp [cuspCoord, Complex.div_im, Complex.normSq_apply]
  ring

theorem cuspCoord_two_re (z : ℂ) : (cuspCoord 2 z).re = -z.re := by
  simp [cuspCoord]

theorem cuspCoord_two_im (z : ℂ) : (cuspCoord 2 z).im = z.im := by
  simp [cuspCoord]

private theorem coe_ne_zero' (z : ℍ) : (z : ℂ) ≠ 0 := z.ne_zero

private theorem conj_ne_zero' (z : ℍ) : conj (z : ℂ) ≠ 0 := by
  simpa using z.ne_zero

private theorem four_mul_sub_ne_zero (z : ℍ) (a : ℝ) : (4 : ℂ) * z - a ≠ 0 := by
  intro h
  have h1 : ((4 : ℂ) * z - a).im = 4 * z.im := by simp
  rw [h, Complex.zero_im] at h1
  exact z.im_ne_zero (by linarith)

private theorem four_mul_conj_sub_ne_zero (z : ℍ) (a : ℝ) : (4 : ℂ) * conj (z : ℂ) - a ≠ 0 := by
  intro h
  have h1 : ((4 : ℂ) * conj (z : ℂ) - a).im = -(4 * z.im) := by simp
  rw [h, Complex.zero_im] at h1
  exact z.im_ne_zero (by linarith)

theorem cuspCoord_one_wall_zero (z : ℍ) :
    cuspCoord 1 ((wallReflection 0 • z : ℍ) : ℂ) = ((0 : ℤ) : ℂ) - conj (cuspCoord 1 z) := by
  have hz := coe_ne_zero' z
  rw [coe_wallReflection_zero_smul]
  simp only [cuspCoord, Int.cast_zero, zero_sub, map_div₀, map_neg, map_one, map_mul,
    map_ofNat]
  field_simp

theorem cuspCoord_two_wall_zero (z : ℍ) :
    cuspCoord 2 ((wallReflection 0 • z : ℍ) : ℂ) = ((0 : ℤ) : ℂ) - conj (cuspCoord 2 z) := by
  rw [coe_wallReflection_zero_smul]
  simp [cuspCoord]

theorem cuspCoord_zero_wall_one (z : ℍ) :
    cuspCoord 0 ((wallReflection 1 • z : ℍ) : ℂ) = ((0 : ℤ) : ℂ) - conj (cuspCoord 0 z) := by
  have hc2 := four_mul_conj_sub_ne_zero z 2
  rw [coe_wallReflection_one_smul]
  simp only [cuspCoord, Int.cast_zero, zero_sub, map_div₀, map_neg, map_one, map_mul,
    map_ofNat, map_sub]
  have h' : (4 : ℂ) * (1 - conj (z : ℂ)) - 2 ≠ 0 := by
    rw [show (4 : ℂ) * (1 - conj (z : ℂ)) - 2 = -(4 * conj (z : ℂ) - 2) by ring]
    exact neg_ne_zero.2 (by exact_mod_cast hc2)
  have hc2' : (4 : ℂ) * conj (z : ℂ) - 2 ≠ 0 := by exact_mod_cast hc2
  field_simp
  ring

theorem cuspCoord_two_wall_one (z : ℍ) :
    cuspCoord 2 ((wallReflection 1 • z : ℍ) : ℂ) = ((-1 : ℤ) : ℂ) - conj (cuspCoord 2 z) := by
  rw [coe_wallReflection_one_smul]
  simp [cuspCoord]
  ring

theorem cuspCoord_zero_wall_two (z : ℍ) :
    cuspCoord 0 ((wallReflection 2 • z : ℍ) : ℂ) = ((1 : ℤ) : ℂ) - conj (cuspCoord 0 z) := by
  have hc1 : (4 : ℂ) * conj (z : ℂ) - 1 ≠ 0 := by exact_mod_cast four_mul_conj_sub_ne_zero z 1
  have hc2 : (4 : ℂ) * conj (z : ℂ) - 2 ≠ 0 := by exact_mod_cast four_mul_conj_sub_ne_zero z 2
  rw [coe_wallReflection_two_smul]
  simp only [cuspCoord, Int.cast_one, map_div₀, map_neg, map_one, map_mul, map_ofNat,
    map_sub]
  have h' : (4 : ℂ) * (conj (z : ℂ) / (4 * conj (z : ℂ) - 1)) - 2 =
      (2 - 4 * conj (z : ℂ)) / (4 * conj (z : ℂ) - 1) := by
    field_simp
    ring
  have h'' : (2 : ℂ) - 4 * conj (z : ℂ) ≠ 0 := by
    rw [show (2 : ℂ) - 4 * conj (z : ℂ) = -(4 * conj (z : ℂ) - 2) by ring]
    exact neg_ne_zero.2 hc2
  rw [h']
  field_simp
  ring

theorem cuspCoord_one_wall_two (z : ℍ) :
    cuspCoord 1 ((wallReflection 2 • z : ℍ) : ℂ) = ((-1 : ℤ) : ℂ) - conj (cuspCoord 1 z) := by
  have hc := conj_ne_zero' z
  have hc1 : (4 : ℂ) * conj (z : ℂ) - 1 ≠ 0 := by exact_mod_cast four_mul_conj_sub_ne_zero z 1
  rw [coe_wallReflection_two_smul]
  simp only [cuspCoord, Int.cast_neg, Int.cast_one, map_div₀, map_neg, map_one, map_mul,
    map_ofNat]
  field_simp
  ring

theorem cuspCoord_wallReflection {i j : Fin 3} (hij : i ≠ j) (z : ℍ) :
    ∃ n : ℤ, cuspCoord j ((wallReflection i • z : ℍ) : ℂ) = n - conj (cuspCoord j z) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact ⟨_, cuspCoord_one_wall_zero z⟩
    | exact ⟨_, cuspCoord_two_wall_zero z⟩
    | exact ⟨_, cuspCoord_zero_wall_one z⟩
    | exact ⟨_, cuspCoord_two_wall_one z⟩
    | exact ⟨_, cuspCoord_zero_wall_two z⟩
    | exact ⟨_, cuspCoord_one_wall_two z⟩

theorem cuspHeight_wallReflection {i j : Fin 3} (hij : i ≠ j) (z : ℍ) :
    cuspHeight j ((wallReflection i • z : ℍ) : ℂ) = cuspHeight j z := by
  obtain ⟨n, hn⟩ := cuspCoord_wallReflection hij z
  simp [cuspHeight, hn]

theorem cuspModel_wallReflection {i j : Fin 3} (hij : i ≠ j) (z : ℍ) :
    cuspModel j ((wallReflection i • z : ℍ) : ℂ) = conj (cuspModel j z) := by
  obtain ⟨n, hn⟩ := cuspCoord_wallReflection hij z
  rw [cuspModel, hn, polarModel_intCast_sub_conj]
  rfl

def wallNbhd (i : Fin 3) : Set ℍ :=
  {z | cuspHeight i z < 3 / 10 ∧ cuspHeight i ((wallReflection i • z : ℍ) : ℂ) < 3 / 10}

theorem foldWeight_wallReflection {i : Fin 3} {z : ℍ} (hz : z ∈ wallNbhd i) (j : Fin 3) :
    foldWeight (cuspHeight j ((wallReflection i • z : ℍ) : ℂ)) = foldWeight (cuspHeight j z) := by
  by_cases hij : i = j
  · subst hij
    rw [foldWeight_eq_zero hz.2.le, foldWeight_eq_zero hz.1.le]
  · rw [cuspHeight_wallReflection hij]

theorem foldTerm_wallReflection {i : Fin 3} {z : ℍ} (hz : z ∈ wallNbhd i) (j : Fin 3) :
    (foldWeight (cuspHeight j ((wallReflection i • z : ℍ) : ℂ)) : ℂ) *
        cuspModel j ((wallReflection i • z : ℍ) : ℂ) =
      conj ((foldWeight (cuspHeight j z) : ℂ) * cuspModel j z) := by
  by_cases hij : i = j
  · subst hij
    rw [foldWeight_eq_zero hz.2.le, foldWeight_eq_zero hz.1.le]
    simp
  · rw [cuspHeight_wallReflection hij, cuspModel_wallReflection hij, map_mul, Complex.conj_ofReal]

theorem foldCore_wallReflection {i : Fin 3} {z : ℍ} (hz : z ∈ wallNbhd i) :
    foldCore ((wallReflection i • z : ℍ) : ℂ) = conj (foldCore z) := by
  have hn : foldNumer ((wallReflection i • z : ℍ) : ℂ) = conj (foldNumer z) := by
    simp only [foldNumer, map_sum]
    exact Finset.sum_congr rfl fun j _ => foldTerm_wallReflection hz j
  have hd : foldDenom ((wallReflection i • z : ℍ) : ℂ) = foldDenom z := by
    simp only [foldDenom]
    exact Finset.sum_congr rfl fun j _ => foldWeight_wallReflection hz j
  rw [foldCore, foldCore, hn, hd, map_div₀, Complex.conj_ofReal]

theorem cuspHeight_le_of_mem_wall {i : Fin 3} {z : ℍ} (hz : z ∈ wall i) :
    cuspHeight i z ≤ 1 / 4 := by
  rw [mem_wall_iff] at hz
  have hy := z.im_pos
  fin_cases i
  · simp only [Fin.zero_eta, wallSide_zero] at hz
    simp only [Fin.zero_eta, cuspHeight, cuspCoord_zero_im, coe_re, coe_im, hz]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * z.im - 1)]
  · simp only [Fin.mk_one, wallSide_one] at hz
    simp only [Fin.mk_one, cuspHeight, cuspCoord_one_im, coe_re, coe_im]
    rw [show z.re = 1 / 2 by linarith, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * z.im - 1)]
  · simp only [Fin.reduceFinMk, wallSide_two] at hz
    simp only [Fin.reduceFinMk, cuspHeight, cuspCoord_two_im, coe_im]
    nlinarith [sq_nonneg (z.re - 1 / 4), sq_nonneg (z.im - 1 / 4)]

theorem mem_wallNbhd_of_mem_wall {i : Fin 3} {z : ℍ} (hz : z ∈ wall i) : z ∈ wallNbhd i := by
  have h := cuspHeight_le_of_mem_wall hz
  refine ⟨by linarith, ?_⟩
  rw [wallReflection_smul_of_mem_wall hz]
  linarith

theorem foldCore_conj_of_mem_wall {i : Fin 3} {z : ℍ} (hz : z ∈ wall i) :
    conj (foldCore z) = foldCore z := by
  have h := foldCore_wallReflection (mem_wallNbhd_of_mem_wall hz)
  rw [wallReflection_smul_of_mem_wall hz] at h
  exact h.symm

theorem exists_cuspHeight_gt {z : ℍ} (hz : z ∈ idealTriangle) : ∃ j, 3 / 10 < cuspHeight j z := by
  obtain ⟨h0, h1, h2⟩ := hz
  rw [quarter_le_norm_iff, wallSide_two] at h2
  have hy := z.im_pos
  by_cases hy3 : 3 / 10 < z.im
  · exact ⟨2, by simpa [cuspHeight, cuspCoord_two_im] using hy3⟩
  push Not at hy3
  by_cases hx : z.re ≤ 1 / 4
  · refine ⟨1, ?_⟩
    simp only [cuspHeight, cuspCoord_one_im, coe_re, coe_im]
    have hxy : z.re ^ 2 ≤ z.im ^ 2 := by nlinarith
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · refine ⟨0, ?_⟩
    simp only [cuspHeight, cuspCoord_zero_im, coe_re, coe_im]
    have hxy : (1 / 2 - z.re) ^ 2 ≤ z.im ^ 2 := by nlinarith
    rw [lt_div_iff₀ (by positivity)]
    nlinarith

theorem foldDenom_pos {z : ℍ} (hz : z ∈ idealTriangle) : 0 < foldDenom z := by
  obtain ⟨j, hj⟩ := exists_cuspHeight_gt hz
  exact lt_of_lt_of_le (foldWeight_pos hj)
    (Finset.single_le_sum (fun k _ => foldWeight_nonneg (cuspHeight k z)) (Finset.mem_univ j))

theorem contDiff_outerRadius : ContDiff ℝ ∞ outerRadius := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => 1 + Real.exp Real.pi / 5 * Real.exp (-(2 * Real.pi * t))) :=
    contDiff_const.add (contDiff_const.mul ((contDiff_const.mul contDiff_id).neg.exp))
  exact contDiff_const.div h fun t => by positivity

theorem contDiff_holeRadius : ContDiff ℝ ∞ holeRadius :=
  contDiff_const.add (contDiff_const.mul ((contDiff_const.mul contDiff_id).neg.exp))

theorem contDiff_foldWeight : ContDiff ℝ ∞ foldWeight :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem contDiff_polarModel (c s : ℝ) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (polarModel c s ρ) := by
  have him : ContDiff ℝ ∞ (fun ζ : ℂ => ((ρ ζ.im : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hρ.comp Complex.imCLM.contDiff)
  have hre : ContDiff ℝ ∞ (fun ζ : ℂ => (((2 * Real.pi * ζ.re : ℝ) : ℂ) * Complex.I)) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.reCLM.contDiff)).mul
      contDiff_const
  exact contDiff_const.add ((contDiff_const.mul him).mul (Complex.contDiff_exp.comp hre))

theorem contDiff_cuspRadius (j : Fin 3) : ContDiff ℝ ∞ (cuspRadius j) := by
  fin_cases j
  exacts [contDiff_holeRadius, contDiff_holeRadius, contDiff_outerRadius]

theorem contDiffAt_cuspCoord (j : Fin 3) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (cuspCoord j) z := by
  have h4 : (4 : ℂ) * z - 2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h0 : (4 : ℂ) * z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hc0 : ContDiffAt ℂ ∞ (fun u : ℂ => -1 / (4 * u - 2)) z :=
    ContDiffAt.div (f := fun _ => (-1 : ℂ)) (g := fun u : ℂ => 4 * u - 2) contDiffAt_const
      ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const) h4
  have hc1 : ContDiffAt ℂ ∞ (fun u : ℂ => -1 / (4 * u)) z :=
    ContDiffAt.div (f := fun _ => (-1 : ℂ)) (g := fun u : ℂ => 4 * u) contDiffAt_const
      (contDiffAt_const.mul contDiffAt_id) h0
  fin_cases j
  · exact hc0.restrict_scalars ℝ
  · exact hc1.restrict_scalars ℝ
  · exact Complex.conjCLE.contDiff.neg.contDiffAt

theorem contDiffAt_foldCore {z : ℂ} (hz : 0 < z.im) (hd : 0 < foldDenom z) :
    ContDiffAt ℝ ∞ foldCore z := by
  have hH (j : Fin 3) : ContDiffAt ℝ ∞ (fun u : ℂ => foldWeight (cuspHeight j u)) z :=
    contDiff_foldWeight.contDiffAt.comp z
      (Complex.imCLM.contDiff.contDiffAt.comp z (contDiffAt_cuspCoord j hz))
  have hM (j : Fin 3) : ContDiffAt ℝ ∞ (cuspModel j) z :=
    (contDiff_polarModel _ _ (contDiff_cuspRadius j)).contDiffAt.comp z (contDiffAt_cuspCoord j hz)
  have hN : ContDiffAt ℝ ∞ foldNumer z := by
    change ContDiffAt ℝ ∞ (fun u : ℂ => ∑ j, (foldWeight (cuspHeight j u) : ℂ) * cuspModel j u) z
    exact ContDiffAt.sum fun j _ =>
      (Complex.ofRealCLM.contDiff.contDiffAt.comp z (hH j)).mul (hM j)
  have hD : ContDiffAt ℝ ∞ (fun u : ℂ => ((foldDenom u : ℝ) : ℂ)) z := by
    have hS : ContDiffAt ℝ ∞ foldDenom z := ContDiffAt.sum fun j _ => hH j
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hS
  have hne : ((foldDenom z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  exact hN.mul (hD.inv hne)

def foldSign (w : GL (Fin 2) ℝ) (u : ℂ) : ℂ := if 0 < w.det.val then u else conj u

theorem foldSign_of_conj_eq (w : GL (Fin 2) ℝ) {u : ℂ} (hu : conj u = u) : foldSign w u = u := by
  unfold foldSign
  split_ifs
  · rfl
  · exact hu

theorem foldSign_conj (w : GL (Fin 2) ℝ) (u : ℂ) : foldSign w (conj u) = conj (foldSign w u) := by
  unfold foldSign
  split_ifs <;> rfl

theorem val_det_ne_zero (w : GL (Fin 2) ℝ) : w.det.val ≠ 0 :=
  w.det.ne_zero

theorem foldSign_mul_of_det_neg {w v : GL (Fin 2) ℝ} (hv : v.det.val < 0) (u : ℂ) :
    foldSign (w * v) u = conj (foldSign w u) := by
  have hw := val_det_ne_zero w
  unfold foldSign
  rw [map_mul, Units.val_mul]
  rcases hw.lt_or_gt with h | h
  · have h1 : 0 < w.det.val * v.det.val := mul_pos_of_neg_of_neg h hv
    have h2 : ¬ 0 < w.det.val := not_lt.2 h.le
    simp only [h1, h2, ↓reduceIte, Complex.conj_conj]
  · have h1 : ¬ 0 < w.det.val * v.det.val := not_lt.2 (mul_neg_of_pos_of_neg h hv).le
    simp only [h1, h, ↓reduceIte]

theorem foldSign_mul_of_det_pos {w v : GL (Fin 2) ℝ} (hv : 0 < v.det.val) (u : ℂ) :
    foldSign (w * v) u = foldSign w u := by
  have hw := val_det_ne_zero w
  unfold foldSign
  rw [map_mul, Units.val_mul]
  rcases hw.lt_or_gt with h | h
  · have h1 : ¬ 0 < w.det.val * v.det.val := not_lt.2 (mul_neg_of_neg_of_pos h hv).le
    have h2 : ¬ 0 < w.det.val := not_lt.2 h.le
    simp only [h1, h2, ↓reduceIte]
  · have h1 : 0 < w.det.val * v.det.val := mul_pos h hv
    simp only [h1, h, ↓reduceIte]

theorem foldSign_comm_mul_of_det_neg {w v : GL (Fin 2) ℝ} (hv : v.det.val < 0) (u : ℂ) :
    foldSign (v * w) u = conj (foldSign w u) := by
  unfold foldSign
  rw [map_mul, mul_comm, ← map_mul]
  exact foldSign_mul_of_det_neg hv u

theorem contDiff_foldSign (w : GL (Fin 2) ℝ) : ContDiff ℝ ∞ (foldSign w) := by
  by_cases h : 0 < w.det.val
  · have he : foldSign w = id := funext fun u => by simp only [foldSign, h, ↓reduceIte, id]
    rw [he]
    exact contDiff_id
  · have he : foldSign w = fun u => conj u := funext fun u => by
      simp only [foldSign, h, ↓reduceIte]
    rw [he]
    exact Complex.conjCLE.contDiff

def foldChoice (z : ℍ) : GL (Fin 2) ℝ :=
  (exists_smul_mem_idealTriangle z).choose

theorem foldChoice_mem (z : ℍ) : foldChoice z ∈ triangleGroup :=
  (exists_smul_mem_idealTriangle z).choose_spec.1

theorem foldChoice_smul_mem (z : ℍ) : foldChoice z • z ∈ idealTriangle :=
  (exists_smul_mem_idealTriangle z).choose_spec.2

def pantsFold (z : ℍ) : ℂ :=
  foldSign (foldChoice z) (foldCore ((foldChoice z • z : ℍ) : ℂ))

theorem pantsFold_eq {w : GL (Fin 2) ℝ} (hw : w ∈ triangleGroup) {z : ℍ}
    (hz : w • z ∈ idealTriangle) : pantsFold z = foldSign w (foldCore ((w • z : ℍ) : ℂ)) := by
  have h₀ := foldChoice_smul_mem z
  have hmem : w * (foldChoice z)⁻¹ ∈ triangleGroup := mul_mem hw (inv_mem (foldChoice_mem z))
  have hsm : (w * (foldChoice z)⁻¹) • (foldChoice z • z) = w • z := by
    rw [mul_smul, inv_smul_smul]
  obtain ⟨heq, hcase⟩ := smul_mem_idealTriangle hmem h₀ (hsm.symm ▸ hz)
  rw [hsm] at heq
  unfold pantsFold
  rw [heq]
  rcases hcase with h1 | ⟨i, hi, -⟩
  · rw [mul_inv_eq_one.mp h1]
  · have hreal := foldCore_conj_of_mem_wall hi
    rw [foldSign_of_conj_eq _ hreal, foldSign_of_conj_eq _ hreal]

theorem pantsFold_wallReflection_smul (i : Fin 3) (z : ℍ) :
    pantsFold (wallReflection i • z) = conj (pantsFold z) := by
  have hw : foldChoice z * wallReflection i ∈ triangleGroup :=
    mul_mem (foldChoice_mem z) (wallReflection_mem_triangleGroup i)
  have hsm : (foldChoice z * wallReflection i) • (wallReflection i • z) = foldChoice z • z := by
    rw [mul_smul, wallReflection_smul_smul]
  rw [pantsFold_eq hw (hsm.symm ▸ foldChoice_smul_mem z), hsm,
    foldSign_mul_of_det_neg (by rw [val_det_wallReflection]; norm_num)]
  rfl

theorem pantsFold_smul {γ : SL(2, ℤ)} (hγ : γ ∈ pantsGroup) (z : ℍ) :
    pantsFold (γ • z) = pantsFold z := by
  obtain ⟨w, hw, hdet, hγw⟩ := exists_triangleGroup_smul_eq hγ
  rw [hγw]
  have hw' : foldChoice z * w⁻¹ ∈ triangleGroup := mul_mem (foldChoice_mem z) (inv_mem hw)
  have hsm : (foldChoice z * w⁻¹) • (w • z) = foldChoice z • z := by
    rw [mul_smul, inv_smul_smul]
  rw [pantsFold_eq hw' (hsm.symm ▸ foldChoice_smul_mem z), hsm,
    foldSign_mul_of_det_pos (by rw [map_inv, hdet, inv_one, Units.val_one]; norm_num)]
  rfl

theorem continuous_wallSide (i : Fin 3) : Continuous (wallSide i) := by
  fin_cases i
  · exact (funext wallSide_zero).symm ▸ UpperHalfPlane.continuous_re
  · exact (funext wallSide_one).symm ▸ (continuous_const.sub UpperHalfPlane.continuous_re)
  · exact (funext wallSide_two).symm ▸ (((UpperHalfPlane.continuous_re.pow 2).add
      (UpperHalfPlane.continuous_im.pow 2)).sub (UpperHalfPlane.continuous_re.div_const 2))

theorem continuous_cuspHeight (j : Fin 3) : Continuous (fun z : ℍ => cuspHeight j z) := by
  have hre := UpperHalfPlane.continuous_re
  have him := UpperHalfPlane.continuous_im
  fin_cases j
  · have h : (fun z : ℍ => cuspHeight 0 z) =
        fun z : ℍ => 4 * z.im / ((4 * z.re - 2) ^ 2 + (4 * z.im) ^ 2) := by
      funext z
      simp only [cuspHeight, cuspCoord_zero_im, coe_re, coe_im]
    exact h ▸ (continuous_const.mul him).div (by fun_prop) fun z => by
      have := z.im_pos
      positivity
  · have h : (fun z : ℍ => cuspHeight 1 z) =
        fun z : ℍ => 4 * z.im / ((4 * z.re) ^ 2 + (4 * z.im) ^ 2) := by
      funext z
      simp only [cuspHeight, cuspCoord_one_im, coe_re, coe_im]
    exact h ▸ (continuous_const.mul him).div (by fun_prop) fun z => by
      have := z.im_pos
      positivity
  · have h : (fun z : ℍ => cuspHeight 2 z) = fun z : ℍ => z.im := by
      funext z
      simp only [cuspHeight, cuspCoord_two_im, coe_im]
    exact h ▸ him

theorem pantsFold_eventuallyEq (z₀ : ℍ) :
    ∀ᶠ z in 𝓝 z₀,
      pantsFold z = foldSign (foldChoice z₀) (foldCore ((foldChoice z₀ • z : ℍ) : ℂ)) := by
  have hw₀ := foldChoice_mem z₀
  have hζ₀ := foldChoice_smul_mem z₀
  have hc : Continuous (fun z : ℍ => foldChoice z₀ • z) := continuous_const_smul _
  by_cases hint : ∀ i, 0 < wallSide i (foldChoice z₀ • z₀)
  · have hev : ∀ᶠ z in 𝓝 z₀, ∀ i, 0 < wallSide i (foldChoice z₀ • z) := by
      rw [Filter.eventually_all]
      intro i
      exact ((continuous_wallSide i).comp hc).continuousAt.eventually (lt_mem_nhds (hint i))
    filter_upwards [hev] with z hz
    exact pantsFold_eq hw₀ ((mem_idealTriangle_iff _).2 fun i => (hz i).le)
  · push Not at hint
    obtain ⟨i, hi⟩ := hint
    have hi0 : wallSide i (foldChoice z₀ • z₀) = 0 :=
      le_antisymm hi ((mem_idealTriangle_iff _).1 hζ₀ i)
    have hwall : foldChoice z₀ • z₀ ∈ wall i := (mem_wall_iff i _).2 hi0
    have hother : ∀ j, j ≠ i → 0 < wallSide j (foldChoice z₀ • z₀) := fun j hj =>
      pos_wallSide_of_mem_idealTriangle hζ₀
        fun hj' => Set.disjoint_left.1 (wall_disjoint hj) hj' hwall
    have hfix : wallReflection i • foldChoice z₀ • z₀ = foldChoice z₀ • z₀ :=
      wallReflection_smul_of_mem_wall hwall
    have hnb := mem_wallNbhd_of_mem_wall hwall
    have hc2 : Continuous (fun z : ℍ => wallReflection i • foldChoice z₀ • z) :=
      (continuous_const_smul _).comp hc
    have e1 : ∀ᶠ z in 𝓝 z₀, ∀ j, j ≠ i → 0 < wallSide j (foldChoice z₀ • z) := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j = i
      · exact Filter.Eventually.of_forall fun z h => absurd hj h
      · exact (((continuous_wallSide j).comp hc).continuousAt.eventually
          (lt_mem_nhds (hother j hj))).mono fun z hz _ => hz
    have e2 : ∀ᶠ z in 𝓝 z₀, ∀ j, j ≠ i → 0 < wallSide j (wallReflection i • foldChoice z₀ • z) := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j = i
      · exact Filter.Eventually.of_forall fun z h => absurd hj h
      · have h0 : 0 < wallSide j (wallReflection i • foldChoice z₀ • z₀) := by
          rw [hfix]
          exact hother j hj
        exact (((continuous_wallSide j).comp hc2).continuousAt.eventually
          (lt_mem_nhds h0)).mono fun z hz _ => hz
    have e3 : ∀ᶠ z in 𝓝 z₀, foldChoice z₀ • z ∈ wallNbhd i := by
      have h1 := (((continuous_cuspHeight i).comp hc).continuousAt.eventually
        (gt_mem_nhds hnb.1))
      have h2 := (((continuous_cuspHeight i).comp hc2).continuousAt.eventually
        (gt_mem_nhds (by rw [Function.comp_apply, hfix]; exact hnb.1)))
      filter_upwards [h1, h2] with z hz1 hz2
      exact ⟨hz1, hz2⟩
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    by_cases hs : 0 ≤ wallSide i (foldChoice z₀ • z)
    · refine pantsFold_eq hw₀ ((mem_idealTriangle_iff _).2 fun j => ?_)
      by_cases hj : j = i
      · rw [hj]
        exact hs
      · exact (h1 j hj).le
    · push Not at hs
      have hmem : wallReflection i • foldChoice z₀ • z ∈ idealTriangle := by
        refine (mem_idealTriangle_iff _).2 fun j => ?_
        by_cases hj : j = i
        · rw [hj]
          exact ((wallSide_wallReflection_smul_pos_iff i _).2 hs).le
        · exact (h2 j hj).le
      have hw' : wallReflection i * foldChoice z₀ ∈ triangleGroup :=
        mul_mem (wallReflection_mem_triangleGroup i) hw₀
      rw [pantsFold_eq hw' (by rw [mul_smul]; exact hmem), mul_smul, foldCore_wallReflection h3,
        foldSign_comm_mul_of_det_neg (by rw [val_det_wallReflection]; norm_num), foldSign_conj,
        Complex.conj_conj]

theorem sigma_apply_eq_foldSign (g : GL (Fin 2) ℝ) (v : ℂ) : σ g v = foldSign g v := by
  unfold σ foldSign
  split_ifs <;> rfl

theorem contDiffAt_pantsFold_ofComplex {u : ℂ} (hu : 0 < u.im) :
    ContDiffAt ℝ ∞ (fun v : ℂ => pantsFold (ofComplex v)) u := by
  set z₀ : ℍ := ⟨u, hu⟩ with hz₀
  set w₀ := foldChoice z₀ with hw₀
  have hloc := pantsFold_eventuallyEq z₀
  have hnhds : 𝓝 u = Filter.map UpperHalfPlane.coe (𝓝 z₀) :=
    (isOpenEmbedding_coe.map_nhds_eq z₀).symm
  have h1 : ∀ᶠ v in 𝓝 u, pantsFold (ofComplex v) =
      foldSign w₀ (foldCore ((w₀ • ofComplex v : ℍ) : ℂ)) := by
    rw [hnhds, Filter.eventually_map]
    exact hloc.mono fun z hz => by rw [ofComplex_apply]; exact hz
  have hopen : ∀ᶠ v in 𝓝 u, 0 < v.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu
  have h2 : ∀ᶠ v in 𝓝 u, pantsFold (ofComplex v) =
      foldSign w₀ (foldCore (foldSign w₀ (num w₀ v / denom w₀ v))) := by
    filter_upwards [h1, hopen] with v hv hvim
    rw [hv, ofComplex_apply_of_im_pos hvim, coe_smul, sigma_apply_eq_foldSign]
  have hden : denom w₀ u ≠ 0 := denom_ne_zero_of_im w₀ hu.ne'
  have hq : ContDiffAt ℂ ∞ (fun v : ℂ => num w₀ v / denom w₀ v) u :=
    ContDiffAt.div (f := fun v : ℂ => (w₀ 0 0 : ℂ) * v + w₀ 0 1)
      (g := fun v : ℂ => (w₀ 1 0 : ℂ) * v + w₀ 1 1)
      ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
      ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) hden
  have hpt : foldSign w₀ (num w₀ u / denom w₀ u) = ((w₀ • z₀ : ℍ) : ℂ) := by
    rw [coe_smul, sigma_apply_eq_foldSign]
  have hζ := foldChoice_smul_mem z₀
  have hcore : ContDiffAt ℝ ∞ foldCore (foldSign w₀ (num w₀ u / denom w₀ u)) := by
    rw [hpt]
    exact contDiffAt_foldCore (w₀ • z₀).im_pos (foldDenom_pos hζ)
  have hinner : ContDiffAt ℝ ∞ (fun v : ℂ => foldSign w₀ (num w₀ v / denom w₀ v)) u :=
    (contDiff_foldSign w₀).contDiffAt.comp u (hq.restrict_scalars ℝ)
  have hmid : ContDiffAt ℝ ∞ (fun v : ℂ => foldCore (foldSign w₀ (num w₀ v / denom w₀ v))) u :=
    ContDiffAt.comp (g := foldCore) u hcore hinner
  have hG : ContDiffAt ℝ ∞
      (fun v : ℂ => foldSign w₀ (foldCore (foldSign w₀ (num w₀ v / denom w₀ v)))) u :=
    ContDiffAt.comp (g := foldSign w₀) u (contDiff_foldSign w₀).contDiffAt hmid
  exact hG.congr_of_eventuallyEq h2

theorem contDiffOn_pantsFold :
    ContDiffOn ℝ ∞ (fun v : ℂ => pantsFold (ofComplex v)) {v | 0 < v.im} := fun _ hu =>
  (contDiffAt_pantsFold_ofComplex hu).contDiffWithinAt

theorem foldSign_of_det_pos {w : GL (Fin 2) ℝ} (h : 0 < w.det.val) (u : ℂ) : foldSign w u = u := by
  simp only [foldSign, h, ↓reduceIte]

theorem foldSign_of_det_neg {w : GL (Fin 2) ℝ} (h : w.det.val < 0) (u : ℂ) :
    foldSign w u = conj u := by
  simp only [foldSign, not_lt.2 h.le, ↓reduceIte]

theorem polarModel_im (c s : ℝ) (ρ : ℝ → ℝ) (ζ : ℂ) :
    (polarModel c s ρ ζ).im = s * ρ ζ.im * Real.sin (2 * Real.pi * ζ.re) := by
  have he : (Complex.exp (((2 * Real.pi * ζ.re : ℝ) : ℂ) * Complex.I)).im =
      Real.sin (2 * Real.pi * ζ.re) := Complex.exp_ofReal_mul_I_im _
  simp only [polarModel, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, he,
    Complex.ofReal_re, Complex.mul_re, mul_zero, zero_mul, sub_zero, add_zero]

theorem holeRadius_pos (t : ℝ) : 0 < holeRadius t := by
  unfold holeRadius
  positivity

theorem outerRadius_pos (t : ℝ) : 0 < outerRadius t := by
  unfold outerRadius
  positivity

theorem cuspRadius_pos (j : Fin 3) (t : ℝ) : 0 < cuspRadius j t := by
  fin_cases j
  exacts [holeRadius_pos t, holeRadius_pos t, outerRadius_pos t]

theorem sin_two_pi_mul_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    0 ≤ Real.sin (2 * Real.pi * t) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])

theorem sin_two_pi_mul_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    0 < Real.sin (2 * Real.pi * t) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])

theorem sin_two_pi_mul_nonpos {t : ℝ} (h0 : t ≤ 0) (h1 : -(1 / 2) ≤ t) :
    Real.sin (2 * Real.pi * t) ≤ 0 :=
  Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

theorem sin_two_pi_mul_neg {t : ℝ} (h0 : t < 0) (h1 : -(1 / 2) < t) :
    Real.sin (2 * Real.pi * t) < 0 := by
  have h := sin_two_pi_mul_pos (t := -t) (by linarith) (by linarith)
  rw [mul_neg, Real.sin_neg] at h
  linarith

theorem cuspModel_im_nonneg {z : ℍ} (hz : z ∈ idealTriangle) (j : Fin 3) :
    0 ≤ (cuspModel j z).im := by
  obtain ⟨h0, h1, h2⟩ := hz
  rw [quarter_le_norm_iff, wallSide_two] at h2
  have hy := z.im_pos
  have hr := cuspRadius_pos j (cuspCoord j z).im
  rw [cuspModel, polarModel_im]
  fin_cases j
  · simp only [Fin.zero_eta, cuspSign, cuspCoord_zero_re, coe_re, coe_im, one_mul] at hr ⊢
    have hD : 0 < (4 * z.re - 2) ^ 2 + (4 * z.im) ^ 2 := by positivity
    refine mul_nonneg hr.le (sin_two_pi_mul_nonneg (div_nonneg (by linarith) hD.le) ?_)
    rw [div_le_iff₀ hD]
    nlinarith
  · simp only [Fin.mk_one, cuspSign, cuspCoord_one_re, coe_re, coe_im] at hr ⊢
    have hD : 0 < (4 * z.re) ^ 2 + (4 * z.im) ^ 2 := by positivity
    have hs := sin_two_pi_mul_nonpos (t := -(4 * z.re) / ((4 * z.re) ^ 2 + (4 * z.im) ^ 2))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le)
      (by rw [le_div_iff₀ hD]; nlinarith)
    nlinarith
  · simp only [Fin.reduceFinMk, cuspSign, cuspCoord_two_re, coe_re] at hr ⊢
    have hs := sin_two_pi_mul_nonpos (t := -z.re) (by linarith) (by linarith)
    nlinarith

theorem cuspModel_im_pos {z : ℍ} (hz : ∀ i, 0 < wallSide i z) (j : Fin 3) :
    0 < (cuspModel j z).im := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  rw [wallSide_zero] at h0
  rw [wallSide_one] at h1
  rw [wallSide_two] at h2
  have hy := z.im_pos
  have hr := cuspRadius_pos j (cuspCoord j z).im
  rw [cuspModel, polarModel_im]
  fin_cases j
  · simp only [Fin.zero_eta, cuspSign, cuspCoord_zero_re, coe_re, coe_im, one_mul] at hr ⊢
    have hD : 0 < (4 * z.re - 2) ^ 2 + (4 * z.im) ^ 2 := by positivity
    refine mul_pos hr (sin_two_pi_mul_pos (div_pos (by linarith) hD) ?_)
    rw [div_lt_iff₀ hD]
    nlinarith
  · simp only [Fin.mk_one, cuspSign, cuspCoord_one_re, coe_re, coe_im] at hr ⊢
    have hD : 0 < (4 * z.re) ^ 2 + (4 * z.im) ^ 2 := by positivity
    have hs := sin_two_pi_mul_neg (t := -(4 * z.re) / ((4 * z.re) ^ 2 + (4 * z.im) ^ 2))
      (div_neg_of_neg_of_pos (by linarith) hD)
      (by rw [lt_div_iff₀ hD]; nlinarith)
    nlinarith
  · simp only [Fin.reduceFinMk, cuspSign, cuspCoord_two_re, coe_re] at hr ⊢
    have hs := sin_two_pi_mul_neg (t := -z.re) (by linarith) (by linarith)
    nlinarith

theorem foldCore_im (z : ℂ) :
    (foldCore z).im = (∑ j, foldWeight (cuspHeight j z) * (cuspModel j z).im) / foldDenom z := by
  rw [foldCore, Complex.div_ofReal_im, foldNumer, Complex.im_sum]
  simp [Complex.mul_im]

theorem foldCore_im_nonneg {z : ℍ} (hz : z ∈ idealTriangle) : 0 ≤ (foldCore z).im := by
  rw [foldCore_im]
  exact div_nonneg (Finset.sum_nonneg fun j _ =>
    mul_nonneg (foldWeight_nonneg _) (cuspModel_im_nonneg hz j)) (foldDenom_pos hz).le

theorem foldCore_im_pos {z : ℍ} (hz : ∀ i, 0 < wallSide i z) : 0 < (foldCore z).im := by
  have hz' : z ∈ idealTriangle := (mem_idealTriangle_iff z).2 fun i => (hz i).le
  obtain ⟨j, hj⟩ := exists_cuspHeight_gt hz'
  rw [foldCore_im]
  refine div_pos (Finset.sum_pos' (fun k _ =>
    mul_nonneg (foldWeight_nonneg _) (cuspModel_im_nonneg hz' k)) ⟨j, Finset.mem_univ j,
      mul_pos (foldWeight_pos hj) (cuspModel_im_pos hz j)⟩) (foldDenom_pos hz')

theorem exists_mem_wall_of_foldCore_im_eq_zero {z : ℍ} (hz : z ∈ idealTriangle)
    (h : (foldCore z).im = 0) : ∃ i, z ∈ wall i := by
  by_contra hcon
  push Not at hcon
  exact (foldCore_im_pos fun i => pos_wallSide_of_mem_idealTriangle hz (hcon i)).ne' h

theorem pantsFold_of_mem_idealTriangle {z : ℍ} (hz : z ∈ idealTriangle) :
    pantsFold z = foldCore z := by
  rw [pantsFold_eq (one_mem _) (by rw [one_smul]; exact hz), one_smul,
    foldSign_of_det_pos (by simp)]

theorem exists_mem_pantsGroup_smul_eq_of_pantsFold_eq
    (hinj : Set.InjOn (fun z : ℍ => foldCore z) idealTriangle) {z z' : ℍ}
    (h : pantsFold z = pantsFold z') : ∃ γ ∈ pantsGroup, γ • z = z' := by
  have hw := foldChoice_mem z
  have hw' := foldChoice_mem z'
  have hζ := foldChoice_smul_mem z
  have hζ' := foldChoice_smul_mem z'
  suffices hv : ∃ v ∈ triangleGroup, v.det = 1 ∧ v • z = z' by
    obtain ⟨v, hv, hdet, hvz⟩ := hv
    obtain ⟨γ, hγ, hγv⟩ := exists_pantsGroup_smul_eq hv hdet
    exact ⟨γ, hγ, by rw [← hγv, hvz]⟩
  have hi := foldCore_im_nonneg hζ
  have hi' := foldCore_im_nonneg hζ'
  unfold pantsFold at h
  have hdirect (heq : foldChoice z • z = foldChoice z' • z')
      (hd : (foldChoice z).det.val = (foldChoice z').det.val) :
      ∃ v ∈ triangleGroup, v.det = 1 ∧ v • z = z' := by
    refine ⟨(foldChoice z')⁻¹ * foldChoice z, mul_mem (inv_mem hw') hw, ?_, ?_⟩
    · refine Units.val_eq_one.mp ?_
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hd,
        inv_mul_cancel₀ (val_det_ne_zero _)]
    · rw [mul_smul, heq, inv_smul_smul]
  have hwall (heq : foldChoice z • z = foldChoice z' • z') (i : Fin 3)
      (hiw : foldChoice z • z ∈ wall i)
      (hd : (foldChoice z).det.val = -(foldChoice z').det.val) :
      ∃ v ∈ triangleGroup, v.det = 1 ∧ v • z = z' := by
    refine ⟨(foldChoice z')⁻¹ * wallReflection i * foldChoice z,
      mul_mem (mul_mem (inv_mem hw') (wallReflection_mem_triangleGroup i)) hw, ?_, ?_⟩
    · refine Units.val_eq_one.mp ?_
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
        val_det_wallReflection, hd]
      have := val_det_ne_zero (foldChoice z')
      field_simp
    · rw [mul_smul, mul_smul, wallReflection_smul_of_mem_wall hiw, heq, inv_smul_smul]
  rcases val_det_eq_one_or_of_mem_triangleGroup hw with hd | hd <;>
    rcases val_det_eq_one_or_of_mem_triangleGroup hw' with hd' | hd'
  · rw [foldSign_of_det_pos (by rw [hd]; norm_num), foldSign_of_det_pos (by rw [hd']; norm_num)]
      at h
    exact hdirect (hinj hζ hζ' h) (by rw [hd, hd'])
  · rw [foldSign_of_det_pos (by rw [hd]; norm_num), foldSign_of_det_neg (by rw [hd']; norm_num)]
      at h
    have him : (foldCore ((foldChoice z' • z' : ℍ) : ℂ)).im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    have hreal : conj (foldCore ((foldChoice z' • z' : ℍ) : ℂ)) =
        foldCore ((foldChoice z' • z' : ℍ) : ℂ) := Complex.conj_eq_iff_im.2 him
    rw [hreal] at h
    have heq := hinj hζ hζ' h
    obtain ⟨i, hiw⟩ := exists_mem_wall_of_foldCore_im_eq_zero hζ (by
      have := congrArg Complex.im h
      rw [him] at this
      exact this)
    exact hwall heq i hiw (by linarith)
  · rw [foldSign_of_det_neg (by rw [hd]; norm_num), foldSign_of_det_pos (by rw [hd']; norm_num)]
      at h
    have him : (foldCore ((foldChoice z • z : ℍ) : ℂ)).im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    have hreal : conj (foldCore ((foldChoice z • z : ℍ) : ℂ)) =
        foldCore ((foldChoice z • z : ℍ) : ℂ) := Complex.conj_eq_iff_im.2 him
    rw [hreal] at h
    have heq := hinj hζ hζ' h
    obtain ⟨i, hiw⟩ := exists_mem_wall_of_foldCore_im_eq_zero hζ him
    exact hwall heq i hiw (by linarith)
  · rw [foldSign_of_det_neg (by rw [hd]; norm_num), foldSign_of_det_neg (by rw [hd']; norm_num)]
      at h
    exact hdirect (hinj hζ hζ' ((starRingEnd ℂ).injective h)) (by rw [hd, hd'])

end GC.Seifert
