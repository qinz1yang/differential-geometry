import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGenericWalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypTriangle

/-!
# The vertex discs of a hyperbolic closed triangle fold

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatDiscs`). For a hyperbolic `CompactShape`
`σ` (the Poincaré disc, `v₃ = 0`, `v₂ = t₂ > 0`, `v₁ = t₁ e^{iθ₃}`) and a fold datum `D`, the
margin `μ = min (t₁ sin θ₃, t₂ sin θ₃, t₂ sin θ₂)` bounds the side functions of the walls
opposite the vertices from below at the vertices, and the radii `radOne`, `radTwo`, `radThree`
are at most `ρ₀ = μ/8`, the apex radii of `D` and `1/2`. The vertex discs are hyperbolic discs in
CF's Möbius coordinates, `discOne = {‖rotOne z‖ < radOne}`, `discTwo = {‖rotTwo z‖ < radTwo}`
inside the unit disc, `discThree = {‖z‖ < radThree}`, and `discOneMirror = conj discOne`.
On the unit disc `‖z - v‖ ≤ 2 ‖disc v z‖` (`norm_sub_le_two_mul_mob`), so the discs lie in
Euclidean discs of radius `2ρ₀`; the side functions `w₀`, `w₁` are `1`-Lipschitz and `w₂` is
`5`-Lipschitz on the unit disc, which gives the margins `3ρ₀ < wⱼ` of the walls opposite the
centres (`im_pos_of_mem_discOne`, `wallSide_one_of_mem_discTwo`, `wallSide_two_of_mem_discThree`)
and the pairwise disjointness of the four discs (`disjoint_*`). The apex germs of `D` hold on the
discs (`f_of_mem_discOne`, `f_of_mem_discTwo`, `f_of_mem_discThree`).
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

variable {σ : CompactShape} (D : σ.FoldData)

section Constants

variable (σ) in
def hypMu : ℝ := min (σ.sideTanOne * Real.sin σ.θ₃)
  (min (σ.sideTanTwo * Real.sin σ.θ₃) (σ.sideTanTwo * Real.sin σ.θ₂))

variable (σ) in
def rhoZero : ℝ := hypMu σ / 8

def radOne : ℝ := min (min (rhoZero σ) (D.apexRadius 0)) (1 / 2)

def radTwo : ℝ := min (min (rhoZero σ) (D.apexRadius 1)) (1 / 2)

def radThree : ℝ := min (min (rhoZero σ) (D.apexRadius 2)) (1 / 2)

omit D in
theorem hypMu_pos : 0 < hypMu σ := by
  have := σ.sideTanOne_pos
  have := σ.sideTanTwo_pos
  have := σ.sin_θ₁_pos
  have := σ.sin_θ₂_pos
  have := σ.sin_θ₃_pos
  unfold hypMu
  refine lt_min (by positivity) (lt_min (by positivity) (by positivity))

omit D in
theorem rhoZero_pos : 0 < rhoZero σ := by unfold rhoZero; linarith [hypMu_pos (σ := σ)]

omit D in
theorem hypMu_le_one : hypMu σ ≤ σ.sideTanOne * Real.sin σ.θ₃ := min_le_left _ _

omit D in
theorem hypMu_le_two : hypMu σ ≤ σ.sideTanTwo * Real.sin σ.θ₃ :=
  (min_le_right _ _).trans (min_le_left _ _)

omit D in
theorem hypMu_le_three : hypMu σ ≤ σ.sideTanTwo * Real.sin σ.θ₂ :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem radOne_pos : 0 < radOne D :=
  lt_min (lt_min rhoZero_pos (D.apexRadius_pos 0)) (by norm_num)

theorem radTwo_pos : 0 < radTwo D :=
  lt_min (lt_min rhoZero_pos (D.apexRadius_pos 1)) (by norm_num)

theorem radThree_pos : 0 < radThree D :=
  lt_min (lt_min rhoZero_pos (D.apexRadius_pos 2)) (by norm_num)

theorem radOne_le_rhoZero : radOne D ≤ rhoZero σ := (min_le_left _ _).trans (min_le_left _ _)

theorem radTwo_le_rhoZero : radTwo D ≤ rhoZero σ := (min_le_left _ _).trans (min_le_left _ _)

theorem radThree_le_rhoZero : radThree D ≤ rhoZero σ :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem radOne_le_apex : radOne D ≤ D.apexRadius 0 := (min_le_left _ _).trans (min_le_right _ _)

theorem radTwo_le_apex : radTwo D ≤ D.apexRadius 1 := (min_le_left _ _).trans (min_le_right _ _)

theorem radThree_le_apex : radThree D ≤ D.apexRadius 2 :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem radOne_le_half : radOne D ≤ 1 / 2 := min_le_right _ _

theorem radTwo_le_half : radTwo D ≤ 1 / 2 := min_le_right _ _

theorem radThree_le_half : radThree D ≤ 1 / 2 := min_le_right _ _

end Constants

section Discs

def discOne : Set ℂ := {z | ‖z‖ < 1 ∧ ‖σ.rotOne z‖ < radOne D}

def discTwo : Set ℂ := {z | ‖z‖ < 1 ∧ ‖σ.rotTwo z‖ < radTwo D}

def discThree : Set ℂ := {z | ‖z‖ < radThree D}

def discOneMirror : Set ℂ := {z | conj z ∈ discOne D}

theorem mem_discOneMirror_iff {z : ℂ} : z ∈ discOneMirror D ↔ conj z ∈ discOne D := Iff.rfl

theorem norm_lt_one_of_mem_discThree {z : ℂ} (hz : z ∈ discThree D) : ‖z‖ < 1 :=
  hz.trans_le ((radThree_le_half D).trans (by norm_num))

theorem norm_sub_le_two_mul_mob {v z : ℂ} (hv : ‖v‖ < 1) (hz : ‖z‖ < 1) :
    ‖z - v‖ ≤ 2 * ‖HypFold.mob v z‖ := by
  have hd := HypFold.one_sub_conj_mul_ne_zero hv hz
  have e : z - v = HypFold.mob v z * (1 - conj v * z) := by
    rw [HypFold.mob, div_mul_cancel₀ _ hd]
  have hb : ‖1 - conj v * z‖ ≤ 2 := by
    calc ‖1 - conj v * z‖ ≤ ‖(1 : ℂ)‖ + ‖conj v * z‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg v, norm_nonneg z]
  rw [e, norm_mul]
  nlinarith [norm_nonneg (HypFold.mob v z)]

variable {D}
variable (hσ : σ.curv = .hyperbolic)
include hσ

theorem norm_sub_vertexOne_lt {z : ℂ} (hz : z ∈ discOne D) :
    ‖z - σ.vertexOne‖ < 2 * radOne D := by
  have h := norm_sub_le_two_mul_mob (HypFold.norm_vertexOne_lt_one hσ) hz.1
  rw [← HypFold.norm_rotOne hσ] at h
  linarith [hz.2]

theorem norm_sub_vertexTwo_lt {z : ℂ} (hz : z ∈ discTwo D) :
    ‖z - σ.vertexTwo‖ < 2 * radTwo D := by
  have h := norm_sub_le_two_mul_mob (HypFold.norm_vertexTwo_lt_one hσ) hz.1
  rw [← HypFold.norm_rotTwo hσ] at h
  linarith [hz.2]

omit hσ in
theorem abs_wallSide_zero_sub_le (z w : ℂ) : |σ.wallSide 0 z - σ.wallSide 0 w| ≤ ‖z - w‖ := by
  change |z.im - w.im| ≤ _
  rw [← sub_im]
  exact abs_im_le_norm _

omit hσ in
theorem abs_wallSide_one_sub_le (z w : ℂ) : |σ.wallSide 1 z - σ.wallSide 1 w| ≤ ‖z - w‖ := by
  change |(exp ((σ.θ₃ : ℂ) * I) * conj z).im - (exp ((σ.θ₃ : ℂ) * I) * conj w).im| ≤ _
  rw [← sub_im, ← mul_sub, ← map_sub]
  refine (abs_im_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]

theorem abs_wallSide_two_sub_le {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    |σ.wallSide 2 z - σ.wallSide 2 w| ≤ 5 * ‖z - w‖ := by
  rw [σ.wallSide_two_eq_poly, σ.wallSide_two_eq_poly, CompactShape.eps_of_hyp σ hσ]
  have ht0 := σ.sideTanTwo_pos
  have ht1 : σ.sideTanTwo < 1 := by
    have := σ.eps_sideTanTwo_sq_lt
    rw [CompactShape.eps_of_hyp σ hσ, one_mul] at this
    nlinarith
  have hs := Real.sin_le_one σ.θ₂
  have hs0 := σ.sin_θ₂_pos
  have hc := Real.cos_le_one σ.θ₂
  have hc0 := σ.cos_θ₂_nonneg
  have hre := abs_re_le_norm (z - w)
  have him := abs_im_le_norm (z - w)
  rw [sub_re] at hre
  rw [sub_im] at him
  have hzr := abs_re_le_norm z
  have hzi := abs_im_le_norm z
  have hwr := abs_re_le_norm w
  have hwi := abs_im_le_norm w
  have hsq : |(z.re ^ 2 + z.im ^ 2) - (w.re ^ 2 + w.im ^ 2)| ≤ 2 * ‖z - w‖ := by
    have e1 : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, normSq_apply]; ring
    have e2 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, normSq_apply]; ring
    rw [e1, e2, sq_sub_sq]
    have := abs_norm_sub_norm_le z w
    rw [abs_mul]
    have h3 : |‖z‖ + ‖w‖| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]; linarith
    nlinarith [abs_nonneg (‖z‖ - ‖w‖), abs_nonneg (‖z‖ + ‖w‖)]
  have key : σ.wallSide 2 z - σ.wallSide 2 w =
      Real.sin σ.θ₂ * σ.sideTanTwo * ((z.re ^ 2 + z.im ^ 2) - (w.re ^ 2 + w.im ^ 2)) -
        Real.sin σ.θ₂ * (1 + σ.sideTanTwo ^ 2) * (z.re - w.re) -
        Real.cos σ.θ₂ * (1 - σ.sideTanTwo ^ 2) * (z.im - w.im) := by
    rw [σ.wallSide_two_eq_poly, σ.wallSide_two_eq_poly, CompactShape.eps_of_hyp σ hσ]
    ring
  rw [σ.wallSide_two_eq_poly, σ.wallSide_two_eq_poly, CompactShape.eps_of_hyp σ hσ] at key
  rw [key]
  have a1 : |Real.sin σ.θ₂ * σ.sideTanTwo * ((z.re ^ 2 + z.im ^ 2) - (w.re ^ 2 + w.im ^ 2))| ≤
      2 * ‖z - w‖ := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have : Real.sin σ.θ₂ * σ.sideTanTwo ≤ 1 := by nlinarith
    nlinarith [abs_nonneg ((z.re ^ 2 + z.im ^ 2) - (w.re ^ 2 + w.im ^ 2)), norm_nonneg (z - w)]
  have a2 : |Real.sin σ.θ₂ * (1 + σ.sideTanTwo ^ 2) * (z.re - w.re)| ≤ 2 * ‖z - w‖ := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have : Real.sin σ.θ₂ * (1 + σ.sideTanTwo ^ 2) ≤ 2 := by nlinarith
    nlinarith [abs_nonneg (z.re - w.re), norm_nonneg (z - w)]
  have a3 : |Real.cos σ.θ₂ * (1 - σ.sideTanTwo ^ 2) * (z.im - w.im)| ≤ ‖z - w‖ := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hc0 (by nlinarith))]
    have : Real.cos σ.θ₂ * (1 - σ.sideTanTwo ^ 2) ≤ 1 := by nlinarith
    nlinarith [abs_nonneg (z.im - w.im), norm_nonneg (z - w)]
  have := abs_sub (Real.sin σ.θ₂ * σ.sideTanTwo * ((z.re ^ 2 + z.im ^ 2) - (w.re ^ 2 + w.im ^ 2)) -
    Real.sin σ.θ₂ * (1 + σ.sideTanTwo ^ 2) * (z.re - w.re))
    (Real.cos σ.θ₂ * (1 - σ.sideTanTwo ^ 2) * (z.im - w.im))
  have := abs_sub (Real.sin σ.θ₂ * σ.sideTanTwo * ((z.re ^ 2 + z.im ^ 2) - (w.re ^ 2 + w.im ^ 2)))
    (Real.sin σ.θ₂ * (1 + σ.sideTanTwo ^ 2) * (z.re - w.re))
  linarith

theorem continuousOn_rotOne : ContinuousOn σ.rotOne (Metric.ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  have hm :=
    (HypFold.contDiffAt_mob (HypFold.one_sub_conj_vertexOne_mul_ne_zero hσ hz)).continuousAt
  have e : σ.rotOne = fun z => -exp (-((σ.θ₃ : ℂ) * I)) * HypFold.mob σ.vertexOne z :=
    funext (HypFold.rotOne_eq_mul_mob hσ)
  rw [e]
  exact (continuousAt_const.mul hm).continuousWithinAt

theorem continuousOn_rotTwo : ContinuousOn σ.rotTwo (Metric.ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  have hne : 1 - conj σ.vertexTwo * z ≠ 0 := by
    rw [HypFold.conj_vertexTwo (σ := σ)]; exact HypFold.one_sub_vertexTwo_mul_ne_zero hσ hz
  have hm := (HypFold.contDiffAt_mob hne).continuousAt
  have e : σ.rotTwo = fun z => -exp ((σ.θ₂ : ℂ) * I) * HypFold.mob σ.vertexTwo z :=
    funext (HypFold.rotTwo_eq_mul_mob hσ)
  rw [e]
  exact (continuousAt_const.mul hm).continuousWithinAt

theorem isOpen_discOne : IsOpen (discOne D) := by
  have e : discOne D = Metric.ball 0 1 ∩ σ.rotOne ⁻¹' Metric.ball 0 (radOne D) := by
    ext z; simp [discOne]
  rw [e]
  exact (continuousOn_rotOne hσ).isOpen_inter_preimage Metric.isOpen_ball Metric.isOpen_ball

theorem isOpen_discTwo : IsOpen (discTwo D) := by
  have e : discTwo D = Metric.ball 0 1 ∩ σ.rotTwo ⁻¹' Metric.ball 0 (radTwo D) := by
    ext z; simp [discTwo]
  rw [e]
  exact (continuousOn_rotTwo hσ).isOpen_inter_preimage Metric.isOpen_ball Metric.isOpen_ball

omit hσ in
theorem isOpen_discThree : IsOpen (discThree D) := isOpen_lt continuous_norm continuous_const

theorem isOpen_discOneMirror : IsOpen (discOneMirror D) :=
  (isOpen_discOne hσ).preimage continuous_conj

omit hσ in
theorem vertexOne_im : σ.vertexOne.im = σ.sideTanOne * Real.sin σ.θ₃ := by
  rw [σ.vertexOne_eq_ray, σ.ray_im]

omit hσ in
theorem rhoZero_eq : 8 * rhoZero σ = hypMu σ := by unfold rhoZero; ring

theorem im_pos_of_mem_discOne {z : ℂ} (hz : z ∈ discOne D) : 3 * rhoZero σ < z.im := by
  have h := abs_im_le_norm (z - σ.vertexOne)
  rw [sub_im, vertexOne_im] at h
  have h2 := norm_sub_vertexOne_lt hσ hz
  have hr := radOne_le_rhoZero D
  have hm := hypMu_le_one (σ := σ)
  have := rhoZero_eq (σ := σ)
  have := abs_lt.mp (h.trans_lt h2)
  linarith [this.1, rhoZero_pos (σ := σ)]

theorem im_neg_of_mem_discOneMirror {z : ℂ} (hz : z ∈ discOneMirror D) :
    z.im < -(3 * rhoZero σ) := by
  have h := im_pos_of_mem_discOne hσ hz
  rw [conj_im] at h
  linarith

theorem wallSide_one_of_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D) :
    3 * rhoZero σ < σ.wallSide 1 z := by
  have h := abs_wallSide_one_sub_le (σ := σ) z σ.vertexTwo
  have hv : σ.wallSide 1 σ.vertexTwo = σ.sideTanTwo * Real.sin σ.θ₃ := by
    rw [σ.wallSide_one_eq, σ.vertexTwo_eq_real, ofReal_re, ofReal_im]
    ring
  rw [hv] at h
  have h2 := norm_sub_vertexTwo_lt hσ hz
  have hr := radTwo_le_rhoZero D
  have hm := hypMu_le_two (σ := σ)
  have := rhoZero_eq (σ := σ)
  have := abs_lt.mp (h.trans_lt h2)
  linarith [this.1, rhoZero_pos (σ := σ)]

theorem wallSide_two_of_mem_discThree {z : ℂ} (hz : z ∈ discThree D) :
    3 * rhoZero σ < σ.wallSide 2 z := by
  have h := abs_wallSide_two_sub_le hσ (norm_lt_one_of_mem_discThree D hz)
    (show ‖(0 : ℂ)‖ < 1 by norm_num)
  rw [σ.wallSide_two_zero, sub_zero] at h
  have hz' : ‖z‖ < radThree D := hz
  have hr := radThree_le_rhoZero D
  have hm := hypMu_le_three (σ := σ)
  have := rhoZero_eq (σ := σ)
  have := abs_le.mp h
  nlinarith [this.1, rhoZero_pos (σ := σ)]

theorem wallSide_zero_of_mem_discOne {z : ℂ} (hz : z ∈ discOne D) :
    3 * rhoZero σ < σ.wallSide 0 z := im_pos_of_mem_discOne hσ hz

omit hσ in
theorem norm_sub_lt_of_disc {a b : ℂ} {r s d : ℝ} {z : ℂ} (hz : ‖z - a‖ < r) (hw : ‖z - b‖ < s)
    (hd : d ≤ ‖a - b‖) (hrs : r + s ≤ d) : False := by
  have := norm_sub_le_norm_sub_add_norm_sub a z b
  rw [norm_sub_rev a z] at this
  linarith

theorem disjoint_discOne_discTwo : Disjoint (discOne D) (discTwo D) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  have hd : σ.sideTanOne * Real.sin σ.θ₃ ≤ ‖σ.vertexOne - σ.vertexTwo‖ := by
    have := abs_im_le_norm (σ.vertexOne - σ.vertexTwo)
    rw [sub_im, vertexOne_im, σ.vertexTwo_eq_real, ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have ha := radOne_le_rhoZero D
  have hb := radTwo_le_rhoZero D
  have hm := hypMu_le_one (σ := σ)
  have := rhoZero_eq (σ := σ)
  have := rhoZero_pos (σ := σ)
  exact norm_sub_lt_of_disc (norm_sub_vertexOne_lt hσ h1) (norm_sub_vertexTwo_lt hσ h2) hd
    (by linarith)

theorem disjoint_discOne_discThree : Disjoint (discOne D) (discThree D) := by
  rw [Set.disjoint_left]
  intro z h1 h3
  have h3' : ‖z - 0‖ < radThree D := by rw [sub_zero]; exact h3
  have hd : σ.sideTanOne * Real.sin σ.θ₃ ≤ ‖σ.vertexOne - 0‖ := by
    rw [sub_zero, ← vertexOne_im]
    exact (le_abs_self _).trans (abs_im_le_norm _)
  have ha := radOne_le_rhoZero D
  have hb := radThree_le_rhoZero D
  have hm := hypMu_le_one (σ := σ)
  have := rhoZero_eq (σ := σ)
  have := rhoZero_pos (σ := σ)
  exact norm_sub_lt_of_disc (norm_sub_vertexOne_lt hσ h1) h3' hd (by linarith)

theorem disjoint_discTwo_discThree : Disjoint (discTwo D) (discThree D) := by
  rw [Set.disjoint_left]
  intro z h2 h3
  have h3' : ‖z - 0‖ < radThree D := by rw [sub_zero]; exact h3
  have hd : σ.sideTanTwo * Real.sin σ.θ₃ ≤ ‖σ.vertexTwo - 0‖ := by
    rw [sub_zero, σ.vertexTwo_eq_real, Complex.norm_real, Real.norm_of_nonneg σ.sideTanTwo_pos.le]
    have := Real.sin_le_one σ.θ₃
    nlinarith [σ.sideTanTwo_pos]
  have ha := radTwo_le_rhoZero D
  have hb := radThree_le_rhoZero D
  have hm := hypMu_le_two (σ := σ)
  have := rhoZero_eq (σ := σ)
  have := rhoZero_pos (σ := σ)
  exact norm_sub_lt_of_disc (norm_sub_vertexTwo_lt hσ h2) h3' hd (by linarith)

theorem disjoint_discOne_discOneMirror : Disjoint (discOne D) (discOneMirror D) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  have := im_pos_of_mem_discOne hσ h1
  have := im_neg_of_mem_discOneMirror hσ h2
  have := rhoZero_pos (σ := σ)
  linarith

theorem norm_rotTwo_conj (z : ℂ) : ‖σ.rotTwo (conj z)‖ = ‖σ.rotTwo z‖ := by
  rw [HypFold.norm_rotTwo hσ, HypFold.norm_rotTwo hσ]
  conv_lhs => rw [← HypFold.conj_vertexTwo (σ := σ)]
  rw [HypFold.mob_conj_conj, Complex.norm_conj]

theorem conj_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D) : conj z ∈ discTwo D :=
  ⟨by rw [Complex.norm_conj]; exact hz.1, by rw [norm_rotTwo_conj hσ]; exact hz.2⟩

omit hσ in
theorem conj_mem_discThree {z : ℂ} (hz : z ∈ discThree D) : conj z ∈ discThree D := by
  change ‖conj z‖ < radThree D
  rw [Complex.norm_conj]; exact hz

theorem disjoint_discTwo_discOneMirror : Disjoint (discTwo D) (discOneMirror D) := by
  rw [Set.disjoint_left]
  intro z h2 h1
  exact Set.disjoint_left.mp (disjoint_discOne_discTwo hσ) h1 (conj_mem_discTwo hσ h2)

theorem disjoint_discThree_discOneMirror : Disjoint (discThree D) (discOneMirror D) := by
  rw [Set.disjoint_left]
  intro z h3 h1
  exact Set.disjoint_left.mp (disjoint_discOne_discThree hσ) h1 (conj_mem_discThree h3)

theorem f_of_mem_discOne {z : ℂ} (hz : z ∈ discOne D) :
    z ∈ D.U ∧ D.f z = 3 / 2 + σ.rotOne z ^ σ.p₁ / 2 := by
  refine D.f_apexOne z ⟨?_, ?_⟩
  · rw [CompactShape.eps_of_hyp σ hσ, ofReal_one, one_mul]
    exact HypFold.one_sub_conj_vertexOne_mul_ne_zero hσ hz.1
  · rw [CompactShape.disc_eq_mob hσ, ← HypFold.norm_rotOne hσ]
    exact hz.2.trans_le (radOne_le_apex D)

theorem f_of_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D) :
    z ∈ D.U ∧ D.f z = -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 := by
  refine D.f_apexTwo z ⟨?_, ?_⟩
  · rw [CompactShape.eps_of_hyp σ hσ, ofReal_one, one_mul, HypFold.conj_vertexTwo (σ := σ)]
    exact HypFold.one_sub_vertexTwo_mul_ne_zero hσ hz.1
  · rw [CompactShape.disc_eq_mob hσ, ← HypFold.norm_rotTwo hσ]
    exact hz.2.trans_le (radTwo_le_apex D)

omit hσ in
theorem f_of_mem_discThree {z : ℂ} (hz : z ∈ discThree D) (h0 : z ≠ 0) :
    z ∈ D.U ∧ D.f z = compactOuterGerm σ.p₃ z :=
  D.f_outer z (norm_pos_iff.mpr h0) (lt_of_lt_of_le hz (radThree_le_apex D))

end Discs

end Hyp

end ClosedTriangle

end GC.Seifert
