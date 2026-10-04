import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatInput

/-!
# The vertex discs of a flat closed triangle fold

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§1, with review 27's certificate: tube domains, disc separation, `r₀ B₁`). For a flat triangle
`σ` (`v₃ = 0`, `v₂ = sin θ₁`, `v₁ = sin θ₂ e^{iθ₃}`, sides `sin θₖ`) and a fold datum `D`, the radii
`radOne`, `radTwo`, `radThree` are at most `ρ₀ = sin θ₁ sin θ₂ sin θ₃ / 4`, the apex radii of `D`,
and `1/2`. The full discs `discOne`, `discTwo`, `discThree` about `v₁`, `v₂`, `0` and the mirror
`discOneMirror` about `v̄₁` are pairwise disjoint (`disjoint_*`), lie on the inner side of the
two walls not through their centre with margin `3ρ₀` (`wallSide_*_of_mem_disc*`), `discOne` lies in
the upper half plane, and the apex germs of `D` hold on them (`f_of_mem_discOne`, ...). The patch
margin `kap = radOne radTwo radThree (8 ρ₀) / 2` is at most `rⱼ sin θⱼ / 2` (`kap_le_*`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

section Constants

variable (σ) in
def sProd : ℝ := Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃

variable (σ) in
def rhoZero : ℝ := sProd σ / 4

def radOne : ℝ := min (min (rhoZero σ) (D.apexRadius 0)) (1 / 2)

def radTwo : ℝ := min (min (rhoZero σ) (D.apexRadius 1)) (1 / 2)

def radThree : ℝ := min (min (rhoZero σ) (D.apexRadius 2)) (1 / 2)

def kap : ℝ := radOne D * radTwo D * radThree D * sProd σ / 2

omit D in
theorem sProd_pos : 0 < sProd σ :=
  mul_pos (mul_pos σ.sin_θ₁_pos σ.sin_θ₂_pos) σ.sin_θ₃_pos

omit D in
theorem sProd_le_one : sProd σ ≤ 1 := by
  unfold sProd
  have h1 := Real.sin_le_one σ.θ₁
  have h2 := Real.sin_le_one σ.θ₂
  have h3 := Real.sin_le_one σ.θ₃
  have p1 := σ.sin_θ₁_pos
  have p2 := σ.sin_θ₂_pos
  have p3 := σ.sin_θ₃_pos
  calc Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃ ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

omit D in
theorem rhoZero_pos : 0 < rhoZero σ := by unfold rhoZero; linarith [sProd_pos (σ := σ)]

omit D in
theorem sProd_le_sin23 : sProd σ ≤ Real.sin σ.θ₂ * Real.sin σ.θ₃ := by
  unfold sProd
  have := mul_pos σ.sin_θ₂_pos σ.sin_θ₃_pos
  nlinarith [Real.sin_le_one σ.θ₁]

omit D in
theorem sProd_le_sin13 : sProd σ ≤ Real.sin σ.θ₁ * Real.sin σ.θ₃ := by
  unfold sProd
  have := mul_pos σ.sin_θ₁_pos σ.sin_θ₃_pos
  nlinarith [Real.sin_le_one σ.θ₂]

omit D in
theorem sProd_le_sin12 : sProd σ ≤ Real.sin σ.θ₁ * Real.sin σ.θ₂ := by
  unfold sProd
  have := mul_pos σ.sin_θ₁_pos σ.sin_θ₂_pos
  nlinarith [Real.sin_le_one σ.θ₃]

omit D in
theorem sProd_le_sin1 : sProd σ ≤ Real.sin σ.θ₁ := by
  have := sProd_le_sin12 (σ := σ)
  nlinarith [Real.sin_le_one σ.θ₂, σ.sin_θ₁_pos]

omit D in
theorem sProd_le_sin2 : sProd σ ≤ Real.sin σ.θ₂ := by
  have := sProd_le_sin12 (σ := σ)
  nlinarith [Real.sin_le_one σ.θ₁, σ.sin_θ₂_pos]

omit D in
theorem sProd_le_sin3 : sProd σ ≤ Real.sin σ.θ₃ := by
  have := sProd_le_sin13 (σ := σ)
  nlinarith [Real.sin_le_one σ.θ₁, σ.sin_θ₃_pos]

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

theorem kap_pos : 0 < kap D := by
  unfold kap
  have := radOne_pos D
  have := radTwo_pos D
  have := radThree_pos D
  have := sProd_pos (σ := σ)
  positivity

theorem kap_le_of {r : ℝ} (hr : 0 < r) (hrr : r = radOne D ∨ r = radTwo D ∨ r = radThree D)
    {s : ℝ} (hs : sProd σ ≤ s) : kap D ≤ r * s / 2 := by
  unfold kap
  have h1 := radOne_pos D
  have h2 := radTwo_pos D
  have h3 := radThree_pos D
  have k1 := radOne_le_half D
  have k2 := radTwo_le_half D
  have k3 := radThree_le_half D
  have hp := sProd_pos (σ := σ)
  rcases hrr with rfl | rfl | rfl
  · have : radTwo D * radThree D ≤ 1 := by nlinarith
    nlinarith [mul_pos h2 h3, mul_pos h1 hp]
  · have : radOne D * radThree D ≤ 1 := by nlinarith
    nlinarith [mul_pos h1 h3, mul_pos h2 hp]
  · have : radOne D * radTwo D ≤ 1 := by nlinarith
    nlinarith [mul_pos h1 h2, mul_pos h3 hp]

end Constants

section Discs

def discOne : Set ℂ := {z | ‖z - σ.vertexOne‖ < radOne D}

def discTwo : Set ℂ := {z | ‖z - σ.vertexTwo‖ < radTwo D}

def discThree : Set ℂ := {z | ‖z‖ < radThree D}

def discOneMirror : Set ℂ := {z | ‖z - conj σ.vertexOne‖ < radOne D}

theorem isOpen_discOne : IsOpen (discOne D) :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem isOpen_discTwo : IsOpen (discTwo D) :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem isOpen_discThree : IsOpen (discThree D) :=
  isOpen_lt continuous_norm continuous_const

theorem isOpen_discOneMirror : IsOpen (discOneMirror D) :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

omit D in
theorem vertexOne_re : σ.vertexOne.re = Real.sin σ.θ₂ * Real.cos σ.θ₃ := by
  simp only [EuclidShape.vertexOne, mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]

omit D in
theorem vertexOne_im : σ.vertexOne.im = Real.sin σ.θ₂ * Real.sin σ.θ₃ := by
  simp only [EuclidShape.vertexOne, mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]

omit D in
theorem abs_wallSide_sub_le (i : Fin 3) (z w : ℂ) :
    |σ.wallSide i z - σ.wallSide i w| ≤ ‖z - w‖ := by
  fin_cases i
  · change |z.im - w.im| ≤ _
    rw [← sub_im]
    exact abs_im_le_norm _
  · change |(exp ((σ.θ₃ : ℂ) * I) * conj z).im - (exp ((σ.θ₃ : ℂ) * I) * conj w).im| ≤ _
    rw [← sub_im, ← mul_sub, ← map_sub]
    refine (abs_im_le_norm _).trans ?_
    rw [norm_mul, EuclidShape.norm_exp_mul_I, one_mul, Complex.norm_conj]
  · change |(σ.rotTwo z).im - (σ.rotTwo w).im| ≤ _
    rw [← sub_im]
    refine (abs_im_le_norm _).trans ?_
    have : σ.rotTwo z - σ.rotTwo w = -(exp ((σ.θ₂ : ℂ) * I) * (z - w)) := by
      simp only [EuclidShape.rotTwo]; ring
    rw [this, norm_neg, norm_mul, EuclidShape.norm_exp_mul_I, one_mul]

theorem mem_discOneMirror_iff {z : ℂ} : z ∈ discOneMirror D ↔ conj z ∈ discOne D := by
  simp only [discOneMirror, discOne, mem_ofPred_eq]
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj]

theorem im_pos_of_mem_discOne {z : ℂ} (hz : z ∈ discOne D) : 3 * rhoZero σ < z.im := by
  have h := abs_im_le_norm (z - σ.vertexOne)
  rw [sub_im, vertexOne_im] at h
  have hs := sProd_le_sin23 (σ := σ)
  have hr := radOne_le_rhoZero D
  have := abs_lt.mp (h.trans_lt hz)
  unfold rhoZero at hr ⊢
  linarith [this.1]

theorem im_neg_of_mem_discOneMirror {z : ℂ} (hz : z ∈ discOneMirror D) :
    z.im < -(3 * rhoZero σ) := by
  have h := im_pos_of_mem_discOne D ((mem_discOneMirror_iff D).1 hz)
  rw [conj_im] at h
  linarith

theorem wallSide_one_of_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D) :
    3 * rhoZero σ < σ.wallSide 1 z := by
  have h := abs_wallSide_sub_le (σ := σ) 1 z σ.vertexTwo
  have hv : σ.wallSide 1 σ.vertexTwo = Real.sin σ.θ₃ * Real.sin σ.θ₁ := by
    rw [EuclidShape.wallSide_one_apply, EuclidShape.vertexTwo, ofReal_re, ofReal_im]
    ring
  rw [hv] at h
  have hr := radTwo_le_rhoZero D
  have hs := sProd_le_sin13 (σ := σ)
  have := abs_lt.mp (h.trans_lt hz)
  unfold rhoZero at hr ⊢
  linarith [this.1]

theorem wallSide_two_of_mem_discThree {z : ℂ} (hz : z ∈ discThree D) :
    3 * rhoZero σ < σ.wallSide 2 z := by
  have h := abs_wallSide_sub_le (σ := σ) 2 z 0
  have hv : σ.wallSide 2 0 = Real.sin σ.θ₁ * Real.sin σ.θ₂ := by
    rw [EuclidShape.wallSide_two_apply]
    simp
  rw [hv, sub_zero] at h
  have hr := radThree_le_rhoZero D
  have hs := sProd_le_sin12 (σ := σ)
  have := abs_lt.mp (h.trans_lt hz)
  unfold rhoZero at hr ⊢
  linarith [this.1]

theorem wallSide_zero_of_mem_discOne {z : ℂ} (hz : z ∈ discOne D) :
    3 * rhoZero σ < σ.wallSide 0 z := im_pos_of_mem_discOne D hz

theorem norm_sub_lt_of_disc {a b : ℂ} {r s d : ℝ} {z : ℂ} (hz : ‖z - a‖ < r) (hw : ‖z - b‖ < s)
    (hd : d ≤ ‖a - b‖) (hrs : r + s ≤ d) : False := by
  have := norm_sub_le_norm_sub_add_norm_sub a z b
  rw [norm_sub_rev a z] at this
  linarith

theorem disjoint_discOne_discTwo : Disjoint (discOne D) (discTwo D) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  have hd : Real.sin σ.θ₃ ≤ ‖σ.vertexOne - σ.vertexTwo‖ := by
    rw [σ.norm_vertexOne_sub_vertexTwo]
  have hs := sProd_le_sin3 (σ := σ)
  have ha := radOne_le_rhoZero D
  have hb := radTwo_le_rhoZero D
  have := sProd_pos (σ := σ)
  unfold rhoZero at ha hb
  exact norm_sub_lt_of_disc h1 h2 hd (by linarith)

theorem disjoint_discOne_discThree : Disjoint (discOne D) (discThree D) := by
  rw [Set.disjoint_left]
  intro z h1 h3
  have h3' : ‖z - 0‖ < radThree D := by rwa [sub_zero]
  have hd : Real.sin σ.θ₂ ≤ ‖σ.vertexOne - 0‖ := by rw [sub_zero, σ.norm_vertexOne]
  have hs := sProd_le_sin2 (σ := σ)
  have ha := radOne_le_rhoZero D
  have hb := radThree_le_rhoZero D
  have := sProd_pos (σ := σ)
  unfold rhoZero at ha hb
  exact norm_sub_lt_of_disc h1 h3' hd (by linarith)

theorem disjoint_discTwo_discThree : Disjoint (discTwo D) (discThree D) := by
  rw [Set.disjoint_left]
  intro z h2 h3
  have h3' : ‖z - 0‖ < radThree D := by rwa [sub_zero]
  have hd : Real.sin σ.θ₁ ≤ ‖σ.vertexTwo - 0‖ := by rw [sub_zero, σ.norm_vertexTwo]
  have hs := sProd_le_sin1 (σ := σ)
  have ha := radTwo_le_rhoZero D
  have hb := radThree_le_rhoZero D
  have := sProd_pos (σ := σ)
  unfold rhoZero at ha hb
  exact norm_sub_lt_of_disc h2 h3' hd (by linarith)

theorem disjoint_discOne_discOneMirror : Disjoint (discOne D) (discOneMirror D) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  have := im_pos_of_mem_discOne D h1
  have := im_neg_of_mem_discOneMirror D h2
  have := rhoZero_pos (σ := σ)
  linarith

theorem disjoint_discTwo_discOneMirror : Disjoint (discTwo D) (discOneMirror D) := by
  rw [Set.disjoint_left]
  intro z h2 h1
  have h2' : conj z ∈ discTwo D := by
    simp only [discTwo, mem_ofPred_eq] at h2 ⊢
    rw [← σ.conj_vertexTwo, ← map_sub, Complex.norm_conj]
    exact h2
  exact Set.disjoint_left.mp (disjoint_discOne_discTwo D) ((mem_discOneMirror_iff D).1 h1) h2'

theorem disjoint_discThree_discOneMirror : Disjoint (discThree D) (discOneMirror D) := by
  rw [Set.disjoint_left]
  intro z h3 h1
  have h3' : conj z ∈ discThree D := by
    simp only [discThree, mem_ofPred_eq] at h3 ⊢
    rwa [Complex.norm_conj]
  exact Set.disjoint_left.mp (disjoint_discOne_discThree D) ((mem_discOneMirror_iff D).1 h1) h3'

theorem f_of_mem_discOne {z : ℂ} (hz : z ∈ discOne D) : z ∈ D.U ∧ D.f z = σ.apexOne z :=
  f_apexOne' D (lt_of_lt_of_le hz (radOne_le_apex D))

theorem f_of_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D) : z ∈ D.U ∧ D.f z = σ.apexTwo z :=
  f_apexTwo' D (lt_of_lt_of_le hz (radTwo_le_apex D))

theorem f_of_mem_discThree {z : ℂ} (hz : z ∈ discThree D) (h0 : z ≠ 0) :
    z ∈ D.U ∧ D.f z = compactOuterGerm σ.p₃ z :=
  f_outer' D (norm_pos_iff.mpr h0) (lt_of_lt_of_le hz (radThree_le_apex D))

theorem norm_rotOne (z : ℂ) : ‖σ.rotOne z‖ = ‖z - σ.vertexOne‖ := by
  rw [EuclidShape.rotOne, norm_neg, norm_mul]
  rw [show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
    EuclidShape.norm_exp_mul_I, one_mul]

theorem norm_rotTwo (z : ℂ) : ‖σ.rotTwo z‖ = ‖z - σ.vertexTwo‖ := by
  rw [EuclidShape.rotTwo, norm_neg, norm_mul, EuclidShape.norm_exp_mul_I, one_mul]

end Discs

end ClosedTriangle

end GC.Seifert
