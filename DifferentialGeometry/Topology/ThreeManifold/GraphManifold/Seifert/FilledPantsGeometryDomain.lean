import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryWalls

/-!
# The open domain of the two-cone fold

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §2,
with review 21 §4.1–§4.2). For a fold datum `D` of a shape with `θ₁ p₁ = π`, `θ₂ p₂ = π`, the
base domain of the fold is assembled from open pieces of the upper half-plane:
the full cone discs `discOne = {|ω₁| < r₁}` about `v₁` and `discTwo = {|ω₂| < r₂}` about `v₂`
(hyperbolic discs, invariant under the reflections through the vertex, on which the apex germs,
the wall neighbourhoods and the strip conditions hold), the open triangle `intT`, and the wall
pieces `patchZero`, `patchOne`, `patchTwo`: reflection-stable neighbourhoods of the walls minus the
vertices, cut by the real segment conditions on `Re f` (from `Seifert/FilledPantsGeometryWalls`)
and, inside the cone discs, by wedges `|arg| < π/(2p)` around the walls, so that the phase
`basePhase ∘ f` is single valued there and agrees with the tube formula on the overlap
(review 21 §5.3). The mirrored pieces are the preimages under `σ₀`.
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open scoped Topology ComplexConjugate ContDiff

namespace GC.Seifert

namespace TwoConeFold

open ConeShape

def wedgeSet (a : ℝ) : Set ℂ := {w | w ≠ 0 ∧ |arg w| < a}

theorem isOpen_wedgeSet {a : ℝ} (ha : a ≤ Real.pi) : IsOpen (wedgeSet a) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  have hslit : w ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]
    refine ⟨fun h => ?_, hw.1⟩
    have := hw.2
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith
  have hc := continuousAt_arg hslit
  have hopen : IsOpen ({w : ℂ | w ≠ 0} ∩ arg ⁻¹' Ioo (-a) a) := by
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    have hxs : x ∈ slitPlane := by
      rw [mem_slitPlane_iff_arg]
      refine ⟨fun h => ?_, hx.1⟩
      have := hx.2.2
      rw [h] at this
      linarith
    exact Filter.inter_mem (isOpen_ne.mem_nhds hx.1)
      ((continuousAt_arg hxs).preimage_mem_nhds (isOpen_Ioo.mem_nhds hx.2))
  have hsub : {w : ℂ | w ≠ 0} ∩ arg ⁻¹' Ioo (-a) a ⊆ wedgeSet a := fun x hx =>
    ⟨hx.1, abs_lt.2 hx.2⟩
  exact Filter.mem_of_superset (hopen.mem_nhds ⟨hw.1, abs_lt.1 hw.2⟩) hsub

theorem arg_exp_mul_of_mem {θ : ℝ} {w : ℂ} (hw : w ≠ 0) (h1 : -Real.pi < θ + arg w)
    (h2 : θ + arg w ≤ Real.pi) : arg (exp (θ * I) * w) = θ + arg w := by
  have hw' := norm_mul_exp_arg_mul_I w
  have e : exp (θ * I) * w = (‖w‖ : ℂ) * exp (((θ + arg w : ℝ) : ℂ) * I) := by
    conv_lhs => rw [← hw']
    push_cast
    rw [add_mul, exp_add]
    ring
  rw [e, arg_real_mul _ (norm_pos_iff.mpr hw), exp_mul_I, arg_cos_add_sin_mul_I ⟨h1, h2⟩]

theorem exists_disc_subset {v : ℂ} (hv : 0 < v.im) {S : Set ℂ} (hS : S ∈ 𝓝 v) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z : ℂ, 0 < z.im → ‖coneDisc v z‖ < r → z ∈ S := by
  set h : ℂ → ℂ := fun w => (v - conj v * w) / (1 - w)
  have hcont : ContinuousAt h 0 := by
    apply ContinuousAt.div (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
      (continuousAt_const.sub continuousAt_id)
    simp
  have h0 : h 0 = v := by simp [h]
  rw [← h0] at hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds hS)
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun z hz hω => ?_⟩
  have hω1 : ‖coneDisc v z‖ < 1 := lt_of_lt_of_le hω (min_le_right _ _)
  have hne : 1 - coneDisc v z ≠ 0 := by
    intro h1
    have : coneDisc v z = 1 := (sub_eq_zero.1 h1).symm
    rw [this, norm_one] at hω1
    exact lt_irrefl _ hω1
  have hz' : h (coneDisc v z) = z := by
    simp only [h]
    rw [div_eq_iff hne, mul_one_sub_coneDisc hv hz]
  have hmem : coneDisc v z ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hω (min_le_left _ _)
  have := hball hmem
  rw [mem_preimage, hz'] at this
  exact this

theorem continuousOn_coneDisc {v : ℂ} (hv : 0 < v.im) :
    ContinuousOn (coneDisc v) {z | 0 < z.im} := by
  intro z hz
  exact ((continuous_id.sub continuous_const).continuousAt.div
    (continuous_id.sub continuous_const).continuousAt (sub_conj_ne_zero hv hz)).continuousWithinAt

theorem isOpen_upper : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im

theorem isOpen_coneDisc_preimage {v : ℂ} (hv : 0 < v.im) {S : Set ℂ} (hS : IsOpen S) :
    IsOpen {z : ℂ | 0 < z.im ∧ coneDisc v z ∈ S} := by
  exact (continuousOn_coneDisc hv).isOpen_inter_preimage isOpen_upper hS

section Rays

variable (σ : ConeShape)

theorem wallSide_two_pos_of_wallZero {z : ℂ} (hz : z ∈ σ.foldWall 0) (hne : z ≠ σ.vertexTwo) :
    0 < σ.wallSide 2 z := by
  rcases (hz.1.2 2).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    have hx : z.re = 0 := hz.2
    have h2 : (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 = 0 := h.symm
    rw [hx] at h2
    have hy : z.im = Real.sin σ.θ₂ / 4 := by
      have hs := σ.sin_θ₂_nonneg
      have := Real.sin_sq_add_cos_sq σ.θ₂
      unfold centre at h2
      nlinarith [hz.1.1]
    exact Complex.ext (by rw [hx, vertexTwo_re]) (by rw [hy, vertexTwo_im])

theorem wallSide_two_pos_of_wallOne {z : ℂ} (hz : z ∈ σ.foldWall 1) (hne : z ≠ σ.vertexOne) :
    0 < σ.wallSide 2 z := by
  rcases (hz.1.2 2).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    have hx : z.re = σ.width := by have := hz.2; change σ.width - z.re = 0 at this; linarith
    have h2 : (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 = 0 := h.symm
    rw [hx] at h2
    have hy : z.im = Real.sin σ.θ₁ / 4 := by
      have hs := σ.sin_θ₁_pos
      have := Real.sin_sq_add_cos_sq σ.θ₁
      unfold width centre at h2
      nlinarith [hz.1.1]
    exact Complex.ext (by rw [hx, vertexOne_re]) (by rw [hy, vertexOne_im])

theorem coneDisc_vertexTwo_wallZero {z : ℂ} (hz : z ∈ σ.foldWall 0) (hne : z ≠ σ.vertexTwo)
    (hθ : 0 < σ.θ₂) : coneDisc σ.vertexTwo z ≠ 0 ∧ arg (coneDisc σ.vertexTwo z) = 0 := by
  have hx : z.re = 0 := hz.2
  have hw2 := wallSide_two_pos_of_wallZero σ hz hne
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
  have hy : Real.sin σ.θ₂ / 4 < z.im := by
    change 0 < (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at hw2
    rw [hx] at hw2
    have := Real.sin_sq_add_cos_sq σ.θ₂
    unfold centre at hw2
    nlinarith [hz.1.1]
  have hz' : z = (σ.vertexTwo.re : ℂ) + (z.im : ℂ) * I :=
    Complex.ext (by simp [hx, vertexTwo_re]) (by simp)
  rw [hz', coneDisc_vertical_point, vertexTwo_im]
  have hpos : 0 < (z.im - Real.sin σ.θ₂ / 4) / (z.im + Real.sin σ.θ₂ / 4) := by
    apply div_pos <;> linarith
  exact ⟨by exact_mod_cast hpos.ne', arg_ofReal_of_nonneg hpos.le⟩

theorem coneDisc_vertexOne_wallOne {z : ℂ} (hz : z ∈ σ.foldWall 1) (hne : z ≠ σ.vertexOne) :
    coneDisc σ.vertexOne z ≠ 0 ∧ arg (coneDisc σ.vertexOne z) = 0 := by
  have hx : z.re = σ.width := by have := hz.2; change σ.width - z.re = 0 at this; linarith
  have hw2 := wallSide_two_pos_of_wallOne σ hz hne
  have hs := σ.sin_θ₁_pos
  have hy : Real.sin σ.θ₁ / 4 < z.im := by
    change 0 < (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at hw2
    rw [hx] at hw2
    have := Real.sin_sq_add_cos_sq σ.θ₁
    unfold width centre at hw2
    nlinarith [hz.1.1]
  have hz' : z = (σ.vertexOne.re : ℂ) + (z.im : ℂ) * I :=
    Complex.ext (by simp [hx, vertexOne_re]) (by simp)
  rw [hz', coneDisc_vertical_point, vertexOne_im]
  have hpos : 0 < (z.im - Real.sin σ.θ₁ / 4) / (z.im + Real.sin σ.θ₁ / 4) := by
    apply div_pos <;> linarith
  exact ⟨by exact_mod_cast hpos.ne', arg_ofReal_of_nonneg hpos.le⟩

theorem arg_coneDisc_one_of_sides {z : ℂ} (hz : 0 < z.im) (h1 : 0 < σ.wallSide 1 z)
    (h2 : 0 < σ.wallSide 2 z) :
    0 < arg (coneDisc σ.vertexOne z) ∧ arg (coneDisc σ.vertexOne z) < σ.θ₁ := by
  set η := coneDisc σ.vertexOne z with hη
  have hnsq : 0 < normSq (z - conj σ.vertexOne) := normSq_sub_conj_pos σ.vertexOne_im_pos hz
  have him : 0 < η.im := by
    have := σ.im_coneDisc_vertexOne_mul z
    rw [← hη] at this
    have hpos : 0 < 2 * σ.vertexOne.im * σ.wallSide 1 z := by
      have := σ.vertexOne_im_pos
      positivity
    rw [← this] at hpos
    exact pos_of_mul_pos_left hpos hnsq.le
  have hrot : (exp (-(σ.θ₁ * I)) * η).im < 0 := by
    have := σ.im_rot_coneDisc_vertexOne_mul z
    rw [← hη] at this
    have hneg : -(Real.sin σ.θ₁ * σ.wallSide 2 z) < 0 := by
      have := σ.sin_θ₁_pos
      have : 0 < Real.sin σ.θ₁ * σ.wallSide 2 z := by positivity
      linarith
    rw [← this] at hneg
    exact neg_of_mul_neg_left hneg hnsq.le
  have hne : η ≠ 0 := fun h => by rw [h] at him; simp at him
  have ha0 : 0 < arg η := lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) (fun h => by
    have := (arg_eq_zero_iff.mp h.symm).2
    linarith)
  have haπ : arg η < Real.pi := arg_lt_pi_iff.mpr (Or.inr him.ne')
  have hθ1 := σ.θ₁_pos
  have hθ2 := σ.θ₁_le
  have heq : arg (exp ((-σ.θ₁ : ℝ) * I) * η) = -σ.θ₁ + arg η :=
    arg_exp_mul_of_mem hne (by linarith [Real.pi_pos]) (by linarith)
  have hexp : exp (((-σ.θ₁ : ℝ) : ℂ) * I) = exp (-(σ.θ₁ * I)) := by
    congr 1
    push_cast
    ring
  have hneg := arg_neg_iff.mpr (show (exp (((-σ.θ₁ : ℝ) : ℂ) * I) * η).im < 0 by
    rw [hexp]; exact hrot)
  rw [heq] at hneg
  exact ⟨ha0, by linarith⟩

theorem arg_xi_of_sides {z : ℂ} (hz : 0 < z.im) (hθ : 0 < σ.θ₂) (h0 : 0 < σ.wallSide 0 z)
    (h2 : 0 < σ.wallSide 2 z) :
    0 < arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) ∧
      arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) < σ.θ₂ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
  have hv : 0 < σ.vertexTwo.im := by rw [vertexTwo_im]; positivity
  set η := coneDisc σ.vertexTwo z with hη
  set ξ := exp (σ.θ₂ * I) * η with hξ
  have hnsq : 0 < normSq (z - conj σ.vertexTwo) := normSq_sub_conj_pos hv hz
  have himη : η.im < 0 := by
    have := σ.im_coneDisc_vertexTwo_mul z
    rw [← hη] at this
    have hneg : -(2 * σ.vertexTwo.im * σ.wallSide 0 z) < 0 := by
      have : 0 < 2 * σ.vertexTwo.im * σ.wallSide 0 z := by positivity
      linarith
    rw [← this] at hneg
    exact neg_of_mul_neg_left hneg hnsq.le
  have hrot : (exp (-(((Real.pi - σ.θ₂ : ℝ) : ℂ) * I)) * η).im < 0 := by
    have := σ.im_rot_coneDisc_vertexTwo_mul z
    rw [← hη] at this
    have hneg : -(Real.sin σ.θ₂ * σ.wallSide 2 z) < 0 := by
      have : 0 < Real.sin σ.θ₂ * σ.wallSide 2 z := by positivity
      linarith
    rw [← this] at hneg
    exact neg_of_mul_neg_left hneg hnsq.le
  have hrotξ : exp (-(((Real.pi - σ.θ₂ : ℝ) : ℂ) * I)) * η = -ξ := by
    rw [hξ]
    have : -(((Real.pi - σ.θ₂ : ℝ) : ℂ) * I) = σ.θ₂ * I + (-(Real.pi * I)) := by push_cast; ring
    rw [this, exp_add, exp_neg, exp_pi_mul_I]
    ring
  rw [hrotξ, neg_im] at hrot
  have himξ : 0 < ξ.im := by linarith
  have hne : ξ ≠ 0 := fun h => by rw [h] at himξ; simp at himξ
  have ha0 : 0 < arg ξ := lt_of_le_of_ne (arg_nonneg_iff.mpr himξ.le) (fun h => by
    have := (arg_eq_zero_iff.mp h.symm).2
    linarith)
  have haπ : arg ξ < Real.pi := arg_lt_pi_iff.mpr (Or.inr himξ.ne')
  have hθ2 := σ.θ₂_le
  have heq : arg (exp (((-σ.θ₂ : ℝ) : ℂ) * I) * ξ) = -σ.θ₂ + arg ξ :=
    arg_exp_mul_of_mem hne (by linarith [Real.pi_pos]) (by linarith)
  have hηξ : exp (((-σ.θ₂ : ℝ) : ℂ) * I) * ξ = η := by
    rw [hξ, ← mul_assoc, ← exp_add]
    push_cast
    simp
  rw [hηξ] at heq
  have hneg := arg_neg_iff.mpr himη
  rw [heq] at hneg
  exact ⟨ha0, by linarith⟩

theorem rot_coneDisc_one_of_wallTwo {z : ℂ} (hz : z ∈ σ.foldWall 2) (hx : z.re < σ.width) :
    ∃ t : ℝ, 0 < t ∧ exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z = t := by
  have hzim : 0 < z.im := hz.1.1
  have hc : z ≠ σ.centre := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hrefl : σ.refl 2 z = z := σ.refl_of_wallSide_eq_zero hzim hz.2
  have hη := σ.coneDisc_vertexOne_refl_two hc
  rw [hrefl] at hη
  set η := coneDisc σ.vertexOne z with hηdef
  set ρ := exp (-(σ.θ₁ * I)) * η with hρdef
  have hconj : conj ρ = ρ := by
    have e1 : conj ρ = exp (σ.θ₁ * I) * conj η := by
      rw [hρdef, map_mul, ← exp_conj]
      congr 2
      simp [conj_ofReal]
    rw [e1]
    conv_rhs => rw [hρdef, hη]
    rw [← mul_assoc, ← exp_add]
    congr 2
    ring
  have hρreal : ρ = (ρ.re : ℂ) := (conj_eq_iff_re.mp hconj).symm
  have hηt : η = exp (σ.θ₁ * I) * (ρ.re : ℂ) := by
    rw [← hρreal, hρdef, ← mul_assoc, ← exp_add]
    simp
  have hnsq : 0 < normSq (z - conj σ.vertexOne) := normSq_sub_conj_pos σ.vertexOne_im_pos hzim
  have him : 0 < η.im := by
    have := σ.im_coneDisc_vertexOne_mul z
    rw [← hηdef] at this
    have hw1 : 0 < σ.wallSide 1 z := by change 0 < σ.width - z.re; linarith
    have hpos : 0 < 2 * σ.vertexOne.im * σ.wallSide 1 z := by
      have := σ.vertexOne_im_pos
      positivity
    rw [← this] at hpos
    exact pos_of_mul_pos_left hpos hnsq.le
  refine ⟨ρ.re, ?_, hρreal⟩
  rw [hηt] at him
  have e : (exp ((σ.θ₁ : ℂ) * I) * (ρ.re : ℂ)).im = Real.sin σ.θ₁ * ρ.re := by
    simp [mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  rw [e] at him
  exact pos_of_mul_pos_right him σ.sin_θ₁_pos.le

theorem xi_of_wallTwo {z : ℂ} (hz : z ∈ σ.foldWall 2) (hx : 0 < z.re) (hθ : 0 < σ.θ₂) :
    ∃ t : ℝ, 0 < t ∧ exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z = t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
  have hv : 0 < σ.vertexTwo.im := by rw [vertexTwo_im]; positivity
  have hzim : 0 < z.im := hz.1.1
  have hc : z ≠ σ.centre := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hrefl : σ.refl 2 z = z := σ.refl_of_wallSide_eq_zero hzim hz.2
  have hη := σ.coneDisc_vertexTwo_refl_two hc
  rw [hrefl] at hη
  set η := coneDisc σ.vertexTwo z with hηdef
  set ξ := exp (σ.θ₂ * I) * η with hξdef
  have hconj : conj ξ = ξ := by
    have e1 : conj ξ = exp (-(σ.θ₂ * I)) * conj η := by
      rw [hξdef, map_mul, ← exp_conj]
      congr 2
      simp [conj_ofReal]
    rw [e1]
    conv_rhs => rw [hξdef, hη]
    rw [← mul_assoc, ← exp_add]
    have : (σ.θ₂ : ℂ) * I + 2 * ((Real.pi - σ.θ₂ : ℝ) : ℂ) * I =
        -(σ.θ₂ * I) + 2 * Real.pi * I := by push_cast; ring
    rw [this, exp_add, exp_two_pi_mul_I, mul_one]
  have hξreal : ξ = (ξ.re : ℂ) := (conj_eq_iff_re.mp hconj).symm
  have hηt : η = exp (-(σ.θ₂ * I)) * (ξ.re : ℂ) := by
    rw [← hξreal, hξdef, ← mul_assoc, ← exp_add]
    simp
  have hnsq : 0 < normSq (z - conj σ.vertexTwo) := normSq_sub_conj_pos hv hzim
  have him : η.im < 0 := by
    have := σ.im_coneDisc_vertexTwo_mul z
    rw [← hηdef] at this
    have hw0 : 0 < σ.wallSide 0 z := hx
    have hneg : -(2 * σ.vertexTwo.im * σ.wallSide 0 z) < 0 := by
      have : 0 < 2 * σ.vertexTwo.im * σ.wallSide 0 z := by positivity
      linarith
    rw [← this] at hneg
    exact neg_of_mul_neg_left hneg hnsq.le
  refine ⟨ξ.re, ?_, hξreal⟩
  rw [hηt] at him
  have e : (exp (-((σ.θ₂ : ℂ) * I)) * (ξ.re : ℂ)).im = -(Real.sin σ.θ₂ * ξ.re) := by
    rw [show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring, mul_im,
      exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    simp [Real.sin_neg]
  rw [e] at him
  have : 0 < Real.sin σ.θ₂ * ξ.re := by linarith
  exact pos_of_mul_pos_right this hs.le

end Rays

theorem continuousAt_refl' (σ : ConeShape) {z : ℂ} (hz : 0 < z.im) (i : Fin 3) :
    ContinuousAt (σ.refl i) z := by
  fin_cases i
  · exact (continuous_conj.neg).continuousAt
  · exact (continuous_const.sub continuous_conj).continuousAt
  · change ContinuousAt (fun w => (σ.centre : ℂ) + 1 / 16 / (conj w - σ.centre)) z
    exact continuousAt_const.add (continuousAt_const.div
      (continuous_conj.continuousAt.sub continuousAt_const) (σ.conj_centre_ne hz))

theorem continuousAt_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    ContinuousAt (coneDisc v) z :=
  (continuousOn_coneDisc hv).continuousAt (isOpen_upper.mem_nhds hz)

theorem continuous_wallSide (σ : ConeShape) (i : Fin 3) : Continuous (σ.wallSide i) := by
  fin_cases i
  · exact continuous_re
  · exact continuous_const.sub continuous_re
  · change Continuous fun z : ℂ => (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16
    fun_prop

theorem eventually_wedge2 {g₁ g₂ : ℂ → ℂ} {z : ℂ} (hg₁ : ContinuousAt g₁ z)
    (hg₂ : ContinuousAt g₂ z) {r a : ℝ} (ha : a ≤ Real.pi) (h : r < ‖g₁ z‖ ∨ g₂ z ∈ wedgeSet a) :
    ∀ᶠ w in 𝓝 z, r < ‖g₁ w‖ ∨ g₂ w ∈ wedgeSet a := by
  rcases h with h | h
  · filter_upwards [(continuous_norm.continuousAt.comp hg₁).eventually (lt_mem_nhds h)] with w hw
    exact Or.inl hw
  · filter_upwards [hg₂.eventually ((isOpen_wedgeSet ha).mem_nhds h)] with w hw
    exact Or.inr hw

theorem eventually_wedge {g : ℂ → ℂ} {z : ℂ} (hg : ContinuousAt g z) {r a : ℝ}
    (ha : a ≤ Real.pi) (h : r < ‖g z‖ ∨ g z ∈ wedgeSet a) :
    ∀ᶠ w in 𝓝 z, r < ‖g w‖ ∨ g w ∈ wedgeSet a := by
  rcases h with h | h
  · filter_upwards [(continuous_norm.continuousAt.comp hg).eventually (lt_mem_nhds h)] with w hw
    exact Or.inl hw
  · filter_upwards [hg.eventually ((isOpen_wedgeSet ha).mem_nhds h)] with w hw
    exact Or.inr hw

namespace Fold

variable {σ : ConeShape} (D : σ.FoldData) {p₁ p₂ : ℕ} (hθ₁ : σ.θ₁ * p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * p₂ = Real.pi)

include hθ₁ in
theorem exists_radiusOne : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z : ℂ, 0 < z.im →
    ‖coneDisc σ.vertexOne z‖ < r → z ∈ D.U ∧ D.f z = σ.coneApexOne p₁ z ∧
      σ.width / 2 < z.re ∧ z ∈ D.V 1 ∧ z ∈ D.V 2 := by
  have hT := vertexOne_mem_triangle' σ
  have hw1 : σ.vertexOne ∈ σ.foldWall 1 := ⟨hT, by
    change σ.width - σ.vertexOne.re = 0
    rw [vertexOne_re, sub_self]⟩
  have hw2 : σ.vertexOne ∈ σ.foldWall 2 := ⟨hT, wallSide_two_vertexOne' σ⟩
  apply exists_disc_subset σ.vertexOne_im_pos
  filter_upwards [D.isOpen_U.mem_nhds (D.triangle_subset_U hT), D.f_apexOne p₁ hθ₁,
    (isOpen_lt continuous_const continuous_re).mem_nhds (show σ.width / 2 < σ.vertexOne.re by
      rw [vertexOne_re]; linarith [σ.width_pos]),
    (D.isOpen_V 1).mem_nhds (D.foldWall_subset_V 1 hw1),
    (D.isOpen_V 2).mem_nhds (D.foldWall_subset_V 2 hw2)] with z h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

include hθ₂ in
theorem exists_radiusTwo : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z : ℂ, 0 < z.im →
    ‖coneDisc σ.vertexTwo z‖ < r → z ∈ D.U ∧ D.f z = σ.coneApexTwo p₂ z ∧
      |z.re| < σ.width / 2 ∧ z ∈ D.V 0 ∧ z ∈ D.V 2 := by
  have hθ := θ₂_pos hθ₂
  have hT := vertexTwo_mem_triangle' σ hθ
  have hw0 : σ.vertexTwo ∈ σ.foldWall 0 := ⟨hT, by
    change σ.vertexTwo.re = 0
    rw [vertexTwo_re]⟩
  have hw2 : σ.vertexTwo ∈ σ.foldWall 2 := ⟨hT, by
    change (σ.vertexTwo.re - σ.centre) ^ 2 + σ.vertexTwo.im ^ 2 - 1 / 16 = 0
    rw [vertexTwo_re, vertexTwo_im]
    unfold centre
    nlinarith [Real.sin_sq_add_cos_sq σ.θ₂]⟩
  have hv : 0 < σ.vertexTwo.im := by
    rw [vertexTwo_im]
    have := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
    positivity
  apply exists_disc_subset hv
  filter_upwards [D.isOpen_U.mem_nhds (D.triangle_subset_U hT), D.f_apexTwo p₂ hθ₂,
    (isOpen_lt (continuous_abs.comp continuous_re) continuous_const).mem_nhds
      (show |σ.vertexTwo.re| < σ.width / 2 by
        rw [vertexTwo_re, abs_zero]; linarith [σ.width_pos]),
    (D.isOpen_V 0).mem_nhds (D.foldWall_subset_V 0 hw0),
    (D.isOpen_V 2).mem_nhds (D.foldWall_subset_V 2 hw2)] with z h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

def radiusOne : ℝ := Classical.choose (exists_radiusOne D hθ₁)

def radiusTwo : ℝ := Classical.choose (exists_radiusTwo D hθ₂)

theorem radiusOne_pos : 0 < radiusOne D hθ₁ := (Classical.choose_spec (exists_radiusOne D hθ₁)).1

theorem radiusOne_le : radiusOne D hθ₁ ≤ 1 :=
  (Classical.choose_spec (exists_radiusOne D hθ₁)).2.1

theorem radiusOne_spec {z : ℂ} (hz : 0 < z.im) (h : ‖coneDisc σ.vertexOne z‖ < radiusOne D hθ₁) :
    z ∈ D.U ∧ D.f z = σ.coneApexOne p₁ z ∧ σ.width / 2 < z.re ∧ z ∈ D.V 1 ∧ z ∈ D.V 2 :=
  (Classical.choose_spec (exists_radiusOne D hθ₁)).2.2 z hz h

theorem radiusTwo_pos : 0 < radiusTwo D hθ₂ := (Classical.choose_spec (exists_radiusTwo D hθ₂)).1

theorem radiusTwo_le : radiusTwo D hθ₂ ≤ 1 :=
  (Classical.choose_spec (exists_radiusTwo D hθ₂)).2.1

theorem radiusTwo_spec {z : ℂ} (hz : 0 < z.im) (h : ‖coneDisc σ.vertexTwo z‖ < radiusTwo D hθ₂) :
    z ∈ D.U ∧ D.f z = σ.coneApexTwo p₂ z ∧ |z.re| < σ.width / 2 ∧ z ∈ D.V 0 ∧ z ∈ D.V 2 :=
  (Classical.choose_spec (exists_radiusTwo D hθ₂)).2.2 z hz h

section Pieces

def discOne : Set ℂ := {z | 0 < z.im ∧ ‖coneDisc σ.vertexOne z‖ < radiusOne D hθ₁}

def discTwo : Set ℂ := {z | 0 < z.im ∧ ‖coneDisc σ.vertexTwo z‖ < radiusTwo D hθ₂}

def intT (σ : ConeShape) : Set ℂ := {z | 0 < z.im ∧ ∀ i, 0 < σ.wallSide i z}

def patchZero : Set ℂ :=
  {z | 0 < z.im ∧ z ∈ D.V 0 ∧ |z.re| < σ.width / 2 ∧ 0 < σ.wallSide 2 z ∧
    0 < σ.wallSide 2 (σ.refl 0 z) ∧ (D.f z).re < -(3 / 2) ∧
    (radiusTwo D hθ₂ < ‖coneDisc σ.vertexTwo z‖ ∨
      coneDisc σ.vertexTwo z ∈ wedgeSet (Real.pi / (2 * p₂)))}

def patchOne : Set ℂ :=
  {z | 0 < z.im ∧ z ∈ D.V 1 ∧ σ.width / 2 < z.re ∧ z.re < 3 * σ.width / 2 ∧
    0 < σ.wallSide 2 z ∧ 0 < σ.wallSide 2 (σ.refl 1 z) ∧ 3 / 2 < (D.f z).re ∧
    (radiusOne D hθ₁ < ‖coneDisc σ.vertexOne z‖ ∨
      coneDisc σ.vertexOne z ∈ wedgeSet (Real.pi / (2 * p₁)))}

def patchTwo : Set ℂ :=
  {z | 0 < z.im ∧ z ∈ D.V 2 ∧ 0 < z.re ∧ z.re < σ.width ∧ 0 < (σ.refl 2 z).re ∧
    (σ.refl 2 z).re < σ.width ∧ -(3 / 2) < (D.f z).re ∧ (D.f z).re < 3 / 2 ∧
    (radiusOne D hθ₁ < ‖coneDisc σ.vertexOne z‖ ∨
      exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z ∈ wedgeSet (Real.pi / (2 * p₁))) ∧
    (radiusTwo D hθ₂ < ‖coneDisc σ.vertexTwo z‖ ∨
      exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z ∈ wedgeSet (Real.pi / (2 * p₂)))}

def mainSet : Set ℂ := intT σ ∪ patchZero D hθ₂ ∪ patchOne D hθ₁ ∪ patchTwo D hθ₁ hθ₂

def mirrorSet (σ : ConeShape) (S : Set ℂ) : Set ℂ := {z | 0 < z.im ∧ σ.refl 0 z ∈ S}

def baseDomain : Set ℂ :=
  mainSet D hθ₁ hθ₂ ∪ mirrorSet σ (mainSet D hθ₁ hθ₂) ∪ discOne D hθ₁ ∪
    mirrorSet σ (discOne D hθ₁) ∪ discTwo D hθ₂

include hθ₁ in
theorem pi_div_le_one : Real.pi / (2 * p₁) ≤ Real.pi := by
  have hp : (1 : ℝ) ≤ p₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (p₁_ne_zero hθ₁)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

include hθ₂ in
theorem pi_div_le_two : Real.pi / (2 * p₂) ≤ Real.pi := by
  have hp : (1 : ℝ) ≤ p₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (p₂_ne_zero hθ₂)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

theorem isOpen_intT (σ : ConeShape) : IsOpen (intT σ) := by
  have : intT σ = {z : ℂ | 0 < z.im} ∩ ⋂ i, {z | 0 < σ.wallSide i z} := by
    ext z
    simp [intT]
  rw [this]
  exact isOpen_upper.inter (isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_wallSide σ i))

theorem isOpen_discOne : IsOpen (discOne D hθ₁) := by
  have := isOpen_coneDisc_preimage σ.vertexOne_im_pos (Metric.isOpen_ball (x := (0 : ℂ))
    (ε := radiusOne D hθ₁))
  simpa [discOne, Metric.mem_ball, dist_zero_right] using this

theorem isOpen_discTwo : IsOpen (discTwo D hθ₂) := by
  have hv : 0 < σ.vertexTwo.im := by
    rw [vertexTwo_im]
    have := Real.sin_pos_of_pos_of_lt_pi (θ₂_pos hθ₂) (by linarith [σ.θ₂_le, Real.pi_pos])
    positivity
  have := isOpen_coneDisc_preimage hv (Metric.isOpen_ball (x := (0 : ℂ))
    (ε := radiusTwo D hθ₂))
  simpa [discTwo, Metric.mem_ball, dist_zero_right] using this

theorem continuousAt_f {z : ℂ} (hz : z ∈ D.U) : ContinuousAt D.f z :=
  D.contDiffOn_f.continuousOn.continuousAt (D.isOpen_U.mem_nhds hz)

theorem isOpen_patchZero : IsOpen (patchZero D hθ₂) := by
  have hv : 0 < σ.vertexTwo.im := by
    rw [vertexTwo_im]
    have := Real.sin_pos_of_pos_of_lt_pi (θ₂_pos hθ₂) (by linarith [σ.θ₂_le, Real.pi_pos])
    positivity
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have hfz := continuousAt_f D (D.V_subset_U 0 h1)
  filter_upwards [isOpen_upper.mem_nhds h0, (D.isOpen_V 0).mem_nhds h1,
    (continuous_abs.comp continuous_re).continuousAt.eventually (gt_mem_nhds h2),
    (continuous_wallSide σ 2).continuousAt.eventually (lt_mem_nhds h3),
    ((continuous_wallSide σ 2).continuousAt.comp (continuousAt_refl' σ h0 0)).eventually
      (lt_mem_nhds h4),
    (continuous_re.continuousAt.comp hfz).eventually (gt_mem_nhds h5),
    eventually_wedge (continuousAt_coneDisc hv h0) (pi_div_le_two hθ₂) h6] with
    w w0 w1 w2 w3 w4 w5 w6
  exact ⟨w0, w1, w2, w3, w4, w5, w6⟩

theorem isOpen_patchOne : IsOpen (patchOne D hθ₁) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨h0, h1, h2, h2', h3, h4, h5, h6⟩
  have hfz := continuousAt_f D (D.V_subset_U 1 h1)
  filter_upwards [isOpen_upper.mem_nhds h0, (D.isOpen_V 1).mem_nhds h1,
    continuous_re.continuousAt.eventually (lt_mem_nhds h2),
    continuous_re.continuousAt.eventually (gt_mem_nhds h2'),
    (continuous_wallSide σ 2).continuousAt.eventually (lt_mem_nhds h3),
    ((continuous_wallSide σ 2).continuousAt.comp (continuousAt_refl' σ h0 1)).eventually
      (lt_mem_nhds h4),
    (continuous_re.continuousAt.comp hfz).eventually (lt_mem_nhds h5),
    eventually_wedge (continuousAt_coneDisc σ.vertexOne_im_pos h0) (pi_div_le_one hθ₁) h6] with
    w w0 w1 w2 w2' w3 w4 w5 w6
  exact ⟨w0, w1, w2, w2', w3, w4, w5, w6⟩

theorem isOpen_patchTwo : IsOpen (patchTwo D hθ₁ hθ₂) := by
  have hv : 0 < σ.vertexTwo.im := by
    rw [vertexTwo_im]
    have := Real.sin_pos_of_pos_of_lt_pi (θ₂_pos hθ₂) (by linarith [σ.θ₂_le, Real.pi_pos])
    positivity
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨h0, h1, h2, h2', h3, h3', h4, h4', h5, h6⟩
  have hfz := continuousAt_f D (D.V_subset_U 2 h1)
  have hr2 := continuousAt_refl' σ h0 2
  filter_upwards [isOpen_upper.mem_nhds h0, (D.isOpen_V 2).mem_nhds h1,
    continuous_re.continuousAt.eventually (lt_mem_nhds h2),
    continuous_re.continuousAt.eventually (gt_mem_nhds h2'),
    (continuous_re.continuousAt.comp hr2).eventually (lt_mem_nhds h3),
    (continuous_re.continuousAt.comp hr2).eventually (gt_mem_nhds h3'),
    (continuous_re.continuousAt.comp hfz).eventually (lt_mem_nhds h4),
    (continuous_re.continuousAt.comp hfz).eventually (gt_mem_nhds h4'),
    eventually_wedge2 (continuousAt_coneDisc σ.vertexOne_im_pos h0)
      (continuousAt_const.mul (continuousAt_coneDisc σ.vertexOne_im_pos h0))
      (pi_div_le_one hθ₁) h5,
    eventually_wedge2 (continuousAt_coneDisc hv h0)
      (continuousAt_const.mul (continuousAt_coneDisc hv h0)) (pi_div_le_two hθ₂) h6] with
    w w0 w1 w2 w2' w3 w3' w4 w4' w5 w6
  exact ⟨w0, w1, w2, w2', w3, w3', w4, w4', w5, w6⟩

theorem isOpen_mainSet : IsOpen (mainSet D hθ₁ hθ₂) :=
  (((isOpen_intT σ).union (isOpen_patchZero D hθ₂)).union (isOpen_patchOne D hθ₁)).union
    (isOpen_patchTwo D hθ₁ hθ₂)

theorem isOpen_mirrorSet {S : Set ℂ} (hS : IsOpen S) : IsOpen (mirrorSet σ S) := by
  have hc : Continuous (σ.refl 0) := continuous_conj.neg
  exact isOpen_upper.inter (hS.preimage hc)

theorem isOpen_baseDomain : IsOpen (baseDomain D hθ₁ hθ₂) :=
  ((((isOpen_mainSet D hθ₁ hθ₂).union (isOpen_mirrorSet (isOpen_mainSet D hθ₁ hθ₂))).union
    (isOpen_discOne D hθ₁)).union (isOpen_mirrorSet (isOpen_discOne D hθ₁))).union
    (isOpen_discTwo D hθ₂)

end Pieces

section Cover

include hθ₂ in
theorem vertexTwo_im_pos' : 0 < σ.vertexTwo.im := by
  rw [vertexTwo_im]
  have := Real.sin_pos_of_pos_of_lt_pi (θ₂_pos hθ₂) (by linarith [σ.θ₂_le, Real.pi_pos])
  positivity

theorem re_of_mem_discOne {z : ℂ} (hz : z ∈ discOne D hθ₁) : σ.width / 2 < z.re :=
  (radiusOne_spec D hθ₁ hz.1 hz.2).2.2.1

theorem re_of_mem_discTwo {z : ℂ} (hz : z ∈ discTwo D hθ₂) : |z.re| < σ.width / 2 :=
  (radiusTwo_spec D hθ₂ hz.1 hz.2).2.2.1

theorem vertexOne_mem_discOne : σ.vertexOne ∈ discOne D hθ₁ :=
  ⟨σ.vertexOne_im_pos, by rw [coneDisc_self, norm_zero]; exact radiusOne_pos D hθ₁⟩

theorem vertexTwo_mem_discTwo : σ.vertexTwo ∈ discTwo D hθ₂ :=
  ⟨vertexTwo_im_pos' hθ₂, by rw [coneDisc_self, norm_zero]; exact radiusTwo_pos D hθ₂⟩

include hθ₁ hθ₂ in
theorem triangle_subset :
    σ.triangle ⊆ mainSet D hθ₁ hθ₂ ∪ discOne D hθ₁ ∪ discTwo D hθ₂ := by
  intro z hz
  by_cases h1 : z ∈ discOne D hθ₁
  · exact Or.inl (Or.inr h1)
  by_cases h2 : z ∈ discTwo D hθ₂
  · exact Or.inr h2
  have hne1 : z ≠ σ.vertexOne := fun h => h1 (h ▸ vertexOne_mem_discOne D hθ₁)
  have hne2 : z ≠ σ.vertexTwo := fun h => h2 (h ▸ vertexTwo_mem_discTwo D hθ₂)
  left; left
  by_cases hint : ∀ i, 0 < σ.wallSide i z
  · exact Or.inl (Or.inl (Or.inl ⟨hz.1, hint⟩))
  push Not at hint
  obtain ⟨i, hi⟩ := hint
  have hi0 : σ.wallSide i z = 0 := le_antisymm hi (hz.2 i)
  have hwall : z ∈ σ.foldWall i := ⟨hz, hi0⟩
  have hfix : σ.refl i z = z := σ.refl_of_wallSide_eq_zero hz.1 hi0
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · left; left; right
    have hx : z.re = 0 := hi0
    obtain ⟨hω0, hωa⟩ := coneDisc_vertexTwo_wallZero σ hwall hne2 (θ₂_pos hθ₂)
    refine ⟨hz.1, D.foldWall_subset_V 0 hwall, by rw [hx, abs_zero]; linarith [σ.width_pos],
      wallSide_two_pos_of_wallZero σ hwall hne2, ?_,
      (re_f_of_mem_foldWall_zero D hθ₂ hwall hne2).2, Or.inr ⟨hω0, ?_⟩⟩
    · change 0 < σ.wallSide 2 (σ.refl 0 z)
      rw [hfix]
      exact wallSide_two_pos_of_wallZero σ hwall hne2
    · rw [hωa, abs_zero]
      have := pi_div_le_two hθ₂
      have hp : (0 : ℝ) < p₂ := by exact_mod_cast Nat.pos_of_ne_zero (p₂_ne_zero hθ₂)
      positivity
  · left; right
    have hx : z.re = σ.width := by change σ.width - z.re = 0 at hi0; linarith
    obtain ⟨hω0, hωa⟩ := coneDisc_vertexOne_wallOne σ hwall hne1
    refine ⟨hz.1, D.foldWall_subset_V 1 hwall, by rw [hx]; linarith [σ.width_pos],
      by rw [hx]; linarith [σ.width_pos], wallSide_two_pos_of_wallOne σ hwall hne1, ?_,
      (re_f_of_mem_foldWall_one D hθ₁ hwall hne1).1, Or.inr ⟨hω0, ?_⟩⟩
    · change 0 < σ.wallSide 2 (σ.refl 1 z)
      rw [hfix]
      exact wallSide_two_pos_of_wallOne σ hwall hne1
    · rw [hωa, abs_zero]
      have hp : (0 : ℝ) < p₁ := by exact_mod_cast Nat.pos_of_ne_zero (p₁_ne_zero hθ₁)
      positivity
  · right
    have hx0 : 0 < z.re := by
      rcases (hz.2 0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hw0 : z ∈ σ.foldWall 0 := ⟨hz, h.symm⟩
        have := wallSide_two_pos_of_wallZero σ hw0 hne2
        change σ.wallSide 2 z = 0 at hi0
        linarith
    have hx1 : z.re < σ.width := by
      rcases (hz.2 1).lt_or_eq with h | h
      · change 0 < σ.width - z.re at h; linarith
      · exfalso
        have hw1 : z ∈ σ.foldWall 1 := ⟨hz, h.symm⟩
        have := wallSide_two_pos_of_wallOne σ hw1 hne1
        change σ.wallSide 2 z = 0 at hi0
        linarith
    obtain ⟨t₁, ht₁, he₁⟩ := rot_coneDisc_one_of_wallTwo σ hwall hx1
    obtain ⟨t₂, ht₂, he₂⟩ := xi_of_wallTwo σ hwall hx0 (θ₂_pos hθ₂)
    have hp₁ : (0 : ℝ) < p₁ := by exact_mod_cast Nat.pos_of_ne_zero (p₁_ne_zero hθ₁)
    have hp₂ : (0 : ℝ) < p₂ := by exact_mod_cast Nat.pos_of_ne_zero (p₂_ne_zero hθ₂)
    have hre := re_f_of_mem_foldWall_two D hθ₁ hθ₂ hwall hne1 hne2
    refine ⟨hz.1, D.foldWall_subset_V 2 hwall, hx0, hx1, by rw [hfix]; exact hx0,
      by rw [hfix]; exact hx1, hre.1, hre.2, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [he₁]; exact_mod_cast ht₁.ne'
    · rw [he₁, arg_ofReal_of_nonneg ht₁.le, abs_zero]; positivity
    · rw [he₂]; exact_mod_cast ht₂.ne'
    · rw [he₂, arg_ofReal_of_nonneg ht₂.le, abs_zero]; positivity

end Cover

section Sectors

include hθ₁ in
theorem sector_one {z : ℂ} (hm : z ∈ mainSet D hθ₁ hθ₂) (hd : z ∈ discOne D hθ₁) :
    coneDisc σ.vertexOne z ≠ 0 ∧ -(Real.pi / 2) < p₁ * arg (coneDisc σ.vertexOne z) ∧
      p₁ * arg (coneDisc σ.vertexOne z) < 3 * Real.pi / 2 := by
  have hp : (0 : ℝ) < p₁ := by exact_mod_cast Nat.pos_of_ne_zero (p₁_ne_zero hθ₁)
  have hθp : p₁ * σ.θ₁ = Real.pi := by rw [mul_comm]; exact hθ₁
  have hx := re_of_mem_discOne D hθ₁ hd
  rcases hm with ((hm | hm) | hm) | hm
  · obtain ⟨h0, hw⟩ := hm
    obtain ⟨ha, hb⟩ := arg_coneDisc_one_of_sides σ h0 (hw 1) (hw 2)
    refine ⟨fun h => by rw [h, arg_zero] at ha; exact lt_irrefl _ ha, by nlinarith, ?_⟩
    nlinarith [Real.pi_pos]
  · have := hm.2.2.1
    rw [abs_lt] at this
    linarith
  · rcases hm.2.2.2.2.2.2.2 with h | ⟨hne, ha⟩
    · exact absurd hd.2 (not_lt.mpr h.le)
    · rw [abs_lt] at ha
      have h1 : p₁ * (Real.pi / (2 * p₁)) = Real.pi / 2 := by field_simp
      refine ⟨hne, by nlinarith, by nlinarith [Real.pi_pos]⟩
  · rcases hm.2.2.2.2.2.2.2.2.1 with h | ⟨hne, ha⟩
    · exact absurd hd.2 (not_lt.mpr h.le)
    · have hne' : coneDisc σ.vertexOne z ≠ 0 := by
        intro h; apply hne; rw [h, mul_zero]
      rw [abs_lt] at ha
      have h1 : p₁ * (Real.pi / (2 * p₁)) = Real.pi / 2 := by field_simp
      have hπ2 : Real.pi / (2 * p₁) ≤ Real.pi / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (1 : ℝ) ≤ p₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (p₁_ne_zero hθ₁)
        nlinarith [Real.pi_pos]
      have heq : arg (exp ((σ.θ₁ : ℝ) * I) * (exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z)) =
          σ.θ₁ + arg (exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z) :=
        arg_exp_mul_of_mem hne (by linarith [σ.θ₁_pos, Real.pi_pos])
          (by linarith [σ.θ₁_le, Real.pi_pos])
      rw [← mul_assoc, ← exp_add, show (σ.θ₁ : ℂ) * I + -(σ.θ₁ * I) = 0 by ring, exp_zero,
        one_mul] at heq
      rw [heq]
      refine ⟨hne', by nlinarith, by nlinarith⟩

include hθ₂ in
theorem sector_two {z : ℂ} (hm : z ∈ mainSet D hθ₁ hθ₂) (hd : z ∈ discTwo D hθ₂) :
    exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z ≠ 0 ∧
      -(Real.pi / 2) < p₂ * arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) ∧
      p₂ * arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) < 3 * Real.pi / 2 := by
  have hp : (0 : ℝ) < p₂ := by exact_mod_cast Nat.pos_of_ne_zero (p₂_ne_zero hθ₂)
  have hθp : p₂ * σ.θ₂ = Real.pi := by rw [mul_comm]; exact hθ₂
  have hx := re_of_mem_discTwo D hθ₂ hd
  have h1 : p₂ * (Real.pi / (2 * p₂)) = Real.pi / 2 := by field_simp
  have hπ2 : Real.pi / (2 * p₂) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ p₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (p₂_ne_zero hθ₂)
    nlinarith [Real.pi_pos]
  rcases hm with ((hm | hm) | hm) | hm
  · obtain ⟨h0, hw⟩ := hm
    obtain ⟨ha, hb⟩ := arg_xi_of_sides σ h0 (θ₂_pos hθ₂) (hw 0) (hw 2)
    refine ⟨fun h => by rw [h, arg_zero] at ha; exact lt_irrefl _ ha, by nlinarith, ?_⟩
    nlinarith [Real.pi_pos]
  · rcases hm.2.2.2.2.2.2 with h | ⟨hne, ha⟩
    · exact absurd hd.2 (not_lt.mpr h.le)
    · rw [abs_lt] at ha
      have heq : arg (exp ((σ.θ₂ : ℝ) * I) * coneDisc σ.vertexTwo z) =
          σ.θ₂ + arg (coneDisc σ.vertexTwo z) :=
        arg_exp_mul_of_mem hne (by linarith [σ.θ₂_nonneg, Real.pi_pos])
          (by linarith [σ.θ₂_le, Real.pi_pos])
      have hne' : exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z ≠ 0 :=
        mul_ne_zero (exp_ne_zero _) hne
      rw [heq]
      refine ⟨hne', by nlinarith, by nlinarith⟩
  · have := hm.2.2.1
    rw [abs_lt] at hx
    linarith
  · rcases hm.2.2.2.2.2.2.2.2.2 with h | ⟨hne, ha⟩
    · exact absurd hd.2 (not_lt.mpr h.le)
    · rw [abs_lt] at ha
      exact ⟨hne, by nlinarith, by nlinarith [Real.pi_pos]⟩

end Sectors

end Fold

end TwoConeFold

end GC.Seifert
