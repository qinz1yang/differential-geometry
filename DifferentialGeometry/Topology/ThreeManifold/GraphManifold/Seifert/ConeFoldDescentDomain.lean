import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentIsometry

/-!
# The domain of the cone-fold descent

For the one-cone shape (`θ₂ = 0`, `θ₁ p = π`) the descent domain is built from five open patches
of the upper half-plane: the open triangle `patchInt`, a `σ₀`-stable band `patchZero` about wall 0
(inside `V 0` and the region where the fibre phase is `1`), a `σ₁`-stable band `patchOne` about
wall 1 and a `σ₂`-stable band `patchTwo` about wall 2 (inside `V i` and the region where the phase
is `unitOf ω ^ q`), and the disc `patchDisc = {‖ω_v‖ < r}` about the apex, on which `f` is the
branched model, the phase is `unitOf ω ^ q` and `Re z > 0` (`discRadius`). Their union `patches`
contains the closed triangle (`triangle_subset_patches`); `descentBase` adds the mirror image under
`σ₀`, and `descentDomain` is its preimage in the log coordinates of `ModelCoordinates`. Off the
disc, every point of `patches` with `Re z ≥ 0` lies in `U`, is not the apex, and `f` maps it into
the filled base minus the cone point (`patches_good`): it lies in the triangle or is reflected
into it by `σ₁`, `σ₂` inside `V 1`, `V 2`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

theorem wallSide_continuous (i : Fin 3) : Continuous (σ.wallSide i) := by
  fin_cases i
  · exact continuous_re
  · exact continuous_const.sub continuous_re
  · change Continuous fun z : ℂ => (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16
    fun_prop

private theorem continuousAt_refl_of_im_pos {z : ℂ} (hz : 0 < z.im) (i : Fin 3) :
    ContinuousAt (σ.refl i) z := by
  fin_cases i
  · change ContinuousAt (fun z : ℂ => -conj z) z
    exact (continuous_conj.neg).continuousAt
  · change ContinuousAt (fun z : ℂ => 2 * (σ.width : ℂ) - conj z) z
    exact (continuous_const.sub continuous_conj).continuousAt
  · change ContinuousAt (fun z : ℂ => (σ.centre : ℂ) + 1 / 16 / (conj z - σ.centre)) z
    exact continuousAt_const.add (continuousAt_const.div
      (continuous_conj.continuousAt.sub continuousAt_const) (σ.conj_centre_ne hz))

theorem re_refl_zero (z : ℂ) : (σ.refl 0 z).re = -z.re := by simp [refl]

theorem im_refl_zero (z : ℂ) : (σ.refl 0 z).im = z.im := by simp [refl]

theorem re_refl_one (z : ℂ) : (σ.refl 1 z).re = 2 * σ.width - z.re := by simp [refl]

private theorem vertexOne_circle : (σ.width - σ.centre) ^ 2 + σ.vertexOne.im ^ 2 = 1 / 16 := by
  rw [vertexOne_im]
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  unfold width centre
  linear_combination hs / 16

theorem wallSide_one_vertexOne_eq_zero : σ.wallSide 1 σ.vertexOne = 0 := by
  simp [wallSide, vertexOne_re]

private theorem wallSide_two_vertexOne : σ.wallSide 2 σ.vertexOne = 0 := by
  simp only [wallSide, vertexOne_re]
  linarith [σ.vertexOne_circle]

private theorem vertexOne_mem_triangle : σ.vertexOne ∈ σ.triangle := by
  refine ⟨σ.vertexOne_im_pos, fun i => ?_⟩
  fin_cases i
  · simp only [wallSide, vertexOne_re]
    exact σ.width_pos.le
  · exact (σ.wallSide_one_vertexOne_eq_zero).ge
  · exact (σ.wallSide_two_vertexOne).ge

theorem descentWidth_lt_half : σ.width < 1 / 2 := by
  have h1 : Real.cos σ.θ₁ < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl σ.θ₁_le σ.θ₁_pos
  have h2 := Real.cos_le_one σ.θ₂
  unfold width
  linarith

theorem eq_vertexOne_of_re_eq {z : ℂ} (hz : 0 < z.im) (hx : z.re = σ.width)
    (hw : σ.wallSide 2 z = 0) : z = σ.vertexOne := by
  have hc := σ.vertexOne_circle
  have hv := σ.vertexOne_im_pos
  simp only [wallSide, hx] at hw
  have h : z.im = σ.vertexOne.im := by nlinarith
  exact Complex.ext (by rw [hx, vertexOne_re]) h

theorem wallSide_two_pos_of_re_eq {z : ℂ} (hz : 0 < z.im) (hx : z.re = σ.width)
    (hw : 0 ≤ σ.wallSide 2 z) (hv : z ≠ σ.vertexOne) : 0 < σ.wallSide 2 z :=
  lt_of_le_of_ne hw fun h => hv (σ.eq_vertexOne_of_re_eq hz hx h.symm)

theorem coneDisc_mem_slitPlane_of_re_eq {z : ℂ} (hz : 0 < z.im) (hx : z.re = σ.width)
    (hw : 0 < σ.wallSide 2 z) : coneDisc σ.vertexOne z ∈ slitPlane := by
  have hc := σ.vertexOne_circle
  have hv := σ.vertexOne_im_pos
  have hy : σ.vertexOne.im < z.im := by
    simp only [wallSide, hx] at hw
    nlinarith
  have hzv : z - σ.vertexOne = ((z.im - σ.vertexOne.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hx, vertexOne_re]
  have hzc : z - conj σ.vertexOne = ((z.im + σ.vertexOne.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hx, vertexOne_re]
  have hpos : 0 < z.im + σ.vertexOne.im := by linarith
  have he : coneDisc σ.vertexOne z =
      (((z.im - σ.vertexOne.im) / (z.im + σ.vertexOne.im) : ℝ) : ℂ) := by
    rw [coneDisc, hzv, hzc, mul_div_mul_right _ _ I_ne_zero, ← Complex.ofReal_div]
  rw [he]
  exact ofReal_mem_slitPlane.2 (div_pos (by linarith) hpos)

theorem coneDisc_vertexOne_mem_slitPlane' {z : ℂ} (hx : z.re < σ.width) :
    coneDisc σ.vertexOne z ∈ slitPlane :=
  σ.coneDisc_mem_slitPlane hx.ne

def patchInt : Set ℂ := {z | 0 < z.im ∧ ∀ i, 0 < σ.wallSide i z}

theorem patchInt_subset_triangle : σ.patchInt ⊆ σ.triangle :=
  fun _ hz => ⟨hz.1, fun i => (hz.2 i).le⟩

theorem isOpen_patchInt : IsOpen σ.patchInt := by
  have : σ.patchInt = {z | 0 < z.im} ∩ ⋂ i, {z | 0 < σ.wallSide i z} := by
    ext z
    simp [patchInt]
  rw [this]
  exact (isOpen_lt continuous_const continuous_im).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (σ.wallSide_continuous i))

theorem re_pos_of_mem_patchInt {z : ℂ} (hz : z ∈ σ.patchInt) : 0 < z.re := hz.2 0

theorem ne_vertexOne_of_mem_patchInt {z : ℂ} (hz : z ∈ σ.patchInt) : z ≠ σ.vertexOne := by
  rintro rfl
  have := hz.2 1
  rw [σ.wallSide_one_vertexOne_eq_zero] at this
  exact lt_irrefl _ this

end ConeShape

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

theorem f_vertexOne (hθ : σ.θ₁ * c.p = Real.pi) : D.f σ.vertexOne = 3 / 2 := by
  have h := (D.f_apexOne c.p hθ).self_of_nhds
  rw [h, σ.coneApexOne_vertexOne (NeZero.ne c.p)]

theorem f_mem_basePlus {z : ℂ} (hz : z ∈ σ.triangle) : D.f z ∈ σ.basePlus :=
  D.bijOn_f.mapsTo hz

theorem f_ne_of_mem_triangle (hθ : σ.θ₁ * c.p = Real.pi) {z : ℂ} (hz : z ∈ σ.triangle)
    (hv : z ≠ σ.vertexOne) :
    D.f z ≠ 3 / 2 := by
  intro h
  apply hv
  exact D.bijOn_f.injOn hz σ.vertexOne_mem_triangle (h.trans (D.f_vertexOne c hθ).symm)

theorem f_mem_filledBase_of_mem_triangle (hσ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.triangle) :
    D.f z ∈ filledBase :=
  basePlus_subset_filledBase σ hσ (D.f_mem_basePlus hz)

theorem f_good_of_refl (hθ : σ.θ₁ * c.p = Real.pi) (hσ : σ.θ₂ = 0) {i : Fin 3} {z : ℂ}
    (hzV : z ∈ D.V i)
    (hT : σ.refl i z ∈ σ.triangle) (hv : σ.refl i z ≠ σ.vertexOne) :
    D.f z ∈ filledBase ∧ D.f z ≠ 3 / 2 := by
  rw [D.f_refl' hzV]
  refine ⟨conj_mem_filledBase (D.f_mem_filledBase_of_mem_triangle hσ hT), fun h => ?_⟩
  apply D.f_ne_of_mem_triangle c hθ hT hv
  have := congrArg conj h
  rw [Complex.conj_conj] at this
  rw [this]
  simp only [map_div₀, map_ofNat]

theorem exists_discRadius (hθ : σ.θ₁ * c.p = Real.pi) : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z : ℂ, 0 < z.im →
    ‖coneDisc σ.vertexOne z‖ < r →
      z ∈ D.U ∧ D.f z = σ.coneApexOne c.p z ∧ z ∈ σ.foldFar ∧ 0 < z.re := by
  set v := σ.vertexOne
  have hv := σ.vertexOne_im_pos
  have hS : {z : ℂ | z ∈ D.U ∧ D.f z = σ.coneApexOne c.p z ∧ z ∈ σ.foldFar ∧ 0 < z.re} ∈ 𝓝 v := by
    have h1 : D.U ∈ 𝓝 v := D.isOpen_U.mem_nhds (D.triangle_subset_U σ.vertexOne_mem_triangle)
    have h2 := D.f_apexOne c.p hθ
    have h3 : σ.foldFar ∈ 𝓝 v := σ.isOpen_foldFar.mem_nhds σ.vertexOne_mem_foldFar
    have h4 : {z : ℂ | 0 < z.re} ∈ 𝓝 v :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        change 0 < σ.vertexOne.re
        rw [vertexOne_re]
        exact σ.width_pos)
    filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
    exact ⟨hz1, hz2, hz3, hz4⟩
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

def discRadius : ℝ := Classical.choose (D.exists_discRadius c hθ)

theorem discRadius_pos : 0 < D.discRadius c hθ :=
  (Classical.choose_spec (D.exists_discRadius c hθ)).1

theorem discRadius_le_one : D.discRadius c hθ ≤ 1 :=
  (Classical.choose_spec (D.exists_discRadius c hθ)).2.1

theorem discRadius_spec {z : ℂ} (hz : 0 < z.im)
    (hω : ‖coneDisc σ.vertexOne z‖ < D.discRadius c hθ) :
    z ∈ D.U ∧ D.f z = σ.coneApexOne c.p z ∧ z ∈ σ.foldFar ∧ 0 < z.re :=
  (Classical.choose_spec (D.exists_discRadius c hθ)).2.2 z hz hω

def patchZero : Set ℂ :=
  {z | 0 < z.im ∧ |z.re| < σ.width ∧ 0 < σ.wallSide 2 z ∧ 0 < σ.wallSide 2 (σ.refl 0 z) ∧
    z ∈ D.V 0 ∧ |foldSplit z| < σ.width / 3}

def patchOne : Set ℂ :=
  {z | 0 < z.im ∧ 0 < z.re ∧ z.re < 2 * σ.width ∧ 0 < σ.wallSide 2 z ∧
    0 < σ.wallSide 2 (σ.refl 1 z) ∧ z ∈ D.V 1 ∧ z ∈ σ.foldFar ∧ σ.refl 1 z ∈ σ.foldFar}

def patchTwo : Set ℂ :=
  {z | 0 < z.im ∧ 0 < z.re ∧ z.re < σ.width ∧ 0 < (σ.refl 2 z).re ∧
    (σ.refl 2 z).re < σ.width ∧ z ∈ D.V 2 ∧ z ∈ σ.foldFar ∧ σ.refl 2 z ∈ σ.foldFar}

def patchDisc : Set ℂ := {z | 0 < z.im ∧ ‖coneDisc σ.vertexOne z‖ < D.discRadius c hθ}

def patches : Set ℂ := σ.patchInt ∪ D.patchZero ∪ D.patchOne ∪ D.patchTwo ∪ D.patchDisc c hθ

def descentBase : Set ℂ := {z | z ∈ D.patches c hθ ∨ σ.refl 0 z ∈ D.patches c hθ}

theorem isOpen_patchZero : IsOpen D.patchZero := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, h1, h2, h3, h4, h5⟩
  have hz0 : z ≠ 0 := ConeShape.ne_zero_of_im_pos hz
  have e1 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz
  have e2 : ∀ᶠ w in 𝓝 z, |w.re| < σ.width :=
    (continuous_abs.comp continuous_re).continuousAt.eventually_lt continuousAt_const h1
  have e3 : ∀ᶠ w in 𝓝 z, 0 < σ.wallSide 2 w :=
    continuousAt_const.eventually_lt (σ.wallSide_continuous 2).continuousAt h2
  have e4 : ∀ᶠ w in 𝓝 z, 0 < σ.wallSide 2 (σ.refl 0 w) :=
    continuousAt_const.eventually_lt
      ((σ.wallSide_continuous 2).continuousAt.comp (σ.continuousAt_refl_of_im_pos hz 0)) h3
  have e5 : D.V 0 ∈ 𝓝 z := (D.isOpen_V 0).mem_nhds h4
  have e6 : ∀ᶠ w in 𝓝 z, |foldSplit w| < σ.width / 3 :=
    (continuous_abs.continuousAt.comp (ConeShape.continuousAt_foldSplit hz0)).eventually_lt
      continuousAt_const h5
  filter_upwards [e1, e2, e3, e4, e5, e6] with w hw1 hw2 hw3 hw4 hw5 hw6
  exact ⟨hw1, hw2, hw3, hw4, hw5, hw6⟩

theorem isOpen_patchOne : IsOpen D.patchOne := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, h1, h2, h3, h4, h5, h6, h7⟩
  have e1 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz
  have e2 : ∀ᶠ w in 𝓝 z, 0 < w.re := continuousAt_const.eventually_lt continuous_re.continuousAt h1
  have e3 : ∀ᶠ w in 𝓝 z, w.re < 2 * σ.width :=
    continuous_re.continuousAt.eventually_lt continuousAt_const h2
  have e4 : ∀ᶠ w in 𝓝 z, 0 < σ.wallSide 2 w :=
    continuousAt_const.eventually_lt (σ.wallSide_continuous 2).continuousAt h3
  have e5 : ∀ᶠ w in 𝓝 z, 0 < σ.wallSide 2 (σ.refl 1 w) :=
    continuousAt_const.eventually_lt
      ((σ.wallSide_continuous 2).continuousAt.comp (σ.continuousAt_refl_of_im_pos hz 1)) h4
  have e6 : D.V 1 ∈ 𝓝 z := (D.isOpen_V 1).mem_nhds h5
  have e7 : σ.foldFar ∈ 𝓝 z := σ.isOpen_foldFar.mem_nhds h6
  have e8 : ∀ᶠ w in 𝓝 z, σ.refl 1 w ∈ σ.foldFar :=
    (σ.continuousAt_refl_of_im_pos hz 1).preimage_mem_nhds (σ.isOpen_foldFar.mem_nhds h7)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8] with w hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
  exact ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8⟩

theorem isOpen_patchTwo : IsOpen D.patchTwo := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, h1, h2, h3, h4, h5, h6, h7⟩
  have hr : ContinuousAt (fun w => (σ.refl 2 w).re) z :=
    continuous_re.continuousAt.comp (σ.continuousAt_refl_of_im_pos hz 2)
  have e1 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz
  have e2 : ∀ᶠ w in 𝓝 z, 0 < w.re := continuousAt_const.eventually_lt continuous_re.continuousAt h1
  have e3 : ∀ᶠ w in 𝓝 z, w.re < σ.width :=
    continuous_re.continuousAt.eventually_lt continuousAt_const h2
  have e4 : ∀ᶠ w in 𝓝 z, 0 < (σ.refl 2 w).re := continuousAt_const.eventually_lt hr h3
  have e5 : ∀ᶠ w in 𝓝 z, (σ.refl 2 w).re < σ.width := hr.eventually_lt continuousAt_const h4
  have e6 : D.V 2 ∈ 𝓝 z := (D.isOpen_V 2).mem_nhds h5
  have e7 : σ.foldFar ∈ 𝓝 z := σ.isOpen_foldFar.mem_nhds h6
  have e8 : ∀ᶠ w in 𝓝 z, σ.refl 2 w ∈ σ.foldFar :=
    (σ.continuousAt_refl_of_im_pos hz 2).preimage_mem_nhds (σ.isOpen_foldFar.mem_nhds h7)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8] with w hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
  exact ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8⟩

theorem isOpen_patchDisc : IsOpen (D.patchDisc c hθ) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, h1⟩
  have e1 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz
  have hcd : ContinuousAt (coneDisc σ.vertexOne) z :=
    (contDiffAt_coneDisc σ.vertexOne_im_pos hz).continuousAt
  have e2 : ∀ᶠ w in 𝓝 z, ‖coneDisc σ.vertexOne w‖ < D.discRadius c hθ :=
    (continuous_norm.continuousAt.comp hcd).eventually_lt continuousAt_const h1
  filter_upwards [e1, e2] with w hw1 hw2
  exact ⟨hw1, hw2⟩

theorem isOpen_patches : IsOpen (D.patches c hθ) :=
  ((((σ.isOpen_patchInt.union D.isOpen_patchZero).union D.isOpen_patchOne).union
    D.isOpen_patchTwo).union (D.isOpen_patchDisc c hθ))

theorem im_pos_of_mem_patches {z : ℂ} (hz : z ∈ D.patches c hθ) : 0 < z.im := by
  rcases hz with (((h | h) | h) | h) | h
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

theorem isOpen_descentBase : IsOpen (D.descentBase c hθ) := by
  rw [isOpen_iff_mem_nhds]
  rintro z (hz | hz)
  · exact Filter.mem_of_superset ((D.isOpen_patches c hθ).mem_nhds hz) fun w hw => Or.inl hw
  · have hz0 : 0 < z.im := by
      have := D.im_pos_of_mem_patches c hθ hz
      rwa [σ.im_refl_zero] at this
    exact Filter.mem_of_superset ((σ.continuousAt_refl_of_im_pos hz0 0).preimage_mem_nhds
      ((D.isOpen_patches c hθ).mem_nhds hz)) fun w hw => Or.inr hw

def descentDomain : TopologicalSpace.Opens ModelCoordinates :=
  ⟨{p | (logPoint p : ℂ) ∈ D.descentBase c hθ},
    (D.isOpen_descentBase c hθ).preimage contDiff_coe_logPoint.continuous⟩

theorem mem_descentDomain {p : ModelCoordinates} :
    p ∈ D.descentDomain c hθ ↔ (logPoint p : ℂ) ∈ D.descentBase c hθ :=
  Iff.rfl

theorem refl_zero_mem_patchZero {z : ℂ} (hz : z ∈ D.patchZero) : σ.refl 0 z ∈ D.patchZero := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hz
  refine ⟨by rwa [σ.im_refl_zero], by rwa [σ.re_refl_zero, abs_neg], h3, ?_,
    D.refl_mapsTo_V 0 h4, by rwa [σ.foldSplit_refl_zero, abs_neg]⟩
  rwa [σ.refl_refl h0 0]

theorem refl_one_mem_patchOne {z : ℂ} (hz : z ∈ D.patchOne) : σ.refl 1 z ∈ D.patchOne := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hz
  refine ⟨by rwa [σ.refl_one_im], by rw [σ.re_refl_one]; linarith,
    by rw [σ.re_refl_one]; linarith, h4, by rwa [σ.refl_refl h0 1], D.refl_mapsTo_V 1 h5, h7,
    by rwa [σ.refl_refl h0 1]⟩

theorem refl_two_mem_patchTwo {z : ℂ} (hz : z ∈ D.patchTwo) : σ.refl 2 z ∈ D.patchTwo := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hz
  refine ⟨σ.refl_im_pos h0 2, h3, h4, by rwa [σ.refl_refl h0 2], by rwa [σ.refl_refl h0 2],
    D.refl_mapsTo_V 2 h5, h7, by rwa [σ.refl_refl h0 2]⟩

theorem re_pos_of_mem_patchDisc {z : ℂ} (hz : z ∈ D.patchDisc c hθ) : 0 < z.re :=
  (D.discRadius_spec c hθ hz.1 hz.2).2.2.2

theorem mem_patchZero_of_re_nonpos {z : ℂ} (hz : z ∈ D.patches c hθ) (hre : z.re ≤ 0) :
    z ∈ D.patchZero := by
  rcases hz with (((h | h) | h) | h) | h
  · exact absurd (σ.re_pos_of_mem_patchInt h) (not_lt.2 hre)
  · exact h
  · exact absurd h.2.1 (not_lt.2 hre)
  · exact absurd h.2.1 (not_lt.2 hre)
  · exact absurd (D.re_pos_of_mem_patchDisc c hθ h) (not_lt.2 hre)

theorem mem_patches_of_mem_descentBase {z : ℂ} (hz : z ∈ D.descentBase c hθ) (hre : 0 ≤ z.re) :
    z ∈ D.patches c hθ := by
  rcases hz with hz | hz
  · exact hz
  · have h0 : (σ.refl 0 z).re ≤ 0 := by rw [σ.re_refl_zero]; linarith
    have h1 := D.refl_zero_mem_patchZero (D.mem_patchZero_of_re_nonpos c hθ hz h0)
    have hz0 : 0 < z.im := by
      have := D.im_pos_of_mem_patches c hθ hz
      rwa [σ.im_refl_zero] at this
    rw [σ.refl_refl hz0 0] at h1
    exact Or.inl (Or.inl (Or.inl (Or.inr h1)))

theorem refl_mem_patches_of_mem_descentBase {z : ℂ} (hz : z ∈ D.descentBase c hθ)
    (hre : z.re ≤ 0) : σ.refl 0 z ∈ D.patches c hθ := by
  rcases hz with hz | hz
  · exact Or.inl (Or.inl (Or.inl (Or.inr
      (D.refl_zero_mem_patchZero (D.mem_patchZero_of_re_nonpos c hθ hz hre)))))
  · exact hz

theorem im_pos_of_mem_descentBase {z : ℂ} (hz : z ∈ D.descentBase c hθ) : 0 < z.im := by
  rcases hz with hz | hz
  · exact D.im_pos_of_mem_patches c hθ hz
  · have := D.im_pos_of_mem_patches c hθ hz
    rwa [σ.im_refl_zero] at this

theorem refl_zero_mem_descentBase {z : ℂ} (hz : z ∈ D.descentBase c hθ) :
    σ.refl 0 z ∈ D.descentBase c hθ := by
  have hz0 := D.im_pos_of_mem_descentBase c hθ hz
  rcases hz with hz | hz
  · exact Or.inr (by rwa [σ.refl_refl hz0 0])
  · exact Or.inl hz

theorem vertexOne_mem_patchDisc : σ.vertexOne ∈ D.patchDisc c hθ :=
  ⟨σ.vertexOne_im_pos, by rw [coneDisc_self, norm_zero]; exact D.discRadius_pos c hθ⟩

theorem triangle_subset_patches (hσ : σ.θ₂ = 0) : σ.triangle ⊆ D.patches c hθ := by
  intro z hz
  have hc := σ.cusp_centre hσ
  obtain ⟨hz0, hw⟩ := hz
  by_cases hint : ∀ i, 0 < σ.wallSide i z
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hz0, hint⟩)))
  push Not at hint
  obtain ⟨i, hi⟩ := hint
  have hi0 : σ.wallSide i z = 0 := le_antisymm hi (hw i)
  have hT : z ∈ σ.triangle := ⟨hz0, hw⟩
  have hx0 : 0 ≤ z.re := hw 0
  have hxW : z.re ≤ σ.width := by have := hw 1; simp only [wallSide] at this; linarith
  by_cases hzv : z = σ.vertexOne
  · rw [hzv]
    exact Or.inr (D.vertexOne_mem_patchDisc c hθ)
  fin_cases i
  · have hx : z.re = 0 := hi0
    have hw2 : 0 < σ.wallSide 2 z := by
      simp only [wallSide, hx, hc]
      nlinarith
    refine Or.inl (Or.inl (Or.inl (Or.inr ⟨hz0, ?_, hw2, ?_, ?_, ?_⟩)))
    · rw [hx, abs_zero]
      exact σ.width_pos
    · simp only [wallSide, re_refl_zero, im_refl_zero, hx, hc]
      nlinarith
    · exact D.foldWall_subset_V 0 ⟨hT, hi0⟩
    · simp only [foldSplit, hx, zero_mul, abs_zero]
      exact div_pos σ.width_pos (by norm_num)
  · have hx : z.re = σ.width := by
      have h := hi0
      simp only [wallSide] at h
      linarith
    have hw2 : 0 < σ.wallSide 2 z := σ.wallSide_two_pos_of_re_eq hz0 hx (hw 2) hzv
    have hfix : σ.refl 1 z = z := σ.refl_of_wallSide_eq_zero hz0 hi0
    have hfar : z ∈ σ.foldFar := σ.mem_foldFar_of_le_re hz0 hx.ge
    refine Or.inl (Or.inl (Or.inr ⟨hz0, by rw [hx]; exact σ.width_pos, by rw [hx]; linarith
      [σ.width_pos], hw2, by rwa [hfix], D.foldWall_subset_V 1 ⟨hT, hi0⟩, hfar,
      by rwa [hfix]⟩))
  · have hfix : σ.refl 2 z = z := σ.refl_of_wallSide_eq_zero hz0 hi0
    have hxpos : 0 < z.re := by
      rcases hx0.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 := hi0
        simp only [wallSide, ← h, hc] at h2
        nlinarith
    have hxlt : z.re < σ.width := by
      rcases hxW.lt_or_eq with h | h
      · exact h
      · exact absurd (σ.eq_vertexOne_of_re_eq hz0 h hi0) hzv
    have hfar : z ∈ σ.foldFar := σ.mem_foldFar_of_wallSide_two hσ hz0 hi0
    refine Or.inl (Or.inr ⟨hz0, hxpos, hxlt, by rwa [hfix], by rwa [hfix],
      D.foldWall_subset_V 2 ⟨hT, hi0⟩, hfar, by rwa [hfix]⟩)

theorem mem_triangle_of_mem_patchZero {z : ℂ} (hz : z ∈ D.patchZero) (hre : 0 ≤ z.re) :
    z ∈ σ.triangle := by
  refine ⟨hz.1, fun i => ?_⟩
  fin_cases i
  · exact hre
  · have h := hz.2.1
    simp only [wallSide]
    linarith [le_abs_self z.re]
  · exact hz.2.2.1.le

theorem ne_vertexOne_of_mem_patchZero {z : ℂ} (hz : z ∈ D.patchZero) : z ≠ σ.vertexOne := by
  rintro rfl
  have h := hz.2.1
  rw [vertexOne_re, abs_of_pos σ.width_pos] at h
  exact lt_irrefl _ h

theorem mem_triangle_of_mem_patchOne {z : ℂ} (hz : z ∈ D.patchOne) (hre : z.re ≤ σ.width) :
    z ∈ σ.triangle := by
  refine ⟨hz.1, fun i => ?_⟩
  fin_cases i
  · exact hz.2.1.le
  · simp only [wallSide]
    linarith
  · exact hz.2.2.2.1.le

theorem refl_mem_triangle_of_mem_patchOne {z : ℂ} (hz : z ∈ D.patchOne) (hre : σ.width ≤ z.re) :
    σ.refl 1 z ∈ σ.triangle := by
  refine ⟨σ.refl_im_pos hz.1 1, fun i => ?_⟩
  fin_cases i
  · simp only [wallSide, re_refl_one]
    linarith [hz.2.2.1]
  · simp only [wallSide, re_refl_one]
    linarith
  · exact hz.2.2.2.2.1.le

theorem ne_vertexOne_of_mem_patchOne {z : ℂ} (hz : z ∈ D.patchOne) : z ≠ σ.vertexOne := by
  rintro rfl
  have h := hz.2.2.2.1
  rw [σ.wallSide_two_vertexOne] at h
  exact lt_irrefl _ h

theorem refl_ne_vertexOne_of_mem_patchOne {z : ℂ} (hz : z ∈ D.patchOne) :
    σ.refl 1 z ≠ σ.vertexOne :=
  D.ne_vertexOne_of_mem_patchOne (D.refl_one_mem_patchOne hz)

theorem mem_triangle_of_mem_patchTwo {z : ℂ} (hz : z ∈ D.patchTwo) (hw : 0 ≤ σ.wallSide 2 z) :
    z ∈ σ.triangle := by
  refine ⟨hz.1, fun i => ?_⟩
  fin_cases i
  · exact hz.2.1.le
  · simp only [wallSide]
    linarith [hz.2.2.1]
  · exact hw

theorem refl_mem_triangle_of_mem_patchTwo {z : ℂ} (hz : z ∈ D.patchTwo)
    (hw : σ.wallSide 2 z ≤ 0) : σ.refl 2 z ∈ σ.triangle := by
  refine ⟨σ.refl_im_pos hz.1 2, fun i => ?_⟩
  fin_cases i
  · exact hz.2.2.2.1.le
  · simp only [wallSide]
    linarith [hz.2.2.2.2.1]
  · change 0 ≤ σ.wallSide 2 (σ.refl 2 z)
    rw [σ.wallSide_refl_two hz.1]
    have := normSq_pos.2 (σ.centre_ne hz.1)
    apply div_nonneg (by linarith) (by positivity)

theorem ne_vertexOne_of_mem_patchTwo {z : ℂ} (hz : z ∈ D.patchTwo) : z ≠ σ.vertexOne := by
  rintro rfl
  have h := hz.2.2.1
  rw [vertexOne_re] at h
  exact lt_irrefl _ h

theorem refl_ne_vertexOne_of_mem_patchTwo {z : ℂ} (hz : z ∈ D.patchTwo) :
    σ.refl 2 z ≠ σ.vertexOne :=
  D.ne_vertexOne_of_mem_patchTwo (D.refl_two_mem_patchTwo hz)

theorem patches_good (hσ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ D.patches c hθ) (hre : 0 ≤ z.re)
    (hd : z ∉ D.patchDisc c hθ) :
    z ∈ D.U ∧ z ≠ σ.vertexOne ∧ D.f z ∈ filledBase ∧ D.f z ≠ 3 / 2 ∧
      coneDisc σ.vertexOne z ∈ slitPlane := by
  have htri : ∀ {w : ℂ}, w ∈ σ.triangle → w ≠ σ.vertexOne → w.re < σ.width →
      w ∈ D.U ∧ w ≠ σ.vertexOne ∧ D.f w ∈ filledBase ∧ D.f w ≠ 3 / 2 ∧
        coneDisc σ.vertexOne w ∈ slitPlane := fun hw hv hx =>
    ⟨D.triangle_subset_U hw, hv, D.f_mem_filledBase_of_mem_triangle hσ hw,
      D.f_ne_of_mem_triangle c hθ hw hv, σ.coneDisc_vertexOne_mem_slitPlane' hx⟩
  rcases hz with (((h | h) | h) | h) | h
  · refine htri (σ.patchInt_subset_triangle h) (σ.ne_vertexOne_of_mem_patchInt h) ?_
    have := h.2 1
    simp only [wallSide] at this
    linarith
  · refine htri (D.mem_triangle_of_mem_patchZero h hre) (D.ne_vertexOne_of_mem_patchZero h) ?_
    linarith [le_abs_self z.re, h.2.1]
  · have hU : z ∈ D.U := D.V_subset_U 1 h.2.2.2.2.2.1
    have hv := D.ne_vertexOne_of_mem_patchOne h
    have hslit : coneDisc σ.vertexOne z ∈ slitPlane := by
      by_cases hx : z.re = σ.width
      · exact σ.coneDisc_mem_slitPlane_of_re_eq h.1 hx h.2.2.2.1
      · exact σ.coneDisc_mem_slitPlane hx
    rcases le_total z.re σ.width with hx | hx
    · have hT := D.mem_triangle_of_mem_patchOne h hx
      exact ⟨hU, hv, D.f_mem_filledBase_of_mem_triangle hσ hT,
        D.f_ne_of_mem_triangle c hθ hT hv, hslit⟩
    · have hg := D.f_good_of_refl c hθ hσ h.2.2.2.2.2.1 (D.refl_mem_triangle_of_mem_patchOne h hx)
        (D.refl_ne_vertexOne_of_mem_patchOne h)
      exact ⟨hU, hv, hg.1, hg.2, hslit⟩
  · have hU : z ∈ D.U := D.V_subset_U 2 h.2.2.2.2.2.1
    have hv := D.ne_vertexOne_of_mem_patchTwo h
    have hslit := σ.coneDisc_vertexOne_mem_slitPlane' h.2.2.1
    rcases le_total 0 (σ.wallSide 2 z) with hw | hw
    · have hT := D.mem_triangle_of_mem_patchTwo h hw
      exact ⟨hU, hv, D.f_mem_filledBase_of_mem_triangle hσ hT,
        D.f_ne_of_mem_triangle c hθ hT hv, hslit⟩
    · have hg := D.f_good_of_refl c hθ hσ h.2.2.2.2.2.1 (D.refl_mem_triangle_of_mem_patchTwo h hw)
        (D.refl_ne_vertexOne_of_mem_patchTwo h)
      exact ⟨hU, hv, hg.1, hg.2, hslit⟩
  · exact absurd h hd

end ConeShape.FoldData

end GC.Seifert
