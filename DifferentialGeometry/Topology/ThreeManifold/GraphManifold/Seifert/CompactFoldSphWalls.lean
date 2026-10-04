import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidCover

/-!
# Wall neighbourhoods and wall identities of the spherical compact fold

Lane CF-S3w, tier 3, curvature `+1` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4–§7, review 23 §6.1: reflection-stable wall
neighbourhoods). Template: `CompactFoldEuclidWalls`. Every declaration carries `sph`.

**Germs.** The apex models `3/2 + rotOne^{p₁}/2`, `-3/2 + rotTwo^{p₂}/2` and the outer germ
`compactOuterGerm p₃` are equivariant under the two reflections through their vertex
(`sphApexOne_refl_one`, …, `outerGerm_refl_one_sph`), because `e^{2iθⱼ pⱼ} = 1`.

**Selectors.** The pseudo-distances `ϖ₁ = ‖rotOne‖`, `ϖ₂ = ‖rotTwo‖`, `ϖ₃ = ‖z‖` are invariant
under the reflections in the walls through their vertex, and the lens coordinate `Im rotTwo` is
odd under `refl 2` (`norm_rotOne_refl_one_sph`, …, `abs_sphSideTwo_refl_two`).

**On the walls.** The canonical coordinates `Tⱼ = sphCanon` of the two vertices of a wall add up
to zero there and every pair sum is `≥ 0` on `T` (`sphCanon_add_*_nonneg`), so on wall `i` the
opposite one dominates: `T₁ ≥ |T₂|` on wall 0, `T₂ ≥ |T₁|` on wall 1, `T₃ ≥ |T₁|` on wall 2, i.e.
a wall stays outside the canonical disc of the opposite vertex; strictly `T₂ < T₁` on wall 0 and
`T₁ < T₂` on wall 1 away from `v₃`, which saturates the outer weight (`sphBlendThree < -w`,
resp. `> w`). The lens coordinate is `sin θ₂ · ϖ₂` on wall 0, at least `sin θ₁ · ϖ₁ / 2` on
wall 1 and `0` on wall 2; the disc angles take their wall values.

**Neighbourhoods.** `sphReflNbhd i W = W ∩ (refl i)⁻¹ W` is open, `refl i`-stable and contains
the wall points of `W` whenever `W` is open and inside `reflChart i`.

**The chain.** `sphFoldChain P` is the piecewise map of `CompactFoldSphPieces` for an arbitrary
parameter record `P : SphFoldParams` (apex germs, outer germ, corners at `v₁`, `v₂`, lens bridge,
outer corner, in this order); `sphPreFold = sphFoldChain sphPreFoldParams` by definition
(`sphPreFold_eq_chain`). For an open `G` (the good set outside the core, chosen by the assembly)
the wall sets `sphWallSet G P i ⊆ G` are cut out by strict inequalities fixing the active branch
and the saturated weights, and `sphWallNbhd G P i = sphReflNbhd i (sphWallSet G P i)` are open,
`refl i`-stable, inside `reflChart i` and `G`, and contain `wall i ∩ T ∩ G` minus `v₃`
(`wall_mem_sphPreFoldNbhd`); on them `sphFoldChain_refl_{zero,one,two}` and `sphPreFold_refl`
give `preFold ∘ refl i = conj ∘ preFold`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem canon_of_oplus_sph {t τ τ' : ℝ} (ht : 0 ≤ t) (hτ : 0 ≤ τ)
    (h : τ + τ' = t * (1 - τ * τ')) : (t - τ) / (1 + t * τ) = τ' := by
  rw [div_eq_iff (by positivity)]
  linear_combination (-1 : ℝ) * h

theorem pos_norm_add_re_sph {w : ℂ} (hw : w ≠ 0) (hre : 0 ≤ w.re) : 0 < ‖w‖ + w.re := by
  have := norm_pos_iff.2 hw
  linarith

theorem im_exp_mul_conj_eq_neg_sph (θ : ℝ) (w : ℂ) :
    (exp ((θ : ℂ) * I) * conj w).im = -(exp (-((θ : ℂ) * I)) * w).im := by
  rw [← CompactShape.conj_exp_neg_sph θ, ← map_mul, Complex.conj_im]

theorem one_le_normSq_one_add_sph {a : ℂ} (h : 0 ≤ a.re) : 1 ≤ Complex.normSq (1 + a) := by
  rw [Complex.normSq_apply, add_re, add_im, one_re, one_im, zero_add]
  nlinarith [sq_nonneg a.im]

namespace CompactShape

variable {σ : CompactShape}

theorem outerGerm_refl_zero_sph (z : ℂ) :
    compactOuterGerm σ.p₃ (σ.refl 0 z) = conj (compactOuterGerm σ.p₃ z) :=
  compactOuterGerm_conj σ.p₃ z

theorem outerGerm_refl_one_sph (z : ℂ) :
    compactOuterGerm σ.p₃ (σ.refl 1 z) = conj (compactOuterGerm σ.p₃ z) := by
  have e1 : exp (2 * (σ.θ₃ : ℂ) * I) ^ σ.p₃ = 1 := EuclidShape.exp_pow_eq_one σ.θ₃_mul_sph
  have e2 : conj (exp (2 * (σ.θ₃ : ℂ) * I)) ^ σ.p₃ = 1 := by
    rw [← map_pow, e1, map_one]
  rw [← compactOuterGerm_conj, compactOuterGerm, compactOuterGerm, norm_refl_one_sph,
    Complex.norm_conj, refl_one_apply_sph, map_mul, Complex.conj_conj, mul_div_assoc, mul_pow,
    e2, one_mul]

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sphApexOne_refl_one (z : ℂ) : σ.sphApexOne (σ.refl 1 z) = conj (σ.sphApexOne z) := by
  simp only [sphApexOne, rotOne_refl_one_sph hs, map_add, map_div₀, map_pow, map_ofNat]

theorem sphApexOne_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (hv1 : 1 + conj σ.vertexOne * z ≠ 0) :
    σ.sphApexOne (σ.refl 2 z) = conj (σ.sphApexOne z) := by
  simp only [sphApexOne, rotOne_refl_two_sph hs hz hv1, mul_pow,
    EuclidShape.exp_pow_eq_one σ.θ₁_mul_sph, one_mul, map_add, map_div₀, map_pow, map_ofNat]

theorem sphApexTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.sphApexTwo (σ.refl 2 z) = conj (σ.sphApexTwo z) := by
  simp only [sphApexTwo, rotTwo_refl_two_sph hs hz, map_add, map_div₀, map_pow, map_ofNat,
    map_neg]

theorem sphApexTwo_refl_zero (z : ℂ) : σ.sphApexTwo (σ.refl 0 z) = conj (σ.sphApexTwo z) := by
  simp only [sphApexTwo, rotTwo_refl_zero_sph hs, mul_pow,
    EuclidShape.exp_pow_eq_one σ.θ₂_mul_sph, one_mul, map_add, map_div₀, map_pow, map_ofNat,
    map_neg]

theorem norm_rotOne_refl_one_sph (z : ℂ) : ‖σ.rotOne (σ.refl 1 z)‖ = ‖σ.rotOne z‖ := by
  rw [rotOne_refl_one_sph hs, Complex.norm_conj]

theorem norm_rotOne_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (hv1 : 1 + conj σ.vertexOne * z ≠ 0) : ‖σ.rotOne (σ.refl 2 z)‖ = ‖σ.rotOne z‖ := by
  rw [rotOne_refl_two_sph hs hz hv1, norm_mul, Complex.norm_conj, exp_two_mul_eq_sph, norm_mul,
    norm_exp_mul_I_sph', one_mul, one_mul]

theorem norm_rotTwo_refl_zero_sph (z : ℂ) : ‖σ.rotTwo (σ.refl 0 z)‖ = ‖σ.rotTwo z‖ := by
  rw [rotTwo_refl_zero_sph hs, norm_mul, Complex.norm_conj, exp_two_mul_eq_sph, norm_mul,
    norm_exp_mul_I_sph', one_mul, one_mul]

theorem norm_rotTwo_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    ‖σ.rotTwo (σ.refl 2 z)‖ = ‖σ.rotTwo z‖ := by
  rw [rotTwo_refl_two_sph hs hz, Complex.norm_conj]

theorem abs_sphSideTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    |σ.sphSideTwo (σ.refl 2 z)| = |σ.sphSideTwo z| := by
  rw [sphSideTwo_refl_two hs hz, abs_neg]


theorem continuousAt_reflTwoAux_sph {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    ContinuousAt σ.reflTwoAux z := by
  have e : σ.reflTwoAux = fun u => exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (sphMoeb σ.vertexTwo u) :=
    funext (reflTwoAux_sph hs)
  rw [e]
  have hm : ContinuousAt (sphMoeb σ.vertexTwo) z :=
    (contDiffAt_sphMoeb (by rwa [conj_vertexTwo_sph])).continuousAt
  exact continuousAt_const.mul (Complex.continuous_conj.continuousAt.comp hm)

theorem isOpen_reflChart_two_sph : IsOpen (σ.reflChart 2) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨h1, h2⟩ := (mem_reflChart_two_iff_sph hs).1 hz
  have c1 : ContinuousAt (fun w : ℂ => 1 + σ.vertexTwo * w) z := by fun_prop
  have c2 : ContinuousAt (fun w : ℂ => 1 - σ.vertexTwo * σ.reflTwoAux w) z :=
    continuousAt_const.sub (continuousAt_const.mul (continuousAt_reflTwoAux_sph hs h1))
  filter_upwards [c1.eventually_ne h1, c2.eventually_ne h2] with w e1 e2
  exact (mem_reflChart_two_iff_sph hs).2 ⟨e1, e2⟩

theorem continuousAt_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    ContinuousAt (σ.refl 2) z := by
  obtain ⟨h1, h2⟩ := (mem_reflChart_two_iff_sph hs).1 hz
  have e : σ.refl 2 = fun u => sphMoebInv σ.vertexTwo (σ.reflTwoAux u) :=
    funext (refl_two_sph hs)
  rw [e]
  have hc : ContinuousAt (fun w => (w + σ.vertexTwo) / (1 - conj σ.vertexTwo * w))
      (σ.reflTwoAux z) := by
    have hne : 1 - conj σ.vertexTwo * σ.reflTwoAux z ≠ 0 := by rwa [conj_vertexTwo_sph]
    exact (continuousAt_id.add continuousAt_const).div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) hne
  exact hc.comp (f := σ.reflTwoAux) (continuousAt_reflTwoAux_sph hs h1)

theorem isOpen_reflChart_sph (i : Fin 3) : IsOpen (σ.reflChart i) := by
  fin_cases i
  · exact isOpen_univ
  · exact isOpen_univ
  · exact isOpen_reflChart_two_sph hs

theorem continuousOn_refl_sph (i : Fin 3) : ContinuousOn (σ.refl i) (σ.reflChart i) := by
  fin_cases i
  · exact Complex.continuous_conj.continuousOn
  · change ContinuousOn (fun z : ℂ => exp (2 * (σ.θ₃ : ℂ) * I) * conj z) _
    exact (continuous_const.mul Complex.continuous_conj).continuousOn
  · exact fun z hz => (continuousAt_refl_two_sph hs hz).continuousWithinAt

theorem refl_refl_sph (i : Fin 3) {z : ℂ} (hz : z ∈ σ.reflChart i) :
    σ.refl i (σ.refl i z) = z := by
  fin_cases i
  · exact refl_refl_zero_sph z
  · exact refl_refl_one_sph z
  · exact refl_refl_two_sph hs hz

theorem refl_eq_self_sph (i : Fin 3) {z : ℂ} (hz : z ∈ σ.reflChart i)
    (hw : σ.wallSide i z = 0) : σ.refl i z = z := by
  fin_cases i
  · exact refl_zero_eq_self_sph hw
  · exact refl_one_eq_self_sph hw
  · exact refl_two_eq_self_sph hs hw ((mem_reflChart_two_iff_sph hs).1 hz).1

omit hs in
variable (σ) in
def sphReflNbhd (i : Fin 3) (W : Set ℂ) : Set ℂ := W ∩ σ.refl i ⁻¹' W

omit hs in
theorem sphReflNbhd_subset (i : Fin 3) (W : Set ℂ) : σ.sphReflNbhd i W ⊆ W := inter_subset_left

theorem isOpen_sphReflNbhd (i : Fin 3) {W : Set ℂ} (hW : IsOpen W) (hWc : W ⊆ σ.reflChart i) :
    IsOpen (σ.sphReflNbhd i W) :=
  ContinuousOn.isOpen_inter_preimage ((continuousOn_refl_sph hs i).mono hWc) hW hW

theorem refl_mapsTo_sphReflNbhd (i : Fin 3) {W : Set ℂ} (hWc : W ⊆ σ.reflChart i) :
    MapsTo (σ.refl i) (σ.sphReflNbhd i W) (σ.sphReflNbhd i W) := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  change σ.refl i (σ.refl i z) ∈ W
  rw [refl_refl_sph hs i (hWc hz.1)]
  exact hz.1

theorem mem_sphReflNbhd_of_wall (i : Fin 3) {W : Set ℂ} (hWc : W ⊆ σ.reflChart i) {z : ℂ}
    (hzW : z ∈ W) (hw : σ.wallSide i z = 0) : z ∈ σ.sphReflNbhd i W := by
  refine ⟨hzW, ?_⟩
  change σ.refl i z ∈ W
  rw [refl_eq_self_sph hs i (hWc hzW) hw]
  exact hzW

omit hs in
theorem sphReflNbhd_subset_reflChart (i : Fin 3) {W : Set ℂ} (hWc : W ⊆ σ.reflChart i) :
    σ.sphReflNbhd i W ⊆ σ.reflChart i := fun _ hz => hWc hz.1

omit hs in
theorem sphCanon_eq_neg_tau {j : Fin 3} {z : ℂ} (h : σ.sphDist j z = 0) :
    σ.sphCanon j z = -σ.sphTau j := by
  rw [sphCanon, h]
  ring

theorem sphCanon_eq_of_oplus {j : Fin 3} {z : ℂ} {t τ' : ℝ} (h : σ.sphDist j z = t)
    (ho : σ.sphTau j + τ' = t * (1 - σ.sphTau j * τ')) : σ.sphCanon j z = τ' := by
  rw [sphCanon, h]
  exact canon_of_oplus_sph (h ▸ σ.sphDist_nonneg j z) (sphTau_pos hs j).le ho

theorem norm_rotOne_vertexTwo_sph : ‖σ.rotOne σ.vertexTwo‖ = σ.sphTOneTwo := by
  rw [rotOne_vertexTwo_sph hs, norm_mul, norm_exp_mul_I_sph', mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (tOneTwo_pos_sph hs)]

theorem norm_rotTwo_vertexOne_sph : ‖σ.rotTwo σ.vertexOne‖ = σ.sphTOneTwo := by
  rw [rotTwo_vertexOne_sph hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (tOneTwo_pos_sph hs)]

theorem norm_rotOne_zero_sph : ‖σ.rotOne 0‖ = σ.sphTOneThree := by
  rw [rotOne_zero_sph hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tOneThree_pos_sph hs)]

theorem norm_rotTwo_zero_sph : ‖σ.rotTwo 0‖ = σ.sphTTwoThree := by
  rw [rotTwo_zero_sph hs, norm_mul, norm_exp_mul_I_sph', mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (tTwoThree_pos_sph hs)]

theorem sphCanon_zero_vertexOne : σ.sphCanon 0 σ.vertexOne = -σ.sphTau 0 :=
  sphCanon_eq_neg_tau (by change ‖σ.rotOne σ.vertexOne‖ = 0; rw [rotOne_vertexOne_sph hs,
    norm_zero])

theorem sphCanon_one_vertexTwo : σ.sphCanon 1 σ.vertexTwo = -σ.sphTau 1 :=
  sphCanon_eq_neg_tau (by change ‖σ.rotTwo σ.vertexTwo‖ = 0; rw [rotTwo_vertexTwo_sph hs,
    norm_zero])

omit hs in
theorem sphCanon_two_zero : σ.sphCanon 2 0 = -σ.sphTau 2 :=
  sphCanon_eq_neg_tau (by change ‖(0 : ℂ)‖ = 0; rw [norm_zero])

theorem sphCanon_zero_vertexTwo : σ.sphCanon 0 σ.vertexTwo = σ.sphTau 1 :=
  sphCanon_eq_of_oplus hs (norm_rotOne_vertexTwo_sph hs) (sphTau_oplus_onetwo hs)

theorem sphCanon_one_vertexOne : σ.sphCanon 1 σ.vertexOne = σ.sphTau 0 :=
  sphCanon_eq_of_oplus hs (norm_rotTwo_vertexOne_sph hs)
    (by linear_combination sphTau_oplus_onetwo hs)

theorem sphCanon_two_vertexOne : σ.sphCanon 2 σ.vertexOne = σ.sphTau 0 :=
  sphCanon_eq_of_oplus hs (norm_vertexOne_sph hs)
    (by linear_combination sphTau_oplus_onethree hs)

theorem sphCanon_two_vertexTwo : σ.sphCanon 2 σ.vertexTwo = σ.sphTau 1 :=
  sphCanon_eq_of_oplus hs (norm_vertexTwo_sph hs)
    (by linear_combination sphTau_oplus_twothree hs)

theorem sphCanon_zero_zero : σ.sphCanon 0 0 = σ.sphTau 2 :=
  sphCanon_eq_of_oplus hs (norm_rotOne_zero_sph hs) (sphTau_oplus_onethree hs)

theorem sphCanon_one_zero : σ.sphCanon 1 0 = σ.sphTau 2 :=
  sphCanon_eq_of_oplus hs (norm_rotTwo_zero_sph hs) (sphTau_oplus_twothree hs)

theorem sphCanon_add_zero_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ σ.sphCanon 2 z + σ.sphCanon 1 z := by
  by_cases h0 : z = 0
  · rw [h0, sphCanon_two_zero, sphCanon_one_zero hs]
    linarith
  by_cases h2 : z = σ.vertexTwo
  · rw [h2, sphCanon_two_vertexTwo hs, sphCanon_one_vertexTwo hs]
    linarith
  have hd := mem_sphDomZero hs hz h0 h2
  rw [sphCanon_add_zero_cof hs hd]
  exact mul_nonneg (sq_nonneg _) (sphCofZero_pos hs hd).le

theorem sphCanon_add_one_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ σ.sphCanon 2 z + σ.sphCanon 0 z := by
  by_cases h0 : z = 0
  · rw [h0, sphCanon_two_zero, sphCanon_zero_zero hs]
    linarith
  by_cases h1 : z = σ.vertexOne
  · rw [h1, sphCanon_two_vertexOne hs, sphCanon_zero_vertexOne hs]
    linarith
  have hd := mem_sphDomOne hs hz h0 h1
  rw [sphCanon_add_one_cof hs hd]
  exact mul_nonneg (sq_nonneg _) (sphCofOne_pos hs hd).le

theorem sphCanon_add_two_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ σ.sphCanon 1 z + σ.sphCanon 0 z := by
  by_cases h1 : z = σ.vertexOne
  · rw [h1, sphCanon_one_vertexOne hs, sphCanon_zero_vertexOne hs]
    linarith
  by_cases h2 : z = σ.vertexTwo
  · rw [h2, sphCanon_one_vertexTwo hs, sphCanon_zero_vertexTwo hs]
    linarith
  have hd := mem_sphDomTwo hs hz h1 h2
  rw [sphCanon_add_two_cof hs hd]
  exact mul_nonneg (sq_nonneg _) (sphCofTwo_pos hs hd).le

theorem sphCanon_zero_ge_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    |σ.sphCanon 1 z| ≤ σ.sphCanon 0 z := by
  have a := sphCanon_add_two_nonneg hs hz
  have b := sphCanon_add_one_nonneg hs hz
  have c := sphCanon_add_zero_wall hs hz hw
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem sphCanon_one_ge_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    |σ.sphCanon 0 z| ≤ σ.sphCanon 1 z := by
  have a := sphCanon_add_two_nonneg hs hz
  have b := sphCanon_add_zero_nonneg hs hz
  have c := sphCanon_add_one_wall hs hz hw
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem sphCanon_two_ge_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    |σ.sphCanon 0 z| ≤ σ.sphCanon 2 z := by
  have a := sphCanon_add_one_nonneg hs hz
  have b := sphCanon_add_zero_nonneg hs hz
  have c := sphCanon_add_two_wall hs hz hw
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem tau_le_of_sphCanon_nonneg {j : Fin 3} {z : ℂ} (h : 0 ≤ σ.sphCanon j z) :
    σ.sphTau j ≤ σ.sphDist j z := by
  rw [sphCanon] at h
  have := div_nonneg_iff.1 h
  rcases this with ⟨a, -⟩ | ⟨-, b⟩
  · linarith
  · linarith [one_add_sphDist_mul_pos hs j z]

theorem tauZero_le_of_wallZero_sph {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    σ.sphTau 0 ≤ ‖σ.rotOne z‖ :=
  tau_le_of_sphCanon_nonneg hs ((abs_nonneg _).trans (sphCanon_zero_ge_of_wallZero hs hz hw))

theorem tauOne_le_of_wallOne_sph {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    σ.sphTau 1 ≤ ‖σ.rotTwo z‖ :=
  tau_le_of_sphCanon_nonneg hs ((abs_nonneg _).trans (sphCanon_one_ge_of_wallOne hs hz hw))

theorem tauTwo_le_of_wallTwo_sph {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    σ.sphTau 2 ≤ ‖z‖ :=
  tau_le_of_sphCanon_nonneg hs ((abs_nonneg _).trans (sphCanon_two_ge_of_wallTwo hs hz hw))

theorem wallSide_one_pos_of_wallZero_sph {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 0 z = 0) : 0 < σ.wallSide 1 z := by
  have him : z.im = 0 := hw
  have hre := re_nonneg_of_mem_sph hs hz
  have hre' : z.re ≠ 0 := fun h => h0 (Complex.ext h him)
  rw [wallSide_one_apply_sph, him, mul_zero, sub_zero]
  exact mul_pos σ.sin_θ₃_pos_sph (lt_of_le_of_ne hre (Ne.symm hre'))

theorem wallSide_zero_pos_of_wallOne_sph {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : 0 < σ.wallSide 0 z := by
  have him := im_nonneg_of_mem_sph hs hz
  rcases lt_or_eq_of_le him with h | h
  · exact h
  · exfalso
    rw [wallSide_one_apply_sph, ← h, mul_zero, sub_zero] at hw
    have hre : z.re = 0 := (mul_eq_zero.1 hw).resolve_left σ.sin_θ₃_pos_sph.ne'
    exact h0 (Complex.ext hre h.symm)

theorem sphCanon_one_lt_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 0 z = 0) : σ.sphCanon 1 z < σ.sphCanon 0 z := by
  have h1 : z ≠ σ.vertexOne := by
    rintro rfl
    have := wallSide_zero_vertexOne_pos_sph hs
    rw [hw] at this
    exact lt_irrefl 0 this
  have hd := mem_sphDomOne hs hz h0 h1
  have e := sphCanon_add_one_cof hs hd
  have hp := mul_pos (pow_pos (wallSide_one_pos_of_wallZero_sph hs hz h0 hw) 2)
    (sphCofOne_pos hs hd)
  linarith [sphCanon_add_zero_wall hs hz hw]

theorem sphCanon_zero_lt_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : σ.sphCanon 0 z < σ.sphCanon 1 z := by
  have h2 : z ≠ σ.vertexTwo := by
    rintro rfl
    have := wallSide_one_vertexTwo_pos_sph hs
    rw [hw] at this
    exact lt_irrefl 0 this
  have hd := mem_sphDomZero hs hz h0 h2
  have e := sphCanon_add_zero_cof hs hd
  have hp := mul_pos (pow_pos (wallSide_zero_pos_of_wallOne_sph hs hz h0 hw) 2)
    (sphCofZero_pos hs hd)
  linarith [sphCanon_add_one_wall hs hz hw]

omit hs in
theorem discAngle_of_wallZero_sph {z : ℂ} (hw : σ.wallSide 0 z = 0) : discAngle z = 0 := by
  change halfArg ‖z‖ z.re z.im = 0
  change z.im = 0 at hw
  rw [hw, halfArg_zero]

theorem discAngle_of_wallOne_sph {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : discAngle z = σ.θ₃ := by
  have hpos := pos_norm_add_re_sph h0 (re_nonneg_of_mem_sph hs hz)
  have h2 : 0 ≤ -(exp (-((σ.θ₃ : ℂ) * I)) * z).im := by
    rw [← wallSide_one_eq_neg_im_sph]
    exact ((mem_triangle_iff_sph hs).1 hz).2.1
  exact (discAngle_sector σ.θ₃_pos_sph σ.θ₃_le_sph hpos (im_nonneg_of_mem_sph hs hz) h2).2.2.2.2.2
    (by rw [← wallSide_one_eq_neg_im_sph]; exact hw)

theorem im_rot_rotTwo_of_wallZero_sph {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im = 0 := by
  have e := wallSide_zero_eq_rotTwo_sph hs z
  rw [hw, zero_mul, im_exp_mul_conj_eq_neg_sph] at e
  have hN := Complex.normSq_pos.2 (one_add_vertexTwo_ne_sph hs hz)
  have := (mul_eq_zero.1 e.symm).resolve_right hN.ne'
  linarith

theorem sphPsiTwo_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo)
    (hw : σ.wallSide 0 z = 0) : σ.sphPsiTwo z = σ.θ₂ := by
  have hne := rotTwo_ne_zero_sph hs (one_add_vertexTwo_ne_sph hs hz) h2
  have hpos := pos_norm_add_re_sph hne (re_rotTwo_nonneg_sph hs hz)
  obtain ⟨s1, s2⟩ := sector_two_sph hs hz
  rw [im_exp_mul_conj_eq_neg_sph] at s2
  exact (discAngle_sector σ.θ₂_pos_sph σ.θ₂_le_sph hpos s1 s2).2.2.2.2.2
    (by rw [im_rot_rotTwo_of_wallZero_sph hs hz hw, neg_zero])

theorem sphSideTwo_of_wallTwo {z : ℂ} (h1 : 1 + σ.vertexTwo * z ≠ 0)
    (hw : σ.wallSide 2 z = 0) : σ.sphSideTwo z = 0 := by
  rw [wallSide_two_eq_sph hs] at hw
  exact (mul_eq_zero.1 hw).resolve_right (Complex.normSq_pos.2 h1).ne'

theorem rotOne_ne_zero_sph {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (h1 : z ≠ σ.vertexOne) : σ.rotOne z ≠ 0 := by
  rw [rotOne_eq_mul_sph hs]
  exact mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _)) (div_ne_zero (sub_ne_zero.2 h1) hv1)

theorem one_le_normSq_rotTwo_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    1 ≤ Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) := by
  refine one_le_normSq_one_add_sph ?_
  rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (tOneTwo_pos_sph hs).le (re_rotTwo_nonneg_sph hs hz)

theorem sphPsiOne_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (hw : σ.wallSide 2 z = 0) : σ.sphPsiOne z = σ.θ₁ := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have hpos := pos_norm_add_re_sph (rotOne_ne_zero_sph hs hv1 h1) (re_rotOne_nonneg_sph hs hz)
  obtain ⟨s1, s2⟩ := sector_one_sph hs hz
  have e := wallSide_two_eq_rotOne_sph hs hv1 (by rwa [conj_vertexTwo_sph])
  have hY : (σ.rotTwo z).im = 0 := sphSideTwo_of_wallTwo hs hv2 hw
  rw [hY, mul_zero] at e
  have hN := lt_of_lt_of_le one_pos (one_le_normSq_rotTwo_sph hs hz)
  have hX := (mul_eq_zero.1 e).resolve_right hN.ne'
  rw [im_exp_mul_conj_eq_neg_sph] at s2 hX
  exact (discAngle_sector σ.θ₁_pos_sph σ.θ₁_le_sph hpos s1 s2).2.2.2.2.2 hX

theorem sphBlendThree_lt_of_wallZero {w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (hw0 : σ.wallSide 0 z = 0) :
    σ.sphBlendThree w δ z < -w := by
  have hc := sphCanon_one_lt_of_wallZero hs hz h0 hw0
  rw [sphBlendThree, discAngle_of_wallZero_sph hw0, mul_zero, zero_div, zero_sub]
  have := mul_pos (div_pos hw hδ) (sub_pos.2 hc)
  linarith

theorem sphBlendThree_gt_of_wallOne {w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (hw1 : σ.wallSide 1 z = 0) :
    w < σ.sphBlendThree w δ z := by
  have hc := sphCanon_zero_lt_of_wallOne hs hz h0 hw1
  rw [sphBlendThree, discAngle_of_wallOne_sph hs hz h0 hw1, mul_div_assoc,
    div_self σ.θ₃_pos_sph.ne']
  have := mul_pos (div_pos hw hδ) (sub_pos.2 hc)
  linarith

theorem sphSideTwo_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    σ.sphSideTwo z = Real.sin σ.θ₂ * ‖σ.rotTwo z‖ := by
  set u := exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z with hu
  have him : u.im = 0 := im_rot_rotTwo_of_wallZero_sph hs hz hw
  have hW : σ.rotTwo z = exp ((σ.θ₂ : ℂ) * I) * u := by
    rw [hu, ← mul_assoc, exp_mul_exp_neg_sph, one_mul]
  have hY : σ.sphSideTwo z = Real.sin σ.θ₂ * u.re := by
    rw [sphSideTwo, hW, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, him,
      mul_zero, zero_add]
  have hre : 0 ≤ u.re := by
    have s1 := (sector_two_sph hs hz).1
    have : 0 ≤ Real.sin σ.θ₂ * u.re := by rw [← hY]; exact s1
    exact (mul_nonneg_iff_of_pos_left σ.sin_θ₂_pos_sph).1 this
  have hn : ‖σ.rotTwo z‖ = u.re := by
    rw [hW, norm_mul, norm_exp_mul_I_sph', one_mul]
    conv_lhs => rw [eq_ofReal_re_of_im_sph him]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre]
  rw [hY, hn]

theorem sphSideTwo_ge_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    Real.sin σ.θ₁ * ‖σ.rotOne z‖ ≤ 2 * σ.sphSideTwo z := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have him : (σ.rotOne z).im = 0 := by
    have e := wallSide_one_eq_rotOne_sph hs z
    rw [hw, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (Complex.normSq_pos.2 hv1).ne'
  have hre := re_rotOne_nonneg_sph hs hz
  have hn : ‖σ.rotOne z‖ = (σ.rotOne z).re := by
    conv_lhs => rw [eq_ofReal_re_of_im_sph him]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre]
  have hv2 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_ne_sph hs hz
  have e := wallSide_two_eq_rotOne_sph hs hv1 hv2
  rw [im_exp_mul_conj_sph, him, mul_zero, sub_zero] at e
  have hN := one_le_normSq_rotTwo_sph hs hz
  have ht := tOneTwo_le_one_sph hs
  have ht0 := tOneTwo_pos_sph hs
  have hY := (sector_two_sph hs hz).1
  have hx : 0 ≤ Real.sin σ.θ₁ * (σ.rotOne z).re := mul_nonneg σ.sin_θ₁_pos_sph.le hre
  have h1 := mul_le_mul_of_nonneg_left hN hx
  have h2 : 0 ≤ (1 - σ.sphTOneTwo ^ 2) * (σ.rotTwo z).im := mul_nonneg (by nlinarith) hY
  rw [hn]
  change _ ≤ 2 * (σ.rotTwo z).im
  nlinarith

omit hs in
theorem sph_switch_cases {a b β β' d s s' : ℝ} (hab : a < b) (hβ : β < β')
    (h : d < a ∨ β' < s) (h' : d < a ∨ β' < s') :
    coneStep a b d = 0 ∨ (coneStep β β' s = 1 ∧ coneStep β β' s' = 1) := by
  rcases h with h | h
  · exact Or.inl (coneStep_eq_zero hab h.le)
  rcases h' with h' | h'
  · exact Or.inl (coneStep_eq_zero hab h'.le)
  exact Or.inr ⟨coneStep_eq_one hβ h.le, coneStep_eq_one hβ h'.le⟩

omit hs in
theorem sph_not_lens {d c a s β' L : ℝ} (hac : a ≤ c) (hL : L ≤ β') (hd : ¬ d < c)
    (h : d < a ∨ β' < s) : ¬ |s| < L := by
  rcases h with h | h
  · exact absurd (h.trans_le hac) hd
  · intro hl
    linarith [le_abs_self s]

theorem continuousAt_sphCanon_sph {j : Fin 3} {z : ℂ} (hd : ContinuousAt (σ.sphDist j) z) :
    ContinuousAt (σ.sphCanon j) z := by
  change ContinuousAt (fun u => (σ.sphDist j u - σ.sphTau j) /
    (1 + σ.sphDist j u * σ.sphTau j)) z
  exact (hd.sub continuousAt_const).div (continuousAt_const.add (hd.mul continuousAt_const))
    (one_add_sphDist_mul_pos hs j z).ne'

theorem continuousAt_normRotOne_sph {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0) :
    ContinuousAt (fun u => ‖σ.rotOne u‖) z :=
  (contDiffAt_rotOne_sph hs hv1).continuousAt.norm

theorem continuousAt_normRotTwo_sph {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ContinuousAt (fun u => ‖σ.rotTwo u‖) z :=
  (contDiffAt_rotTwo_sph hs hv2).continuousAt.norm

theorem continuousAt_sphBlendThree_sph (w δ : ℝ) {z : ℂ} (hψ : 0 < ‖z‖ + z.re)
    (hv1 : 1 + conj σ.vertexOne * z ≠ 0) (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ContinuousAt (σ.sphBlendThree w δ) z := by
  have c0 : ContinuousAt (σ.sphCanon 0) z :=
    continuousAt_sphCanon_sph hs (continuousAt_normRotOne_sph hs hv1)
  have c1 : ContinuousAt (σ.sphCanon 1) z :=
    continuousAt_sphCanon_sph hs (continuousAt_normRotTwo_sph hs hv2)
  have ca : ContinuousAt (fun u : ℂ => discAngle u) z :=
    (EuclidShape.contDiffAt_psiThree hψ).continuousAt
  change ContinuousAt (fun u => w * (2 * discAngle u / σ.θ₃ - 1) +
    w / δ * (σ.sphCanon 1 u - σ.sphCanon 0 u)) z
  exact (continuousAt_const.mul (((continuousAt_const.mul ca).div_const _).sub
    continuousAt_const)).add (continuousAt_const.mul (c1.sub c0))

end Spherical

structure SphFoldParams where
  germOne : ℝ
  germTwo : ℝ
  germOuter : ℝ
  cornerOne : ℝ
  cornerTwo : ℝ
  lens : ℝ
  blendOneStart : ℝ
  blendOneEnd : ℝ
  blendTwoStart : ℝ
  blendTwoEnd : ℝ
  switchStart : ℝ
  switchEnd : ℝ
  outerStart : ℝ
  outerEnd : ℝ
  nuWidth : ℝ
  nuScale : ℝ

variable (σ) in
def sphFoldChain (P : SphFoldParams) (z : ℂ) : ℂ :=
  if ‖σ.rotOne z‖ < P.germOne then σ.sphApexOne z
  else if ‖σ.rotTwo z‖ < P.germTwo then σ.sphApexTwo z
  else if ‖z‖ < P.germOuter then compactOuterGerm σ.p₃ z
  else if ‖σ.rotOne z‖ < P.cornerOne then
    σ.sphCornerOne P.blendOneStart P.blendOneEnd P.switchStart P.switchEnd z
  else if ‖σ.rotTwo z‖ < P.cornerTwo then
    σ.sphCornerTwo P.blendTwoStart P.blendTwoEnd P.switchStart P.switchEnd z
  else if |σ.sphSideTwo z| < P.lens then σ.sphBridgeTwo z
  else σ.sphCornerThree P.outerStart P.outerEnd P.nuWidth P.nuScale z

variable (σ) in
def sphWallSetZero (G : Set ℂ) (P : SphFoldParams) : Set ℂ :=
  {z | z ∈ G ∧ 1 + conj σ.vertexOne * z ≠ 0 ∧ 1 + σ.vertexTwo * z ≠ 0 ∧ 0 < ‖z‖ + z.re ∧
    P.cornerOne < ‖σ.rotOne z‖ ∧
    (‖σ.rotTwo z‖ < P.blendTwoStart ∨ P.switchEnd < σ.sphSideTwo z) ∧
    σ.sphBlendThree P.nuWidth P.nuScale z < -P.nuWidth ∧
    (‖σ.rotTwo z‖ < P.germTwo ∨ (0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧
      -Real.pi < 2 * σ.θ₂ - σ.sphPsiTwo z ∧ 2 * σ.θ₂ - σ.sphPsiTwo z < Real.pi))}

variable (σ) in
def sphWallSetOne (G : Set ℂ) (P : SphFoldParams) : Set ℂ :=
  {z | z ∈ G ∧ 1 + conj σ.vertexOne * z ≠ 0 ∧ 1 + σ.vertexTwo * z ≠ 0 ∧ 0 < ‖z‖ + z.re ∧
    P.cornerTwo < ‖σ.rotTwo z‖ ∧
    (‖σ.rotOne z‖ < P.blendOneStart ∨ P.switchEnd < σ.sphSideTwo z) ∧
    P.nuWidth < σ.sphBlendThree P.nuWidth P.nuScale z ∧
    -Real.pi < 2 * σ.θ₃ - discAngle z ∧ 2 * σ.θ₃ - discAngle z < Real.pi}

variable (σ) in
def sphWallSetTwo (G : Set ℂ) (P : SphFoldParams) : Set ℂ :=
  {z | z ∈ G ∧ z ∈ σ.reflChart 2 ∧ 1 + conj σ.vertexOne * z ≠ 0 ∧
    |σ.sphSideTwo z| < P.lens ∧ P.germOuter < ‖z‖ ∧
    (‖σ.rotOne z‖ < P.germOne ∨ (0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
      -Real.pi < 2 * σ.θ₁ - σ.sphPsiOne z ∧ 2 * σ.θ₁ - σ.sphPsiOne z < Real.pi))}

variable (σ) in
def sphWallSet (G : Set ℂ) (P : SphFoldParams) : Fin 3 → Set ℂ
  | 0 => σ.sphWallSetZero G P
  | 1 => σ.sphWallSetOne G P
  | 2 => σ.sphWallSetTwo G P

variable (σ) in
def sphWallNbhd (G : Set ℂ) (P : SphFoldParams) (i : Fin 3) : Set ℂ :=
  σ.sphReflNbhd i (σ.sphWallSet G P i)

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem eventually_rotTwo_disj_sph {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) {r : ℝ}
    (h : ‖σ.rotTwo z‖ < r ∨ (0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧
      -Real.pi < 2 * σ.θ₂ - σ.sphPsiTwo z ∧ 2 * σ.θ₂ - σ.sphPsiTwo z < Real.pi)) :
    ∀ᶠ u in 𝓝 z, ‖σ.rotTwo u‖ < r ∨ (0 < ‖σ.rotTwo u‖ + (σ.rotTwo u).re ∧
      -Real.pi < 2 * σ.θ₂ - σ.sphPsiTwo u ∧ 2 * σ.θ₂ - σ.sphPsiTwo u < Real.pi) := by
  have cR := continuousAt_normRotTwo_sph hs hv2
  rcases h with h | ⟨h1, h2, h3⟩
  · exact (cR.eventually (gt_mem_nhds h)).mono fun u hu => Or.inl hu
  · have cN : ContinuousAt (fun u => ‖σ.rotTwo u‖ + (σ.rotTwo u).re) z :=
      cR.add (Complex.continuous_re.continuousAt.comp (contDiffAt_rotTwo_sph hs hv2).continuousAt)
    have cP : ContinuousAt (fun u => 2 * σ.θ₂ - σ.sphPsiTwo u) z :=
      continuousAt_const.sub (contDiffAt_sphPsiTwo hs hv2 h1).continuousAt
    filter_upwards [cN.eventually (lt_mem_nhds h1), cP.eventually (lt_mem_nhds h2),
      cP.eventually (gt_mem_nhds h3)] with u b1 b2 b3
    exact Or.inr ⟨b1, b2, b3⟩

theorem eventually_rotOne_disj_sph {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0) {r : ℝ}
    (h : ‖σ.rotOne z‖ < r ∨ (0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
      -Real.pi < 2 * σ.θ₁ - σ.sphPsiOne z ∧ 2 * σ.θ₁ - σ.sphPsiOne z < Real.pi)) :
    ∀ᶠ u in 𝓝 z, ‖σ.rotOne u‖ < r ∨ (0 < ‖σ.rotOne u‖ + (σ.rotOne u).re ∧
      -Real.pi < 2 * σ.θ₁ - σ.sphPsiOne u ∧ 2 * σ.θ₁ - σ.sphPsiOne u < Real.pi) := by
  have cR := continuousAt_normRotOne_sph hs hv1
  rcases h with h | ⟨h1, h2, h3⟩
  · exact (cR.eventually (gt_mem_nhds h)).mono fun u hu => Or.inl hu
  · have cN : ContinuousAt (fun u => ‖σ.rotOne u‖ + (σ.rotOne u).re) z :=
      cR.add (Complex.continuous_re.continuousAt.comp (contDiffAt_rotOne_sph hs hv1).continuousAt)
    have cP : ContinuousAt (fun u => 2 * σ.θ₁ - σ.sphPsiOne u) z :=
      continuousAt_const.sub (contDiffAt_sphPsiOne hs hv1 h1).continuousAt
    filter_upwards [cN.eventually (lt_mem_nhds h1), cP.eventually (lt_mem_nhds h2),
      cP.eventually (gt_mem_nhds h3)] with u b1 b2 b3
    exact Or.inr ⟨b1, b2, b3⟩

theorem eventually_switch_disj_sph {z : ℂ} {d : ℂ → ℝ} (hd : ContinuousAt d z)
    (hv2 : 1 + σ.vertexTwo * z ≠ 0) {a β' : ℝ} (h : d z < a ∨ β' < σ.sphSideTwo z) :
    ∀ᶠ u in 𝓝 z, d u < a ∨ β' < σ.sphSideTwo u := by
  rcases h with h | h
  · exact (hd.eventually (gt_mem_nhds h)).mono fun u hu => Or.inl hu
  · exact ((contDiffAt_sphSideTwo hs hv2).continuousAt.eventually (lt_mem_nhds h)).mono
      fun u hu => Or.inr hu

theorem isOpen_sphWallSetZero {G : Set ℂ} (hG : IsOpen G) (P : SphFoldParams) :
    IsOpen (σ.sphWallSetZero G P) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hz
  have c1 : ContinuousAt (fun w : ℂ => 1 + conj σ.vertexOne * w) z := by fun_prop
  have c2 : ContinuousAt (fun w : ℂ => 1 + σ.vertexTwo * w) z := by fun_prop
  have c4 : ContinuousAt (fun u : ℂ => ‖u‖ + u.re) z :=
    (continuous_norm.add Complex.continuous_re).continuousAt
  filter_upwards [hG.mem_nhds a1, c1.eventually_ne a2, c2.eventually_ne a3,
    c4.eventually (lt_mem_nhds a4),
    (continuousAt_normRotOne_sph hs a2).eventually (lt_mem_nhds a5),
    eventually_switch_disj_sph hs (continuousAt_normRotTwo_sph hs a3) a3 a6,
    (continuousAt_sphBlendThree_sph hs _ _ a4 a2 a3).eventually (gt_mem_nhds a7),
    eventually_rotTwo_disj_sph hs a3 a8] with u b1 b2 b3 b4 b5 b6 b7 b8
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩

theorem isOpen_sphWallSetOne {G : Set ℂ} (hG : IsOpen G) (P : SphFoldParams) :
    IsOpen (σ.sphWallSetOne G P) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hz
  have c1 : ContinuousAt (fun w : ℂ => 1 + conj σ.vertexOne * w) z := by fun_prop
  have c2 : ContinuousAt (fun w : ℂ => 1 + σ.vertexTwo * w) z := by fun_prop
  have c4 : ContinuousAt (fun u : ℂ => ‖u‖ + u.re) z :=
    (continuous_norm.add Complex.continuous_re).continuousAt
  have cA : ContinuousAt (fun u : ℂ => 2 * σ.θ₃ - discAngle u) z :=
    continuousAt_const.sub (EuclidShape.contDiffAt_psiThree a4).continuousAt
  filter_upwards [hG.mem_nhds a1, c1.eventually_ne a2, c2.eventually_ne a3,
    c4.eventually (lt_mem_nhds a4),
    (continuousAt_normRotTwo_sph hs a3).eventually (lt_mem_nhds a5),
    eventually_switch_disj_sph hs (continuousAt_normRotOne_sph hs a2) a3 a6,
    (continuousAt_sphBlendThree_sph hs _ _ a4 a2 a3).eventually (lt_mem_nhds a7),
    cA.eventually (lt_mem_nhds a8), cA.eventually (gt_mem_nhds a9)]
    with u b1 b2 b3 b4 b5 b6 b7 b8 b9
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩

theorem isOpen_sphWallSetTwo {G : Set ℂ} (hG : IsOpen G) (P : SphFoldParams) :
    IsOpen (σ.sphWallSetTwo G P) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hz
  have hv2 := ((mem_reflChart_two_iff_sph hs).1 a2).1
  have c1 : ContinuousAt (fun w : ℂ => 1 + conj σ.vertexOne * w) z := by fun_prop
  have cS : ContinuousAt (fun u => |σ.sphSideTwo u|) z :=
    (contDiffAt_sphSideTwo hs hv2).continuousAt.abs
  filter_upwards [hG.mem_nhds a1, (isOpen_reflChart_two_sph hs).mem_nhds a2, c1.eventually_ne a3,
    cS.eventually (gt_mem_nhds a4), continuous_norm.continuousAt.eventually (lt_mem_nhds a5),
    eventually_rotOne_disj_sph hs a3 a6] with u b1 b2 b3 b4 b5 b6
  exact ⟨b1, b2, b3, b4, b5, b6⟩

theorem isOpen_sphWallSet {G : Set ℂ} (hG : IsOpen G) (P : SphFoldParams) (i : Fin 3) :
    IsOpen (σ.sphWallSet G P i) := by
  fin_cases i
  · exact isOpen_sphWallSetZero hs hG P
  · exact isOpen_sphWallSetOne hs hG P
  · exact isOpen_sphWallSetTwo hs hG P

omit hs in
theorem sphWallSet_subset_reflChart (G : Set ℂ) (P : SphFoldParams) (i : Fin 3) :
    σ.sphWallSet G P i ⊆ σ.reflChart i := by
  fin_cases i
  · exact fun _ _ => trivial
  · exact fun _ _ => trivial
  · exact fun _ hz => hz.2.1

omit hs in
theorem sphWallSet_subset (G : Set ℂ) (P : SphFoldParams) (i : Fin 3) :
    σ.sphWallSet G P i ⊆ G := by
  fin_cases i
  · exact fun _ hz => hz.1
  · exact fun _ hz => hz.1
  · exact fun _ hz => hz.1

theorem isOpen_sphWallNbhd {G : Set ℂ} (hG : IsOpen G) (P : SphFoldParams) (i : Fin 3) :
    IsOpen (σ.sphWallNbhd G P i) :=
  isOpen_sphReflNbhd hs i (isOpen_sphWallSet hs hG P i) (sphWallSet_subset_reflChart G P i)

theorem refl_mapsTo_sphWallNbhd (G : Set ℂ) (P : SphFoldParams) (i : Fin 3) :
    MapsTo (σ.refl i) (σ.sphWallNbhd G P i) (σ.sphWallNbhd G P i) :=
  refl_mapsTo_sphReflNbhd hs i (sphWallSet_subset_reflChart G P i)

omit hs in
theorem sphWallNbhd_subset_reflChart (G : Set ℂ) (P : SphFoldParams) (i : Fin 3) :
    σ.sphWallNbhd G P i ⊆ σ.reflChart i :=
  sphReflNbhd_subset_reflChart i (sphWallSet_subset_reflChart G P i)

omit hs in
theorem sphWallNbhd_subset (G : Set ℂ) (P : SphFoldParams) (i : Fin 3) :
    σ.sphWallNbhd G P i ⊆ G := fun _ hz => sphWallSet_subset G P i hz.1

omit hs in
theorem refl_mem_of_sphWallNbhd {G : Set ℂ} {P : SphFoldParams} {i : Fin 3} {z : ℂ}
    (hz : z ∈ σ.sphWallNbhd G P i) : σ.refl i z ∈ G := sphWallSet_subset G P i hz.2

theorem wall_mem_sphWallSetZero {G : Set ℂ} {P : SphFoldParams}
    (hg2 : 0 < P.germTwo) (hc1 : P.cornerOne < σ.sphTau 0)
    (hsw : P.switchEnd < Real.sin σ.θ₂ * P.blendTwoStart) (hw : 0 < P.nuWidth)
    (hδ : 0 < P.nuScale) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw0 : σ.wallSide 0 z = 0) (hG : z ∈ G) : z ∈ σ.sphWallSetZero G P := by
  refine ⟨hG, one_add_conj_vertexOne_ne_sph hs hz, one_add_vertexTwo_ne_sph hs hz,
    pos_norm_add_re_sph h0 (re_nonneg_of_mem_sph hs hz),
    hc1.trans_le (tauZero_le_of_wallZero_sph hs hz hw0), ?_,
    sphBlendThree_lt_of_wallZero hs hw hδ hz h0 hw0, ?_⟩
  · rcases lt_or_ge ‖σ.rotTwo z‖ P.blendTwoStart with h | h
    · exact Or.inl h
    · right
      rw [sphSideTwo_of_wallZero hs hz hw0]
      exact hsw.trans_le (mul_le_mul_of_nonneg_left h σ.sin_θ₂_pos_sph.le)
  · by_cases h2 : z = σ.vertexTwo
    · left
      rw [h2, rotTwo_vertexTwo_sph hs, norm_zero]
      exact hg2
    · right
      have hne := rotTwo_ne_zero_sph hs (one_add_vertexTwo_ne_sph hs hz) h2
      have e := sphPsiTwo_of_wallZero hs hz h2 hw0
      refine ⟨pos_norm_add_re_sph hne (re_rotTwo_nonneg_sph hs hz), ?_, ?_⟩ <;> rw [e] <;>
        linarith [σ.θ₂_pos_sph, σ.θ₂_le_sph, Real.pi_pos]

theorem wall_mem_sphWallSetOne {G : Set ℂ} {P : SphFoldParams}
    (hc2 : P.cornerTwo < σ.sphTau 1)
    (hsw : P.switchEnd < Real.sin σ.θ₁ / 2 * P.blendOneStart) (hw : 0 < P.nuWidth)
    (hδ : 0 < P.nuScale) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw1 : σ.wallSide 1 z = 0) (hG : z ∈ G) : z ∈ σ.sphWallSetOne G P := by
  have ht := discAngle_of_wallOne_sph hs hz h0 hw1
  refine ⟨hG, one_add_conj_vertexOne_ne_sph hs hz, one_add_vertexTwo_ne_sph hs hz,
    pos_norm_add_re_sph h0 (re_nonneg_of_mem_sph hs hz),
    hc2.trans_le (tauOne_le_of_wallOne_sph hs hz hw1), ?_,
    sphBlendThree_gt_of_wallOne hs hw hδ hz h0 hw1, ?_, ?_⟩
  · rcases lt_or_ge ‖σ.rotOne z‖ P.blendOneStart with h | h
    · exact Or.inl h
    · right
      have h1 := sphSideTwo_ge_of_wallOne hs hz hw1
      have h2 := mul_le_mul_of_nonneg_left h σ.sin_θ₁_pos_sph.le
      linarith
  · rw [ht]
    linarith [σ.θ₃_pos_sph, Real.pi_pos]
  · rw [ht]
    linarith [σ.θ₃_le_sph, Real.pi_pos]

theorem wall_mem_sphWallSetTwo {G : Set ℂ} {P : SphFoldParams} (hg1 : 0 < P.germOne)
    (hL : 0 < P.lens) (hg3 : P.germOuter < σ.sphTau 2) {z : ℂ} (hz : z ∈ σ.triangle)
    (hw2 : σ.wallSide 2 z = 0) (hG : z ∈ G) : z ∈ σ.sphWallSetTwo G P := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  refine ⟨hG, mem_reflChart_two_of_wall_sph hs hw2 hv2, hv1,
    by rw [sphSideTwo_of_wallTwo hs hv2 hw2, abs_zero]; exact hL,
    hg3.trans_le (tauTwo_le_of_wallTwo_sph hs hz hw2), ?_⟩
  by_cases h1 : z = σ.vertexOne
  · left
    rw [h1, rotOne_vertexOne_sph hs, norm_zero]
    exact hg1
  · right
    have e := sphPsiOne_of_wallTwo hs hz h1 hw2
    refine ⟨pos_norm_add_re_sph (rotOne_ne_zero_sph hs hv1 h1) (re_rotOne_nonneg_sph hs hz), ?_,
      ?_⟩ <;> rw [e] <;> linarith [σ.θ₁_pos_sph, σ.θ₁_le_sph, Real.pi_pos]

theorem sphFoldChain_refl_zero {P : SphFoldParams} (hg1 : P.germOne ≤ P.cornerOne)
    (ha2 : P.blendTwoStart ≤ P.cornerTwo) (hab2 : P.blendTwoStart < P.blendTwoEnd)
    (hβ : P.switchStart < P.switchEnd) (hL : P.lens ≤ P.switchStart) (hw : 0 < P.nuWidth)
    {G : Set ℂ} {z : ℂ} (hz : z ∈ σ.sphWallNbhd G P 0) :
    σ.sphFoldChain P (σ.refl 0 z) = conj (σ.sphFoldChain P z) := by
  obtain ⟨⟨-, -, -, -, a5, a6, a7, a8⟩, ⟨-, -, -, -, b5, b6, b7, -⟩⟩ := hz
  have n2 : ‖σ.rotTwo (σ.refl 0 z)‖ = ‖σ.rotTwo z‖ := norm_rotTwo_refl_zero_sph hs z
  have n0 : ‖σ.refl 0 z‖ = ‖z‖ := norm_refl_zero_sph z
  rw [n2] at b6
  have f1 : ¬ ‖σ.rotOne z‖ < P.cornerOne := not_lt.2 a5.le
  have f1' : ¬ ‖σ.rotOne (σ.refl 0 z)‖ < P.cornerOne := not_lt.2 b5.le
  have g1 : ¬ ‖σ.rotOne z‖ < P.germOne := fun h => f1 (h.trans_le hg1)
  have g1' : ¬ ‖σ.rotOne (σ.refl 0 z)‖ < P.germOne := fun h => f1' (h.trans_le hg1)
  simp only [sphFoldChain, g1, g1', f1, f1', n2, n0, ite_false]
  by_cases c2 : ‖σ.rotTwo z‖ < P.germTwo
  · simp only [c2, ite_true]
    exact sphApexTwo_refl_zero hs z
  simp only [c2, ite_false]
  by_cases c3 : ‖z‖ < P.germOuter
  · simp only [c3, ite_true]
    exact outerGerm_refl_zero_sph z
  simp only [c3, ite_false]
  by_cases c5 : ‖σ.rotTwo z‖ < P.cornerTwo
  · simp only [c5, ite_true]
    obtain ⟨hψ, h1, h2⟩ := a8.resolve_left c2
    exact sphCornerTwo_refl_zero hs _ _ _ _ hψ h1 h2 (sph_switch_cases hab2 hβ a6 b6)
  have hL' : P.lens ≤ P.switchEnd := hL.trans hβ.le
  simp only [c5, ite_false, sph_not_lens ha2 hL' c5 a6, sph_not_lens ha2 hL' c5 b6]
  exact sphCornerThree_refl_zero hs _ _ _ _ (Or.inr ⟨coneStep_eq_zero (by linarith) a7.le,
    coneStep_eq_zero (by linarith) b7.le⟩)

theorem sphFoldChain_refl_one {P : SphFoldParams} (hg2 : P.germTwo ≤ P.cornerTwo)
    (ha1 : P.blendOneStart ≤ P.cornerOne) (hab1 : P.blendOneStart < P.blendOneEnd)
    (hβ : P.switchStart < P.switchEnd) (hL : P.lens ≤ P.switchStart) (hw : 0 < P.nuWidth)
    {G : Set ℂ} {z : ℂ} (hz : z ∈ σ.sphWallNbhd G P 1) :
    σ.sphFoldChain P (σ.refl 1 z) = conj (σ.sphFoldChain P z) := by
  obtain ⟨⟨-, -, -, a4, a5, a6, a7, a8, a9⟩, ⟨-, -, -, -, b5, b6, b7, -, -⟩⟩ := hz
  have n1 : ‖σ.rotOne (σ.refl 1 z)‖ = ‖σ.rotOne z‖ := norm_rotOne_refl_one_sph hs z
  have n0 : ‖σ.refl 1 z‖ = ‖z‖ := norm_refl_one_sph z
  rw [n1] at b6
  have f2 : ¬ ‖σ.rotTwo z‖ < P.cornerTwo := not_lt.2 a5.le
  have f2' : ¬ ‖σ.rotTwo (σ.refl 1 z)‖ < P.cornerTwo := not_lt.2 b5.le
  have g2 : ¬ ‖σ.rotTwo z‖ < P.germTwo := fun h => f2 (h.trans_le hg2)
  have g2' : ¬ ‖σ.rotTwo (σ.refl 1 z)‖ < P.germTwo := fun h => f2' (h.trans_le hg2)
  simp only [sphFoldChain, g2, g2', f2, f2', n1, n0, ite_false]
  by_cases c1 : ‖σ.rotOne z‖ < P.germOne
  · simp only [c1, ite_true]
    exact sphApexOne_refl_one hs z
  simp only [c1, ite_false]
  by_cases c3 : ‖z‖ < P.germOuter
  · simp only [c3, ite_true]
    exact outerGerm_refl_one_sph z
  simp only [c3, ite_false]
  by_cases c4 : ‖σ.rotOne z‖ < P.cornerOne
  · simp only [c4, ite_true]
    exact sphCornerOne_refl_one hs _ _ _ _ (sph_switch_cases hab1 hβ a6 b6)
  have hL' : P.lens ≤ P.switchEnd := hL.trans hβ.le
  simp only [c4, ite_false, sph_not_lens ha1 hL' c4 a6, sph_not_lens ha1 hL' c4 b6]
  exact sphCornerThree_refl_one hs _ _ _ _ a4 a8 a9 (Or.inr ⟨coneStep_eq_one (by linarith) a7.le,
    coneStep_eq_one (by linarith) b7.le⟩)

theorem sphFoldChain_refl_two {P : SphFoldParams} (hβ : P.switchStart < P.switchEnd)
    (hL : P.lens ≤ P.switchStart) {G : Set ℂ} {z : ℂ} (hz : z ∈ σ.sphWallNbhd G P 2) :
    σ.sphFoldChain P (σ.refl 2 z) = conj (σ.sphFoldChain P z) := by
  obtain ⟨⟨-, a2, a3, a4, a5, a6⟩, ⟨-, -, -, b4, b5, -⟩⟩ := hz
  have n1 : ‖σ.rotOne (σ.refl 2 z)‖ = ‖σ.rotOne z‖ := norm_rotOne_refl_two_sph hs a2 a3
  have n2 : ‖σ.rotTwo (σ.refl 2 z)‖ = ‖σ.rotTwo z‖ := norm_rotTwo_refl_two_sph hs a2
  have f3 : ¬ ‖z‖ < P.germOuter := not_lt.2 a5.le
  have f3' : ¬ ‖σ.refl 2 z‖ < P.germOuter := not_lt.2 b5.le
  have s0 : σ.sphLensSwitch P.switchStart P.switchEnd z = 0 :=
    coneStep_eq_zero hβ (by linarith [le_abs_self (σ.sphSideTwo z)])
  have s0' : σ.sphLensSwitch P.switchStart P.switchEnd (σ.refl 2 z) = 0 :=
    coneStep_eq_zero hβ (by linarith [le_abs_self (σ.sphSideTwo (σ.refl 2 z))])
  simp only [sphFoldChain, f3, f3', n1, n2, a4, b4, ite_false, ite_true]
  by_cases c1 : ‖σ.rotOne z‖ < P.germOne
  · simp only [c1, ite_true]
    exact sphApexOne_refl_two hs a2 a3
  simp only [c1, ite_false]
  by_cases c2 : ‖σ.rotTwo z‖ < P.germTwo
  · simp only [c2, ite_true]
    exact sphApexTwo_refl_two hs a2
  simp only [c2, ite_false]
  by_cases c4 : ‖σ.rotOne z‖ < P.cornerOne
  · simp only [c4, ite_true]
    obtain ⟨hψ, h1, h2⟩ := a6.resolve_left c1
    exact sphCornerOne_refl_two hs _ _ _ _ a2 a3 hψ h1 h2 (Or.inr ⟨s0, s0'⟩)
  simp only [c4, ite_false]
  by_cases c5 : ‖σ.rotTwo z‖ < P.cornerTwo
  · simp only [c5, ite_true]
    exact sphCornerTwo_refl_two hs _ _ _ _ a2 a3 (Or.inr ⟨s0, s0'⟩)
  simp only [c5, ite_false]
  exact sphBridgeTwo_refl_two hs a2 a3

omit hs in
theorem ne_zero_of_mem_sphWallNbhd {G : Set ℂ} {P : SphFoldParams} (hg3 : 0 ≤ P.germOuter)
    {i : Fin 3} {z : ℂ} (hz : z ∈ σ.sphWallNbhd G P i) : z ≠ 0 := by
  rintro rfl
  fin_cases i
  · have := hz.1.2.2.2.1
    rw [norm_zero, zero_re, add_zero] at this
    exact lt_irrefl 0 this
  · have := hz.1.2.2.2.1
    rw [norm_zero, zero_re, add_zero] at this
    exact lt_irrefl 0 this
  · have := hz.1.2.2.2.2.1
    rw [norm_zero] at this
    linarith

end Spherical

variable (σ) in
def sphPreFoldParams : SphFoldParams where
  germOne := σ.sphGermRadius
  germTwo := σ.sphGermRadius
  germOuter := σ.sphOuterGermRadius
  cornerOne := σ.sphCornerRad 0
  cornerTwo := σ.sphCornerRad 1
  lens := σ.sphLensWidth
  blendOneStart := σ.sphBlendStart
  blendOneEnd := σ.sphBlendEnd
  blendTwoStart := σ.sphBlendStart
  blendTwoEnd := σ.sphBlendEnd
  switchStart := σ.sphLensWidth
  switchEnd := σ.sphSwitchTop
  outerStart := σ.sphOuterBlendStart
  outerEnd := σ.sphOuterBlendEnd
  nuWidth := 1
  nuScale := σ.sphCornerShrink

theorem sphPreFold_eq_chain : σ.sphPreFold = σ.sphFoldChain σ.sphPreFoldParams := rfl

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sphPreFold_refl (i : Fin 3) {G : Set ℂ} {z : ℂ}
    (hz : z ∈ σ.sphWallNbhd G σ.sphPreFoldParams i) :
    σ.sphPreFold (σ.refl i z) = conj (σ.sphPreFold z) := by
  obtain ⟨-, -, p3, -, -, p6, -, -, -, -, -⟩ := sphParams hs
  obtain ⟨l1, l2, l3, l4, -, -, -, -, -⟩ := sphLayout_ineqs hs
  rw [sphPreFold_eq_chain]
  fin_cases i
  · exact sphFoldChain_refl_zero hs (P := σ.sphPreFoldParams) l1 l4 p6 p3 le_rfl one_pos hz
  · exact sphFoldChain_refl_one hs (P := σ.sphPreFoldParams) l2 l3 p6 p3 le_rfl one_pos hz
  · exact sphFoldChain_refl_two hs (P := σ.sphPreFoldParams) p3 le_rfl hz

theorem wall_mem_sphPreFoldNbhd (i : Fin 3) {G : Set ℂ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : z ≠ 0) (hw : σ.wallSide i z = 0) (hG : z ∈ G) :
    z ∈ σ.sphWallNbhd G σ.sphPreFoldParams i := by
  obtain ⟨p1, p2, -, p4, -, -, -, -, -, -, -⟩ := sphParams hs
  obtain ⟨-, -, -, -, l5, l6, l7, l8, l9⟩ := sphLayout_ineqs hs
  refine mem_sphReflNbhd_of_wall hs i (sphWallSet_subset_reflChart G _ i) ?_ hw
  fin_cases i
  · exact wall_mem_sphWallSetZero hs (P := σ.sphPreFoldParams) p4 l5 l8 one_pos p1 hz h0 hw hG
  · exact wall_mem_sphWallSetOne hs (P := σ.sphPreFoldParams) l6 l9 one_pos p1 hz h0 hw hG
  · exact wall_mem_sphWallSetTwo hs (P := σ.sphPreFoldParams) p4 p2 l7 hz hw hG

theorem ne_zero_of_mem_sphPreFoldNbhd {G : Set ℂ} {i : Fin 3} {z : ℂ}
    (hz : z ∈ σ.sphWallNbhd G σ.sphPreFoldParams i) : z ≠ 0 :=
  ne_zero_of_mem_sphWallNbhd (sphParams hs).2.2.2.2.2.2.2.1.le hz

end Spherical

end CompactShape

end GC.Seifert
