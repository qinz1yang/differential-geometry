/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Conformal.Euclidean.CoordinateDependence
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Ext

open RealInnerProductSpace InnerProductSpace Filter Metric
open scoped Topology

namespace DifferentialGeometry.LiouvilleQuadratic

open DifferentialGeometry.LiouvilleRigidity DifferentialGeometry.LiouvilleIntegration

noncomputable section

variable {m : ℕ}

abbrev dρ (hm : 3 ≤ m) (F : ES m → ES m) (j : Fin m) (z : ES m) : ℝ :=
  fderiv ℝ (recipConfFactor hm F) z (stdBasis m j)

abbrev ddρ (hm : 3 ≤ m) (F : ES m → ES m) (j : Fin m) (z : ES m) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m j)) z (stdBasis m j)

theorem coord_stdBasis_self (k : Fin m) : (stdBasis m k : ES m) k = 1 := by
  simp [stdBasis, EuclideanSpace.basisFun_apply]

theorem coord_stdBasis_of_ne {j k : Fin m} (h : j ≠ k) : (stdBasis m k : ES m) j = 0 := by
  simp [stdBasis, EuclideanSpace.basisFun_apply, h]

theorem inner_stdBasis_left (k : Fin m) (w : ES m) : ⟪stdBasis m k, w⟫_ℝ = w k := by
  rw [stdBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]; simp

theorem inner_stdBasis_right (k : Fin m) (w : ES m) : ⟪w, stdBasis m k⟫_ℝ = w k := by
  rw [stdBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]; simp

theorem norm_stdBasis (k : Fin m) : ‖stdBasis m k‖ = 1 := (stdBasis m).orthonormal.1 k

theorem abs_coord_sub_le (k : Fin m) (x c : ES m) : |x k - c k| ≤ ‖x - c‖ := by
  rw [show x k - c k = (x - c) k from rfl, ← inner_stdBasis_right k (x - c)]
  calc |⟪x - c, stdBasis m k⟫_ℝ| ≤ ‖x - c‖ * ‖stdBasis m k‖ := abs_real_inner_le_norm _ _
  _ = ‖x - c‖ := by rw [norm_stdBasis, mul_one]

theorem affine_mem_ball {c : ES m} {k : Fin m} {r : ℝ} {t : ℝ}
    (ht : |t - c k| < r) : c + (t - c k) • stdBasis m k ∈ Metric.ball c r := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_stdBasis, mul_one,
    Real.norm_eq_abs]
  exact ht

theorem affine_coord_self {c : ES m} {k : Fin m} (t : ℝ) :
    (c + (t - c k) • stdBasis m k : ES m) k = t := by
  change c k + (t - c k) * (stdBasis m k : ES m) k = t
  rw [coord_stdBasis_self]; ring

theorem affine_coord_of_ne {c : ES m} {j k : Fin m} (h : j ≠ k) (t : ℝ) :
    (c + (t - c k) • stdBasis m k : ES m) j = c j := by
  change c j + (t - c k) * (stdBasis m k : ES m) j = c j
  rw [coord_stdBasis_of_ne h]; ring

theorem exists_ne_index {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m) : ∃ a : Fin m, a ≠ k := by
  have h2 : 1 < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨a₁, a₂, -, -, ha₁₂⟩ := Finset.one_lt_card_iff.mp h2
  by_cases h : a₁ = k
  · exact ⟨a₂, fun ha2k => ha₁₂ (h.trans ha2k.symm)⟩
  · exact ⟨a₁, h⟩

theorem sum_coord_stdBasis (v : ES m) : ∑ i, (v i) • stdBasis m i = v := coord_expand v

theorem clm2_eq_zero_of_stdBasis (B : ES m →L[ℝ] (ES m →L[ℝ] ES m))
    (h : ∀ i j : Fin m, B (stdBasis m j) (stdBasis m i) = 0) (v w : ES m) :
    B v w = 0 := by
  conv_lhs => rw [← sum_coord_stdBasis v, ← sum_coord_stdBasis w]
  rw [map_sum]
  simp_rw [map_smul]
  have step : ∀ x : Fin m, (B (∑ j, (v j) • stdBasis m j)) (stdBasis m x) = 0 := by
    intro x
    rw [map_sum, sum_apply]
    simp_rw [map_smul, smul_apply]
    simp_rw [h]
    simp
  simp_rw [step]
  simp

theorem hasDerivAt_profile (g : ES m → ℝ) {c : ES m} {r : ℝ} {k : Fin m}
    (hdiff : DifferentiableOn ℝ g (Metric.ball c r)) {t : ℝ} (ht : |t - c k| < r) :
    HasDerivAt (fun s => g (c + (s - c k) • stdBasis m k))
      (fderiv ℝ g (c + (t - c k) • stdBasis m k) (stdBasis m k)) t := by
  have hσ : HasDerivAt (fun s => c + (s - c k) • stdBasis m k) (stdBasis m k) t := by
    have heq : (fun s : ℝ => c + (s - c k) • stdBasis m k)
        = fun s => (c - (c k) • stdBasis m k) + s • stdBasis m k := by
      funext s; module
    rw [heq]; exact hasDerivAt_affine _ _ _
  have hmem : c + (t - c k) • stdBasis m k ∈ Metric.ball c r := affine_mem_ball ht
  have hgAt : DifferentiableAt ℝ g (c + (t - c k) • stdBasis m k) :=
    hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  exact hgAt.hasFDerivAt.comp_hasDerivAt t hσ

theorem fderiv_eq_of_mem_ball_of_coord_eq {g : ES m → ℝ} {c : ES m} {r : ℝ} {k : Fin m}
    (hdiff : DifferentiableOn ℝ g (Metric.ball c r))
    (hfac : ∀ x y : ES m, x ∈ Metric.ball c r → y ∈ Metric.ball c r → x k = y k → g x = g y)
    {z w : ES m} (hz : z ∈ Metric.ball c r) (hw : w ∈ Metric.ball c r) (hzw : z k = w k)
    (v : ES m) :
    fderiv ℝ g z v = fderiv ℝ g w v := by
  have hev : (fun u => g (z + u)) =ᶠ[𝓝 (0 : ES m)] fun u => g (w + u) := by
    have hTz : Tendsto (fun u => z + u) (𝓝 0) (𝓝 z) :=
      (continuous_const.add continuous_id).tendsto' 0 z (add_zero z)
    have hTw : Tendsto (fun u => w + u) (𝓝 0) (𝓝 w) :=
      (continuous_const.add continuous_id).tendsto' 0 w (add_zero w)
    have hz' : ∀ᶠ u in 𝓝 (0 : ES m), z + u ∈ Metric.ball c r :=
      hTz.eventually (Metric.isOpen_ball.mem_nhds hz)
    have hw' : ∀ᶠ u in 𝓝 (0 : ES m), w + u ∈ Metric.ball c r :=
      hTw.eventually (Metric.isOpen_ball.mem_nhds hw)
    filter_upwards [hz', hw'] with u hzu hwu
    exact hfac _ _ hzu hwu (by change z k + u k = w k + u k; rw [hzw])
  have hzf : HasFDerivAt (fun u => g (z + u)) (fderiv ℝ g z) 0 := by
    have hgz : HasFDerivAt g (fderiv ℝ g z) z :=
      (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasFDerivAt
    have hgz' : HasFDerivAt g (fderiv ℝ g z) (z + (0 : ES m)) := by
      rw [add_zero]; exact hgz
    have htr : HasFDerivAt (fun u : ES m => z + u) (ContinuousLinearMap.id ℝ (ES m)) 0 := by
      simpa using (hasFDerivAt_id (0 : ES m)).const_add z
    have hcomp := hgz'.comp 0 htr
    rw [ContinuousLinearMap.comp_id] at hcomp
    exact hcomp
  have hwf : HasFDerivAt (fun u => g (w + u)) (fderiv ℝ g w) 0 := by
    have hgw : HasFDerivAt g (fderiv ℝ g w) w :=
      (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasFDerivAt
    have hgw' : HasFDerivAt g (fderiv ℝ g w) (w + (0 : ES m)) := by
      rw [add_zero]; exact hgw
    have htr : HasFDerivAt (fun u : ES m => w + u) (ContinuousLinearMap.id ℝ (ES m)) 0 := by
      simpa using (hasFDerivAt_id (0 : ES m)).const_add w
    have hcomp := hgw'.comp 0 htr
    rw [ContinuousLinearMap.comp_id] at hcomp
    exact hcomp
  have heq := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
  rw [hzf.fderiv, hwf.fderiv] at heq
  exact congrFun (congrArg DFunLike.coe heq) v

theorem inner_sum_smul_stdBasis (B : Fin m → ℝ) (l : Fin m) :
    ⟪∑ j, B j • stdBasis m j, stdBasis m l⟫_ℝ = B l := by
  rw [sum_inner]
  simp_rw [real_inner_smul_left, stdBasis_inner]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem inner_sum_smul_stdBasis_right (B : Fin m → ℝ) (v : ES m) :
    ⟪∑ j, B j • stdBasis m j, v⟫_ℝ = ∑ l, B l * v l := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro l _
  rw [real_inner_smul_left, inner_stdBasis_left]

theorem normSq_sum_smul_stdBasis (B : Fin m → ℝ) :
    ‖∑ j, B j • stdBasis m j‖^2 = ∑ l, (B l)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [inner_sum]
  simp_rw [real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro l _
  rw [inner_sum_smul_stdBasis B l, pow_two]

theorem norm_sq_eq_sum (v : ES m) : ‖v‖^2 = ∑ i, (v i)^2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply]
  simp [pow_two]

theorem normSq_eq_sum_inner (v : ES m) : ‖v‖^2 = ∑ l, (⟪v, stdBasis m l⟫_ℝ)^2 := by
  conv_lhs => rw [← (stdBasis m).sum_repr v]
  rw [normSq_sum_smul_stdBasis]
  apply Finset.sum_congr rfl
  intro l _
  rw [(stdBasis m).repr_apply_apply, real_inner_comm]

theorem inner_eq_sum_coord (v w : ES m) : ⟪v, w⟫_ℝ = ∑ l, ⟪v, stdBasis m l⟫_ℝ * (w l) := by
  conv_lhs => rw [← (stdBasis m).sum_repr v]
  rw [inner_sum_smul_stdBasis_right]
  apply Finset.sum_congr rfl
  intro l _
  rw [(stdBasis m).repr_apply_apply, real_inner_comm]

variable (hm : 3 ≤ m) (F : ES m → ES m) (hF : ContDiff ℝ 3 F) {U : Set (ES m)}
  (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) (hU : IsOpen U)

include hF hconf hU

theorem recipPartial_factoring {c : ES m} {r : ℝ} (_hr : 0 < r)
    (hball : Metric.ball c r ⊆ U) (k : Fin m)
    {x y : ES m} (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r) (hk : x k = y k) :
    dρ hm F k x = dρ hm F k y := by
  have hdiff : DifferentiableOn ℝ (dρ hm F k) (Metric.ball c r) :=
    (differentiableOn_recipPartial hm F hF hconf k).mono hball
  have hzero : ∀ z ∈ Metric.ball c r, ∀ j : Fin m, j ≠ k →
      fderiv ℝ (dρ hm F k) z (stdBasis m j) = 0 :=
    fun z hz j hjk => recipConfFactor_offdiag hm F hF hconf hU (hball hz) hjk
  exact apply_eq_of_off_partial_eq_zero Metric.isOpen_ball (convex_ball c r) hdiff hzero hx hy hk

theorem ddρ_const {c : ES m} {r : ℝ} (hr : 0 < r) (hball : Metric.ball c r ⊆ U)
    {z : ES m} (hz : z ∈ Metric.ball c r) (k : Fin m) :
    ddρ hm F k z = ddρ hm F k c := by
  have hdiff : ∀ j, DifferentiableOn ℝ (dρ hm F j) (Metric.ball c r) :=
    fun j => (differentiableOn_recipPartial hm F hF hconf j).mono hball
  have hfac : ∀ j, ∀ x y : ES m, x ∈ Metric.ball c r → y ∈ Metric.ball c r → x j = y j →
      dρ hm F j x = dρ hm F j y :=
    fun j x y hx hy hj => recipPartial_factoring hm F hF hconf hU hr hball j hx hy hj
  obtain ⟨a, hak⟩ := exists_ne_index (by omega : 2 ≤ m) k
  have hwmem : c + (z k - c k) • stdBasis m k ∈ Metric.ball c r :=
    affine_mem_ball (lt_of_le_of_lt (abs_coord_sub_le k z c)
      (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz))
  have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have h1 : ddρ hm F k z
      = ddρ hm F k (c + (z k - c k) • stdBasis m k) :=
    fderiv_eq_of_mem_ball_of_coord_eq (hdiff k) (hfac k) hz hwmem
      (affine_coord_self (z k)).symm (stdBasis m k)
  have h2 : ddρ hm F k (c + (z k - c k) • stdBasis m k)
      = ddρ hm F a (c + (z k - c k) • stdBasis m k) :=
    recipConfFactor_diag hm F hF hconf hU (hball hwmem) k a
  have h3 : ddρ hm F a (c + (z k - c k) • stdBasis m k) = ddρ hm F a c :=
    fderiv_eq_of_mem_ball_of_coord_eq (hdiff a) (hfac a) hwmem hc
      (affine_coord_of_ne hak (z k)) (stdBasis m a)
  have h4 : ddρ hm F a c = ddρ hm F k c :=
    recipConfFactor_diag hm F hF hconf hU (hball hc) a k
  exact h1.trans (h2.trans (h3.trans h4))

theorem dρ_affine {c : ES m} {r : ℝ} (hr : 0 < r) (hball : Metric.ball c r ⊆ U)
    (k : Fin m) {z : ES m} (hz : z ∈ Metric.ball c r) :
    dρ hm F k z = (ddρ hm F k c) * (z k) + (dρ hm F k c - ddρ hm F k c * (c k)) := by
  have hdiffk : DifferentiableOn ℝ (dρ hm F k) (Metric.ball c r) :=
    (differentiableOn_recipPartial hm F hF hconf k).mono hball
  have Ioo_of_abs : ∀ t : ℝ, |t - c k| < r ↔ t ∈ Set.Ioo (c k - r) (c k + r) := by
    intro t
    rw [Set.mem_Ioo, abs_lt]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hpdiff : DifferentiableOn ℝ
      (fun s => dρ hm F k (c + (s - c k) • stdBasis m k)) (Set.Ioo (c k - r) (c k + r)) := by
    intro t ht
    exact (hasDerivAt_profile (dρ hm F k) hdiffk
      ((Ioo_of_abs t).mpr ht)).differentiableAt.differentiableWithinAt
  have hpder : ∀ t ∈ Set.Ioo (c k - r) (c k + r),
      deriv (fun s => dρ hm F k (c + (s - c k) • stdBasis m k)) t = ddρ hm F k c := by
    intro t ht
    have ht' : |t - c k| < r := (Ioo_of_abs t).mpr ht
    rw [(hasDerivAt_profile (dρ hm F k) hdiffk ht').deriv]
    exact ddρ_const hm F hF hconf hU hr hball (affine_mem_ball ht') k
  have hck : c k ∈ Set.Ioo (c k - r) (c k + r) := by
    rw [Set.mem_Ioo]; constructor <;> linarith [hr]
  have hEq : Set.EqOn (fun s => dρ hm F k (c + (s - c k) • stdBasis m k))
      (fun s => (ddρ hm F k c) * s + (dρ hm F k c - ddρ hm F k c * (c k)))
      (Set.Ioo (c k - r) (c k + r)) := by
    apply IsOpen.eqOn_of_deriv_eq isOpen_Ioo (convex_Ioo _ _).isPreconnected hpdiff
    · exact ((differentiable_id.const_mul _).add (differentiable_const _)).differentiableOn
    · intro t ht
      rw [hpder t ht]
      have h3 := ((hasDerivAt_id t).const_mul (ddρ hm F k c)).add
        (hasDerivAt_const t (dρ hm F k c - ddρ hm F k c * (c k)))
      rw [mul_one, add_zero] at h3
      exact h3.deriv.symm
    · exact hck
    · show dρ hm F k (c + (c k - c k) • stdBasis m k)
        = (ddρ hm F k c) * (c k) + (dρ hm F k c - ddρ hm F k c * (c k))
      rw [sub_self, zero_smul, add_zero]; ring
  have hzk : z k ∈ Set.Ioo (c k - r) (c k + r) := by
    rw [← Ioo_of_abs]
    exact lt_of_le_of_lt (abs_coord_sub_le k z c)
      (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz)
  have h1 : dρ hm F k z = dρ hm F k (c + (z k - c k) • stdBasis m k) :=
    recipPartial_factoring hm F hF hconf hU hr hball k hz
      (affine_mem_ball (lt_of_le_of_lt (abs_coord_sub_le k z c)
        (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz))) (affine_coord_self (z k)).symm
  rw [h1]
  exact hEq hzk

theorem recipConfFactor_quadratic {c : ES m} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball c r ⊆ U) :
    ∃ A a₀ : ℝ, ∃ Bv : ES m,
      (∀ z ∈ Metric.ball c r, recipConfFactor hm F z = (A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ + a₀)
      ∧ (∀ z ∈ Metric.ball c r, ∀ j, dρ hm F j z = A * (z j) + ⟪Bv, stdBasis m j⟫_ℝ)
      ∧ (∀ z ∈ Metric.ball c r, ∀ j, ddρ hm F j z = A) := by
  have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  let j₀ : Fin m := ⟨0, by omega⟩
  set A := ddρ hm F j₀ c with hAdef
  have hddc : ∀ j, ddρ hm F j c = A := fun j => by
    change fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m j)) c (stdBasis m j) = A
    rw [recipConfFactor_diag hm F hF hconf hU (hball hc) j j₀]
  set Bv : ES m := ∑ j, (dρ hm F j c - A * (c j)) • stdBasis m j with hBvdef
  have hd : ∀ z ∈ Metric.ball c r, ∀ j, dρ hm F j z = A * (z j) + ⟪Bv, stdBasis m j⟫_ℝ := by
    intro w hw j
    rw [hBvdef, inner_sum_smul_stdBasis]
    have h2 := dρ_affine hm F hF hconf hU hr hball j hw
    rw [hddc j] at h2
    exact h2
  have hdd : ∀ z ∈ Metric.ball c r, ∀ j, ddρ hm F j z = A := by
    intro w hw j
    rw [ddρ_const hm F hF hconf hU hr hball hw j, hddc j]
  have hQ0 : ∀ z ∈ Metric.ball c r, ∀ j, fderiv ℝ
      (fun z => recipConfFactor hm F z - ((A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ)) z (stdBasis m j)
      = 0 := by
    intro w hw j
    have hρd : DifferentiableAt ℝ (recipConfFactor hm F) w :=
      (hasFDerivAt_recipConfFactor hm F hF hconf (hball hw)).differentiableAt
    have hns : DifferentiableAt ℝ (fun z => ‖z‖^2) w :=
      (hasStrictFDerivAt_norm_sq w).hasFDerivAt.differentiableAt
    have hinnd : DifferentiableAt ℝ (fun z => ⟪Bv, z⟫_ℝ) w :=
      (differentiableAt_const (c := Bv)).inner ℝ differentiableAt_id
    have hPd : DifferentiableAt ℝ (fun z => (A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ) w :=
      (hns.const_mul (A / 2)).add hinnd
    rw [show (fun z => recipConfFactor hm F z - ((A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ))
        = recipConfFactor hm F - (fun z => (A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ) from rfl]
    rw [fderiv_sub hρd hPd, sub_apply]
    rw [show fderiv ℝ (recipConfFactor hm F) w (stdBasis m j) = dρ hm F j w from rfl,
      hd w hw j]
    rw [show (fun z => (A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ)
        = (fun z => (A / 2) * ‖z‖^2) + (fun z => ⟪Bv, z⟫_ℝ) from rfl]
    rw [fderiv_add (hns.const_mul (A / 2)) hinnd, add_apply]
    have hns2 : fderiv ℝ (fun z => (A / 2) * ‖z‖^2) w (stdBasis m j) = A * (w j) := by
      have h1 : HasFDerivAt (fun z => ‖z‖^2) (2 • innerSL ℝ w) w :=
        (hasStrictFDerivAt_norm_sq w).hasFDerivAt
      have h2 := h1.const_mul (A / 2)
      rw [h2.fderiv]
      simp only [smul_apply, smul_eq_mul]
      rw [show (innerSL ℝ w) (stdBasis m j) = w j from by
        rw [show (innerSL ℝ w) (stdBasis m j) = ⟪w, stdBasis m j⟫_ℝ from
          congrFun (coe_innerSL_apply (𝕜 := ℝ) w) (stdBasis m j)]
        exact inner_stdBasis_right j w]
      ring
    rw [hns2]
    have hinn : fderiv ℝ (fun z => ⟪Bv, z⟫_ℝ) w (stdBasis m j) = ⟪Bv, stdBasis m j⟫_ℝ := by
      rw [show (fun z => ⟪Bv, z⟫_ℝ) = ⇑(innerSL ℝ Bv) from
        (coe_innerSL_apply (𝕜 := ℝ) Bv).symm]
      rw [(innerSL ℝ Bv).hasFDerivAt.fderiv]
      exact congrFun (coe_innerSL_apply (𝕜 := ℝ) Bv) (stdBasis m j)
    rw [hinn]
    ring
  have hQ0' : ∀ z ∈ Metric.ball c r,
      fderiv ℝ (fun z => recipConfFactor hm F z - ((A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ)) z = 0 := by
    intro w hw
    ext v
    conv_lhs => rw [← sum_coord_stdBasis v]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul, hQ0 w hw, mul_zero]
    simp
  have hdiffQ : DifferentiableOn ℝ
      (fun z => recipConfFactor hm F z - ((A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ)) (Metric.ball c r) := by
    intro w hw
    have hρd : DifferentiableAt ℝ (recipConfFactor hm F) w :=
      (hasFDerivAt_recipConfFactor hm F hF hconf (hball hw)).differentiableAt
    have hns : DifferentiableAt ℝ (fun z => ‖z‖^2) w :=
      (hasStrictFDerivAt_norm_sq w).hasFDerivAt.differentiableAt
    have hinnd : DifferentiableAt ℝ (fun z => ⟪Bv, z⟫_ℝ) w :=
      (differentiableAt_const (c := Bv)).inner ℝ differentiableAt_id
    have h1 := hρd.sub ((hns.const_mul (A / 2)).add hinnd)
    rw [show (recipConfFactor hm F - ((fun z => (A / 2) * ‖z‖^2) + fun z => ⟪Bv, z⟫_ℝ))
        = (fun z => recipConfFactor hm F z - ((A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ)) from rfl] at h1
    exact h1.differentiableWithinAt
  refine ⟨A, recipConfFactor hm F c - ((A / 2) * ‖c‖^2 + ⟪Bv, c⟫_ℝ), Bv, ?_, hd, hdd⟩
  intro z hz
  have hconst := Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball c r).isPreconnected
    hdiffQ (fun w hw => hQ0' w hw) hz hc
  have hconst' : recipConfFactor hm F z - ((A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ)
      = recipConfFactor hm F c - ((A / 2) * ‖c‖^2 + ⟪Bv, c⟫_ℝ) := hconst
  linarith [hconst']

theorem recipConfFactor_scalar_flat {z : ES m} (hz : z ∈ U) {a b : Fin m} (hab : a ≠ b) :
    recipConfFactor hm F z * (ddρ hm F a z + ddρ hm F b z)
      = ∑ l : Fin m, (dρ hm F l z)^2 := by
  have hσ : 0 < confFactorSq hm F z := confFactorSq_pos hm F hconf hz
  have haa := ddRecip_eq hm F hF hconf hU hz a a
  have hbb := ddRecip_eq hm F hF hconf hU hz b b
  have hgl : ∀ l : Fin m, fderiv ℝ (recipConfFactor hm F) z (stdBasis m l)
      = -(1/2 : ℝ) * (confFactorSq hm F z) ^ (-(3/2 : ℝ)) * dc2 hm F l z :=
    fun l => dRecip_eq hm F hF hconf hz l
  have hpd := pairdiag hm F hF hconf hU hz hab
  have key1 : (confFactorSq hm F z) ^ (-(1/2 : ℝ)) * (confFactorSq hm F z) ^ (-(3/2 : ℝ))
      = (confFactorSq hm F z) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hσ]; norm_num
  have key2 : (confFactorSq hm F z) ^ (-(1/2 : ℝ)) * (confFactorSq hm F z) ^ (-(5/2 : ℝ))
      = (confFactorSq hm F z) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hσ]; norm_num
  have key3 : ((confFactorSq hm F z) ^ (-(3/2 : ℝ)))^2
      = (confFactorSq hm F z) ^ (-(3 : ℝ)) := by
    rw [sq, ← Real.rpow_add hσ]; norm_num
  have key4 : (confFactorSq hm F z) ^ (-(2 : ℝ))
      = (confFactorSq hm F z) ^ (-(3 : ℝ)) * (confFactorSq hm F z) := by
    have h : (confFactorSq hm F z) ^ (-(3 : ℝ)) * (confFactorSq hm F z) ^ (1 : ℝ)
        = (confFactorSq hm F z) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hσ]; norm_num
    rw [Real.rpow_one] at h
    exact h.symm
  rw [show recipConfFactor hm F z = (confFactorSq hm F z) ^ (-(1/2 : ℝ)) from rfl]
  change (confFactorSq hm F z) ^ (-(1/2 : ℝ)) *
      (fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m a)) z (stdBasis m a)
      + fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m b)) z (stdBasis m b))
    = ∑ l : Fin m, (fderiv ℝ (recipConfFactor hm F) z (stdBasis m l))^2
  rw [haa, hbb]
  rw [Finset.sum_congr rfl (fun l _ => congrArg (· ^ 2) (hgl l))]
  have e1 : (confFactorSq hm F z) ^ (-(1/2 : ℝ)) *
        (-(1/2 : ℝ) * (confFactorSq hm F z) ^ (-(3/2 : ℝ)) * ddc2 hm F a a z
          + (3/4 : ℝ) * (confFactorSq hm F z) ^ (-(5/2 : ℝ)) * dc2 hm F a z * dc2 hm F a z
        + (-(1/2 : ℝ) * (confFactorSq hm F z) ^ (-(3/2 : ℝ)) * ddc2 hm F b b z
          + (3/4 : ℝ) * (confFactorSq hm F z) ^ (-(5/2 : ℝ)) * dc2 hm F b z * dc2 hm F b z))
      = -(1/2 : ℝ) * (confFactorSq hm F z) ^ (-(2 : ℝ))
          * (ddc2 hm F a a z + ddc2 hm F b b z)
        + (3/4 : ℝ) * (confFactorSq hm F z) ^ (-(3 : ℝ))
          * (dc2 hm F a z * dc2 hm F a z + dc2 hm F b z * dc2 hm F b z) := by
    linear_combination
      (-(1/2) * ddc2 hm F a a z) * key1 + ((3/4) * dc2 hm F a z * dc2 hm F a z) * key2
        + (-(1/2) * ddc2 hm F b b z) * key1
        + ((3/4) * dc2 hm F b z * dc2 hm F b z) * key2
  have e2 : ∑ l : Fin m, (-(1/2 : ℝ) * (confFactorSq hm F z) ^ (-(3/2 : ℝ)) * dc2 hm F l z)^2
      = (1/4 : ℝ) * (confFactorSq hm F z) ^ (-(3 : ℝ)) * ∑ l, (dc2 hm F l z)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    linear_combination ((1/4) * (dc2 hm F l z)^2) * key3
  rw [e1, e2]
  linear_combination (-(1/4) * (confFactorSq hm F z) ^ (-(3 : ℝ))) * hpd
    + (-(1/2) * (ddc2 hm F a a z + ddc2 hm F b b z)) * key4

theorem recipConfFactor_quadratic_full {c : ES m} (hc : c ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ A a₀ : ℝ, ∃ Bv : ES m,
      Metric.ball c r ⊆ U
      ∧ (∀ z ∈ Metric.ball c r, recipConfFactor hm F z = (A / 2) * ‖z‖^2 + ⟪Bv, z⟫_ℝ + a₀)
      ∧ 2 * A * a₀ = ‖Bv‖^2
      ∧ (∀ z ∈ Metric.ball c r, ∀ j, dρ hm F j z = A * (z j) + ⟪Bv, stdBasis m j⟫_ℝ)
      ∧ (∀ z ∈ Metric.ball c r, ∀ j, ddρ hm F j z = A) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU c hc
  obtain ⟨A, a₀, Bv, hquad, hd, hdd⟩ := recipConfFactor_quadratic hm F hF hconf hU hr hball
  refine ⟨r, hr, A, a₀, Bv, hball, hquad, ?_, hd, hdd⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin m, a ≠ b := by
    have h2 : 1 < (Finset.univ : Finset (Fin m)).card := by
      rw [Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨a, b, -, -, hab⟩ := Finset.one_lt_card_iff.mp h2
    exact ⟨a, b, hab⟩
  have hcm : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hs := recipConfFactor_scalar_flat hm F hF hconf hU (hball hcm) hab
  rw [hdd c hcm a, hdd c hcm b, hquad c hcm] at hs
  rw [Finset.sum_congr rfl (fun l _ => congrArg (· ^ 2) (hd c hcm l))] at hs
  have hexp : ∑ l, (A * (c l) + ⟪Bv, stdBasis m l⟫_ℝ)^2
      = A^2 * (∑ l, (c l)^2) + 2 * A * (∑ l, ⟪Bv, stdBasis m l⟫_ℝ * (c l))
        + ∑ l, (⟪Bv, stdBasis m l⟫_ℝ)^2 := by
    have h1 : ∀ l : Fin m, (A * (c l) + ⟪Bv, stdBasis m l⟫_ℝ)^2
        = A^2 * (c l)^2 + 2 * A * (⟪Bv, stdBasis m l⟫_ℝ * (c l))
          + (⟪Bv, stdBasis m l⟫_ℝ)^2 := fun l => by ring
    rw [Finset.sum_congr rfl (fun l _ => h1 l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexp, ← norm_sq_eq_sum c, ← inner_eq_sum_coord Bv c, ← normSq_eq_sum_inner Bv] at hs
  linear_combination hs

omit hF hconf hU in
theorem recipConfFactor_cases {c : ES m} {r : ℝ} {A a₀ : ℝ} {Bv : ES m}
    (hquad : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = (A / 2) * ‖z‖ ^ 2 + ⟪Bv, z⟫_ℝ + a₀)
    (hdisc : 2 * A * a₀ = ‖Bv‖ ^ 2) :
    (A = 0 ∧ ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = a₀)
    ∨ (A ≠ 0 ∧ ∀ z ∈ Metric.ball c r,
        recipConfFactor hm F z = (A / 2) * ‖z + (1/A) • Bv‖^2) := by
  by_cases hA : A = 0
  · left
    have hBv0 : Bv = 0 := by
      have h1 : ‖Bv‖^2 = 0 := by rw [← hdisc, hA]; ring
      have h2 : ‖Bv‖ = 0 := sq_eq_zero_iff.mp h1
      exact norm_eq_zero.mp h2
    exact ⟨hA, fun z hz => by
      rw [hquad z hz, hA, hBv0]
      simp [inner_zero_left]⟩
  · right
    refine ⟨hA, fun z hz => ?_⟩
    rw [hquad z hz]
    have hBv' : ‖(1/A) • Bv‖^2 = (1/A)^2 * ‖Bv‖^2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_div, abs_one, div_pow, div_pow, one_pow,
        sq_abs]
    have h1 : ‖z + (1/A) • Bv‖^2
        = ‖z‖^2 + 2 * ((1/A) * ⟪Bv, z⟫_ℝ) + (1/A)^2 * ‖Bv‖^2 := by
      rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm z Bv, hBv']
    rw [h1, ← hdisc]
    field_simp [hA]

omit hF hU in
theorem confFactorSq_const_of_recipConfFactor_const {c : ES m} {r : ℝ}
    (hball : Metric.ball c r ⊆ U) {a₀ : ℝ}
    (hρconst : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = a₀) :
    ∀ z ∈ Metric.ball c r, confFactorSq hm F z = a₀ ^ (-(2 : ℝ)) := by
  intro z hz
  have hσ : 0 < confFactorSq hm F z := confFactorSq_pos hm F hconf (hball hz)
  have h1 : recipConfFactor hm F z = (confFactorSq hm F z) ^ (-(1/2 : ℝ)) := rfl
  rw [hρconst z hz] at h1
  rw [h1, ← Real.rpow_mul hσ.le, show (-(1/2 : ℝ)) * (-(2 : ℝ)) = 1 by norm_num,
    Real.rpow_one]

omit hF hU in
theorem dc2_eq_zero_of_recipConfFactor_const {c : ES m} {r : ℝ}
    (hball : Metric.ball c r ⊆ U) {a₀ : ℝ}
    (hρconst : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = a₀) :
    ∀ z ∈ Metric.ball c r, ∀ l, dc2 hm F l z = 0 := by
  intro z hz l
  have hev : confFactorSq hm F =ᶠ[𝓝 z] fun _ => a₀ ^ (-(2 : ℝ)) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
      (confFactorSq_const_of_recipConfFactor_const hm F hconf hball hρconst)
  change fderiv ℝ (confFactorSq hm F) z (stdBasis m l) = 0
  rw [hev.fderiv_eq]
  simp

theorem HessF_eq_zero_of_recipConfFactor_const {c : ES m} {r : ℝ}
    (hball : Metric.ball c r ⊆ U) {a₀ : ℝ}
    (hρconst : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = a₀) :
    ∀ z ∈ Metric.ball c r, HessF F z = 0 := by
  intro z hz
  have hdc2 := dc2_eq_zero_of_recipConfFactor_const hm F hconf hball hρconst
  have hH0 : ∀ i j : Fin m, HessF F z (stdBasis m j) (stdBasis m i) = 0 := by
    intro i j
    have hk : ∀ k : Fin m, ⟪HessF F z (stdBasis m j) (stdBasis m i), pF F k z⟫_ℝ = 0 := by
      intro k
      have h := christoffel' hm F hF hconf hU (hball hz) i j k
      rw [hdc2 z hz i, hdc2 z hz j, hdc2 z hz k] at h
      simpa using h
    have hvv : ⟪HessF F z (stdBasis m j) (stdBasis m i),
        HessF F z (stdBasis m j) (stdBasis m i)⟫_ℝ = 0 := by
      have hp := frame_parseval hm F hconf (hball hz) (HessF F z (stdBasis m j) (stdBasis m i))
        (HessF F z (stdBasis m j) (stdBasis m i))
      rw [hp]
      simp [hk]
    exact inner_self_eq_zero.mp hvv
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  change HessF F z v w = 0
  exact clm2_eq_zero_of_stdBasis (HessF F z) hH0 v w

theorem isSimilarity_on_ball_of_recipConfFactor_const {c : ES m} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball c r ⊆ U) {a₀ : ℝ}
    (hρconst : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = a₀) :
    ∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m,
      ∀ z ∈ Metric.ball c r, F z = L z + t := by
  have hcm : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hH0 := HessF_eq_zero_of_recipConfFactor_const hm F hF hconf hU hball hρconst
  have hdiffF : DifferentiableOn ℝ (fderiv ℝ F) (Metric.ball c r) :=
    ((contDiff_fderiv F hF).differentiable (by norm_num)).differentiableOn.mono
      (Set.subset_univ _)
  have hfc : ∀ z ∈ Metric.ball c r, fderiv ℝ F z = fderiv ℝ F c := by
    intro z hz
    have h0 : ∀ w ∈ Metric.ball c r, fderivWithin ℝ (fderiv ℝ F) (Metric.ball c r) w = 0 := by
      intro w hw
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
      exact hH0 w hw
    exact (convex_ball c r).is_const_of_fderivWithin_eq_zero hdiffF h0 hz hcm
  refine ⟨fderiv ℝ F c, hconf c (hball hcm), F c - (fderiv ℝ F c) c, fun z hz => ?_⟩
  have hFd : DifferentiableOn ℝ (fun z => F z - (fderiv ℝ F c) z) (Metric.ball c r) := by
    intro w hw
    have h1 : DifferentiableAt ℝ F w := (hF.differentiable (by norm_num)) w
    have h2 := h1.sub ((fderiv ℝ F c).differentiableAt)
    rw [show (F - ⇑(fderiv ℝ F c)) = (fun z => F z - (fderiv ℝ F c) z) from rfl] at h2
    exact h2.differentiableWithinAt
  have hG0 : ∀ w ∈ Metric.ball c r,
      fderivWithin ℝ (fun z => F z - (fderiv ℝ F c) z) (Metric.ball c r) w = 0 := by
    intro w hw
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
    have hFd' : DifferentiableAt ℝ F w := (hF.differentiable (by norm_num)) w
    have hLd' : DifferentiableAt ℝ (⇑(fderiv ℝ F c)) w := (fderiv ℝ F c).differentiableAt
    rw [show (fun z => F z - (fderiv ℝ F c) z) = F - ⇑(fderiv ℝ F c) from rfl]
    rw [fderiv_sub hFd' hLd']
    rw [(fderiv ℝ F c).hasFDerivAt.fderiv, hfc w hw, sub_self]
  have hGc := (convex_ball c r).is_const_of_fderivWithin_eq_zero hFd hG0 hz hcm
  have h3 : F z - (fderiv ℝ F c) z = F c - (fderiv ℝ F c) c := hGc
  rw [sub_eq_iff_eq_add] at h3
  rw [h3, add_comm]

theorem isSimilarity_on_ball_of_quadratic_A_eq_zero {c : ES m} {r : ℝ} (hr : 0 < r)
    {A a₀ : ℝ} {Bv : ES m} (hball : Metric.ball c r ⊆ U)
    (hquad : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = (A / 2) * ‖z‖ ^ 2 + ⟪Bv, z⟫_ℝ + a₀)
    (hdisc : 2 * A * a₀ = ‖Bv‖ ^ 2) (hA : A = 0) :
    ∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m,
      ∀ z ∈ Metric.ball c r, F z = L z + t := by
  obtain ⟨-, hρconst⟩ | ⟨hAne, -⟩ := recipConfFactor_cases hm F hquad hdisc
  · exact isSimilarity_on_ball_of_recipConfFactor_const hm F hF hconf hU hr hball hρconst
  · exact absurd hA hAne

end

end DifferentialGeometry.LiouvilleQuadratic
