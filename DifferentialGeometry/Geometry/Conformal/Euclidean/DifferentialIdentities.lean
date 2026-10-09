/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Batteries.Data.BitVec.Lemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder

open RealInnerProductSpace InnerProductSpace Filter
open scoped Topology

namespace DifferentialGeometry.LiouvilleRigidity

variable {m : ℕ} (hm : 3 ≤ m)

abbrev ES (m : ℕ) := EuclideanSpace ℝ (Fin m)

noncomputable def stdBasis (m : ℕ) : OrthonormalBasis (Fin m) ℝ (ES m) :=
  EuclideanSpace.basisFun (Fin m) ℝ

theorem stdBasis_inner (i j : Fin m) :
    ⟪stdBasis m i, stdBasis m j⟫_ℝ = if i = j then 1 else 0 := by
  have h := (stdBasis m).orthonormal
  rw [orthonormal_iff_ite] at h
  exact h i j

variable (F : ES m → ES m) {U : Set (ES m)}

noncomputable def confFactor (F : ES m → ES m) (x : ES m) : ℝ :=
  ‖fderiv ℝ F x (stdBasis m ⟨0, by omega⟩)‖

noncomputable def confFactorSq (F : ES m → ES m) (x : ES m) : ℝ :=
  (confFactor hm F x) ^ 2

theorem confFactorSq_eq (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) :
    ∃ c : ℝ, 0 < c ∧ (∀ u v : ES m, ⟪fderiv ℝ F x u, fderiv ℝ F x v⟫_ℝ = c * ⟪u, v⟫_ℝ)
      ∧ confFactorSq hm F x = c := by
  obtain ⟨c, hc, huv⟩ := (isConformalMap_iff _).1 (hconf x hx)
  refine ⟨c, hc, huv, ?_⟩
  have h00 := huv (stdBasis m ⟨0, by omega⟩) (stdBasis m ⟨0, by omega⟩)
  rw [stdBasis_inner, ite_eq_left rfl, mul_one] at h00
  rw [confFactorSq, confFactor, ← real_inner_self_eq_norm_sq, h00]

theorem inner_fderiv_eq_confFactorSq_mul
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) (u v : ES m) :
    ⟪fderiv ℝ F x u, fderiv ℝ F x v⟫_ℝ = confFactorSq hm F x * ⟪u, v⟫_ℝ := by
  obtain ⟨c, hc, huv, hsq⟩ := confFactorSq_eq hm F hconf hx
  rw [huv, hsq]

theorem confFactor_pos (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : 0 < confFactor hm F x := by
  obtain ⟨c, hc, huv, hsq⟩ := confFactorSq_eq hm F hconf hx
  have hpos : 0 < confFactorSq hm F x := hsq ▸ hc
  rw [confFactorSq] at hpos
  exact lt_of_le_of_ne' (norm_nonneg _) (sq_pos_iff.1 hpos)

theorem confFactor_ne_zero (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : confFactor hm F x ≠ 0 :=
  (confFactor_pos hm F hconf hx).ne'

theorem fderiv_inj (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : Function.Injective (fderiv ℝ F x) :=
  (hconf x hx).injective

noncomputable def pF (i : Fin m) (x : ES m) : ES m :=
  fderiv ℝ F x (stdBasis m i)

theorem contDiff_fderiv (hF : ContDiff ℝ 3 F) : ContDiff ℝ 2 (fderiv ℝ F) :=
  hF.fderiv_right (m := 2) (by norm_num)

theorem contDiff_pF (hF : ContDiff ℝ 3 F) (i : Fin m) : ContDiff ℝ 2 (pF F (m := m) i) := by
  have h2 : ContDiff ℝ 2 (fderiv ℝ F) := contDiff_fderiv F hF
  exact h2.clm_apply contDiff_const

theorem differentiable_pF (hF : ContDiff ℝ 3 F) (i : Fin m) : Differentiable ℝ (pF F (m := m) i) :=
  (contDiff_pF F hF i).differentiable (by norm_num)

theorem contDiff_confFactorSq (hF : ContDiff ℝ 3 F) : ContDiff ℝ 2 (confFactorSq hm F) := by
  have h2 : ContDiff ℝ 2 (pF F ⟨0, by omega⟩) := contDiff_pF F hF _
  have hrw : confFactorSq hm F = fun x => ⟪pF F ⟨0, by omega⟩ x, pF F ⟨0, by omega⟩ x⟫_ℝ := by
    funext x
    rw [confFactorSq, confFactor, pF, real_inner_self_eq_norm_sq]
  rw [hrw]
  exact ContDiff.inner ℝ h2 h2

theorem differentiable_confFactorSq (hF : ContDiff ℝ 3 F) :
    Differentiable ℝ (confFactorSq hm F) :=
  (contDiff_confFactorSq hm F hF).differentiable (by norm_num)

theorem inner_pF (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) (i j : Fin m) :
    ⟪pF F i x, pF F j x⟫_ℝ = confFactorSq hm F x * (if i = j then 1 else 0) := by
  rw [pF, pF, inner_fderiv_eq_confFactorSq_mul hm F hconf hx, stdBasis_inner]

noncomputable def HessF (x : ES m) : ES m →L[ℝ] ES m →L[ℝ] ES m :=
  fderiv ℝ (fderiv ℝ F) x

theorem HessF_symm (hF : ContDiff ℝ 3 F) (x : ES m) (v w : ES m) :
    HessF F x v w = HessF F x w v := by
  have h : IsSymmSndFDerivAt ℝ F x :=
    (hF.contDiffAt).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  exact h v w

theorem fderiv_pF_apply (hF : ContDiff ℝ 3 F) (i : Fin m) (x v : ES m) :
    fderiv ℝ (pF F i) x v = HessF F x v (stdBasis m i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (contDiff_fderiv F hF).differentiable (by norm_num) x
  have hc : DifferentiableAt ℝ (fun _ : ES m => stdBasis m i) x := differentiableAt_const _
  have h := fderiv_clm_apply hd hc
  have hconst : fderiv ℝ (fun _ : ES m => stdBasis m i) x = 0 := (hasFDerivAt_const _ _).fderiv
  rw [hconst, ContinuousLinearMap.comp_zero, zero_add] at h
  have h2 : fderiv ℝ (pF F i) x = (HessF F x).flip (stdBasis m i) := h
  rw [h2, ContinuousLinearMap.flip_apply]

theorem metric_rel_deriv (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) (i j : Fin m) (v : ES m) :
    ⟪HessF F x v (stdBasis m i), pF F j x⟫_ℝ + ⟪HessF F x v (stdBasis m j), pF F i x⟫_ℝ
      = fderiv ℝ (confFactorSq hm F) x v * (if i = j then 1 else 0) := by
  have hEq : (fun y => ⟪pF F i y, pF F j y⟫_ℝ) =ᶠ[𝓝 x]
      fun y => confFactorSq hm F y * (if i = j then 1 else 0) := by
    filter_upwards [hU.mem_nhds hx] with y hy using inner_pF hm F hconf hy i j
  have hfd : fderiv ℝ (fun y => ⟪pF F i y, pF F j y⟫_ℝ) x
      = fderiv ℝ (fun y => confFactorSq hm F y * (if i = j then 1 else 0)) x := hEq.fderiv_eq
  have hi : DifferentiableAt ℝ (pF F i) x := differentiable_pF F hF i x
  have hj : DifferentiableAt ℝ (pF F j) x := differentiable_pF F hF j x
  have hL : fderiv ℝ (fun y => ⟪pF F i y, pF F j y⟫_ℝ) x v
      = ⟪pF F i x, HessF F x v (stdBasis m j)⟫_ℝ + ⟪HessF F x v (stdBasis m i), pF F j x⟫_ℝ := by
    have hder := (hi.hasFDerivAt.inner ℝ hj.hasFDerivAt).fderiv
    rw [hder]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    rw [fderiv_pF_apply F hF, fderiv_pF_apply F hF]
  have hR : fderiv ℝ (fun y => confFactorSq hm F y * (if i = j then 1 else 0)) x v
      = fderiv ℝ (confFactorSq hm F) x v * (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · simp only [ite_eq_left hij, mul_one]
    · simp only [ite_eq_right hij, mul_zero]
      simp [fderiv_fun_const]
  have hmain := congrFun (congrArg DFunLike.coe hfd) v
  rw [hL, hR] at hmain
  rw [real_inner_comm (HessF F x v (stdBasis m j)) (pF F i x), add_comm] at hmain
  exact hmain

theorem christoffel (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) (i j k : Fin m) :
    ⟪HessF F x (stdBasis m j) (stdBasis m i), pF F k x⟫_ℝ
      = (fderiv ℝ (confFactorSq hm F) x (stdBasis m i) * (if j = k then 1 else 0)
        + fderiv ℝ (confFactorSq hm F) x (stdBasis m j) * (if i = k then 1 else 0)
        - fderiv ℝ (confFactorSq hm F) x (stdBasis m k) * (if i = j then 1 else 0)) / 2 := by
  have e1 := metric_rel_deriv hm F hF hconf hU hx i k (stdBasis m j)
  have e2 := metric_rel_deriv hm F hF hconf hU hx j k (stdBasis m i)
  have e3 := metric_rel_deriv hm F hF hconf hU hx i j (stdBasis m k)
  rw [HessF_symm F hF x (stdBasis m j) (stdBasis m k)] at e1
  rw [HessF_symm F hF x (stdBasis m i) (stdBasis m j),
      HessF_symm F hF x (stdBasis m i) (stdBasis m k)] at e2
  linarith

theorem pF_linearIndependent (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : LinearIndependent ℝ (fun i => pF F i x) := by
  have hinj : LinearMap.ker (fderiv ℝ F x).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 (fderiv_inj F hconf hx)
  have h := (stdBasis m).toBasis.linearIndependent.map' (fderiv ℝ F x).toLinearMap hinj
  have heq : (fderiv ℝ F x).toLinearMap ∘ ⇑(stdBasis m).toBasis = fun i => pF F i x := rfl
  rw [heq] at h
  exact h

theorem pF_span (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : Submodule.span ℝ (Set.range (fun i => pF F i x)) = ⊤ := by
  apply (pF_linearIndependent F hconf hx).span_eq_top_of_card_eq_finrank'
  rw [finrank_euclideanSpace, Fintype.card_fin]

noncomputable def onbF (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : OrthonormalBasis (Fin m) ℝ (ES m) :=
  OrthonormalBasis.mk (v := fun i => (confFactor hm F x)⁻¹ • pF F i x)
    (by
      rw [orthonormal_iff_ite]
      intro i j
      have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
      rw [real_inner_smul_left, real_inner_smul_right, inner_pF hm F hconf hx i j, confFactorSq]
      by_cases hij : i = j
      · simp only [ite_eq_left hij]; field_simp
      · simp only [ite_eq_right hij]; field_simp)
    (by
      have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
      have hsp := pF_span F hconf hx
      rw [← hsp, Submodule.span_le]
      rintro v ⟨i, rfl⟩
      change pF F i x ∈ Submodule.span ℝ (Set.range fun i => (confFactor hm F x)⁻¹ • pF F i x)
      have hvi : pF F i x = confFactor hm F x • ((confFactor hm F x)⁻¹ • pF F i x) :=
        (smul_inv_smul₀ hcf _).symm
      rw [hvi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem onbF_apply (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) (i : Fin m) :
    onbF hm F hconf hx i = (confFactor hm F x)⁻¹ • pF F i x :=
  congrFun (OrthonormalBasis.coe_mk _ _) i

theorem frame_parseval (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) (u v : ES m) :
    ⟪u, v⟫_ℝ = (confFactorSq hm F x)⁻¹ *
      ∑ i, ⟪u, pF F i x⟫_ℝ * ⟪pF F i x, v⟫_ℝ := by
  have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
  have hparse := (onbF hm F hconf hx).sum_inner_mul_inner u v
  rw [← hparse]
  simp_rw [onbF_apply hm F hconf hx]
  simp_rw [real_inner_smul_left, real_inner_smul_right]
  rw [confFactorSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

noncomputable def D3F (x u v w : ES m) : ES m :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x u v w

theorem contDiff_HessF (hF : ContDiff ℝ 3 F) : ContDiff ℝ 1 (HessF F) :=
  (contDiff_fderiv F hF).fderiv_right (m := 1) (by norm_num)

theorem D3F_symm12 (hF : ContDiff ℝ 3 F) (x u v w : ES m) :
    D3F F x u v w = D3F F x v u w := by
  have h : IsSymmSndFDerivAt ℝ (fderiv ℝ F) x :=
    (contDiff_fderiv F hF).contDiffAt.isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField])
  exact congrArg (fun T : ES m →L[ℝ] ES m => T w) (h u v)

theorem fderiv_HessF_apply (hF : ContDiff ℝ 3 F) (a b : Fin m) (x v : ES m) :
    fderiv ℝ (fun y => HessF F y (stdBasis m a) (stdBasis m b)) x v
      = D3F F x v (stdBasis m a) (stdBasis m b) := by
  have hd : DifferentiableAt ℝ (HessF F) x :=
    (contDiff_HessF F hF).differentiable (by norm_num) x
  have hga_diff : DifferentiableAt ℝ (fun y => HessF F y (stdBasis m a)) x :=
    hd.clm_apply (differentiableAt_const _)
  have hcb : DifferentiableAt ℝ (fun _ : ES m => stdBasis m b) x := differentiableAt_const _
  have hga : fderiv ℝ (fun y => HessF F y (stdBasis m a)) x
      = (fderiv ℝ (HessF F) x).flip (stdBasis m a) := by
    have hca : DifferentiableAt ℝ (fun _ : ES m => stdBasis m a) x := differentiableAt_const _
    have hh := fderiv_clm_apply hd hca
    have hc0 : fderiv ℝ (fun _ : ES m => stdBasis m a) x = 0 := (hasFDerivAt_const _ _).fderiv
    rw [hc0, ContinuousLinearMap.comp_zero, zero_add] at hh
    exact hh
  have hh := fderiv_clm_apply hga_diff hcb
  have hcb0 : fderiv ℝ (fun _ : ES m => stdBasis m b) x = 0 := (hasFDerivAt_const _ _).fderiv
  rw [hcb0, ContinuousLinearMap.comp_zero, zero_add] at hh
  rw [hga] at hh
  rw [hh]
  simp only [ContinuousLinearMap.flip_apply]
  rfl

theorem sum_delta_mul_delta (a b : Fin m) :
    ∑ l : Fin m, (if a = l then (1:ℝ) else 0) * (if b = l then 1 else 0)
      = if a = b then 1 else 0 := by
  have hterm : ∀ l : Fin m, (if a = l then (1:ℝ) else 0) * (if b = l then 1 else 0)
      = if a = l then (if b = l then (1:ℝ) else 0) else 0 := by
    intro l; by_cases h : a = l <;> simp [h]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  rw [Finset.sum_ite_eq Finset.univ a (fun l => if b = l then (1:ℝ) else 0)]
  simp only [Finset.mem_univ, ite_true]
  by_cases hab : a = b
  · subst hab; simp
  · rw [ite_eq_right hab, ite_eq_right (fun h => hab h.symm)]

noncomputable def dc2 (l : Fin m) (x : ES m) : ℝ :=
  fderiv ℝ (confFactorSq hm F) x (stdBasis m l)

noncomputable def ddc2 (l q : Fin m) (x : ES m) : ℝ :=
  fderiv ℝ (dc2 hm F l) x (stdBasis m q)

theorem contDiff_dc2 (hF : ContDiff ℝ 3 F) (l : Fin m) : ContDiff ℝ 1 (dc2 hm F l) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ (confFactorSq hm F)) :=
    (contDiff_confFactorSq hm F hF).fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

theorem differentiable_dc2 (hF : ContDiff ℝ 3 F) (l : Fin m) : Differentiable ℝ (dc2 hm F l) :=
  (contDiff_dc2 hm F hF l).differentiable (by norm_num)

theorem christoffel' (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) (i j k : Fin m) :
    ⟪HessF F x (stdBasis m j) (stdBasis m i), pF F k x⟫_ℝ
      = (dc2 hm F i x * (if j = k then 1 else 0)
        + dc2 hm F j x * (if i = k then 1 else 0)
        - dc2 hm F k x * (if i = j then 1 else 0)) / 2 :=
  christoffel hm F hF hconf hU hx i j k

theorem inner_HessF_pF_deriv (hF : ContDiff ℝ 3 F) (a b c : Fin m) (x v : ES m) :
    fderiv ℝ (fun y => ⟪HessF F y (stdBasis m a) (stdBasis m b), pF F c y⟫_ℝ) x v
      = ⟪D3F F x v (stdBasis m a) (stdBasis m b), pF F c x⟫_ℝ
        + ⟪HessF F x (stdBasis m a) (stdBasis m b), HessF F x v (stdBasis m c)⟫_ℝ := by
  have h1 : DifferentiableAt ℝ (fun y => HessF F y (stdBasis m a) (stdBasis m b)) x :=
    (((contDiff_HessF F hF).differentiable_one x).clm_apply
      (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (pF F c) x := differentiable_pF F hF c x
  have hder := (h1.hasFDerivAt.inner ℝ h2.hasFDerivAt).fderiv
  rw [hder]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
  rw [fderiv_HessF_apply F hF a b x v, fderiv_pF_apply F hF c x v]
  rw [add_comm]

include hm in
theorem relA (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {i j k : Fin m}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⟪D3F F x (stdBasis m i) (stdBasis m j) (stdBasis m i), pF F k x⟫_ℝ
      + ⟪HessF F x (stdBasis m j) (stdBasis m i), HessF F x (stdBasis m i) (stdBasis m k)⟫_ℝ
      = 0 := by
  have hzero : (fun y => ⟪HessF F y (stdBasis m j) (stdBasis m i), pF F k y⟫_ℝ)
      =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hcc := christoffel' hm F hF hconf hU hy i j k
    rw [ite_eq_right hjk, ite_eq_right hik, ite_eq_right hij] at hcc
    rw [hcc]; ring
  have hfd0 : (fderiv ℝ (fun y => ⟪HessF F y (stdBasis m j) (stdBasis m i), pF F k y⟫_ℝ) x)
      (stdBasis m i) = 0 := by
    have h0 : fderiv ℝ (fun y => ⟪HessF F y (stdBasis m j) (stdBasis m i), pF F k y⟫_ℝ) x = 0 := by
      rw [hzero.fderiv_eq]; exact (hasFDerivAt_const _ _).fderiv
    rw [h0]; rfl
  have happ := inner_HessF_pF_deriv F hF j i k x (stdBasis m i)
  rw [hfd0] at happ
  exact happ.symm

theorem relB (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {i j k : Fin m} (hik : i ≠ k) :
    ⟪D3F F x (stdBasis m j) (stdBasis m i) (stdBasis m i), pF F k x⟫_ℝ
      + ⟪HessF F x (stdBasis m i) (stdBasis m i), HessF F x (stdBasis m j) (stdBasis m k)⟫_ℝ
      = -(ddc2 hm F k j x) / 2 := by
  have hEq : (fun y => ⟪HessF F y (stdBasis m i) (stdBasis m i), pF F k y⟫_ℝ)
      =ᶠ[𝓝 x] fun y => -(dc2 hm F k y) / 2 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hcc := christoffel' hm F hF hconf hU hy i i k
    rw [ite_eq_right hik, ite_eq_left rfl] at hcc
    rw [hcc]; ring
  have hfd : fderiv ℝ (fun y => ⟪HessF F y (stdBasis m i) (stdBasis m i), pF F k y⟫_ℝ) x
      = fderiv ℝ (fun y => -(dc2 hm F k y) / 2) x := hEq.fderiv_eq
  have hR : (fderiv ℝ (fun y => -(dc2 hm F k y) / 2) x) (stdBasis m j) = -(ddc2 hm F k j x) / 2 := by
    have hdd : DifferentiableAt ℝ (dc2 hm F k) x := differentiable_dc2 hm F hF k x
    have hder : fderiv ℝ (fun y => -(dc2 hm F k y) / 2) x = (-(1/2 : ℝ)) • fderiv ℝ (dc2 hm F k) x := by
      have : (fun y => -(dc2 hm F k y) / 2) = fun y => (-(1/2 : ℝ)) * dc2 hm F k y := by
        funext y; ring
      rw [this, fderiv_const_mul hdd _]
    rw [hder, smul_apply, smul_eq_mul]
    unfold ddc2
    ring
  have happ := inner_HessF_pF_deriv F hF i i k x (stdBasis m j)
  have hmain := congrFun (congrArg DFunLike.coe hfd) (stdBasis m j)
  rw [happ, hR] at hmain
  exact hmain

theorem inner_HessF_HessF (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) (a b c d : Fin m) :
    ⟪HessF F x (stdBasis m a) (stdBasis m b), HessF F x (stdBasis m c) (stdBasis m d)⟫_ℝ
      = (confFactorSq hm F x)⁻¹ *
        ∑ l : Fin m,
          (dc2 hm F b x * (if a = l then 1 else 0) + dc2 hm F a x * (if b = l then 1 else 0)
            - dc2 hm F l x * (if b = a then 1 else 0)) / 2
          * ((dc2 hm F d x * (if c = l then 1 else 0) + dc2 hm F c x * (if d = l then 1 else 0)
            - dc2 hm F l x * (if d = c then 1 else 0)) / 2) := by
  rw [frame_parseval hm F hconf hx]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [christoffel' hm F hF hconf hU hx b a l]
  rw [real_inner_comm (HessF F x (stdBasis m c) (stdBasis m d)) (pF F l x)]
  rw [christoffel' hm F hF hconf hU hx d c l]

theorem sum_mul_delta (f : Fin m → ℝ) (b : Fin m) :
    ∑ l : Fin m, f l * (if b = l then 1 else 0) = f b := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro l _ hlb; rw [ite_eq_right (hlb ∘ Eq.symm)]; simp
  · intro hb; exact (hb (Finset.mem_univ b)).elim

theorem sum_delta (a : Fin m) : ∑ l : Fin m, (if a = l then (1:ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro l _ hla; rw [ite_eq_right (Ne.symm hla)]
  · intro ha; exact (ha (Finset.mem_univ a)).elim

theorem inner_HH_relA (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {i j k : Fin m}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⟪HessF F x (stdBasis m j) (stdBasis m i), HessF F x (stdBasis m i) (stdBasis m k)⟫_ℝ
      = dc2 hm F j x * dc2 hm F k x / (4 * confFactorSq hm F x) := by
  have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
  have hc2 : confFactorSq hm F x ≠ 0 := by rw [confFactorSq]; exact pow_ne_zero 2 hcf
  rw [inner_HessF_HessF hm F hF hconf hU hx j i i k]
  have hCV1 : ∀ l : Fin m,
      (dc2 hm F i x * (if j = l then 1 else 0) + dc2 hm F j x * (if i = l then 1 else 0)
        - dc2 hm F l x * (if i = j then 1 else 0)) / 2
      = (dc2 hm F i x * (if j = l then 1 else 0) + dc2 hm F j x * (if i = l then 1 else 0)) / 2 := by
    intro l; rw [ite_eq_right hij]; ring
  have hCV2 : ∀ l : Fin m,
      (dc2 hm F k x * (if i = l then 1 else 0) + dc2 hm F i x * (if k = l then 1 else 0)
        - dc2 hm F l x * (if k = i then 1 else 0)) / 2
      = (dc2 hm F k x * (if i = l then 1 else 0) + dc2 hm F i x * (if k = l then 1 else 0)) / 2 := by
    intro l; rw [ite_eq_right (Ne.symm hik)]; ring
  have hsum : (∑ l : Fin m,
      (dc2 hm F i x * (if j = l then 1 else 0) + dc2 hm F j x * (if i = l then 1 else 0)
        - dc2 hm F l x * (if i = j then 1 else 0)) / 2
      * ((dc2 hm F k x * (if i = l then 1 else 0) + dc2 hm F i x * (if k = l then 1 else 0)
        - dc2 hm F l x * (if k = i then 1 else 0)) / 2))
      = dc2 hm F j x * dc2 hm F k x / 4 := by
    rw [Finset.sum_congr rfl (fun l _ => by rw [hCV1 l, hCV2 l])]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_left rfl, ite_eq_right (Ne.symm hik)]
      ring
    · intro l _ hli
      have hjl : (if j = l then (1:ℝ) else 0) * (if k = l then 1 else 0) = 0 := by
        by_cases hjl' : j = l
        · rw [ite_eq_left hjl']
          have hkl : ¬ (k = l) := fun h => hjk (hjl'.trans h.symm)
          rw [ite_eq_right hkl]; ring
        · rw [ite_eq_right hjl']; ring
      have e1 : (dc2 hm F i x * (if j = l then 1 else 0) + dc2 hm F j x * (if i = l then 1 else 0)) / 2
          = dc2 hm F i x * (if j = l then 1 else 0) / 2 := by rw [ite_eq_right (Ne.symm hli)]; ring
      have e2 : (dc2 hm F k x * (if i = l then 1 else 0) + dc2 hm F i x * (if k = l then 1 else 0)) / 2
          = dc2 hm F i x * (if k = l then 1 else 0) / 2 := by rw [ite_eq_right (Ne.symm hli)]; ring
      rw [e1, e2]
      have : dc2 hm F i x * (if j = l then 1 else 0) / 2 * (dc2 hm F i x * (if k = l then 1 else 0) / 2)
          = (dc2 hm F i x / 2)^2 * ((if j = l then 1 else 0) * (if k = l then 1 else 0)) := by ring
      rw [this, hjl]; ring
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [hsum]
  field_simp

theorem sum_const_mul_delta_delta (C : ℝ) (a b : Fin m) :
    ∑ l : Fin m, C * ((if a = l then (1:ℝ) else 0) * (if b = l then 1 else 0))
      = C * (if a = b then 1 else 0) := by
  rw [← Finset.mul_sum, sum_delta_mul_delta]

theorem sum_const_mul_mul_delta (C : ℝ) (f : Fin m → ℝ) (b : Fin m) :
    ∑ l : Fin m, C * (f l * (if b = l then (1:ℝ) else 0)) = C * f b := by
  rw [← Finset.mul_sum, sum_mul_delta]

theorem inner_HH_relB (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⟪HessF F x (stdBasis m i) (stdBasis m i), HessF F x (stdBasis m j) (stdBasis m k)⟫_ℝ
      = -(dc2 hm F j x * dc2 hm F k x) / (2 * confFactorSq hm F x) := by
  have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
  have hc2 : confFactorSq hm F x ≠ 0 := by rw [confFactorSq]; exact pow_ne_zero 2 hcf
  rw [inner_HessF_HessF hm F hF hconf hU hx i i j k]
  have hpt : ∀ l : Fin m,
      ((dc2 hm F i x * (if i = l then 1 else 0) + dc2 hm F i x * (if i = l then 1 else 0)
          - dc2 hm F l x * (if i = i then 1 else 0)) / 2)
      * ((dc2 hm F k x * (if j = l then 1 else 0) + dc2 hm F j x * (if k = l then 1 else 0)
          - dc2 hm F l x * (if k = j then 1 else 0)) / 2)
      = (dc2 hm F i x * dc2 hm F k x / 2) * ((if i = l then 1 else 0) * (if j = l then 1 else 0))
        + (dc2 hm F i x * dc2 hm F j x / 2) * ((if i = l then 1 else 0) * (if k = l then 1 else 0))
        + (-(dc2 hm F k x) / 4) * (dc2 hm F l x * (if j = l then 1 else 0))
        + (-(dc2 hm F j x) / 4) * (dc2 hm F l x * (if k = l then 1 else 0)) := by
    intro l
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hjk)]
    ring
  have hsum : (∑ l : Fin m,
      ((dc2 hm F i x * (if i = l then 1 else 0) + dc2 hm F i x * (if i = l then 1 else 0)
          - dc2 hm F l x * (if i = i then 1 else 0)) / 2)
      * ((dc2 hm F k x * (if j = l then 1 else 0) + dc2 hm F j x * (if k = l then 1 else 0)
          - dc2 hm F l x * (if k = j then 1 else 0)) / 2))
      = -(dc2 hm F j x * dc2 hm F k x) / 2 := by
    rw [Finset.sum_congr rfl (fun l _ => hpt l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_const_mul_delta_delta, sum_const_mul_delta_delta,
      sum_const_mul_mul_delta, sum_const_mul_mul_delta]
    rw [ite_eq_right hij, ite_eq_right hik]
    ring
  rw [hsum]
  field_simp

theorem exists_third (hm : 3 ≤ m) (j k : Fin m) : ∃ i : Fin m, i ≠ j ∧ i ≠ k := by
  have h2 : ({j, k} : Finset (Fin m)).card ≤ 2 := by
    by_cases h : j = k
    · subst h; simp
    · rw [Finset.card_pair h]
  have hne : ({j, k} : Finset (Fin m)) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact ⟨i, hi.1, hi.2⟩

theorem offdiag_liouville (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {j k : Fin m} (hjk : j ≠ k) :
    2 * confFactorSq hm F x * ddc2 hm F k j x
      = 3 * dc2 hm F j x * dc2 hm F k x := by
  obtain ⟨i, hij, hik⟩ := exists_third hm j k
  have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
  have hc2 : confFactorSq hm F x ≠ 0 := by rw [confFactorSq]; exact pow_ne_zero 2 hcf
  have hA := relA hm F hF hconf hU hx hij hjk hik
  have hB := relB (i := i) (j := j) (k := k) hm F hF hconf hU hx hik
  have hPA := inner_HH_relA hm F hF hconf hU hx hij hjk hik
  have hPB := inner_HH_relB hm F hF hconf hU hx hij hik hjk
  have hsymm : D3F F x (stdBasis m i) (stdBasis m j) (stdBasis m i)
      = D3F F x (stdBasis m j) (stdBasis m i) (stdBasis m i) :=
    D3F_symm12 F hF x (stdBasis m i) (stdBasis m j) (stdBasis m i)
  have hsymm2 : ⟪D3F F x (stdBasis m i) (stdBasis m j) (stdBasis m i), pF F k x⟫_ℝ
      = ⟪D3F F x (stdBasis m j) (stdBasis m i) (stdBasis m i), pF F k x⟫_ℝ :=
    congrArg (fun w => ⟪w, pF F k x⟫_ℝ) hsymm
  rw [hPA] at hA
  rw [hPB] at hB
  rw [hsymm2] at hA
  field_simp at hA hB ⊢
  linarith

theorem confFactorSq_pos (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : 0 < confFactorSq hm F x := by
  rw [confFactorSq]
  exact pow_pos (confFactor_pos hm F hconf hx) 2

theorem confFactorSq_ne_zero (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {x : ES m} (hx : x ∈ U) : confFactorSq hm F x ≠ 0 :=
  (confFactorSq_pos hm F hconf hx).ne'

theorem hasFDerivAt_confFactorSq (hF : ContDiff ℝ 3 F) (x : ES m) :
    HasFDerivAt (confFactorSq hm F) (fderiv ℝ (confFactorSq hm F) x) x :=
  (differentiable_confFactorSq hm F hF x).hasFDerivAt

noncomputable def recipConfFactor (hm : 3 ≤ m) (F : ES m → ES m) (x : ES m) : ℝ :=
  (confFactorSq hm F x) ^ (-(1/2 : ℝ))

theorem hasFDerivAt_recipConfFactor (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {y : ES m} (hy : y ∈ U) :
    HasFDerivAt (recipConfFactor hm F)
      ((-(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ))) •
        fderiv ℝ (confFactorSq hm F) y) y := by
  have h := (hasFDerivAt_confFactorSq hm F hF y).rpow_const
    (Or.inl (confFactorSq_ne_zero hm F hconf hy) : confFactorSq hm F y ≠ 0 ∨ 1 ≤ (-(1/2 : ℝ)))
  have hexp : (-(1/2 : ℝ)) - 1 = -(3/2 : ℝ) := by norm_num
  rw [hexp] at h
  exact h

theorem dRecip_eq (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    {y : ES m} (hy : y ∈ U) (a : Fin m) :
    fderiv ℝ (recipConfFactor hm F) y (stdBasis m a)
      = -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ)) * dc2 hm F a y := by
  rw [(hasFDerivAt_recipConfFactor hm F hF hconf hy).fderiv]
  rw [smul_apply, smul_eq_mul]
  rw [dc2]

theorem dRecip_eventually (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) (a : Fin m) :
    (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m a))
      =ᶠ[𝓝 x] fun y => -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ)) * dc2 hm F a y := by
  filter_upwards [hU.mem_nhds hx] with y hy using dRecip_eq hm F hF hconf hy a

theorem recipConfFactor_offdiag (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {j k : Fin m} (hjk : j ≠ k) :
    fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m k)) x (stdBasis m j) = 0 := by
  have hs : 0 < confFactorSq hm F x := confFactorSq_pos hm F hconf hx
  have hne : confFactorSq hm F x ≠ 0 := hs.ne'
  rw [(dRecip_eventually hm F hF hconf hU hx k).fderiv_eq]
  have hpow : HasFDerivAt (fun y => (confFactorSq hm F y) ^ (-(3/2 : ℝ)))
      ((-(3/2 : ℝ) * (confFactorSq hm F x) ^ (-(5/2 : ℝ))) • fderiv ℝ (confFactorSq hm F) x) x := by
    have h := (hasFDerivAt_confFactorSq hm F hF x).rpow_const (Or.inl hne : confFactorSq hm F x ≠ 0 ∨ 1 ≤ (-(3/2 : ℝ)))
    have hexp : (-(3/2 : ℝ)) - 1 = (-(5/2 : ℝ)) := by norm_num
    rw [hexp] at h
    exact h
  have hA : HasFDerivAt (fun y => -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ)))
      ((-(1/2 : ℝ)) • ((-(3/2 : ℝ) * (confFactorSq hm F x) ^ (-(5/2 : ℝ))) •
        fderiv ℝ (confFactorSq hm F) x)) x :=
    hpow.const_mul (-(1/2 : ℝ))
  have hB : HasFDerivAt (dc2 hm F k) (fderiv ℝ (dc2 hm F k) x) x :=
    (differentiable_dc2 hm F hF k x).hasFDerivAt
  have hAB := hA.mul hB
  change (fderiv ℝ ((fun y => -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ))) * dc2 hm F k) x)
      (stdBasis m j) = 0
  rw [hAB.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have h1 : fderiv ℝ (dc2 hm F k) x (stdBasis m j) = ddc2 hm F k j x := rfl
  have h2 : fderiv ℝ (confFactorSq hm F) x (stdBasis m j) = dc2 hm F j x := rfl
  rw [h1, h2]
  have hpow_id : (confFactorSq hm F x) ^ (-(3/2 : ℝ))
      = (confFactorSq hm F x) ^ (-(5/2 : ℝ)) * confFactorSq hm F x := by
    have he : (-(3/2 : ℝ)) = (-(5/2 : ℝ)) + 1 := by norm_num
    rw [he, Real.rpow_add hs, Real.rpow_one]
  rw [hpow_id]
  have hoff := offdiag_liouville hm F hF hconf hU hx hjk
  linear_combination (-((confFactorSq hm F x) ^ (-(5/2 : ℝ))) / 4) * hoff

theorem sum_const_delta (C : ℝ) (a : Fin m) :
    ∑ l : Fin m, C * (if a = l then (1:ℝ) else 0) = C := by
  rw [← Finset.mul_sum, sum_delta, mul_one]

theorem inner_HH_relC (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {a b : Fin m}
    (hab : a ≠ b) :
    ⟪HessF F x (stdBasis m b) (stdBasis m b), HessF F x (stdBasis m a) (stdBasis m a)⟫_ℝ
      = (∑ l : Fin m, (dc2 hm F l x)^2 - 2*(dc2 hm F a x)^2 - 2*(dc2 hm F b x)^2)
        / (4 * confFactorSq hm F x) := by
  have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
  have hc2 : confFactorSq hm F x ≠ 0 := by rw [confFactorSq]; exact pow_ne_zero 2 hcf
  rw [inner_HessF_HessF hm F hF hconf hU hx b b a a]
  have hpt : ∀ l : Fin m,
      ((dc2 hm F b x * (if b = l then 1 else 0) + dc2 hm F b x * (if b = l then 1 else 0)
          - dc2 hm F l x * (if b = b then 1 else 0)) / 2)
      * ((dc2 hm F a x * (if a = l then 1 else 0) + dc2 hm F a x * (if a = l then 1 else 0)
          - dc2 hm F l x * (if a = a then 1 else 0)) / 2)
      = (dc2 hm F a x * dc2 hm F b x) * ((if b = l then 1 else 0) * (if a = l then 1 else 0))
        + (-(dc2 hm F b x)/2) * (dc2 hm F l x * (if b = l then 1 else 0))
        + (-(dc2 hm F a x)/2) * (dc2 hm F l x * (if a = l then 1 else 0))
        + (1/4) * (dc2 hm F l x * dc2 hm F l x) := by
    intro l
    rw [ite_eq_left rfl, ite_eq_left rfl]
    ring
  have hsum4 : (∑ l : Fin m, (1/4:ℝ) * (dc2 hm F l x * dc2 hm F l x))
      = (1/4) * ∑ l : Fin m, (dc2 hm F l x)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hsum : (∑ l : Fin m,
      ((dc2 hm F b x * (if b = l then 1 else 0) + dc2 hm F b x * (if b = l then 1 else 0)
          - dc2 hm F l x * (if b = b then 1 else 0)) / 2)
      * ((dc2 hm F a x * (if a = l then 1 else 0) + dc2 hm F a x * (if a = l then 1 else 0)
          - dc2 hm F l x * (if a = a then 1 else 0)) / 2))
      = (1/4) * ∑ l : Fin m, (dc2 hm F l x)^2
        - (dc2 hm F b x)^2/2 - (dc2 hm F a x)^2/2 := by
    rw [Finset.sum_congr rfl (fun l _ => hpt l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_const_mul_delta_delta, sum_const_mul_mul_delta, sum_const_mul_mul_delta, hsum4]
    rw [ite_eq_right hab.symm]
    ring
  rw [hsum]
  field_simp
  ring

theorem inner_HH_relD (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {a b : Fin m}
    (hab : a ≠ b) :
    ⟪HessF F x (stdBasis m a) (stdBasis m b), HessF F x (stdBasis m b) (stdBasis m a)⟫_ℝ
      = ((dc2 hm F a x)^2 + (dc2 hm F b x)^2) / (4 * confFactorSq hm F x) := by
  have hcf : confFactor hm F x ≠ 0 := confFactor_ne_zero hm F hconf hx
  have hc2 : confFactorSq hm F x ≠ 0 := by rw [confFactorSq]; exact pow_ne_zero 2 hcf
  rw [inner_HessF_HessF hm F hF hconf hU hx a b b a]
  have hpt : ∀ l : Fin m,
      ((dc2 hm F b x * (if a = l then 1 else 0) + dc2 hm F a x * (if b = l then 1 else 0)
          - dc2 hm F l x * (if b = a then 1 else 0)) / 2)
      * ((dc2 hm F a x * (if b = l then 1 else 0) + dc2 hm F b x * (if a = l then 1 else 0)
          - dc2 hm F l x * (if a = b then 1 else 0)) / 2)
      = ((dc2 hm F b x)^2/4) * (if a = l then 1 else 0)
        + ((dc2 hm F a x)^2/4) * (if b = l then 1 else 0)
        + ((dc2 hm F a x * dc2 hm F b x)/2)
          * ((if a = l then 1 else 0) * (if b = l then 1 else 0)) := by
    intro l
    rw [ite_eq_right hab.symm, ite_eq_right hab]
    by_cases hal : a = l
    · have hbl : b ≠ l := fun h => hab (hal.trans h.symm)
      rw [ite_eq_left hal, ite_eq_right hbl]; ring
    · rw [ite_eq_right hal]
      by_cases hbl : b = l
      · rw [ite_eq_left hbl]; ring
      · rw [ite_eq_right hbl]; ring
  have hsum : (∑ l : Fin m,
      ((dc2 hm F b x * (if a = l then 1 else 0) + dc2 hm F a x * (if b = l then 1 else 0)
          - dc2 hm F l x * (if b = a then 1 else 0)) / 2)
      * ((dc2 hm F a x * (if b = l then 1 else 0) + dc2 hm F b x * (if a = l then 1 else 0)
          - dc2 hm F l x * (if a = b then 1 else 0)) / 2))
      = (dc2 hm F b x)^2/4 + (dc2 hm F a x)^2/4 := by
    rw [Finset.sum_congr rfl (fun l _ => hpt l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_const_delta, sum_const_delta, sum_const_mul_delta_delta]
    rw [ite_eq_right hab]
    ring
  rw [hsum]
  field_simp
  ring

theorem relD (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {a b : Fin m} (hab : a ≠ b) :
    ⟪D3F F x (stdBasis m b) (stdBasis m a) (stdBasis m b), pF F a x⟫_ℝ
      + ⟪HessF F x (stdBasis m a) (stdBasis m b), HessF F x (stdBasis m b) (stdBasis m a)⟫_ℝ
      = (ddc2 hm F b b x) / 2 := by
  have hEq : (fun y => ⟪HessF F y (stdBasis m a) (stdBasis m b), pF F a y⟫_ℝ)
      =ᶠ[𝓝 x] fun y => (dc2 hm F b y) / 2 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hcc := christoffel' hm F hF hconf hU hy b a a
    rw [ite_eq_left rfl, ite_eq_right hab.symm] at hcc
    rw [hcc]; ring
  have hfd : fderiv ℝ (fun y => ⟪HessF F y (stdBasis m a) (stdBasis m b), pF F a y⟫_ℝ) x
      = fderiv ℝ (fun y => (dc2 hm F b y) / 2) x := hEq.fderiv_eq
  have hR : (fderiv ℝ (fun y => (dc2 hm F b y) / 2) x) (stdBasis m b) = (ddc2 hm F b b x) / 2 := by
    have hdd : DifferentiableAt ℝ (dc2 hm F b) x := differentiable_dc2 hm F hF b x
    have hder : fderiv ℝ (fun y => (dc2 hm F b y) / 2) x = ((1/2 : ℝ)) • fderiv ℝ (dc2 hm F b) x := by
      have : (fun y => (dc2 hm F b y) / 2) = fun y => (1/2 : ℝ) * dc2 hm F b y := by
        funext y; ring
      rw [this, fderiv_const_mul hdd _]
    rw [hder, smul_apply, smul_eq_mul]
    unfold ddc2
    ring
  have happ := inner_HessF_pF_deriv F hF a b a x (stdBasis m b)
  have hmain := congrFun (congrArg DFunLike.coe hfd) (stdBasis m b)
  rw [happ, hR] at hmain
  exact hmain

theorem pairdiag (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {a b : Fin m} (hab : a ≠ b) :
    2 * confFactorSq hm F x * (ddc2 hm F a a x + ddc2 hm F b b x)
      = 3 * ((dc2 hm F a x)^2 + (dc2 hm F b x)^2) - ∑ l : Fin m, (dc2 hm F l x)^2 := by
  have hc2 : confFactorSq hm F x ≠ 0 := confFactorSq_ne_zero hm F hconf hx
  have hsymm : ⟪D3F F x (stdBasis m a) (stdBasis m b) (stdBasis m b), pF F a x⟫_ℝ
      = ⟪D3F F x (stdBasis m b) (stdBasis m a) (stdBasis m b), pF F a x⟫_ℝ :=
    congrArg (fun w => ⟪w, pF F a x⟫_ℝ)
      (D3F_symm12 F hF x (stdBasis m a) (stdBasis m b) (stdBasis m b))
  have hrelC := relB hm F hF hconf hU hx (i := b) (j := a) (k := a) hab.symm
  have hrelD := relD hm F hF hconf hU hx hab
  have hPA := inner_HH_relC hm F hF hconf hU hx hab
  have hPB := inner_HH_relD hm F hF hconf hU hx hab
  rw [hPA] at hrelC
  rw [hPB] at hrelD
  rw [hsymm] at hrelC
  field_simp at hrelC hrelD ⊢
  nlinarith [hrelC, hrelD]

theorem diag_liouville (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) {j k : Fin m} :
    2 * confFactorSq hm F x * ddc2 hm F j j x - 3 * (dc2 hm F j x)^2
      = 2 * confFactorSq hm F x * ddc2 hm F k k x - 3 * (dc2 hm F k x)^2 := by
  obtain ⟨i, hij, hik⟩ := exists_third hm j k
  have h1 := pairdiag hm F hF hconf hU hx hij
  have h2 := pairdiag hm F hF hconf hU hx hik
  linear_combination h1 - h2

theorem ddRecip_eq (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) (a b : Fin m) :
    fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m a)) x (stdBasis m b)
      = -(1/2 : ℝ) * (confFactorSq hm F x) ^ (-(3/2 : ℝ)) * ddc2 hm F a b x
        + (3/4 : ℝ) * (confFactorSq hm F x) ^ (-(5/2 : ℝ)) * dc2 hm F a x * dc2 hm F b x := by
  have hs : 0 < confFactorSq hm F x := confFactorSq_pos hm F hconf hx
  have hne : confFactorSq hm F x ≠ 0 := hs.ne'
  rw [(dRecip_eventually hm F hF hconf hU hx a).fderiv_eq]
  have hpow : HasFDerivAt (fun y => (confFactorSq hm F y) ^ (-(3/2 : ℝ)))
      ((-(3/2 : ℝ) * (confFactorSq hm F x) ^ (-(5/2 : ℝ))) • fderiv ℝ (confFactorSq hm F) x) x := by
    have h := (hasFDerivAt_confFactorSq hm F hF x).rpow_const
      (Or.inl hne : confFactorSq hm F x ≠ 0 ∨ 1 ≤ (-(3/2 : ℝ)))
    have hexp : (-(3/2 : ℝ)) - 1 = (-(5/2 : ℝ)) := by norm_num
    rw [hexp] at h
    exact h
  have hA : HasFDerivAt (fun y => -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ)))
      ((-(1/2 : ℝ)) • ((-(3/2 : ℝ) * (confFactorSq hm F x) ^ (-(5/2 : ℝ))) •
        fderiv ℝ (confFactorSq hm F) x)) x :=
    hpow.const_mul (-(1/2 : ℝ))
  have hB : HasFDerivAt (dc2 hm F a) (fderiv ℝ (dc2 hm F a) x) x :=
    (differentiable_dc2 hm F hF a x).hasFDerivAt
  have hAB := hA.mul hB
  change (fderiv ℝ ((fun y => -(1/2 : ℝ) * (confFactorSq hm F y) ^ (-(3/2 : ℝ))) * dc2 hm F a) x)
      (stdBasis m b) = _
  rw [hAB.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have h1 : fderiv ℝ (dc2 hm F a) x (stdBasis m b) = ddc2 hm F a b x := rfl
  have h2 : fderiv ℝ (confFactorSq hm F) x (stdBasis m b) = dc2 hm F b x := rfl
  rw [h1, h2]
  ring

theorem recipConfFactor_diag (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hU : IsOpen U) {x : ES m} (hx : x ∈ U) (a b : Fin m) :
    fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m a)) x (stdBasis m a)
      = fderiv ℝ (fun y => fderiv ℝ (recipConfFactor hm F) y (stdBasis m b)) x (stdBasis m b) := by
  have hs : 0 < confFactorSq hm F x := confFactorSq_pos hm F hconf hx
  rw [ddRecip_eq hm F hF hconf hU hx a a, ddRecip_eq hm F hF hconf hU hx b b]
  have hpow_id : (confFactorSq hm F x) ^ (-(3/2 : ℝ))
      = (confFactorSq hm F x) ^ (-(5/2 : ℝ)) * confFactorSq hm F x := by
    have he : (-(3/2 : ℝ)) = (-(5/2 : ℝ)) + 1 := by norm_num
    rw [he, Real.rpow_add hs, Real.rpow_one]
  rw [hpow_id]
  have hd := diag_liouville hm F hF hconf hU hx (j := a) (k := b)
  linear_combination (-((confFactorSq hm F x) ^ (-(5/2 : ℝ))) / 4) * hd

end DifferentialGeometry.LiouvilleRigidity
