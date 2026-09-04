import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Topology

variable {E' P Q : Type*}
  [NormedAddCommGroup E'] [NormedSpace Real E']
  [NormedAddCommGroup P] [NormedSpace Real P]
  [NormedAddCommGroup Q] [NormedSpace Real Q]

theorem fderiv_pair_sub_id_le
    {Φ : P × Q → E'} {u : E' → P} {v w : E' → Q} {x : E'}
    {DΦv DΦw : P × Q →L[Real] E'} {Du : E' →L[Real] P}
    {Dv Dw : E' →L[Real] Q} {LΦ BΦ Bu Bv δ' : Real}
    (hΦv : HasFDerivAt Φ DΦv (u x, v x))
    (hΦw : HasFDerivAt Φ DΦw (u x, w x))
    (hu : HasFDerivAt u Du x) (hv : HasFDerivAt v Dv x)
    (hw : HasFDerivAt w Dw x)
    (hdiag : (fun y => Φ (u y, w y)) =ᶠ[nhds x] fun y => y)
    (hLip : ‖DΦv - DΦw‖ ≤ LΦ) (hBΦ : ‖DΦw‖ ≤ BΦ)
    (hBu : ‖Du‖ ≤ Bu) (hBv : ‖Dv‖ ≤ Bv) (hδ' : ‖Dv - Dw‖ ≤ δ') :
    ‖fderiv Real (fun y => Φ (u y, v y)) x - ContinuousLinearMap.id Real E'‖
      ≤ LΦ * max Bu Bv + BΦ * δ' := by
  have hG : HasFDerivAt (fun y => Φ (u y, v y)) (DΦv.comp (Du.prod Dv)) x :=
    hΦv.comp x (hu.prodMk hv)
  have hW : HasFDerivAt (fun y => Φ (u y, w y)) (DΦw.comp (Du.prod Dw)) x :=
    hΦw.comp x (hu.prodMk hw)
  have hkey : DΦw.comp (Du.prod Dw) = ContinuousLinearMap.id Real E' := by
    have h1 : fderiv Real (fun y => Φ (u y, w y)) x =
        fderiv Real (fun y : E' => y) x :=
      Filter.EventuallyEq.fderiv_eq hdiag
    rw [hW.fderiv] at h1
    rw [h1, fderiv_fun_id]
  have hsplit : DΦv.comp (Du.prod Dv) - ContinuousLinearMap.id Real E'
      = (DΦv - DΦw).comp (Du.prod Dv)
        + DΦw.comp ((0 : E' →L[Real] P).prod (Dv - Dw)) := by
    rw [← hkey]
    ext ξ
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, add_apply, zero_apply]
    have hpt : (((0 : P), Dv ξ - Dw ξ) : P × Q) =
        (Du ξ, Dv ξ) - (Du ξ, Dw ξ) := by
      simp [Prod.mk_sub_mk]
    rw [hpt, map_sub]
    abel
  rw [hG.fderiv, hsplit]
  have hLΦ0 : 0 ≤ LΦ := le_trans (norm_nonneg _) hLip
  have hBΦ0 : 0 ≤ BΦ := le_trans (norm_nonneg _) hBΦ
  have h1 : ‖(DΦv - DΦw).comp (Du.prod Dv)‖ ≤ LΦ * max Bu Bv := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
      (mul_le_mul hLip ?_ (norm_nonneg _) hLΦ0)
    rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
    exact max_le_max hBu hBv
  have h2 : ‖DΦw.comp ((0 : E' →L[Real] P).prod (Dv - Dw))‖ ≤ BΦ * δ' := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
      (mul_le_mul hBΦ ?_ (norm_nonneg _) hBΦ0)
    rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
    simp only [norm_zero]
    rw [max_eq_right (norm_nonneg _)]
    exact hδ'
  exact le_trans (norm_add_le _ _) (by linarith)

omit [NormedAddCommGroup P] [NormedSpace Real P] in
theorem norm_pair_sub_self_le
    {Φ : P × Q → E'} {u : E' → P} {v w : E' → Q} {x : E'} {B : Real}
    (hdiag : Φ (u x, w x) = x)
    (hdiff : ∀ q ∈ segment Real (w x) (v x),
      DifferentiableAt Real (fun q' => Φ (u x, q')) q)
    (hbd : ∀ q ∈ segment Real (w x) (v x),
      ‖fderiv Real (fun q' => Φ (u x, q')) q‖ ≤ B) :
    ‖Φ (u x, v x) - x‖ ≤ B * ‖v x - w x‖ := by
  have hseg : Convex Real (segment Real (w x) (v x)) := convex_segment _ _
  have hmvt : ‖Φ (u x, v x) - Φ (u x, w x)‖ ≤ B * ‖v x - w x‖ :=
    hseg.norm_image_sub_le_of_norm_fderiv_le hdiff hbd
      (left_mem_segment Real (w x) (v x)) (right_mem_segment Real (w x) (v x))
  rwa [hdiag] at hmvt

omit [NormedAddCommGroup P] [NormedSpace Real P]
  [NormedAddCommGroup Q] [NormedSpace Real Q] in
theorem neumannOfDerivNorm {G : E' → E'} {x : E'} {ε : Real}
    (hG : DifferentiableAt Real G x)
    (h : mapDerivNorm 1 G (fun y => y) x ≤ ε) :
    ‖ContinuousLinearMap.id Real E' - fderiv Real G x‖ ≤ ε := by
  simp only [mapDerivNorm] at h
  rw [norm_iteratedFDeriv_one] at h
  have hsub : fderiv Real (fun y => G y - y) x =
      fderiv Real G x - ContinuousLinearMap.id Real E' := by
    have h1 : HasFDerivAt (fun y => G y - y)
        (fderiv Real G x - ContinuousLinearMap.id Real E') x :=
      hG.hasFDerivAt.sub (hasFDerivAt_id x)
    exact h1.fderiv
  rw [hsub, norm_sub_rev] at h
  exact h

end HCGCompactness
end DifferentialGeometry
