import DifferentialGeometry.Analysis.ODE.QuadraticLevelScaling
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set
open scoped ContDiff Manifold
open DifferentialGeometry.Analysis.ODE

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def quadraticFiberVectorField (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ))
    (c : ℝ) (p : ℝ × E) : E :=
  (fderiv ℝ (A : E × ℝ → E × ℝ) (A.symm (p.2, p.1))
    (quadraticLevelVectorField c (p.1, (A.symm (p.2, p.1)).1), 1)).1

theorem contDiffOn_quadraticFiberVectorField (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (c : ℝ) :
    ContDiffOn ℝ ∞ (quadraticFiberVectorField A c) {p | p.1 ≠ c} := by
  have hA : ContDiff ℝ ∞ (A : E × ℝ → E × ℝ) := A.contMDiff.contDiff
  have hAi : ContDiff ℝ ∞ (fun p : ℝ × E => A.symm (p.2, p.1)) :=
    A.symm.contMDiff.contDiff.comp (contDiff_snd.prodMk contDiff_fst)
  have hD := (hA.fderiv_right (by simp)).comp hAi
  have hW : ContDiffOn ℝ ∞
      (fun p : ℝ × E => quadraticLevelVectorField c (p.1, (A.symm (p.2, p.1)).1))
      {p | p.1 ≠ c} :=
    (contDiffOn_quadraticLevelVectorField c).comp
      (contDiff_fst.prodMk hAi.fst).contDiffOn (fun _ hp => hp)
  exact (hD.contDiffOn.clm_apply (hW.prodMk contDiffOn_const)).fst

theorem hasDerivAt_fst_comp_quadraticLevelScaling
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ p, (A p).2 = p.2)
    (a c : ℝ) (x : E) {t : ℝ} (ht : 0 < (t - c) / (a - c)) :
    HasDerivAt (fun s => (A (quadraticLevelScaling a c x s, s)).1)
      (quadraticFiberVectorField A c (t, (A (quadraticLevelScaling a c x t, t)).1)) t := by
  have hd := ((A.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_quadraticLevelScaling a c x ht).prodMk (hasDerivAt_id t)))
  have hdfst := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have hp : ((A (quadraticLevelScaling a c x t, t)).1, t) =
      A (quadraticLevelScaling a c x t, t) :=
        Prod.ext rfl (hA (quadraticLevelScaling a c x t, t)).symm
  unfold quadraticFiberVectorField
  rw [hp, A.symm_apply_apply]
  convert! hdfst using 1

theorem continuous_fst_comp_quadraticLevelScaling
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (a c : ℝ) :
    Continuous (fun p : ℝ × E => (A (quadraticLevelScaling a c p.2 p.1, p.1)).1) :=
  (A.contMDiff.continuous.comp
    ((continuous_quadraticLevelScaling a c).prodMk continuous_fst)).fst

theorem contDiffOn_fst_comp_quadraticLevelScaling
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (a c : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (A (quadraticLevelScaling a c p.2 p.1, p.1)).1)
      {p | 0 < (p.1 - c) / (a - c)} :=
  (A.contMDiff.contDiff.comp_contDiffOn
    ((contDiffOn_quadraticLevelScaling a c).prodMk contDiff_fst.contDiffOn)).fst

open Filter in
open scoped Topology in
theorem hasDerivAt_fst_comp_of_quadratic_transport
    {M : Type*}
    (χ : E → M) {U : Set E} (hU : IsOpen U) (e : M → E × ℝ)
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ z, (A z).2 = z.2)
    {c α u : ℝ} (huc : u ≠ c)
    (hnormal : ∀ y ∈ U, e (χ y) = A (y, c + α / 2 * ‖y‖ ^ 2))
    {x : E} (hx : c + α / 2 * ‖x‖ ^ 2 = u) {γ : ℝ → M}
    {S : Set ℝ} (hS : IsOpen S)
    (hradial : ∀ s ∈ S, γ s = χ (quadraticRadialCurve (-α⁻¹) x (u - s)))
    {t : ℝ} (ht : t ∈ S) (hpos : 0 < (t - c) / (u - c))
    (hsource : quadraticLevelScaling u c x t ∈ U) :
    HasDerivAt (fun s => (e (γ s)).1)
      (A.quadraticFiberVectorField c (t, (e (γ t)).1)) t := by
  have hsmooth := A.hasDerivAt_fst_comp_quadraticLevelScaling hA u c x hpos
  have hcont : Continuous (quadraticLevelScaling u c x) :=
    (continuous_quadraticLevelScaling u c).comp (continuous_id.prodMk continuous_const)
  have hposopen : IsOpen {s : ℝ | 0 < (s - c) / (u - c)} :=
    isOpen_lt continuous_const ((continuous_id.sub continuous_const).div_const _)
  have heq : (fun s => (e (γ s)).1) =ᶠ[𝓝 t]
      (fun s => (A (quadraticLevelScaling u c x s, s)).1) := by
    filter_upwards [hS.mem_nhds ht, hcont.continuousAt (hU.mem_nhds hsource),
      hposopen.mem_nhds hpos] with s hs hsU hspos
    rw [hradial s hs, quadraticRadialCurve_eq_quadraticLevelScaling huc hx,
      hnormal _ hsU, quadraticLevelScaling_height huc hx hspos.le]
  have heqt : (e (γ t)).1 = (A (quadraticLevelScaling u c x t, t)).1 := heq.self_of_nhds
  rw [heqt]
  exact hsmooth.congr_of_eventuallyEq heq

end Diffeomorph
