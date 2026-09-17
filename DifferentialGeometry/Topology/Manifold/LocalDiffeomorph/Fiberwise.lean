import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Mathlib.Analysis.Calculus.FDeriv.Prod

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem isLocalDiffeomorphAt_prod_of_injective_fderiv
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : P × E → E} {U : Set (P × E)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {z : P × E} (hz : z ∈ U)
    (hinj : Function.Injective (fderiv ℝ (fun y => F (z.1, y)) z.2)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) ∞ (fun q => (q.1, F q)) z := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hFd : HasFDerivAt F (fderiv ℝ F z) z :=
    ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  let A := (ContinuousLinearMap.fst ℝ P E).prod (fderiv ℝ F z)
  have hA : HasFDerivAt (fun q => (q.1, F q)) A z := (hasFDerivAt_fst (p := z)).prodMk hFd
  have hs : HasFDerivAt (fun y => F (z.1, y))
      ((fderiv ℝ F z).comp (ContinuousLinearMap.inr ℝ P E)) z.2 := by
    convert! hFd.comp (f := fun y : E => (z.1, y)) z.2
      ((hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2)) using 1
  have hAi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have hv₁ : v.1 = 0 := congrArg Prod.fst hv
    have hv₂ : fderiv ℝ F z v = 0 := congrArg Prod.snd hv
    have hslice : fderiv ℝ (fun y => F (z.1, y)) z.2 v.2 = 0 := by
      rw [hs.fderiv]
      change fderiv ℝ F z (0, v.2) = 0
      simpa only [← hv₁] using hv₂
    have hv₂zero : v.2 = 0 := hinj (hslice.trans (map_zero _).symm)
    exact Prod.ext hv₁ hv₂zero
  have hAs : Function.Surjective A := by
    intro q
    have hsE : Function.Surjective (fderiv ℝ (fun y => F (z.1, y)) z.2) :=
      LinearMap.injective_iff_surjective.mp hinj
    obtain ⟨v, hv⟩ := hsE (q.2 - fderiv ℝ F z (q.1, 0))
    rw [hs.fderiv] at hv
    change fderiv ℝ F z (0, v) = q.2 - fderiv ℝ F z (q.1, 0) at hv
    refine ⟨(q.1, v), Prod.ext rfl ?_⟩
    change fderiv ℝ F z (q.1, v) = q.2
    rw [show (q.1, v) = (q.1, 0) + (0, v) from by simp, map_add, hv]
    exact add_sub_cancel _ _
  let L : (P × E) ≃L[ℝ] (P × E) := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hAi)
    (LinearMap.range_eq_top.mpr hAs)
  exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    (fun q => (q.1, F q)) (contDiff_fst.contDiffOn.prodMk hF).contMDiffOn hU z hz L
      hA.hasMFDerivAt

end DifferentialGeometry.Topology.Manifold
