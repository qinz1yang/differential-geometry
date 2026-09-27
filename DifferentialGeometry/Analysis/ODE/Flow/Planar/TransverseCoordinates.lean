import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_localInverse_of_transverse_zeroSlice
    {f : E × ℝ → E × ℝ} {U : Set (E × ℝ)} {p : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hp : (p, 0) ∈ U)
    (hzero : ∀ x, (x, 0) ∈ U → f (x, 0) = (x, 0))
    (htransverse : (deriv (fun t ↦ f (p, t)) 0).2 ≠ 0) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) (E × ℝ),
      (p, 0) ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ z, e z = f z) := by
  let L := fderiv ℝ f (p, 0)
  have hdf : HasFDerivAt f L (p, 0) :=
    ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have heq : (fun x ↦ f (x, 0)) =ᶠ[𝓝 p] fun x ↦ (x, (0 : ℝ)) := by
    have hnear : ∀ᶠ x in 𝓝 p, (x, (0 : ℝ)) ∈ U :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hU.mem_nhds hp)
    exact hnear.mono hzero
  have hparam : L.comp (ContinuousLinearMap.inl ℝ E ℝ) = ContinuousLinearMap.inl ℝ E ℝ :=
    ((hdf.comp p (hasFDerivAt_prodMk_left p (0 : ℝ))).congr_of_eventuallyEq heq.symm).unique
      (hasFDerivAt_prodMk_left p (0 : ℝ))
  have htime : HasDerivAt (fun t ↦ f (p, t)) (L (0, 1)) 0 :=
    hdf.comp_hasDerivAt 0 ((hasDerivAt_const 0 p).prodMk (hasDerivAt_id 0))
  let v := L (0, 1)
  have hv : v.2 ≠ 0 := by rwa [htime.deriv] at htransverse
  let S : ℝ ≃L[ℝ] ℝ := Units.mk0 v.2 hv • ContinuousLinearEquiv.refl ℝ ℝ
  let T : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
    ((ContinuousLinearEquiv.prodComm ℝ E ℝ).trans
      (S.skewProd (ContinuousLinearEquiv.refl ℝ E)
        (ContinuousLinearMap.toSpanSingleton ℝ v.1))).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  have hT : (T : (E × ℝ) →L[ℝ] (E × ℝ)) = L := by
    apply ContinuousLinearMap.ext
    intro z
    have hz : z = (z.1, (0 : ℝ)) + z.2 • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    have hLz : L z = (z.1, (0 : ℝ)) + z.2 • v := by
      conv_lhs => rw [hz]
      rw [map_add, map_smul]
      have h := congrArg (fun A : E →L[ℝ] E × ℝ ↦ A z.1) hparam
      exact congrArg (fun w ↦ w + z.2 • v) h
    rw [hLz]
    change (z.1 + z.2 • v.1, v.2 * z.2) = (z.1 + z.2 • v.1, 0 + z.2 • v.2)
    simp [mul_comm]
  apply exists_localInverse_of_hasFDerivAt_equiv hf hU hp
  rwa [hT]

end DifferentialGeometry.Analysis
