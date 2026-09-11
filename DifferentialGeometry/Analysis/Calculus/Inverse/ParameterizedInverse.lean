import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse

noncomputable section
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_localInverse_preserving_parameter
    {h : E × ℝ → ℝ} {U : Set (E × ℝ)} {p₀ : E × ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U) (hp₀ : p₀ ∈ U)
    (hvertical : fderiv ℝ h p₀ (0, 1) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) (E × ℝ),
      p₀ ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, e p = (p.1, h p)) ∧
      ∀ q ∈ e.target, (e.symm q).1 = q.1 ∧ h (e.symm q) = q.2 := by
  let L := fderiv ℝ h p₀
  let c := L (0, 1)
  let S : ℝ ≃L[ℝ] ℝ := Units.mk0 c hvertical • ContinuousLinearEquiv.refl ℝ ℝ
  let T : (E × ℝ) ≃L[ℝ] (E × ℝ) := (ContinuousLinearEquiv.refl ℝ E).skewProd S
    (L.comp (ContinuousLinearMap.inl ℝ E ℝ))
  have hT : (T : (E × ℝ) →L[ℝ] (E × ℝ)) =
      (ContinuousLinearMap.fst ℝ E ℝ).prod L := by
    apply ContinuousLinearMap.ext
    intro p
    change (p.1, c * p.2 + L (p.1, 0)) = (p.1, L p)
    refine Prod.ext (by rfl) ?_
    have hp : p = (p.1, (0 : ℝ)) + p.2 • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    have hLp : L p = L (p.1, 0) + p.2 * c := by
      conv_lhs => rw [hp]
      rw [map_add, map_smul]
      rfl
    rw [hLp]
    ring
  have hderiv := (hh.contDiffAt (hU.mem_nhds hp₀)).differentiableAt (by simp) |>.hasFDerivAt
  have hd : HasFDerivAt (fun p : E × ℝ ↦ (p.1, h p))
      (T : (E × ℝ) →L[ℝ] (E × ℝ)) p₀ := by
    rw [hT]
    exact hasFDerivAt_fst.prodMk hderiv
  obtain ⟨e, hp, heU, he, heinv, heq⟩ := exists_localInverse_of_hasFDerivAt_equiv
    (contDiffOn_fst.prodMk hh) hU hp₀ hd
  refine ⟨e, hp, heU, he, heinv, heq, ?_⟩
  intro q hq
  have hboth : ((e.symm q).1, h (e.symm q)) = q := (heq _).symm.trans (e.right_inv hq)
  exact Prod.mk.inj hboth

end DifferentialGeometry.Analysis
