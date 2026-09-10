import DifferentialGeometry.Topology.Manifold.InverseFunction

open Set Function Manifold Filter
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.BoundaryCollar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def flowBoxLinear (v : ℝ × E) (hv : v.1 ≠ 0) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toFun p := (p.1 * v.1, p.1 • v.2 + p.2)
  invFun q := (q.1 / v.1, q.2 - (q.1 / v.1) • v.2)
  left_inv p := by simp [hv]
  right_inv p := by simp [hv]
  map_add' p q := by
    apply Prod.ext
    · exact add_mul _ _ _
    · simp only [Prod.snd_add, Prod.fst_add, add_smul]
      abel
  map_smul' a p := by
    apply Prod.ext
    · change (a * p.1) * v.1 = a * (p.1 * v.1)
      ring
    · change (a * p.1) • v.2 + a • p.2 = a • (p.1 • v.2 + p.2)
      rw [smul_add, mul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem flowBoxLinear_apply (v : ℝ × E) (hv : v.1 ≠ 0) (p : ℝ × E) :
    flowBoxLinear v hv p = (p.1 * v.1, p.1 • v.2 + p.2) := rfl

@[simp]
theorem flowBoxLinear_symm_apply (v : ℝ × E) (hv : v.1 ≠ 0) (p : ℝ × E) :
    (flowBoxLinear v hv).symm p = (p.1 / v.1, p.2 - (p.1 / v.1) • v.2) := rfl

theorem hasFDerivAt_flowBox {Φ : (ℝ × E) × ℝ → ℝ × E}
    (hΦ : ContDiff ℝ ∞ Φ) (hzero : ∀ y, Φ (y, 0) = y)
    {g : ℝ × E → ℝ × E} {z : E}
    (hder : HasDerivAt (fun t => Φ ((0, z), t)) (g (0, z)) 0)
    (hg : (g (0, z)).1 ≠ 0) :
    HasFDerivAt (fun p : ℝ × E => Φ ((0, p.2), p.1))
      (flowBoxLinear (g (0, z)) hg).toContinuousLinearMap (0, z) := by
  let Ψ : ℝ × E → ℝ × E := fun p => Φ ((0, p.2), p.1)
  have hΨ : ContDiff ℝ ∞ Ψ := hΦ.comp ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)
  have hd : HasFDerivAt Ψ (fderiv ℝ Ψ (0, z)) (0, z) :=
    (hΨ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have htime := hd.comp (f := fun t : ℝ => (t, z)) (0 : ℝ)
    ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk (hasFDerivAt_const (𝕜 := ℝ) z (0 : ℝ)))
  have hspace := hd.comp (f := fun w : E => ((0 : ℝ), w)) z
    ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
  have ht : (fderiv ℝ Ψ (0, z)).comp
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] E)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (g (0, z)) := htime.unique hder.hasFDerivAt
  have hs : (fderiv ℝ Ψ (0, z)).comp
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) =
      (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) := by
    have he : Ψ ∘ (fun w : E => ((0 : ℝ), w)) =
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) : E → ℝ × E) := by
      funext w
      exact hzero (0, w)
    rw [he] at hspace
    exact hspace.unique ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)).hasFDerivAt
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro p
  have ht' := congrArg (fun L : ℝ →L[ℝ] (ℝ × E) => L p.1) ht
  have hs' := congrArg (fun L : E →L[ℝ] (ℝ × E) => L p.2) hs
  change (fderiv ℝ Ψ (0, z)) (p.1, 0) = p.1 • g (0, z) at ht'
  change (fderiv ℝ Ψ (0, z)) (0, p.2) = (0, p.2) at hs'
  change (p.1 * (g (0, z)).1, p.1 • (g (0, z)).2 + p.2) = (fderiv ℝ Ψ (0, z)) p
  rw [show p = (p.1, 0) + (0, p.2) by ext <;> simp, map_add, ht', hs']
  ext <;> simp [smul_eq_mul]

theorem exists_flowBox_of_flow [CompleteSpace E]
    {Φ : (ℝ × E) × ℝ → ℝ × E} (hΦ : ContDiff ℝ ∞ Φ)
    (hzero : ∀ y, Φ (y, 0) = y) {g : ℝ × E → ℝ × E} {z : E}
    (hder : HasDerivAt (fun t => Φ ((0, z), t)) (g (0, z)) 0)
    (hg : (g (0, z)).1 ≠ 0) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) 1,
      (0, z) ∈ e.source ∧ (e : ℝ × E → ℝ × E) = fun p => Φ ((0, p.2), p.1) := by
  apply exists_partialDiffeomorph_of_contDiffAt (flowBoxLinear (g (0, z)) hg)
  · exact (hΦ.comp ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)).contDiffAt.of_le
      (by norm_num)
  · exact hasFDerivAt_flowBox hΦ hzero hder hg

end Poincare.Manifold.BoundaryCollar
