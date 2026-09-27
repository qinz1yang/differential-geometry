import DifferentialGeometry.Geometry.Gradient.Normalized
import DifferentialGeometry.Geometry.Boundary.Normal.InwardCurve
import DifferentialGeometry.Geometry.Boundary.Normal.Derivative
import DifferentialGeometry.Geometry.Metric.Basic

noncomputable section
open scoped ContDiff Manifold Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Gradient

namespace DifferentialGeometry.Geometry.Boundary

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
private theorem mfderiv_inwardCoord_nonneg {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin f x.1) (hf : MDifferentiableAt I 𝓘(ℝ) f x.1) :
    (0 : ℝ) ≤ mfderiv I 𝓘(ℝ) f x.1 (inwardCoord (M := M) x) := by
  obtain ⟨γ, hγ0, hγ, hγd, -⟩ := exists_inward_curve x
  have hminγ : IsLocalMinOn (f ∘ γ) (Set.Ici 0) 0 := by
    have hm : IsLocalMin f (γ 0) := hγ0 ▸ hmin
    exact hm.comp_tendsto hγ.continuousWithinAt
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    rw [Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self, closure_Ioi]
    change (0 : ℝ) ≤ 0
    exact le_refl 0
  have hn := hminγ.fderivWithin_nonneg hcone
  have hc := mfderiv_comp_mfderivWithin_of_eq hf hγ
    (uniqueDiffWithinAt_Ici (0 : ℝ)).uniqueMDiffWithinAt hγ0
  rw [mfderivWithin_eq_fderivWithin] at hc
  have hv := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hc
  change (fderivWithin ℝ (f ∘ γ) (Set.Ici 0) 0) 1 =
    mfderiv I 𝓘(ℝ) f x.1 ((mfderivWithin 𝓘(ℝ) I γ (Set.Ici 0) 0) (1 : ℝ)) at hv
  rw [hγd] at hv
  exact hv ▸ hn

set_option backward.isDefEq.respectTransparency false in
private theorem mfderiv_inwardCoord_pos_of_isLocalMin (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin f x.1) (hf : MDifferentiableAt I 𝓘(ℝ) f x.1)
    (hreg : mfderiv I 𝓘(ℝ) f x.1 ≠ 0) :
    (0 : ℝ) < mfderiv I 𝓘(ℝ) f x.1 (inwardCoord (M := M) x) := by
  have hminB : IsLocalMin (fun y : BoundaryManifold I M ↦ f y.1) x :=
    hmin.comp_continuous (boundaryInclusion_contMDiff (I := I) (M := M)).continuous.continuousAt
  have hgrad : gradFun g f x.1 ∈ normalSubspace (M := M) g x := by
    intro w
    rw [inner_gradFun]
    exact mfderiv_boundary_tangent_eq_zero_at_local_min hminB hf w
  let v : normalSubspace (M := M) g x :=
    ⟨outwardDir (M := M) g x, outwardDir_mem_normalSubspace g x⟩
  have hv : v ≠ 0 := by
    intro he
    exact outwardDir_ne_zero g x (congrArg Subtype.val he)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (normalSubspace_finrank_one g x) hv (⟨gradFun g f x.1, hgrad⟩ : normalSubspace (M := M) g x)
  have hcg : c • outwardDir (M := M) g x = gradFun g f x.1 := congrArg Subtype.val hc
  have hcne : c ≠ 0 := by
    intro hc0
    have hg0 : gradFun g f x.1 = 0 := by simpa only [hc0, zero_smul] using hcg.symm
    have hu := mfderiv_normalizedGradient g f x.1 hreg
    simp only [normalizedGradient, hg0, smul_zero, map_zero] at hu
    change (0 : ℝ) = 1 at hu
    exact zero_ne_one hu
  have hne : mfderiv I 𝓘(ℝ) f x.1 (inwardCoord (M := M) x) ≠ (0 : ℝ) := by
    rw [← inner_gradFun, ← hcg, map_smul, smul_apply]
    change c * g.inner x.1 (outwardDir (M := M) g x) (inwardCoord (M := M) x) ≠ (0 : ℝ)
    exact mul_ne_zero hcne (g_inner_outwardDir_inwardCoord_neg g x).ne
  exact lt_of_le_of_ne (mfderiv_inwardCoord_nonneg hmin hf) hne.symm

private theorem outwardNormalDerivative_neg_of_isLocalMin (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin f x.1) (hf : MDifferentiableAt I 𝓘(ℝ) f x.1)
    (hreg : mfderiv I 𝓘(ℝ) f x.1 ≠ 0) : outwardNormalDerivative g f x < 0 := by
  apply outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min g
    (hmin.comp_continuous (boundaryInclusion_contMDiff (I := I) (M := M)).continuous.continuousAt) hf
  rw [inner_gradientFun]
  exact mfderiv_inwardCoord_pos_of_isLocalMin g hmin hf hreg

private theorem outwardNormalDerivative_pos_of_isLocalMax (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmax : IsLocalMax f x.1) (hf : MDifferentiableAt I 𝓘(ℝ) f x.1)
    (hreg : mfderiv I 𝓘(ℝ) f x.1 ≠ 0) : 0 < outwardNormalDerivative g f x := by
  have hregneg : mfderiv I 𝓘(ℝ) (-f) x.1 ≠ 0 := by
    rw [mfderiv_neg]
    exact neg_ne_zero.mpr hreg
  have hn := outwardNormalDerivative_neg_of_isLocalMin g hmax.neg hf.neg hregneg
  change g.inner x.1 (gradientFun g (-f) x.1) (outwardNormal g x) < 0 at hn
  rw [gradientFun_neg g hf, map_neg, neg_apply] at hn
  exact neg_neg_iff_pos.mp hn

omit hI in
private theorem normalizedGradient_scale_pos (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) (hreg : mfderiv I 𝓘(ℝ) f x ≠ 0) :
    0 < (g.inner x (gradFun g f x) (gradFun g f x))⁻¹ := by
  apply inv_pos.mpr
  apply g.pos
  intro hg0
  have hu := mfderiv_normalizedGradient g f x hreg
  simp only [normalizedGradient, hg0, smul_zero, map_zero] at hu
  change (0 : ℝ) = 1 at hu
  exact zero_ne_one hu

theorem normalizedGradient_inner_outwardNormal_neg_of_isLocalMin
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin f x.1) (hf : MDifferentiableAt I 𝓘(ℝ) f x.1)
    (hreg : mfderiv I 𝓘(ℝ) f x.1 ≠ 0) :
    g.inner x.1 (normalizedGradient g f x.1) (outwardNormal g x) < 0 := by
  rw [normalizedGradient, map_smul, smul_apply]
  exact mul_neg_of_pos_of_neg (normalizedGradient_scale_pos g f x.1 hreg)
    (outwardNormalDerivative_neg_of_isLocalMin g hmin hf hreg)

theorem normalizedGradient_inner_outwardNormal_pos_of_isLocalMax
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : BoundaryManifold I M}
    (hmax : IsLocalMax f x.1) (hf : MDifferentiableAt I 𝓘(ℝ) f x.1)
    (hreg : mfderiv I 𝓘(ℝ) f x.1 ≠ 0) :
    0 < g.inner x.1 (normalizedGradient g f x.1) (outwardNormal g x) := by
  rw [normalizedGradient, map_smul, smul_apply]
  exact mul_pos (normalizedGradient_scale_pos g f x.1 hreg)
    (outwardNormalDerivative_pos_of_isLocalMax g hmax hf hreg)

end DifferentialGeometry.Geometry.Boundary
