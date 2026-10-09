/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientNormalizedGraph

set_option autoImplicit false
noncomputable section

open Set Filter Metric Manifold
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

/-- A single fixed original-chart graph germ identifies the normalized root
slope on a neighborhood. Its actual graph Hessian is the derivative of that
same slope composed with the inverse power derivative. -/
theorem chartLeadingPlaneProjection_graph_second_fderiv_eq_normalized_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) (U : ℂ → M) (a : ℂ)
    (b : Fin (Module.finrank ℝ E) → ℂ) (N : E) :
    let Q := chartGramBilin g p (U a)
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p (U a) b (X z)
    ∀ (m : ℕ) (eRoot eGraph : OpenPartialHomeomorph ℂ ℂ),
      (eGraph : ℂ → ℂ) = F →
      (∀ v ∈ eRoot.target,
        F (eRoot.symm v) = F a + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) →
      let h : ℂ → ℝ := fun y => Q N (X (eGraph.symm y) - X a)
      let Hroot : ℂ → ℝ := fun v => Q N (X (eRoot.symm v) - X a)
      let R := Analysis.complexPowerNormalizedGradient m Hroot
      ContDiffOn ℝ ∞ h eGraph.target →
      ∀ w ∈ eRoot.target, w ≠ 0 → eRoot.symm w ∈ eGraph.source →
        ((fun v : ℂ => fderiv ℝ h
          (F a + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ))) =ᶠ[𝓝 w] R) ∧
        DifferentiableAt ℝ R w ∧
        fderiv ℝ (fderiv ℝ h) (F (eRoot.symm w)) =
          (fderiv ℝ R w).comp (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)) ∧
        ‖fderiv ℝ (fderiv ℝ h) (F (eRoot.symm w))‖ ≤
          ‖fderiv ℝ R w‖ / ‖w‖ ^ m := by
  intro Q X F m eRoot eGraph heGraph hpower h Hroot R hh w hw hw0 hwGraph
  let P : ℂ → ℂ := fun v => F a + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
  have hRootCont : ContinuousAt (eRoot.symm : ℂ → ℂ) w :=
    eRoot.continuousOn_invFun.continuousAt (eRoot.open_target.mem_nhds hw)
  have hnear : (fun v : ℂ => fderiv ℝ h (P v)) =ᶠ[𝓝 w] R := by
    filter_upwards [eRoot.open_target.mem_nhds hw, eventually_ne_nhds hw0,
      hRootCont (eGraph.open_source.mem_nhds hwGraph)] with v hv hv0 hvGraph
    change fderiv ℝ h (F a + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) = R v
    rw [← hpower v hv]
    exact DifferentialGeometry.Geometry.chartLeadingPlaneProjection_graph_fderiv_eq_normalized_gradient
      g p U a b N m eRoot eGraph heGraph hpower hh v hv hv0 hvGraph
  have hPw : F (eRoot.symm w) = P w := hpower w hw
  have hy : P w ∈ eGraph.target := by
    rw [← hPw, ← heGraph]
    exact eGraph.map_source hwGraph
  have h2 : ContDiffAt ℝ 2 h (P w) :=
    (hh.contDiffAt (eGraph.open_target.mem_nhds hy)).of_le (by norm_num)
  have hdh : DifferentiableAt ℝ (fderiv ℝ h) (P w) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hdP : HasFDerivAt P (ContinuousLinearMap.mul ℝ ℂ (w ^ m)) w := by
    have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hd : HasDerivAt P (w ^ m) w := by
      dsimp only [P]
      convert (hasDerivAt_const w (F a)).add
        ((hasDerivAt_pow (m + 1) w).div_const ((m + 1 : ℕ) : ℂ)) using 1
      simp only [Nat.add_sub_cancel, zero_add, mul_div_cancel_left₀ _ hm]
    convert hd.hasFDerivAt.restrictScalars ℝ using 1
    ext v
    change w ^ m * v = v * w ^ m
    exact mul_comm _ _
  have hdR : HasFDerivAt R
      ((fderiv ℝ (fderiv ℝ h) (P w)).comp
        (ContinuousLinearMap.mul ℝ ℂ (w ^ m))) w :=
    (hdh.hasFDerivAt.comp w hdP).congr_of_eventuallyEq hnear.symm
  have hsecond : fderiv ℝ (fderiv ℝ h) (F (eRoot.symm w)) =
      (fderiv ℝ R w).comp (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)) := by
    rw [hPw, hdR.fderiv]
    ext u v
    change fderiv ℝ (fderiv ℝ h) (P w) u v =
      fderiv ℝ (fderiv ℝ h) (P w) (w ^ m * ((w ^ m)⁻¹ * u)) v
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hw0), one_mul]
  refine ⟨hnear, hdR.differentiableAt, hsecond, ?_⟩
  rw [hsecond]
  calc
    _ ≤ ‖fderiv ℝ R w‖ * ‖ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ R w‖ / ‖w‖ ^ m := by
      rw [ContinuousLinearMap.opNorm_mul_apply, norm_inv, norm_pow, div_eq_mul_inv]

end DifferentialGeometry.Geometry
