/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Analysis.Complex.NormalizedGradient

set_option autoImplicit false
noncomputable section

open Set Filter Metric Manifold
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem normalized_projection_power_hasFDerivAt (c w : ℂ) (m : ℕ) :
    HasFDerivAt (fun z : ℂ => c + z ^ (m + 1) / ((m + 1 : ℕ) : ℂ))
      (ContinuousLinearMap.mul ℝ ℂ (w ^ m)) w := by
  have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hd : HasDerivAt (fun z : ℂ => c + z ^ (m + 1) / ((m + 1 : ℕ) : ℂ))
      (w ^ m) w := by
    convert (hasDerivAt_const w c).add
      ((hasDerivAt_pow (m + 1) w).div_const ((m + 1 : ℕ) : ℂ)) using 1
    simp only [Nat.add_sub_cancel, zero_add, mul_div_cancel_left₀ _ hm]
  convert hd.hasFDerivAt.restrictScalars ℝ using 1
  ext v
  change w ^ m * v = v * w ^ m
  exact mul_comm _ _

/-- The derivative of an actual original-chart inverse-germ graph equals the
normalized derivative of the same height in its supplied root coordinate.
The literal power relation determines the normalization, with no equation or
regularity assumption at the branch center. -/
theorem chartLeadingPlaneProjection_graph_fderiv_eq_normalized_gradient
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
      ContDiffOn ℝ ∞ h eGraph.target →
      ∀ w ∈ eRoot.target, w ≠ 0 → eRoot.symm w ∈ eGraph.source →
        fderiv ℝ h (F (eRoot.symm w)) =
          Analysis.complexPowerNormalizedGradient m Hroot w := by
  intro Q X F m eRoot eGraph heGraph hpower h Hroot hh w hw hw0 hwGraph
  let P : ℂ → ℂ := fun v => F a + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
  have hy : F (eRoot.symm w) ∈ eGraph.target := by
    rw [← heGraph]
    exact eGraph.map_source hwGraph
  have hRootCont : ContinuousAt (eRoot.symm : ℂ → ℂ) w :=
    eRoot.continuousOn_invFun.continuousAt (eRoot.open_target.mem_nhds hw)
  have hnear : Hroot =ᶠ[𝓝 w] h ∘ P := by
    filter_upwards [eRoot.open_target.mem_nhds hw,
      hRootCont (eGraph.open_source.mem_nhds hwGraph)] with v hv hvGraph
    have hPv : P v = eGraph (eRoot.symm v) := by
      calc
        P v = F (eRoot.symm v) := (hpower v hv).symm
        _ = eGraph (eRoot.symm v) := congrArg (fun f : ℂ → ℂ => f (eRoot.symm v)) heGraph.symm
    change Q N (X (eRoot.symm v) - X a) = Q N (X (eGraph.symm (P v)) - X a)
    rw [hPv, eGraph.left_inv hvGraph]
  have hPw : F (eRoot.symm w) = P w := hpower w hw
  have hdh : DifferentiableAt ℝ h (P w) := by
    rw [← hPw]
    exact (hh.contDiffAt (eGraph.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hdP : HasFDerivAt P (ContinuousLinearMap.mul ℝ ℂ (w ^ m)) w :=
    normalized_projection_power_hasFDerivAt (F a) w m
  have hDroot : fderiv ℝ Hroot w =
      (fderiv ℝ h (P w)).comp (ContinuousLinearMap.mul ℝ ℂ (w ^ m)) :=
    hnear.fderiv_eq.trans (hdh.hasFDerivAt.comp w hdP).fderiv
  rw [hPw]
  change fderiv ℝ h (P w) =
    (fderiv ℝ Hroot w).comp (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹))
  rw [hDroot]
  ext v
  change fderiv ℝ h (P w) v = fderiv ℝ h (P w) (w ^ m * ((w ^ m)⁻¹ * v))
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hw0), one_mul]

end DifferentialGeometry.Geometry
