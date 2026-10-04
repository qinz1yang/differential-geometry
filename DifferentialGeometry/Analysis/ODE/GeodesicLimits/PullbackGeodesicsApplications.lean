import DifferentialGeometry.Analysis.ODE.GeodesicLimits.PullbackGeodesics
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.MetricChristoffelApplications

/-!
# Consumer of the LC50 binding kernel: moving chart transitions

Euclidean metrics on both sides, chart transitions `ψ i = (· + a i)` with `a i → 0`, source geodesics
`t ↦ p i + t • v i`. `tendstoUniformlyOn_of_pullback_geodesics` gives the convergence of the pushed-forward
lines and velocities to `t ↦ pInf + t • vInf` and `vInf`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric
open DifferentialGeometry.MetricKoszul DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem tendstoUniformlyOn_translated_lines (a p v : ℕ → F) (pInf vInf : F)
    (ha : Tendsto a atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 pInf))
    (hv : Tendsto v atTop (𝓝 vInf)) (T : ℝ) :
    TendstoUniformlyOn (fun i t => (p i + t • v i) + a i) (fun t => pInf + t • vInf) atTop
        (Icc 0 T) ∧
      TendstoUniformlyOn (fun i t => fderiv ℝ (fun y => y + a i) (p i + t • v i) (v i))
        (fun _ => vInf) atTop (Icc 0 T) := by
  have hsymm : ∀ (y u w : F), (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) u w =
      (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) w u := fun _ u w => by
    simp only [innerSL_apply_apply]; exact real_inner_comm w u
  have hconv : ∀ C : Set F, IsCompact C → C ⊆ univ →
      MapCPConvergenceOn C 1 (fun (_ : ℕ) (_ : F) => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ))
        (fun _ => innerSL ℝ) := fun C _ _ ε hε =>
    ⟨0, fun k _ r _ x _ => by simp [mapDerivNorm, hε.le]⟩
  have hline : ∀ (q w : F) (t : ℝ), HasDerivWithinAt (fun t : ℝ => q + t • w) w (Icc 0 T) t :=
    fun q w t => by simpa using ((hasDerivWithinAt_id t (Icc 0 T)).smul_const w).const_add q
  have hconst : ∀ (q w : F) (t : ℝ), HasDerivWithinAt (fun _ : ℝ => w)
      (-(raisedKoszulOp ((fun _ : F => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) q)
        (fderiv ℝ (fun _ : F => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) q) w w)) (Icc 0 T) t :=
    fun q w t => by
      rw [raisedKoszulOp_innerSL_fderiv_const]
      simpa using hasDerivWithinAt_const t (Icc (0 : ℝ) T) w
  have hD : ∀ (i : ℕ) (y : F), fderiv ℝ (fun y => y + a i) y = ContinuousLinearMap.id ℝ F :=
    fun i y => by rw [fderiv_add_const, fderiv_fun_id]
  refine tendstoUniformlyOn_of_pullback_geodesics isOpen_univ (fun _ _ => innerSL ℝ)
    (fun _ => innerSL ℝ) (fun _ => contDiffOn_const) (fun _ y _ => hsymm y)
    (fun _ _ _ => isCoercive_innerSL) contDiffOn_const (fun _ _ => isCoercive_innerSL) hconv
    (fun _ => univ) (fun _ => isOpen_univ) (fun _ _ => innerSL ℝ) (fun i y => y + a i)
    (fun i => (contDiff_id.add contDiff_const).contDiffOn) (fun _ _ _ => mem_univ _)
    (fun i y _ => ⟨ContinuousLinearEquiv.refl ℝ F, by rw [hD]; rfl⟩)
    (fun i y _ u w => by rw [hD]; rfl)
    (fun i t => p i + t • v i) (fun i _ => v i) (fun _ _ _ => mem_univ _)
    (fun i t _ => hline (p i) (v i) t) (fun i t _ => hconst _ (v i) t)
    (fun t => pInf + t • vInf) (fun _ => vInf) (fun _ _ => mem_univ _)
    (fun t _ => hline pInf vInf t) (fun t _ => hconst _ vInf t) ?_ ?_
  · simpa using hp.add ha
  · simpa [hD] using hv

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
