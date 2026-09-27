import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.DensityInverse

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem perelman_bracket_eq_zero_of_hamilton_jacobi
    (D : RealTimeInterval) (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (R u : ℝ → M → ℝ)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D G (fun s x => -R s x) u)
    {s : ℝ} (hs : s ∈ D.regular) (hspos : 0 < s)
    (hpos : ∀ y : M, 0 < u s y) (x : M)
    (hHJ : 2 * deriv (fun r => perelmanPotential (Module.finrank ℝ E) r (u r) x) s +
      (G.metric s).inner x
        (gradientFun (I := I) (G.metric s) (perelmanPotential (Module.finrank ℝ E) s (u s)) x)
        (gradientFun (I := I) (G.metric s) (perelmanPotential (Module.finrank ℝ E) s (u s)) x) -
      R s x + perelmanPotential (Module.finrank ℝ E) s (u s) x / s = 0) :
    s * (2 * laplacianAt (I := I) G s (perelmanPotential (Module.finrank ℝ E) s (u s)) x -
      (G.metric s).inner x
        (gradientFun (I := I) (G.metric s) (perelmanPotential (Module.finrank ℝ E) s (u s)) x)
        (gradientFun (I := I) (G.metric s) (perelmanPotential (Module.finrank ℝ E) s (u s)) x) +
      R s x) + perelmanPotential (Module.finrank ℝ E) s (u s) x -
        (Module.finrank ℝ E : ℝ) = 0 := by
  have hpde := (potential_pde D G (fun r y => -R r y) u (Module.finrank ℝ E)
    hu hs hspos hpos x).deriv
  rw [hpde] at hHJ
  field_simp [ne_of_gt hspos] at hHJ ⊢
  nlinarith

theorem perelman_bracket_eq_zero_of_conjugate_density_and_hamilton_jacobi
    (D : RealTimeInterval) (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (R f : ℝ → M → ℝ)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D G (fun s x => -R s x)
      (fun s => perelmanDensity (Module.finrank ℝ E) s (f s)))
    {s : ℝ} (hs : s ∈ D.regular) (hspos : 0 < s) (x : M)
    (hHJ : 2 * deriv (fun r => f r x) s +
      (G.metric s).inner x (gradientFun (I := I) (G.metric s) (f s) x)
        (gradientFun (I := I) (G.metric s) (f s) x) -
      R s x + f s x / s = 0) :
    s * (2 * laplacianAt (I := I) G s (f s) x -
      (G.metric s).inner x (gradientFun (I := I) (G.metric s) (f s) x)
        (gradientFun (I := I) (G.metric s) (f s) x) + R s x) + f s x -
        (Module.finrank ℝ E : ℝ) = 0 := by
  have hpos : ∀ y : M, 0 < perelmanDensity (Module.finrank ℝ E) s (f s) y := by
    intro y
    exact mul_pos (prefactor_pos (Module.finrank ℝ E) hspos) (Real.exp_pos _)
  have hsame :
      (fun r => perelmanPotential (Module.finrank ℝ E) r
        (perelmanDensity (Module.finrank ℝ E) r (f r)) x) =ᶠ[nhds s] (fun r => f r x) := by
    filter_upwards [eventually_gt_nhds hspos] with r hr
    rw [potential_density (Module.finrank ℝ E) hr]
  have hd := hsame.deriv_eq
  have h := perelman_bracket_eq_zero_of_hamilton_jacobi D G R
    (fun r => perelmanDensity (Module.finrank ℝ E) r (f r)) hu hs hspos hpos x
  simp only [potential_density (Module.finrank ℝ E) hspos, hd] at h
  exact h hHJ

end DifferentialGeometry.PDE.RicciFlow.Entropy
