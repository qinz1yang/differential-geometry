import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Defs
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance : ChartedSpace E (Hyperboloid E) :=
  Manifold.Homeomorph.pullbackChartedSpace spaceHomeomorph

instance : IsManifold 𝓘(ℝ, E) ω (Hyperboloid E) :=
  Manifold.Homeomorph.instIsManifoldPullback spaceHomeomorph

def spaceDiffeomorph : Hyperboloid E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E :=
  Manifold.Homeomorph.pullbackDiffeomorph spaceHomeomorph

@[simp] theorem spaceDiffeomorph_apply (x : Hyperboloid E) : spaceDiffeomorph x = x.space := rfl

@[simp] theorem spaceDiffeomorph_symm_apply (x : E) : spaceDiffeomorph.symm x = ofSpace x := rfl

@[simp] theorem spaceDiffeomorph_toHomeomorph :
    (spaceDiffeomorph (E := E)).toHomeomorph = spaceHomeomorph := rfl

variable {n : ℕ∞ω}

theorem contMDiff_space : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (space : Hyperboloid E → E) :=
  Manifold.Homeomorph.contMDiff_pullback spaceHomeomorph

theorem contMDiff_ofSpace : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (ofSpace : E → Hyperboloid E) :=
  Manifold.Homeomorph.contMDiff_symm_pullback spaceHomeomorph

theorem contMDiff_time : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (time : Hyperboloid E → ℝ) := by
  have h : ContDiff ℝ n (fun x : E => Real.sqrt (1 + ‖x‖ ^ 2)) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun x => by positivity
  simpa only [Function.comp_def, ← time_eq_sqrt] using h.contMDiff.comp contMDiff_space

theorem contMDiff_time_space :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) n (fun x : Hyperboloid E => (x.time, x.space)) :=
  contMDiff_time.prodMk_space contMDiff_space

end DifferentialGeometry.Hyperboloid
