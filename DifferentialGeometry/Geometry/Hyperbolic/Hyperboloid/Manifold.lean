import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Defs
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

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

theorem chartAt_eq_spaceHomeomorph (x : Hyperboloid E) :
    chartAt E x = spaceHomeomorph.toOpenPartialHomeomorph := by
  change spaceHomeomorph.toOpenPartialHomeomorph.trans (OpenPartialHomeomorph.refl E) = _
  exact OpenPartialHomeomorph.trans_refl _

theorem tangent_trivializationAt_symmL (x y : Hyperboloid E) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ y = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by
    rw [chartAt_eq_spaceHomeomorph]
    trivial)]
  have h : achart E x = achart E y :=
    Subtype.ext ((chartAt_eq_spaceHomeomorph x).trans (chartAt_eq_spaceHomeomorph y).symm)
  rw [h]
  ext v
  exact (tangentBundleCore 𝓘(ℝ, E) (Hyperboloid E)).coordChange_self
    (achart E y) y (mem_achart_source E y) v

theorem mfderiv_spaceDiffeomorph (x : Hyperboloid E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x = (1 : E →L[ℝ] E) := by
  have h : (extChartAt 𝓘(ℝ, E) x : Hyperboloid E → E) = spaceDiffeomorph := by
    rw [extChartAt_coe, chartAt_eq_spaceHomeomorph]
    rfl
  rw [← h]
  exact mfderiv_extChartAt_self

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

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mfderiv_time_apply (x : Hyperboloid E) (v : TangentSpace 𝓘(ℝ, E) x) :
    NormedSpace.fromTangentSpace (𝕜 := ℝ) x.time
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) time x v) =
      inner ℝ x.space
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x v)) / x.time := by
  let f : E → ℝ := fun u => Real.sqrt (1 + ‖u‖ ^ 2)
  have hd : HasFDerivAt (fun u : E => 1 + ‖u‖ ^ 2) (2 • innerSL ℝ x.space) x.space := by
    simpa only [zero_add] using!
      (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x.space).add
        (hasStrictFDerivAt_norm_sq x.space).hasFDerivAt
  have hf : HasFDerivAt f
      ((1 / (2 * Real.sqrt (1 + ‖x.space‖ ^ 2))) • (2 • innerSL ℝ x.space)) x.space :=
    hd.sqrt (by positivity)
  have htime : (time : Hyperboloid E → ℝ) = f ∘ spaceDiffeomorph := by
    funext y
    exact y.time_eq_sqrt
  let u : E := NormedSpace.fromTangentSpace (𝕜 := ℝ) (spaceDiffeomorph x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x v)
  change mvfderiv 𝓘(ℝ, E) time x v = inner ℝ x.space u / x.time
  rw [htime, mvfderiv_comp_apply (f := (spaceDiffeomorph : Hyperboloid E → E)) (g := f)
    x hf.differentiableAt.mdifferentiableAt
    ((spaceDiffeomorph (E := E)).contMDiff.mdifferentiableAt (by decide)), mvfderiv_eq_fderiv]
  change fderiv ℝ f x.space u = inner ℝ x.space u / f x.space
  rw [hf.fderiv]
  simp only [smul_apply, two_smul, smul_eq_mul]
  change (1 / (2 * Real.sqrt (1 + ‖x.space‖ ^ 2))) *
    (inner ℝ x.space u + inner ℝ x.space u) =
      inner ℝ x.space u / Real.sqrt (1 + ‖x.space‖ ^ 2)
  rw [← x.time_eq_sqrt]
  field_simp [x.time_pos.ne']
  ring

end DifferentialGeometry.Hyperboloid
