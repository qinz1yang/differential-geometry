import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

theorem contMDiff_logarithm_of_continuous {f g : M → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) n f) (hg : Continuous g)
    (hexp : ∀ x, Complex.exp (g x) = f x) : ContMDiff I 𝓘(ℝ, ℂ) n g := by
  intro x
  let q : M → ℂ := fun y ↦ f y * (f x)⁻¹
  have hq : ContMDiff I 𝓘(ℝ, ℂ) n q :=
    contDiff_mul.contMDiff.comp (hf.prodMk_space contMDiff_const)
  have hxq : q x = 1 := mul_inv_cancel₀ ((hexp x) ▸ Complex.exp_ne_zero (g x))
  have hlog : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n Complex.log (q x) := by
    apply (Complex.contDiffAt_log (n := n) ?_).restrict_scalars ℝ |>.contMDiffAt
    rw [hxq]
    exact Complex.one_mem_slitPlane
  have hlocal : ContMDiffAt I 𝓘(ℝ, ℂ) n (fun y ↦ g x + Complex.log (q y)) x :=
    contMDiffAt_const.add (hlog.comp x (hq x))
  apply hlocal.congr_of_eventuallyEq
  have hc : ContinuousAt (fun y ↦ (g y - g x).im) x :=
    Complex.continuous_im.continuousAt.comp (hg.continuousAt.sub continuousAt_const)
  have hn : ∀ᶠ y in 𝓝 x, (g y - g x).im ∈ Ioo (-Real.pi) Real.pi :=
    hc.eventually (isOpen_Ioo.mem_nhds (by simpa using
      (show (0 : ℝ) ∈ Ioo (-Real.pi) Real.pi from ⟨by linarith [Real.pi_pos], Real.pi_pos⟩)))
  filter_upwards [hn] with y hy
  have he : q y = Complex.exp (g y - g x) := by
    dsimp only [q]
    rw [Complex.exp_sub, hexp, hexp, div_eq_mul_inv]
  rw [he, Complex.log_exp hy.1 hy.2.le]
  ring

theorem exists_contMDiff_logarithm [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    {f : M → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) n f) (hne : ∀ x, f x ≠ 0)
    (x₀ : M) (z₀ : ℂ) (hz₀ : Complex.exp z₀ = f x₀) :
    ∃ g : M → ℂ, ContMDiff I 𝓘(ℝ, ℂ) n g ∧ g x₀ = z₀ ∧
      ∀ x, Complex.exp (g x) = f x := by
  let F : C(M, {z : ℂ // z ≠ 0}) :=
    ⟨fun x ↦ ⟨f x, hne x⟩, hf.continuous.subtype_mk _⟩
  obtain ⟨g, ⟨hg₀, hg⟩, _⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F x₀ z₀ (Subtype.ext hz₀)
  have he (x : M) : Complex.exp (g x) = f x :=
    congrArg Subtype.val (congrFun hg x)
  exact ⟨g, contMDiff_logarithm_of_continuous hf g.continuous he, hg₀, he⟩

end Poincare.Topology.Manifold
