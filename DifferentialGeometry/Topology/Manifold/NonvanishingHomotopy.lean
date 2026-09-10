import DifferentialGeometry.Topology.Manifold.ComplexLogarithm
import Mathlib.Geometry.Manifold.Algebra.SMul
import DifferentialGeometry.Topology.Connected.BallComplement
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.ProperSpace

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem logarithm_eq_zero_on_preconnected {g : M → ℂ} {U : Set M}
    (hU : IsPreconnected U) (hg : ContinuousOn g U)
    (hexp : ∀ x ∈ U, Complex.exp (g x) = 1)
    {x₀ : M} (hx₀ : x₀ ∈ U) (hg₀ : g x₀ = 0) : EqOn g (fun _ ↦ 0) U := by
  apply Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hU hg continuousOn_const ?_ hx₀ hg₀
  intro x hx
  apply Subtype.ext
  exact (hexp x hx).trans Complex.exp_zero.symm

theorem exists_smooth_nonvanishing_homotopy_relative
    [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    {f : M → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (hne : ∀ x, f x ≠ 0)
    {U : Set M} (hU : IsConnected U) (hfixed : ∀ x ∈ U, f x = 1) :
    ∃ Φ : ℝ × M → ℂ,
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, ℂ) ∞ Φ ∧
      (∀ t x, Φ (t, x) ≠ 0) ∧
      (∀ x, Φ (0, x) = f x) ∧
      (∀ x, Φ (1, x) = 1) ∧
      ∀ t x, x ∈ U → Φ (t, x) = 1 := by
  obtain ⟨x₀, hx₀⟩ := hU.nonempty
  obtain ⟨g, hg, hg₀, hexp⟩ := exists_contMDiff_logarithm hf hne x₀ 0
    ((Complex.exp_zero).trans (hfixed x₀ hx₀).symm)
  have hgz : EqOn g (fun _ ↦ 0) U := logarithm_eq_zero_on_preconnected hU.isPreconnected
    hg.continuous.continuousOn (fun x hx ↦ (hexp x).trans (hfixed x hx)) hx₀ hg₀
  let Φ : ℝ × M → ℂ := fun p ↦ Complex.exp ((1 - p.1) • g p.2)
  have he : ContDiff ℝ ∞ Complex.exp :=
    (show ContDiff ℂ ∞ Complex.exp from Complex.contDiff_exp).restrict_scalars ℝ
  have ht : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (fun p : ℝ × M ↦ 1 - p.1) :=
    contMDiff_const.sub contMDiff_fst
  have hΦ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, ℂ) ∞ Φ :=
    he.contMDiff.comp (ht.smul (hg.comp contMDiff_snd))
  exact ⟨Φ, hΦ, fun _ _ ↦ Complex.exp_ne_zero _, by simpa [Φ] using hexp,
    by simp [Φ], fun t x hx ↦ by simp [Φ, hgz hx]⟩

theorem exists_smooth_nonvanishing_homotopy_of_compactMulSupport
    {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hne : ∀ z, f z ≠ 0)
    (hc : HasCompactMulSupport f) :
    ∃ Φ : ℝ × ℂ → ℂ,
      ContDiff ℝ ∞ Φ ∧
      (∀ t z, Φ (t, z) ≠ 0) ∧
      (∀ z, Φ (0, z) = f z) ∧
      (∀ z, Φ (1, z) = 1) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ t, mulTSupport (fun z ↦ Φ (t, z)) ⊆ Metric.closedBall 0 r := by
  obtain ⟨r, hr, hsupport⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hd : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hU := (Poincare.Topology.isPathConnected_compl_closedBall hd (0 : ℂ) r).isConnected
  have hfixed (z : ℂ) (hz : z ∈ (Metric.closedBall (0 : ℂ) r)ᶜ) : f z = 1 :=
    image_eq_one_of_notMem_mulTSupport (fun hs ↦ hz (hsupport hs))
  obtain ⟨Φ, hΦ, hnonzero, hzero, hone, hout⟩ :=
    exists_smooth_nonvanishing_homotopy_relative hf.contMDiff hne hU hfixed
  have hparam : ContMDiff 𝓘(ℝ, ℝ × ℂ) (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) ∞
      (fun p : ℝ × ℂ ↦ p) := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  refine ⟨Φ, (hΦ.comp hparam).contDiff, hnonzero, hzero, hone, r, hr, ?_⟩
  intro t
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra hzball
  exact hz (hout t z hzball)

end Poincare.Topology.Manifold
