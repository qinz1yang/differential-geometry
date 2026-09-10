import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.EigenpairDerivative
import DifferentialGeometry.Analysis.Calculus.Inverse.VectorParameterizedInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Poincare.Analysis

theorem exists_smooth_eigenpair_near_simple
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : P → E →L[ℝ] E) {U : Set P} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    {p₀ : P} (hp₀ : p₀ ∈ U) (hself : IsSelfAdjoint (A p₀))
    (μ₀ : ℝ) (w₀ : E) (hw₀ : ‖w₀‖ = 1) (heigen : A p₀ w₀ = μ₀ • w₀)
    (hsimple : Module.End.eigenspace (A p₀).toLinearMap μ₀ = Submodule.span ℝ {w₀}) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ V ⊆ U ∧
      ∃ (μ : P → ℝ) (w : P → E), ContDiffOn ℝ ∞ μ V ∧ ContDiffOn ℝ ∞ w V ∧
        μ p₀ = μ₀ ∧ w p₀ = w₀ ∧ ∀ p ∈ V, ‖w p‖ = 1 ∧ A p (w p) = μ p • w p := by
  let f : P × (ℝ × E) → ℝ × E := fun q ↦
    ((‖q.2.2‖ ^ 2 - 1) / 2, A q.1 q.2.2 - q.2.1 • q.2.2)
  let q₀ : P × (ℝ × E) := (p₀, μ₀, w₀)
  have hq₀ : q₀ ∈ U ×ˢ univ := ⟨hp₀, mem_univ _⟩
  have hf : ContDiffOn ℝ ∞ f (U ×ˢ univ) := by
    have hAp : ContDiffOn ℝ ∞ (fun q : P × (ℝ × E) ↦ A q.1) (U ×ˢ univ) :=
      hA.comp contDiffOn_fst (fun _ h ↦ h.1)
    have hs : ContDiffOn ℝ ∞ (fun q : P × (ℝ × E) ↦ q.2.2) (U ×ˢ univ) :=
      contDiffOn_snd.snd
    exact (((hs.norm_sq (𝕜 := ℝ)).sub contDiffOn_const).div_const 2).prodMk
      ((hAp.clm_apply contDiffOn_snd.snd).sub (contDiffOn_snd.fst.smul contDiffOn_snd.snd))
  let D := fderiv ℝ (fun q : ℝ × E ↦ ((‖q.2‖ ^ 2 - 1) / 2, A p₀ q.2 - q.1 • q.2)) (μ₀, w₀)
  have hbij : Function.Bijective D :=
    bijective_fderiv_normalized_eigenpair (A p₀) hself μ₀ w₀ hw₀ heigen hsimple
  let L : (ℝ × E) ≃L[ℝ] (ℝ × E) := (LinearEquiv.ofBijective D.toLinearMap hbij).toContinuousLinearEquiv
  have hslice := (((hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds hq₀)).differentiableAt
    (by simp)).hasFDerivAt).comp (μ₀, w₀)
      ((hasFDerivAt_const p₀ (μ₀, w₀)).prodMk (hasFDerivAt_id (μ₀, w₀)))
  have hvertical : ∀ q : ℝ × E, fderiv ℝ f q₀ (0, q) = L q := by
    intro q
    have h := congrArg (fun K : (ℝ × E) →L[ℝ] (ℝ × E) ↦ K q) hslice.fderiv
    exact h.symm
  obtain ⟨e, he₀, _, _, hei, he, hparam⟩ :=
    exists_localInverse_preserving_vector_parameter hf (hU.prod isOpen_univ) hq₀ L hvertical
  have hf₀ : f q₀ = 0 := by
    change ((‖w₀‖ ^ 2 - 1) / 2, A p₀ w₀ - μ₀ • w₀) = 0
    simp [hw₀, heigen]
  have heval : e q₀ = (p₀, 0) := by rw [he, hf₀]
  have htarget : (p₀, (0 : ℝ × E)) ∈ e.target := heval ▸ e.map_source he₀
  let V := U ∩ (fun p : P ↦ (p, (0 : ℝ × E))) ⁻¹' e.target
  have hVo : IsOpen V := hU.inter (e.open_target.preimage (continuous_id.prodMk continuous_const))
  let s : P → ℝ × E := fun p ↦ (e.symm (p, 0)).2
  have hs : ContDiffOn ℝ ∞ s V :=
    (hei.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ h ↦ h.2)).snd
  have hs₀ : s p₀ = (μ₀, w₀) := by
    change (e.symm (p₀, 0)).2 = (μ₀, w₀)
    rw [← heval, e.left_inv he₀]
  refine ⟨V, hVo, ⟨hp₀, htarget⟩, inter_subset_left, (fun p ↦ (s p).1),
    (fun p ↦ (s p).2), hs.fst, hs.snd, congrArg Prod.fst hs₀, congrArg Prod.snd hs₀, ?_⟩
  intro p hp
  have hroot := hparam (p, 0) hp.2
  have hpair : (p, s p) = e.symm (p, 0) := Prod.ext hroot.1.symm rfl
  have heq : f (p, s p) = 0 := (congrArg f hpair).trans hroot.2
  have hnorm := congrArg Prod.fst heq
  have heigen' := congrArg Prod.snd heq
  change (‖(s p).2‖ ^ 2 - 1) / 2 = 0 at hnorm
  change A p (s p).2 - (s p).1 • (s p).2 = 0 at heigen'
  exact ⟨by nlinarith [norm_nonneg (s p).2], sub_eq_zero.mp heigen'⟩

end Poincare.Analysis
