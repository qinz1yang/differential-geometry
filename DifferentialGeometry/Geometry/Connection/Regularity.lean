import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

theorem ContMDiffCovariantDerivative.contMDiffOn
    {cov : CovariantDerivative I F V} {n : ℕ∞}
    (hcov : ContMDiffCovariantDerivative cov n) {U : Set M} (hU : IsOpen U)
    {σ : ∀ x : M, V x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ((n : ℕ∞ω) + 1) (T% σ) U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun x : M => (⟨x, cov σ x⟩ : TotalSpace (E →L[ℝ] F)
        (fun x => TangentSpace I x →L[ℝ] V x))) U := by
  intro x hx
  obtain ⟨χ, _, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hU.mem_nhds hx)
  have hχsmooth : ContMDiff I 𝓘(ℝ, ℝ) ((n : ℕ∞ω) + 1) χ :=
    χ.contMDiff.of_le (by exact_mod_cast (le_top : n + 1 ≤ (⊤ : ℕ∞)))
  have hτ := hχsmooth.contMDiffOn.smul_section_of_tsupport hU hχ hσ
  have hτderiv := contMDiffOn_univ.mp (hcov.contMDiff.contMDiff hτ.contMDiffOn)
  apply (hτderiv x).contMDiffWithinAt.congr_of_eventuallyEq
  · have heq : ∀ᶠ y in 𝓝 x, cov σ y = cov ((χ : M → ℝ) • σ) y := by
      filter_upwards [χ.eventuallyEq_one.eventuallyEq_nhds, hU.mem_nhds hx] with y hy hyU
      apply cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((hσ.contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt (by simp))
        (hτ.mdifferentiableAt (by simp)) (by simp)
      filter_upwards [hy] with z hz
      change σ z = χ z • σ z
      simp only [hz, Pi.one_apply, one_smul]
    exact heq.filter_mono nhdsWithin_le_nhds |>.mono fun y hy => by
      dsimp only
      rw [hy]
  · congr 1
    apply cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((hσ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      (hτ.mdifferentiableAt (by simp)) (by simp)
    filter_upwards [χ.eventuallyEq_one] with y hy
    change σ y = χ y • σ y
    simp only [hy, Pi.one_apply, one_smul]

end CovariantDerivative
