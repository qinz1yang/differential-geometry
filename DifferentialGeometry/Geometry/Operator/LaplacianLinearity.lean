import DifferentialGeometry.Geometry.Operator.Operators

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem laplacian_finset_sum_at {ι : Type*}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) (s : Finset ι) {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) y)
    (hgrad : ∀ i ∈ s, MDiffAt (T% fun y => gradientFun g (f i) y) x) :
    laplacian cov g (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, laplacian cov g (f i) x := by
  classical
  suffices h : ∀ s : Finset ι,
      (∀ i ∈ s, ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) y) →
      (∀ i ∈ s, MDiffAt (T% fun y => gradientFun g (f i) y) x) →
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => ∑ i ∈ s, f i z) y) ∧
      MDiffAt (T% fun y => gradientFun g (fun z => ∑ i ∈ s, f i z) y) x ∧
        laplacian cov g (fun y => ∑ i ∈ s, f i y) x =
          ∑ i ∈ s, laplacian cov g (f i) x from (h s hf hgrad).2.2
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    simp only [Finset.sum_empty]
    refine ⟨Filter.Eventually.of_forall (fun _ => mdifferentiableAt_const), ?_, ?_⟩
    · simpa only [gradientFun_const] using!
        (contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)).contMDiffAt.mdifferentiableAt one_ne_zero
    · exact laplacian_const cov g 0 x
  | @insert a s ha ih =>
    intro hf hgrad
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hgrad a (Finset.mem_insert_self a s)
    have hfs := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    obtain ⟨hfsum, hgs, hls⟩ := ih hfs (fun i hi => hgrad i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hfa, hfsum] with y hay hsy
      exact hay.add hsy
    · apply (mdifferentiableAt_add_section hga hgs).congr_of_eventuallyEq
      filter_upwards [hfa, hfsum] with y hfy hsy
      apply congrArg (fun v => (⟨y, v⟩ : TotalSpace E (TangentSpace I)))
      exact gradientFun_add g hfy hsy
    · rw [laplacian_add_at cov g hfa hfsum hga hgs, hls]

end DifferentialGeometry.Geometry.Operator
