import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.DiscreteSubset

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff
namespace Poincare.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_near_regular_value {f : E → E} {s : Set E}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (y : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E, dist v y < ε ∧ ∀ x ∈ s, f x = v → (fderiv ℝ f x).det ≠ 0 := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := addHaar
  let C : Set E := {x | x ∈ s ∧ (fderiv ℝ f x).det = 0}
  have hnull : μ (f '' C) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := μ)
      (fun x hx => (hf x hx.1).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)
  have hae : ∀ᵐ v ∂μ, ∀ x ∈ s, f x = v → (fderiv ℝ f x).det ≠ 0 := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnull] with v hv x hx hfx hdet
    exact hv ⟨x, ⟨hx,hdet⟩, hfx⟩
  obtain ⟨v,hv,hreg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos μ y hε).ne' (ae_restrict_of_ae hae)
  exact ⟨v,hv,hreg⟩

theorem exists_open_isolated_fiber {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hdet : (fderiv ℝ f x).det ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, f y = f x → y = x := by
  let A := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  have hd : HasStrictFDerivAt f (A : E →L[ℝ] E) x := hf.hasStrictFDerivAt one_ne_zero
  let c := hd.toOpenPartialHomeomorph f
  exact ⟨c.source,c.open_source,hd.mem_toOpenPartialHomeomorph_source,
    fun y hy heq => c.injOn hy hd.mem_toOpenPartialHomeomorph_source heq⟩

theorem finite_regular_fiber {f : E → E} {K : Set E} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) (v : E)
    (hreg : ∀ x ∈ K, f x = v → (fderiv ℝ f x).det ≠ 0) :
    {x | x ∈ K ∧ f x = v}.Finite := by
  have hc : ContinuousOn f K := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hZ : IsCompact (K ∩ f ⁻¹' {v}) :=
    hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  apply hZ.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨V,hV,hxV,hfiber⟩ := exists_open_isolated_fiber (hf x hx.1) (hreg x hx.1 hx.2)
  refine ⟨V,hV,?_⟩
  ext y
  constructor
  · intro hy
    exact Set.mem_singleton_iff.mpr (hfiber y hy.1 (hy.2.2.trans hx.2.symm))
  · intro hy
    have hyx : y = x := hy
    subst y
    exact ⟨hxV,hx⟩

end Poincare.Calculus
