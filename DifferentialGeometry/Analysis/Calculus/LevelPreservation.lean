import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Continuous.eq_of_fderiv_eq_zero_on_preimage {f : E → F} (hf : Continuous f)
    {U : Set F} (hU : IsOpen U) (hdiff : DifferentiableOn ℝ f (f ⁻¹' U))
    (hzero : ∀ x, f x ∈ U → _root_.fderiv ℝ f x = 0) {x : E} (hx : f x ∈ U) (y : E) :
    f y = f x := by
  have hopen : IsOpen (f ⁻¹' {f x}) := by
    have h := (hU.preimage hf).isOpen_inter_preimage_of_fderiv_eq_zero hdiff
      (fun z hz => hzero z hz) {f x}
    convert! h using 1
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff]
    exact ⟨fun hz => ⟨hz ▸ hx, hz⟩, fun hz => hz.2⟩
  have hclosed : IsClosed (f ⁻¹' {f x}) := isClosed_singleton.preimage hf
  have hall := (show IsClopen (f ⁻¹' {f x}) from ⟨hclosed, hopen⟩).eq_univ ⟨x, rfl⟩
  have hy : y ∈ f ⁻¹' {f x} := hall ▸ mem_univ y
  exact hy

theorem Continuous.eq_iff_eq_of_deriv_eq_zero_on_preimage {f : ℝ → ℝ} (hf : Continuous f)
    {U : Set ℝ} (hU : IsOpen U) (hdiff : DifferentiableOn ℝ f (f ⁻¹' U))
    (hzero : ∀ x, f x ∈ U → deriv f x = 0) {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    f s = r ↔ f t = r := by
  have hD (x : ℝ) (hx : f x ∈ U) : _root_.fderiv ℝ f x = 0 := by
    apply ContinuousLinearMap.ext_ring
    simpa only [fderiv_apply_one_eq_deriv, zero_apply] using hzero x hx
  constructor
  · intro hs
    exact (hf.eq_of_fderiv_eq_zero_on_preimage hU hdiff hD (hs ▸ hr) t).trans hs
  · intro ht
    exact (hf.eq_of_fderiv_eq_zero_on_preimage hU hdiff hD (ht ▸ hr) s).trans ht

theorem Continuous.lt_iff_lt_of_deriv_eq_zero_on_preimage {f : ℝ → ℝ} (hf : Continuous f)
    {U : Set ℝ} (hU : IsOpen U) (hdiff : DifferentiableOn ℝ f (f ⁻¹' U))
    (hzero : ∀ x, f x ∈ U → deriv f x = 0) {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    f s < r ↔ f t < r := by
  have hlt : ∀ a b : ℝ, f a < r → f b < r := by
    intro a b ha
    by_contra hb
    obtain ⟨u, hu⟩ := intermediate_value_univ a b hf ⟨ha.le, le_of_not_gt hb⟩
    exact ha.ne ((hf.eq_iff_eq_of_deriv_eq_zero_on_preimage hU hdiff hzero hr u a).mp hu)
  exact ⟨hlt s t, hlt t s⟩

theorem Continuous.le_iff_le_of_deriv_eq_zero_on_preimage {f : ℝ → ℝ} (hf : Continuous f)
    {U : Set ℝ} (hU : IsOpen U) (hdiff : DifferentiableOn ℝ f (f ⁻¹' U))
    (hzero : ∀ x, f x ∈ U → deriv f x = 0) {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    f s ≤ r ↔ f t ≤ r := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt]
  exact or_congr (hf.eq_iff_eq_of_deriv_eq_zero_on_preimage hU hdiff hzero hr s t)
    (hf.lt_iff_lt_of_deriv_eq_zero_on_preimage hU hdiff hzero hr s t)
