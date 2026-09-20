import Mathlib.MeasureTheory.Function.L1Space.Integrable

open Filter
open scoped Topology

namespace MeasureTheory

theorem integrable_of_dominated_convergence
    {ι α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated] [NeBot l]
    {F : ι → α → E} {f : α → E} (bound : α → ℝ)
    (hF : ∀ᶠ i in l, AEStronglyMeasurable (F i) μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ bound x)
    (hbound_int : Integrable bound μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Integrable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.eventually (hF.and hbound))
  have hseq : Tendsto (fun n => u (n + N)) atTop l :=
    hu.comp (tendsto_add_atTop_nat N)
  have hmeas : ∀ n, AEStronglyMeasurable (F (u (n + N))) μ :=
    fun n => (hN (n + N) (Nat.le_add_left N n)).1
  have hdom : ∀ n, ∀ᵐ x ∂μ, ‖F (u (n + N)) x‖ ≤ bound x :=
    fun n => (hN (n + N) (Nat.le_add_left N n)).2
  have hconv : ∀ᵐ x ∂μ,
      Tendsto (fun n => F (u (n + N)) x) atTop (𝓝 (f x)) :=
    hlim.mono fun x hx => hx.comp hseq
  exact ⟨aestronglyMeasurable_of_tendsto_ae atTop hmeas hconv,
    hasFiniteIntegral_of_dominated_convergence hbound_int.hasFiniteIntegral hdom hconv⟩

end MeasureTheory
