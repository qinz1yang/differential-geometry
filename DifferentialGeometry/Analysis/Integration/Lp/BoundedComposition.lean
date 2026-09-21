import DifferentialGeometry.Analysis.Integration.Lp.BoundedConvergence

section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

theorem memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded
    {α X F : Type*} [MeasurableSpace α] [TopologicalSpace X]
    [NormedAddCommGroup F] {μ : Measure α} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {Φ : X → F} (hΦ : Continuous Φ) {D : ℝ} (hD : ∀ x, ‖Φ x‖ ≤ D)
    {U : ℕ → α → X} {v : α → X}
    (hU : ∀ n, AEStronglyMeasurable (Φ ∘ U n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => U n x) atTop (𝓝 (v x))) :
    MemLp (Φ ∘ v) p μ ∧
      Tendsto (fun n => eLpNorm (fun x => Φ (U n x) - Φ (v x)) p μ) atTop (𝓝 0) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hscalar : ∀ᵐ x ∂μ, Tendsto (fun n => Φ (U n x)) atTop (𝓝 (Φ (v x))) :=
    hlim.mono fun x hx => (hΦ.tendsto (v x)).comp hx
  have hfm (n : ℕ) : MemLp (Φ ∘ U n) p μ :=
    MemLp.of_bound (hU n) D (Eventually.of_forall fun x => hD (U n x))
  have hvm : MemLp (Φ ∘ v) p μ := MemLp.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop hU hscalar) D
    (Eventually.of_forall fun x => hD (v x))
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖(hfm n).toLp (Φ ∘ U n) x‖ ≤ D := by
    intro n
    filter_upwards [(hfm n).coeFn_toLp] with x hx
    rw [hx]
    exact hD (U n x)
  have hLp : ∀ᵐ x ∂μ, Tendsto (fun n => (hfm n).toLp (Φ ∘ U n) x)
      atTop (𝓝 (hvm.toLp (Φ ∘ v) x)) := by
    filter_upwards [hscalar, ae_all_iff.mpr (fun n => (hfm n).coeFn_toLp),
      hvm.coeFn_toLp] with x hx hn hv
    simpa only [hn, hv, Function.comp_apply] using hx
  refine ⟨hvm, ?_⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => Φ ∘ U n) hfm (Φ ∘ v) hvm).mp
    (Lp.tendsto_of_ae_tendsto_of_ae_norm_le hpt
      (fun n => (hfm n).toLp (Φ ∘ U n)) (hvm.toLp (Φ ∘ v)) hbound hLp)

end MeasureTheory

end

end
