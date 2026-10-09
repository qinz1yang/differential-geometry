import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.inv_scalar_le_time_length_of_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps : ℝ} (neck : ∀ n, StrongNeck G.flow eps x.1 (τ n)) :
    (metricScalarAt L.metric x)⁻¹ ≤ s - a := by
  have hscalar := (L.tendsto_metricScalarAt x).comp hτ
  have ht : Tendsto τ atTop (𝓝 s) := hτ.mono_right nhdsWithin_le_nhds
  have hlim := ht.sub (hscalar.inv₀ hx.ne')
  have hleft : ∀ n, a ≤ τ n - (G.flow.scalar (τ n) x.1)⁻¹ := by
    intro n
    have hmem := (neck n).time_domain
      ⟨le_rfl, sub_le_self _ (inv_nonneg.mpr (neck n).Q_pos.le)⟩
    exact hmem.1
  have hbound : a ≤ s - (metricScalarAt L.metric x)⁻¹ :=
    ge_of_tendsto hlim (Eventually.of_forall hleft)
  linarith

theorem TerminalLimitMetric.parabolicTime_mem_incoming_of_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps : ℝ} (neck : ∀ n, StrongNeck G.flow eps x.1 (τ n))
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k) (hcenter : N.center = x)
    {v : ℝ} (hv : v ∈ Ico (-1 : ℝ) 0) :
    parabolicTime s N.scale v ∈ Ico a s := by
  have hscale : N.scale = metricScalarAt L.metric x := by rw [N.scale_scalar, hcenter]
  have hleft := L.inv_scalar_le_time_length_of_strongNecks hτ x hx neck
  have hlow : -(N.scale⁻¹) ≤ v / N.scale := by
    simpa only [neg_div, one_div] using
      div_le_div_of_nonneg_right hv.1 N.scale_pos.le
  have hhigh : v / N.scale < 0 := div_neg_of_neg_of_pos hv.2 N.scale_pos
  rw [← hscale] at hleft
  change a ≤ s + v / N.scale ∧ s + v / N.scale < s
  constructor <;> linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
