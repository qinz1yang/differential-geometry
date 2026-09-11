import DifferentialGeometry.Topology.VectorField.ContinuousIsolatedZero

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]


theorem HasContinuousIsolatedZero.congr {V W : ∀ x : M, TangentSpace I x} {x : M}
    (hV : HasContinuousIsolatedZero I V x) (hVW : V =ᶠ[𝓝 x] W) :
    HasContinuousIsolatedZero I W x where
  zero := hVW.self_of_nhds.symm.trans hV.zero
  continuous := by
    obtain ⟨s,hs,hc⟩ := hV.continuous
    refine ⟨s ∩ {y | V y = W y}, inter_mem hs hVW, ?_⟩
    apply (hc.mono inter_subset_left).congr
    intro y hy
    exact congrArg (fun v => (⟨y,v⟩ : TangentBundle I M)) hy.2.symm
  isolated := by
    filter_upwards [hVW,hV.isolated] with y hy hz
    exact fun hW => hz (hy.trans hW)

omit [IsManifold I 1 M] in
theorem hasContinuousIsolatedZero_modelSpace_iff {W : E → E} {x : E} :
    HasContinuousIsolatedZero 𝓘(ℝ, E) W x ↔ DifferentialGeometry.LocalDegree.isolatedZero W x := by
  constructor
  · intro h
    obtain ⟨s,hs,hc⟩ := h.continuous
    have hW : ContinuousOn W s := by
      intro y hy
      have hh := (FiberBundle.continuousWithinAt_section E).mp (hc y hy)
      simpa only [trivializationAt_model_space_apply] using! hh
    apply DifferentialGeometry.LocalDegree.isolatedZero_of_nhds hs hW h.zero
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [h.isolated] with y hy
    exact fun hne hz => hne (hy hz)
  · rintro ⟨R,hR⟩
    refine ⟨hR.zero, ⟨closedBall x R, closedBall_mem_nhds _ hR.pos, ?_⟩, ?_⟩
    · intro y hy
      apply (FiberBundle.continuousWithinAt_section E).mpr
      simpa only [trivializationAt_model_space_apply] using! hR.continuousOn y hy
    · filter_upwards [closedBall_mem_nhds x hR.pos] with y hy
      exact (hR.zero_iff y hy).mp

end DifferentialGeometry.VectorField
