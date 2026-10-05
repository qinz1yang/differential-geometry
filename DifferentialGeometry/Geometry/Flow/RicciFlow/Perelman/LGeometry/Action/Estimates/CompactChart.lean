import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartRamp

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology NNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRampAct_slab_of_compact_chart
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (p : M) {A B : ℝ}
    (hreg : ∀ s ∈ Icc A B, T - s ^ 2 ∈ D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target) :
    ∃ Cg Cs : ℝ, 0 ≤ Cg ∧ 0 ≤ Cs ∧
      ∀ {a L : ℝ} {y z : E} (hL : 0 < L),
        (∀ r ∈ Icc (0 : ℝ) L, a + r ∈ Icc A B) →
        MapsTo (lChartRamp y z hL.le).toFun (Icc (0 : ℝ) L) K →
        lChartAction S T a p (lChartRamp y z hL.le) ≤
          (Cg / 2) * (‖z - y‖ ^ 2 / L) + Cs * L := by
  let τ : ℝ → ℝ := fun s => T - s ^ 2
  let J : Set ℝ := τ '' Icc A B
  have hτc : ContinuousOn τ (Icc A B) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro _ ⟨s, hs, rfl⟩
    exact hreg s hs
  obtain ⟨Cg, hCg⟩ :=
    chartGramOp_bound (I := I) hS.smoothMetric hJreg hJc p hKchart hKc
  let Kman : Set M := (extChartAt I p).symm '' K
  have hKman : IsCompact Kman :=
    hKc.image_of_continuousOn
      ((continuousOn_extChartAt_symm p).mono (hKchart.trans interior_subset))
  let P : ℝ → M → ℝ := fun s x => 2 * s ^ 2 * S.scalar (T - s ^ 2) x
  have hpair : ContinuousOn
      (fun q : ℝ × M => (T - q.1 ^ 2, q.2)) (Icc A B ×ˢ Kman) :=
    (continuous_const.sub (continuous_fst.pow 2)).continuousOn.prodMk
      continuous_snd.continuousOn
  have hmaps : MapsTo (fun q : ℝ × M => (T - q.1 ^ 2, q.2))
      (Icc A B ×ˢ Kman) (D.carrier ×ˢ (univ : Set M)) := by
    intro q hq
    exact ⟨D.regular_subset (hreg q.1 hq.1), mem_univ _⟩
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar : ContinuousOn
      (fun q : ℝ × M => S.scalar (T - q.1 ^ 2) q.2) (Icc A B ×ˢ Kman) := by
    simpa only [Function.comp_def] using hSc.scalar_continuousOn.comp hpair hmaps
  have hP : ContinuousOn (fun q : ℝ × M => P q.1 q.2) (Icc A B ×ˢ Kman) :=
    (continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar
  obtain ⟨Cs0, hCs0⟩ :=
    (isCompact_Icc.prod hKman).exists_bound_of_continuousOn hP
  let Cs : ℝ := max Cs0 0
  refine ⟨Cg, Cs, NNReal.coe_nonneg Cg, le_max_right _ _, ?_⟩
  intro a L y z hL htime hrange
  apply lRampAct_bound (I := I) S hS T a p hL
  · intro r hr
    exact hreg (a + r) (htime r hr)
  · intro r hr
    exact hKchart (hrange hr)
  · intro r hr
    exact hCg (T - (a + r) ^ 2, (lChartRamp y z hL.le).toFun r)
      ⟨⟨a + r, htime r hr, rfl⟩, hrange hr⟩
  · intro r hr
    have hpoint : (extChartAt I p).symm ((lChartRamp y z hL.le).toFun r) ∈ Kman :=
      ⟨(lChartRamp y z hL.le).toFun r, hrange hr, rfl⟩
    have hb := hCs0
      (a + r, (extChartAt I p).symm ((lChartRamp y z hL.le).toFun r))
      ⟨htime r hr, hpoint⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left Cs0 0)
end DifferentialGeometry.PDE.RicciFlow
