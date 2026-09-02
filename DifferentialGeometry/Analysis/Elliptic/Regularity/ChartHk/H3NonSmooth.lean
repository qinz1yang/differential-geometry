import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.LocalWeakLimit

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartH3NonSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_loc_of_diff_data_and_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D_deriv : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {MBound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hM_nn : ∀ i k, 0 ≤ MBound i k)
    (h_uniform_bd :
      ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D_deriv.weakPartial i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (MBound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D_deriv.weakPartial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (MBound i k) := by
  classical
  intro i k
  exact exists_weak_second_partial_of_uniform_diffQuot_bound (I := I) (M := M)
    (g := g) (α := α) D_deriv
    hΩ''_open hΩ''_compact_closure hh₀ h_room hM_nn h_uniform_bd i k

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_loc_weak_partial_deriv_of_diff_data_and_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (D_deriv : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (h_weak_partial_eq : ∀ i, D_deriv.weakPartial i = D.weakPartialDeriv i)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {MBound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hM_nn : ∀ i k, 0 ≤ MBound i k)
    (h_uniform_bd :
      ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartialDeriv i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (MBound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D.weakPartialDeriv i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (MBound i k) := by
  classical
  intro i k
  have h_uniform_bd' :
      ∀ (i' : Fin (Module.finrank ℝ E)) (k' : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k' h (D_deriv.weakPartial i')) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (MBound i' k') := by
    intro i' k' h hh hh_le
    rw [h_weak_partial_eq i']
    exact h_uniform_bd i' k' h hh hh_le
  obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩ :=
    chart_loc_of_diff_data_and_uniform_bound (I := I) (M := M)
      (g := g) (α := α) D_deriv hΩ''_open hΩ''_compact_closure hh₀ h_room
      hM_nn h_uniform_bd' i k
  refine ⟨g_ik, hg_ik_memLp, ?_, hg_ik_norm⟩
  have h_eq := h_weak_partial_eq i
  intro φ hφ_smooth hφ_supp hφ_sub
  have h_id := hg_ik_partial φ hφ_smooth hφ_supp hφ_sub
  rw [show D.weakPartialDeriv i = D_deriv.weakPartial i from h_eq.symm]
  exact h_id

end ChartH3NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
