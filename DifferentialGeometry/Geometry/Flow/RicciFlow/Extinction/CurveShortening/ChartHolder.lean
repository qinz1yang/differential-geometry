import DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ChartEquation

noncomputable section

open Set
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Schauder

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M} {β : M}

theorem exists_pos_le_curveShorteningChartDiffusionCoefficient
    (hg : MetricFamilySmoothOn D g) (β : M)
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {j : X → (ℝ × E × E)} (hj : ContinuousOn j S)
    (hjD : MapsTo j S (curveShorteningChartFirstJetDomain D g β)) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ S, a ≤ curveShorteningChartDiffusionCoefficient g β (j x) := by
  rcases S.eq_empty_or_nonempty with hS0 | hSn
  · subst S
    exact ⟨1, zero_lt_one, fun _ h => h.elim⟩
  have ha : ContinuousOn (fun x => curveShorteningChartDiffusionCoefficient g β (j x)) S :=
    (contDiffOn_curveShorteningChartDiffusionCoefficient hg β).continuousOn.comp hj hjD
  obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hSn ha
  exact ⟨_, curveShorteningChartDiffusionCoefficient_pos g β (hjD hx), hmin⟩

theorem exists_holderOnWith_curveShorteningChart_coefficients
    (hg : MetricFamilySmoothOn D g) (β : M)
    {X : Type*} [PseudoMetricSpace X] {S : Set X} (hS : IsCompact S)
    {K α : ℝ≥0} {j : X → (ℝ × E × E)}
    (hj : HolderOnWith K α j S) (hα : 0 < α)
    (hjD : MapsTo j S (curveShorteningChartFirstJetDomain D g β)) :
    ∃ a : ℝ, ∃ A B : ℝ≥0, 0 < a ∧
      (∀ x ∈ S, a ≤ curveShorteningChartDiffusionCoefficient g β (j x)) ∧
      HolderOnWith A α (fun x => curveShorteningChartDiffusionCoefficient g β (j x)) S ∧
      HolderOnWith B α (fun x => curveShorteningParametricChartReaction g β (j x)) S := by
  have hU := isOpen_curveShorteningChartFirstJetDomain hg β
  have ha := (contDiffOn_curveShorteningChartDiffusionCoefficient hg β).of_le
    (by decide : (1 : ℕ∞ω) ≤ ∞)
  have hb := (contDiffOn_curveShorteningParametricChartReaction hg β).of_le
    (by decide : (1 : ℕ∞ω) ≤ ∞)
  obtain ⟨A, hA⟩ := exists_holderOnWith_comp_of_contDiffOn_isCompact hS hU hj hα hjD ha
  obtain ⟨B, hB⟩ := exists_holderOnWith_comp_of_contDiffOn_isCompact hS hU hj hα hjD hb
  obtain ⟨a, ha, hapos⟩ := exists_pos_le_curveShorteningChartDiffusionCoefficient hg β
    hS (hj.continuousOn hα) hjD
  exact ⟨a, A, B, ha, hapos, hA, hB⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
