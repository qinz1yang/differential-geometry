import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalSmoothConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRicciJetOperators


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open Bundle Filter Set DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ancientConnectionC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem solution_chartChristoffel_jets_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (p : M) {y : E} (hy : y ∈ (extChartAt I p).target)
    (i j k : Fin (Module.finrank ℝ E)) (r : ℕ) :
    ContinuousWithinAt
      (fun s => iteratedFDeriv ℝ r (chartChristoffel (I := I) (S.base.metric s) p i j k) y)
      (Iic b) t := by
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (s := Iic b) (x := t) ht]
  apply tendsto_iff_seq_tendsto.mpr
  intro τ hτ
  have hτt : Tendsto (fun n => (τ n).val) atTop (𝓝 t) :=
    continuous_subtype_val.continuousAt.tendsto.comp hτ
  have hW := isOpen_extChartAt_target (I := I) p
  have hgram := solution_chartGram_mapCInf_of_carrier_time_sequence S hS
    hcarrier hregular ht p (fun n => (τ n).val) (fun n => (τ n).property) hτt
  have hchr := mapCInfConvergence_chartChristoffel_of_gram
    (fun n => S.base.metric (τ n).val) (S.base.metric t) p hW (fun _ hx => hx) hgram i j k
  have hs (s : ℝ) : ContDiffOn ℝ ∞
      (chartChristoffel (I := I) (S.base.metric s) p i j k) (extChartAt I p).target := by
    simpa only [hW.interior_eq] using
      chartChristoffel_contDiffOn_interior (I := I) (S.base.metric s) p i j k
  exact (MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv hW isCompact_singleton
    (singleton_subset_iff.mpr hy) hchr (fun n => hs (τ n).val) (hs t) r).tendsto_at
      (mem_singleton y)


theorem solution_chartChristoffel_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (p : M) {y : E} (hy : y ∈ (extChartAt I p).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousWithinAt (fun s => chartChristoffel (I := I) (S.base.metric s) p i j k y)
      (Iic b) t := by
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (s := Iic b) (x := t) ht]
  apply tendsto_iff_seq_tendsto.mpr
  intro τ hτ
  have hτt : Tendsto (fun n => (τ n).val) atTop (𝓝 t) :=
    continuous_subtype_val.continuousAt.tendsto.comp hτ
  have hgram := solution_chartGram_mapCInf_of_carrier_time_sequence S hS
    hcarrier hregular ht p (fun n => (τ n).val) (fun n => (τ n).property) hτt
  have hchr := mapCInfConvergence_chartChristoffel_of_gram
    (fun n => S.base.metric (τ n).val) (S.base.metric t) p
    (isOpen_extChartAt_target (I := I) p) (fun _ hx => hx) hgram i j k
  exact (tendstoUniformlyOn_of_cPConvergence
    (hchr {y} isCompact_singleton (singleton_subset_iff.mpr hy) 0)).tendsto_at
      (mem_singleton y)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
