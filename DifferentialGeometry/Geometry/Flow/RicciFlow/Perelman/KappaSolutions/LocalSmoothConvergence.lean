import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialJetTimeContinuity


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem mapCInfConvOnCompacts_of_locally {U : Set E} {f : ℕ → E → F} {f₀ : E → F}
    (hloc : ∀ x ∈ U, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ MapCInfConvergenceOnCompacts W f f₀) :
    MapCInfConvergenceOnCompacts U f f₀ := by
  classical
  intro K hK hKU m ε hε
  choose W hW hxW hconv using fun x : K => hloc x.val (hKU x.property)
  have hcompact (x : K) : ∃ L : Set E, IsCompact L ∧ {x.val} ⊆ interior L ∧ L ⊆ W x :=
    exists_compact_between isCompact_singleton (hW x) (singleton_subset_iff.mpr (hxW x))
  choose L hL hxL hLW using hcompact
  obtain ⟨T, hcover⟩ := hK.elim_finite_subcover (fun x : K => interior (L x))
    (fun _ => isOpen_interior)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hxL ⟨y, hy⟩ (mem_singleton y)⟩)
  choose N hN using fun x : K => hconv x (L x) (hL x) (hLW x) m ε hε
  refine ⟨T.sup N, fun n hn r hr y hy => ?_⟩
  obtain ⟨x, hxT, hyL⟩ := mem_iUnion₂.mp (hcover hy)
  exact hN x n ((Finset.le_sup hxT).trans hn) r hr y (interior_subset hyL)

end Calculus

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]


theorem solution_chartGram_mapCInf_of_carrier_time_sequence {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (p : M) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ≤ b)
    (hτt : Tendsto τ atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
    MapCInfConvergenceOnCompacts (extChartAt I p).target
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S.base.metric t) p i j) := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  apply mapCInfConvOnCompacts_of_locally
  intro y hy
  obtain ⟨W, hW, hxW, _hWt, hconv⟩ := solution_chartGram_mapCInf_of_time_tendsto
    S hS hcarrier hregular ht p ((extChartAt I p).symm y) ((extChartAt I p).map_target hy)
  refine ⟨W, hW, ?_, hconv τ hτ hτt i j⟩
  simpa only [(extChartAt I p).right_inv hy] using hxW

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
