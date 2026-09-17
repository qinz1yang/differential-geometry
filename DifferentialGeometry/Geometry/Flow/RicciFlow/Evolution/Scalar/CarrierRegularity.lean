import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLocalCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ScalarCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn Bundle Filter Set
open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff _root_.Topology

private theorem continuousOn_of_uniform_time_sequences
    {E F : Type*} [NormedAddCommGroup E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] {U : Set E} (hU : IsOpen U) {J : Set ℝ}
    {f : ℝ → E → F}
    (hspace : ∀ t ∈ J, ContinuousOn (f t) U)
    (htime : ∀ t ∈ J, ∀ τ : ℕ → ℝ, (∀ n, τ n ∈ J) → Tendsto τ atTop (𝓝 t) →
      ∀ K : Set E, IsCompact K → K ⊆ U →
        TendstoUniformlyOn (fun n => f (τ n)) (f t) atTop K) :
    ContinuousOn (fun q : ℝ × E => f q.1 q.2) (J ×ˢ U) := by
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (s := J ×ˢ U)
    (x := (t, y)) ⟨ht, hy⟩]
  apply tendsto_iff_seq_tendsto.mpr
  intro q hq
  have hval := continuous_subtype_val.continuousAt.tendsto.comp hq
  have hτ : Tendsto (fun n => (q n).val.1) atTop (𝓝 t) :=
    continuous_fst.continuousAt.tendsto.comp hval
  have hyseq : Tendsto (fun n => (q n).val.2) atTop (𝓝 y) :=
    continuous_snd.continuousAt.tendsto.comp hval
  obtain ⟨K, hK, hyK, hKU⟩ := exists_compact_between isCompact_singleton hU
    (singleton_subset_iff.mpr hy)
  have hKnhds : K ∈ 𝓝 y := mem_of_superset
    (isOpen_interior.mem_nhds (hyK (mem_singleton y))) interior_subset
  have hunif := htime t ht (fun n => (q n).val.1)
    (fun n => (q n).property.1) hτ K hK hKU
  exact hunif.tendsto_comp ((hspace t ht y hy).mono hKU)
    (tendsto_nhdsWithin_iff.mpr ⟨hyseq, hyseq.eventually hKnhds⟩)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private def scalarJetTrace (J : MatJet E (Module.finrank ℝ E)) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (Matrix.of J.1)⁻¹ i j * jetRicci (chartModelBasis E) J i j

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem scalarJetTrace_smooth
    (J : MatJet E (Module.finrank ℝ E)) (hJ : (Matrix.of J.1).det ≠ 0) :
    ContDiffAt ℝ ∞ scalarJetTrace J := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (contDiffAt_jetInvGram hJ i j).mul (contDiffAt_jetRicci (chartModelBasis E) hJ i j)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem mapCInfConvergence_scalarJetTrace
    (g : ℕ → SmoothRiemannianMetric I M) (g0 : SmoothRiemannianMetric I M)
    (p : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), MapCInfConvergenceOnCompacts
      (extChartAt I p).target (fun n => chartGramOnE (I := I) (g n) p i j)
      (chartGramOnE (I := I) g0 p i j)) :
    MapCInfConvergenceOnCompacts (extChartAt I p).target
      (fun n y => scalarJetTrace (jet2 (chartGramPi (I := I) (g n) p) y))
      (fun y => scalarJetTrace (jet2 (chartGramPi (I := I) g0 p) y)) := by
  exact mapCInfConvergence_chartJetOperator g g0 p
    (isOpen_extChartAt_target (I := I) p) (fun _ h => h) hgram
    scalarJetTrace scalarJetTrace_smooth


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem scalar_eq_scalarJetTrace
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    scalarOnE (I := I) p (S.scalar t) y =
      scalarJetTrace (jet2 (chartGramPi (I := I) (S.base.metric t) p) y) := by
  have hW := isOpen_extChartAt_target (I := I) p
  have hG : ContDiffOn ℝ ∞ (chartGramPi (I := I) (S.base.metric t) p)
      (extChartAt I p).target :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
      chartGramOnE_contDiffOn (I := I) (S.base.metric t) p i j
  have hGAt := hG.contDiffAt (hW.mem_nhds hy)
  have hGd := hG.fderiv_of_isOpen hW (m := ∞) (by simp)
  have hnear : ∀ᶠ z in 𝓝 y, z ∈ (extChartAt I p).target := hW.mem_nhds hy
  change S.scalar t ((extChartAt I p).symm y) = _
  rw [S.scalar_chartTrace_eq t p hy]
  unfold scalarJetTrace
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [jet2_chartGram_invGram]
  rw [chartRicci_eq_jet (S.base.metric t) p (hW.interior_eq.symm ▸ hy)
    (hGAt.differentiableAt (by simp))
    (hnear.mono fun z hz =>
      (hG.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
    ((hGd.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))]

private theorem scalar_mapCInf_of_carrier_time_sequence
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ∈ Iic b) (p : M) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Iic b)
    (hτt : Tendsto τ atTop (𝓝 t)) :
    MapCInfConvergenceOnCompacts (extChartAt I p).target
      (fun n => scalarOnE (I := I) p (S.scalar (τ n)))
      (scalarOnE (I := I) p (S.scalar t)) := by
  have hgram := solution_chartGram_mapCInf_of_carrier_time_sequence S hS
    hcarrier hregular ht p τ hτ hτt
  have h := mapCInfConvergence_scalarJetTrace (fun n => S.base.metric (τ n))
    (S.base.metric t) p hgram
  exact h.congr (isOpen_extChartAt_target (I := I) p)
    (fun n y hy => scalar_eq_scalarJetTrace S (τ n) p hy)
    (fun y hy => scalar_eq_scalarJetTrace S t p hy)

theorem solution_chartScalar_jets_continuousOn_carrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (r : ℕ) :
    ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ r
      (scalarOnE (I := I) p (S.scalar q.1)) q.2)
      (Iic b ×ˢ (extChartAt I p).target) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hW := isOpen_extChartAt_target (I := I) p
  have hs (t : ℝ) : ContDiffOn ℝ ∞
      (scalarOnE (I := I) p (S.scalar t)) (extChartAt I p).target :=
    scalarOnE_contDiffOn (I := I) p (scalarSmoothOfSolution (I := I) S t)
  apply continuousOn_of_uniform_time_sequences hW (J := Iic b)
    (f := fun t y => iteratedFDeriv ℝ r (scalarOnE (I := I) p (S.scalar t)) y)
  · intro t _ y hy
    exact ((hs t).contDiffAt (hW.mem_nhds hy)).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top) |>.continuousWithinAt
  · intro t ht τ hτ hτt K hK hKW
    have h := scalar_mapCInf_of_carrier_time_sequence S hS hcarrier hregular ht p τ hτ hτt
    exact h.tendstoUniformlyOn_iteratedFDeriv hW hK hKW (fun n => hs (τ n)) (hs t) r

theorem solution_chartScalar_fderiv_continuousOn_carrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) :
    ContinuousOn (fun q : ℝ × E => fderiv ℝ
      (scalarOnE (I := I) p (S.scalar q.1)) q.2)
      (Iic b ×ˢ (extChartAt I p).target) := by
  have h := (continuousMultilinearCurryFin1 ℝ E ℝ).continuous.comp_continuousOn
    (solution_chartScalar_jets_continuousOn_carrier S hS hcarrier hregular p 1)
  refine h.congr fun q _ => ?_
  ext v
  simp only [Function.comp_apply, continuousMultilinearCurryFin1_apply,
    iteratedFDeriv_one_apply]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
