import DifferentialGeometry.Analysis.Calculus.TimeJetMatch
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.RankZeroRealization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarLapDiffCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarPotential
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.HeatPotential
import DifferentialGeometry.Geometry.Operator.NormGradSqTime
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ScalarWeyl

/-!
# Classical scalar reconstruction inputs for the conjugate-heat limit

This file starts the classical assembly above the strong Galerkin limit.  It
keeps the local Weyl input out of the strong-limit module and first packages
compact-interior, time-uniform spectral majorants for every scalar time jet.
-/

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.Evolution.Volume
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
/-- Reverse-time chart Gram entries inherit joint smoothness from the solution metric. -/
private theorem rev_gram_smooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) (T : Real) {U : Set Real}
    (hU : Set.MapsTo (fun r : Real => T - r) U D.regular)
    (x₀ : M) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        chartGramMatrix (I := I)
          ((reverseFamily (I := I) (M := M) (flowG (I := I) S) T).metric p.1)
          x₀ p.2 i j)
      (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  let e := trivializationAt E (TangentSpace I) x₀
  change ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
    (fun p : Real × M =>
      chartGramMatrix (I := I)
        ((reverseFamily (I := I) (M := M) (flowG (I := I) S) T).metric p.1)
        x₀ p.2 i j) (U ×ˢ e.baseSet)
  have hframe :
      IsLocalFrameOn I E ∞ (e.localFrame (chartModelBasis E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I ∞ (chartModelBasis E)
  have hrev : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (T - p.1, p.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hmap : Set.MapsTo (fun p : Real × M => (T - p.1, p.2))
      (U ×ˢ e.baseSet) (D.regular ×ˢ e.baseSet) := by
    intro p hp
    exact ⟨hU hp.1, hp.2⟩
  have hcomp : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      ((fun q : Real × M =>
        (S.family.metric q.1).inner q.2
          (e.localFrame (chartModelBasis E) i q.2)
          (e.localFrame (chartModelBasis E) j q.2)) ∘
        fun p : Real × M => (T - p.1, p.2)) (U ×ˢ e.baseSet) :=
    (hS.smoothMetric.frameCompSmooth
      (e.localFrame (chartModelBasis E)) hframe i j).comp hrev.contMDiffOn hmap
  refine hcomp.congr ?_
  intro p hp
  have hx : p.2 ∈ e.baseSet := hp.2
  simp only [Function.comp_apply, chartGramMatrix_apply, reverse_metric]
  rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx,
    e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
  rfl

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
/-- The reversed Ricci-flow metric has volume trace `2 R`. -/
private theorem rev_trace_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) (T s : Real)
    (hs : T - s ∈ D.regular) (x : M) :
    traceTimeDerivMetricAt (I := I)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T) s x =
        (2 : Real) * S.scalar (T - s) x := by
  classical
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  let Ric : RicciTensorField (I := I) (M := M) Real := fun r y X Y =>
    -S.ricciAt (T - r) y (vec2 (I := I) X Y)
  let scalar : Real → M → Real := fun r y => -S.scalar (T - r) y
  have hsub : HasDerivAt (fun r : Real => T - r) (-1) s := by
    simpa using
      (hasDerivAt_const (x := s) (c := T)).sub (hasDerivAt_id (x := s))
  have hEq : MetricVariationEquationDerivAt (I := I) G Ric s := by
    intro y X Y
    have hcomp := (metricDerivAt (I := I) S hS ⟨T - s, hs⟩ y X Y).comp s hsub
    simpa [G, Ric, reverseFamily, flowG] using hcomp
  have hScalar : ScalarRealizesRicciTraceInFrame (I := I)
      (scalar s) (Ric s)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric s))
      (volumeTraceFrame (I := I) (M := M)) := by
    intro y
    have hy : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
      exact mem_baseSet_trivializationAt E (TangentSpace I) y
    let b := chartBasisFamily (I := I) y hy
    have hinv : MetricInverseInBasis_gen (I := I) (G.metric s) y b
        (fun i j => chartInvGramMatrix (I := I) (G.metric s) y y i j) := by
      simpa only [b] using
        chartInvGram_inverse (I := I) (G.metric s) y hy
    have htrace := metricTracePair0SAt_eq_sum_basis
      (I := I) (G.metric s) b
      (fun i j => chartInvGramMatrix (I := I) (G.metric s) y y i j)
      hinv (S.ricciAt (T - s) y)
    change -S.scalar (T - s) y =
      ∑ i : Fin (Module.finrank Real E),
        ∑ j : Fin (Module.finrank Real E),
          ((chartGramMatrix (I := I) (G.metric s) y y)⁻¹) i j *
            (-S.ricciAt (T - s) y
              (vec2 (I := I) (chartBasisVecFiber (I := I) y i y)
                (chartBasisVecFiber (I := I) y j y)))
    rw [S.scalar_eq_metricTrace]
    change -metricTracePair0SAt (I := I) (G.metric s)
      (S.ricciAt (T - s) y) = _
    rw [htrace]
    simp only [b, chartBasisFamily_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [chartInvGramMatrix]
    ring
  have htrace :=
    traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
      (I := I) (M := M) G Ric scalar hEq hScalar x
  change traceTimeDerivMetricAt (I := I) G s x = _
  rw [htrace]
  dsimp only [scalar]
  ring

omit [BoundarylessManifold I M] [NeZero (Module.finrank Real E)] in
/-- A genuine reversed heat potential preserves its moving Riemannian mass at interior times. -/
theorem heatpot_mass_deriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {tau : Real} (htau : 0 ≤ tau) {u : Real → M → Real}
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau htau)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun r x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
      u)
    {s : Real} (hs : s ∈ Set.Ioo (0 : Real) tau)
    (hTs : (T : Real) - s ∈ D.regular) :
    HasDerivAt
      (fun r : Real =>
        ∫ x, u r x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) r))
      0 s := by
  classical
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)
  let U : Set Real := Set.Ioo (0 : Real) tau ∩
    (fun r : Real => (T : Real) - r) ⁻¹' D.regular
  have hsub_cont : Continuous (fun r : Real => (T : Real) - r) :=
    continuous_const.sub continuous_id
  have hUopen : IsOpen U :=
    isOpen_Ioo.inter (D.regular_isOpen.preimage hsub_cont)
  have hsU : s ∈ U := ⟨hs, hTs⟩
  have hUmap : Set.MapsTo (fun r : Real => (T : Real) - r) U D.regular := by
    intro r hr
    exact hr.2
  have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    simpa only [G] using
      rev_gram_smooth (I := I) (M := M) hS (T : Real) hUmap x₀ i j
  have hu_joint : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => u p.1 p.2) (U ×ˢ Set.univ) :=
    hu.jointSmooth.mono (Set.prod_mono Set.inter_subset_left Set.Subset.rfl)
  have hvariation :
      HasDerivAt
        (fun r : Real => ∫ x, u r x ∂(volumeMeasureFamily (I := I) (M := M) G r))
        (∫ x, (deriv (fun r : Real => u r x) s +
              (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G s x * u s x)
            ∂(volumeMeasureFamily (I := I) (M := M) G s)) s := by
    simpa [volumeMeasureFamily, traceTimeDerivMetricAt] using
      (first_var_joint (I := I) (M := M) hUopen hsU hgram hu_joint)
  have hu_smooth : ContMDiff I 𝓘(Real, Real) ∞ (u s) :=
    hu.sliceSmooth s ⟨hs.1.le, hs.2.le⟩
  have hgreen :=
    integral_smul_laplacian_sub_eq_zero_family
      (I := I) (M := M) (fun r : Real => G.metric r)
      (f := fun _ : M => (1 : Real)) (h := u s)
      contMDiff_const hu_smooth s
  have hlap :
      ∫ x, Δ_g (I := I) (G.metric s) hu_smooth x
        ∂(volumeMeasureFamily (I := I) (M := M) G s) = 0 := by
    simpa only [one_mul, Δ_g_const, mul_zero, sub_zero] using hgreen
  have hmass :
      ∫ x, (deriv (fun r : Real => u r x) s +
            (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G s x * u s x)
          ∂(volumeMeasureFamily (I := I) (M := M) G s) = 0 := by
    calc
      _ = ∫ x, Δ_g (I := I) (G.metric s) hu_smooth x
            ∂(volumeMeasureFamily (I := I) (M := M) G s) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [(hu.equation s hs x).deriv]
          rw [rev_trace_eq (I := I) (M := M) hS (T : Real) s hTs x]
          rw [laplacianAt_eq_delta (I := I) (M := M) G s hu_smooth (by rfl) x]
          simp only [conjCoeff_apply]
          ring
      _ = 0 := hlap
  change HasDerivAt
    (fun r : Real => ∫ x, u r x ∂(volumeMeasureFamily (I := I) (M := M) G r)) 0 s
  exact hvariation.congr_deriv hmass

omit [BoundarylessManifold I M] [NeZero (Module.finrank Real E)] in
/-- On a shorter interval, a genuine reversed heat potential has constant moving mass. -/
theorem heatpot_mass_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {tau : Real} (htau : 0 < tau) {u : Real → M → Real}
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau htau.le)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun r x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
      u) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ tau ∧
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (RealTimeInterval.closed 0 tau' htau'.le)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
        (fun r x =>
          (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
        u ∧
      ∀ s ∈ Set.Icc (0 : Real) tau',
        (∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) s)) =
        ∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) 0) := by
  classical
  let W : Set Real := (fun r : Real => (T : Real) - r) ⁻¹' D.regular
  have hsub_cont : Continuous (fun r : Real => (T : Real) - r) :=
    continuous_const.sub continuous_id
  have hWopen : IsOpen W := D.regular_isOpen.preimage hsub_cont
  have h0W : (0 : Real) ∈ W := by
    change (T : Real) - 0 ∈ D.regular
    simpa only [sub_zero] using T.2
  obtain ⟨l, w, h0lw, hlw⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWopen.mem_nhds h0W)
  let tau' : Real := min tau (w / 2)
  have htau' : 0 < tau' := by
    simpa only [tau'] using lt_min htau (half_pos h0lw.2)
  have htau'_tau : tau' ≤ tau := min_le_left _ _
  have hmap : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Icc (0 : Real) tau') D.regular := by
    intro r hr
    apply hlw
    refine ⟨h0lw.1.trans_le hr.1, ?_⟩
    exact lt_of_le_of_lt (hr.2.trans (min_le_right tau (w / 2)))
      (half_lt_self h0lw.2)
  have hu' := hu.mono
    (D' := RealTimeInterval.closed 0 tau' htau'.le)
    (Set.Icc_subset_Icc le_rfl htau'_tau)
    (Set.Ioo_subset_Ioo le_rfl htau'_tau)
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)
  let mass : Real → Real := fun s =>
    ∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M) G s)
  have hmass_cont : ContinuousOn mass (Set.Icc (0 : Real) tau') := by
    have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
        ContinuousOn
          (fun p : Real × M => chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
          (Set.Icc (0 : Real) tau' ×ˢ
            (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      exact (rev_gram_smooth (I := I) (M := M) hS (T : Real) hmap x₀ i j).continuousOn
    simpa only [mass, volumeMeasureFamily, metricFamilyForMeasure] using
      (integral_family_cont (I := I) (M := M) isCompact_Icc hgram hu'.jointCont)
  have hderiv (r : Real) (hr : r ∈ Set.Ioo (0 : Real) tau') :
      HasDerivAt mass 0 r := by
    have hTr : (T : Real) - r ∈ D.regular := hmap ⟨hr.1.le, hr.2.le⟩
    simpa only [mass, G] using
      heatpot_mass_deriv (I := I) (M := M) S hS T htau'.le hu' hr hTr
  have hdiff : DifferentiableOn Real mass (Set.Ioo (0 : Real) tau') := by
    intro r hr
    exact (hderiv r hr).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv mass) 0 (Set.Ioo (0 : Real) tau') := by
    intro r hr
    exact (hderiv r hr).deriv
  let mid : Real := tau' / 2
  have hmid : mid ∈ Set.Ioo (0 : Real) tau' := by
    exact ⟨half_pos htau', half_lt_self htau'⟩
  have hinner : Set.EqOn mass (fun _ : Real => mass mid)
      (Set.Ioo (0 : Real) tau') := by
    intro r hr
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hzero hr hmid
  have hclosed : Set.EqOn mass (fun _ : Real => mass mid)
      (Set.Icc (0 : Real) tau') := by
    apply hinner.of_subset_closure hmass_cont continuousOn_const
      Set.Ioo_subset_Icc_self
    rw [closure_Ioo htau'.ne]
  refine ⟨tau', htau', htau'_tau, hu', ?_⟩
  intro s hs
  change mass s = mass 0
  exact (hclosed hs).trans (hclosed ⟨le_rfl, htau'.le⟩).symm

omit [BoundarylessManifold I M] [NeZero (Module.finrank Real E)] in
/-- On a prescribed reflected regular interval, a genuine heat potential has
constant moving mass on the entire closed interval. -/
theorem heatpot_mass_on
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {tau : Real} (htau : 0 < tau) {u : Real → M → Real}
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau htau.le)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun r x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
      u)
    (hreg : ∀ r ∈ Set.Icc (0 : Real) tau,
      (T : Real) - r ∈ D.regular) :
    ∀ s ∈ Set.Icc (0 : Real) tau,
      (∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) s)) =
      ∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) 0) := by
  classical
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)
  let mass : Real → Real := fun s =>
    ∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M) G s)
  have hmap : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Icc (0 : Real) tau) D.regular := by
    intro r hr
    exact hreg r hr
  have hmass_cont : ContinuousOn mass (Set.Icc (0 : Real) tau) := by
    have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
        ContinuousOn
          (fun p : Real × M => chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
          (Set.Icc (0 : Real) tau ×ˢ
            (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      exact (rev_gram_smooth (I := I) (M := M) hS (T : Real) hmap x₀ i j).continuousOn
    simpa only [mass, volumeMeasureFamily, metricFamilyForMeasure] using
      (integral_family_cont (I := I) (M := M) isCompact_Icc hgram hu.jointCont)
  have hderiv (r : Real) (hr : r ∈ Set.Ioo (0 : Real) tau) :
      HasDerivAt mass 0 r := by
    have hTr : (T : Real) - r ∈ D.regular :=
      hreg r ⟨hr.1.le, hr.2.le⟩
    simpa only [mass, G] using
      heatpot_mass_deriv (I := I) (M := M) S hS T htau.le hu hr hTr
  have hdiff : DifferentiableOn Real mass (Set.Ioo (0 : Real) tau) := by
    intro r hr
    exact (hderiv r hr).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv mass) 0 (Set.Ioo (0 : Real) tau) := by
    intro r hr
    exact (hderiv r hr).deriv
  let mid : Real := tau / 2
  have hmid : mid ∈ Set.Ioo (0 : Real) tau := by
    exact ⟨half_pos htau, half_lt_self htau⟩
  have hinner : Set.EqOn mass (fun _ : Real => mass mid)
      (Set.Ioo (0 : Real) tau) := by
    intro r hr
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hzero hr hmid
  have hclosed : Set.EqOn mass (fun _ : Real => mass mid)
      (Set.Icc (0 : Real) tau) := by
    apply hinner.of_subset_closure hmass_cont continuousOn_const
      Set.Ioo_subset_Icc_self
    rw [closure_Ioo htau.ne]
  intro s hs
  change mass s = mass 0
  exact (hclosed hs).trans (hclosed ⟨le_rfl, htau.le⟩).symm

/-- Every Sobolev realization of the Galerkin limit has the original limiting
coefficient on the compact Galerkin interval. -/
@[simp] theorem galLimExt_coeff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (m : Nat) {t : Real} (ht : t ∈ Icc (0 : Real) tau)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    (galLimExt hτ hlim m t).coeff i = ulim t i := by
  rw [galLimExt_mem hτ hlim m ht]
  rfl

/-- At reverse time zero, every Sobolev realization of the Galerkin limit is
the prescribed smooth initial tensor in that same Sobolev scale. -/
@[simp] theorem galLimExt_zero
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (m : Nat) :
    galLimExt hτ hlim m 0 =
      ccTensorToHs (I := I) (M := M)
        (S.family.metric (T : Real)) 0 (m : Real) u0 := by
  apply tensorHs.ext
  funext i
  rw [galLimExt_coeff hτ hlim m ⟨le_rfl, hτ⟩,
    ccTensorToHs_coeff, hlim.lim_init i]

/-- The first covariant derivative of a smooth rank-zero tensor, after full
evaluation, is the differential of its scalar readout. -/
private theorem covGrad0_apply
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 0)
    (x : M) (X : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 1 I x from
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad
            (I := I) (M := M) g 0 0 U).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun _ : Fin 1 => X) =
      extDerivFun (I := I)
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection) x X := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) U.toSection
  let A : Tensor0SField ∞ 0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞ f hf
  have hunit (y : M) :
      tensor0SSpace_evalScalar y (unitZeroSec (I := I) (M := M) y) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  have hsection :
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[Real] Tensor0SSpace 0 I y from
          U.toSection y) (unitZeroSec (I := I) (M := M) y)) =
        fun y : M => A y := by
    funext y
    have hlift := TensorRSField.lift_scalar0
      (n := (∞ : WithTop ℕ∞)) U.toSection
    change U.toSection y (unitZeroSec (I := I) (M := M) y) = A y
    rw [← hlift, Tensor0SField.toRS0_apply, hunit, one_smul]
  have hscalar : Tensor0SNabla.scalarFn I M (fun y : M => A y) = f := by
    funext y
    rw [Tensor0SNabla.scalarFn_eq_apply_zero]
    change Tensor0SField.toScalarField ∞ A y = f y
    exact congrFun (Tensor0SField.toScalarField_fromScalarField ∞ f hf) y
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
    (I := I) (M := M) g 0 0 U x
    (unitZeroSec (I := I) (M := M) x) (fun _ : Fin 1 => X)]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def,
    tensorRSCovariantDerivative_zeroS_unit_eval, hsection,
    Tensor0SNabla.tensor0SCovariantDerivative_apply_zero, hscalar]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (extDerivFun (I := I) f x X)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- On every compact subinterval of the smooth backward-time interior, all
time jets of the scalar Galerkin coefficients admit a single summable spectral
majorant at every natural Sobolev order. -/
theorem galLim_jet_mass
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ ⦃a b : Real⦄, 0 < a → a ≤ b → b < tau' →
        (∀ i, ContDiffOn Real ∞ (fun t => ulim t i) (Icc a b)) ∧
        ∀ (j m : Nat),
          ∃ B : TensorEigenIdx (I := I) (M := M)
              (S.family.metric (T : Real)) 0 0 → Real,
            Summable B ∧
            ∀ i, ∀ t ∈ Icc a b,
              tensorSobolevWeight (I := I) (M := M) i (m : Real) *
                (iteratedDeriv j (fun s => ulim s i) t) ^ 2 ≤ B i := by
  classical
  obtain ⟨tau', htau', htau'_tau, hsmooth⟩ :=
    galLimExt_smooth (I := I) (M := M) hS hτ hlim
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  obtain ⟨p, _hp, hpsum⟩ := htail
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro a b ha hab hb
  have hKsub : Icc a b ⊆ Ioo (0 : Real) tau' := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hcoeff_smooth (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ContDiffOn Real ∞ (fun t => ulim t i) (Icc a b) := by
    let L := tensorHsCoeffL (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0)
      (a := ((0 : Nat) : Real)) i
    have hcomp : ContDiffOn Real ∞
        (fun t => L (galLimExt hτ.le hlim 0 t))
        (Ioo (0 : Real) tau') := by
      simpa only [Function.comp_apply] using
        L.contDiff.comp_contDiffOn (hsmooth 0)
    have hcoeff_open : ContDiffOn Real ∞
        (fun t => ulim t i) (Ioo (0 : Real) tau') := by
      refine hcomp.congr ?_
      intro t ht
      simpa only [L, q, tensorHsCoeffL_apply] using
        (galLimExt_coeff hτ.le hlim 0
          ⟨ht.1.le, ht.2.le.trans htau'_tau⟩ i).symm
    exact hcoeff_open.mono hKsub
  refine ⟨hcoeff_smooth, ?_⟩
  intro j m
  obtain ⟨k : Nat, hk⟩ := exists_nat_gt p
  have hmp : (m : Real) + p ≤ ((m + k : Nat) : Real) := by
    rw [Nat.cast_add]
    nlinarith
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0) hmp
  let U : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => J (galLimExt hτ.le hlim (m + k) t)
  have hU : ContDiffOn Real ∞ U (Ioo (0 : Real) tau') := by
    simpa only [U, Function.comp_apply] using
      J.contDiff.comp_contDiffOn (hsmooth (m + k))
  let W : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => iteratedDeriv j U t
  have hWopen : ContinuousOn W (Ioo (0 : Real) tau') := by
    have hF : ContinuousOn (iteratedFDeriv Real j U)
        (Ioo (0 : Real) tau') :=
      ContinuousOn.continuousOn_iteratedFDeriv hU isOpen_Ioo
        (by exact_mod_cast le_top)
    have hE :=
      (ContinuousMultilinearMap.piFieldEquiv Real (Fin j)
        (tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p))).symm.continuous
        |>.comp_continuousOn hF
    simpa only [W, iteratedDeriv_eq_equiv_comp, Function.comp_apply] using hE
  have hW : ContinuousOn W (Icc a b) := hWopen.mono hKsub
  let jet : TensorEigenIdx (I := I) (M := M) q 0 0 → Real → Real :=
    fun i t => iteratedDeriv j (fun s => ulim s i) t
  have hjet (i : TensorEigenIdx (I := I) (M := M) q 0 0)
      (t : Real) (ht : t ∈ Icc a b) :
      (W t).coeff i = jet i t := by
    have htO : t ∈ Ioo (0 : Real) tau' := hKsub ht
    let L := tensorHsCoeffL (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (a := (m : Real) + p) i
    have hEq : Set.EqOn (fun z => L (U z)) (fun z => ulim z i)
        (Ioo (0 : Real) tau') := by
      intro z hz
      simpa only [L, U, J, q, tensorHsCoeffL_apply,
        tensorHsInclusion_coeff_apply] using
        galLimExt_coeff hτ.le hlim (m + k)
          ⟨hz.1.le, hz.2.le.trans htau'_tau⟩ i
    have hUt : ContDiffWithinAt Real j U (Ioo (0 : Real) tau') t :=
      (hU t htO).of_le (by exact_mod_cast le_top)
    have hcomm := DifferentialGeometry.Analysis.iteratedDerivWithin_clm_comp
      L hUt (uniqueDiffOn_Ioo (0 : Real) tau') htO
    calc
      (W t).coeff i = L (iteratedDeriv j U t) := by
        simp only [W, L, tensorHsCoeffL_apply]
      _ = L (iteratedDerivWithin j U (Ioo (0 : Real) tau') t) :=
        congrArg L
          (iteratedDerivWithin_of_isOpen (f := U) isOpen_Ioo htO).symm
      _ = iteratedDerivWithin j (fun z => L (U z))
          (Ioo (0 : Real) tau') t := hcomm.symm
      _ = iteratedDerivWithin j (fun z => ulim z i)
          (Ioo (0 : Real) tau') t :=
        iteratedDerivWithin_congr hEq htO
      _ = iteratedDeriv j (fun z => ulim z i) t :=
        iteratedDerivWithin_of_isOpen isOpen_Ioo htO
      _ = jet i t := rfl
  have hneg : Summable (fun i : TensorEigenIdx (I := I) (M := M) q 0 0 =>
      tensorSobolevWeight (I := I) (M := M) i
        (-(((m : Real) + p) - (m : Real)))) := by
    simpa only [tensorSobolevWeight, sub_self, add_sub_cancel_left,
      neg_inj] using hpsum
  obtain ⟨B, hB, hB_le⟩ :=
    mass_le_of_compact (I := I) (M := M) q hneg isCompact_Icc W hW jet
      (fun t ht i => hjet i t ht)
  refine ⟨B, hB, ?_⟩
  intro i t ht
  simpa only [jet] using hB_le i t ht

/-- On the full compact Galerkin interval, the undifferentiated limiting
coefficients admit a summable spectral majorant at every natural Sobolev
order. -/
theorem galLim_mass0
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∀ m : Nat,
      ∃ B : TensorEigenIdx (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 → Real,
        Summable B ∧
        ∀ i, ∀ t ∈ Icc (0 : Real) tau,
          tensorSobolevWeight (I := I) (M := M) i (m : Real) *
            (ulim t i) ^ 2 ≤ B i := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  obtain ⟨p, _hp, hpsum⟩ := htail
  intro m
  obtain ⟨k : Nat, hk⟩ := exists_nat_gt p
  have hmp : (m : Real) + p ≤ ((m + k : Nat) : Real) := by
    rw [Nat.cast_add]
    nlinarith
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0) hmp
  let W : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => J (galLimExt hτ.le hlim (m + k) t)
  have hW : Continuous W := by
    simpa only [W, Function.comp_apply] using
      J.continuous.comp (galLimExt_cont hτ.le hlim (m + k))
  have hcoeff : ∀ t ∈ Icc (0 : Real) tau, ∀ i,
      (W t).coeff i = ulim t i := by
    intro t ht i
    simpa only [W, J, q, tensorHsInclusion_coeff_apply] using
      galLimExt_coeff hτ.le hlim (m + k) ht i
  have hneg : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) q 0 0 =>
        tensorSobolevWeight (I := I) (M := M) i
          (-(((m : Real) + p) - (m : Real)))) := by
    simpa only [tensorSobolevWeight, sub_self, add_sub_cancel_left,
      neg_inj] using hpsum
  exact mass_le_of_compact (I := I) (M := M) q hneg isCompact_Icc
    W hW.continuousOn (fun i t => ulim t i) hcoeff

/-- Every Galerkin limit slice has one smooth representative realizing all
natural Sobolev orders and its scalar spectral series. -/
theorem galLim_slice_cc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    {t : Real} (ht : t ∈ Icc (0 : Real) tau) :
    ∃ U : SmoothCcTensor (S.family.metric (T : Real)) 0 0,
      (∀ m : Nat,
        ccTensorToHs (I := I) (M := M)
            (S.family.metric (T : Real)) 0 (m : Real) U =
          galLimExt hτ hlim m t) ∧
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i s => ulim s i) t =
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection := by
  classical
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M)
    (S.family.metric (T : Real)) 0 0
  have h0 : 0 ≤ ((0 : Nat) : Real) := by positivity
  let u : TensorL2 0 0 (S.family.metric (T : Real)) :=
    tensorHsToL2 (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0)
      hc h0 (galLimExt hτ hlim 0 t)
  have htail : EigenvalueTailSummable (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 :=
    scalar_eigen_tail (I := I) (M := M) (S.family.metric (T : Real))
  have hmem : ∀ σ : Real, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 σ,
        tensorHsToL2 (I := I) (M := M)
            (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            hc hσ v = u := by
    intro σ hσ
    obtain ⟨m, hm⟩ := exists_nat_ge σ
    let J := tensorHsInclusion (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0) hm
    refine ⟨J (galLimExt hτ hlim m t), ?_⟩
    let b :=
      _root_.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) hc
    apply b.repr.injective
    ext i
    change tensorL2Coeff (I := I) (M := M) hc
        (tensorHsToL2 (I := I) (M := M)
          (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            hc hσ (J (galLimExt hτ hlim m t))) i =
      tensorL2Coeff (I := I) (M := M) hc u i
    rw [tensorHsToL2_tensorL2Coeff, tensorHsInclusion_coeff_apply,
      galLimExt_coeff hτ hlim m ht,
      show tensorL2Coeff (I := I) (M := M) hc u i = ulim t i by
        dsimp only [u]
        rw [tensorHsToL2_tensorL2Coeff]
        exact galLimExt_coeff hτ hlim 0 ht i]
  have hgate : SpectralSmoothRealizesAsSmooth (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 :=
    spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable
      (I := I) (M := M) (S.family.metric (T : Real)) 0 0 htail
  obtain ⟨U, hU⟩ := hgate u hmem
  have hrealize (m : Nat) :
      ccTensorToHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 (m : Real) U =
        galLimExt hτ hlim m t := by
    apply tensorHs.ext
    funext i
    rw [ccTensorToHs_coeff, SmoothCcTensor.toL2_apply, hU]
    dsimp only [u]
    rw [tensorHsToL2_tensorL2Coeff]
    calc
      (galLimExt hτ hlim 0 t).coeff i = ulim t i :=
        galLimExt_coeff hτ hlim 0 ht i
      _ = (galLimExt hτ hlim m t).coeff i :=
        (galLimExt_coeff hτ hlim m ht i).symm
  refine ⟨U, ?_, ?_⟩
  · intro m
    exact hrealize m
  · calc
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i s => ulim s i) t =
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i _ => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 U) i) 0 := by
            funext x
            unfold scalarSpecSum
            apply tsum_congr
            intro i
            have hcoeff : tensorL2Coeff (I := I) (M := M) hc
                (SmoothCcTensor.toL2 U) i = ulim t i := by
              rw [SmoothCcTensor.toL2_apply, hU]
              dsimp only [u]
              rw [tensorHsToL2_tensorL2Coeff]
              exact galLimExt_coeff hτ hlim 0 ht i
            simp only [hcoeff]
      _ = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection := by
        simpa only [hc] using scalarSpec_cc (I := I) (M := M)
          (S.family.metric (T : Real)) U

/-- At backward time zero, the scalar Galerkin limit is the scalar readout of
the prescribed smooth initial tensor. -/
theorem galLim_initial
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i t => ulim t i) 0 =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection := by
  calc
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i t => ulim t i) 0 =
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i _ => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0)
          (SmoothCcTensor.toL2 u0) i) 0 := by
      funext x
      unfold scalarSpecSum
      apply tsum_congr
      intro i
      change ulim 0 i * _ =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0)
          (SmoothCcTensor.toL2 u0) i * _
      rw [hlim.lim_init i]
    _ = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection :=
      scalarSpec_cc (I := I) (M := M) (S.family.metric (T : Real)) u0

/-- At reverse time zero, every fixed directional derivative of the scalar
Galerkin limit converges to the corresponding derivative of the initial data. -/
theorem galLim_d_zero
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hDim : Module.finrank Real E = 3) (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (x : M) (X : TangentSpace I x) :
    Tendsto
      (fun t => extDerivFun (I := I)
        (scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i s => ulim s i) t) x X)
      (𝓝[Set.Icc (0 : Real) tau] 0)
      (𝓝 (extDerivFun (I := I)
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection) x X)) := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let f : Real → M → Real := fun t =>
    scalarSpecSum (I := I) (M := M) q (fun i s => ulim s i) t
  let f0 : Real := extDerivFun (I := I)
    (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection) x X
  let N : Real → Real := fun t =>
    ‖galLimExt hτ hlim 3 t - galLimExt hτ hlim 3 0‖
  obtain ⟨C, hC, hgrad⟩ :=
    hs3_grad_low2 (I := I) (M := M) hDim q 0
  have hN : Tendsto N (𝓝[Set.Icc (0 : Real) tau] 0) (𝓝 0) := by
    have hc : Continuous (fun t =>
        ‖galLimExt hτ hlim 3 t - galLimExt hτ hlim 3 0‖) :=
      (galLimExt_cont hτ hlim 3).sub continuous_const |>.norm
    simpa only [N, sub_self, norm_zero] using
      (hc.tendsto 0).mono_left inf_le_left
  have hupper : Tendsto
      (fun t => q.inner x X X * (C * N t) ^ 2)
      (𝓝[Set.Icc (0 : Real) tau] 0) (𝓝 0) := by
    have hCN : Tendsto (fun t => C * N t)
        (𝓝[Set.Icc (0 : Real) tau] 0) (𝓝 0) := by
      simpa only [mul_zero] using hN.const_mul C
    have hQN : Tendsto (fun t => q.inner x X X * (C * N t) ^ 2)
        (𝓝[Set.Icc (0 : Real) tau] 0)
        (𝓝 (q.inner x X X * (0 : Real) ^ 2)) :=
      (hCN.pow 2).const_mul (q.inner x X X)
    convert hQN using 1
    norm_num
  have hsq : Tendsto (fun t => (extDerivFun (I := I) (f t) x X - f0) ^ 2)
      (𝓝[Set.Icc (0 : Real) tau] 0) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) ?_ hupper
    filter_upwards [(@self_mem_nhdsWithin Real inferInstance 0
      (Set.Icc (0 : Real) tau))] with t ht
    obtain ⟨U, hUall, hUscalar⟩ :=
      galLim_slice_cc (I := I) (M := M) hτ hlim ht
    let DU : SmoothCcTensor q 0 0 := U - u0
    have hscalar : extDerivFun (I := I) (f t) x X - f0 =
        extDerivFun (I := I)
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) DU.toSection) x X := by
      have hUsmooth := TensorRSField.scalar0_smooth
        (n := (∞ : WithTop ℕ∞)) U.toSection
      have h0smooth := TensorRSField.scalar0_smooth
        (n := (∞ : WithTop ℕ∞)) u0.toSection
      rw [show f t = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection by
        simpa only [f, q] using hUscalar]
      rw [show f0 = extDerivFun (I := I)
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection) x X by rfl]
      rw [← extDerivFun_sub_at (I := I) X
        (hUsmooth.mdifferentiable (by simp)).mdifferentiableAt
        (h0smooth.mdifferentiable (by simp)).mdifferentiableAt]
      apply congrArg (fun h : M → Real => extDerivFun (I := I) h x X)
      funext y
      simp only [DU, SmoothCcTensor.toSection_sub, TensorRSField.scalar0_sub,
        Pi.sub_apply]
    have hpoint := sq_unit_eval_le (I := I) (M := M) q x
      ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad
        (I := I) (M := M) q 0 0 DU).toSection x) X
    rw [covGrad0_apply (I := I) (M := M) q DU x X] at hpoint
    have hDU : ccTensorToHs (I := I) (M := M) q 0 (3 : Real) DU =
        galLimExt hτ hlim 3 t - galLimExt hτ hlim 3 0 := by
      have hU3 : ccTensorToHs (I := I) (M := M) q 0 (3 : Real) U =
          galLimExt hτ hlim 3 t := by
        simpa only [q] using hUall 3
      have h03 : ccTensorToHs (I := I) (M := M) q 0 (3 : Real) u0 =
          galLimExt hτ hlim 3 0 := by
        simpa only [q] using (galLimExt_zero hτ hlim 3).symm
      dsimp only [DU]
      rw [← ccToHsLin_apply, map_sub, ccToHsLin_apply, ccToHsLin_apply,
        hU3, h03]
    rw [hscalar]
    calc
      (extDerivFun (I := I)
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) DU.toSection) x X) ^ 2
          ≤ q.inner x X X *
              riemannianFiberNormSq (I := I) (M := M) q 0 1 x
                ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad
                  (I := I) (M := M) q 0 0 DU).toSection x) := hpoint
      _ ≤ q.inner x X X *
          (C * ‖ccTensorToHs (I := I) (M := M) q 0 (3 : Real) DU‖) ^ 2 :=
        mul_le_mul_of_nonneg_left ((hgrad DU).1 x)
          (DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
            (I := I) (M := M) q x X)
      _ = q.inner x X X * (C * N t) ^ 2 := by rw [hDU]
  have habs : Tendsto (fun t => |extDerivFun (I := I) (f t) x X - f0|)
      (𝓝[Set.Icc (0 : Real) tau] 0) (𝓝 0) := by
    simpa only [← Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hzero : Tendsto (fun t => extDerivFun (I := I) (f t) x X - f0)
      (𝓝[Set.Icc (0 : Real) tau] 0) (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  simpa only [f, q, f0, sub_add_cancel, zero_add] using hzero.add_const f0

/-- In a genuine chart frame, the spatial derivatives of the scalar Galerkin
limit are jointly continuous at the reverse-time endpoint. -/
theorem galLim_d_joint
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hDim : Module.finrank Real E = 3) (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (a : M) (i : Fin (Module.finrank Real E)) :
    ContinuousWithinAt
      (fun p : Real × M => extDerivFun (I := I)
        (scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun k s => ulim s k) p.1) p.2
        (chartBasisVecFiber (I := I) a i p.2))
      (Set.Icc (0 : Real) tau ×ˢ
        (trivializationAt E (TangentSpace I) a).baseSet)
      ((0 : Real), a) := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let e := trivializationAt E (TangentSpace I) a
  let Xf : (y : M) → TangentSpace I y := fun y =>
    chartBasisVecFiber (I := I) a i y
  let f : Real → M → Real := fun t =>
    scalarSpecSum (I := I) (M := M) q (fun k s => ulim s k) t
  let f0 : M → Real :=
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection
  let base : M → Real := fun y => extDerivFun (I := I) f0 y (Xf y)
  let N : Real → Real := fun t =>
    ‖galLimExt hτ hlim 3 t - galLimExt hτ hlim 3 0‖
  let K : Set (Real × M) := Set.Icc (0 : Real) tau ×ˢ e.baseSet
  have hae : a ∈ e.baseSet := by
    simpa only [e] using
      mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) a
  have hfzero : f 0 = f0 := by
    simpa only [f, f0, q] using galLim_initial (I := I) (M := M) hlim
  obtain ⟨C, hC, hgrad⟩ :=
    hs3_grad_low2 (I := I) (M := M) hDim q 0
  have hN0 : Tendsto N (𝓝 (0 : Real)) (𝓝 0) := by
    have hc : Continuous (fun t =>
        ‖galLimExt hτ hlim 3 t - galLimExt hτ hlim 3 0‖) :=
      (galLimExt_cont hτ hlim 3).sub continuous_const |>.norm
    simpa only [N, sub_self, norm_zero] using hc.tendsto 0
  have hN : Tendsto (fun p : Real × M => N p.1)
      (𝓝[K] ((0 : Real), a)) (𝓝 0) :=
    hN0.comp (continuousAt_fst.mono_left inf_le_left)
  have hgram0 : ContinuousWithinAt
      (fun y : M => q.inner y (Xf y) (Xf y)) e.baseSet a := by
    simpa only [q, Xf, e, chartGramMatrix_apply] using
      (chartGramMatrix_entry_contMDiffOn (I := I) q a i i).continuousOn a hae
  have hmap : Set.MapsTo (fun p : Real × M => p.2) K e.baseSet := by
    intro p hp
    exact hp.2
  have hsndW : Tendsto (fun p : Real × M => p.2)
      (𝓝[K] ((0 : Real), a)) (𝓝[e.baseSet] a) :=
    (show ContinuousWithinAt (fun p : Real × M => p.2) K ((0 : Real), a) from
      continuousWithinAt_snd).tendsto_nhdsWithin hmap
  have hgram : Tendsto
      (fun p : Real × M => q.inner p.2 (Xf p.2) (Xf p.2))
      (𝓝[K] ((0 : Real), a))
      (𝓝 (q.inner a (Xf a) (Xf a))) := by
    simpa only [Function.comp_apply] using hgram0.tendsto.comp hsndW
  have hupper : Tendsto
      (fun p : Real × M =>
        q.inner p.2 (Xf p.2) (Xf p.2) * (C * N p.1) ^ 2)
      (𝓝[K] ((0 : Real), a)) (𝓝 0) := by
    have hCN : Tendsto (fun p : Real × M => C * N p.1)
        (𝓝[K] ((0 : Real), a)) (𝓝 0) := by
      simpa only [mul_zero] using hN.const_mul C
    have hmul := hgram.mul (hCN.pow 2)
    convert hmul using 1
    norm_num
  have hsq : Tendsto
      (fun p : Real × M =>
        (extDerivFun (I := I) (f p.1) p.2 (Xf p.2) - base p.2) ^ 2)
      (𝓝[K] ((0 : Real), a)) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun p => sq_nonneg _) ?_ hupper
    filter_upwards [(@self_mem_nhdsWithin (Real × M) inferInstance
      ((0 : Real), a) K)] with p hp
    obtain ⟨U, hUall, hUscalar⟩ :=
      galLim_slice_cc (I := I) (M := M) hτ hlim hp.1
    let DU : SmoothCcTensor q 0 0 := U - u0
    have hscalar :
        extDerivFun (I := I) (f p.1) p.2 (Xf p.2) - base p.2 =
          extDerivFun (I := I)
            (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) DU.toSection)
            p.2 (Xf p.2) := by
      have hUsmooth := TensorRSField.scalar0_smooth
        (n := (∞ : WithTop ℕ∞)) U.toSection
      have h0smooth := TensorRSField.scalar0_smooth
        (n := (∞ : WithTop ℕ∞)) u0.toSection
      rw [show f p.1 =
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection by
        simpa only [f, q] using hUscalar]
      rw [show base p.2 = extDerivFun (I := I) f0 p.2 (Xf p.2) by rfl]
      rw [← extDerivFun_sub_at (I := I) (Xf p.2)
        (hUsmooth.mdifferentiable (by simp)).mdifferentiableAt
        (h0smooth.mdifferentiable (by simp)).mdifferentiableAt]
      apply congrArg (fun h : M → Real =>
        extDerivFun (I := I) h p.2 (Xf p.2))
      funext y
      simp only [DU, SmoothCcTensor.toSection_sub,
        TensorRSField.scalar0_sub, Pi.sub_apply]
    have hpoint := sq_unit_eval_le (I := I) (M := M) q p.2
      ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad
        (I := I) (M := M) q 0 0 DU).toSection p.2) (Xf p.2)
    rw [covGrad0_apply (I := I) (M := M) q DU p.2 (Xf p.2)] at hpoint
    have hDU : ccTensorToHs (I := I) (M := M) q 0 (3 : Real) DU =
        galLimExt hτ hlim 3 p.1 - galLimExt hτ hlim 3 0 := by
      have hU3 : ccTensorToHs (I := I) (M := M) q 0 (3 : Real) U =
          galLimExt hτ hlim 3 p.1 := by
        simpa only [q] using hUall 3
      have h03 : ccTensorToHs (I := I) (M := M) q 0 (3 : Real) u0 =
          galLimExt hτ hlim 3 0 := by
        simpa only [q] using (galLimExt_zero hτ hlim 3).symm
      dsimp only [DU]
      rw [← ccToHsLin_apply, map_sub, ccToHsLin_apply, ccToHsLin_apply,
        hU3, h03]
    rw [hscalar]
    calc
      (extDerivFun (I := I)
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) DU.toSection)
          p.2 (Xf p.2)) ^ 2
          ≤ q.inner p.2 (Xf p.2) (Xf p.2) *
              riemannianFiberNormSq (I := I) (M := M) q 0 1 p.2
                ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad
                  (I := I) (M := M) q 0 0 DU).toSection p.2) := hpoint
      _ ≤ q.inner p.2 (Xf p.2) (Xf p.2) *
          (C * ‖ccTensorToHs (I := I) (M := M) q 0 (3 : Real) DU‖) ^ 2 :=
        mul_le_mul_of_nonneg_left ((hgrad DU).1 p.2)
          (DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
            (I := I) (M := M) q p.2 (Xf p.2))
      _ = q.inner p.2 (Xf p.2) (Xf p.2) * (C * N p.1) ^ 2 := by
        rw [hDU]
  have herr : Tendsto
      (fun p : Real × M =>
        extDerivFun (I := I) (f p.1) p.2 (Xf p.2) - base p.2)
      (𝓝[K] ((0 : Real), a)) (𝓝 0) := by
    have habs : Tendsto
        (fun p : Real × M =>
          |extDerivFun (I := I) (f p.1) p.2 (Xf p.2) - base p.2|)
        (𝓝[K] ((0 : Real), a)) (𝓝 0) := by
      simpa only [← Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have hX : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun y : M => (⟨y, Xf y⟩ : TotalSpace E (TangentSpace I : M → Type _))) a := by
    have hmem : (trivializationAt E (TangentSpace I) a).baseSet ∈ 𝓝 a :=
      (trivializationAt E (TangentSpace I) a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) a)
    exact (chartBasisVec_contMDiffOn (I := I) a i).contMDiffAt
      hmem
  have hbase0 : ContinuousAt base a := by
    exact (extDerivFun_apply_contMDiffAt_of_section (I := I)
      (TensorRSField.scalar0_smooth
        (n := (∞ : WithTop ℕ∞)) u0.toSection).contMDiffAt hX).continuousAt
  have hbase : Tendsto (fun p : Real × M => base p.2)
      (𝓝[K] ((0 : Real), a)) (𝓝 (base a)) := by
    have hsnd : Tendsto (fun p : Real × M => p.2)
        (𝓝[K] ((0 : Real), a)) (𝓝 a) :=
      (show ContinuousAt (fun p : Real × M => p.2) ((0 : Real), a) from
        continuousAt_snd).mono_left inf_le_left
    simpa only [Function.comp_apply] using hbase0.tendsto.comp hsnd
  have hmain : Tendsto
      (fun p : Real × M => extDerivFun (I := I) (f p.1) p.2 (Xf p.2))
      (𝓝[K] ((0 : Real), a)) (𝓝 (base a)) := by
    simpa only [sub_add_cancel, zero_add] using herr.add hbase
  change Tendsto _ (𝓝[_] ((0 : Real), a)) (𝓝 _)
  simpa only [q, e, Xf, f, f0, base, K, hfzero] using hmain

/-- The moving squared gradient of the scalar Galerkin limit is jointly
continuous at the reverse-time endpoint. -/
theorem galLim_grad_zero
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau sigma : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3) (hτ : 0 ≤ tau)
    (hσ : 0 ≤ sigma) (hστ : sigma ≤ tau)
    (hmap : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Icc (0 : Real) sigma) D.regular)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (a : M) :
    ContinuousWithinAt
      (fun p : Real × M =>
        let g := (reverseFamily (I := I) (M := M)
          (flowG (I := I) S) (T : Real)).metric p.1
        let u := scalarSpecSum (I := I) (M := M)
          (S.family.metric (T : Real)) (fun k s => ulim s k) p.1
        g.inner p.2 (gradientFun (I := I) g u p.2)
          (gradientFun (I := I) g u p.2))
      (Set.Icc (0 : Real) sigma ×ˢ (Set.univ : Set M))
      ((0 : Real), a) := by
  classical
  let G := reverseFamily (I := I) (M := M)
    (flowG (I := I) S) (T : Real)
  let e := trivializationAt E (TangentSpace I) a
  let f : Real → M → Real := fun t =>
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
      (fun k s => ulim s k) t
  let L : Set (Real × M) := Set.Icc (0 : Real) sigma ×ˢ (Set.univ : Set M)
  let O : Set (Real × M) := (Set.univ : Set Real) ×ˢ e.baseSet
  let K : Set (Real × M) := Set.Icc (0 : Real) sigma ×ˢ e.baseSet
  let Gm : Real × M → Matrix (Fin (Module.finrank Real E))
      (Fin (Module.finrank Real E)) Real := fun p =>
    chartGramMatrix (I := I) (G.metric p.1) a p.2
  let dF : Real × M → Fin (Module.finrank Real E) → Real := fun p i =>
    extDerivFun (I := I) (f p.1) p.2
      (chartBasisVecFiber (I := I) a i p.2)
  let rhs : Real × M → Real := fun p =>
    ∑ i, ∑ j, (Gm p)⁻¹ i j * dF p i * dF p j
  have hae : a ∈ e.baseSet := by
    simpa only [e] using
      mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) a
  have hp0 : ((0 : Real), a) ∈ K := by
    exact ⟨⟨le_rfl, hσ⟩, hae⟩
  have hGm : ContinuousWithinAt Gm K ((0 : Real), a) := by
    have hpi : ContinuousWithinAt
        (fun p => (fun i j => Gm p i j :
          Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real))
        K ((0 : Real), a) := by
      rw [continuousWithinAt_pi]
      intro i
      rw [continuousWithinAt_pi]
      intro j
      exact (rev_gram_smooth (I := I) (M := M) hS (T : Real)
        hmap a i j).continuousOn ((0 : Real), a) hp0
    exact hpi
  have hdet : (Gm ((0 : Real), a)).det ≠ 0 := by
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (G.metric 0) a hae)
  have hinvAt : ContinuousAt Inv.inv (Gm ((0 : Real), a)) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hinv : ContinuousWithinAt (fun p => (Gm p)⁻¹) K ((0 : Real), a) :=
    hinvAt.comp_continuousWithinAt hGm
  have hinvEntry (i j : Fin (Module.finrank Real E)) :
      ContinuousWithinAt (fun p => (Gm p)⁻¹ i j) K ((0 : Real), a) := by
    exact (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp hinv i) j)
  have hdF (i : Fin (Module.finrank Real E)) :
      ContinuousWithinAt (fun p => dF p i) K ((0 : Real), a) := by
    have hjoint := galLim_d_joint (I := I) (M := M) hDim hτ hlim a i
    have hsub : Set.Icc (0 : Real) sigma ×ˢ
        (trivializationAt E (TangentSpace I) a).baseSet ⊆
        Set.Icc (0 : Real) tau ×ˢ
          (trivializationAt E (TangentSpace I) a).baseSet := by
      rintro ⟨t, x⟩ htx
      exact ⟨⟨htx.1.1, htx.1.2.trans hστ⟩, htx.2⟩
    simpa only [dF, f, K, e] using hjoint.mono hsub
  have hrhs : ContinuousWithinAt rhs K ((0 : Real), a) := by
    dsimp only [rhs]
    refine tendsto_finset_sum Finset.univ fun i _ =>
      tendsto_finset_sum Finset.univ fun j _ => ?_
    exact ((hinvEntry i j).mul (hdF i)).mul (hdF j)
  have hnorm (p : Real × M) (hp : p ∈ K) :
      (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2)
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2) = rhs p := by
    let df : Tensor0SSpace 1 I p.2 :=
      differential1FormFun (I := I) (f p.1) p.2
    have hsharp :
        cotangentSharp (I := I) (G.metric p.1) p.2 df =
          gradientFun (I := I) (G.metric p.1) (f p.1) p.2 := by
      apply tangentFlatLinear_injective (I := I) (G.metric p.1) p.2
      ext X
      change (G.metric p.1).inner p.2
          (cotangentSharp (I := I) (G.metric p.1) p.2 df) X =
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2) X
      rw [cotangentSharp_inner, cotangentToDual_apply]
      exact differential1FormFun_apply_eq_inner_gradientFun
        (I := I) (G.metric p.1) (f p.1) p.2 X
    have hInv : MetricInverseInBasis (I := I) (G.metric p.1) p.2
        (chartBasisFamily (I := I) a hp.2)
        (fun i j => (Gm p)⁻¹ i j) := by
      intro i j
      have hunit : IsUnit (Gm p).det := isUnit_iff_ne_zero.2
        (ne_of_gt (chartGramMatrix_det_pos (I := I) (G.metric p.1) a hp.2))
      have hGb (i' j' : Fin (Module.finrank Real E)) :
          (G.metric p.1).inner p.2
              (chartBasisFamily (I := I) a hp.2 i')
              (chartBasisFamily (I := I) a hp.2 j') = Gm p i' j' := by
        rw [chartBasisFamily_apply, chartBasisFamily_apply]
        rfl
      constructor
      · have hmul : (∑ k, (Gm p)⁻¹ i k * Gm p k j) =
            ((Gm p)⁻¹ * Gm p) i j := (Matrix.mul_apply).symm
        rw [Finset.sum_congr rfl fun k _ => by rw [hGb k j], hmul,
          Matrix.nonsing_inv_mul (Gm p) hunit, Matrix.one_apply]
      · have hmul : (∑ k, Gm p i k * (Gm p)⁻¹ k j) =
            (Gm p * (Gm p)⁻¹) i j := (Matrix.mul_apply).symm
        rw [Finset.sum_congr rfl fun k _ => by rw [hGb i k], hmul,
          Matrix.mul_nonsing_inv (Gm p) hunit, Matrix.one_apply]
    calc
      (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2)
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2) =
          cotangentInner (I := I) (G.metric p.1) p.2 df df := by
        rw [cotangentInner_eq_sharp, hsharp]
      _ = ∑ i, ∑ j, (Gm p)⁻¹ i j *
          cotangentToDual (I := I) df (chartBasisFamily (I := I) a hp.2 i) *
          cotangentToDual (I := I) df (chartBasisFamily (I := I) a hp.2 j) :=
        cotangentInner_eq_coord (I := I) (G.metric p.1) p.2
          (chartBasisFamily (I := I) a hp.2) (fun i j => (Gm p)⁻¹ i j)
          hInv df df
      _ = rhs p := by
        dsimp only [rhs]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [df, dF, cotangentToDual_apply,
          differential1FormFun_apply_eq_extDerivFun, chartBasisFamily_apply]
  have hlocal : ContinuousWithinAt
      (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2)
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2))
      K ((0 : Real), a) := by
    exact hrhs.congr (fun p hp => hnorm p hp) (hnorm ((0 : Real), a) hp0)
  have hKO : K = L ∩ O := by
    ext p
    simp only [K, L, O, Set.mem_prod, Set.mem_univ, and_true,
      Set.mem_inter_iff]
    tauto
  have hO : O ∈ 𝓝 ((0 : Real), a) := by
    exact (isOpen_univ.prod e.open_baseSet).mem_nhds ⟨Set.mem_univ _, hae⟩
  rw [hKO] at hlocal
  have hglobal := (continuousWithinAt_inter hO).mp hlocal
  simpa only [G, f, L, reverse_metric] using hglobal

/-- The scalar eigen-series of the Galerkin limit is jointly continuous on
the full compact Galerkin interval, including both endpoints. -/
theorem galLim_joint_cont
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ContinuousOn
      (fun q : Real × M =>
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i t => ulim t i) q.1 q.2)
      (Icc (0 : Real) tau ×ˢ (Set.univ : Set M)) := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  have hc : ∀ i : TensorEigenIdx (I := I) (M := M) q 0 0,
      ContDiffOn Real (0 : Nat) (fun t => ulim t i) Set.univ := by
    intro i
    exact contDiffOn_zero.mpr (hlim.lim_cont i).continuousOn
  have hmass : ∀ j : Nat, j ≤ 0 → ∀ m : Nat,
      ∃ B : TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
        Summable B ∧
        ∀ i t, t ∈ Icc (0 : Real) tau →
          tensorSobolevWeight (I := I) (M := M) i (m : Real) *
            (iteratedDeriv j (fun s => ulim s i) t) ^ 2 ≤ B i := by
    intro j hj m
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    obtain ⟨B, hB, hB_le⟩ :=
      galLim_mass0 (I := I) (M := M) hτ hlim m
    refine ⟨B, hB, ?_⟩
    intro i t ht
    simpa only [iteratedDeriv_zero] using hB_le i t ht
  exact (scalar_path_recon (I := I) (M := M) q htail hτ 0
    (fun i t => ulim t i) isOpen_univ (Set.subset_univ _) hc hmass).continuousOn

/-- On one positive interior interval, the scalar eigen-series of the strong
Galerkin limit is jointly smooth to every finite order on compact spacetime
slabs. -/
theorem galLim_joint_smooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ ⦃a b : Real⦄, 0 < a → a < b → b < tau' → ∀ N : Nat,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) (N : Nat)
          (fun q : Real × M =>
            scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
              (fun i t => ulim t i) q.1 q.2)
          (Icc a b ×ˢ (Set.univ : Set M)) := by
  classical
  obtain ⟨tau', htau', htau'_tau, hjet⟩ :=
    galLim_jet_mass (I := I) (M := M) hS hτ hlim
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro a b ha hab hb N
  let a₀ : Real := a / 2
  let b₀ : Real := (b + tau') / 2
  have ha₀ : 0 < a₀ := by
    dsimp only [a₀]
    linarith
  have hab₀ : a₀ ≤ b₀ := by
    dsimp only [a₀, b₀]
    linarith
  have hb₀ : b₀ < tau' := by
    dsimp only [b₀]
    linarith
  obtain ⟨hcoeff, hmass⟩ := hjet ha₀ hab₀ hb₀
  have hinner : Icc a b ⊆ Ioo a₀ b₀ := by
    intro t ht
    constructor <;> dsimp only [a₀, b₀] <;> linarith [ht.1, ht.2]
  refine scalar_path_recon (I := I) (M := M) q htail hab N
    (fun i t => ulim t i) isOpen_Ioo hinner ?_ ?_
  · intro i
    exact ((hcoeff i).mono Ioo_subset_Icc_self).of_le
      (by exact_mod_cast le_top)
  · intro j _hj m
    obtain ⟨B, hB, hB_le⟩ := hmass j m
    refine ⟨B, hB, ?_⟩
    intro i t ht
    exact hB_le i t (Ioo_subset_Icc_self (hinner ht))

/-- The scalar eigen-series of the Galerkin limit is jointly smooth on one
full positive-time interior. -/
theorem galLim_joint_top
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun q : Real × M =>
          scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i t => ulim t i) q.1 q.2)
        (Ioo (0 : Real) tau' ×ˢ (Set.univ : Set M)) := by
  obtain ⟨tau', htau', htau'_tau, hfin⟩ :=
    galLim_joint_smooth (I := I) (M := M) hS hτ hlim
  refine ⟨tau', htau', htau'_tau, ?_⟩
  rw [contMDiffOn_infty]
  intro N p hp
  let a : Real := p.1 / 2
  let b : Real := (p.1 + tau') / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith [hp.1.1]
  have hab : a < b := by
    dsimp only [a, b]
    linarith [hp.1.2]
  have hb : b < tau' := by
    dsimp only [b]
    linarith [hp.1.2]
  have hat : a < p.1 := by
    dsimp only [a]
    linarith [hp.1.1]
  have htb : p.1 < b := by
    dsimp only [b]
    linarith [hp.1.2]
  have hpab : p ∈ Icc a b ×ˢ (Set.univ : Set M) :=
    ⟨⟨hat.le, htb.le⟩, Set.mem_univ _⟩
  have hnhds : Icc a b ×ˢ (Set.univ : Set M) ∈ 𝓝 p :=
    prod_mem_nhds (Icc_mem_nhds hat htb) univ_mem
  exact ((hfin ha hab hb N) p hpab).contMDiffAt hnhds |>.contMDiffWithinAt

/-- On a shorter nontrivial Galerkin interval, the moving squared gradient of
the scalar limit is jointly continuous through reverse time zero. -/
theorem galLim_grad_cont
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ContinuousOn
        (fun p : Real × M =>
          let g := (reverseFamily (I := I) (M := M)
            (flowG (I := I) S) (T : Real)).metric p.1
          let u := scalarSpecSum (I := I) (M := M)
            (S.family.metric (T : Real)) (fun k s => ulim s k) p.1
          g.inner p.2 (gradientFun (I := I) g u p.2)
            (gradientFun (I := I) g u p.2))
        (Set.Icc (0 : Real) tau' ×ˢ (Set.univ : Set M)) := by
  classical
  obtain ⟨tauTop, htauTop, htauTop_le, hjoint⟩ :=
    galLim_joint_top (I := I) (M := M) hS hτ hlim
  let W : Set Real := (fun r : Real => (T : Real) - r) ⁻¹' D.regular
  have hWopen : IsOpen W :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have h0W : (0 : Real) ∈ W := by
    change (T : Real) - 0 ∈ D.regular
    simpa only [sub_zero] using T.2
  obtain ⟨l, w, h0lw, hlw⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWopen.mem_nhds h0W)
  let tauCore : Real := min tauTop (min tau (w / 2))
  have htauCore : 0 < tauCore := by
    dsimp only [tauCore]
    exact lt_min htauTop (lt_min hτ (half_pos h0lw.2))
  have htauCore_top : tauCore ≤ tauTop := by
    exact min_le_left _ _
  have htauCore_tau : tauCore ≤ tau := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmapCore : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Icc (0 : Real) tauCore) D.regular := by
    intro r hr
    apply hlw
    refine ⟨h0lw.1.trans_le hr.1, ?_⟩
    exact lt_of_le_of_lt
      (hr.2.trans ((min_le_right tauTop (min tau (w / 2))).trans
        (min_le_right tau (w / 2))))
      (half_lt_self h0lw.2)
  let tau' : Real := tauCore / 2
  have htau' : 0 < tau' := by
    dsimp only [tau']
    linarith
  have htau'_core : tau' < tauCore := by
    dsimp only [tau']
    linarith
  have htau'_tau : tau' ≤ tau :=
    le_trans htau'_core.le htauCore_tau
  let G := reverseFamily (I := I) (M := M)
    (flowG (I := I) S) (T : Real)
  let f : Real → M → Real := fun t =>
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
      (fun k s => ulim s k) t
  have hmapOpen : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Ioo (0 : Real) tauCore) D.regular := by
    intro r hr
    exact hmapCore ⟨hr.1.le, hr.2.le⟩
  have hpos := gradSq_joint (I := I) G isOpen_Ioo
    (rev_gram_smooth (I := I) (M := M) hS (T : Real) hmapOpen)
    f (by
      simpa only [f] using hjoint.mono (Set.prod_mono
        (Set.Ioo_subset_Ioo le_rfl htauCore_top) Set.Subset.rfl))
  refine ⟨tau', htau', htau'_tau, ?_⟩
  rintro ⟨t, x⟩ htx
  by_cases ht0 : t = 0
  · subst t
    have hzero := galLim_grad_zero (I := I) (M := M)
      hS hDim hτ.le htauCore.le htauCore_tau hmapCore hlim x
    refine hzero.mono ?_
    intro p hp
    exact ⟨⟨hp.1.1, le_trans hp.1.2 htau'_core.le⟩, hp.2⟩
  · have htpos : 0 < t := lt_of_le_of_ne htx.1.1 (Ne.symm ht0)
    have htcore : t < tauCore := lt_of_le_of_lt htx.1.2 htau'_core
    have hopen : (t, x) ∈ Set.Ioo (0 : Real) tauCore ×ˢ
        (Set.univ : Set M) := ⟨⟨htpos, htcore⟩, Set.mem_univ x⟩
    have hnhds : Set.Ioo (0 : Real) tauCore ×ˢ (Set.univ : Set M) ∈
        𝓝 (t, x) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds hopen
    exact ((hpos (t, x) hopen).contMDiffAt hnhds).continuousAt.continuousWithinAt

/-- Every positive-time slice of the jointly smooth Galerkin scalar series is
a smooth scalar function on the manifold. -/
theorem galLim_slice_pos
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ t ∈ Ioo (0 : Real) tau',
        ContMDiff I 𝓘(Real) ∞
          (scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i s => ulim s i) t) := by
  obtain ⟨tau', htau', htau'_tau, htop⟩ :=
    galLim_joint_top (I := I) (M := M) hS hτ hlim
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro t ht
  have harg : ContMDiffOn I (𝓘(Real, Real).prod I) ∞
      (fun x : M => (t, x)) Set.univ :=
    (contMDiffOn_const (c := t)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun x : M => (t, x)) Set.univ
      (Ioo (0 : Real) tau' ×ˢ (Set.univ : Set M)) := by
    intro x _hx
    exact ⟨ht, Set.mem_univ x⟩
  exact contMDiffOn_univ.mp (htop.comp harg hmaps)

/-- On one positive backward-time interval, the scalar Galerkin series solves
the original-time conjugate heat equation pointwise. -/
theorem galLim_pde
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ t ∈ Ioo (0 : Real) tau', ∀ x : M,
        HasDerivAt
          (fun s =>
            scalarSpecSum (I := I) (M := M)
              (S.family.metric (T : Real))
              (fun i r => ulim r i) s x)
          (laplacianAt (I := I) (flowG (I := I) S) ((T : Real) - t)
              (scalarSpecSum (I := I) (M := M)
                (S.family.metric (T : Real))
                (fun i r => ulim r i) t) x +
            (conjCoeff (I := I) (M := M) S ((T : Real) - t) : M → Real) x *
              scalarSpecSum (I := I) (M := M)
                (S.family.metric (T : Real))
                (fun i r => ulim r i) t x) t := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  obtain ⟨tauJ, htauJ, htauJ_tau, hjet⟩ :=
    galLim_jet_mass (I := I) (M := M) hS hτ hlim
  obtain ⟨tauD, htauD, _htauD_one, _hreg, hcore⟩ :=
    lapDiffHs_core (I := I) (M := M) S.family hS.smoothMetric T
  obtain ⟨tauV, htauV, _htauV_tau, hlift⟩ :=
    galLimVel_lift (I := I) (M := M) hS hτ hlim
  obtain ⟨w, _hwcont, hw0, hwcan⟩ := hlift 0
  let tau' : Real := min tauJ (min tauD tauV)
  have htau' : 0 < tau' := by
    dsimp only [tau']
    exact lt_min htauJ (lt_min htauD htauV)
  have htau'_J : tau' ≤ tauJ := by
    dsimp only [tau']
    exact min_le_left _ _
  have htau'_D : tau' ≤ tauD := by
    dsimp only [tau']
    exact (min_le_right _ _).trans (min_le_left _ _)
  have htau'_V : tau' ≤ tauV := by
    dsimp only [tau']
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨tau', htau', htau'_J.trans htauJ_tau, ?_⟩
  intro t ht x
  have htJ : t < tauJ := ht.2.trans_le htau'_J
  have htDlt : t < tauD := ht.2.trans_le htau'_D
  have htVlt : t < tauV := ht.2.trans_le htau'_V
  have htTauOpen : t ∈ Ioo (0 : Real) tau :=
    ⟨ht.1, htJ.trans_le htauJ_tau⟩
  have htTau : t ∈ Icc (0 : Real) tau :=
    ⟨htTauOpen.1.le, htTauOpen.2.le⟩
  have htD : t ∈ Icc (0 : Real) tauD := ⟨ht.1.le, htDlt.le⟩
  have htV : t ∈ Icc (0 : Real) tauV := ⟨ht.1.le, htVlt.le⟩
  obtain ⟨U, hUall, hscalar⟩ :=
    galLim_slice_cc (I := I) (M := M) hτ.le hlim htTau
  let f : M → Real :=
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := by
    exact TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) U.toSection
  have hscalar' :
      scalarSpecSum (I := I) (M := M) q
          (fun i s => ulim s i) t = f := by
    simpa only [q, f] using hscalar
  let h : SmoothRiemannianMetric I M := S.family.metric ((T : Real) - t)
  let zeta : C^∞⟮I, M; Real⟯ :=
    conjCoeff (I := I) (M := M) S ((T : Real) - t)
  let W : SmoothCcTensor q 0 0 :=
    rawTensorConnLapSmooth (I := I) q 0 0 U +
      scalarLapDiffCc (I := I) q h U +
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
          (I := I) (M := M) q 0 0 zeta U
  let U3 : tensorHs (I := I) (M := M) q 0 0
      (((1 : Nat) : Real) + 2) :=
    ccTensorToHs (I := I) (M := M) q 0 (((1 : Nat) : Real) + 2) U
  let U1 : tensorHs (I := I) (M := M) q 0 0 ((1 : Nat) : Real) :=
    ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) U
  let Ubar : tensorHs (I := I) (M := M) q 0 0
      (((1 : Nat) : Real) + 2) :=
    tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((1 + 2 : Nat) : Real) = ((1 : Nat) : Real) + 2)
      (galLimExt hτ.le hlim (1 + 2) t)
  let U1bar : tensorHs (I := I) (M := M) q 0 0 ((1 : Nat) : Real) :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((1 : Nat) : Real) ≤ ((1 : Nat) : Real) + 2) Ubar
  have hUbar : Ubar = U3 := by
    apply tensorHs.ext
    funext i
    simp only [Ubar, tensorHs.castEquiv_coeff]
    have hi := congrArg
      (fun v : tensorHs (I := I) (M := M) q 0 0
          (((1 + 2 : Nat) : Real)) => v.coeff i)
      (hUall (1 + 2))
    simpa only [U3, q, ccTensorToHs_coeff] using hi.symm
  have hU1bar : U1bar = U1 := by
    apply tensorHs.ext
    funext i
    simp only [U1bar, tensorHsInclusion_coeff_apply]
    rw [hUbar]
    simp only [U3, U1, ccTensorToHs_coeff]
  have hlapCore :
      tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) U3 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (rawTensorConnLapSmooth (I := I) q 0 0 U) := by
    simpa only [U3] using
      scalarLapHs_core (I := I) (M := M) q ((1 : Nat) : Real) U
  have hdiffCore :
      lapDiffHs (I := I) (M := M) q h 1 U3 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (scalarLapDiffCc (I := I) q h U) := by
    simpa only [q, h, U3] using hcore (1 : Nat) t htD U
  have hpotCore :
      scalarPotHs (I := I) (M := M) q zeta 1 U1 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
            (I := I) (M := M) q 0 0 zeta U) := by
    simpa only [U1] using
      scalarPotHs_core (I := I) (M := M) q zeta 1 U
  have hvelExpand :
      galLimVelHs hτ.le hlim 1 t =
        tensorScaleLaplacian (I := I) (M := M)
            (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) Ubar +
          lapDiffHs (I := I) (M := M) q h 1 Ubar +
          scalarPotHs (I := I) (M := M) q zeta 1 U1bar := by
    rfl
  have hW1 :
      ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) W =
        galLimVelHs hτ.le hlim 1 t := by
    calc
      _ = ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (rawTensorConnLapSmooth (I := I) q 0 0 U) +
            ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (scalarLapDiffCc (I := I) q h U) +
            ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
                (I := I) (M := M) q 0 0 zeta U) := by
              simp only [W, ccTensorToHs_add]
      _ = tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) U3 +
            lapDiffHs (I := I) (M := M) q h 1 U3 +
            scalarPotHs (I := I) (M := M) q zeta 1 U1 := by
              rw [← hlapCore, ← hdiffCore, ← hpotCore]
      _ = _ := by
        rw [← hUbar, ← hU1bar]
        exact hvelExpand.symm
  let J10 := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : ((0 : Nat) : Real) ≤ ((1 : Nat) : Real))
  have hcan :
      J10 (ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) W) =
        galLimVelCan hτ.le hlim 0 t := by
    have hz := congrArg J10 hW1
    simpa only [J10, galLimVelCan, q] using hz
  let tt : Icc (0 : Real) tauV := ⟨t, htV⟩
  have hWcoeff (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 W) i =
        (galLimVel hτ.le hlim t).coeff i := by
    have h1 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 ((0 : Nat) : Real) =>
        z.coeff i) hcan
    have h2 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 ((0 : Nat) : Real) =>
        z.coeff i) (hwcan tt)
    have h3 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 (0 : Real) =>
        z.coeff i) (hw0 tt)
    calc
      _ = (ccTensorToHs (I := I) (M := M) q 0
          ((1 : Nat) : Real) W).coeff i := by
        simpa only [hc] using
          (ccTensorToHs_coeff (I := I) (M := M) q 0
            ((1 : Nat) : Real) W i).symm
      _ = (galLimVelCan hτ.le hlim 0 t).coeff i := by
        simpa only [J10, tensorHsInclusion_coeff_apply] using h1
      _ = (w tt).coeff i := by
        simpa only [tt] using h2.symm
      _ = (galLimVel hτ.le hlim t).coeff i := by
        simpa only [tt, tensorHsInclusion_coeff_apply] using h3
  let a : Real := t / 2
  let b : Real := (t + tauJ) / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith [ht.1]
  have hab : a < b := by
    dsimp only [a, b]
    linarith [htJ]
  have hb : b < tauJ := by
    dsimp only [b]
    linarith [htJ]
  obtain ⟨_hcoeff, hmass⟩ := hjet ha hab.le hb
  have hIcc : Icc a b ⊆ Ioo (0 : Real) tau := by
    intro s hs
    constructor
    · exact ha.trans_le hs.1
    · exact hs.2.trans_lt (hb.trans_le htauJ_tau)
  have htIcc : t ∈ Icc a b := by
    constructor <;> dsimp only [a, b] <;> linarith [ht.1, htJ]
  have hat : a < t := by
    dsimp only [a]
    linarith [ht.1]
  have htb : t < b := by
    dsimp only [b]
    linarith [htJ]
  have hmass1 : ∀ j : Nat, j ≤ 1 → ∀ m : Nat,
      ∃ B : TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
        Summable B ∧
        ∀ i s, s ∈ Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : Real) *
            (iteratedDeriv j (fun r => ulim r i) s) ^ 2 ≤ B i := by
    intro j _hj m
    simpa only [q] using hmass j m
  have hderiv :
      HasDerivAt
        (fun s => scalarSpecSum (I := I) (M := M) q
          (fun i r => ulim r i) s x)
        (scalarSpecSum (I := I) (M := M) q
          (fun i s => deriv (fun r => ulim r i) s) t x) t := by
    exact (scalarSpec_d1 (I := I) (M := M) q htail hab
      (fun i r => ulim r i) isOpen_Ioo hIcc
      (fun i => galLim_mode_c1 hτ hlim i) hmass1 x htIcc).hasDerivAt
        (Icc_mem_nhds hat htb)
  have hderivSeries :
      scalarSpecSum (I := I) (M := M) q
          (fun i s => deriv (fun r => ulim r i) s) t x =
        scalarSpecSum (I := I) (M := M) q
          (fun i _ => (galLimVel hτ.le hlim t).coeff i) t x := by
    unfold scalarSpecSum
    apply tsum_congr
    intro i
    change deriv (fun r => ulim r i) t * _ =
      (galLimVel hτ.le hlim t).coeff i * _
    rw [(galLim_mode_deriv hτ hlim htTauOpen i).deriv]
  have hseriesW :
      scalarSpecSum (I := I) (M := M) q
          (fun i _ => (galLimVel hτ.le hlim t).coeff i) t x =
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x := by
    calc
      _ = scalarSpecSum (I := I) (M := M) q
          (fun i _ => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 W) i) 0 x := by
              unfold scalarSpecSum
              apply tsum_congr
              intro i
              change (galLimVel hτ.le hlim t).coeff i * _ =
                tensorL2Coeff (I := I) (M := M) hc
                  (SmoothCcTensor.toL2 W) i * _
              rw [hWcoeff i]
      _ = _ := congrFun (scalarSpec_cc (I := I) (M := M) q W) x
  have htime :
      HasDerivAt
        (fun s => scalarSpecSum (I := I) (M := M) q
          (fun i r => ulim r i) s x)
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x) t :=
    hderiv.congr_deriv (hderivSeries.trans hseriesW)
  have hWscalar :
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x =
        Δ_g (I := I) h hf x + (zeta : M → Real) x * f x := by
    simp only [W, SmoothCcTensor.toSection_add, TensorRSField.scalar0_add,
      Pi.add_apply, rawLap_cc_scalar (I := I) (M := M) q U x,
      scalarLapDiff_eq (I := I) (M := M) q h U x,
      DifferentialGeometry.Integral.Connection.scalar0_smul_cc
        (I := I) (M := M) q zeta U x, f]
    ring
  have hlap :
      laplacianAt (I := I) (flowG (I := I) S) ((T : Real) - t) f x =
        Δ_g (I := I) h hf x := by
    simpa only [h] using
      (laplacianAt_eq_delta (I := I) (M := M)
        (flowG (I := I) S) ((T : Real) - t) hf (by rfl) x)
  refine htime.congr_deriv ?_
  rw [hscalar']
  rw [hlap]
  simpa only [zeta] using hWscalar

/-- The strong Galerkin limit yields a genuine classical heat potential for
the reversed Ricci-flow family on a nontrivial closed time interval. -/
theorem heatpot_of_gallim
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ tau ∧
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (RealTimeInterval.closed 0 tau' htau'.le)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
        (fun s x =>
          (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
        (fun s x =>
          scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i r => ulim r i) s x) := by
  obtain ⟨tauP, htauP, htauP_tau, hpde⟩ :=
    galLim_pde (I := I) (M := M) hS hτ hlim
  obtain ⟨tauS, htauS, _htauS_tau, hsmooth⟩ :=
    galLim_joint_top (I := I) (M := M) hS hτ hlim
  obtain ⟨tauL, htauL, _htauL_tau, hslice⟩ :=
    galLim_slice_pos (I := I) (M := M) hS hτ hlim
  have hcont := galLim_joint_cont (I := I) (M := M) hτ hlim
  let rho : Real := min tauP (min tauS tauL)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min htauP (lt_min htauS htauL)
  have hrhoP : rho ≤ tauP := by
    dsimp only [rho]
    exact min_le_left _ _
  have hrhoS : rho ≤ tauS := by
    dsimp only [rho]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrhoL : rho ≤ tauL := by
    dsimp only [rho]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let tau' : Real := rho / 2
  have htau' : 0 < tau' := by
    dsimp only [tau']
    positivity
  have htau'P : tau' < tauP := by
    dsimp only [tau']
    exact (half_lt_self hrho).trans_le hrhoP
  have htau'S : tau' < tauS := by
    dsimp only [tau']
    exact (half_lt_self hrho).trans_le hrhoS
  have htau'L : tau' < tauL := by
    dsimp only [tau']
    exact (half_lt_self hrho).trans_le hrhoL
  have htau'_tau : tau' ≤ tau :=
    (htau'P.trans_le htauP_tau).le
  refine ⟨tau', htau', htau'_tau, ?_⟩
  refine
    { jointSmooth := ?_
      jointCont := ?_
      sliceSmooth := ?_
      equation := ?_ }
  · exact hsmooth.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨⟨hs.1, hs.2.trans htau'S⟩, hx⟩)
  · exact hcont.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨⟨hs.1, hs.2.trans htau'_tau⟩, hx⟩)
  · intro s hs
    change s ∈ Icc (0 : Real) tau' at hs
    by_cases hs0 : s = 0
    · subst s
      rw [galLim_initial (I := I) (M := M) hlim]
      exact TensorRSField.scalar0_smooth
        (n := (∞ : WithTop ℕ∞)) u0.toSection
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      exact hslice s ⟨hspos, hs.2.trans_lt htau'L⟩
  · intro s hs x
    change s ∈ Ioo (0 : Real) tau' at hs
    have hsP : s ∈ Ioo (0 : Real) tauP :=
      ⟨hs.1, hs.2.trans htau'P⟩
    simpa only [reverseFamily] using hpde s hsP x

/-- Every smooth scalar initial tensor generates a classical heat potential on
a nontrivial reversed-time interval, with its prescribed scalar initial
trace. -/
theorem heatpot_exists
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
          (fun s x =>
            (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
          u ∧
        u 0 = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection := by
  obtain ⟨tau, htau, htau_one, hsubseq⟩ :=
    scalar_gal_subseq (I := I) (M := M) S hS T
  obtain ⟨V, phi, ulim, hlim⟩ := hsubseq u0
  obtain ⟨tau', htau', htau'_tau, hpot⟩ :=
    heatpot_of_gallim (I := I) (M := M) hS htau hlim
  let u : Real → M → Real := fun s x =>
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
      (fun i r => ulim r i) s x
  refine ⟨tau', htau', htau'_tau.trans htau_one, u, ?_, ?_⟩
  · simpa only [u] using hpot
  · simpa only [u] using galLim_initial (I := I) (M := M) hlim

/-- Every smooth terminal scalar tensor generates a classical solution of the
conjugate heat equation on a nontrivial reversed-time interval, with the
prescribed terminal trace. -/
theorem conj_heat_exists
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        IsConjHeatOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (flowG (I := I) S) S.scalar u (T : Real) ∧
        u (T : Real) =
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection := by
  obtain ⟨tau', htau', htau'_one, v, hv, hv0⟩ :=
    heatpot_exists (I := I) (M := M) S hS T u0
  have hv' :
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (RealTimeInterval.closed 0 tau' htau'.le)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
        (fun s x => -S.scalar ((T : Real) - s) x) v := by
    simpa only [conjCoeff_apply] using hv
  let u : Real → M → Real := reverseHeat (T : Real) v
  refine ⟨tau', htau', htau'_one, u, ?_, ?_⟩
  · simpa only [u] using
      conj_heat_of_pot (I := I) (M := M)
        (RealTimeInterval.closed 0 tau' htau'.le)
        (flowG (I := I) S) S.scalar v (T : Real) hv'
  · change v ((T : Real) - (T : Real)) =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection
    simpa only [sub_self] using hv0

/-- A nonnegative smooth scalar initial tensor generates a nonnegative
classical heat potential on a nontrivial reversed-time interval. -/
theorem gallim_nonneg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0)
    (hinit : ∀ x : M,
      0 ≤ TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection x) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
          (fun s x =>
            (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
          u ∧
        u 0 = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection ∧
        ∀ s ∈ Set.Icc (0 : Real) tau', ∀ x : M, 0 ≤ u s x := by
  obtain ⟨tauH, htauH, htauH_one, u, hu, hu0⟩ :=
    heatpot_exists (I := I) (M := M) S hS T u0
  obtain ⟨tauC, htauC, _htauC_one, C, _hCnonneg, hC⟩ :=
    conjCoeff_bound (I := I) (M := M) S hS T
  let tau' : Real := min tauH tauC
  have htau' : 0 < tau' := by
    simpa only [tau'] using lt_min htauH htauC
  have htau'_H : tau' ≤ tauH := min_le_left _ _
  have htau'_C : tau' ≤ tauC := min_le_right _ _
  have htau'_one : tau' ≤ 1 := htau'_H.trans htauH_one
  have hcarrier :
      (RealTimeInterval.closed 0 tau' htau'.le).carrier ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).carrier := by
    change Set.Icc (0 : Real) tau' ⊆ Set.Icc (0 : Real) tauH
    exact Set.Icc_subset_Icc le_rfl htau'_H
  have hregular :
      (RealTimeInterval.closed 0 tau' htau'.le).regular ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).regular := by
    change Set.Ioo (0 : Real) tau' ⊆ Set.Ioo (0 : Real) tauH
    intro s hs
    exact ⟨hs.1, hs.2.trans_le htau'_H⟩
  have hu' := hu.mono hcarrier hregular
  have hV : ∀ s : Real, s ∈ Set.Icc (0 : Real) tau' → ∀ x : M,
      (conjCoeff (I := I) (M := M) S
        ((T : Real) - s) : M → Real) x ≤ C := by
    intro s hs x
    exact (le_abs_self _).trans
      (hC s ⟨hs.1, hs.2.trans htau'_C⟩ x)
  have huinit : ∀ x : M, 0 ≤ u 0 x := by
    intro x
    rw [hu0]
    exact hinit x
  have hnonneg :=
    DifferentialGeometry.Analysis.Parabolic.heat_pot_nonneg
      (I := I) (M := M)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      htau'.le
      (fun s x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
      u hu' C hV huinit
  exact ⟨tau', htau', htau'_one, u, hu', hu0, hnonneg⟩

/-- A strictly positive smooth scalar initial tensor generates a strictly
positive classical heat potential on a nontrivial reversed-time interval. -/
theorem gallim_pos
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0)
    (hinit : ∀ x : M,
      0 < TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection x) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
          (fun s x =>
            (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
          u ∧
        u 0 = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection ∧
        ∀ s ∈ Set.Icc (0 : Real) tau', ∀ x : M, 0 < u s x := by
  obtain ⟨tauH, htauH, htauH_one, u, hu, hu0⟩ :=
    heatpot_exists (I := I) (M := M) S hS T u0
  obtain ⟨tauC, htauC, _htauC_one, C, _hCnonneg, hC⟩ :=
    conjCoeff_bound (I := I) (M := M) S hS T
  let tau' : Real := min tauH tauC
  have htau' : 0 < tau' := by
    simpa only [tau'] using lt_min htauH htauC
  have htau'_H : tau' ≤ tauH := min_le_left _ _
  have htau'_C : tau' ≤ tauC := min_le_right _ _
  have htau'_one : tau' ≤ 1 := htau'_H.trans htauH_one
  have hcarrier :
      (RealTimeInterval.closed 0 tau' htau'.le).carrier ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).carrier := by
    change Set.Icc (0 : Real) tau' ⊆ Set.Icc (0 : Real) tauH
    exact Set.Icc_subset_Icc le_rfl htau'_H
  have hregular :
      (RealTimeInterval.closed 0 tau' htau'.le).regular ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).regular := by
    change Set.Ioo (0 : Real) tau' ⊆ Set.Ioo (0 : Real) tauH
    intro s hs
    exact ⟨hs.1, hs.2.trans_le htau'_H⟩
  have hu' := hu.mono hcarrier hregular
  have hV : ∀ s : Real, s ∈ Set.Icc (0 : Real) tau' → ∀ x : M,
      |(conjCoeff (I := I) (M := M) S
        ((T : Real) - s) : M → Real) x| ≤ C := by
    intro s hs x
    exact hC s ⟨hs.1, hs.2.trans htau'_C⟩ x
  have huinit : ∀ x : M, 0 < u 0 x := by
    intro x
    rw [hu0]
    exact hinit x
  have hpos :=
    DifferentialGeometry.Analysis.Parabolic.heat_pot_pos
      (I := I) (M := M)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      htau'.le
      (fun s x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
      u hu' C hV huinit
  exact ⟨tau', htau', htau'_one, u, hu', hu0, hpos⟩

/-- Unless the manifold is empty, there is a positive reversed heat potential of unit mass. -/
theorem gallim_unit_pos
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    IsEmpty M ∨
      ∃ tau : Real, ∃ htau : 0 < tau, tau ≤ 1 ∧
        ∃ u : Real → M → Real,
          DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
            (RealTimeInterval.closed 0 tau htau.le)
            (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
            (fun s x =>
              (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
            u ∧
          (∀ s ∈ Set.Icc (0 : Real) tau, ∀ x : M, 0 < u s x) ∧
          ∀ s ∈ Set.Icc (0 : Real) tau,
            (∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M)
              (reverseFamily (I := I) (M := M)
                (flowG (I := I) S) (T : Real)) s)) = 1 := by
  rcases unit_init_or_empty (I := I) (M := M)
      (S.family.metric (T : Real)) with hM | ⟨u0, hinit, hunit⟩
  · exact Or.inl hM
  · right
    obtain ⟨tau, htau, htau_one, u, hu, hu0, hpos⟩ :=
      gallim_pos (I := I) (M := M) S hS T u0 hinit
    obtain ⟨tau', htau', htau'_tau, hu', hmass⟩ :=
      heatpot_mass_eq (I := I) (M := M) S hS T htau hu
    refine ⟨tau', htau', htau'_tau.trans htau_one, u, hu', ?_, ?_⟩
    · intro s hs x
      exact hpos s ⟨hs.1, hs.2.trans htau'_tau⟩ x
    · have hmass0 :
          (∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
            (reverseFamily (I := I) (M := M)
              (flowG (I := I) S) (T : Real)) 0)) = 1 := by
        rw [hu0]
        simpa only [volumeMeasureFamily, metricFamilyForMeasure,
          riemannianMeasureFamily, reverseFamily, flowG, sub_zero] using hunit
      intro s hs
      exact (hmass s hs).trans hmass0

end DifferentialGeometry.PDE.RicciFlow.Entropy
