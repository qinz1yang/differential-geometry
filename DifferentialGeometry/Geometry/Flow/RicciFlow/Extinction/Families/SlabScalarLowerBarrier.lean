import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparisonRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SurgeryWidthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open Set Filter
open Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open scoped Topology ENNReal Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.CheegerGromovCompactness
    (metricDerivNorm metricCovDerivNorm covNorm_le_add covNorm_self_succ
      metricQuadFormDiff_le_metricDerivNorm)

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem ricciNorm_ge_scalar_sq_div_finrank [NeZero (Module.finrank ℝ E)]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    (1 / (Module.finrank ℝ E : ℝ)) * S.scalar t x ^ 2 ≤
      ricciNorm (I := I) S t x := by
  classical
  let : Nonempty (CoordinateIdx (𝕜 := ℝ) E) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv := fun k l => inverseMetricFlatModelInChartComponent
    (I := I) (S.family.metric t) x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) (S.family.metric t) x basis gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) (S.family.metric t) x
  have h := metricTracePair0SAt_sq_div_rank_le_normSq0S
    (I := I) (S.family.metric t) basis gInv hinv (S.ricci t x)
  rw [SolutionOn.scalar_eq_metricTrace]
  simpa only [CoordinateIdx, Fintype.card_fin, SolutionOn.family_metric, SolutionOn.ricci,
    SolutionFamily.ricci_apply, SolutionOn.ricciAt, ricciNorm] using h

omit [SigmaCompactSpace M] in
theorem scalarEvolutionEquationOn_of_isSolutionOn
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ScalarEvolutionEquationOn (D := D) S.scalar
      (fun t x => laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x)
      (ricciNorm (I := I) S) :=
  scalar_evolution_of_smooth_solution (I := I) (M := M) S
    (smoothOfSolution (I := I) S hS) (flowG (I := I) S) (fun _ => rfl) (fun _ => rfl)

omit [SigmaCompactSpace M] in
theorem scalarRegularity_of_isSolutionOn
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (T n c0 : ℝ) (K : NNReal)
    (hsubset : ∀ t : ℝ, t ∈ Set.Icc 0 T → t ∈ D.carrier)
    (hmetric : ∀ t : ℝ, t ∈ Set.Icc 0 T → G.metric t = S.family.metric t)
    (hden : ∀ t : ℝ, t ∈ Set.Icc 0 T → 1 - (2 / n) * c0 * t ≠ 0) :
    ScalarLowerBoundWeakMaximumPrincipleRegularity (I := I) G T n c0 S.scalar K :=
  scalarRegularityOfSmooth (I := I) (M := M) S (smoothOfSolution (I := I) S hS) G T n c0 K
    hsubset hmetric hden

end

theorem scalarLowerBarrier_neg {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    -3 / (2 * (t + c)) < 0 := by
  have hpos : 0 < 2 * (t + c) := by linarith
  exact div_neg_of_neg_of_pos (by norm_num) hpos

theorem scalarLowerBarrier_le_on_slab
    {P : OrientedThreeStage.{u}} {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {a s c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hS : IsSolutionOn (I := ThreeModel) (M := P.Carrier) S)
    (hcarrier : Set.Ico a s ⊆ D.carrier) (hregD : Set.Ioo a s ⊆ D.regular)
    (hinit : ∀ x : P.Carrier, -3 / (2 * (a + c)) ≤ metricScalarAt (S.base.metric a) x)
    {t : ℝ} (ht : t ∈ Set.Ico a s) (x : P.Carrier) :
    -3 / (2 * (t + c)) ≤ metricScalarAt (S.base.metric t) x := by
  rcases eq_or_lt_of_le ht.1 with hta | hat
  · rw [← hta]; exact hinit x
  · have hpos : 0 < a + c := by linarith [ha, hc]
    let c0 : ℝ := -3 / (2 * (a + c))
    let S' : SolutionOn (I := ThreeModel) (M := P.Carrier) (D.timeShift a) := S.timeShift a
    have hS' : IsSolutionOn (I := ThreeModel) (M := P.Carrier) S' :=
      isSolutionOn_timeShift hS a
    have hTpos : 0 < t - a := by linarith
    have hslab : Set.Icc 0 (t - a) ⊆ (D.timeShift a).carrier := by
      intro u hu
      exact hcarrier ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩
    have hregular : ∀ u : ℝ, u ∈ Set.Icc 0 (t - a) → 0 < u →
        u ∈ (D.timeShift a).regular := by
      intro u hu hu0
      exact hregD ⟨by linarith, by linarith [hu.2, ht.2]⟩
    have hden : ∀ u : ℝ, u ∈ Set.Icc 0 (t - a) → 0 < 1 - (2 / 3 : ℝ) * c0 * u := by
      intro u hu
      have h1 : (2 / 3 : ℝ) * c0 = -(1 / (a + c)) := by
        have h1def : c0 = -3 / (2 * (a + c)) := rfl
        rw [h1def]
        field_simp
      rw [h1]
      have h2 : 1 - -(1 / (a + c)) * u = 1 + u / (a + c) := by ring
      rw [h2]
      have : 0 ≤ u / (a + c) := div_nonneg hu.1 hpos.le
      linarith
    have hcont_scalar : ContinuousOn (fun p : ℝ × P.Carrier => S'.scalar p.1 p.2)
        (spacetimeSlab (M := P.Carrier) (t - a)) :=
      hS'.scalarCont.mono (Set.prod_mono hslab Set.Subset.rfl)
    have hcont_barrier : ContinuousOn (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)
        (Set.Icc 0 (t - a)) := by
      have hden_cont : ContinuousOn (fun u : ℝ => 1 - (2 / 3 : ℝ) * c0 * u)
          (Set.Icc 0 (t - a)) := by fun_prop
      have hne : ∀ u ∈ Set.Icc 0 (t - a), 1 - (2 / 3 : ℝ) * c0 * u ≠ 0 :=
        fun u hu => ne_of_gt (hden u hu)
      unfold DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier
      exact (continuousOn_const (c := c0)).div hden_cont hne
    obtain ⟨K, hK⟩ := exists_scalarLowerReaction_lipschitzOn_valueSet 3 (t - a) S'.scalar
      (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)
      (scalarWeakMaximumPrincipleValueSet_isCompact (M := P.Carrier) (t - a) S'.scalar
        (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0) hcont_scalar hcont_barrier)
    have hreg : ScalarLowerBoundWeakMaximumPrincipleRegularity (I := ThreeModel) (flowG S')
        (t - a) 3 c0 S'.scalar K :=
      scalarRegularity_of_isSolutionOn (D := D.timeShift a) S' hS' (flowG S') (t - a) 3 c0 K
        hslab (fun _ _ => rfl) (fun u hu => ne_of_gt (hden u hu))
    have hevol : ScalarEvolutionEquationOn (D := D.timeShift a) S'.scalar
        (fun u y => laplacianAt (I := ThreeModel) (flowG S') u (S'.scalar u) y)
        (ricciNorm (I := ThreeModel) S') :=
      scalarEvolutionEquationOn_of_isSolutionOn (D := D.timeShift a) S' hS'
    have hlap : ScalarLaplacianRealizesHeatOperatorOn (I := ThreeModel) (flowG S') (t - a)
        S'.scalar
        (fun u y => laplacianAt (I := ThreeModel) (flowG S') u (S'.scalar u) y) :=
      ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt (fun _ _ _ => rfl)
    have hricci : ∀ u : ℝ, u ∈ Set.Icc 0 (t - a) → ∀ y : P.Carrier,
        (1 / 3 : ℝ) * (S'.scalar u y) ^ 2 ≤ ricciNorm (I := ThreeModel) S' u y := by
      intro u _ y
      have hfr : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
      have h := ricciNorm_ge_scalar_sq_div_finrank (D := D.timeShift a) S' u y
      simpa [hfr] using h
    have hinit' : InitialScalarLowerBound (M := P.Carrier) S'.scalar c0 := by
      intro y
      have h0 : S'.scalar 0 y = metricScalarAt (S.base.metric a) y := by
        change metricScalarAt (S.base.metric (0 + a)) y = metricScalarAt (S.base.metric a) y
        rw [zero_add]
      rw [h0]
      exact hinit y
    have hF_lip : ∀ u : ℝ, u ∈ Set.Icc 0 (t - a) →
        LipschitzOnWith K (fun b : ℝ => scalarLowerReaction 3 b)
          (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet
            (M := P.Carrier) (t - a) S'.scalar
            (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) :=
      fun u hu => hK u hu
    have hmain := scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
      (I := ThreeModel) (M := P.Carrier) (D := D.timeShift a) (flowG S')
      (t - a) 3 c0 hTpos (by norm_num : (3 : ℝ) ≠ 0)
      S'.scalar
      (fun u y => laplacianAt (I := ThreeModel) (flowG S') u (S'.scalar u) y)
      (ricciNorm (I := ThreeModel) S') K
      hslab hregular hden hreg hevol hlap hricci hinit' hF_lip
    have hb := hmain (t - a) ⟨by linarith, le_rfl⟩ x
    have hbar : DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0 (t - a) =
        -3 / (2 * (t + c)) := by
      have h := DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scalarLowerBarrier_three_neg_inv
        (c := a + c) (t := t - a) hpos.ne' (by linarith)
      have harg : t - a + (a + c) = t + c := by ring
      rw [harg] at h
      simpa only [c0] using h
    have hval : S'.scalar (t - a) x = metricScalarAt (S.base.metric t) x := by
      change metricScalarAt (S.base.metric (t - a + a)) x = metricScalarAt (S.base.metric t) x
      rw [sub_add_cancel]
    rw [hbar, hval] at hb
    exact hb

theorem incomingSlab_scalarLowerBarrier_le
    {P : OrientedThreeStage.{u}} {a s c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (G : P.IncomingSlab a s)
    (hinit : ∀ x : P.Carrier, -3 / (2 * (a + c)) ≤ metricScalarAt (G.flow.base.metric a) x)
    {t : ℝ} (ht : t ∈ Set.Ico a s) (x : P.Carrier) :
    -3 / (2 * (t + c)) ≤ metricScalarAt (G.flow.base.metric t) x :=
  scalarLowerBarrier_le_on_slab ha hc G.flow G.equation
    (fun _ ht => ht) (fun _ ht => ht) hinit ht x

theorem closedSlab_scalarLowerBarrier_le_interior
    {P : OrientedThreeStage.{u}} {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (G : P.ClosedSlab a b)
    (hinit : ∀ x : P.Carrier, -3 / (2 * (a + c)) ≤ metricScalarAt (G.flow.base.metric a) x)
    {t : ℝ} (ht : t ∈ Set.Ico a b) (x : P.Carrier) :
    -3 / (2 * (t + c)) ≤ metricScalarAt (G.flow.base.metric t) x :=
  scalarLowerBarrier_le_on_slab ha hc G.flow G.equation
    (fun _ ht => ⟨ht.1, ht.2.le⟩) (fun _ ht => ht) hinit ht x

theorem closedSlab_scalarLowerBarrier_le
    {P : OrientedThreeStage.{u}} {a b c : ℝ} (hab : a < b) (ha : 0 ≤ a) (hc : 0 < c)
    (G : P.ClosedSlab a b)
    (hinit : ∀ x : P.Carrier, -3 / (2 * (a + c)) ≤ metricScalarAt (G.flow.base.metric a) x)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (x : P.Carrier) :
    -3 / (2 * (t + c)) ≤ metricScalarAt (G.flow.base.metric t) x := by
  rcases eq_or_lt_of_le ht.2 with htb | hltb
  · have hS : IsSolutionOn (I := ThreeModel) (M := P.Carrier) G.flow := G.equation
    have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
    have hcont_f : ContinuousOn (fun t : ℝ => G.flow.scalar t x) (Set.Icc a b) := by
      have hcar :
          (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed a b hab.le).carrier =
            Set.Icc a b := rfl
      have hcont := hS.scalarCont
      rw [hcar] at hcont
      have := hcont.comp hmap.continuousOn (fun t ht' => ⟨ht', trivial⟩)
      simpa only [Function.comp_def] using this
    have hcont_g : ContinuousOn (fun t : ℝ => -3 / (2 * (t + c))) (Set.Icc a b) := by
      have hden_cont : ContinuousOn (fun t : ℝ => 2 * (t + c)) (Set.Icc a b) := by fun_prop
      have hne : ∀ t ∈ Set.Icc a b, 2 * (t + c) ≠ 0 := by
        intro t ht'
        have : 0 < 2 * (t + c) := by linarith [ht'.1, hc]
        exact this.ne'
      exact (continuousOn_const (c := (-3 : ℝ))).div hden_cont hne
    have hdiff : ContinuousOn (fun t : ℝ => G.flow.scalar t x - (-3 / (2 * (t + c))))
        (Set.Icc a b) := hcont_f.sub hcont_g
    have hnonneg : ∀ t ∈ Set.Ioo a b,
        (0 : ℝ) ≤ G.flow.scalar t x - (-3 / (2 * (t + c))) := by
      intro t ht'
      have hb : -3 / (2 * (t + c)) ≤ G.flow.scalar t x :=
        closedSlab_scalarLowerBarrier_le_interior ha hc G hinit
          (⟨ht'.1.le, ht'.2⟩ : t ∈ Set.Ico a b) x
      linarith
    have hclosure : closure (Set.Ioo a b) = Set.Icc a b := closure_Ioo hab.ne
    have hmem : b ∈ closure (Set.Ioo a b) := by
      rw [hclosure]; exact ⟨hab.le, le_rfl⟩
    have hb : (0 : ℝ) ≤ G.flow.scalar b x - (-3 / (2 * (b + c))) :=
      le_on_closure hnonneg (continuousOn_const (c := (0 : ℝ)))
        (by rw [hclosure]; exact hdiff) hmem
    rw [htb]
    change -3 / (2 * (b + c)) ≤ G.flow.scalar b x
    linarith
  · exact closedSlab_scalarLowerBarrier_le_interior ha hc G hinit ⟨ht.1, hltb⟩ x

def TerminalScalarLowerBound (H : ObservedHistory.{u}) (c : ℝ) : Prop :=
  ∀ i : Fin H.eventCount, ∀ x : (H.event i).incoming.terminalRegularOpen,
    -3 / (2 * (H.time i.succ + c)) ≤ metricScalarAt (H.event i).terminal.metric x

theorem stageInitial_scalarLowerBound_of_terminal
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
    (G : GeometricCutoffRecord H i parameters) {c : ℝ} (hc : 0 < c)
    (hterm : ∀ x : (H.event i).incoming.terminalRegularOpen,
      -3 / (2 * (H.time i.succ + c)) ≤ metricScalarAt (H.event i).terminal.metric x) :
    ∀ x : (H.stage i.succ).Carrier,
      -3 / (2 * (H.time i.succ + c)) ≤ metricScalarAt (H.initialMetric i.succ) x := by
  intro x
  have hge : 0 ≤ H.time i.succ := (ObservedHistory.eventTimes_subset_Ioc H ⟨i, rfl⟩).1.le
  have hle : -3 / (2 * (H.time i.succ + c)) ≤ 0 :=
    (scalarLowerBarrier_neg hc hge).le
  have h := G.scalar_preserving (-3 / (2 * (H.time i.succ + c))) hle hterm x
  rwa [H.event_output i] at h

theorem stageInitial_scalarLowerBound_of_terminalLowerBound
    {H : ObservedHistory.{u}} {parameters : CutoffParameters}
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters) {c : ℝ} (hc : 0 < c)
    (hterm : TerminalScalarLowerBound H c) :
    ∀ i : Fin H.eventCount, ∀ x : (H.stage i.succ).Carrier,
      -3 / (2 * (H.time i.succ + c)) ≤ metricScalarAt (H.initialMetric i.succ) x :=
  fun i => stageInitial_scalarLowerBound_of_terminal (cutoff i) hc (hterm i)

theorem terminalScalarLowerBound_of_incomingSlab
    {P : OrientedThreeStage.{u}} {a s c : ℝ} (hab : a < s) (ha : 0 ≤ a) (hc : 0 < c)
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric)
    (hinit : ∀ y : P.Carrier, -3 / (2 * (a + c)) ≤ metricScalarAt (G.flow.base.metric a) y) :
    ∀ x : G.terminalRegularOpen, -3 / (2 * (s + c)) ≤ metricScalarAt L.metric x := by
  intro x
  have hspos : 0 < s + c := by linarith
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hSigma : SigmaCompactSpace G.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (I := ThreeModel)
        (M := P.Carrier) (U := (G.terminalRegularOpen : Set P.Carrier))
        G.terminalRegularOpen.2)
  set B : ℝ := metricCovDerivNorm 0 L.metric L.metric x + 1 with hB
  obtain ⟨C, hCpos, hC⟩ := DifferentialGeometry.Geometry.Curvature.exists_abs_metricScalarAt_sub_le
    (I := ThreeModel) (M := G.terminalRegularOpen) (gRef := L.metric)
    (K := ({x} : Set G.terminalRegularOpen)) isCompact_singleton (1 / 2) B (by norm_num)
  set ε₁ : ℝ := min (1 / 8) (ε / (6 * C + 6)) with hε₁
  have hε₁a : (0 : ℝ) < 1 / 8 := by norm_num
  have hε₁b : (0 : ℝ) < ε / (6 * C + 6) := div_pos hε (by linarith)
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁]
    exact lt_min hε₁a hε₁b
  have hε₁le : ε₁ ≤ 1 / 8 := by rw [hε₁]; exact min_le_left _ _
  have hε₁small : C * 3 * ε₁ ≤ ε / 2 := by
    have hle : ε₁ ≤ ε / (6 * C + 6) := by rw [hε₁]; exact min_le_right _ _
    have hden : (0 : ℝ) < 6 * C + 6 := by linarith
    have hmul : ε₁ * (6 * C + 6) ≤ ε := (le_div_iff₀ hden).mp hle
    nlinarith only [hmul, hε₁pos.le, hCpos.le]
  obtain ⟨d0, hd0, hcv0⟩ := L.converges {x} isCompact_singleton 0 ε₁ hε₁pos
  obtain ⟨d1, hd1, hcv1⟩ := L.converges {x} isCompact_singleton 1 ε₁ hε₁pos
  obtain ⟨d2, hd2, hcv2⟩ := L.converges {x} isCompact_singleton 2 ε₁ hε₁pos
  set d : ℝ := max d0 (max d1 d2) with hd
  have hdIco : d ∈ Set.Ico a s :=
    ⟨hd0.1.trans (le_max_left _ _), max_lt hd0.2 (max_lt hd1.2 hd2.2)⟩
  have hd0le : d0 ≤ d := by rw [hd]; exact le_max_left _ _
  have hd1le : d1 ≤ d := by rw [hd]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hd2le : d2 ≤ d := by
    rw [hd]
    exact (le_max_right d1 d2).trans (le_max_right d0 (max d1 d2))
  set δ : ℝ := min ((s - d) / 2) (ε * (s + c) * c / 3) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith [hdIco.2] : (0 : ℝ) < (s - d) / 2)
      (div_pos (mul_pos (mul_pos hε hspos) hc) (by norm_num) :
        (0 : ℝ) < ε * (s + c) * c / 3)
  set t : ℝ := (s + max d (s - δ)) / 2 with ht
  have hm_lt : max d (s - δ) < s := max_lt hdIco.2 (by linarith)
  have hm_ge : d ≤ max d (s - δ) := le_max_left _ _
  have ht_gt : d < t := by rw [ht]; linarith [hm_ge, hdIco.2]
  have ht_lt : t < s := by rw [ht]; linarith [hm_lt]
  have htIco : t ∈ Set.Ico a s := ⟨hdIco.1.trans ht_gt.le, ht_lt⟩
  have htIoo0 : t ∈ Set.Ioo d0 s := ⟨hd0le.trans_lt ht_gt, ht_lt⟩
  have htIoo1 : t ∈ Set.Ioo d1 s := ⟨hd1le.trans_lt ht_gt, ht_lt⟩
  have htIoo2 : t ∈ Set.Ioo d2 s := ⟨hd2le.trans_lt ht_gt, ht_lt⟩
  have hst : s - t ≤ δ / 2 := by
    have h1 : s - δ ≤ max d (s - δ) := le_max_right _ _
    rw [ht]
    linarith
  have h3st : 3 * (s - t) ≤ ε * (s + c) * (t + c) := by
    have hδle : δ ≤ ε * (s + c) * c / 3 := by rw [hδ]; exact min_le_right _ _
    have htc : c ≤ t + c := by linarith [htIco.1, ha]
    have h1 : 3 * (s - t) ≤ 3 * (δ / 2) := by linarith
    have h2 : 3 * (δ / 2) ≤ ε * (s + c) * (t + c) := by
      have h2a : 3 * (δ / 2) ≤ ε * (s + c) * c / 2 := by nlinarith only [hδle]
      have hfac : 0 ≤ ε * (s + c) := mul_nonneg hε.le hspos.le
      have hc2 : c / 2 ≤ t + c := by linarith [htc, hc]
      have h2b : ε * (s + c) * c / 2 ≤ ε * (s + c) * (t + c) := by
        have hm := mul_le_mul_of_nonneg_left hc2 hfac
        nlinarith only [hm]
      linarith only [h2a, h2b]
    exact h1.trans h2
  have htsl : 3 / (2 * (t + c)) - 3 / (2 * (s + c)) ≤ ε / 2 := by
    have htcpos : 0 < t + c := by linarith [htIco.1, ha]
    have hden2 : (0 : ℝ) < 2 * (t + c) * (s + c) :=
      mul_pos (mul_pos (by norm_num) htcpos) hspos
    have hgoal : 3 * (s - t) / (2 * (t + c) * (s + c)) ≤ ε / 2 := by
      rw [div_le_div_iff₀ hden2 (by norm_num)]
      nlinarith only [h3st]
    have heq : 3 / (2 * (t + c)) - 3 / (2 * (s + c))
        = 3 * (s - t) / (2 * (t + c) * (s + c)) := by
      field_simp
      ring
    rw [heq]
    exact hgoal
  have e1 : -3 / (2 * (s + c)) = -(3 / (2 * (s + c))) := by ring
  have e2 : -3 / (2 * (t + c)) = -(3 / (2 * (t + c))) := by ring
  have hLt : -(3 / (2 * (s + c))) - ε / 2 ≤ -(3 / (2 * (t + c))) := by
    linarith only [htsl]
  have hlowu : ∀ y ∈ ({x} : Set G.terminalRegularOpen), ∀ ξ : TangentSpace ThreeModel y,
      (1 / 2) * L.metric.inner y ξ ξ
        ≤ ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner y ξ ξ := by
    intro y hy ξ
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hfin : (Module.finrank ℝ (TangentSpace ThreeModel x) : ℝ) = 3 := by
      have h1 : Module.finrank ℝ (TangentSpace ThreeModel x) = Module.finrank ℝ ThreeSpace := rfl
      rw [h1, finrank_euclideanSpace_fin]
      simp
    have h0 : metricDerivNorm 0 ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
        L.metric L.metric x ≤ ε₁ := (hcv0 t htIoo0 x (Set.mem_singleton x)).le
    have hq := metricQuadFormDiff_le_metricDerivNorm (I := ThreeModel)
      (gk := (G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
      (gInf := L.metric) (gRef := L.metric) x ξ
    have hnonneg : 0 ≤ L.metric.inner x ξ ξ :=
      DifferentialGeometry.metric_inner_self_nonneg L.metric x ξ
    have hkey : |((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner x ξ ξ
        - L.metric.inner x ξ ξ| ≤ (1 / 2) * L.metric.inner x ξ ξ := by
      refine hq.trans ?_
      rw [hfin]
      nlinarith only [h0, hnonneg, hε₁le]
    linarith [(abs_le.mp hkey).1]
  have hlowu' : ∀ y ∈ ({x} : Set G.terminalRegularOpen), ∀ ξ : TangentSpace ThreeModel y,
      (1 / 2) * L.metric.inner y ξ ξ ≤ L.metric.inner y ξ ξ := by
    intro y hy ξ
    have h := DifferentialGeometry.metric_inner_self_nonneg L.metric y ξ
    linarith
  have hBnn : 0 ≤ metricCovDerivNorm 0 L.metric L.metric x := Real.sqrt_nonneg _
  have hz0 : metricCovDerivNorm 1 L.metric L.metric x = 0 := by
    simpa using covNorm_self_succ (I := ThreeModel) L.metric 0 x
  have hz1 : metricCovDerivNorm 2 L.metric L.metric x = 0 := by
    simpa using covNorm_self_succ (I := ThreeModel) L.metric 1 x
  have hcovu : ∀ y ∈ ({x} : Set G.terminalRegularOpen), ∀ k ≤ 2,
      metricCovDerivNorm k ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
        L.metric y ≤ B := by
    intro y hy k hk
    rw [Set.mem_singleton_iff] at hy
    subst y
    have htri := covNorm_le_add (I := ThreeModel) k
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric x
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl
    · have h10 : metricDerivNorm 0 ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
          L.metric L.metric x ≤ 1 :=
        (hcv0 t htIoo0 x (Set.mem_singleton x)).le.trans (by linarith)
      rw [hB]
      linarith only [htri, h10, hBnn]
    · have h11 : metricDerivNorm 1 ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
          L.metric L.metric x ≤ 1 :=
        (hcv1 t htIoo1 x (Set.mem_singleton x)).le.trans (by linarith)
      rw [hB]
      linarith only [htri, hz0, h11, hBnn]
    · have h12 : metricDerivNorm 2 ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
          L.metric L.metric x ≤ 1 :=
        (hcv2 t htIoo2 x (Set.mem_singleton x)).le.trans (by linarith)
      rw [hB]
      linarith only [htri, hz1, h12, hBnn]
  have hcovu' : ∀ y ∈ ({x} : Set G.terminalRegularOpen), ∀ k ≤ 2,
      metricCovDerivNorm k L.metric L.metric y ≤ B := by
    intro y hy k hk
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    have hBpos : 0 ≤ B := by rw [hB]; linarith only [hBnn]
    rcases hk3 with rfl | rfl | rfl
    · rw [hB]; linarith only [hBnn]
    · rw [hz0]; exact hBpos
    · rw [hz1]; exact hBpos
  have hCbound : |metricScalarAt ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) x
      - metricScalarAt L.metric x| ≤ ε / 2 := by
    have h := hC ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric
      hlowu hlowu' hcovu hcovu' x (Set.mem_singleton x)
    refine h.trans ?_
    have hsum : (∑ q ∈ Finset.range 3,
        metricDerivNorm q ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
          L.metric L.metric x) ≤ 3 * ε₁ := by
      have hterm : ∀ q, q < 3 →
          metricDerivNorm q ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
            L.metric L.metric x ≤ ε₁ := by
        intro q hq
        have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by omega
        rcases hq' with rfl | rfl | rfl
        · exact (hcv0 t htIoo0 x (Set.mem_singleton x)).le
        · exact (hcv1 t htIoo1 x (Set.mem_singleton x)).le
        · exact (hcv2 t htIoo2 x (Set.mem_singleton x)).le
      calc (∑ q ∈ Finset.range 3,
            metricDerivNorm q ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
              L.metric L.metric x)
          ≤ ∑ _q ∈ Finset.range 3, ε₁ :=
            Finset.sum_le_sum (fun q hq => hterm q (Finset.mem_range.mp hq))
        _ = 3 * ε₁ := by simp
    have h1 : C * (∑ q ∈ Finset.range 3,
        metricDerivNorm q ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
          L.metric L.metric x) ≤ C * (3 * ε₁) := mul_le_mul_of_nonneg_left hsum hCpos.le
    nlinarith only [h1, hε₁small]
  have hbar : -3 / (2 * (t + c)) ≤ metricScalarAt (G.flow.base.metric t) (x : P.Carrier) :=
    incomingSlab_scalarLowerBarrier_le ha hc G hinit htIco (x : P.Carrier)
  have hbridge : metricScalarAt ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) x
      = metricScalarAt (G.flow.base.metric t) (x : P.Carrier) :=
    DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen
      (I := ThreeModel) (M := P.Carrier) (G.flow.base.metric t) G.terminalRegularOpen x
  have hlow := (abs_le.mp hCbound).2
  rw [e1]
  rw [e2] at hbar
  linarith only [hlow, hbar, hbridge, hLt]

theorem stageInitial_scalarLowerBound_of_history
    {H : ObservedHistory.{u}} {parameters : CutoffParameters}
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + c)) ≤ metricScalarAt (H.initialMetric 0) y) :
    ∀ i : Fin (H.eventCount + 1), ∀ y : (H.stage i).Carrier,
      -3 / (2 * (H.time i + c)) ≤ metricScalarAt (H.initialMetric i) y := by
  refine Fin.induction (n := H.eventCount) (motive := fun i => ∀ y : (H.stage i).Carrier,
      -3 / (2 * (H.time i + c)) ≤ metricScalarAt (H.initialMetric i) y) h0 ?_
  intro i ih y
  have hle : 0 ≤ H.time i.castSucc :=
    (Extinction.Width.historyStageTime H i.castSucc).2.1
  have hinit : ∀ z : (H.stage i.castSucc).Carrier,
      -3 / (2 * (H.time i.castSucc + c)) ≤
        metricScalarAt ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) z := by
    intro z
    rw [H.event_initial i]
    exact ih z
  have hterm := terminalScalarLowerBound_of_incomingSlab
    (H.time_strictMono (Fin.castSucc_lt_succ (i := i))) hle hc (H.event i).incoming
    (H.event i).terminal hinit
  exact stageInitial_scalarLowerBound_of_terminal (cutoff i) hc hterm y

theorem terminalScalarLowerBound_of_history
    {H : ObservedHistory.{u}} {c : ℝ} (hc : 0 < c)
    (hstage : ∀ i : Fin (H.eventCount + 1), ∀ y : (H.stage i).Carrier,
      -3 / (2 * (H.time i + c)) ≤ metricScalarAt (H.initialMetric i) y) :
    TerminalScalarLowerBound H c := by
  intro i x
  have hle : 0 ≤ H.time i.castSucc :=
    (Extinction.Width.historyStageTime H i.castSucc).2.1
  have hinit : ∀ z : (H.stage i.castSucc).Carrier,
      -3 / (2 * (H.time i.castSucc + c)) ≤
        metricScalarAt ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) z := by
    intro z
    rw [H.event_initial i]
    exact hstage i.castSucc z
  exact terminalScalarLowerBound_of_incomingSlab
    (H.time_strictMono (Fin.castSucc_lt_succ (i := i))) hle hc (H.event i).incoming
    (H.event i).terminal hinit x

theorem historyScalarLowerBound_of_stageInitial
    {H : ObservedHistory.{u}} {c : ℝ} (hc : 0 < c)
    (hstage : ∀ i : Fin (H.eventCount + 1), ∀ y : (H.stage i).Carrier,
      -3 / (2 * (H.time i + c)) ≤ metricScalarAt (H.initialMetric i) y) :
    HistoryScalarLowerBound H c := by
  intro t htE
  have key : ∀ j : Fin (H.eventCount + 1), j = Extinction.Width.historyStageAt H t →
      ∀ x : (H.stage j).Carrier,
        -3 / (2 * (t.1 + c)) ≤ metricScalarAt (Extinction.Width.historyStageMetric H j t.1) x := by
    intro j hj
    cases j using Fin.lastCases with
    | last =>
      intro x
      have hmem := Extinction.Width.historyStageAt_mem H t
      rw [← hj] at hmem
      have htIcc : t.1 ∈ Set.Icc (H.time (Fin.last H.eventCount)) H.horizon := by
        simpa only [Extinction.Width.historyStageDomain, Fin.lastCases_last] using hmem
      by_cases hfin : H.time (Fin.last H.eventCount) < H.horizon
      · have hle : 0 ≤ H.time (Fin.last H.eventCount) :=
          (Extinction.Width.historyStageTime H (Fin.last H.eventCount)).2.1
        have hinit : ∀ z : (H.stage (Fin.last H.eventCount)).Carrier,
            -3 / (2 * (H.time (Fin.last H.eventCount) + c)) ≤
              metricScalarAt ((H.finalSlab hfin).flow.base.metric
                (H.time (Fin.last H.eventCount))) z := by
          intro z
          rw [H.final_initial hfin]
          exact hstage (Fin.last H.eventCount) z
        have hmetric : Extinction.Width.historyStageMetric H (Fin.last H.eventCount) t.1
            = (H.finalSlab hfin).flow.base.metric t.1 := by
          simp only [Extinction.Width.historyStageMetric, Fin.lastCases_last]
          rw [dif_pos hfin]
        rw [hmetric]
        exact closedSlab_scalarLowerBarrier_le hfin hle hc (H.finalSlab hfin) hinit htIcc x
      · have hge : H.horizon ≤ H.time (Fin.last H.eventCount) := le_of_not_gt hfin
        have ht_eq : t.1 = H.time (Fin.last H.eventCount) :=
          le_antisymm (htIcc.2.trans hge) htIcc.1
        rw [ht_eq, Extinction.Width.historyStageMetric_initial H (Fin.last H.eventCount)]
        exact hstage (Fin.last H.eventCount) x
    | cast i =>
      intro x
      have hmem := Extinction.Width.historyStageAt_mem H t
      rw [← hj] at hmem
      have htIco : t.1 ∈ Set.Ico (H.time i.castSucc) (H.time i.succ) := by
        simpa only [Extinction.Width.historyStageDomain, Fin.lastCases_castSucc] using hmem
      have hle : 0 ≤ H.time i.castSucc :=
        (Extinction.Width.historyStageTime H i.castSucc).2.1
      have hinit : ∀ z : (H.stage i.castSucc).Carrier,
          -3 / (2 * (H.time i.castSucc + c)) ≤
            metricScalarAt ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) z := by
        intro z
        rw [H.event_initial i]
        exact hstage i.castSucc z
      have hmetric : Extinction.Width.historyStageMetric H i.castSucc t.1
          = (H.event i).incoming.flow.base.metric t.1 := by
        simp only [Extinction.Width.historyStageMetric, Fin.lastCases_castSucc]
      rw [hmetric]
      exact incomingSlab_scalarLowerBarrier_le hle hc (H.event i).incoming hinit htIco x
  exact key (Extinction.Width.historyStageAt H t) rfl

theorem historyScalarLowerBound_of_history
    {H : ObservedHistory.{u}} {parameters : CutoffParameters}
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + c)) ≤ metricScalarAt (H.initialMetric 0) y) :
    HistoryScalarLowerBound H c ∧ TerminalScalarLowerBound H c :=
  ⟨historyScalarLowerBound_of_stageInitial hc
      (stageInitial_scalarLowerBound_of_history cutoff hc h0),
    terminalScalarLowerBound_of_history hc
      (stageInitial_scalarLowerBound_of_history cutoff hc h0)⟩

end DifferentialGeometry.PDE.RicciFlow
