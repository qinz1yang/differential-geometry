import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparisonRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SurgeryWidthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity

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

end DifferentialGeometry.PDE.RicciFlow
