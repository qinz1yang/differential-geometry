import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SlabScalarLowerBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeEvent_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventVolumeAssembly_S14

set_option autoImplicit false

/-!
# CH12-CX9: nonnegative scalar curvature and volume on a smooth interval

The smooth maximum principle is the existing scalar lower barrier theorem, with
arbitrarily large positive shifts. Terminal scalar convergence is on compact
subsets of the regular open set. The event volume bound is S14's compact-set
VB-B statement; no terminal total volume is introduced.
-/

noncomputable section

open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {D : RealTimeInterval}

/-- The smooth scalar maximum principle, with zero initial lower bound. -/
theorem scalar_nonnegative_on_Ico_CX9 {a b : ℝ} (ha : 0 ≤ a)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    (hcar : Ico a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hinit : ∀ x, 0 ≤ metricScalarAt (S.base.metric a) x)
    {t : ℝ} (ht : t ∈ Ico a b) (x : P.Carrier) :
    0 ≤ metricScalarAt (S.base.metric t) x := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 < 3 / ε := div_pos (by norm_num) hε
  have ht0 : 0 ≤ t := ha.trans ht.1
  have hb := scalarLowerBarrier_le_on_slab ha hc S hS hcar hreg
    (fun y => (scalarLowerBarrier_neg hc ha).le.trans (hinit y)) ht x
  have hden : 0 < 2 * (t + 3 / ε) := by positivity
  have hsmall : 3 / (2 * (t + 3 / ε)) ≤ ε := by
    rw [div_le_iff₀ hden]
    have he : ε * (3 / ε) = 3 := by field_simp
    nlinarith [mul_nonneg hε.le ht0]
  rw [neg_div] at hb
  linarith

/-- Endpoint continuity extends the smooth nonnegativity statement to a closed slab. -/
theorem scalar_nonnegative_on_Icc_CX9 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hinit : ∀ x, 0 ≤ metricScalarAt (S.base.metric a) x) :
    ∀ t ∈ Icc a b, ∀ x, 0 ≤ metricScalarAt (S.base.metric t) x := by
  rcases hab.eq_or_lt with rfl | hab
  · intro t ht x
    have : t = a := le_antisymm ht.2 ht.1
    subst t
    exact hinit x
  intro t ht x
  have hcont : ContinuousOn (fun v => S.scalar v x) (Icc a b) := by
    have hmap : Continuous (fun v : ℝ => (v, x)) := continuous_id.prodMk continuous_const
    have hc : ContinuousOn (fun p : ℝ × P.Carrier => S.scalar p.1 p.2)
        (Icc a b ×ˢ univ) := hS.scalarCont.mono (Set.prod_mono hcar Set.Subset.rfl)
    have hh := hc.comp hmap.continuousOn (fun v hv => ⟨hv, mem_univ x⟩)
    simpa only [Function.comp_def] using hh
  have hlow : ∀ v ∈ Ioo a b, 0 ≤ S.scalar v x := by
    intro v hv
    rw [solution_scalar_eq_S10]
    exact scalar_nonnegative_on_Ico_CX9 ha S hS
      (fun z hz => hcar ⟨hz.1, hz.2.le⟩) hreg hinit ⟨hv.1.le, hv.2⟩ x
  have hclosure : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  rw [← solution_scalar_eq_S10]
  exact le_on_closure hlow continuousOn_const (by rw [hclosure]; exact hcont)
    (by rw [hclosure]; exact ht)

/-- With nonnegative scalar curvature, the unnormalised volume is nonincreasing. -/
theorem flowVolume_antitone_of_nonnegative_CX9 {a b : ℝ}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x, 0 ≤ metricScalarAt (S.base.metric t) x) :
    AntitoneOn (flowVolume_S10 S) (Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
    ((S.continuousOn_volume hS).mono hcar) ?_ ?_
  · intro t ht
    rw [interior_Icc] at ht
    exact (flowVolume_hasDerivAt_S10 S hS (hreg ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(flowVolume_hasDerivAt_S10 S hS (hreg ht)).deriv]
    have h := integral_neg_scalar_le_S10 S t (k := 0) le_rfl
      (fun x => by rw [neg_zero, solution_scalar_eq_S10]; exact hR t ht x)
    simpa only [zero_mul] using h

/-- Smooth propagation from an arbitrary starting time, including the volume bound. -/
theorem smooth_nonnegative_volume_CX9 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hinit : ∀ x, 0 ≤ metricScalarAt (S.base.metric a) x) :
    (∀ x, 0 ≤ metricScalarAt (S.base.metric b) x) ∧
      riemannianVolumeMeasure ThreeModel P.Carrier (S.base.metric b) univ ≤
        riemannianVolumeMeasure ThreeModel P.Carrier (S.base.metric a) univ := by
  have hR := scalar_nonnegative_on_Icc_CX9 ha hab S hS hcar hreg hinit
  refine ⟨hR b ⟨hab, le_rfl⟩, ?_⟩
  have hanti := flowVolume_antitone_of_nonnegative_CX9 S hS hcar hreg
    (fun t ht => hR t ⟨ht.1.le, ht.2.le⟩)
  have hfin (t : ℝ) :
      riemannianVolumeMeasure ThreeModel P.Carrier (S.base.metric t) univ ≠ ⊤ :=
    (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := ThreeModel) (M := P.Carrier) _).measure_univ_lt_top.ne
  exact (ENNReal.toReal_le_toReal (hfin b) (hfin a)).mp
    (hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)

/-- Terminal regular convergence and `scalar_preserving 0` cross one recorded surgery. -/
theorem event_nonnegative_of_eventually_CX9 {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {parameters : CutoffParameters}
    (R : GeometricCutoffRecord H i parameters)
    (hR : ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∀ x, 0 ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x) :
    ∀ x, 0 ≤ metricScalarAt (H.initialMetric i.succ) x := by
  apply R.scalar_lower_bound_output_of_incoming (b := fun _ => 0) le_rfl tendsto_const_nhds
  intro x
  filter_upwards [hR] with t ht
  exact ht x.val

/-- VB-B plus convergence on its compact set crosses the event volume bound. -/
theorem event_volume_le_of_eventually_CX9 {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {parameters : CutoffParameters}
    (R : GeometricCutoffRecord H i parameters) (V : ℝ≥0∞)
    (hV : ∀ᶠ t in 𝓝[<] H.time i.succ,
      riemannianVolumeMeasure ThreeModel (H.stage i.castSucc).Carrier
        ((H.event i).incoming.flow.base.metric t) univ ≤ V) :
    riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
      (H.initialMetric i.succ) univ ≤ V := by
  let G := (H.event i).incoming
  let : SigmaCompactSpace G.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        G.terminalRegularOpen.isOpen)
  obtain ⟨K, hK, hKle⟩ := event_volume_le_compact_S14 R
  have hterm := (H.event i).terminal.volume_compact_le_of_eventually_volume_le hK hV
  rw [H.event_output i] at hKle
  exact hKle.trans hterm

end GC.LongTime.Ch12
