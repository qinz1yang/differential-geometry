import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ScaffoldData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffAccuracyGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix.Basic
import DifferentialGeometry.Analysis.Order.CommonProfile

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped ENNReal

namespace GC.GeneralFlow.PreparedSpatialChain
universe u

/-- Glue parameters and records on the actual prepared spatial chain. The same
flow carries closed-time canonical witnesses and a positive antitone physical
noncollapse profile. This does not yet assert the larger-ball conclusion. -/
theorem exists_surgery_with_spatial_control
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      F.tower = S.tower ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) C.epsilon t) ∧
      ∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static := by
  let T := S.tower
  let p : ℕ → CutoffParameters := fun n => (S.observation n).parameters
  let κ : ℕ → ℝ := fun n => (S.observation n).kappa
  let old : ∀ n, ∀ i : Fin (T.history n).eventCount,
      GeometricCutoffRecord (T.history n).toHistory i (p n) :=
    fun n => (S.observation n).records
  have hstatic := fun n => (S.observation n).static_eq
  have hcontrol := fun n => (S.observation n).control
  have hwin := fun n => (S.observation n).windows
  have hnc : ∀ n, 0 < κ n ∧ (T.history n).NoncollapsedBefore (κ n) C.epsilon (n : ℝ) :=
    fun n => ⟨(S.observation n).kappa_pos, (S.observation n).noncollapsed⟩
  have hnext : ∀ n, (T.initial n).IsPrefixOf (T.initial (n + 1)) ∧
      ∃ hn : (T.history n).eventCount ≤ (T.history (n + 1)).eventCount,
        (∀ t : ℝ, t ≤ (n : ℝ) → (p (n + 1)).delta t = (p n).delta t ∧
          (p (n + 1)).neckRadius t = (p n).neckRadius t ∧
          (p (n + 1)).protectedRadius t = (p n).protectedRadius t) ∧
        ∀ i : Fin (T.history n).eventCount,
          HEq (old (n + 1) (i.castLE hn)).nominalRadius (old n i).nominalRadius ∧
          HEq (old (n + 1) (i.castLE hn)).delta (old n i).delta ∧
          HEq (old (n + 1) (i.castLE hn)).order (old n i).order ∧
          HEq (old (n + 1) (i.castLE hn)).neck (old n i).neck ∧
          HEq (old (n + 1) (i.castLE hn)).static (old n i).static := by
    intro n
    have hn := S.observation_successor n
    exact ⟨hn.initial_prefix, hn.count_le, hn.parameters_past, hn.records_preserved⟩
  have hfields : ∀ n : ℕ,
      ∃ hn : (T.history n).eventCount ≤ (T.history (n + 1)).eventCount,
        ∀ i : Fin (T.history n).eventCount,
          HEq (old (n + 1) (i.castLE hn)).nominalRadius (old n i).nominalRadius ∧
          HEq (old (n + 1) (i.castLE hn)).delta (old n i).delta ∧
          HEq (old (n + 1) (i.castLE hn)).order (old n i).order ∧
          HEq (old (n + 1) (i.castLE hn)).neck (old n i).neck ∧
          HEq (old (n + 1) (i.castLE hn)).static (old n i).static := by
    intro n
    obtain ⟨hn, _, hR⟩ := (hnext n).2
    exact ⟨hn, hR⟩
  obtain ⟨hc, hOld⟩ := all_record_fields_of_successors T p old hfields
  have hpast := all_parameter_values_of_successors p (fun n t ht => by
    obtain ⟨_, hp, _⟩ := (hnext n).2
    exact hp t ht)
  have hmark : ∀ m n : ℕ, m ≤ n → (T.initial m).IsPrefixOf (T.initial n) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact InitialIdentification.IsPrefixOf.refl _
    | succ n _ ih => exact ih.trans (hnext n).1
  have hstatic' : ∀ n, (p n).fixed = (p 0).fixed ∧
      (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧
      (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant := by
    intro n
    exact ⟨(hstatic n).1.trans (hstatic 0).1.symm,
      (hstatic n).2.1.trans (hstatic 0).2.1.symm,
      (hstatic n).2.2.1.trans (hstatic 0).2.2.1.symm,
      (hstatic n).2.2.2.1.trans (hstatic 0).2.2.2.1.symm,
      (hstatic n).2.2.2.2.trans (hstatic 0).2.2.2.2.symm⟩
  have hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p n).delta t ∧ (p m).neckRadius t = (p n).neckRadius t ∧
      (p m).protectedRadius t = (p n).protectedRadius t := by
    intro m n hmn t ht
    obtain ⟨hd, hr, hp⟩ := hpast m n hmn t ht.2
    exact ⟨hd.symm, hr.symm, hp.symm⟩
  have htime (n : ℕ) (i : Fin (T.history n).eventCount) :
      (T.history n).toHistory.time i.succ ≤ (n : ℝ) := by
    simpa only [T.horizon_eq] using (T.history n).toHistory.time_le_horizon_at i.succ
  let q := CutoffParameters.diagonal p
  let records : ∀ n, ∀ i : Fin (T.history n).eventCount,
      GeometricCutoffRecord (T.history n).toHistory i q :=
    fun n i => (old n i).diagonalParameters (hstatic' n) hcompat (htime n i)
  have hrecord := fun n i =>
    (old n i).diagonalParameters_preserves (hstatic' n) hcompat (htime n i)
  let F : GC.Interface.RawSurgery P g := ⟨T, hcontrol⟩
  refine ⟨F, q, commonProfile κ, records, rfl, hstatic 0,
    commonProfile_pos (fun n => (hnc n).1), commonProfile_antitone κ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc, ?_⟩
  · exact CutoffParameters.diagonal_delta_antitone p
      (fun m n hmn t ht => (hcompat m n hmn t ht).1)
      (fun n s hs t ht hst => (S.state (n + 1)).delta_antitone hs.1 ht.1 hst)
  · exact CutoffParameters.diagonal_neckRadius_antitone p
      (fun m n hmn t ht => (hcompat m n hmn t ht).2.1)
      (fun n s hs t ht hst => (S.state (n + 1)).radius_antitone hs.1 ht.1 hst)
  · intro n t ht
    exact CutoffParameters.diagonal_eq_on_prefix p hcompat n ht
  · intro n i j hij
    have hij' : i = j := Fin.ext hij
    subst j
    have hr := hrecord n i
    exact ⟨heq_of_eq hr.1, heq_of_eq hr.2.1, heq_of_eq hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2⟩
  · intro n t x hx
    have ht : (t : ℝ) ∈ Icc (0 : ℝ) (n : ℝ) := t.2
    have hr := (CutoffParameters.diagonal_eq_on_prefix p hcompat n ht).2.1
    rw [hr] at hx
    exact S.observation_canonical n t x hx
  · intro n i
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      rfl rfl rfl rfl HEq.rfl (hstatic' n).1.symm (hstatic' n).2.1.symm
      (hstatic' n).2.2.1.symm (hstatic' n).2.2.2.1.symm
      (old n i).static (records n i).static (hrecord n i).2.2.2.2 (hwin n i)
  · intro n t ht
    have hκ : commonProfile κ t ≤ κ (Nat.ceil t) :=
      (commonProfile_lt_budget (fun n => (hnc n).1) t (Nat.ceil t)
        (Nat.ceil_le_floor_add_one t)).le
    have hsmall : (T.history (Nat.ceil t)).NoncollapsedBefore (commonProfile κ t) C.epsilon t := by
      intro s x r hst hr hball
      exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hκ) (le_refl (ENNReal.ofReal r ^ 3))).trans
        ((hnc (Nat.ceil t)).2 s x r (hst.trans (Nat.le_ceil t)) hr hball)
    exact RetainedCoreHistory.noncollapsedBefore_of_isPrefixOf
      (hmark (Nat.ceil t) n (Nat.ceil_le.mpr ht.2)).1
      (by rw [T.horizon_eq]; exact Nat.le_ceil t) hsmall
  · intro m n hmn
    refine ⟨hmark m n hmn, ?_⟩
    intro i
    obtain ⟨hr, hd, ho, hk, hs⟩ := hOld m n hmn i
    have hm := hrecord m i
    have hn := hrecord n (i.castLE (hc hmn))
    exact ⟨(heq_of_eq hn.1).trans (hr.trans (heq_of_eq hm.1).symm),
      (heq_of_eq hn.2.1).trans (hd.trans (heq_of_eq hm.2.1).symm),
      (heq_of_eq hn.2.2.1).trans (ho.trans (heq_of_eq hm.2.2.1).symm),
      hn.2.2.2.1.trans (hk.trans hm.2.2.2.1.symm),
      hn.2.2.2.2.trans (hs.trans hm.2.2.2.2.symm)⟩

end GC.GeneralFlow.PreparedSpatialChain
