import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ZeroPoleComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CollarCompetitors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarSupport

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u uP

/-- Literal restriction of the original attained family at a surgery-time pole.
The original zero-clock node supplies cost comparison; the singleton new stage
has zero action, so the older restriction attains its own cost. -/
theorem regularizedCost_attained_of_zero_pole_restriction
    (H : ObservedHistory.{u})
    (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) {B v : ℝ} (hv : 0 ≤ v)
    (hpast : H.time i.succ - v ^ 2 ∈ H.stageDomain first)
    (gamma : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier)
    (hAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hInt : ∀ j, IntervalIntegrable
      (H.stageRegularizedLagrangian j.val (H.time i.succ) (gamma j)) volume
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hNodes : ∀ (k : Fin H.eventCount)
      (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.succ),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)))
    (hscalar : ∀ j t, t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hattain : H.regularizedExtendedAction first i.succ (H.time i.succ) B 0 v gamma =
      H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ)
        (H.time i.succ) B 0 v
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)
        (gamma ⟨first, le_rfl, hf.trans i.castSucc_le_succ⟩ v))
    (z : (H.event i).old)
    (hzOld : z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0)
    (hzNew : (H.event i).oldOutput z =
      gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) :
    let gammaOld : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier :=
      fun j => gamma ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
    (∑ j : H.StageInterval first i.succ,
      H.stageRegularizedAction j.val (H.time i.succ) (gamma j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) =
      (∑ j : H.StageInterval first i.castSucc,
        H.stageRegularizedAction j.val (H.time i.succ) (gammaOld j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) ∧
    H.regularizedExtendedAction first i.succ (H.time i.succ) B 0 v gamma =
      H.regularizedExtendedAction first i.castSucc (H.time i.succ) B 0 v gammaOld ∧
    H.regularizedExtendedAction first i.castSucc (H.time i.succ) B 0 v gammaOld =
      H.regularizedCost first i.castSucc hf (H.time i.succ) B 0 v
        (gammaOld ⟨i.castSucc, hf, le_rfl⟩ 0)
        (gammaOld ⟨first, le_rfl, hf⟩ v) := by
  classical
  intro gammaOld
  have hOldAC (j : H.StageInterval first i.castSucc) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (gammaOld j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val) :=
    hAC ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
  have hOldInt (j : H.StageInterval first i.castSucc) :
      IntervalIntegrable (H.stageRegularizedLagrangian j.val (H.time i.succ) (gammaOld j))
        volume (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val) :=
    hInt ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
  have hOldNodes : ∀ (k : Fin H.eventCount)
      (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.castSucc),
      ∃ z : (H.event k).old,
        z.val.val = gammaOld ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
        (H.event k).oldOutput z = gammaOld ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) :=
    fun k hkf hkl => hNodes k hkf (hkl.trans i.castSucc_le_succ)
  obtain ⟨beta, _, _, hbetaOld, hbetaLast, _, hsum⟩ :=
    H.extend_stage_family_by_zero_pole_stage first i hf v gamma gammaOld
      hOldAC hOldInt hOldNodes rfl ⟨z, hzOld, hzNew⟩
  have hbetaEq (j : H.StageInterval first i.succ) : beta j = gamma j := by
    by_cases hj : j.val ≤ i.castSucc
    · exact hbetaOld ⟨j.val, j.property.1, hj⟩
    · have heq : j = ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ := by
        apply Subtype.ext
        apply Fin.ext
        have hh := j.property.2
        change j.val.val ≤ i.val + 1 at hh
        change ¬j.val.val ≤ i.val at hj
        change j.val.val = i.val + 1
        omega
      subst j
      exact hbetaLast
  have hreal :
      (∑ j : H.StageInterval first i.succ,
        H.stageRegularizedAction j.val (H.time i.succ) (gamma j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) =
      (∑ j : H.StageInterval first i.castSucc,
        H.stageRegularizedAction j.val (H.time i.succ) (gammaOld j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) := by
    simpa only [hbetaEq] using hsum
  have hupperNew : H.time i.succ - (0 : ℝ) ^ 2 ∈
      Icc (H.time i.succ) (H.stageEndTime i.succ) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show H.time i.succ ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) from
        ⟨le_rfl, H.time_le_stageEndTime i.succ⟩)
  have hupperOld : H.time i.succ - (0 : ℝ) ^ 2 ∈
      Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [zero_pow two_ne_zero, sub_zero, H.stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
  have hfull := H.regularizedExtendedAction_eq_sum_action first i.succ
    le_rfl hv hupperNew hpast gamma hInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j.val (H.time i.succ - r ^ 2)
        (H.mapsTo_regularizedStage_Ioo (H.time i.succ) 0 v j.val hr) (gamma j r))
  have hold := H.regularizedExtendedAction_eq_sum_action first i.castSucc
    le_rfl hv hupperOld hpast gammaOld hOldInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j.val (H.time i.succ - r ^ 2)
        (H.mapsTo_regularizedStage_Ioo (H.time i.succ) 0 v j.val hr) (gammaOld j r))
  have hExt : H.regularizedExtendedAction first i.succ (H.time i.succ) B 0 v gamma =
      H.regularizedExtendedAction first i.castSucc (H.time i.succ) B 0 v gammaOld :=
    hfull.trans ((congrArg (fun A : ℝ => (A : WithTop ℝ)) hreal).trans hold.symm)
  have hmember : H.regularizedExtendedAction first i.castSucc (H.time i.succ) B 0 v gammaOld ∈
      H.regularizedActionValues first i.castSucc hf (H.time i.succ) B 0 v
        (gammaOld ⟨i.castSucc, hf, le_rfl⟩ 0) (gammaOld ⟨first, le_rfl, hf⟩ v) :=
    ⟨le_rfl, hv, hupperOld, hpast, gammaOld, hOldAC, rfl, rfl, hOldNodes, rfl⟩
  have hcostOld := H.regularizedCost_le_of_competitor first i.castSucc hf
    (H.time i.succ) B 0 v (gammaOld ⟨i.castSucc, hf, le_rfl⟩ 0)
      (gammaOld ⟨first, le_rfl, hf⟩ v) hmember
  have hcompare := H.regularizedCost_le_of_zero_pole first i hf B v z
    (gammaOld ⟨first, le_rfl, hf⟩ v)
  rw [hzNew, hzOld] at hcompare
  have hcostLower : H.regularizedExtendedAction first i.castSucc (H.time i.succ) B 0 v gammaOld ≤
      H.regularizedCost first i.castSucc hf (H.time i.succ) B 0 v
        (gammaOld ⟨i.castSucc, hf, le_rfl⟩ 0) (gammaOld ⟨first, le_rfl, hf⟩ v) :=
    hExt.symm.trans_le (hattain.trans_le hcompare)
  exact ⟨hreal, hExt, le_antisymm hcostLower hcostOld⟩

/-- Construct one support from the literal older restriction and retain the
same open neighborhood, inverse, scalar and action identities for the original
new-pole history. Only the original node witness is used at clock zero. -/
theorem exists_smooth_collar_cost_support_at_zero_pole
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) {v : ℝ} (hv : 0 < v)
    (hpast : H.time i.succ - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) (Bfloor : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -Bfloor ≤ metricScalarAt (H.stageMetric j t) x) :
    let T := H.time i.succ;
    let last := i.castSucc;
    let hle : first ≤ last := hf;
    let Jfull := H.StageInterval first i.succ;
    let Jstage := H.StageInterval first last;
    let Eevent := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : Eevent) : Jstage := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : Eevent) : Jstage := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : Jstage := ⟨first, le_rfl, hle⟩;
    let jl : Jstage := ⟨last, hle, le_rfl⟩;
    ∀ (gammaFull : (j : Jfull) → ℝ → (H.stage j.val).Carrier),
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gammaFull j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gammaFull j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      (∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.succ),
        ∃ z : (H.event k).old,
          z.val.val = gammaFull ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
            (Real.sqrt (T - H.time k.succ)) ∧
          (H.event k).oldOutput z = gammaFull ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
            (Real.sqrt (T - H.time k.succ))) →
      H.regularizedExtendedAction first i.succ T Bfloor 0 v gammaFull =
        H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ) T Bfloor 0 v
          (gammaFull ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)
          (gammaFull ⟨first, le_rfl, hf.trans i.castSucc_le_succ⟩ v) →
    let gamma : (j : Jstage) → ℝ → (H.stage j.val).Carrier :=
      fun j => gammaFull ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩;
    ∀ (lo hi : Jstage → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      hi jf < v →
    ∀ (W : (i : Eevent) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : Eevent) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DO : Jstage → RealTimeInterval) (DS : Eevent → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : Jstage) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (SS : (i : Eevent) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      (ordinary : (j : Jstage) → P × ℝ → (H.stage j.val).Carrier)
      (survivor : (i : Eevent) → P × ℝ → W i) (tail : P × ℝ → (H.stage first).Carrier),
      (∀ j, IsSolutionOn (SO j)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ j t, (SO j).base.metric t = H.stageMetric j.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (FC i z.val)) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => FC i z.val) (hnew i)) →
      (∀ j, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (ordinary j)) →
      (∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (survivor i)) →
      ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 tail →
    ∀ (V : Set P), IsOpen V → (0 : P) ∈ V →
    ∀ (KO : Jstage → Set ℝ) (KS : Eevent → Set ℝ) (KT : Set ℝ),
      (∀ j, IsOpen (KO j) ∧ IsPreconnected (KO j) ∧ lo j ∈ KO j ∧ hi j ∈ KO j) →
      (∀ i, IsOpen (KS i) ∧ IsPreconnected (KS i) ∧ hi (jn i) ∈ KS i ∧ lo (jo i) ∈ KS i) →
      IsOpen KT ∧ IsPreconnected KT ∧ hi jf ∈ KT ∧ v ∈ KT →
      (∀ j r, r ∈ KO j → T - r ^ 2 ∈ (DO j).regular) →
      (∀ i r, r ∈ KS i → T - r ^ 2 ∈ (DS i).regular) →
      (∀ r ∈ KT, T - r ^ 2 ∈ DT.regular) →
      (∀ z ∈ V, ordinary jl (z, lo jl) = gamma jl (lo jl)) →
      (∀ z ∈ V, ∀ i, ordinary (jo i) (z, lo (jo i)) =
        (survivor i (z, lo (jo i))).val.val) →
      (∀ z ∈ V, ∀ i, ordinary (jn i) (z, hi (jn i)) =
        FC i (survivor i (z, hi (jn i))).val) →
      (∀ z ∈ V, ordinary jf (z, hi jf) = tail (z, hi jf)) →
      (∀ j, EqOn (fun r => ordinary j (0, r)) (gamma j) (Icc (lo j) (hi j))) →
      (∀ i, EqOn (fun r => (survivor i (0, r)).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (survivor i (0, r)).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      EqOn (fun r => tail (0, r)) (gamma jf) (Icc (hi jf) v) →
    ∀ (Bframe : P ≃L[ℝ] ThreeSpace),
      (fun z => tail (z, v)) =ᶠ[𝓝 (0 : P)]
        (fun z => expMap (ST.base.metric (T - v ^ 2)) (gamma jf v)
          (show TangentSpace ThreeModel (gamma jf v) from Bframe z)) →
    let action : P × ℝ → ℝ := fun z =>
      H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
      (∑ j : Jstage, lRegularizedAction (SO j) T (fun r => ordinary j (z.1, r)) (lo j) (hi j)) +
      (∑ i : Eevent, lRegularizedAction (SS i) T (fun r => survivor i (z.1, r))
        (hi (jn i)) (lo (jo i))) +
      lRegularizedAction ST T (fun r => tail (z.1, r)) (hi jf) z.2;
    ∃ z : (H.event i).old,
      z.val.val = gamma jl 0 ∧
      (H.event i).oldOutput z = gammaFull ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0 ∧
    ∃ (Jclock : Set ℝ) (U : Set ((H.stage first).Carrier × ℝ))
      (psi : (H.stage first).Carrier × ℝ → P) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen Jclock ∧ v ∈ Jclock ∧ Jclock ⊆ KT ∧
      (∀ w ∈ Jclock, 0 < w ∧ hi jf < w ∧ T - w ^ 2 ∈ H.stageDomain first) ∧
      ContDiffOn ℝ 2 action (V ×ˢ KT) ∧
      IsOpen U ∧ (gamma jf v, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      psi (gamma jf v, v) = 0 ∧
      F (gamma jf v, v) = ∑ j : Jstage, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ∧
      H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) =
        (F (gamma jf v, v) : WithTop ℝ) ∧
      F (gamma jf v, v) = ∑ j : Jfull, H.stageRegularizedAction j.val T (gammaFull j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ∧
      H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ) T Bfloor 0 v
        (gammaFull ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) (gamma jf v) =
          (F (gamma jf v, v) : WithTop ℝ) ∧
      ∀ x ∈ U, psi x ∈ V ∧ x.2 ∈ Jclock ∧
        tail (psi x, x.2) = x.1 ∧ F x = action (psi x, x.2) ∧
        H.regularizedCost first last hle T Bfloor 0 x.2 (gamma jl 0) x.1 ≤
          (F x : WithTop ℝ) ∧
        H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ) T Bfloor 0 x.2
          (gammaFull ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) x.1 ≤
            (F x : WithTop ℝ) := by
  classical
  intro T last hle Jfull Jstage Eevent jo jn jf jl gammaFull hAC hInt hNodes hattain
    gamma lo hi hbounds hiv W FC DO DS DT SO SS ST hold hnew
    ordinary survivor tail hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew
    hOrd hSurv hTail V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
    hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail Bframe hexp action
  have hpastD : T - v ^ 2 ∈ H.stageDomain first := H.mem_stageDomain_of_mem_Ioo hpast
  have hpole : ∃ z : (H.event i).old,
      z.val.val = gamma jl 0 ∧
      (H.event i).oldOutput z = gammaFull ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0 := by
    simpa only [T, sub_self, Real.sqrt_zero] using hNodes i hf le_rfl
  obtain ⟨z, hzOld, hzNew⟩ := hpole
  obtain ⟨hreal, hExt, hOldAttain⟩ :=
    H.regularizedCost_attained_of_zero_pole_restriction first i hf hv.le hpastD
      gammaFull hAC hInt hNodes hscalar hattain z hzOld hzNew
  have hupper : T ∈ Ioc (H.time last) (H.stageEndTime last) := by
    change H.time i.succ ∈ Ioc (H.time i.castSucc) (H.stageEndTime i.castSucc)
    rw [H.stageEndTime_castSucc]
    exact ⟨H.time_strictMono i.castSucc_lt_succ, le_rfl⟩
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show T ∈ Icc (H.time last) (H.stageEndTime last) from ⟨hupper.1.le, hupper.2⟩)
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper0
  have hOldAC (j : Jstage) : Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) :=
    hAC ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
  have hOldInt (j : Jstage) : IntervalIntegrable
      (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) :=
    hInt ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
  have hlo0 : 0 ≤ lo jl := by
    simpa only [jl, hstart] using (hbounds jl).1
  have hloEnd : lo jl ≤ H.regularizedStageEnd T v last :=
    (hbounds jl).2.1.trans (hbounds jl).2.2
  have h0end : 0 ≤ H.regularizedStageEnd T v last := Real.sqrt_nonneg _
  have hprefixSubset : uIcc 0 (lo jl) ⊆
      uIcc (H.regularizedStageStart T 0 last) (H.regularizedStageEnd T v last) := by
    rw [hstart, uIcc_of_le hlo0, uIcc_of_le h0end]
    exact Icc_subset_Icc le_rfl hloEnd
  have hprefixAC : Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) :=
    Manifold.absolutelyContinuousOnInterval_mono (hOldAC jl) hprefixSubset
  obtain ⟨Jclock, U, psi, F, hJclock, hvJclock, hJKT, hJdomain, hAction,
      hU, hqU, hpsi, hF, hpsi0, hF0, hOldContact, hbranch⟩ :=
    H.exists_smooth_collar_cost_support first last hle hv hupper hpast Bfloor hscalar
      gamma lo hi hbounds hiv hprefixAC hOldInt hOldAttain
      W FC DO DS DT SO SS ST hold hnew ordinary survivor tail
      hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew hOrd hSurv hTail
      V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
      hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail Bframe hexp
  have hFfull : F (gamma jf v, v) = ∑ j : Jfull,
      H.stageRegularizedAction j.val T (gammaFull j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) :=
    hF0.trans hreal.symm
  have hNewContact : H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ) T Bfloor 0 v
      (gammaFull ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) (gamma jf v) =
        (F (gamma jf v, v) : WithTop ℝ) :=
    hattain.symm.trans (hExt.trans (hOldAttain.trans hOldContact))
  refine ⟨z, hzOld, hzNew, Jclock, U, psi, F, hJclock, hvJclock, hJKT, hJdomain,
    hAction, hU, hqU, hpsi, hF, hpsi0, hF0, hOldContact, hFfull, hNewContact, ?_⟩
  intro x hx
  obtain ⟨hz, hw, hend, hvalue, hOldBound⟩ := hbranch x hx
  have hcompare := H.regularizedCost_le_of_zero_pole first i hf Bfloor x.2 z x.1
  rw [hzOld, hzNew] at hcompare
  exact ⟨hz, hw, hend, hvalue, hOldBound, hcompare.trans hOldBound⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
