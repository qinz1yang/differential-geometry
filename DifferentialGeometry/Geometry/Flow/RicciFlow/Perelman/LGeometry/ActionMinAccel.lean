import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionBootstrap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionClassical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionMomentum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem lChart_min_accel
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L,
      T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAct S T a p) (sameTimeEnds u) u) :
    ∀ r ∈ Ioo (0 : Real) L,
      let alpha : Real → M := fun s =>
        (extChartAt I p).symm (u.toFun (s - a))
      covDerivAlong (I := I) (S.base.metric (T - (a + r) ^ 2))
          alpha (fun s => lVelocity (I := I) alpha s) (a + r) =
        lRegAccel S T (a + r) (alpha (a + r))
          (lVelocity (I := I) alpha (a + r)) := by
  obtain ⟨q, P, hqcont, hqae, hu1, huder, hP1, hPeq, hPder⟩ :=
    lChart_mom_c1 (I := I) S hS T a p hL u hreg hchart hmin
  have hEuler :=
    (lChart_weak_euler (I := I) S hS T a p hL u hreg hchart hmin).2
  obtain ⟨q1, hq1, _hq1ae, huder1⟩ :=
    lChartVel_c1 (I := I) S hS T a p hL u hreg hchart
      q hqcont hqae hEuler
  have hqq1 : EqOn q q1 (Icc (0 : Real) L) := by
    intro s hs
    exact (huder hs).symm.trans (huder1 hs)
  have hq1on : ContDiffOn Real 1 q (Icc (0 : Real) L) :=
    hq1.congr hqq1
  intro r hr
  have hrcc : r ∈ Icc (0 : Real) L := ⟨hr.1.le, hr.2.le⟩
  have hIcc : Icc (0 : Real) L ∈ nhds r :=
    mem_of_superset (Ioo_mem_nhds hr.1 hr.2) Ioo_subset_Icc_self
  have huAt : DifferentiableAt Real u.toFun r :=
    (hu1.differentiableOn (by norm_num) r hrcc).differentiableAt hIcc
  have huDeriv : deriv u.toFun r = q r := by
    rw [← derivWithin_of_mem_nhds hIcc]
    exact huder hrcc
  have hu : HasDerivAt u.toFun (q r) r :=
    huAt.hasDerivAt.congr_deriv huDeriv
  have hqAt : DifferentiableAt Real q r :=
    (hq1on.differentiableOn (by norm_num) r hrcc).differentiableAt hIcc
  have hPAt : DifferentiableAt Real P r :=
    (hP1.differentiableOn (by norm_num) r hrcc).differentiableAt hIcc
  have hPDeriv : deriv P r =
      (2 : Real) • lChartForceRep (I := I) S T a p u q r := by
    rw [← derivWithin_of_mem_nhds hIcc]
    exact hPder hrcc
  have hPHas : HasDerivAt P
      ((2 : Real) • lChartForceRep (I := I) S T a p u q r) r :=
    hPAt.hasDerivAt.congr_deriv hPDeriv
  let mom : Real → E := fun s =>
    chartGramOp (I := I) S.family p
      (T - (a + s) ^ 2, u.toFun s) (q s)
  have hPmom : P =ᶠ[nhds r] fun s => (2 : Real) • mom s := by
    exact hPeq.eventuallyEq_of_mem hIcc
  have htwo : HasDerivAt (fun s => (2 : Real) • mom s)
      ((2 : Real) • lChartForceRep (I := I) S T a p u q r) r :=
    hPHas.congr_of_eventuallyEq hPmom.symm
  have hmom : HasDerivAt mom
      (lChartForceRep (I := I) S T a p u q r) r := by
    convert htwo.const_smul (1 / 2 : Real) using 1
    · funext s
      simp only [Pi.smul_apply, smul_smul]
      norm_num
    · simp only [smul_smul]
      norm_num
  have hqDeriv : deriv q r =
      (lPhaseField S T p (a + r) (u.toFun r, q r)).2 :=
    (lChartEuler_iff (I := I) S hS T a p u q r
      (hreg r hrcc) (hchart hrcc) hu hqAt).mp (by
        simpa only [mom] using hmom.deriv)
  have hq : HasDerivAt q
      (lPhaseField S T p (a + r) (u.toFun r, q r)).2 r :=
    hqAt.hasDerivAt.congr_deriv hqDeriv
  let z : Real → E × E := fun s => (u.toFun (s - a), q (s - a))
  let alpha : Real → M := lPhaseCurve (I := I) p z
  let A : ∀ s, TangentSpace I (alpha s) := lPhaseVel (I := I) p z
  have hshift : HasDerivAt (fun s : Real => s - a) 1 (a + r) := by
    simpa using (hasDerivAt_id (x := a + r)).sub_const a
  have har : a + r - a = r := by ring
  have hu' : HasDerivAt u.toFun (q r) (a + r - a) := by
    simpa only [har] using hu
  have huShift : HasDerivAt (fun s => u.toFun (s - a)) (q r) (a + r) := by
    have h := hu'.scomp (a + r) hshift
    rw [one_smul] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hq' : HasDerivAt q
      (lPhaseField S T p (a + r) (u.toFun r, q r)).2 (a + r - a) := by
    simpa only [har] using hq
  have hqShift : HasDerivAt (fun s => q (s - a))
      (lPhaseField S T p (a + r) (u.toFun r, q r)).2 (a + r) := by
    have h := hq'.scomp (a + r) hshift
    rw [one_smul] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hz : HasDerivAt z (lPhaseField S T p (a + r) (z (a + r)))
      (a + r) := by
    have hpair := huShift.prodMk hqShift
    have hzval : z (a + r) = (u.toFun r, q r) := by
      simp only [z, har]
    rw [hzval]
    exact hpair.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hzpos : (z (a + r)).1 ∈
      interior (extChartAt I p).target := by
    simpa only [z, har] using hchart hrcc
  have hphase := lPhase_accel (I := I) S T p z (a + r) hz hzpos
  have hvel : EqOn (fun s => lVelocity (I := I) alpha s) A
      (Ioo a (a + L)) := by
    intro s hs
    have hsLocal : s - a ∈ Ioo (0 : Real) L := by
      constructor <;> linarith [hs.1, hs.2]
    have hscc : s - a ∈ Icc (0 : Real) L :=
      ⟨hsLocal.1.le, hsLocal.2.le⟩
    have hsIcc : Icc (0 : Real) L ∈ nhds (s - a) :=
      mem_of_superset (Ioo_mem_nhds hsLocal.1 hsLocal.2)
        Ioo_subset_Icc_self
    have husAt : DifferentiableAt Real u.toFun (s - a) :=
      (hu1.differentiableOn (by norm_num) (s - a) hscc).differentiableAt hsIcc
    have husDeriv : deriv u.toFun (s - a) = q (s - a) := by
      rw [← derivWithin_of_mem_nhds hsIcc]
      exact huder hscc
    have hus : HasDerivAt u.toFun (q (s - a)) (s - a) :=
      husAt.hasDerivAt.congr_deriv husDeriv
    have hsShift : HasDerivAt (fun x : Real => x - a) 1 s := by
      simpa using (hasDerivAt_id (x := s)).sub_const a
    have hzs : HasDerivAt (fun x : Real => (z x).1) (z s).2 s := by
      have h := hus.scomp s hsShift
      rw [one_smul] at h
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
    have hzchart : (z s).1 ∈ interior (extChartAt I p).target := by
      simpa only [z] using hchart hscc
    change lVelocity (I := I) (lPhaseCurve (I := I) p z) s =
      lPhaseVel (I := I) p z s
    exact lPhase_velocity (I := I) p z s hzs hzchart
  have harIoo : a + r ∈ Ioo a (a + L) := by
    constructor <;> linarith [hr.1, hr.2]
  have hfield : (fun s => lVelocity (I := I) alpha s) =ᶠ[nhds (a + r)] A :=
    hvel.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds harIoo)
  change covDerivAlong (I := I) (S.base.metric (T - (a + r) ^ 2))
      alpha (fun s => lVelocity (I := I) alpha s) (a + r) =
    lRegAccel S T (a + r) (alpha (a + r))
      (lVelocity (I := I) alpha (a + r))
  calc
    covDerivAlong (I := I) (S.base.metric (T - (a + r) ^ 2))
        alpha (fun s => lVelocity (I := I) alpha s) (a + r) =
      covDerivAlong (I := I) (S.base.metric (T - (a + r) ^ 2))
        alpha A (a + r) :=
      covDerivAlong_congr_of_eventuallyEq
        (I := I) (S.base.metric (T - (a + r) ^ 2)) alpha hfield
    _ = lRegAccel S T (a + r) (alpha (a + r)) (A (a + r)) := by
      simpa only [alpha, A] using hphase
    _ = lRegAccel S T (a + r) (alpha (a + r))
        (lVelocity (I := I) alpha (a + r)) := by
      rw [hfield.eq_of_nhds]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
