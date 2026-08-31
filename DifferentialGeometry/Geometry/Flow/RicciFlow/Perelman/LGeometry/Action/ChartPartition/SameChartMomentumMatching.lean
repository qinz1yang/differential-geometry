import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.TwoPieceActionMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.PieceLocalMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Momentum
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Ramp
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Buffer
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeQuadraticBoundary

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set intervalIntegral
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
private theorem ramp_up_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (q P : Real → E)
    (hq : u.deriv =ᵐ[timeMeasure L] q)
    (hP : ContDiffOn Real 1 P (Icc (0 : Real) L))
    (hPeq : EqOn P
      (fun r ↦ (2 : Real) • chartGramOp (I := I) S.family p
        (T - (a + r) ^ 2, u.toFun r) (q r))
      (Icc (0 : Real) L))
    (hPF : EqOn (derivWithin P (Icc (0 : Real) L))
      (fun r ↦ (2 : Real) •
        lChartForceRep (I := I) S T a p u q r)
      (Icc (0 : Real) L)) (z : E)
    (hbuf : MapsTo
      (fun x : Real × Real ↦
        u.toFun x.2 + x.1 • (timeH1.rampUp L z).toFun x.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    HasDerivAt
      (fun c : Real ↦ lChartAct S T a p
        (u + c • timeH1.rampUp L z))
      (inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + L) ^ 2, u.toFun L) (q L)) z) 0 := by
  have hline := lChartAct_line (I := I) S hS T a p hL.le u
    (timeH1.rampUp L z) hreg hbuf
  have hForce := lChartForceRep_ae (I := I) S hS T a p u q
    hreg hchart hq
  have hsub : uIoc (0 : Real) L ⊆ Icc (0 : Real) L := by
    simpa only [uIcc_of_le hL.le] using
      (uIoc_subset_uIcc : uIoc (0 : Real) L ⊆ uIcc (0 : Real) L)
  have hq' : u.deriv =ᵐ[volume.restrict (uIoc (0 : Real) L)] q := by
    have hm := hq.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    simpa only [timeMeasure] using hm
  have hForce' : lChartForce (I := I) S T a p u
      =ᵐ[volume.restrict (uIoc (0 : Real) L)]
        lChartForceRep (I := I) S T a p u q := by
    have hm := hForce.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    simpa only [timeMeasure] using hm
  have hramp' : (timeH1.rampUp L z).deriv
      =ᵐ[volume.restrict (uIoc (0 : Real) L)]
        fun _ ↦ (1 / L) • z := by
    have hm := (timeH1.rampUp_deriv hL z).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    simpa only [timeMeasure] using hm
  have hbound := mom_ramp_up hL P
    (fun r ↦ (2 : Real) • lChartForceRep (I := I) S T a p u q r)
    hP hPF z
  have hint :
      (∫ r in (0 : Real)..L,
        inner Real (lChartForce (I := I) S T a p u r)
            ((timeH1.rampUp L z).toFun r) +
          inner Real
            (chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
            ((timeH1.rampUp L z).deriv r)) =
        inner Real
          (chartGramOp (I := I) S.family p
            (T - (a + L) ^ 2, u.toFun L) (q L)) z := by
    calc
      _ = (1 / 2 : Real) *
          ∫ r in (0 : Real)..L,
            (inner Real
                ((2 : Real) • lChartForceRep (I := I) S T a p u q r)
                ((r / L) • z) +
              inner Real (P r) ((1 / L) • z)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [hq', hForce', hramp',
          ae_restrict_mem measurableSet_uIoc] with r hqr hfr hvr hr
        have hr' : r ∈ Icc (0 : Real) L := hsub hr
        rw [timeH1.rampUp_apply hL.le z hr', hqr, hfr, hvr,
          hPeq hr']
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = (1 / 2 : Real) * inner Real (P L) z := by rw [hbound]
      _ = _ := by
        rw [hPeq ⟨hL.le, le_rfl⟩, real_inner_smul_left]
        ring
  convert hline using 1
  symm
  exact hint

omit [CompactSpace M] in
private theorem ramp_down_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (q P : Real → E)
    (hq : u.deriv =ᵐ[timeMeasure L] q)
    (hP : ContDiffOn Real 1 P (Icc (0 : Real) L))
    (hPeq : EqOn P
      (fun r ↦ (2 : Real) • chartGramOp (I := I) S.family p
        (T - (a + r) ^ 2, u.toFun r) (q r))
      (Icc (0 : Real) L))
    (hPF : EqOn (derivWithin P (Icc (0 : Real) L))
      (fun r ↦ (2 : Real) •
        lChartForceRep (I := I) S T a p u q r)
      (Icc (0 : Real) L)) (z : E)
    (hbuf : MapsTo
      (fun x : Real × Real ↦
        u.toFun x.2 + x.1 • (timeH1.rampDown L z).toFun x.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    HasDerivAt
      (fun c : Real ↦ lChartAct S T a p
        (u + c • timeH1.rampDown L z))
      (-inner Real
        (chartGramOp (I := I) S.family p
          (T - a ^ 2, u.toFun 0) (q 0)) z) 0 := by
  have hline := lChartAct_line (I := I) S hS T a p hL.le u
    (timeH1.rampDown L z) hreg hbuf
  have hForce := lChartForceRep_ae (I := I) S hS T a p u q
    hreg hchart hq
  have hsub : uIoc (0 : Real) L ⊆ Icc (0 : Real) L := by
    simpa only [uIcc_of_le hL.le] using
      (uIoc_subset_uIcc : uIoc (0 : Real) L ⊆ uIcc (0 : Real) L)
  have hq' : u.deriv =ᵐ[volume.restrict (uIoc (0 : Real) L)] q := by
    have hm := hq.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    simpa only [timeMeasure] using hm
  have hForce' : lChartForce (I := I) S T a p u
      =ᵐ[volume.restrict (uIoc (0 : Real) L)]
        lChartForceRep (I := I) S T a p u q := by
    have hm := hForce.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    simpa only [timeMeasure] using hm
  have hramp' : (timeH1.rampDown L z).deriv
      =ᵐ[volume.restrict (uIoc (0 : Real) L)]
        fun _ ↦ (-(1 / L)) • z := by
    have hm := (timeH1.rampDown_deriv hL z).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    simpa only [timeMeasure] using hm
  have hbound := mom_ramp_down hL P
    (fun r ↦ (2 : Real) • lChartForceRep (I := I) S T a p u q r)
    hP hPF z
  have hint :
      (∫ r in (0 : Real)..L,
        inner Real (lChartForce (I := I) S T a p u r)
            ((timeH1.rampDown L z).toFun r) +
          inner Real
            (chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
            ((timeH1.rampDown L z).deriv r)) =
        -inner Real
          (chartGramOp (I := I) S.family p
            (T - a ^ 2, u.toFun 0) (q 0)) z := by
    calc
      _ = (1 / 2 : Real) *
          ∫ r in (0 : Real)..L,
            (inner Real
                ((2 : Real) • lChartForceRep (I := I) S T a p u q r)
                (((L - r) / L) • z) +
              inner Real (P r) ((-(1 / L)) • z)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [hq', hForce', hramp',
          ae_restrict_mem measurableSet_uIoc] with r hqr hfr hvr hr
        have hr' : r ∈ Icc (0 : Real) L := hsub hr
        rw [timeH1.rampDown_apply hL.le z hr', hqr, hfr, hvr,
          hPeq hr']
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = (1 / 2 : Real) * (-inner Real (P 0) z) := by rw [hbound]
      _ = _ := by
        rw [hPeq ⟨le_rfl, hL.le⟩]
        simp only [add_zero, real_inner_smul_left]
        ring
  convert hline using 1
  symm
  exact hint

omit [CompactSpace M] in
theorem lChartAct_momentum_eq_of_pair_minimality
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (t : Fin 3 → Real) (p : M)
    (u : (i : Fin 2) → timeH1 E (partitionIntervalLength t i))
    (hpos : ∀ i : Fin 2, t i.castSucc < t i.succ)
    (hreg : ∀ i r, r ∈ Icc (0 : Real) (partitionIntervalLength t i) →
      T - (t i.castSucc + r) ^ 2 ∈ D.regular)
    (hchart : ∀ i, MapsTo (u i).toFun
      (Icc (0 : Real) (partitionIntervalLength t i))
      (interior (extChartAt I p).target))
    (hnode : (extChartAt I p).symm
        ((u 0).toFun (partitionIntervalLength t 0)) =
      (extChartAt I p).symm ((u 1).toFun 0))
    (hcmp : ∀ v : (i : Fin 2) → timeH1 E (partitionIntervalLength t i),
      (∀ i, MapsTo (v i).toFun
        (Icc (0 : Real) (partitionIntervalLength t i)) (extChartAt I p).target) →
      (extChartAt I p).symm ((v 0).toFun 0) =
        (extChartAt I p).symm ((u 0).toFun 0) →
      (extChartAt I p).symm ((v 1).toFun (partitionIntervalLength t 1)) =
        (extChartAt I p).symm ((u 1).toFun (partitionIntervalLength t 1)) →
      (extChartAt I p).symm ((v 0).toFun (partitionIntervalLength t 0)) =
        (extChartAt I p).symm ((v 1).toFun 0) →
      (∑ i : Fin 2, lChartAct S T (t i.castSucc) p (u i)) ≤
        ∑ i : Fin 2, lChartAct S T (t i.castSucc) p (v i)) :
    chartGramOp (I := I) S.family p
        (T - (t 1) ^ 2, (u 0).toFun (partitionIntervalLength t 0))
        (derivWithin (u 0).toFun
          (Icc (0 : Real) (partitionIntervalLength t 0)) (partitionIntervalLength t 0)) =
      chartGramOp (I := I) S.family p
        (T - (t 1) ^ 2, (u 1).toFun 0)
        (derivWithin (u 1).toFun
          (Icc (0 : Real) (partitionIntervalLength t 1)) 0) := by
  classical
  have hL (i : Fin 2) : 0 < partitionIntervalLength t i := by
    simpa only [partitionIntervalLength] using sub_pos.mpr (hpos i)
  have hlocal0 : IsLocalMinOn
      (lChartAct S T (t 0) p) (sameTimeEnds (u 0)) (u 0) :=
    lChartAct_isLocalMinOn_of_pair_minimality (I := I) S T t (fun _ ↦ p) u hchart hnode hcmp 0
  have hlocal1 : IsLocalMinOn
      (lChartAct S T (t 1) p) (sameTimeEnds (u 1)) (u 1) :=
    lChartAct_isLocalMinOn_of_pair_minimality (I := I) S T t (fun _ ↦ p) u hchart hnode hcmp 1
  obtain ⟨q0, P0, hq0c, hq0ae, hu0c1, hu0d, hP0c1, hP0eq, hP0d⟩ :=
    lChart_mom_c1 (I := I) S hS T (t 0) p (hL 0) (u 0)
      (hreg 0) (hchart 0) hlocal0
  obtain ⟨q1, P1, hq1c, hq1ae, hu1c1, hu1d, hP1c1, hP1eq, hP1d⟩ :=
    lChart_mom_c1 (I := I) S hS T (t 1) p (hL 1) (u 1)
      (hreg 1) (hchart 1) hlocal1
  apply ext_inner_right Real
  intro z
  have hnode' : (u 0).toFun (partitionIntervalLength t 0) = (u 1).toFun 0 := by
    calc
      (u 0).toFun (partitionIntervalLength t 0) =
          extChartAt I p ((extChartAt I p).symm
            ((u 0).toFun (partitionIntervalLength t 0))) :=
        ((extChartAt I p).right_inv
          (interior_subset (hchart 0 ⟨(hL 0).le, le_rfl⟩))).symm
      _ = extChartAt I p ((extChartAt I p).symm ((u 1).toFun 0)) :=
        congrArg (extChartAt I p) hnode
      _ = (u 1).toFun 0 :=
        (extChartAt I p).right_inv
          (interior_subset (hchart 1 ⟨le_rfl, (hL 1).le⟩))
  obtain ⟨s0, hs0, hs0one, hbuf0⟩ :=
    timeH1.exists_line_scale (u 0) (timeH1.rampUp (partitionIntervalLength t 0) z)
      isOpen_interior (hchart 0)
  obtain ⟨s1, hs1, hs1one, hbuf1⟩ :=
    timeH1.exists_line_scale (u 1)
      (timeH1.rampDown (partitionIntervalLength t 1) (s0 • z))
      isOpen_interior (hchart 1)
  let ze : E := (s1 * s0) • z
  have hbufUp : MapsTo
      (fun x : Real × Real ↦
        (u 0).toFun x.2 +
          x.1 • (timeH1.rampUp (partitionIntervalLength t 0) ze).toFun x.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) (partitionIntervalLength t 0))
      (interior (extChartAt I p).target) := by
    intro x hx
    have hxscale : x.1 * s1 ∈ Icc (-1 : Real) 1 := by
      constructor <;> nlinarith [hs1, hs1one, hx.1.1, hx.1.2]
    have hb := hbuf0 (x := ((x.1 * s1), x.2)) ⟨hxscale, hx.2⟩
    convert hb using 1
    dsimp only [ze]
    rw [mul_smul]
    rw [timeH1.rampUp_smul (hL 0) s1 (s0 • z),
      timeH1.rampUp_smul (hL 0) s0 z,
      timeH1.toFun_smul s1 (s0 • timeH1.rampUp (partitionIntervalLength t 0) z) hx.2,
      timeH1.toFun_smul s0 (timeH1.rampUp (partitionIntervalLength t 0) z) hx.2]
    simp only [smul_smul]
    congr 1
    ring_nf
  have hbufDown : MapsTo
      (fun x : Real × Real ↦
        (u 1).toFun x.2 +
          x.1 • (timeH1.rampDown (partitionIntervalLength t 1) ze).toFun x.2)
      (Icc (-1 : Real) 1 ×ˢ Icc (0 : Real) (partitionIntervalLength t 1))
      (interior (extChartAt I p).target) := by
    intro x hx
    have hb := hbuf1 (x := (x.1, x.2)) hx
    convert hb using 1
    dsimp only [ze]
    rw [mul_smul]
    rw [timeH1.rampDown_smul (hL 1) s1 (s0 • z),
      timeH1.toFun_smul s1
        (timeH1.rampDown (partitionIntervalLength t 1) (s0 • z)) hx.2]
  have hline0 := ramp_up_deriv (I := I) S hS T (t 0) p (hL 0)
    (u 0) (hreg 0) (hchart 0) q0 P0 hq0ae hP0c1 hP0eq hP0d ze hbufUp
  have hline1 := ramp_down_deriv (I := I) S hS T (t 1) p (hL 1)
    (u 1) (hreg 1) (hchart 1) q1 P1 hq1ae hP1c1 hP1eq hP1d ze hbufDown
  let phi : Real → Real := fun c ↦
    lChartAct S T (t 0) p
        (u 0 + c • timeH1.rampUp (partitionIntervalLength t 0) ze) +
      lChartAct S T (t 1) p
        (u 1 + c • timeH1.rampDown (partitionIntervalLength t 1) ze)
  have hphi : HasDerivAt phi
      (inner Real
          (chartGramOp (I := I) S.family p
            (T - (t 0 + partitionIntervalLength t 0) ^ 2,
              (u 0).toFun (partitionIntervalLength t 0))
            (q0 (partitionIntervalLength t 0))) ze -
        inner Real
          (chartGramOp (I := I) S.family p
            (T - (t 1) ^ 2, (u 1).toFun 0) (q1 0)) ze) 0 := by
    refine ((hline0.add hline1).congr_of_eventuallyEq
      (Eventually.of_forall fun _ ↦ rfl)).congr_deriv ?_
    rfl
  have hphimin : IsLocalMin phi 0 := by
    change ∀ᶠ c in nhds (0 : Real), phi 0 ≤ phi c
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : Real) < 0)
      (by norm_num : (0 : Real) < 1)] with c hc
    let w : (i : Fin 2) → timeH1 E (partitionIntervalLength t i) := fun i ↦
      Fin.cases
        (by simpa using u 0 + c • timeH1.rampUp (partitionIntervalLength t 0) ze)
        (Fin.cases
          (by simpa using u 1 + c • timeH1.rampDown (partitionIntervalLength t 1) ze)
          (fun j ↦ Fin.elim0 j)) i
    have hwtar : ∀ i, MapsTo (w i).toFun
        (Icc (0 : Real) (partitionIntervalLength t i)) (extChartAt I p).target := by
      intro i
      fin_cases i
      · intro r hr
        change (u 0 + c • timeH1.rampUp (partitionIntervalLength t 0) ze).toFun r ∈ _
        rw [timeH1.toFun_add (u 0)
          (c • timeH1.rampUp (partitionIntervalLength t 0) ze) hr,
          timeH1.toFun_smul c (timeH1.rampUp (partitionIntervalLength t 0) ze) hr]
        exact interior_subset (hbufUp (x := (c, r)) ⟨hc, hr⟩)
      · intro r hr
        change (u 1 + c • timeH1.rampDown (partitionIntervalLength t 1) ze).toFun r ∈ _
        rw [timeH1.toFun_add (u 1)
          (c • timeH1.rampDown (partitionIntervalLength t 1) ze) hr,
          timeH1.toFun_smul c (timeH1.rampDown (partitionIntervalLength t 1) ze) hr]
        exact interior_subset (hbufDown (x := (c, r)) ⟨hc, hr⟩)
    have hw0 : (extChartAt I p).symm ((w 0).toFun 0) =
        (extChartAt I p).symm ((u 0).toFun 0) := by
      rw [show w 0 = u 0 + c • timeH1.rampUp (partitionIntervalLength t 0) ze from rfl,
        timeH1.toFun_add _ _ ⟨le_rfl, (hL 0).le⟩,
        timeH1.toFun_smul _ _ ⟨le_rfl, (hL 0).le⟩,
        timeH1.rampUp_zero (hL 0), smul_zero, add_zero]
    have hw2 : (extChartAt I p).symm
        ((w 1).toFun (partitionIntervalLength t 1)) =
        (extChartAt I p).symm ((u 1).toFun (partitionIntervalLength t 1)) := by
      rw [show w 1 = u 1 + c • timeH1.rampDown (partitionIntervalLength t 1) ze from rfl,
        timeH1.toFun_add _ _ ⟨(hL 1).le, le_rfl⟩,
        timeH1.toFun_smul _ _ ⟨(hL 1).le, le_rfl⟩,
        timeH1.rampDown_end (hL 1), smul_zero, add_zero]
    have hwnode : (extChartAt I p).symm
        ((w 0).toFun (partitionIntervalLength t 0)) =
        (extChartAt I p).symm ((w 1).toFun 0) := by
      apply congrArg (extChartAt I p).symm
      rw [show w 0 = u 0 + c • timeH1.rampUp (partitionIntervalLength t 0) ze from rfl,
        show w 1 = u 1 + c • timeH1.rampDown (partitionIntervalLength t 1) ze from rfl,
        timeH1.toFun_add _ _ ⟨(hL 0).le, le_rfl⟩,
        timeH1.toFun_smul _ _ ⟨(hL 0).le, le_rfl⟩,
        timeH1.toFun_add _ _ ⟨le_rfl, (hL 1).le⟩,
        timeH1.toFun_smul _ _ ⟨le_rfl, (hL 1).le⟩,
        timeH1.rampUp_end (hL 0), timeH1.rampDown_zero (hL 1), hnode']
    have hc' := hcmp w hwtar hw0 hw2 hwnode
    simp only [Fin.sum_univ_two] at hc'
    rw [show w 0 = u 0 + c • timeH1.rampUp (partitionIntervalLength t 0) ze from rfl,
      show w 1 = u 1 + c • timeH1.rampDown (partitionIntervalLength t 1) ze from rfl] at hc'
    rw [show (0 : Fin 2).castSucc = (0 : Fin 3) by rfl,
      show (1 : Fin 2).castSucc = (1 : Fin 3) by
        apply Fin.ext
        rfl] at hc'
    simpa only [phi, zero_smul, add_zero] using hc'
  have hzero := hphimin.deriv_eq_zero
  rw [hphi.deriv] at hzero
  have hscale : 0 < s1 * s0 := mul_pos hs1 hs0
  have hinner : inner Real
      (chartGramOp (I := I) S.family p
        (T - (t 0 + partitionIntervalLength t 0) ^ 2,
          (u 0).toFun (partitionIntervalLength t 0)) (q0 (partitionIntervalLength t 0))) z =
      inner Real
        (chartGramOp (I := I) S.family p
          (T - (t 1) ^ 2, (u 1).toFun 0) (q1 0)) z := by
    simp only [ze, real_inner_smul_right] at hzero
    nlinarith
  have hend : t 0 + partitionIntervalLength t 0 = t 1 := by
    change t 0 + (t 1 - t 0) = t 1
    ring
  rw [hu0d ⟨(hL 0).le, le_rfl⟩, hu1d ⟨le_rfl, (hL 1).le⟩]
  simpa only [hend, add_zero, hnode'] using hinner

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
