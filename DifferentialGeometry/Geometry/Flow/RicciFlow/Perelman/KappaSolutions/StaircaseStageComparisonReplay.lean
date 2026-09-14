import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageComparison.MetricLimits
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseChartReplayBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseStageRegularityReplay

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter
open scoped ContDiff Manifold Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

namespace SeqBallNormalChartData

theorem exists_stage_metric
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    ∃ (psi : Nat → Nat)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      StrictMono psi ∧
      (∀ n (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi n))
          (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat))
          (X.obj (L.φ (psi n))).basepoint <
            L.rInf (alpha.1 : Nat) + 1) ∧
      ∀ alpha : LiveSlot L inp.pack r,
        let Ralpha := L.rInf (alpha.1 : Nat) + 1
        let V := Metric.ball (0 : E) (d.phaseRadius Ralpha)
        ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) V ∧
        MapCInfConvergenceOnCompacts V
          (fun n => d.chartMetric (L.φ (psi n))
            (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)))
          (gInf alpha) ∧
        ∀ z ∈ V, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
            gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (liveCenters_rInf (I := I) inp.decay P inp.realizes L inp.pack r)
  let shift : Nat → Nat := fun n => n + N
  have hshift : StrictMono shift := by
    simpa only [shift, id_eq] using strictMono_id.add_const N
  let V : LiveSlot L inp.pack r → Set E := fun alpha =>
    Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1))
  let Φ : LiveSlot L inp.pack r → Nat → E →
      (E →L[Real] E →L[Real] Real) := fun alpha n =>
    d.chartMetric (L.φ (shift n))
      (seqCenterD inp.decay P L (shift n) (alpha.1 : Nat))
  let Q : LiveSlot L inp.pack r →
      (E → (E →L[Real] E →L[Real] Real)) → Prop := fun alpha g =>
    ContDiffOn Real (∞ : WithTop ℕ∞) g (V alpha) ∧
      ∀ z ∈ V alpha, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ g z v v ∧
          g z v v ≤ 2 * ‖v‖ ^ 2
  have hstep : ∀ alpha (τ : Nat → Nat), StrictMono τ →
      ∃ (σ : Nat → Nat) (g : E → (E →L[Real] E →L[Real] Real)),
        StrictMono σ ∧
        MapCInfConvergenceOnCompacts (V alpha)
          (fun n => Φ alpha (τ (σ n))) g ∧ Q alpha g := by
    intro alpha τ hτ
    let index : Nat → Nat := fun n => L.φ (shift (τ n))
    let X' : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
    have hidx : ∀ j : Nat, j ≤ index j := by
      intro j
      have h1 : j ≤ shift (τ j) := by
        have htj : j ≤ τ j := hτ.id_le j
        simp only [shift]
        omega
      exact h1.trans (L.φ_mono.id_le (shift (τ j)))
    let d' : SeqBallNormalChartData (I := I) X' (inp.decay.subseq index) :=
      d.subseq index hidx
    let c : ∀ n : Nat, (X'.obj n).M := fun n =>
      seqCenterD inp.decay P L (shift (τ n)) (alpha.1 : Nat)
    have hcenter : ∀ n,
        inp.decay.dist (index n) (c n) (X'.obj n).basepoint <
          L.rInf (alpha.1 : Nat) + 1 := by
      intro n
      have hn : N ≤ shift (τ n) := by simp only [shift]; omega
      simpa only [index, X', c, PointedRiemannianSeq.subseq] using
        hN (shift (τ n)) hn alpha
    have hsub : ∀ n,
        V alpha ⊆ Metric.ball (0 : E)
          (d'.ratio * (inp.decay.subseq index).mu
            ((inp.decay.subseq index).dist n (c n)
              (X'.obj n).basepoint)) := by
      intro n
      let : TopologicalSpace (X'.obj n).M := (X'.obj n).topology
      let : ChartedSpace H (X'.obj n).M := (X'.obj n).charted
      let : IsManifold I ∞ (X'.obj n).M := (X'.obj n).smooth
      let : T2Space (TangentBundle I (X'.obj n).M) :=
        (X'.obj n).t2TangentBundle
      have hquarter := d'.phaseRadius_chart (I := I) (j := n) (x := c n)
        (R := L.rInf (alpha.1 : Nat) + 1) (hcenter n).le
      change Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1)) ⊆
        Metric.ball 0
          (d'.ratio * (inp.decay.subseq index).mu
            ((inp.decay.subseq index).dist n (c n)
              (X'.obj n).basepoint))
      rw [← d'.radius_eq n (c n)]
      exact hquarter.trans
        (Metric.ball_subset_ball (by linarith [(d'.chart n (c n)).radius_pos]))
    obtain ⟨σ, g, hσ, hg, hconv, hequiv⟩ :=
      d'.exists_chart_metric_limit_subsequence (I := I) (inp.realizes.subseq index)
        c (fun n => (hcenter n).le) Metric.isOpen_ball hsub
    refine ⟨σ, g, hσ, ?_, ?_⟩
    · with_unfolding_all
        exact hconv
    · simpa only [Q] using ⟨hg, hequiv⟩
  obtain ⟨psi0, hpsi0, hall⟩ :=
    exists_cInf_finite V Φ Q hstep
  choose gInf hconv hQ using hall
  let psi : Nat → Nat := shift ∘ psi0
  refine ⟨psi, gInf, hshift.comp hpsi0, ?_, ?_⟩
  · intro n alpha
    have hn : N ≤ shift (psi0 n) := by simp only [shift]; omega
    simpa only [psi, Function.comp_apply] using
      hN (shift (psi0 n)) hn alpha
  intro alpha
  have hconvAlpha := hconv alpha
  have hQAlpha := hQ alpha
  dsimp only [Q] at hQAlpha
  refine ⟨?_, ?_, ?_⟩
  · simpa only [V] using hQAlpha.1
  · simpa only [V, Φ, psi, Function.comp_apply] using hconvAlpha
  · simpa only [V] using hQAlpha.2

theorem of_boundedGeometryNormalChartData_exists_stage_metric
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    ∃ (psi : Nat → Nat)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      StrictMono psi ∧
      (∀ n (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi n))
          (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat))
          (X.obj (L.φ (psi n))).basepoint <
            L.rInf (alpha.1 : Nat) + 1) ∧
      ∀ alpha : LiveSlot L inp.pack r,
        let Ralpha := L.rInf (alpha.1 : Nat) + 1
        let V := Metric.ball (0 : E) (d.phaseRadius Ralpha)
        ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) V ∧
        MapCInfConvergenceOnCompacts V
          (fun n => d.chartMetric (L.φ (psi n))
            (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)))
          (gInf alpha) ∧
        ∀ z ∈ V, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
            gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
  simpa only [SeqBallNormalChartData.phaseRadius,
    BoundedGeometryNormalChartData.phaseRadius,
    BoundedGeometryNormalChartData.chartMetric,
    SeqBallNormalChartData.chartMetric,
    SeqBallNormalChartData.of_boundedGeometryNormalChartData]
    using exists_stage_metric (I := I) inp
      (SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d) P L r

def phaseK
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (n : Nat) (R : NNReal) : NNReal where
  val := (6 * (d.metricC n 1) ^ 2 + 3 * d.metricC n 2) * (R : Real) ^ 2 +
    6 * d.metricC n 1 * (R : Real)
  property := by
    have hA : 0 ≤ 6 * (d.metricC n 1) ^ 2 + 3 * d.metricC n 2 :=
      add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (d.metricC n 1)))
        (mul_nonneg (by norm_num) (d.metricC_nonneg n 2))
    exact add_nonneg
      (mul_nonneg hA (sq_nonneg (R : Real)))
      (mul_nonneg (mul_nonneg (by norm_num) (d.metricC_nonneg n 1))
        R.coe_nonneg)

theorem chartPhaseK_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M)
    (hn : hd.dist j x (X.obj j).basepoint ≤ n)
    (h1 : n + 1 ≤ j) (h2 : n + 2 ≤ j) (R : NNReal) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) :=
       (X.obj j).t2TangentBundle
     chartPhaseK (X.obj j).metric (d.metricBounds hreal x hn) R) = d.phaseK n R := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  apply NNReal.eq
  simp only [chartPhaseK, metricBounds, phaseK, h1, h2, if_true]

theorem exists_metricBounds_C_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n : Nat} (c : ∀ j : Nat, (X.obj j).M)
    (hc : ∀ j : Nat, hd.dist j (c j) (X.obj j).basepoint ≤ n) (q : Nat) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ j : Nat, (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
        letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
        letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
        letI : T2Space (TangentBundle I (X.obj j).M) :=
          (X.obj j).t2TangentBundle
        (d.metricBounds hreal (c j) (hc j)).C q) ≤ C := by
  classical
  let f : Nat → Real := fun j =>
    let : TopologicalSpace (X.obj j).M := (X.obj j).topology
    let : ChartedSpace H (X.obj j).M := (X.obj j).charted
    let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    (d.metricBounds hreal (c j) (hc j)).C q
  let S : Finset Nat := Finset.range (n + q + 1)
  have h0 : S.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  refine ⟨max (d.metricC n q) (S.sup' h0 f), ?_, ?_⟩
  · exact (d.metricC_nonneg n q).trans (le_max_left _ _)
  · intro j
    rcases lt_or_ge j (n + q) with hj | hj
    · have hle : f j ≤ S.sup' h0 f := by
        rw [Finset.le_sup'_iff]
        exact ⟨j, Finset.mem_range.mpr (by omega), le_rfl⟩
      exact hle.trans (le_max_right _ _)
    · have hC : f j = d.metricC n q := by
        simp only [f, metricBounds, hj, if_true]
      exact hC.le.trans (le_max_left _ _)

end SeqBallNormalChartData

namespace SeqBallNormalChartData

theorem exists_stage_pair
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (V C1 : LiveSlot L inp.pack r → Set E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hV : ∀ alpha, V alpha =
      Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1)))
    (hcenter : ∀ n (alpha : LiveSlot L inp.pack r),
      inp.decay.dist ((L.subseq hphi).φ n)
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (X.obj ((L.subseq hphi).φ n)).basepoint ≤
          L.rInf (alpha.1 : Nat) + 1)
    (hmetric : HasStageMetricOn inp P L phi hphi d.chart V C1 gInf)
    (q : LiveSlot L inp.pack r → NNReal)
    (hqdata : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      0 < q alpha ∧
      6 * (q alpha : Real) < d.phaseRadius Ralpha ∧
      3 * CB 1 * (2 * (q alpha : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q alpha : Real) ∧
      PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q alpha)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q alpha)))⁻¹ *
          PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q alpha)) < 1 / 24) :
    let Lphi := L.subseq hphi
    let index : Nat → Nat := fun n => Lphi.φ n
    let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
      X.subseq index
    let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
      fun alpha n =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
    ∃ (deltaStage deltaInf : LiveSlot L inp.pack r → Real)
        (e : LiveSlot L inp.pack r →
          Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : LiveSlot L inp.pack r →
          OpenPartialHomeomorph (E × E) (E × E)),
      (∀ alpha, HasDiagPairConvergence (I := I) (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        (c alpha) (q alpha) (q alpha / 2)
        (deltaStage alpha) (deltaInf alpha) (e alpha) (eInf alpha)
        (chart := fun k x => d.chart (index k) x)) ∧
      ∀ alpha n, NormalDiagFence (I := I) (Xphi.obj n)
        (c alpha n) (q alpha) (e alpha n)
          (c := d.chart (index n) (c alpha n)) ∧
        ApproximatesLinearOn
          ((e alpha n).symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))
          (e alpha n).target
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q alpha)))⁻¹ *
            PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q alpha))) := by
  classical
  let db : BoundedGeometryNormalChartData (I := I) X inp.decay :=
    { ratio := d.ratio
      ratio_pos := d.ratio_pos
      ratio_mu0_le := d.ratio_mu0_le
      chart := d.chart
      radius_eq := d.radius_eq
      hom_eq := d.hom_eq
      metricC := CB
      metricC_nonneg := hCB
      metric_equiv := by
        intro k x
        let : TopologicalSpace (X.obj k).M := (X.obj k).topology
        let : ChartedSpace H (X.obj k).M := (X.obj k).charted
        let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        let : T2Space (TangentBundle I (X.obj k).M) :=
          (X.obj k).t2TangentBundle
        obtain ⟨b, hrad, _hC⟩ := hunif k x
        simpa only [hrad] using b.equiv
      metric_deriv := by
        intro k p x
        let : TopologicalSpace (X.obj k).M := (X.obj k).topology
        let : ChartedSpace H (X.obj k).M := (X.obj k).charted
        let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        let : T2Space (TangentBundle I (X.obj k).M) :=
          (X.obj k).t2TangentBundle
        obtain ⟨b, hrad, hC⟩ := hunif k x
        intro z hz
        exact (b.deriv p z (by simpa only [hrad] using hz)).trans (hC p) }
  have hphase : ∀ R : NNReal, phaseKOf CB hCB R = db.phaseK R := by
    intro R
    apply NNReal.eq
    rfl
  have hqdata' : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      0 < q alpha ∧
      6 * (q alpha : Real) < db.phaseRadius Ralpha ∧
      3 * db.metricC 1 * (2 * (q alpha : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q alpha : Real) ∧
      PhaseFlow.phaseErr (db.phaseK (2 * q alpha)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (db.phaseK (2 * q alpha)))⁻¹ *
          PhaseFlow.phaseErr (db.phaseK (2 * q alpha)) < 1 / 24 := by
    intro alpha
    obtain ⟨hq, hwide, hacc, herr, hinv⟩ := hqdata alpha
    refine ⟨hq, ?_, ?_, ?_, ?_⟩
    · simpa only [db, SeqBallNormalChartData.phaseRadius,
        BoundedGeometryNormalChartData.phaseRadius] using hwide
    · simpa only [db] using hacc
    · rw [← hphase (2 * q alpha)]
      exact herr
    · rw [← hphase (2 * q alpha)]
      exact hinv
  exact BoundedGeometryNormalChartData.exists_stage_pair inp db P L phi hphi
    hcomplete hconn V C1 gInf (by
      simpa only [db, SeqBallNormalChartData.phaseRadius,
        BoundedGeometryNormalChartData.phaseRadius] using hV)
    (by simpa only [db] using hcenter) (by simpa only [db] using hmetric)
    q hqdata'

theorem of_boundedGeometryNormalChartData_exists_stage_pair
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (V C1 : LiveSlot L inp.pack r → Set E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hV : ∀ alpha, V alpha =
      Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1)))
    (hcenter : ∀ n (alpha : LiveSlot L inp.pack r),
      inp.decay.dist ((L.subseq hphi).φ n)
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (X.obj ((L.subseq hphi).φ n)).basepoint ≤
          L.rInf (alpha.1 : Nat) + 1)
    (hmetric : HasStageMetricOn inp P L phi hphi d.chart V C1 gInf)
    (q : LiveSlot L inp.pack r → NNReal)
    (hqdata : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      0 < q alpha ∧
      6 * (q alpha : Real) < d.phaseRadius Ralpha ∧
      3 * d.metricC 1 * (2 * (q alpha : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q alpha : Real) ∧
      PhaseFlow.phaseErr (d.phaseK (2 * q alpha)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (d.phaseK (2 * q alpha)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q alpha)) < 1 / 24) :
    let Lphi := L.subseq hphi
    let index : Nat → Nat := fun n => Lphi.φ n
    let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
      X.subseq index
    let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
      fun alpha n =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
    ∃ (deltaStage deltaInf : LiveSlot L inp.pack r → Real)
        (e : LiveSlot L inp.pack r →
          Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : LiveSlot L inp.pack r →
          OpenPartialHomeomorph (E × E) (E × E)),
      (∀ alpha, HasDiagPairConvergence (I := I) (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        (c alpha) (q alpha) (q alpha / 2)
        (deltaStage alpha) (deltaInf alpha) (e alpha) (eInf alpha)
        (chart := fun k x => d.chart (index k) x)) ∧
      ∀ alpha n, NormalDiagFence (I := I) (Xphi.obj n)
        (c alpha n) (q alpha) (e alpha n)
          (c := d.chart (index n) (c alpha n)) ∧
        ApproximatesLinearOn
          ((e alpha n).symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))
          (e alpha n).target
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (d.phaseK (2 * q alpha)))⁻¹ *
            PhaseFlow.phaseErr (d.phaseK (2 * q alpha))) := by
  classical
  refine SeqBallNormalChartData.exists_stage_pair inp
    (SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d)
    d.metricC d.metricC_nonneg ?_ P L phi hphi hcomplete hconn V C1 gInf ?_ ?_ ?_ q ?_
  · intro j x
    let : TopologicalSpace (X.obj j).M := (X.obj j).topology
    let : ChartedSpace H (X.obj j).M := (X.obj j).charted
    let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    let : T2Space (TangentBundle I (X.obj j).M) :=
      (X.obj j).t2TangentBundle
    exact ⟨d.metricBounds j x, rfl, fun _p => le_rfl⟩
  · simpa only [SeqBallNormalChartData.of_boundedGeometryNormalChartData,
      SeqBallNormalChartData.phaseRadius,
      BoundedGeometryNormalChartData.phaseRadius] using hV
  · simpa only [SeqBallNormalChartData.of_boundedGeometryNormalChartData] using hcenter
  · simpa only [SeqBallNormalChartData.of_boundedGeometryNormalChartData,
      SeqBallNormalChartData.chartMetric,
      BoundedGeometryNormalChartData.chartMetric] using hmetric
  · intro alpha
    obtain ⟨hq, hwide, hacc, herr, hinv⟩ := hqdata alpha
    refine ⟨hq, hwide, ?_, ?_, ?_⟩
    · simpa only [SeqBallNormalChartData.of_boundedGeometryNormalChartData] using hacc
    · rw [show SeqBallNormalChartData.phaseKOf d.metricC d.metricC_nonneg
          (2 * q alpha) = d.phaseK (2 * q alpha) by
        apply NNReal.eq
        rfl]
      exact herr
    · rw [show SeqBallNormalChartData.phaseKOf d.metricC d.metricC_nonneg
          (2 * q alpha) = d.phaseK (2 * q alpha) by
        apply NNReal.eq
        rfl]
      exact hinv

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
