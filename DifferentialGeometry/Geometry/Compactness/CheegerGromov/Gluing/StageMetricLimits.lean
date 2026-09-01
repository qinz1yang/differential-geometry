import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.MetricLimits

import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.Convergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageComparison

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter
open scoped ContDiff Manifold Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

namespace BoundedGeometryNormalChartData

theorem exists_stage_metric
    (inp : MetricCompactCore (I := I) X)
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
        MapCInfConvOnCompacts V
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
        MapCInfConvOnCompacts (V alpha)
          (fun n => Φ alpha (τ (σ n))) g ∧ Q alpha g := by
    intro alpha τ hτ
    let index : Nat → Nat := fun n => L.φ (shift (τ n))
    let X' : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
    let d' : BoundedGeometryNormalChartData (I := I) X' (inp.decay.subseq index) :=
      d.subseq index
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
      have hphase := d.phaseRadius_metric (hcenter n).le
      change Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1)) ⊆
        Metric.ball 0
          (d'.ratio * (inp.decay.subseq index).mu
            ((inp.decay.subseq index).dist n (c n)
              (X'.obj n).basepoint))
      rw [← d'.radius_eq n (c n)]
      with_unfolding_all
        exact hphase
    obtain ⟨σ, g, hσ, hg, hconv, hequiv⟩ :=
      exists_chart_metric_limit_subsequence (I := I) d' c Metric.isOpen_ball hsub
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

theorem exists_stage_pair
    (inp : MetricCompactCore (I := I) X)
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
    let dphi : BoundedGeometryNormalChartData (I := I) Xphi
        (inp.decay.subseq index) := d.subseq index
    let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
      fun alpha n =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
    ∃ (deltaStage deltaInf : LiveSlot L inp.pack r → Real)
        (e : LiveSlot L inp.pack r →
          Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : LiveSlot L inp.pack r →
          OpenPartialHomeomorph (E × E) (E × E)),
      (∀ alpha, HasDiagPairConv (I := I) (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        (c alpha) (q alpha) (q alpha / 2)
        (deltaStage alpha) (deltaInf alpha) (e alpha) (eInf alpha)
        (chart := dphi.chart)) ∧
      ∀ alpha n, NormalDiagFence (I := I) (Xphi.obj n)
        (c alpha n) (q alpha) (e alpha n)
          (c := dphi.chart n (c alpha n)) ∧
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
  let Lphi := L.subseq hphi
  let index : Nat → Nat := fun n => Lphi.φ n
  let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
    X.subseq index
  let dphi : BoundedGeometryNormalChartData (I := I) Xphi
      (inp.decay.subseq index) := d.subseq index
  let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
    fun alpha n =>
      seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
  have hslot : ∀ alpha : LiveSlot L inp.pack r,
      ∃ (deltaStage deltaInf : Real)
          (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
          (eInf : OpenPartialHomeomorph (E × E) (E × E)),
        HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) (q alpha) (q alpha / 2)
          deltaStage deltaInf e eInf (chart := dphi.chart) ∧
        ∀ n, NormalDiagFence (I := I) (Xphi.obj n)
          (c alpha n) (q alpha) (e n)
            (c := dphi.chart n (c alpha n)) ∧
          ApproximatesLinearOn
            ((e n).symm : E × E → E × E)
            ((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))
            (e n).target
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))‖₊ *
              (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                  (E × E) →L[Real] (E × E))‖₊⁻¹ -
                PhaseFlow.phaseErr (d.phaseK (2 * q alpha)))⁻¹ *
              PhaseFlow.phaseErr (d.phaseK (2 * q alpha))) := by
    intro alpha
    let Ralpha := L.rInf (alpha.1 : Nat) + 1
    have hc : ∀ n,
        (inp.decay.subseq index).dist n (c alpha n)
          (Xphi.obj n).basepoint ≤ Ralpha := by
      intro n
      simpa only [Ralpha, index, Xphi, c, Lphi,
        InjectivityRadiusDecay.subseq, PointedRiemannianSeq.subseq] using
        hcenter n alpha
    obtain ⟨_hC1, hgInf, hconv, hequiv⟩ := hmetric alpha
    rw [hV alpha] at hgInf hconv hequiv
    have hgInf' : ContDiffOn Real ∞ (gInf alpha)
        (Metric.ball 0 (dphi.phaseRadius Ralpha)) := by
      with_unfolding_all
        exact hgInf
    have hconv' : MapCInfConvOnCompacts
        (Metric.ball 0 (dphi.phaseRadius Ralpha))
        (fun n ↦ dphi.chartMetric n (c alpha n)) (gInf alpha) := by
      with_unfolding_all
        exact hconv
    have hequiv' : ∀ z ∈ Metric.ball 0 (dphi.phaseRadius Ralpha),
        ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v := by
      intro z hz v
      have hz' : z ∈ Metric.ball 0 (d.phaseRadius Ralpha) := by
        with_unfolding_all
          exact hz
      exact (hequiv z hz' v).1
    rcases hqdata alpha with
      ⟨hq, hqWide, hqAcc, herr, hinvErr⟩
    exact dphi.exists_diagPair_at (hcomplete.subseq index)
      (PointedRiemannianSeq.connected_subseq hconn index)
      Ralpha (c alpha) hc (q alpha) hq
      (by with_unfolding_all exact hqWide)
      (by with_unfolding_all exact hqAcc)
      (by with_unfolding_all exact herr)
      (by with_unfolding_all exact hinvErr)
      hgInf' hequiv' hconv'
  choose deltaStage deltaInf e eInf hpair hfence using hslot
  exact ⟨deltaStage, deltaInf, e, eInf, hpair, hfence⟩

end BoundedGeometryNormalChartData

end HCGCompactness
end DifferentialGeometry
