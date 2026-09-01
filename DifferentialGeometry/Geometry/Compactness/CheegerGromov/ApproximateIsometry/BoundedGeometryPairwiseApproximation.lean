import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Construction


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricCarrier
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricCarrierHigherRegularity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageComparisonHigherRegularity

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff Manifold

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private theorem cast_preapprox
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (i j K L' : Nat) (hi : L.φ i = K) (hj : L.φ j = L')
    (r R ε : Real) (p : Nat)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X)
    (hnative :
      let Yi := X.obj (L.φ i)
      let Yj := X.obj (L.φ j)
      letI : TopologicalSpace Yi.M := Yi.topology
      letI : ChartedSpace H Yi.M := Yi.charted
      letI : IsManifold I ∞ Yi.M := Yi.smooth
      letI : SigmaCompactSpace Yi.M := Yi.sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Yi.M := Yi.smooth
      letI : T2Space Yi.M := Yi.t2
      letI : TopologicalSpace Yj.M := Yj.topology
      letI : ChartedSpace H Yj.M := Yj.charted
      letI : IsManifold I ∞ Yj.M := Yj.smooth
      letI : SigmaCompactSpace Yj.M := Yj.sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Yj.M := Yj.smooth
      letI : T2Space Yj.M := Yj.t2
      letI : MetricSpace Yi.M := (P (L.φ i)).ms
      letI : MetricSpace Yj.M := (P (L.φ j)).ms
      letI : Nonempty Yi.M := ⟨Yi.basepoint⟩
      let F₀ := stageComparisonMap inp P L s hs i j
        (chart := chart)
      Nonempty (MapMetricApproximationOn (I := I)
          (Metric.closedBall Yi.basepoint r) ε p F₀ Yi.metric Yj.metric) ∧
        Nonempty (MapMetricApproximationOn (I := I)
          (F₀ '' Metric.closedBall Yi.basepoint r) ε p
          (Function.invFunOn F₀ (Metric.ball Yi.basepoint R))
          Yj.metric Yi.metric)) :
    let YK := X.obj K
    let YL := X.obj L'
    letI : TopologicalSpace YK.M := YK.topology
    letI : ChartedSpace H YK.M := YK.charted
    letI : IsManifold I ∞ YK.M := YK.smooth
    letI : SigmaCompactSpace YK.M := YK.sigmaCompact
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) YK.M := YK.smooth
    letI : T2Space YK.M := YK.t2
    letI : TopologicalSpace YL.M := YL.topology
    letI : ChartedSpace H YL.M := YL.charted
    letI : IsManifold I ∞ YL.M := YL.smooth
    letI : SigmaCompactSpace YL.M := YL.sigmaCompact
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) YL.M := YL.smooth
    letI : T2Space YL.M := YL.t2
    letI : MetricSpace YK.M := (P K).ms
    letI : MetricSpace YL.M := (P L').ms
    letI : Nonempty YK.M := ⟨YK.basepoint⟩
    let F := stageMapCast inp P L s hs i j K L' hi hj
      (chart := chart)
    Nonempty (MapMetricApproximationOn (I := I)
        (Metric.closedBall YK.basepoint r) ε p F YK.metric YL.metric) ∧
      Nonempty (MapMetricApproximationOn (I := I)
        (F '' Metric.closedBall YK.basepoint r) ε p
        (Function.invFunOn F (Metric.ball YK.basepoint R))
        YL.metric YK.metric) := by
  subst K
  subst L'
  simpa only [stageMapCast] using hnative

theorem MetricCompactBase.exists_pairwise_approximate_isometry_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
      fun j => properMetricOn (I := I) (X.obj j)
        (hcomplete.complete j) (hconn j)
    ∃ psi : Nat → Nat, StrictMono psi ∧
      let Xpsi := X.subseq psi
      let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) (Xpsi.obj k) :=
        fun k => P (psi k)
      PairwiseApproximateIsometryInput (I := I) (X := Xpsi) Ppsi := by
  classical
  dsimp only
  obtain ⟨inp, L0, hseed, psi, hpsi, htail⟩ :=
    b.exists_stage_diag hcomplete hconn
  refine ⟨psi, hpsi, ?_⟩
  refine { comparison := ?_ }
  intro r hr ε hε hε1 p
  let gap := (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0
  let Smid := r + 1 / 2
  let R := r + 1
  let R1 := R + gap + 1
  let q := Nat.ceil R1 + 1
  have hrR : r < R := by
    dsimp only [R]
    linarith
  have hrS : r < Smid := by
    dsimp only [Smid]
    norm_num
  have hSR : Smid < R := by
    dsimp only [Smid, R]
    norm_num
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact mul_pos (by positivity) (inp.decay.lambda_pos inp.hD 0)
  have hroom : R + gap < R1 := by
    dsimp only [R1]
    linarith
  have hR1q : R1 < (q : Real) := by
    have hceil := Nat.le_ceil R1
    dsimp only [q]
    push_cast
    linarith
  obtain ⟨rho, hrho, hindex, hstage, N, hNq, hgeom⟩ :=
    HasRadiusTail.geom_tail inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) L0
      hcomplete.complete hconn hseed psi q (htail q) R R1 hroom hR1q
  let Sstate := stageStates inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) L0 hconn hseed q
  let d := radiusPayload inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) L0 hconn hseed q
  let Lbase := L0.subseq Sstate.sigma_strict
  obtain ⟨Nm, hmetric⟩ :=
    hstage.preapprox_tail inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) Lbase
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      hcomplete.complete hconn d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf
      hrS hSR hroom hR1q p ε hε hε1
  let Nall := max N (q + Nm)
  refine ⟨Nall, ?_⟩
  intro k l hk hl
  let : MetricSpace ((X.subseq psi).obj k).M :=
    ((properMetricsOfCompleteConnected (I := I) hcomplete hconn) (psi k)).ms
  let : MetricSpace ((X.subseq psi).obj l).M :=
    ((properMetricsOfCompleteConnected (I := I) hcomplete hconn) (psi l)).ms
  let Lq := Lbase.subseq (d.phi_strict.comp hrho)
  have hkGeom : N ≤ k := (Nat.le_max_left _ _).trans hk
  have hlGeom : N ≤ l := (Nat.le_max_left _ _).trans hl
  have hkMetric : q + Nm ≤ k := (Nat.le_max_right _ _).trans hk
  have hlMetric : q + Nm ≤ l := (Nat.le_max_right _ _).trans hl
  let hkq : q ≤ k := hNq.trans hkGeom
  let hlq : q ≤ l := hNq.trans hlGeom
  have hkNative : Nm ≤ k - q := by omega
  have hlNative : Nm ≤ l - q := by omega
  let hki : Lq.φ (k - q) = psi k :=
    (hindex (k - q)).trans (congrArg psi (Nat.add_sub_of_le hkq))
  let hli : Lq.φ (l - q) = psi l :=
    (hindex (l - q)).trans (congrArg psi (Nat.add_sub_of_le hlq))
  let F : (X.obj (psi k)).M → (X.obj (psi l)).M :=
    stageMapCast inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) Lq q
      (Nat.cast_nonneg q) (k - q) (l - q) (psi k) (psi l) hki hli
  have hgeomKL := hgeom k hkGeom l hlGeom
  have hnative := hmetric (k - q) hkNative (l - q) hlNative
  have hpair := cast_preapprox inp (properMetricsOfCompleteConnected (I := I) hcomplete hconn) Lq q
    (Nat.cast_nonneg q) (k - q) (l - q) (psi k) (psi l)
    hki hli r R ε p (chart := c2RadiusNormalChartFamily (I := I) X) hnative
  refine ⟨R, hrR, F, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact hgeomKL.1 ⟨x, Metric.ball_subset_closedBall x.property⟩
  · intro x hx y hy hxy
    exact hgeomKL.2.1 (Metric.ball_subset_closedBall hx)
      (Metric.ball_subset_closedBall hy) hxy
  · exact hgeomKL.2.2
  · exact hpair.1
  · exact hpair.2

theorem BoundedGeometryNormalData.pairwise_approximate_isometry_input_of_diagonal_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L0 : NetLimitData inp.decay inp.D P)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeedOn inp P L0 d.chart)
    (psi : Nat → Nat)
    (htail : ∀ q : Nat,
      HasRadiusTailOn inp P L0 hconn d.chart hseed psi q) :
    let Xpsi := X.subseq psi
    let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) (Xpsi.obj k) :=
      fun k => P (psi k)
    PairwiseApproximateIsometryInput (I := I) (X := Xpsi) Ppsi := by
  classical
  dsimp only
  refine { comparison := ?_ }
  intro r hr ε hε hε1 p
  let gap := (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0
  let Smid := r + 1 / 2
  let R := r + 1
  let R1 := R + gap + 1
  let q := Nat.ceil R1 + 1
  have hrR : r < R := by
    dsimp only [R]
    linarith
  have hrS : r < Smid := by
    dsimp only [Smid]
    norm_num
  have hSR : Smid < R := by
    dsimp only [Smid, R]
    norm_num
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact mul_pos (by positivity) (inp.decay.lambda_pos inp.hD 0)
  have hroom : R + gap < R1 := by
    dsimp only [R1]
    linarith
  have hR1q : R1 < (q : Real) := by
    have hceil := Nat.le_ceil R1
    dsimp only [q]
    push_cast
    linarith
  obtain ⟨rho, hrho, hindex, hstage, N, hNq, hgeom⟩ :=
    HasRadiusTailOn.geom_tail inp d P L0 hcomplete.complete hconn hseed psi q
      (htail q) R R1 hroom hR1q
  let Sstate := stageStatesOn inp P L0 hconn d.chart hseed q
  let a := radiusPayloadOn inp P L0 hconn d.chart hseed q
  let Lbase := L0.subseq Sstate.sigma_strict
  obtain ⟨Nm, hmetric⟩ :=
    d.preapprox_tail inp P Lbase (Nat.cast_nonneg q)
      (a.phi ∘ rho) (a.phi_strict.comp hrho) hcomplete.complete hconn
      a.V a.U a.C0 a.C1 a.aInf a.Jinf a.Jbarinf a.gInf hstage
      hrS hSR hroom hR1q p ε hε hε1
  let Nall := max N (q + Nm)
  refine ⟨Nall, ?_⟩
  intro k l hk hl
  let : MetricSpace ((X.subseq psi).obj k).M := (P (psi k)).ms
  let : MetricSpace ((X.subseq psi).obj l).M := (P (psi l)).ms
  let Lq := Lbase.subseq (a.phi_strict.comp hrho)
  have hkGeom : N ≤ k := (Nat.le_max_left _ _).trans hk
  have hlGeom : N ≤ l := (Nat.le_max_left _ _).trans hl
  have hkMetric : q + Nm ≤ k := (Nat.le_max_right _ _).trans hk
  have hlMetric : q + Nm ≤ l := (Nat.le_max_right _ _).trans hl
  let hkq : q ≤ k := hNq.trans hkGeom
  let hlq : q ≤ l := hNq.trans hlGeom
  have hkNative : Nm ≤ k - q := by omega
  have hlNative : Nm ≤ l - q := by omega
  let hki : Lq.φ (k - q) = psi k :=
    (hindex (k - q)).trans (congrArg psi (Nat.add_sub_of_le hkq))
  let hli : Lq.φ (l - q) = psi l :=
    (hindex (l - q)).trans (congrArg psi (Nat.add_sub_of_le hlq))
  let F : (X.obj (psi k)).M → (X.obj (psi l)).M :=
    stageMapCast inp P Lq q (Nat.cast_nonneg q)
      (k - q) (l - q) (psi k) (psi l) hki hli (chart := d.chart)
  have hgeomKL := hgeom k hkGeom l hlGeom
  have hnative := hmetric (k - q) hkNative (l - q) hlNative
  have hpair := cast_preapprox inp P Lq q (Nat.cast_nonneg q)
    (k - q) (l - q) (psi k) (psi l) hki hli r R ε p
    (chart := d.chart) hnative
  refine ⟨R, hrR, F, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact hgeomKL.1 ⟨x, Metric.ball_subset_closedBall x.property⟩
  · intro x hx y hy hxy
    exact hgeomKL.2.1 (Metric.ball_subset_closedBall hx)
      (Metric.ball_subset_closedBall hy) hxy
  · exact hgeomKL.2.2
  · exact hpair.1
  · exact hpair.2

theorem MetricCompactSeed.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
      fun j => properMetricOn (I := I) (X.obj j)
        (hcomplete.complete j) (hconn j)
    ∃ psi : Nat → Nat, StrictMono psi ∧
      let Xpsi := X.subseq psi
      let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) (Xpsi.obj k) :=
        fun k => P (psi k)
      PairwiseApproximateIsometryInput (I := I) (X := Xpsi) Ppsi := by
  classical
  dsimp only
  let aMin := d.stageScale b.realizes hcomplete hconn
  have haMin : 0 < aMin :=
    d.stageScale_pos b.realizes hcomplete hconn
  let c0 := 8 * Real.exp b.decay.C / aMin
  obtain ⟨D, hD, hcap, _hD_one, _hmuD, hc0⟩ := b.exists_core c0
  let inp := b.withDivisor D hD hcap
  have haMin' :
      0 < d.stageScale inp.realizes hcomplete hconn := by
    simpa only [MetricCompactSeed.withDivisor, aMin] using haMin
  have hc0' :
      (8 * Real.exp inp.decay.C /
          d.stageScale inp.realizes hcomplete hconn) < inp.D := by
    change 8 * Real.exp b.decay.C / aMin < D at hc0
    change 8 * Real.exp b.decay.C / aMin < D
    exact hc0
  have hphys :
      8 * Real.exp inp.decay.C <
        d.stageScale inp.realizes hcomplete hconn * inp.D := by
    simpa only [mul_comm] using (div_lt_iff₀ haMin').1 hc0'
  let P := properMetricsOfCompleteConnected (I := I) hcomplete hconn
  obtain ⟨L0, hstable⟩ := inp.exists_stable_net P
  obtain ⟨hseed, psi, hpsi, htail⟩ :=
    d.stage_diag inp hcomplete hconn hphys P L0 hstable
  refine ⟨psi, hpsi, ?_⟩
  exact d.pairwise_approximate_isometry_input_of_diagonal_data inp P L0 hcomplete hconn hseed psi htail

theorem MetricCompactBase.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
      fun j => properMetricOn (I := I) (X.obj j)
        (hcomplete.complete j) (hconn j)
    ∃ psi : Nat → Nat, StrictMono psi ∧
      let Xpsi := X.subseq psi
      let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) (Xpsi.obj k) :=
        fun k => P (psi k)
      PairwiseApproximateIsometryInput (I := I) (X := Xpsi) Ppsi := by
  exact b.toSeed.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry d hcomplete hconn

end HCGCompactness
end DifferentialGeometry
