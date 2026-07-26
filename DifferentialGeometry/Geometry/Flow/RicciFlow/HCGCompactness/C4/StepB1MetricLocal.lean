import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1MetricBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSourceBuffer

set_option autoImplicit false

/-!
# Local moving-source metric coefficients for Step B1

This file removes the fixed-patch source-stay premise from the chart
coefficient bridge by localizing a hypothetical bad sequence inside the
producer-owned uniformly buffered source cover.  It remains entirely at the
Euclidean coefficient level; the intrinsic covariant-tensor norm bridge is a
separate downstream theorem.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology
open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

private theorem mapDerivNorm_tri
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {f g h : E → F} {x : E} (j : Nat)
    (hf : ContDiffAt Real (∞ : WithTop ℕ∞) f x)
    (hg : ContDiffAt Real (∞ : WithTop ℕ∞) g x)
    (hh : ContDiffAt Real (∞ : WithTop ℕ∞) h x) :
    mapDerivNorm j f h x ≤ mapDerivNorm j f g x + mapDerivNorm j h g x := by
  have hfun : (fun y ↦ f y - h y) =
      (fun y ↦ f y - g y) - (fun y ↦ h y - g y) := by
    funext y
    simp only [Pi.sub_apply]
    abel
  rw [mapDerivNorm, hfun, iteratedFDeriv_sub_apply
    ((hf.sub hg).of_le (by exact_mod_cast le_top))
    ((hh.sub hg).of_le (by exact_mod_cast le_top))]
  exact norm_sub_le _ _

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- A coordinate center with a fixed closed-ball buffer inside the retained
core has one fixed pair of nested coordinate neighborhoods whose inverse
charts eventually remain in any prescribed larger source ball. -/
theorem HasSuppConvData.source_stay
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) {R S eta : Real}
    (hRS : R < S) (heta : 0 < eta)
    (kn : Nat → Nat) (z : Nat → E) (zInf : E)
    (hzconv : Tendsto z atTop (𝓝 zInf))
    (hbuffer : ∀ n, Metric.closedBall (z n) eta ⊆ interior (C0 alpha))
    (hsource : ∀ n,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      (NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm (z n) ∈
          Lphi.hatSourceBall inp.decay P R (kn n)) :
    ∃ q : Real, 0 < q ∧
      let V := Metric.ball zInf q
      let W := Metric.ball zInf (2 * q)
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ W ∧
        W ⊆ interior (C0 alpha) ∧
        ∀ᶠ n in atTop,
          let Lphi := L.subseq hphi
          let Yk := X.obj (Lphi.φ (kn n))
          letI : TopologicalSpace Yk.M := Yk.topology
          letI : ChartedSpace H Yk.M := Yk.charted
          letI : IsManifold I ∞ Yk.M := Yk.smooth
          letI : T2Space Yk.M := Yk.t2
          letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
          letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
          Set.MapsTo
            (NormalCoordinates.framedChartAt (I := I) Yk.metric
              (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
            W (Lphi.hatSourceBall inp.decay P S (kn n)) := by
  classical
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hIntU : interior (C0 alpha) ⊆ U alpha :=
    interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
  let q : Real := min (eta / 8) ((S - R) / 8)
  have hq : 0 < q := by
    dsimp only [q]
    exact lt_min (by positivity) (by linarith)
  have hqEta : q ≤ eta / 8 := min_le_left _ _
  have hqGap : q ≤ (S - R) / 8 := min_le_right _ _
  have hzclose : ∀ᶠ n in atTop, dist (z n) zInf < q := by
    rw [eventually_atTop]
    exact (Metric.tendsto_atTop.1 hzconv) q hq
  obtain ⟨Nclose, hNclose⟩ := eventually_atTop.mp hzclose
  have hclose0 : dist (z Nclose) zInf < q := hNclose Nclose le_rfl
  refine ⟨q, hq, Metric.isOpen_ball, ?_, ?_, ?_, ?_⟩
  · rw [closure_ball zInf hq.ne']
    exact isCompact_closedBall zInf q
  · rw [closure_ball zInf hq.ne']
    exact Metric.closedBall_subset_ball (by linarith)
  · intro w hw
    have hwz : dist w (z Nclose) < eta := by
      calc
        dist w (z Nclose) ≤ dist w zInf + dist zInf (z Nclose) :=
          dist_triangle _ _ _
        _ < 2 * q + q := by
          have hw' : dist w zInf < 2 * q := Metric.mem_ball.mp hw
          rw [dist_comm zInf (z Nclose)]
          exact add_lt_add hw' hclose0
        _ < eta := by linarith
    exact hbuffer Nclose (Metric.mem_closedBall.mpr hwz.le)
  · filter_upwards [hzclose] with n hn
    dsimp only
    let Lphi := L.subseq hphi
    let Yk := X.obj (Lphi.φ (kn n))
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
    let ck := seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat)
    let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric ck
    intro w hw
    have hwzq : dist w (z n) < 3 * q := by
      calc
        dist w (z n) ≤ dist w zInf + dist zInf (z n) := dist_triangle _ _ _
        _ < 2 * q + q := by
          have hw' : dist w zInf < 2 * q := Metric.mem_ball.mp hw
          rw [dist_comm zInf (z n)]
          exact add_lt_add hw' hn
        _ = 3 * q := by ring
    have hwz : dist w (z n) < eta := by linarith
    have hsegInt : segment Real w (z n) ⊆ interior (C0 alpha) := by
      refine (segment_subset_closedBall_right w (z n)).trans ?_
      exact (Metric.closedBall_subset_closedBall hwz.le).trans (hbuffer n)
    obtain ⟨hRad, hExp, _hMaps⟩ :=
      hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf (kn n) alpha
    have hEquiv : NormalCoordMetricEquivOn (I := I) Yk ck (U alpha) := by
      intro v hv xi
      exact inp.normalBounds.metric_equiv (Lphi.φ (kn n)) ck v (hRad hv) xi
    have hUtgt : U alpha ⊆ chiK.target := by
      intro v hv
      have hvBall := hExp hv
      rw [Metric.mem_ball, dist_zero_right] at hvBall
      change v ∈ (NormalCoordinates.framedExpDiffeo (I := I) Yk.metric ck).source
      rw [NormalCoordinates.framedExp_source]
      apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric ck
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yk.metric ck
      simpa only [NormalCoordinates.normalFrame_sqrt] using hvBall
    have hman := NormalCoordMetricEquivOn.symm_dist_le
      (I := I) Yk (P (Lphi.φ (kn n))) hEquiv hUtgt
        (hsegInt.trans hIntU)
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      linarith [Real.sqrt_two_lt_three_halves]
    have hlocal : dist (chiK.symm w) (chiK.symm (z n)) < S - R := by
      calc
        dist (chiK.symm w) (chiK.symm (z n)) ≤
            Real.sqrt 2 * dist w (z n) := by
          simpa only [chiK] using hman
        _ ≤ 2 * dist w (z n) :=
          mul_le_mul_of_nonneg_right hsqrt dist_nonneg
        _ < S - R := by linarith
    have hzSource : dist (chiK.symm (z n)) Yk.basepoint ≤ R := by
      simpa only [NetLimitData.hatSourceBall, Metric.mem_closedBall,
        chiK, ck, Yk, Lphi] using hsource n
    have hdist : dist (chiK.symm w) Yk.basepoint < S := by
      calc
        dist (chiK.symm w) Yk.basepoint ≤
            dist (chiK.symm w) (chiK.symm (z n)) +
              dist (chiK.symm (z n)) Yk.basepoint := dist_triangle _ _ _
        _ < (S - R) + R := add_lt_add_of_lt_of_le hlocal (by
          exact hzSource)
        _ = S := by ring
    change dist (chiK.symm w) Yk.basepoint ≤ S
    exact hdist.le

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- On one retained source patch with a fixed coordinate buffer, every finite
jet of the actual pulled-back target metric converges to the corresponding
source-stage normal metric, with one rectangular tail in the two stages. -/
theorem HasStageJetData.pb_buf_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (alpha : LiveSlot L inp.pack r) {R S eta : Real}
    (hRS : R < S) (hSr : S < r) (heta : 0 < eta)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    let Lphi := L.subseq hphi
    let A : Nat → Nat → E → E := fun k l z ↦
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
    let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun l ↦
      normalCoordMetric (I := I) (X.obj (Lphi.φ l))
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    let Q : Nat → Nat → E → (E →L[Real] E →L[Real] Real) :=
      fun k l z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B l (A k l z), fderiv Real (A k l) z)
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ z : E,
      Metric.closedBall z eta ⊆ interior (C0 alpha) →
      let Yk := X.obj (Lphi.φ k)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
        mapDerivNorm j (Q k l) (B k) z ≤ eps := by
  classical
  letI : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  dsimp only
  let Lphi := L.subseq hphi
  let A : Nat → Nat → E → E := fun k l z ↦
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
  let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun l ↦
    normalCoordMetric (I := I) (X.obj (Lphi.φ l))
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let Q : Nat → Nat → E → (E →L[Real] E →L[Real] Real) :=
    fun k l z ↦ _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (B l (A k l z), fderiv Real (A k l) z)
  change ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ z : E,
    Metric.closedBall z eta ⊆ interior (C0 alpha) →
    let Yk := X.obj (Lphi.φ k)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
      mapDerivNorm j (Q k l) (B k) z ≤ eps
  rcases hstage with ⟨hdata, hmetric, hjets, hbase⟩
  obtain ⟨hUopen, hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hIntU : interior (C0 alpha) ⊆ U alpha :=
    interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
  by_contra htail
  push Not at htail
  choose k hk l hl j hj z hbuffer hrest using htail
  have hrest' : ∀ n,
      let Yk := X.obj (Lphi.φ (k n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (k n))).ms
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (k n) (alpha.1 : Nat))
      chiK.symm (z n) ∈ Lphi.hatSourceBall inp.decay P R (k n) ∧
        eps < mapDerivNorm (j n) (Q (k n) (l n)) (B (k n)) (z n) := by
    intro n
    have hn := hrest n
    dsimp only at hn ⊢
    push Not at hn
    exact hn
  have hsource : ∀ n,
      let Yk := X.obj (Lphi.φ (k n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (k n))).ms
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (k n) (alpha.1 : Nat))
      chiK.symm (z n) ∈ Lphi.hatSourceBall inp.decay P R (k n) :=
    fun n ↦ (hrest' n).1
  have hbad : ∀ n,
      eps < mapDerivNorm (j n) (Q (k n) (l n)) (B (k n)) (z n) :=
    fun n ↦ (hrest' n).2
  have hzC0 : ∀ n, z n ∈ C0 alpha := by
    intro n
    exact interior_subset (hbuffer n (Metric.mem_closedBall_self heta.le))
  obtain ⟨zInf, _hzInf, ψ, hψ, hzconv⟩ :=
    hC0compact.tendsto_subseq hzC0
  let kn : Nat → Nat := fun n ↦ k (ψ n)
  let ln : Nat → Nat := fun n ↦ l (ψ n)
  let zn : Nat → E := fun n ↦ z (ψ n)
  have hkn : Tendsto kn atTop atTop :=
    (tendsto_atTop_mono hk tendsto_id).comp hψ.tendsto_atTop
  have hln : Tendsto ln atTop atTop :=
    (tendsto_atTop_mono hl tendsto_id).comp hψ.tendsto_atTop
  have hzn : Tendsto zn atTop (𝓝 zInf) := by
    simpa only [zn] using hzconv
  have hbuffer' : ∀ n, Metric.closedBall (zn n) eta ⊆
      interior (C0 alpha) := fun n ↦ hbuffer (ψ n)
  have hsource' : ∀ n,
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      (NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm (zn n) ∈
          Lphi.hatSourceBall inp.decay P R (kn n) := by
    intro n
    simpa only [kn, zn, Lphi] using hsource (ψ n)
  obtain ⟨q, hq, hVopen, hVcompact, hVW, hWint, hstay⟩ :=
    hdata.source_stay inp P L hr phi hphi U C0 C1 aInf Jinf Jbarinf
      alpha hRS heta kn zn zInf hzn hbuffer' hsource'
  let V : Set E := Metric.ball zInf q
  let W : Set E := Metric.ball zInf (2 * q)
  have hstay' : ∀ᶠ n in atTop,
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      Set.MapsTo
        (NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
        W (Lphi.hatSourceBall inp.decay P S (kn n)) := by
    simpa only [V, W, Lphi] using hstay
  have hQconv : MapCInfConvOnCompacts V
      (fun n ↦ Q (kn n) (ln n)) (gInf alpha) := by
    simpa only [V, W, Q, B, A, Lphi] using
      HasStageJetData.pb_conv (I := I) inp P L hr phi hphi hconn
        U C0 C1 aInf Jinf Jbarinf gInf
        ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha V W hVopen hVcompact
        hVW hWint kn ln hkn hln hstay'
  let K : Set E := Metric.closedBall zInf (q / 2)
  have hKcompact : IsCompact K := isCompact_closedBall zInf (q / 2)
  have hKV : K ⊆ V := by
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨hC1D, hgInf, hBconv, _hgEquiv⟩ := hmetric alpha
  have hKC1 : K ⊆ C1 alpha := by
    exact hKV.trans (subset_closure.trans (hVW.trans (hWint.trans
      (interior_subset.trans (hC01.trans interior_subset)))))
  have hKD : K ⊆ Metric.ball (0 : E)
      (inp.normalRadius.phaseRadius (L.rInf (alpha.1 : Nat) + 1)) :=
    hKC1.trans hC1D
  have hGconv : MapCInfConvOnCompacts
      (Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius (L.rInf (alpha.1 : Nat) + 1)))
      (fun n ↦ B (kn n)) (gInf alpha) := by
    simpa only [B, Lphi] using hBconv.comp_tendsto_atTop hkn
  obtain ⟨NQ, hNQ⟩ := hQconv K hKcompact hKV p (eps / 2) (by positivity)
  obtain ⟨NG, hNG⟩ := hGconv K hKcompact hKD p (eps / 2) (by positivity)
  obtain ⟨Nz, hNz⟩ := Metric.tendsto_atTop.1 hzn (q / 2) (by positivity)
  obtain ⟨Njet, hNjet⟩ := hjets S hSr 0 (eta / 2) (by positivity)
  let n := max (max NQ NG) (max Nz Njet)
  have hnQ : NQ ≤ n := (le_max_left NQ NG).trans (le_max_left _ _)
  have hnG : NG ≤ n := (le_max_right NQ NG).trans (le_max_left _ _)
  have hnZ : Nz ≤ n := (le_max_left Nz Njet).trans (le_max_right _ _)
  have hnJet : Njet ≤ n := (le_max_right Nz Njet).trans (le_max_right _ _)
  have hnψ : n ≤ ψ n := hψ.id_le n
  have hkJet : Njet ≤ kn n := by
    exact hnJet.trans (hnψ.trans (by simpa only [kn] using hk (ψ n)))
  have hlJet : Njet ≤ ln n := by
    exact hnJet.trans (hnψ.trans (by simpa only [ln] using hl (ψ n)))
  have hznK : zn n ∈ K := by
    change dist (zn n) zInf ≤ q / 2
    exact (hNz n hnZ).le
  have hQsmall : mapDerivNorm (j (ψ n)) (Q (kn n) (ln n))
      (gInf alpha) (zn n) ≤ eps / 2 :=
    hNQ n hnQ (j (ψ n)) (hj (ψ n)) (zn n) hznK
  have hGsmall : mapDerivNorm (j (ψ n)) (B (kn n))
      (gInf alpha) (zn n) ≤ eps / 2 :=
    hNG n hnG (j (ψ n)) (hj (ψ n)) (zn n) hznK
  have hznInt : zn n ∈ interior (C0 alpha) :=
    hbuffer' n (Metric.mem_closedBall_self heta.le)
  have hznC0 : zn n ∈ C0 alpha := interior_subset hznInt
  have hsrcS :
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      (NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm (zn n) ∈
          Lphi.hatSourceBall inp.decay P S (kn n) := by
    dsimp only
    let Yk := X.obj (Lphi.φ (kn n))
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
    have hsrc := hsource' n
    change dist
      ((NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm (zn n))
      Yk.basepoint ≤ R at hsrc
    change dist
      ((NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm (zn n))
      Yk.basepoint ≤ S
    exact hsrc.trans hRS.le
  have hjet := hNjet (kn n) hkJet (ln n) hlJet alpha (zn n) hznC0
    hznInt hsrcS
  have hAcd : ContDiffAt Real (∞ : WithTop ℕ∞) (A (kn n) (ln n)) (zn n) := by
    simpa only [A, Lphi] using hjet.2.1
  have hAclose : dist (A (kn n) (ln n) (zn n)) (zn n) ≤ eta / 2 := by
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
      dist_eq_norm, A, Lphi] using hjet.2.2 0 le_rfl
  have hAzInt : A (kn n) (ln n) (zn n) ∈ interior (C0 alpha) := by
    apply hbuffer' n
    rw [Metric.mem_closedBall]
    exact hAclose.trans (by linarith)
  have hzU : zn n ∈ U alpha := hIntU hznInt
  have hAzU : A (kn n) (ln n) (zn n) ∈ U alpha := hIntU hAzInt
  have hgeomK := hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf
    (kn n) alpha
  have hgeomL := hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf
    (ln n) alpha
  have hBksm : ContDiffOn Real (∞ : WithTop ℕ∞) (B (kn n)) (U alpha) := by
    simpa only [B, Lphi] using
      (normalCoordMetric_contDiffOn_expBall (I := I)
        (X.obj (Lphi.φ (kn n)))
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).mono hgeomK.2.1
  have hBlsm : ContDiffOn Real (∞ : WithTop ℕ∞) (B (ln n)) (U alpha) := by
    simpa only [B, Lphi] using
      (normalCoordMetric_contDiffOn_expBall (I := I)
        (X.obj (Lphi.φ (ln n)))
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))).mono hgeomL.2.1
  have hGcd : ContDiffAt Real (∞ : WithTop ℕ∞) (B (kn n)) (zn n) :=
    hBksm.contDiffAt (hUopen.mem_nhds hzU)
  have hgInfCd : ContDiffAt Real (∞ : WithTop ℕ∞) (gInf alpha) (zn n) := by
    apply hgInf.contDiffAt (Metric.isOpen_ball.mem_nhds (hC1D
      (interior_subset (hC01 hznC0))))
  have hBAcd : ContDiffAt Real (∞ : WithTop ℕ∞)
      (fun w ↦ B (ln n) (A (kn n) (ln n) w)) (zn n) :=
    (hBlsm.contDiffAt (hUopen.mem_nhds hAzU)).comp (zn n) hAcd
  have hDAcd : ContDiffAt Real (∞ : WithTop ℕ∞)
      (fun w ↦ fderiv Real (A (kn n) (ln n)) w) (zn n) :=
    hAcd.fderiv_right (m := (∞ : WithTop ℕ∞)) (by simp)
  have hQcd : ContDiffAt Real (∞ : WithTop ℕ∞)
      (Q (kn n) (ln n)) (zn n) := by
    have hpair := hBAcd.prodMk hDAcd
    have hpull := (_root_.DifferentialGeometry.HCGCompactness.pullbackForm.contDiff
      (E := E) (F := E)).contDiffAt.comp (zn n) hpair
    simpa only [Q] using hpull
  have hle : mapDerivNorm (j (ψ n)) (Q (kn n) (ln n))
      (B (kn n)) (zn n) ≤ eps := by
    calc
      mapDerivNorm (j (ψ n)) (Q (kn n) (ln n))
          (B (kn n)) (zn n) ≤
          mapDerivNorm (j (ψ n)) (Q (kn n) (ln n))
              (gInf alpha) (zn n) +
            mapDerivNorm (j (ψ n)) (B (kn n))
              (gInf alpha) (zn n) :=
        mapDerivNorm_tri (j (ψ n)) hQcd hgInfCd hGcd
      _ ≤ eps / 2 + eps / 2 := add_le_add hQsmall hGsmall
      _ = eps := by ring
  have hbad' := hbad (ψ n)
  simpa only [kn, ln, zn] using (not_lt_of_ge hle hbad')

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- On a smaller source ball, the producer-owned finite buffered chart cover
admits one common two-stage tail for all coefficient jets through a prescribed
finite order.  The conclusion keeps the chart witnessing each source point. -/
theorem HasStageJetData.pb_local_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    {R S : Real} (hRS : R < S) (hSr : S < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    let Lphi := L.subseq hphi
    let A : LiveSlot L inp.pack r → Nat → Nat → E → E :=
      fun alpha k l z ↦
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
    let B : LiveSlot L inp.pack r → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha l ↦
      normalCoordMetric (I := I) (X.obj (Lphi.φ l))
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    let Q : LiveSlot L inp.pack r → Nat → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha k l z ↦
      _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B alpha l (A alpha k l z), fderiv Real (A alpha k l) z)
    ∃ eta : LiveSlot L inp.pack r → Real,
      (∀ alpha, 0 < eta alpha) ∧
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
        let Yk := X.obj (Lphi.φ k)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        ∀ y ∈ Lphi.hatSourceBall inp.decay P R k,
          ∃ (alpha : LiveSlot L inp.pack r) (z : E),
            (NormalCoordinates.framedChartAt (I := I) Yk.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z = y ∧
            Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) ∧
            ∀ j ≤ p,
              mapDerivNorm j (Q alpha k l) (B alpha k) z ≤ eps := by
  classical
  dsimp only
  let Lphi := L.subseq hphi
  let A : LiveSlot L inp.pack r → Nat → Nat → E → E :=
    fun alpha k l z ↦
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
  let B : LiveSlot L inp.pack r → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha l ↦
    normalCoordMetric (I := I) (X.obj (Lphi.φ l))
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let Q : LiveSlot L inp.pack r → Nat → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha k l z ↦
    _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (B alpha l (A alpha k l z), fderiv Real (A alpha k l) z)
  change ∃ eta : LiveSlot L inp.pack r → Real,
    (∀ alpha, 0 < eta alpha) ∧
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Yk := X.obj (Lphi.φ k)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      ∀ y ∈ Lphi.hatSourceBall inp.decay P R k,
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          (NormalCoordinates.framedChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z = y ∧
          Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) ∧
          ∀ j ≤ p, mapDerivNorm j (Q alpha k l) (B alpha k) z ≤ eps
  obtain ⟨eta, heta, hcover⟩ :=
    hstage.1.buffer_cover inp P L r hr U C0 C1 aInf Jinf Jbarinf
  have hlocal : ∀ alpha : LiveSlot L inp.pack r,
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ z : E,
        Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) →
        let Yk := X.obj (Lphi.φ k)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
          mapDerivNorm j (Q alpha k l) (B alpha k) z ≤ eps := by
    intro alpha
    simpa only [Q, B, A, Lphi] using
      hstage.pb_buf_tail inp P L hr phi hphi hconn U C0 C1 aInf Jinf Jbarinf
        gInf alpha hRS hSr (heta alpha) p eps heps
  choose Nalpha hNalpha using hlocal
  letI := Fintype.ofFinite (LiveSlot L inp.pack r)
  refine ⟨eta, heta, Finset.univ.sup Nalpha, ?_⟩
  intro k hk l hl
  dsimp only
  let Yk := X.obj (Lphi.φ k)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  intro y hy
  have hyBig : y ∈ Lphi.hatSourceBall inp.decay P r k :=
    cball_subset_of_le (hRS.trans hSr).le hy
  obtain ⟨alpha, z, hzy, hzbuffer⟩ := hcover k y hyBig
  let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  have hzy' : chiK.symm z = y := by
    simpa only [chiK, Yk, Lphi] using hzy
  have hzSource : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k := by
    simpa only [hzy'] using hy
  have hAlpha : Nalpha alpha ≤ Finset.univ.sup Nalpha :=
    Finset.le_sup (f := Nalpha) (Finset.mem_univ alpha)
  have hkAlpha : Nalpha alpha ≤ k := hAlpha.trans hk
  have hlAlpha : Nalpha alpha ≤ l := hAlpha.trans hl
  refine ⟨alpha, z, hzy', hzbuffer, ?_⟩
  intro j hj
  simpa only [chiK, Yk, Lphi] using
    hNalpha alpha k hkAlpha l hlAlpha j hj z hzbuffer hzSource

end HCGCompactness
end DifferentialGeometry
