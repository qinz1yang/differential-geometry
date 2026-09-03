import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.TransitionLimits


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterMap.SupportConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageComparison.Basic

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

namespace BoundedGeometryNormalChartData

def transitionPatch
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r) : Set E :=
  Metric.ball 0 ((21 / 10 : Real) * L.lamInf (alpha.1 : Nat))

def innerTransitionCore
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r) : Set E :=
  Metric.closedBall 0 ((83 / 40 : Real) * L.lamInf (alpha.1 : Nat))

def outerTransitionCore
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r) : Set E :=
  Metric.closedBall 0 ((167 / 80 : Real) * L.lamInf (alpha.1 : Nat))

def transitionCoreBuffer
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r) : Real :=
  L.lamInf (alpha.1 : Nat) / 80

omit [CompleteSpace E] in
theorem transition_patch_geometry
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    (∀ alpha : LiveSlot L inp.pack r, IsOpen (transitionPatch L alpha)) ∧
    (∀ alpha : LiveSlot L inp.pack r,
      transitionPatch L alpha ⊆
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    (∀ alpha : LiveSlot L inp.pack r, IsCompact (innerTransitionCore L alpha)) ∧
    (∀ alpha : LiveSlot L inp.pack r, IsCompact (outerTransitionCore L alpha)) ∧
    (∀ alpha : LiveSlot L inp.pack r,
      innerTransitionCore L alpha ⊆ interior (outerTransitionCore L alpha)) ∧
    (∀ alpha : LiveSlot L inp.pack r,
      outerTransitionCore L alpha ⊆ transitionPatch L alpha) ∧
    (∀ alpha : LiveSlot L inp.pack r, Convex Real (innerTransitionCore L alpha)) ∧
    (∀ alpha : LiveSlot L inp.pack r, (0 : E) ∈ innerTransitionCore L alpha) ∧
    ∀ alpha : LiveSlot L inp.pack r, 0 < transitionCoreBuffer L alpha := by
  have hlam (alpha : LiveSlot L inp.pack r) :
      0 < L.lamInf (alpha.1 : Nat) :=
    inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
  refine ⟨fun _ => Metric.isOpen_ball, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro alpha z hz
    change z ∈ Metric.ball 0
      ((21 / 10 : Real) * L.lamInf (alpha.1 : Nat)) at hz
    change dist z 0 <
      (21 / 10 : Real) * L.lamInf (alpha.1 : Nat) at hz
    change dist z 0 < 8 * L.lamInf (alpha.1 : Nat)
    nlinarith [hlam alpha]
  · intro alpha
    change IsCompact (Metric.closedBall 0
      ((83 / 40 : Real) * L.lamInf (alpha.1 : Nat)))
    exact isCompact_closedBall _ _
  · intro alpha
    change IsCompact (Metric.closedBall 0
      ((167 / 80 : Real) * L.lamInf (alpha.1 : Nat)))
    exact isCompact_closedBall _ _
  · intro alpha z hz
    change z ∈ Metric.closedBall 0
      ((83 / 40 : Real) * L.lamInf (alpha.1 : Nat)) at hz
    change dist z 0 ≤
      (83 / 40 : Real) * L.lamInf (alpha.1 : Nat) at hz
    change z ∈ interior (Metric.closedBall 0
      ((167 / 80 : Real) * L.lamInf (alpha.1 : Nat)))
    rw [interior_closedBall (0 : E)
      (ne_of_gt (mul_pos (by norm_num) (hlam alpha)) :
        (167 / 80 : Real) * L.lamInf (alpha.1 : Nat) ≠ 0)]
    change dist z 0 <
      (167 / 80 : Real) * L.lamInf (alpha.1 : Nat)
    exact hz.trans_lt
      (mul_lt_mul_of_pos_right (by norm_num) (hlam alpha))
  · intro alpha z hz
    change z ∈ Metric.closedBall 0
      ((167 / 80 : Real) * L.lamInf (alpha.1 : Nat)) at hz
    change dist z 0 ≤
      (167 / 80 : Real) * L.lamInf (alpha.1 : Nat) at hz
    change z ∈ Metric.ball 0
      ((21 / 10 : Real) * L.lamInf (alpha.1 : Nat))
    change dist z 0 <
      (21 / 10 : Real) * L.lamInf (alpha.1 : Nat)
    nlinarith [hlam alpha]
  · intro alpha
    exact convex_closedBall 0 _
  · intro alpha
    change (0 : E) ∈ Metric.closedBall 0
      ((83 / 40 : Real) * L.lamInf (alpha.1 : Nat))
    rw [Metric.mem_closedBall, dist_self]
    nlinarith [hlam alpha]
  · intro alpha
    change 0 < L.lamInf (alpha.1 : Nat) / 80
    nlinarith [hlam alpha]

omit [CompleteSpace E] in
theorem closed_ball_subset_inner_transition_core
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (alpha : LiveSlot L inp.pack r) {z : E}
    (hz : ‖z‖ < (41 / 20 : Real) * L.lamInf (alpha.1 : Nat)) :
    Metric.closedBall z (transitionCoreBuffer L alpha) ⊆
      interior (innerTransitionCore L alpha) := by
  have hlam : 0 < L.lamInf (alpha.1 : Nat) :=
    inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
  intro w hw
  change w ∈ interior (Metric.closedBall 0
    ((83 / 40 : Real) * L.lamInf (alpha.1 : Nat)))
  rw [interior_closedBall (0 : E)
    (ne_of_gt (mul_pos (by norm_num) hlam) :
      (83 / 40 : Real) * L.lamInf (alpha.1 : Nat) ≠ 0)]
  change dist w 0 <
    (83 / 40 : Real) * L.lamInf (alpha.1 : Nat)
  rw [dist_zero_right]
  change dist w z ≤ L.lamInf (alpha.1 : Nat) / 80 at hw
  have htri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (w - z) z
  rw [dist_eq_norm] at hw
  nlinarith

omit [CompleteSpace E] in
theorem pair_overlap_at
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    {alpha gamma k : Nat}
    (hratio : 48 * aMin < d.ratio)
    (hcenterAlpha :
      inp.decay.dist (L.φ k)
          (seqCenterD inp.decay P L k alpha)
          (X.obj (L.φ k)).basepoint <
        L.rInf alpha + 1)
    (hcenterGamma :
      inp.decay.dist (L.φ k)
          (seqCenterD inp.decay P L k gamma)
          (X.obj (L.φ k)).basepoint <
        L.rInf gamma + 1)
    (hfreq : ∀ᶠ n : Nat in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf alpha gamma (L.φ n))
    (hinter :
      BInter inp.decay inp.D P L.lamInf alpha gamma (L.φ k)) :
    let j := L.φ k
    let cAlpha := seqCenterD inp.decay P L k alpha
    let cGamma := seqCenterD inp.decay P L k gamma
    d.chartOverlapOn j cAlpha cGamma
        (Metric.ball 0 (8 * L.lamInf alpha)) ∧
      Set.MapsTo (d.chartTransition j cAlpha cGamma)
        (Metric.ball 0 (8 * L.lamInf alpha))
        (Metric.ball 0 (72 * L.lamInf gamma)) ∧
      ∀ z ∈ Metric.ball 0 (8 * L.lamInf alpha),
        ‖d.chartTransition j cAlpha cGamma z‖ =
          inp.decay.dist j cGamma
            (d.chartMap j cAlpha z) := by
  let j := L.φ k
  let Y := X.obj j
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y (hcomplete.complete j)
  let : ConnectedSpace Y.M := hconn j
  let : MetricSpace Y.M := (P j).ms
  let cAlpha := seqCenterD inp.decay P L k alpha
  let cGamma := seqCenterD inp.decay P L k gamma
  let chiAlpha := d.chart j cAlpha
  let chiGamma := d.chart j cGamma
  have hradAlpha :
      384 * L.lamInf alpha < chiAlpha.radius := by
    simpa only [chiAlpha, cAlpha, Y, j] using
      d.stage_radius_gt inp aMin hphys P L hratio hcenterAlpha
  have hradGamma :
      384 * L.lamInf gamma < chiGamma.radius := by
    simpa only [chiGamma, cGamma, Y, j] using
      d.stage_radius_gt inp aMin hphys P L hratio hcenterGamma
  have hlamAlpha : 0 < L.lamInf alpha :=
    inp.decay.lambda_pos inp.hD (L.rInf alpha)
  have hlamGamma : 0 < L.lamInf gamma :=
    inp.decay.lambda_pos inp.hD (L.rInf gamma)
  have hfreq' : ∀ᶠ n : Nat in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf gamma alpha (L.φ n) :=
    hfreq.mono fun n hn =>
      BInter.symm inp.decay inp.D P L.lamInf hn
  have hpair :
      L.lamInf alpha < 3 * L.lamInf gamma :=
    d.pair_lam_lt_three inp aMin hphys P L hratio hfreq'.frequently
  have hcenterDist :
      (letI : MetricSpace Y.M := (P j).ms
       dist cGamma cAlpha) <
        5 * L.lamInf gamma + 5 * L.lamInf alpha := by
    obtain ⟨x, z, hx, hz, hmeet⟩ := hinter
    have hxc : x = cAlpha := by
      dsimp only [cAlpha]
      unfold seqCenterD
      rw [hx]
      simp only [Option.getD_some]
    have hzc : z = cGamma := by
      dsimp only [cGamma]
      unfold seqCenterD
      rw [hz]
      simp only [Option.getD_some]
    rw [hxc, hzc] at hmeet
    obtain ⟨v, hvAlpha, hvGamma⟩ := Set.not_disjoint_iff.mp hmeet
    rw [Metric.mem_ball] at hvAlpha hvGamma
    have htri := dist_triangle cGamma v cAlpha
    rw [dist_comm v cGamma] at hvGamma
    linarith
  have hpoint : ∀ z ∈ Metric.ball (0 : E) (8 * L.lamInf alpha),
      z ∈ Metric.ball 0 chiAlpha.radius ∧
        chiAlpha.hom z ∈ chiGamma.hom ''
          Metric.ball 0 chiGamma.radius ∧
        chiAlpha.transition chiGamma z ∈
          Metric.ball 0 (72 * L.lamInf gamma) ∧
        ‖chiAlpha.transition chiGamma z‖ =
          inp.decay.dist j cGamma (chiAlpha.hom z) := by
    intro z hz
    let y := chiAlpha.hom z
    have hzNorm : ‖z‖ < 8 * L.lamInf alpha := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzBall : z ∈ Metric.ball 0 chiAlpha.radius := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hzNorm.trans (by nlinarith)
    have hseg :
        segment Real 0 z ⊆ Metric.ball 0 chiAlpha.radius :=
      (convex_ball (0 : E) chiAlpha.radius).segment_subset
        (Metric.mem_ball_self chiAlpha.radius_pos) hzBall
    have hchart :
        (letI : MetricSpace Y.M := (P j).ms
         dist (chiAlpha.hom 0) (chiAlpha.hom z)) ≤
          Real.sqrt 2 * dist 0 z := by
      exact NormalBallChart.MetricEquivOn.hom_dist_le
        Y (P j) chiAlpha
          (by simpa only [chiAlpha, cAlpha, Y, j] using
            d.metric_equiv j cAlpha)
          chiAlpha.ball_subset hseg
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      linarith [Real.sqrt_two_lt_three_halves]
    have halphaTarget :
        (letI : MetricSpace Y.M := (P j).ms
         dist cAlpha y) < 16 * L.lamInf alpha := by
      calc
        (letI : MetricSpace Y.M := (P j).ms
         dist cAlpha y) =
            dist (chiAlpha.hom 0) (chiAlpha.hom z) := by
              rw [chiAlpha.map_zero]
        _ ≤ Real.sqrt 2 * dist 0 z := hchart
        _ = Real.sqrt 2 * ‖z‖ := by rw [dist_zero_left]
        _ < Real.sqrt 2 * (8 * L.lamInf alpha) :=
          mul_lt_mul_of_pos_left hzNorm (Real.sqrt_pos.2 (by norm_num))
        _ ≤ 2 * (8 * L.lamInf alpha) :=
          mul_le_mul_of_nonneg_right hsqrt
            (mul_nonneg (by norm_num) hlamAlpha.le)
        _ = 16 * L.lamInf alpha := by ring
    have hproper :
        (letI : MetricSpace Y.M := (P j).ms
         dist cGamma y) < 68 * L.lamInf gamma := by
      have htri :
          (letI : MetricSpace Y.M := (P j).ms
           dist cGamma y) ≤ dist cGamma cAlpha + dist cAlpha y :=
        dist_triangle _ _ _
      nlinarith
    have hdist :
        inp.decay.dist j cGamma y < chiGamma.radius := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P
        j cGamma y]
      exact hproper.trans (by nlinarith)
    have hdist72 :
        inp.decay.dist j cGamma y < 72 * L.lamInf gamma := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P
        j cGamma y]
      exact hproper.trans (by nlinarith)
    have hed : riemannianEDist I cGamma y =
        ENNReal.ofReal (inp.decay.dist j cGamma y) := by
      have hrealize := inp.realizes.edist_eq j cGamma y
      change riemannianEDist I cGamma y = _ at hrealize
      exact hrealize
    have hedRad : riemannianEDist I cGamma y <
        ENNReal.ofReal chiGamma.radius := by
      rw [hed]
      exact (ENNReal.ofReal_lt_ofReal_iff chiGamma.radius_pos).2 hdist
    have hread := d.toNormalChartData.mem_image_and_norm_inv_eq_riemannian_distance
      j (hcomplete.complete j) (hconn j) cGamma y hedRad
    have hcoord :
        chiAlpha.transition chiGamma z =
          chiGamma.inv y := by
      rfl
    have hcoordBall :
        chiAlpha.transition chiGamma z ∈
          Metric.ball 0 (72 * L.lamInf gamma) := by
      rw [Metric.mem_ball, dist_zero_right, hcoord, hread.2, hed,
        ENNReal.toReal_ofReal (inp.realizes.dist_nonneg j cGamma y)]
      exact hdist72
    have hcoordNorm :
        ‖chiAlpha.transition chiGamma z‖ =
          inp.decay.dist j cGamma y := by
      rw [hcoord, hread.2, hed,
        ENNReal.toReal_ofReal (inp.realizes.dist_nonneg j cGamma y)]
    exact ⟨hzBall, hread.1, hcoordBall, hcoordNorm⟩
  change d.chartOverlapOn j cAlpha cGamma
      (Metric.ball 0 (8 * L.lamInf alpha)) ∧
    Set.MapsTo (d.chartTransition j cAlpha cGamma)
      (Metric.ball 0 (8 * L.lamInf alpha))
      (Metric.ball 0 (72 * L.lamInf gamma)) ∧
    ∀ z ∈ Metric.ball 0 (8 * L.lamInf alpha),
      ‖d.chartTransition j cAlpha cGamma z‖ =
        inp.decay.dist j cGamma (d.chartMap j cAlpha z)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact ⟨(hpoint z hz).1, (hpoint z hz).2.1⟩
  · intro z hz
    simpa only [BoundedGeometryNormalChartData.chartTransition] using (hpoint z hz).2.2.1
  · intro z hz
    simpa only [BoundedGeometryNormalChartData.chartTransition, BoundedGeometryNormalChartData.chartMap] using
      (hpoint z hz).2.2.2

omit [CompleteSpace E] in
theorem chart_transition_pair_eventually
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    {r : Real}
    (hratio : 48 * aMin < d.ratio)
    (alpha gamma : LiveSlot L inp.pack r)
    (hinter : ∀ᶠ k : Nat in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf
        (alpha.1 : Nat) (gamma.1 : Nat) (L.φ k)) :
    ∀ᶠ k : Nat in Filter.atTop,
      let j := L.φ k
      let cAlpha := seqCenterD inp.decay P L k (alpha.1 : Nat)
      let cGamma := seqCenterD inp.decay P L k (gamma.1 : Nat)
      d.chartOverlapOn j cAlpha cGamma
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        Set.MapsTo (d.chartTransition j cAlpha cGamma)
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
          (Metric.ball 0 (72 * L.lamInf (gamma.1 : Nat))) ∧
        ∀ z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)),
          ‖d.chartTransition j cAlpha cGamma z‖ =
            inp.decay.dist j cGamma
              (d.chartMap j cAlpha z) := by
  have hcenters :=
    liveCenters_rInf (I := I) inp.decay P inp.realizes L inp.pack r
  filter_upwards [hinter, hcenters] with k hinterK hcentersK
  exact d.pair_overlap_at inp aMin hphys P L hcomplete hconn hratio
    (hcentersK alpha) (hcentersK gamma) hinter hinterK

omit [CompleteSpace E] in
theorem transition_patch_eventually
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real)
    (hratio : 48 * aMin < d.ratio) :
    ∀ᶠ k : Nat in Filter.atTop,
      let j := L.φ k
      let Y := X.obj j
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P j).ms
      (∀ alpha : LiveSlot L inp.pack r,
        transitionPatch L alpha ⊆ Metric.ball 0
            (d.chart j
              (seqCenterD inp.decay P L k (alpha.1 : Nat))).radius ∧
        Set.MapsTo
          (d.chart j
            (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom
          (transitionPatch L alpha)
          (L.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              L.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
      L.hatSourceBall inp.decay P r k ⊆
        ⋃ alpha : LiveSlot L inp.pack r,
          (d.chart j
            (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom ''
              interior (innerTransitionCore L alpha) ∧
      ∀ y ∈ L.hatSourceBall inp.decay P r k,
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          (d.chart j
              (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom z = y ∧
            Metric.closedBall z (transitionCoreBuffer L alpha) ⊆
              interior (innerTransitionCore L alpha) := by
  have hscaled :=
    L.scaled_cover inp.decay inp.hD P inp.realizes inp.pack r
      (41 / 20 : Real) (by norm_num)
  have hcenters :=
    liveCenters_rInf (I := I) inp.decay P inp.realizes L inp.pack r
  have halive : ∀ᶠ k : Nat in Filter.atTop,
      ∀ gamma ∈ Finset.range (inp.pack.A r),
        (seqCenter inp.decay inp.D P (L.φ k) gamma).isSome =
          L.alive gamma :=
    (Filter.eventually_all_finset _).mpr fun gamma _ =>
      L.alive_eventually gamma
  filter_upwards [hscaled, hcenters, halive]
    with k hscaledK hcentersK haliveK
  let j := L.φ k
  let Y := X.obj j
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y (hcomplete.complete j)
  let : ConnectedSpace Y.M := hconn j
  let : MetricSpace Y.M := (P j).ms
  have hsqrt : Real.sqrt 2 < (10 / 7 : Real) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
    have hn := Real.sqrt_nonneg 2
    nlinarith
  have hpatch :
      ∀ alpha : LiveSlot L inp.pack r,
        transitionPatch L alpha ⊆ Metric.ball 0
            (d.chart j
              (seqCenterD inp.decay P L k (alpha.1 : Nat))).radius ∧
        Set.MapsTo
          (d.chart j
            (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom
          (transitionPatch L alpha)
          (L.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              L.innerBall inp.decay inp.D P inp.pack r k gamma) := by
    intro alpha
    let c := seqCenterD inp.decay P L k (alpha.1 : Nat)
    let chi := d.chart j c
    have hlam : 0 < L.lamInf (alpha.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
    have hrad : 384 * L.lamInf (alpha.1 : Nat) < chi.radius := by
      simpa only [chi, c, Y, j] using
        d.stage_radius_gt inp aMin hphys P L hratio (hcentersK alpha)
    have hUrad : transitionPatch L alpha ⊆ Metric.ball 0 chi.radius := by
      intro z hz
      change dist z 0 <
        (21 / 10 : Real) * L.lamInf (alpha.1 : Nat) at hz
      change dist z 0 < chi.radius
      exact hz.trans (by nlinarith)
    refine ⟨hUrad, fun z hz => ?_⟩
    have hzBall := hUrad hz
    have hseg :
        segment Real 0 z ⊆ Metric.ball 0 chi.radius :=
      (convex_ball (0 : E) chi.radius).segment_subset
        (Metric.mem_ball_self chi.radius_pos) hzBall
    have hchart :
        (letI : MetricSpace Y.M := (P j).ms
         dist (chi.hom 0) (chi.hom z)) ≤
          Real.sqrt 2 * dist 0 z := by
      exact NormalBallChart.MetricEquivOn.hom_dist_le
        Y (P j) chi
          (by simpa only [chi, c, Y, j] using d.metric_equiv j c)
          chi.ball_subset hseg
    have hzNorm : ‖z‖ <
        (21 / 10 : Real) * L.lamInf (alpha.1 : Nat) := by
      simpa only [transitionPatch, Metric.mem_ball, dist_zero_right] using hz
    have himage :
        (letI : MetricSpace Y.M := (P j).ms
         dist c (chi.hom z)) < 3 * L.lamInf (alpha.1 : Nat) := by
      calc
        (letI : MetricSpace Y.M := (P j).ms
         dist c (chi.hom z)) =
            dist (chi.hom 0) (chi.hom z) := by rw [chi.map_zero]
        _ ≤ Real.sqrt 2 * dist 0 z := hchart
        _ = Real.sqrt 2 * ‖z‖ := by rw [dist_zero_left]
        _ < Real.sqrt 2 *
            ((21 / 10 : Real) * L.lamInf (alpha.1 : Nat)) :=
          mul_lt_mul_of_pos_left hzNorm (Real.sqrt_pos.2 (by norm_num))
        _ < (10 / 7 : Real) *
            ((21 / 10 : Real) * L.lamInf (alpha.1 : Nat)) :=
          mul_lt_mul_of_pos_right hsqrt
            (mul_pos (by norm_num) hlam)
        _ = 3 * L.lamInf (alpha.1 : Nat) := by ring
    have hsome :
        seqCenter inp.decay inp.D P (L.φ k) (alpha.1 : Nat) =
          some c := by
      apply seqCenterD_some inp.decay P L k (alpha.1 : Nat)
      rw [haliveK (alpha.1 : Nat)
        (by simpa only [Finset.mem_range] using alpha.1.2), alpha.2]
    have hinner :
        chi.hom z ∈
          L.innerBall inp.decay inp.D P inp.pack r k alpha.1 := by
      simpa only [NetLimitData.innerBall, hsome, Metric.mem_ball,
        dist_comm] using himage
    have hhat :
        chi.hom z ∈
          L.hatBall inp.decay inp.D P inp.pack r k alpha.1 := by
      simp only [NetLimitData.hatBall, hsome, Metric.mem_ball]
      change dist (chi.hom z) c < 4 * L.lamInf (alpha.1 : Nat)
      rw [dist_comm]
      exact himage.trans (by nlinarith)
    exact ⟨hhat, mem_iUnion.mpr ⟨alpha.1, hinner⟩⟩
  have hwitness :
      ∀ y ∈ L.hatSourceBall inp.decay P r k,
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          (d.chart j
              (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom z = y ∧
            Metric.closedBall z (transitionCoreBuffer L alpha) ⊆
              interior (innerTransitionCore L alpha) := by
    intro y hy
    have hyr :
        (letI : MetricSpace Y.M := (P j).ms
         dist y Y.basepoint ≤ r) := by
      simpa only [NetLimitData.hatSourceBall, Y, j,
        Metric.mem_closedBall] using hy
    obtain ⟨gamma, hgammaA, c, hc, hyc⟩ := hscaledK y hyr
    let gammaFin : Fin (inp.pack.A r) := ⟨gamma, hgammaA⟩
    have hgammaLive : L.alive gamma = true := by
      have hisSome :
          (seqCenter inp.decay inp.D P (L.φ k) gamma).isSome = true := by
        rw [hc]
        rfl
      rw [haliveK gamma (by simpa only [Finset.mem_range] using hgammaA)]
        at hisSome
      exact hisSome
    let alpha : LiveSlot L inp.pack r := ⟨gammaFin, hgammaLive⟩
    have hlam : 0 < L.lamInf gamma :=
      inp.decay.lambda_pos inp.hD (L.rInf gamma)
    have hcD : seqCenterD inp.decay P L k gamma = c := by
      unfold seqCenterD
      rw [hc]
      rfl
    let chi := d.chart j c
    have hrad : 384 * L.lamInf gamma < chi.radius := by
      have hcenter := hcentersK alpha
      have hrad' :=
        d.stage_radius_gt inp aMin hphys P L hratio hcenter
      rw [hcD] at hrad'
      simpa only [chi, j] using hrad'
    have hproper :
        inp.decay.dist j c y <
          (41 / 20 : Real) * L.lamInf gamma := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P j c y]
      simpa only [dist_comm] using hyc
    have hsmall :
        (41 / 20 : Real) * L.lamInf gamma <
          384 * L.lamInf gamma :=
      mul_lt_mul_of_pos_right (by norm_num) hlam
    have hdist : inp.decay.dist j c y < chi.radius :=
      hproper.trans (hsmall.trans hrad)
    have hed : riemannianEDist I c y =
        ENNReal.ofReal (inp.decay.dist j c y) := by
      have hrealize := inp.realizes.edist_eq j c y
      change riemannianEDist I c y = _ at hrealize
      exact hrealize
    have hedRad : riemannianEDist I c y <
        ENNReal.ofReal chi.radius := by
      rw [hed]
      exact (ENNReal.ofReal_lt_ofReal_iff chi.radius_pos).2 hdist
    have hread := d.toNormalChartData.mem_image_and_norm_inv_eq_riemannian_distance
      j (hcomplete.complete j) (hconn j) c y hedRad
    have htarget : y ∈ chi.hom.target := by
      obtain ⟨w, hw, hwy⟩ := hread.1
      rw [← hwy]
      exact chi.hom.map_source (chi.ball_subset hw)
    let z := chi.inv y
    have hmap : chi.hom z = y := by
      exact chi.hom.right_inv htarget
    have hzNorm :
        ‖z‖ < (41 / 20 : Real) * L.lamInf gamma := by
      dsimp only [z]
      rw [hread.2, hed,
        ENNReal.toReal_ofReal (inp.realizes.dist_nonneg j c y)]
      exact hproper
    have hbuffer :
        Metric.closedBall z (transitionCoreBuffer L alpha) ⊆
          interior (innerTransitionCore L alpha) := by
      apply closed_ball_subset_inner_transition_core inp P L alpha
      simpa only [alpha, gammaFin] using hzNorm
    refine ⟨alpha, z, ?_, hbuffer⟩
    change (d.chart j (seqCenterD inp.decay P L k gamma)).hom z = y
    rw [hcD]
    exact hmap
  refine ⟨hpatch, ?_, hwitness⟩
  intro y hy
  obtain ⟨alpha, z, hzy, hbuffer⟩ := hwitness y hy
  have heta : 0 ≤ transitionCoreBuffer L alpha :=
    (transition_patch_geometry inp P L r).2.2.2.2.2.2.2.2 alpha |>.le
  have hzCore : z ∈ interior (innerTransitionCore L alpha) :=
    hbuffer (Metric.mem_closedBall_self heta)
  exact mem_iUnion.mpr ⟨alpha, ⟨z, hzCore, hzy⟩⟩

omit [CompleteSpace E] in
theorem transition_target_ball_eventually
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    {r : Real}
    (hratio : 48 * aMin < d.ratio)
    (alpha : LiveSlot L inp.pack r) :
    ∀ᶠ k : Nat in Filter.atTop,
      Metric.ball (0 : E) (72 * L.lamInf (alpha.1 : Nat)) ⊆
        Metric.ball (0 : E)
          (d.ratio * inp.decay.mu
            (inp.decay.dist (L.φ k)
              (seqCenterD inp.decay P L k (alpha.1 : Nat))
              (X.obj (L.φ k)).basepoint)) := by
  have hcenters :=
    liveCenters_rInf (I := I) inp.decay P inp.realizes L inp.pack r
  filter_upwards [hcenters] with k hcentersK
  have hstage :
      384 * L.lamInf (alpha.1 : Nat) <
        d.ratio * inp.decay.mu
          (inp.decay.dist (L.φ k)
            (seqCenterD inp.decay P L k (alpha.1 : Nat))
            (X.obj (L.φ k)).basepoint) := by
    let : TopologicalSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).topology
    let : ChartedSpace H (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).charted
    let : IsManifold I ∞ (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).smooth
    let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    simpa only [d.radius_eq] using
      d.stage_radius_gt inp aMin hphys P L hratio (hcentersK alpha)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  exact hz.trans <| (mul_lt_mul_of_pos_right (by norm_num)
    (inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat)))).trans hstage

private theorem trans_fin
    {ι : Type*} (s : Finset ι)
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd)
    (x y : ι → ∀ k : Nat, (X.obj k).M)
    (U V Ua Va : ι → Set E)
    (hU : ∀ i, i ∈ s → IsOpen (U i))
    (hV : ∀ i, i ∈ s → IsOpen (V i))
    (hUa : ∀ i, i ∈ s → IsOpen (Ua i))
    (hVa : ∀ i, i ∈ s → IsOpen (Va i))
    (hUanorm : ∀ i, i ∈ s → ∃ Z : Real, ∀ z ∈ Ua i, ‖z‖ ≤ Z)
    (hVanorm : ∀ i, i ∈ s → ∃ Z : Real, ∀ z ∈ Va i, ‖z‖ ≤ Z)
    (hUarad : ∀ i, i ∈ s → ∀ k,
      Ua i ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (x i k) (X.obj k).basepoint)))
    (hVarad : ∀ i, i ∈ s → ∀ k,
      Va i ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (y i k) (X.obj k).basepoint)))
    (hovlJ : ∀ i, i ∈ s → ∀ k, d.chartOverlapOn k (x i k) (y i k) (U i))
    (hovlJbar : ∀ i, i ∈ s → ∀ k, d.chartOverlapOn k (y i k) (x i k) (V i))
    (hmapJ : ∀ i, i ∈ s → ∀ k, Set.MapsTo
      (d.chartTransition k (x i k) (y i k)) (U i) (Va i))
    (hmapJbar : ∀ i, i ∈ s → ∀ k, Set.MapsTo
      (d.chartTransition k (y i k) (x i k)) (V i) (Ua i)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      ∀ i, i ∈ s → ∃ Jinf : E → E, ∃ Jbarinf : E → E,
        ContDiffOn Real (⊤ : ℕ∞) Jinf (U i) ∧
        ContDiffOn Real (⊤ : ℕ∞) Jbarinf (V i) ∧
        MapCInfConvOnCompacts (U i)
          (fun k => d.chartTransition (phi k)
            (x i (phi k)) (y i (phi k))) Jinf ∧
        MapCInfConvOnCompacts (V i)
          (fun k => d.chartTransition (phi k)
            (y i (phi k)) (x i (phi k))) Jbarinf ∧
        (∀ z ∈ U i, Jinf z ∈ V i → Jbarinf (Jinf z) = z) ∧
        (∀ z ∈ V i, Jbarinf z ∈ U i → Jinf (Jbarinf z) = z) := by
  classical
  revert hU hV hUa hVa hUanorm hVanorm hUarad hVarad
    hovlJ hovlJbar hmapJ hmapJbar
  induction s using Finset.induction with
  | empty =>
      intro hU hV hUa hVa hUanorm hVanorm hUarad hVarad
        hovlJ hovlJbar hmapJ hmapJbar
      exact ⟨id, strictMono_id, fun i hi => by simp at hi⟩
  | @insert a s ha ih =>
      intro hU hV hUa hVa hUanorm hVanorm hUarad hVarad
        hovlJ hovlJbar hmapJ hmapJbar
      obtain ⟨phi0, hphi0, hprev⟩ :=
        ih
          (fun i hi => hU i (Finset.mem_insert_of_mem hi))
          (fun i hi => hV i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUa i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVa i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUanorm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVanorm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUarad i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVarad i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJbar i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapJbar i (Finset.mem_insert_of_mem hi))
      let d0 := d.subseq phi0
      obtain ⟨phi1, Jinf, Jbarinf, hphi1, hJinf, hJbarinf,
          hJ, hJbar, hleft, hright⟩ :=
        d0.exists_transition_limit_subsequence
          (fun k => x a (phi0 k)) (fun k => y a (phi0 k))
          (hU a (Finset.mem_insert_self a s))
          (hV a (Finset.mem_insert_self a s))
          (hUa a (Finset.mem_insert_self a s))
          (hVa a (Finset.mem_insert_self a s))
          (hUanorm a (Finset.mem_insert_self a s))
          (hVanorm a (Finset.mem_insert_self a s))
          (fun k => by
            with_unfolding_all
              exact hUarad a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hVarad a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hovlJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hovlJbar a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hmapJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hmapJbar a (Finset.mem_insert_self a s) (phi0 k))
      refine ⟨phi0 ∘ phi1, hphi0.comp hphi1, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | his
      · refine ⟨Jinf, Jbarinf, hJinf, hJbarinf, ?_, ?_, hleft, hright⟩
        · with_unfolding_all
            exact hJ
        · with_unfolding_all
            exact hJbar
      · obtain ⟨Jprev, Jbarprev, hJprev, hJbarprev, hconv, hconvbar,
            hleftprev, hrightprev⟩ := hprev i his
        refine ⟨Jprev, Jbarprev, hJprev, hJbarprev, ?_, ?_,
          hleftprev, hrightprev⟩
        · simpa only [Function.comp_apply] using hconv.comp_subseq hphi1
        · simpa only [Function.comp_apply] using hconvbar.comp_subseq hphi1

omit [CompleteSpace E] in
theorem atomOn_readout
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (k : Nat)
    (alpha gamma : Fin (inp.pack.A r))
    (hc : seqCenter inp.decay inp.D P (L.φ k) (gamma : Nat) =
      some (seqCenterD inp.decay P L k (gamma : Nat)))
    {z : E}
    (hnorm :
      ‖d.chartTransition (L.φ k)
        (seqCenterD inp.decay P L k (alpha : Nat))
        (seqCenterD inp.decay P L k (gamma : Nat)) z‖ =
      inp.decay.dist (L.φ k)
        (seqCenterD inp.decay P L k (gamma : Nat))
        (d.chartMap (L.φ k)
          (seqCenterD inp.decay P L k (alpha : Nat)) z)) :
    seqAtomOn (I := I) d.chart inp.decay inp.hD P L inp.pack r
        (fun n => seqCenterD inp.decay P L n (alpha : Nat)) gamma k z =
      gluingBump (L.lamInf (gamma : Nat))
          (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))
        (‖d.chartTransition (L.φ k)
          (seqCenterD inp.decay P L k (alpha : Nat))
          (seqCenterD inp.decay P L k (gamma : Nat)) z‖ ^ 2) := by
  let j := L.φ k
  let Y := X.obj j
  let cAlpha := seqCenterD inp.decay P L k (alpha : Nat)
  let cGamma := seqCenterD inp.decay P L k (gamma : Nat)
  let lam := L.lamInf (gamma : Nat)
  let hlam := inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := (P j).ms
  have hdist :
      dist cGamma (d.chartMap j cAlpha z) =
        ‖d.chartTransition j cAlpha cGamma z‖ := by
    exact (ProperMetricOn.dist_eq inp.decay inp.realizes P
      j cGamma (d.chartMap j cAlpha z)).trans hnorm.symm
  unfold seqAtomOn
  rw [seqAtom_some inp.decay inp.hD P L inp.pack r k gamma hc]
  change gluingBump lam hlam
      (dist cGamma (d.chartMap j cAlpha z) ^ 2) =
    gluingBump lam hlam
      (‖d.chartTransition j cAlpha cGamma z‖ ^ 2)
  rw [hdist]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] in
private theorem normBump_conv
    {U : Set E} (hU : IsOpen U)
    {J : Nat → E → E} {Jinf : E → E}
    (hJ : MapCInfConvOnCompacts U J Jinf)
    (hJc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (J k) U)
    (hJinf : ContDiffOn Real (∞ : WithTop ℕ∞) Jinf U)
    (lam : Real) (hlam : 0 < lam) :
    MapCInfConvOnCompacts U
      (fun k z => gluingBump lam hlam (‖J k z‖ ^ 2))
      (fun z => gluingBump lam hlam (‖Jinf z‖ ^ 2)) := by
  let B : E →L[Real] E →L[Real] Real := innerSL Real
  have hB : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : E => B) (fun _ : E => B) :=
    mapCInfConv_const (fun _ : E => B)
  have hconv := quadBump_conv hU hB hJ
    (fun _ => contDiffOn_const) contDiffOn_const hJc hJinf
    (gluingBump lam hlam) (gluingBump lam hlam).contDiff
  have hquad (v : E) : B v v = ‖v‖ ^ 2 := by
    dsimp only [B]
    change Inner.inner Real v v = ‖v‖ ^ 2
    exact real_inner_self_eq_norm_sq v
  simpa only [quadRead, hquad] using hconv

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    [CompleteSpace E] in
private theorem normBump_smooth
    {U : Set E} {J : E → E}
    (hJ : ContDiffOn Real (∞ : WithTop ℕ∞) J U)
    (lam : Real) (hlam : 0 < lam) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => gluingBump lam hlam (‖J z‖ ^ 2)) U := by
  let B : E →L[Real] E →L[Real] Real := innerSL Real
  have hquad : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => B (J z) (J z)) U :=
    ((contDiffOn_const : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun _ : E => B) U).clm_apply hJ).clm_apply hJ
  have hnorm : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => ‖J z‖ ^ 2) U := by
    refine ContDiffOn.congr hquad fun z _ => ?_
    change ‖J z‖ ^ 2 = Inner.inner Real (J z) (J z)
    exact (real_inner_self_eq_norm_sq _).symm
  exact (gluingBump lam hlam).contDiff.comp_contDiffOn hnorm

omit [CompleteSpace E] in
theorem atomOn_live_conv
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    (alpha gamma : LiveSlot L inp.pack r)
    {U : Set E} (hU : IsOpen U)
    {Jinf : E → E}
    (hJ : MapCInfConvOnCompacts U
      (fun k => d.chartTransition (L.φ k)
        (seqCenterD inp.decay P L k (alpha.1 : Nat))
        (seqCenterD inp.decay P L k (gamma.1 : Nat))) Jinf)
    (hJc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (d.chartTransition (L.φ k)
        (seqCenterD inp.decay P L k (alpha.1 : Nat))
        (seqCenterD inp.decay P L k (gamma.1 : Nat))) U)
    (hJinf : ContDiffOn Real (∞ : WithTop ℕ∞) Jinf U)
    (hread : ∀ᶠ k : Nat in Filter.atTop,
      ∀ z ∈ U,
        ‖d.chartTransition (L.φ k)
          (seqCenterD inp.decay P L k (alpha.1 : Nat))
          (seqCenterD inp.decay P L k (gamma.1 : Nat)) z‖ =
        inp.decay.dist (L.φ k)
          (seqCenterD inp.decay P L k (gamma.1 : Nat))
          (d.chartMap (L.φ k)
            (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomOn (I := I) d.chart inp.decay inp.hD P L
        inp.pack r
        (fun n => seqCenterD inp.decay P L n (alpha.1 : Nat))
        gamma.1 k)
      (fun z => gluingBump (L.lamInf (gamma.1 : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma.1 : Nat)))
        (‖Jinf z‖ ^ 2)) := by
  have hbump := normBump_conv hU hJ hJc hJinf
    (L.lamInf (gamma.1 : Nat))
    (inp.decay.lambda_pos inp.hD (L.rInf (gamma.1 : Nat)))
  refine hbump.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [hread,
    seqCenterD_live inp.decay P L (gamma.1 : Nat) gamma.2] with k hreadK hc
  intro z hz
  exact atomOn_readout inp d P L r k alpha.1 gamma.1 hc
    (hreadK z hz)

omit [CompleteSpace E] in
theorem atomOn_dead_conv
    (chart : NormalChartFamily (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U) (hgamma : L.alive (gamma : Nat) = false) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomOn (I := I) chart hd hD P L pb r beta gamma k)
      (fun _ => 0) := by
  have hzero : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : E => (0 : Real)) (fun _ => 0) :=
    mapCInfConv_const (fun _ : E => (0 : Real))
  refine hzero.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [seqCenter_dead hd P L (gamma : Nat) hgamma] with k hk
  intro z _hz
  simp [seqAtomOn, seqAtom_none hd hD P L pb r k gamma hk]

omit [CompleteSpace E] in
theorem atomOn_disjoint_conv
    (chart : NormalChartFamily (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (alpha gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (chart (L.φ k) (beta k)).hom U
        (L.hatBall hd D P pb r k alpha))
    (hdisjoint : ∀ᶠ k in Filter.atTop,
      ¬ BInter hd D P L.lamInf (alpha : Nat) (gamma : Nat) (L.φ k)) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomOn (I := I) chart hd hD P L pb r beta gamma k)
      (fun _ => 0) := by
  have hzero : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : E => (0 : Real)) (fun _ => 0) :=
    mapCInfConv_const (fun _ : E => (0 : Real))
  refine hzero.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [hsource, hdisjoint] with k hsourceK hdisjointK
  intro z hz
  by_contra hne
  apply hdisjointK
  exact L.binter_of_mem_hat hd hD P pb r k (hsourceK hz)
    (seqAtom_mem_hat_raw hd hD P L pb r k gamma (by
      simpa only [seqAtomOn] using hne))

theorem exists_supp_data
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (r : Real) (hr : 0 ≤ r)
    (hratio : 48 * aMin < d.ratio) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
        U C0 C1 aInf Jinf Jbarinf := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r,
    InterSlot L inp.pack r alpha
  let (alpha : LiveSlot L inp.pack r) :
      Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  let : Finite PairSlot := inferInstance
  let : Fintype PairSlot := Fintype.ofFinite PairSlot
  have hpair (pair : PairSlot) :
      ∀ᶠ k : Nat in Filter.atTop,
        (d.chartOverlapOn (L.φ k)
            (seqCenterD inp.decay P L k (pair.1.1 : Nat))
            (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
            (Metric.ball 0 (8 * L.lamInf (pair.1.1 : Nat))) ∧
          Set.MapsTo
            (d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat)))
            (Metric.ball 0 (8 * L.lamInf (pair.1.1 : Nat)))
            (Metric.ball 0 (72 * L.lamInf (pair.2.1.1 : Nat))) ∧
          ∀ z ∈ Metric.ball 0 (8 * L.lamInf (pair.1.1 : Nat)),
            ‖d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat)) z‖ =
                inp.decay.dist (L.φ k)
                  (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
                  (d.chartMap (L.φ k)
                    (seqCenterD inp.decay P L k (pair.1.1 : Nat)) z)) ∧
        (d.chartOverlapOn (L.φ k)
            (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
            (seqCenterD inp.decay P L k (pair.1.1 : Nat))
            (Metric.ball 0 (8 * L.lamInf (pair.2.1.1 : Nat))) ∧
          Set.MapsTo
            (d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.1.1 : Nat)))
            (Metric.ball 0 (8 * L.lamInf (pair.2.1.1 : Nat)))
            (Metric.ball 0 (72 * L.lamInf (pair.1.1 : Nat))) ∧
          ∀ z ∈ Metric.ball 0 (8 * L.lamInf (pair.2.1.1 : Nat)),
            ‖d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.1.1 : Nat)) z‖ =
                inp.decay.dist (L.φ k)
                  (seqCenterD inp.decay P L k (pair.1.1 : Nat))
                  (d.chartMap (L.φ k)
                    (seqCenterD inp.decay P L k (pair.2.1.1 : Nat)) z)) ∧
        Metric.ball (0 : E) (72 * L.lamInf (pair.1.1 : Nat)) ⊆
          Metric.ball 0
            (d.ratio * inp.decay.mu
              (inp.decay.dist (L.φ k)
                (seqCenterD inp.decay P L k (pair.1.1 : Nat))
                (X.obj (L.φ k)).basepoint)) ∧
        Metric.ball (0 : E) (72 * L.lamInf (pair.2.1.1 : Nat)) ⊆
          Metric.ball 0
            (d.ratio * inp.decay.mu
              (inp.decay.dist (L.φ k)
                (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
                (X.obj (L.φ k)).basepoint)) := by
    have hf := d.chart_transition_pair_eventually inp aMin hphys P L hcomplete hconn
      hratio pair.1 pair.2.1 pair.2.2
    have hinterRev : ∀ᶠ k : Nat in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf
          (pair.2.1.1 : Nat) (pair.1.1 : Nat) (L.φ k) :=
      pair.2.2.mono fun _ hk =>
        BInter.symm inp.decay inp.D P L.lamInf hk
    have hb := d.chart_transition_pair_eventually inp aMin hphys P L hcomplete hconn
      hratio pair.2.1 pair.1 hinterRev
    have hra := d.transition_target_ball_eventually inp aMin hphys P L hratio pair.1
    have hrb := d.transition_target_ball_eventually inp aMin hphys P L hratio pair.2.1
    filter_upwards [hf, hb, hra, hrb] with k hfK hbK hraK hrbK
    exact ⟨hfK, hbK, hraK, hrbK⟩
  have hcenter (gamma : Fin (inp.pack.A r)) :
      ∀ᶠ k : Nat in Filter.atTop,
        (L.alive (gamma : Nat) = false →
          seqCenter inp.decay inp.D P (L.φ k) (gamma : Nat) = none) ∧
        (L.alive (gamma : Nat) = true →
          seqCenter inp.decay inp.D P (L.φ k) (gamma : Nat) =
            some (seqCenterD inp.decay P L k (gamma : Nat))) := by
    cases hgamma : L.alive (gamma : Nat) with
    | false =>
        filter_upwards [
          seqCenter_dead inp.decay P L (gamma : Nat) hgamma] with k hk
        constructor
        · intro _
          exact hk
        · intro htrue
          cases htrue
    | true =>
        filter_upwards [
          seqCenterD_live inp.decay P L (gamma : Nat) hgamma] with k hk
        constructor
        · intro hfalse
          cases hfalse
        · intro _
          exact hk
  have hsep (alpha : LiveSlot L inp.pack r)
      (gamma : Fin (inp.pack.A r)) :
      ∀ᶠ k : Nat in Filter.atTop,
        (∀ᶠ n : Nat in Filter.atTop,
            ¬ BInter inp.decay inp.D P L.lamInf
              (alpha.1 : Nat) (gamma : Nat) (L.φ n)) →
          ¬ BInter inp.decay inp.D P L.lamInf
            (alpha.1 : Nat) (gamma : Nat) (L.φ k) := by
    by_cases hdisjoint : ∀ᶠ n : Nat in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf
          (alpha.1 : Nat) (gamma : Nat) (L.φ n)
    · exact hdisjoint.mono fun _ hk _ => hk
    · exact Filter.Eventually.of_forall fun _ htail => (hdisjoint htail).elim
  have hall : ∀ᶠ k : Nat in Filter.atTop,
      (let j := L.φ k
       let Y := X.obj j
       letI : TopologicalSpace Y.M := Y.topology
       letI : ChartedSpace H Y.M := Y.charted
       letI : IsManifold I ∞ Y.M := Y.smooth
       letI : T2Space Y.M := Y.t2
       letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
       letI : MetricSpace Y.M := (P j).ms
       (∀ alpha : LiveSlot L inp.pack r,
          transitionPatch L alpha ⊆ Metric.ball 0
              (d.chart j
                (seqCenterD inp.decay P L k (alpha.1 : Nat))).radius ∧
          Set.MapsTo
            (d.chart j
              (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom
            (transitionPatch L alpha)
            (L.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                L.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
        L.hatSourceBall inp.decay P r k ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (d.chart j
              (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom ''
                interior (innerTransitionCore L alpha) ∧
        ∀ y ∈ L.hatSourceBall inp.decay P r k,
          ∃ (alpha : LiveSlot L inp.pack r) (z : E),
            (d.chart j
                (seqCenterD inp.decay P L k (alpha.1 : Nat))).hom z = y ∧
              Metric.closedBall z (transitionCoreBuffer L alpha) ⊆
                interior (innerTransitionCore L alpha)) ∧
      ((∀ gamma : Fin (inp.pack.A r),
          (L.alive (gamma : Nat) = false →
            seqCenter inp.decay inp.D P (L.φ k) (gamma : Nat) = none) ∧
          (L.alive (gamma : Nat) = true →
            seqCenter inp.decay inp.D P (L.φ k) (gamma : Nat) =
              some (seqCenterD inp.decay P L k (gamma : Nat)))) ∧
        ∀ (alpha : LiveSlot L inp.pack r) (gamma : Fin (inp.pack.A r)),
          (∀ᶠ n : Nat in Filter.atTop,
              ¬ BInter inp.decay inp.D P L.lamInf
                (alpha.1 : Nat) (gamma : Nat) (L.φ n)) →
            ¬ BInter inp.decay inp.D P L.lamInf
              (alpha.1 : Nat) (gamma : Nat) (L.φ k)) ∧
      ∀ pair : PairSlot,
        (d.chartOverlapOn (L.φ k)
            (seqCenterD inp.decay P L k (pair.1.1 : Nat))
            (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
            (Metric.ball 0 (8 * L.lamInf (pair.1.1 : Nat))) ∧
          Set.MapsTo
            (d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat)))
            (Metric.ball 0 (8 * L.lamInf (pair.1.1 : Nat)))
            (Metric.ball 0 (72 * L.lamInf (pair.2.1.1 : Nat))) ∧
          ∀ z ∈ Metric.ball 0 (8 * L.lamInf (pair.1.1 : Nat)),
            ‖d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat)) z‖ =
                inp.decay.dist (L.φ k)
                  (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
                  (d.chartMap (L.φ k)
                    (seqCenterD inp.decay P L k (pair.1.1 : Nat)) z)) ∧
        (d.chartOverlapOn (L.φ k)
            (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
            (seqCenterD inp.decay P L k (pair.1.1 : Nat))
            (Metric.ball 0 (8 * L.lamInf (pair.2.1.1 : Nat))) ∧
          Set.MapsTo
            (d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.1.1 : Nat)))
            (Metric.ball 0 (8 * L.lamInf (pair.2.1.1 : Nat)))
            (Metric.ball 0 (72 * L.lamInf (pair.1.1 : Nat))) ∧
          ∀ z ∈ Metric.ball 0 (8 * L.lamInf (pair.2.1.1 : Nat)),
            ‖d.chartTransition (L.φ k)
              (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
              (seqCenterD inp.decay P L k (pair.1.1 : Nat)) z‖ =
                inp.decay.dist (L.φ k)
                  (seqCenterD inp.decay P L k (pair.1.1 : Nat))
                  (d.chartMap (L.φ k)
                    (seqCenterD inp.decay P L k (pair.2.1.1 : Nat)) z)) ∧
        Metric.ball (0 : E) (72 * L.lamInf (pair.1.1 : Nat)) ⊆
          Metric.ball 0
            (d.ratio * inp.decay.mu
              (inp.decay.dist (L.φ k)
                (seqCenterD inp.decay P L k (pair.1.1 : Nat))
                (X.obj (L.φ k)).basepoint)) ∧
        Metric.ball (0 : E) (72 * L.lamInf (pair.2.1.1 : Nat)) ⊆
          Metric.ball 0
            (d.ratio * inp.decay.mu
              (inp.decay.dist (L.φ k)
                (seqCenterD inp.decay P L k (pair.2.1.1 : Nat))
                (X.obj (L.φ k)).basepoint)) := by
    filter_upwards [d.transition_patch_eventually inp aMin hphys P L hcomplete hconn r hratio,
      Filter.eventually_all.mpr hcenter,
      Filter.eventually_all.mpr fun alpha => Filter.eventually_all.mpr (hsep alpha),
      Filter.eventually_all.mpr hpair] with k hpatchK hcenterK hsepK hpairK
    exact ⟨hpatchK, ⟨hcenterK, hsepK⟩, hpairK⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  let shift : Nat → Nat := fun k => k + N
  have hshift : StrictMono shift := by
    intro a b hab
    exact Nat.add_lt_add_right hab N
  let L0 := L.subseq hshift
  have hstage (k : Nat) := hN (shift k) (by
    simpa only [shift] using Nat.le_add_left N k)
  let d0 := d.subseq L0.φ
  let x0 : PairSlot → ∀ k : Nat, ((X.subseq L0.φ).obj k).M :=
    fun pair k => seqCenterD inp.decay P L0 k (pair.1.1 : Nat)
  let y0 : PairSlot → ∀ k : Nat, ((X.subseq L0.φ).obj k).M :=
    fun pair k => seqCenterD inp.decay P L0 k (pair.2.1.1 : Nat)
  let U8 : PairSlot → Set E := fun pair =>
    Metric.ball 0 (8 * L.lamInf (pair.1.1 : Nat))
  let V8 : PairSlot → Set E := fun pair =>
    Metric.ball 0 (8 * L.lamInf (pair.2.1.1 : Nat))
  let Ua : PairSlot → Set E := fun pair =>
    Metric.ball 0 (72 * L.lamInf (pair.1.1 : Nat))
  let Va : PairSlot → Set E := fun pair =>
    Metric.ball 0 (72 * L.lamInf (pair.2.1.1 : Nat))
  obtain ⟨tau, htau, hlim⟩ :=
    trans_fin (I := I) (X := X.subseq L0.φ)
      (Finset.univ : Finset PairSlot) d0 x0 y0 U8 V8 Ua Va
      (fun _ _ => Metric.isOpen_ball)
      (fun _ _ => Metric.isOpen_ball)
      (fun _ _ => Metric.isOpen_ball)
      (fun _ _ => Metric.isOpen_ball)
      (fun pair _ => by
        refine ⟨72 * L.lamInf (pair.1.1 : Nat), ?_⟩
        intro z hz
        exact le_of_lt (by
          simpa only [Ua, Metric.mem_ball, dist_zero_right] using hz))
      (fun pair _ => by
        refine ⟨72 * L.lamInf (pair.2.1.1 : Nat), ?_⟩
        intro z hz
        exact le_of_lt (by
          simpa only [Va, Metric.mem_ball, dist_zero_right] using hz))
      (fun pair _ k => by
        have hk := (hstage k).2.2 pair
        with_unfolding_all
          exact hk.2.2.1)
      (fun pair _ k => by
        have hk := (hstage k).2.2 pair
        with_unfolding_all
          exact hk.2.2.2)
      (fun pair _ k => by
        have hk := (hstage k).2.2 pair
        with_unfolding_all
          exact hk.1.1)
      (fun pair _ k => by
        have hk := (hstage k).2.2 pair
        with_unfolding_all
          exact hk.2.1.1)
      (fun pair _ k => by
        have hk := (hstage k).2.2 pair
        with_unfolding_all
          exact hk.1.2.1)
      (fun pair _ k => by
        have hk := (hstage k).2.2 pair
        with_unfolding_all
          exact hk.2.1.2.1)
  have hlim0 (pair : PairSlot) :=
    hlim pair (Finset.mem_univ pair)
  let J : PairSlot → E → E := fun pair =>
    Classical.choose (hlim0 pair)
  let Jbar : PairSlot → E → E := fun pair =>
    Classical.choose (Classical.choose_spec (hlim0 pair))
  have hspec (pair : PairSlot) :
      ContDiffOn Real (⊤ : ℕ∞) (J pair) (U8 pair) ∧
      ContDiffOn Real (⊤ : ℕ∞) (Jbar pair) (V8 pair) ∧
      MapCInfConvOnCompacts (U8 pair)
        (fun k => d0.chartTransition (tau k)
          (x0 pair (tau k)) (y0 pair (tau k))) (J pair) ∧
      MapCInfConvOnCompacts (V8 pair)
        (fun k => d0.chartTransition (tau k)
          (y0 pair (tau k)) (x0 pair (tau k))) (Jbar pair) ∧
      (∀ z ∈ U8 pair, J pair z ∈ V8 pair →
        Jbar pair (J pair z) = z) ∧
      (∀ z ∈ V8 pair, Jbar pair z ∈ U8 pair →
        J pair (Jbar pair z) = z) := by
    simpa only [J, Jbar] using
      Classical.choose_spec (Classical.choose_spec (hlim0 pair))
  let phi : Nat → Nat := shift ∘ tau
  have hphi : StrictMono phi := hshift.comp htau
  let Lphi := L.subseq hphi
  let U : LiveSlot L inp.pack r → Set E := fun alpha => transitionPatch L alpha
  let C0 : LiveSlot L inp.pack r → Set E := fun alpha => innerTransitionCore L alpha
  let C1 : LiveSlot L inp.pack r → Set E := fun alpha => outerTransitionCore L alpha
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  let aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real := fun alpha gamma =>
    if htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma then
      let target := Classical.choose htarget
      fun z => gluingBump (L.lamInf (gamma : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))
        (‖Jinf alpha target z‖ ^ 2)
    else fun _ => 0
  have hpatchPhi (k : Nat) :
      let j := Lphi.φ k
      let Y := X.obj j
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P j).ms
      (∀ alpha : LiveSlot L inp.pack r,
        U alpha ⊆ Metric.ball 0
            (d.chart j
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).radius ∧
        Set.MapsTo
          (d.chart j
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom
          (U alpha)
          (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              Lphi.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
      Lphi.hatSourceBall inp.decay P r k ⊆
        ⋃ alpha : LiveSlot L inp.pack r,
          (d.chart j
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom ''
              interior (C0 alpha) ∧
      ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          (d.chart j
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom z = y ∧
            Metric.closedBall z (transitionCoreBuffer L alpha) ⊆
              interior (C0 alpha) := by
    have hk := (hstage (tau k)).1
    dsimp only [U, C0]
    convert hk using 1
    all_goals
      simp only [Lphi, phi, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq, NetLimitData.hatBall_subseq,
        NetLimitData.innerBall_subseq, NetLimitData.hatSourceBall_subseq]
    all_goals rfl
  have hgeom := transition_patch_geometry inp P L r
  have hlimAll : ∀ alpha,
      HasAtomWeightLimOn (I := I) d.chart
        inp.decay inp.hD P Lphi inp.realizes inp.pack r hr
        (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (U alpha) (aInf alpha) := by
    intro alpha
    let alphaPhi : LiveSlot Lphi inp.pack r :=
      ⟨alpha.1, by simpa only [Lphi, NetLimitData.subseq] using alpha.2⟩
    let beta : ∀ k : Nat, (X.obj (Lphi.φ k)).M :=
      fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
    have hU8alpha :
        U alpha ⊆ Metric.ball (0 : E)
          (8 * L.lamInf (alpha.1 : Nat)) := by
      simpa only [U] using hgeom.2.1 alpha
    have hsourcePhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M :=
          (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M :=
          (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
          (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        Set.MapsTo
          (d.chart (Lphi.φ k) (beta k)).hom
          (U alpha)
          (⋃ gamma : Fin (inp.pack.A r),
            Lphi.innerBall inp.decay inp.D P inp.pack r k gamma) := by
      let : TopologicalSpace (X.obj (Lphi.φ k)).M :=
        (X.obj (Lphi.φ k)).topology
      let : ChartedSpace H (X.obj (Lphi.φ k)).M :=
        (X.obj (Lphi.φ k)).charted
      let : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
        (X.obj (Lphi.φ k)).smooth
      let : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
        (X.obj (Lphi.φ k)).t2TangentBundle
      intro z hz
      exact ((hpatchPhi k).1 alpha).2 hz |>.2
    have hJInf (target : InterSlot L inp.pack r alpha) :
        ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target) (U alpha) := by
      have hs := (hspec (⟨alpha, target⟩ : PairSlot)).1.mono hU8alpha
      simpa only [Jinf, J, U8] using hs
    have hJConv (target : InterSlot L inp.pack r alpha) :
        MapCInfConvOnCompacts (U alpha)
          (fun k => d.chartTransition (Lphi.φ k)
            (beta k)
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Jinf alpha target) := by
      intro K hK hKU p
      have hc := (hspec (⟨alpha, target⟩ : PairSlot)).2.2.1
        K hK (hKU.trans hU8alpha) p
      with_unfolding_all
        exact hc
    have hJStage (target : InterSlot L inp.pack r alpha) (k : Nat) :
        ContDiffOn Real (⊤ : ℕ∞)
          (d.chartTransition (Lphi.φ k)
            (beta k)
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (U alpha) := by
      have hp := (hstage (tau k)).2.2 (⟨alpha, target⟩ : PairSlot)
      have hov :
          d.chartOverlapOn (Lphi.φ k)
            (beta k)
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
            (Metric.ball (0 : E)
              (8 * L.lamInf (alpha.1 : Nat))) := by
        with_unfolding_all
          exact hp.1.1
      let : TopologicalSpace (X.obj (Lphi.φ k)).M :=
        (X.obj (Lphi.φ k)).topology
      let : ChartedSpace H (X.obj (Lphi.φ k)).M :=
        (X.obj (Lphi.φ k)).charted
      let : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
        (X.obj (Lphi.φ k)).smooth
      let : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
        (X.obj (Lphi.φ k)).t2TangentBundle
      have hs := (d.chart (Lphi.φ k) (beta k)).transition_smooth
        (d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
        (by simpa only [BoundedGeometryNormalChartData.chartOverlapOn] using hov)
      simpa only [BoundedGeometryNormalChartData.chartTransition] using hs.mono hU8alpha
    have hread (target : InterSlot L inp.pack r alpha) :
        ∀ᶠ k : Nat in Filter.atTop,
          ∀ z ∈ U alpha,
            ‖d.chartTransition (Lphi.φ k)
              (beta k)
              (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) z‖ =
              inp.decay.dist (Lphi.φ k)
                (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
                (d.chartMap (Lphi.φ k) (beta k) z) := by
      refine Filter.Eventually.of_forall fun k z hz => ?_
      have hp := (hstage (tau k)).2.2 (⟨alpha, target⟩ : PairSlot)
      have hreadK := hp.1.2.2 z (hU8alpha hz)
      with_unfolding_all
        exact hreadK
    have hatom (gamma : Fin (inp.pack.A r)) :
        MapCInfConvOnCompacts (U alpha)
          (fun k => seqAtomOn (I := I) d.chart inp.decay inp.hD P Lphi
            inp.pack r beta gamma k)
          (aInf alpha gamma) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hslot : target.1.1 = gamma := Classical.choose_spec htarget
        let gammaPhi : LiveSlot Lphi inp.pack r :=
          ⟨target.1.1, by
            simpa only [Lphi, NetLimitData.subseq] using target.1.2⟩
        have hc := d.atomOn_live_conv inp P Lphi r
          alphaPhi gammaPhi (hgeom.1 alpha) (hJConv target)
          (hJStage target) (hJInf target) (hread target)
        simpa only [aInf, dif_pos htarget, target, Jinf, beta, alphaPhi,
          gammaPhi, hslot, Lphi, NetLimitData.subseq_lamInf] using hc
      · cases hgamma : L.alive (gamma : Nat) with
        | false =>
            have hgammaPhi : Lphi.alive (gamma : Nat) = false := by
              simpa only [Lphi, NetLimitData.subseq] using hgamma
            simpa only [aInf, dif_neg htarget] using
              atomOn_dead_conv (I := I) d.chart inp.decay inp.hD P Lphi
                inp.pack r beta gamma (hgeom.1 alpha) hgammaPhi
        | true =>
            rcases hstable (alpha.1 : Nat) (gamma : Nat) with hinter | hdisjoint
            · exact (htarget
                ⟨⟨⟨gamma, hgamma⟩, hinter⟩, rfl⟩).elim
            · have hdisjointPhi : ∀ᶠ k in Filter.atTop,
                  ¬ BInter inp.decay inp.D P Lphi.lamInf
                    (alpha.1 : Nat) (gamma : Nat) (Lphi.φ k) := by
                with_unfolding_all
                  exact hphi.tendsto_atTop.eventually hdisjoint
              have hsourceTail : ∀ᶠ k in Filter.atTop,
                  letI : TopologicalSpace (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).topology
                  letI : ChartedSpace H (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).charted
                  letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).smooth
                  letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
                    (X.obj (Lphi.φ k)).t2TangentBundle
                  Set.MapsTo
                    (d.chart (Lphi.φ k) (beta k)).hom
                    (U alpha)
                    (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1) :=
                Filter.Eventually.of_forall fun k z hz =>
                  ((hpatchPhi k).1 alpha).2 hz |>.1
              simpa only [aInf, dif_neg htarget] using
                atomOn_disjoint_conv (I := I) d.chart inp.decay inp.hD P Lphi
                  inp.pack r beta alpha.1 gamma (hgeom.1 alpha)
                  hsourceTail hdisjointPhi
    have hdead (gamma : Fin (inp.pack.A r))
        (hgamma : Lphi.alive (gamma : Nat) = false) :
        aInf alpha gamma = 0 := by
      have hnone : ¬ ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma := by
        rintro ⟨target, hslot⟩
        have htrue : Lphi.alive (gamma : Nat) = true := by
          simpa only [Lphi, NetLimitData.subseq, hslot] using target.1.2
        rw [hgamma] at htrue
        contradiction
      simp only [aInf, dif_neg hnone]
      rfl
    have hatomSmooth (k : Nat) (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (seqAtomOn (I := I) d.chart inp.decay inp.hD P Lphi
            inp.pack r beta gamma k) (U alpha) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hslot : target.1.1 = gamma := Classical.choose_spec htarget
        have hgamma : L.alive (gamma : Nat) = true := by
          simpa only [hslot] using target.1.2
        have hc0 :=
          ((hstage (tau k)).2.1.1 gamma).2 hgamma
        have hc :
            seqCenter inp.decay inp.D P (Lphi.φ k) (gamma : Nat) =
              some (seqCenterD inp.decay P Lphi k (gamma : Nat)) := by
          with_unfolding_all
            exact hc0
        have hreadK (z : E) (hz : z ∈ U alpha) :
            ‖d.chartTransition (Lphi.φ k)
              (beta k)
              (seqCenterD inp.decay P Lphi k (gamma : Nat)) z‖ =
              inp.decay.dist (Lphi.φ k)
                (seqCenterD inp.decay P Lphi k (gamma : Nat))
                (d.chartMap (Lphi.φ k) (beta k) z) := by
          have hp := (hstage (tau k)).2.2
            (⟨alpha, target⟩ : PairSlot)
          have hr := hp.1.2.2 z (hU8alpha hz)
          simpa only [Lphi, phi, NetLimitData.subseq_phi,
            Function.comp_apply, beta, seqCenterD_subseq, hslot] using hr
        have hsmooth := normBump_smooth (hJStage target k)
          (Lphi.lamInf (gamma : Nat))
          (inp.decay.lambda_pos inp.hD (Lphi.rInf (gamma : Nat)))
        have hsmooth' : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun z => gluingBump (Lphi.lamInf (gamma : Nat))
              (inp.decay.lambda_pos inp.hD (Lphi.rInf (gamma : Nat)))
              (‖d.chartTransition (Lphi.φ k)
                (beta k)
                (seqCenterD inp.decay P Lphi k (gamma : Nat)) z‖ ^ 2))
            (U alpha) := by
          simpa only [hslot] using hsmooth
        exact ContDiffOn.congr hsmooth' fun z hz =>
          atomOn_readout inp d P Lphi r k alpha.1 gamma hc
            (hreadK z hz)
      · cases hgamma : L.alive (gamma : Nat) with
        | false =>
            have hnone0 :=
              ((hstage (tau k)).2.1.1 gamma).1 hgamma
            have hnone :
                seqCenter inp.decay inp.D P (Lphi.φ k) (gamma : Nat) = none := by
              simpa only [Lphi, phi, L0, Function.comp_apply,
                NetLimitData.subseq] using hnone0
            refine ContDiffOn.congr
              (contDiffOn_const : ContDiffOn Real (∞ : WithTop ℕ∞)
                (fun _ : E => (0 : Real)) (U alpha)) fun z _ => ?_
            simp [seqAtomOn,
              seqAtom_none inp.decay inp.hD P Lphi inp.pack r k gamma hnone]
        | true =>
            rcases hstable (alpha.1 : Nat) (gamma : Nat) with hinter | hdisjoint
            · exact (htarget
                ⟨⟨⟨gamma, hgamma⟩, hinter⟩, rfl⟩).elim
            · have hdisjoint0 :=
                (hstage (tau k)).2.1.2 alpha gamma hdisjoint
              have hdisjointK :
                  ¬ BInter inp.decay inp.D P Lphi.lamInf
                    (alpha.1 : Nat) (gamma : Nat) (Lphi.φ k) := by
                with_unfolding_all
                  exact hdisjoint0
              refine ContDiffOn.congr
                (contDiffOn_const : ContDiffOn Real (∞ : WithTop ℕ∞)
                  (fun _ : E => (0 : Real)) (U alpha)) fun z hz => ?_
              by_contra hne
              apply hdisjointK
              exact Lphi.binter_of_mem_hat inp.decay inp.hD P inp.pack r k
                (((hpatchPhi k).1 alpha).2 hz).1
                (seqAtom_mem_hat_raw inp.decay inp.hD P Lphi inp.pack r k
                  gamma (by simpa only [seqAtomOn] using hne))
    have hatomInfSmooth (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞) (aInf alpha gamma) (U alpha) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        simpa only [aInf, dif_pos htarget, target] using
          normBump_smooth (hJInf target)
            (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))
      · simpa only [aInf, dif_neg htarget] using
          (contDiffOn_const : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun _ : E => (0 : Real)) (U alpha))
    exact HasAtomWeightLimOn.of_raw (I := I) d.chart inp.hD P Lphi
      inp.realizes inp.pack r hr beta (U alpha) (hgeom.1 alpha)
      hsourcePhi (aInf alpha) hdead hatom hatomSmooth hatomInfSmooth
  have hweightAll : ∀ alpha,
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ)
        (fun z gamma =>
          rawWeights
            (cutRaw
              (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
              (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
            z gamma) := by
    intro alpha
    exact (hlimAll alpha).weight_data_raw
      (Filter.Eventually.of_forall fun k z hz =>
        ((hpatchPhi k).1 alpha).2 hz |>.2)
  have htransAll : ∀ alpha target,
      ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
      ContinuousOn (Jinf alpha target)
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      ContinuousOn (Jbarinf alpha target)
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
      MapCInfConvOnCompacts
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
        (fun k => d.chartTransition (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
        (Jinf alpha target) ∧
      MapCInfConvOnCompacts
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
        (fun k => d.chartTransition (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
        (Jbarinf alpha target) ∧
      (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
        Jinf alpha target z ∈
            Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
          Jbarinf alpha target (Jinf alpha target z) = z) ∧
      ∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
        Jbarinf alpha target w ∈
            Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
          Jinf alpha target (Jbarinf alpha target w) = w := by
    intro alpha target
    have hs := hspec (⟨alpha, target⟩ : PairSlot)
    have hsmoothF : ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) := by
      simpa only [Jinf, J, U8] using hs.1
    have hsmoothR : ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
      simpa only [Jbarinf, Jbar, V8] using hs.2.1
    refine ⟨hsmoothF, hsmoothR, hsmoothF.continuousOn,
      hsmoothR.continuousOn, ?_, ?_, ?_, ?_⟩
    · with_unfolding_all
        exact hs.2.2.1
    · with_unfolding_all
        exact hs.2.2.2.1
    · simpa only [Jinf, Jbarinf, J, Jbar, U8, V8] using
        hs.2.2.2.2.1
    · simpa only [Jinf, Jbarinf, J, Jbar, U8, V8] using
        hs.2.2.2.2.2
  have hsmoothAll (alpha : LiveSlot L inp.pack r)
      (target : InterSlot L inp.pack r alpha) (k : Nat) :
      let Y := X.obj (Lphi.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      ContDiffOn Real (⊤ : ℕ∞)
        (d.chartTransition (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      ContDiffOn Real (⊤ : ℕ∞)
        (d.chartTransition (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
    let : TopologicalSpace (X.obj (Lphi.φ k)).M :=
      (X.obj (Lphi.φ k)).topology
    let : ChartedSpace H (X.obj (Lphi.φ k)).M :=
      (X.obj (Lphi.φ k)).charted
    let : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
      (X.obj (Lphi.φ k)).smooth
    let : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
      (X.obj (Lphi.φ k)).t2TangentBundle
    have hp := (hstage (tau k)).2.2 (⟨alpha, target⟩ : PairSlot)
    have hovF :
        d.chartOverlapOn (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
          (Metric.ball (0 : E)
            (8 * L.lamInf (alpha.1 : Nat))) := by
      with_unfolding_all
        exact hp.1.1
    have hovR :
        d.chartOverlapOn (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          (Metric.ball (0 : E)
            (8 * L.lamInf (target.1.1 : Nat))) := by
      with_unfolding_all
        exact hp.2.1.1
    have hsF :=
      (d.chart (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).transition_smooth
        (d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
        (by simpa only [BoundedGeometryNormalChartData.chartOverlapOn] using hovF)
    have hsR :=
      (d.chart (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))).transition_smooth
        (d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
        (by simpa only [BoundedGeometryNormalChartData.chartOverlapOn] using hovR)
    exact ⟨by simpa only [BoundedGeometryNormalChartData.chartTransition] using hsF,
      by simpa only [BoundedGeometryNormalChartData.chartTransition] using hsR⟩
  have hchartAll (k : Nat) :
      let Y := X.obj (Lphi.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
      (∀ alpha : LiveSlot L inp.pack r,
        U alpha ⊆ Metric.ball 0
            (d.chart (Lphi.φ k)
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).radius ∧
        Set.MapsTo
          (d.chart (Lphi.φ k)
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom
          (U alpha)
          (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              Lphi.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
      Lphi.hatSourceBall inp.decay P r k ⊆
        ⋃ alpha : LiveSlot L inp.pack r,
          (d.chart (Lphi.φ k)
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom ''
              U alpha := by
    let : TopologicalSpace (X.obj (Lphi.φ k)).M :=
      (X.obj (Lphi.φ k)).topology
    let : ChartedSpace H (X.obj (Lphi.φ k)).M :=
      (X.obj (Lphi.φ k)).charted
    let : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
      (X.obj (Lphi.φ k)).smooth
    let : T2Space (X.obj (Lphi.φ k)).M :=
      (X.obj (Lphi.φ k)).t2
    let : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
      (X.obj (Lphi.φ k)).t2TangentBundle
    let : MetricSpace (X.obj (Lphi.φ k)).M := (P (Lphi.φ k)).ms
    refine ⟨(hpatchPhi k).1, ?_⟩
    intro y hy
    obtain ⟨alpha, z, hz, rfl⟩ :=
      Set.mem_iUnion.mp ((hpatchPhi k).2.1 hy)
    refine Set.mem_iUnion.mpr ⟨alpha, z, ?_, rfl⟩
    exact hgeom.2.2.2.2.2.1 alpha
      (interior_subset
        (hgeom.2.2.2.2.1 alpha (interior_subset hz)))
  refine ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, ?_⟩
  dsimp only [HasSuppConvDataOn]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa only [U] using hgeom.1
  · simpa only [U] using hgeom.2.1
  · simpa only [C0] using hgeom.2.2.1
  · simpa only [C1] using hgeom.2.2.2.1
  · simpa only [C0, C1] using hgeom.2.2.2.2.1
  · simpa only [C1, U] using hgeom.2.2.2.2.2.1
  · simpa only [C0] using hgeom.2.2.2.2.2.2.1
  · simpa only [C0] using hgeom.2.2.2.2.2.2.2.1
  · refine ⟨fun alpha => transitionCoreBuffer L alpha, hgeom.2.2.2.2.2.2.2.2, ?_⟩
    intro k
    with_unfolding_all
      exact (hpatchPhi k).2.2
  · intro k
    with_unfolding_all
      exact (hpatchPhi k).2.1
  · intro k
    simp only [NormalChartFamily.hom, NormalChartFamily.radius]
    convert hchartAll k using 1
    all_goals
      simp only [Lphi, phi, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq, NetLimitData.hatBall_subseq,
        NetLimitData.innerBall_subseq, NetLimitData.hatSourceBall_subseq]
    all_goals rfl
  · with_unfolding_all
      exact hlimAll
  · exact hweightAll
  · intro alpha target
    with_unfolding_all
      exact htransAll alpha target
  · intro alpha target k
    with_unfolding_all
      exact hsmoothAll alpha target k

end BoundedGeometryNormalChartData

end HCGCompactness
end DifferentialGeometry
