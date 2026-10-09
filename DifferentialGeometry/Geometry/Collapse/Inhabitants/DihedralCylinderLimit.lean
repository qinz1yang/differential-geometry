import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralModelMaps
import DifferentialGeometry.Geometry.Metric.LocalPullDistance
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Geometry.Metric.RestrictionDistance
import DifferentialGeometry.Geometry.Metric.Comparison.IsometricBalls
import DifferentialGeometry.Geometry.Collapse.CompleteRiemannianSegments

/-!
The actual physical cylinder charts cover the middle of the same dihedral carrier. Their
buffered model balls preserve ambient distances and map onto the actual target balls. At a
fixed positive sphere scale, all sequences with both physical margins diverging converge
pointedly to the complete spherical cylinder, for arbitrary moving sphere isometries.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse GC.Endpoint GC.Geometry.SphericalProduct
open Set
open scoped Manifold ContDiff NNReal ENNReal
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
open private edistOf_localPullMetric_le
from DifferentialGeometry.Geometry.Metric.DistancePullback
universe u
namespace DifferentialGeometry.Geometry.Collapse

theorem dihedralCylinderImage_contains_middle (L : ℝ) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (q : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier)
    (hq0 : 0 < dihedralAxis L q) (hqL : dihedralAxis L q < L) :
    q ∈ dihedralCylinderMap L hL s A '' dihedralCylinderDomain L s := by
  obtain ⟨p, hp, ht, haxis⟩ := exists_dihedralCanonicalLift q
  have ht0 : 0 < 2 * L * p.2 := by rwa [haxis L] at hq0
  have htL : 2 * L * p.2 < L := by rwa [haxis L] at hqL
  let z := sphereCylinderRechartDiffeomorph
    ((sphereDiffeo (n := 2) A).symm p.1, 2 * L * p.2 - s)
  refine ⟨z, ?_, ?_⟩
  · change -s < 2 * L * p.2 - s ∧ 2 * L * p.2 - s < L - s
    constructor <;> linarith
  · change dihedralStandardPresentation.proj (sphereCylinderRechartDiffeomorph.symm
      (dihedralCylinderPhysicalDiffeo L hL s A z)) = q
    rw [dihedralCylinderPhysical_formula]
    have hfrac : (s + (2 * L * p.2 - s)) / (2 * L) = p.2 := by field_simp; ring
    change dihedralStandardPresentation.proj
      ((sphereDiffeo (n := 2) A) ((sphereDiffeo (n := 2) A).symm p.1),
        (s + (2 * L * p.2 - s)) / (2 * L)) = q
    rw [(sphereDiffeo (n := 2) A).apply_symm_apply, hfrac]
    exact hp
theorem dihedralCylinderMap_axis (L : ℝ) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (z : sphereCylinderRechart) (hz : z ∈ dihedralCylinderDomain L s) :
    dihedralAxis L (dihedralCylinderMap.{u} L hL s A z) = s + z.point.2 := by
  change dihedralAxis L (dihedralProjection (dihedralCylinderPhysicalDiffeo L hL s A z)) = _
  rw [dihedralAxis_projection, dihedralCylinderPhysical_formula]
  have hden : 0 < 2 * L := mul_pos (by norm_num) hL
  have hnum : 0 < s + z.point.2 := by
    change -s < z.point.2 ∧ z.point.2 < L - s at hz
    linarith [hz.1]
  have hphase : (s + z.point.2) / (2 * L) < 1 / 2 := by
    apply (div_lt_iff₀ hden).mpr
    change -s < z.point.2 ∧ z.point.2 < L - s at hz
    nlinarith [hz.2]
  have hn : ‖((s + z.point.2) / (2 * L) : AddCircle (1 : ℝ))‖ =
      (s + z.point.2) / (2 * L) := by
    have h := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr
      (by rw [abs_of_pos (div_pos hnum hden), abs_one]; exact hphase.le)
    simpa only [abs_of_pos (div_pos hnum hden)] using h
  rw [hn]
  field_simp

theorem dihedralCylinderTargetBall_image (ε L s R : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (hs : 0 < s) (hsL : s < L) (hR : 0 < R) (hRs : R ≤ s) (hRLs : R ≤ L - s)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    riemannianBallOf (dihedralMetric.{u} ε L hε hL)
      (dihedralCylinderMap L hL s A
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0))) R ⊆
      dihedralCylinderMap L hL s A '' dihedralCylinderDomain L s := by
  let n := sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)
  have hn : n ∈ dihedralCylinderDomain L s := by
    change -s < (0 : ℝ) ∧ (0 : ℝ) < L - s
    constructor <;> linarith
  have haxis : dihedralAxis L (dihedralCylinderMap L hL s A n) = s := by
    simpa only [n, sphereCylinderRechartDiffeomorph_point, add_zero] using
      dihedralCylinderMap_axis L hL s A n hn
  intro q hq
  have hd := (dihedralAxis_distance_le ε L hε hL
    (dihedralCylinderMap L hL s A n) q).trans_lt hq
  rw [haxis] at hd
  have ht : |s - dihedralAxis L q| < R := (ENNReal.ofReal_lt_ofReal_iff hR).mp hd
  have hb := abs_lt.mp ht
  apply dihedralCylinderImage_contains_middle L hL s A q
  · linarith [hb.2]
  · linarith [hb.1]

theorem dihedralCylinder_ball_edist_eq (ε L s : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (r : ℝ≥0) (hr : 0 < r) (hrs : 3 * (r : ℝ) ≤ s) (hrLs : 3 * (r : ℝ) ≤ L - s)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x y : sphereCylinderRechart)
    (hx : x ∈ riemannianBallOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) r)
    (hy : y ∈ riemannianBallOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) r) :
    riemannianEDistOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)) x y =
      riemannianEDistOf (dihedralMetric.{u} ε L hε hL)
        (dihedralCylinderMap L hL s A x) (dihedralCylinderMap L hL s A y) := by
  have hrR : 0 < (r : ℝ) := hr
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hrs
  have hsL : s < L := by linarith
  let n := sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)
  let gM := dihedralRechartedMetric ε (1 / 2) hε (by norm_num)
  let gQ := dihedralMetric.{u} ε L hε hL
  obtain ⟨jm, hjm, hsrc, htgt, hfun, hn, hmetric, hballs⟩ :=
    exists_dihedralCylinderPointedMetricChart ε L hε hL s hs hsL A
  let U : TopologicalSpace.Opens sphereCylinderRechart := ⟨jm.source, jm.open_source⟩
  let V : TopologicalSpace.Opens
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
    ⟨(jm : sphereCylinderRechart → _) '' (U : Set sphereCylinderRechart),
      DifferentialGeometry.image_opens_isOpen jm Subset.rfl⟩
  let D := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo jm (U := U) Subset.rfl
  have hmet : gM.restrictOpen U = Diffeomorph.pullbackMetricCross (gQ.restrictOpen V) D := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    have hm := congrArg (fun g : SmoothRiemannianMetric (𝓡 3) sphereCylinderRechart =>
      g.inner (z : sphereCylinderRechart) v w) hmetric
    rw [localPullMetric_inner (I := 𝓡 3) (J := 𝓡 3)
      (dihedralMetric ε L hε hL) jm hjm (z : sphereCylinderRechart) v w] at hm
    rw [DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo jm Subset.rfl z v,
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo jm Subset.rfl z w]
    exact hm.symm
  have hsource : {z | riemannianEDistOf gM n z < (3 * r : ℝ≥0)} ⊆ (U : Set _) := by
    have h := hballs (3 * (r : ℝ)) (by positivity) hrs hrLs
    change riemannianBallOf gM n ((3 * r : ℝ≥0) : ℝ) ⊆ jm.source at h
    change {z | riemannianEDistOf gM n z < (3 * r : ℝ≥0)} ⊆ jm.source
    simpa only [riemannianBallOf, ENNReal.ofReal_coe_nnreal] using h
  have htarget : {q | riemannianEDistOf gQ (jm n) q < (3 * r : ℝ≥0)} ⊆ (V : Set _) := by
    have h := dihedralCylinderTargetBall_image ε L s (3 * (r : ℝ)) hε hL hs hsL
      (by positivity) hrs hrLs A
    change riemannianBallOf gQ (dihedralCylinderMap L hL s A n)
      ((3 * r : ℝ≥0) : ℝ) ⊆ dihedralCylinderMap L hL s A '' dihedralCylinderDomain L s at h
    change {q | riemannianEDistOf gQ (jm n) q < (3 * r : ℝ≥0)} ⊆
      (jm : sphereCylinderRechart → _) '' jm.source
    rw [hfun, hsrc]
    simpa only [riemannianBallOf, ENNReal.ofReal_coe_nnreal] using h
  have hxr : x ∈ U := hballs r hrR (by linarith) (by linarith) hx
  have hyr : y ∈ U := hballs r hrR (by linarith) (by linarith) hy
  let xu : U := ⟨x, hxr⟩
  let yu : U := ⟨y, hyr⟩
  have hthird : (3 * r : ℝ≥0) / 3 = r := by field_simp
  have hxx : riemannianEDistOf gM n x < ((3 * r : ℝ≥0) / 3 : ℝ≥0) := by
    rw [hthird]
    simpa only [gM, n, riemannianBallOf, Set.mem_ofPred_eq,
      ENNReal.ofReal_coe_nnreal] using hx
  have hyy : riemannianEDistOf gM n y < ((3 * r : ℝ≥0) / 3 : ℝ≥0) := by
    rw [hthird]
    simpa only [gM, n, riemannianBallOf, Set.mem_ofPred_eq,
      ENNReal.ofReal_coe_nnreal] using hy
  have hqx : riemannianEDistOf gQ (jm n) (jm x) < ((3 * r : ℝ≥0) / 3 : ℝ≥0) := by
    have h := (edistOf_localPullMetric_le gQ jm hjm n x)
    rw [hmetric] at h
    exact h.trans_lt hxx
  have hqy : riemannianEDistOf gQ (jm n) (jm y) < ((3 * r : ℝ≥0) / 3 : ℝ≥0) := by
    have h := (edistOf_localPullMetric_le gQ jm hjm n y)
    rw [hmetric] at h
    exact h.trans_lt hyy
  calc
    _ = riemannianEDistOf (gM.restrictOpen U) xu yu :=
      (DifferentialGeometry.Geometry.Metric.riemannianEDistOf_restrictOpen_eq_of_ball_subset
        gM U n (3 * r) hsource xu yu hxx hyy).symm
    _ = riemannianEDistOf (gQ.restrictOpen V) (D xu) (D yu) := by
      rw [hmet, DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross]
    _ = riemannianEDistOf gQ (jm x) (jm y) :=
      DifferentialGeometry.Geometry.Metric.riemannianEDistOf_restrictOpen_eq_of_ball_subset
        gQ V (jm n) (3 * r) htarget (D xu) (D yu) hqx hqy
    _ = _ := by rw [hfun]
theorem dihedralCylinder_ball_image (ε L s r : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (hr : 0 < r) (hrs : 3 * r ≤ s) (hrLs : 3 * r ≤ L - s)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    dihedralCylinderMap.{u} L hL s A ''
      riemannianBallOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) r =
      riemannianBallOf (dihedralMetric ε L hε hL)
        (dihedralCylinderMap L hL s A
          (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0))) r := by
  have hs : 0 < s := by linarith
  have hsL : s < L := by linarith
  let n := sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)
  let gM := dihedralRechartedMetric ε (1 / 2) hε (by norm_num)
  let gQ := dihedralMetric.{u} ε L hε hL
  obtain ⟨jm, hjm, hsrc, htgt, hfun, hn, hmetric, hballs⟩ :=
    exists_dihedralCylinderPointedMetricChart ε L hε hL s hs hsL A
  let _modelSigma : SigmaCompactSpace sphereCylinderRechart :=
    sphereCylinderRechartDiffeomorph.symm.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let _modelMetric : MetricSpace sphereCylinderRechart := inducedMetricSpace gM
  let _modelProper : ProperSpace sphereCylinderRechart :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete
      (dihedralRechartedMetric_complete ε (1 / 2) hε (by norm_num))
  have hcpt : IsCompact (riemannianClosedBallOf gM n (2 * r)) := by
    rw [← inducedMetricSpace_closedBall gM n (by positivity)]
    exact isCompact_closedBall (x := n) (r := 2 * r)
  have hsource : riemannianClosedBallOf gM n (2 * r) ⊆ jm.source := by
    intro z hz
    apply hballs (3 * r) (by positivity) hrs hrLs
    exact hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hinner (z : sphereCylinderRechart) (hz : z ∈ riemannianClosedBallOf gM n (2 * r))
      (v : TangentSpace (𝓡 3) z) :
      gQ.inner (jm z) (mfderiv (𝓡 3) (𝓡 3) jm z v)
        (mfderiv (𝓡 3) (𝓡 3) jm z v) = gM.inner z v v := by
    have h := congrArg (fun g : SmoothRiemannianMetric (𝓡 3) sphereCylinderRechart =>
      g.inner z v v) hmetric
    rw [localPullMetric_inner (I := 𝓡 3) (J := 𝓡 3) gQ jm hjm z v v] at h
    exact h
  have himage : (jm : sphereCylinderRechart → _) '' riemannianBallOf gM n r =
      riemannianBallOf gQ (jm n) r := by
    apply Set.Subset.antisymm
    · rintro q ⟨z, hz, rfl⟩
      have hd := edistOf_localPullMetric_le gQ jm hjm n z
      rw [hmetric] at hd
      exact hd.trans_lt hz
    · intro q hq
      let d := (riemannianEDistOf gQ (jm n) q).toReal
      have hdr : d < r := ENNReal.toReal_lt_of_lt_ofReal hq
      have hfin : riemannianEDistOf gQ (jm n) q ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq.le
      have hqD : q ∈ riemannianClosedBallOf gQ (jm n) d := by
        change riemannianEDistOf gQ (jm n) q ≤ ENNReal.ofReal d
        rw [ENNReal.ofReal_toReal hfin]
      obtain ⟨hqt, hpre⟩ :=
        DifferentialGeometry.PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower
          gM gQ jm n ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) < 1)
          (by linarith : 1 * d < 2 * r) hcpt hsource
          (fun z hz v => by rw [one_pow, one_mul, hinner z hz v]) q hqD
      refine ⟨jm.symm q, ?_, jm.right_inv' hqt⟩
      have hpre' : riemannianEDistOf gM n (jm.symm q) ≤ ENNReal.ofReal d := by
        simpa only [one_mul, riemannianClosedBallOf, Set.mem_ofPred_eq, d] using hpre
      exact hpre'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hdr)
  rw [hfun] at himage
  exact himage

theorem exists_dihedralCylinderPointedApprox (ε L s R δ : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (hδ : 0 < δ) (hδR : δ < R) (hRs : 9 * R ≤ s) (hRLs : 9 * R ≤ L - s)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    let _modelMetric : MetricSpace sphereCylinderRechart :=
      inducedMetricSpace (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
    let _targetMetric : MetricSpace
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
      inducedMetricSpace (dihedralMetric ε L hε hL)
    Nonempty (GC.MetricGeometry.PointedBallApprox
      (dihedralCylinderMap L hL s A
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)))
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) R δ) := by
  let gM := dihedralRechartedMetric ε (1 / 2) hε (by norm_num)
  let gQ := dihedralMetric.{u} ε L hε hL
  let _modelMetric : MetricSpace sphereCylinderRechart := inducedMetricSpace gM
  let _targetMetric : MetricSpace
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
    inducedMetricSpace gQ
  let n := sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)
  let F := dihedralCylinderMap.{u} L hL s A
  have hR : 0 < R := hδ.trans hδR
  have hdist (x y : sphereCylinderRechart)
      (hx : dist x n ≤ 2 * R) (hy : dist y n ≤ 2 * R) : dist (F x) (F y) = dist x y := by
    have hxB : x ∈ riemannianBallOf gM n (3 * R) := by
      rw [← inducedMetricSpace_ball gM n]
      exact lt_of_le_of_lt hx (by linarith)
    have hyB : y ∈ riemannianBallOf gM n (3 * R) := by
      rw [← inducedMetricSpace_ball gM n]
      exact lt_of_le_of_lt hy (by linarith)
    have he := dihedralCylinder_ball_edist_eq ε L s hε hL ⟨3 * R, by positivity⟩
      (by change 0 < 3 * R; positivity)
      (by change 3 * (3 * R) ≤ s; nlinarith)
      (by change 3 * (3 * R) ≤ L - s; nlinarith) A x y hxB hyB
    exact congrArg ENNReal.toReal he.symm
  have himage : F '' Metric.ball n (2 * R) = Metric.ball (F n) (2 * R) := by
    rw [inducedMetricSpace_ball gM n, inducedMetricSpace_ball gQ (F n)]
    exact dihedralCylinder_ball_image ε L s (2 * R) hε hL (by positivity)
      (by linarith) (by linarith) A
  let f : GC.MetricGeometry.PointedBallApprox n (F n) (2 * R) (δ / 4) := {
    error_pos := by positivity
    error_lt_radius := by linarith
    toFun := fun x => F x
    basepoint := rfl
    distortion := fun x y => by
      rw [hdist x y x.property y.property, sub_self, abs_zero]
      positivity
    coverage := fun y hy => by
      have hyB : y ∈ Metric.ball (F n) (2 * R) := by
        rw [Metric.mem_ball]
        linarith
      rw [← himage] at hyB
      obtain ⟨x, hx, heq⟩ := hyB
      refine ⟨⟨x, le_of_lt hx⟩, ?_⟩
      change dist y (F x) < δ / 4
      rw [heq, dist_self]
      positivity }
  have hrev := f.quasiInverse (s := R) (by linarith) (by linarith)
  have hfour : 4 * (δ / 4) = δ := by ring
  rw [hfour] at hrev
  exact ⟨hrev⟩
theorem dihedralCylinder_pointedGH (ε : ℝ) (hε : 0 < ε) (L s : ℕ → ℝ)
    (hL : ∀ i, 0 < L i) (hs : Filter.Tendsto s Filter.atTop Filter.atTop)
    (hLs : Filter.Tendsto (fun i => L i - s i) Filter.atTop Filter.atTop)
    (A : ℕ → EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    let _modelMetric : MetricSpace sphereCylinderRechart :=
      inducedMetricSpace (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
    let targetMetrics : ∀ _i : ℕ, MetricSpace
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
      fun i => inducedMetricSpace (dihedralMetric ε (L i) hε (hL i))
    @GC.MetricGeometry.PointedGHConverges
      (fun _ : ℕ =>
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier)
      targetMetrics sphereCylinderRechart _modelMetric
      (fun i => dihedralCylinderMap (L i) (hL i) (s i) (A i)
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)))
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) := by
  let _modelMetric : MetricSpace sphereCylinderRechart :=
    inducedMetricSpace (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
  let targetMetrics : ∀ _i : ℕ, MetricSpace
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
    fun i => inducedMetricSpace (dihedralMetric ε (L i) hε (hL i))
  let _modelSigma : SigmaCompactSpace sphereCylinderRechart :=
    sphereCylinderRechartDiffeomorph.symm.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  refine ⟨riemannianMetricComplete_iff_inducedMetricSpace.mp
    (dihedralRechartedMetric_complete ε (1 / 2) hε (by norm_num)), ?_⟩
  intro R δ hδ hδR
  filter_upwards [Filter.Tendsto.eventually_ge_atTop hs (9 * R),
    Filter.Tendsto.eventually_ge_atTop hLs (9 * R)] with i hsi hLsi
  exact exists_dihedralCylinderPointedApprox ε (L i) (s i) R δ hε (hL i) hδ hδR hsi hLsi (A i)

end DifferentialGeometry.Geometry.Collapse
