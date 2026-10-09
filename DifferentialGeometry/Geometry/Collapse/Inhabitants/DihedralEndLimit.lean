import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralEndMaps
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralCylinderLimit
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphCurves
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import DifferentialGeometry.Geometry.Metric.Approximation.TargetBasepointRepair

/-!
Actual endpoint physical maps preserve buffered ambient ball distances and cover the target
balls. At a fixed positive sphere scale, arbitrary moving physical heights converging to a
finite real height give the genuine endpoint pointed limit. Internally chosen partial charts
have exact anchors, exhaust every model ball and satisfy the original compact native metric
convergence clause on their actual open pullback domains.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse GC.Endpoint GC.Geometry.SphericalProduct
open scoped Manifold ContDiff NNReal ENNReal
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension
  dihedralEndSigma dihedralEndMetrizable dihedralEndRawConnected
open private edistOf_localPullMetric_le
from DifferentialGeometry.Geometry.Metric.DistancePullback
universe u
namespace DifferentialGeometry.Geometry.Collapse

theorem dihedralEndImage_contains_half (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (q : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier)
    (hq : (if b then L - dihedralAxis L q else dihedralAxis L q) < L / 2) :
    q ∈ dihedralEndMap L hL b A '' dihedralEndDomain L := by
  obtain ⟨p, hp, ht, haxis⟩ := exists_dihedralCanonicalLift q
  let t := if b then L - 2 * L * p.2 else 2 * L * p.2
  let z := sphereCylinderRechartDiffeomorph ((sphereDiffeo (n := 2) A).symm p.1, t)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith [ht.1, ht.2]
  have htL : t < L / 2 := by
    rw [haxis L] at hq
    exact hq
  refine ⟨dihedralEndProjection z, ?_, ?_⟩
  · change dihedralEndHeight (dihedralEndProjection z) < L / 2
    rw [dihedralEndHeight_projection]
    change |t| < L / 2
    rwa [abs_of_nonneg ht0]
  · rw [dihedralEndMap_projection_formula]
    change dihedralStandardPresentation.proj
      ((sphereDiffeo (n := 2) A) ((sphereDiffeo (n := 2) A).symm p.1),
        (if b then L - t else t) / (2 * L)) = q
    rw [(sphereDiffeo (n := 2) A).apply_symm_apply]
    have hfrac : (if b then L - t else t) / (2 * L) = p.2 := by
      dsimp [t]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        field_simp
      · simp only [↓reduceIte]
        field_simp
        ring
    rw [hfrac]
    exact hp
theorem dihedralEndTargetBall_image (ε L R : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (b : Bool) (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : dihedralEndCarrier) (hR : 0 < R) (hmargin : dihedralEndHeight p + R ≤ L / 2) :
    riemannianBallOf (dihedralMetric.{u} ε L hε hL) (dihedralEndMap L hL b A p) R ⊆
      dihedralEndMap L hL b A '' dihedralEndDomain L := by
  have hp : p ∈ dihedralEndDomain L := by change dihedralEndHeight p < L / 2; linarith
  have haxis := dihedralEndMap_axis L hL b A p hp
  intro q hq
  have hd := (dihedralAxis_distance_le ε L hε hL (dihedralEndMap L hL b A p) q).trans_lt hq
  rw [haxis] at hd
  have hb := abs_lt.mp ((ENNReal.ofReal_lt_ofReal_iff hR).mp hd)
  apply dihedralEndImage_contains_half L hL b A q
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢ <;> linarith [hb.1, hb.2]
private theorem dihedralEndMap_inner (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (z : dihedralEndCarrier) (v : TangentSpace (𝓡 3) z) :
    (dihedralMetric.{u} ε L hε hL).inner (dihedralEndMap.{u} L hL b A z)
      (mfderiv (𝓡 3) (𝓡 3) (dihedralEndMap.{u} L hL b A) z v)
      (mfderiv (𝓡 3) (𝓡 3) (dihedralEndMap.{u} L hL b A) z v) =
      (dihedralEndMetric ε hε).inner z v v := by
  have h := congrArg (fun g : SmoothRiemannianMetric (𝓡 3) dihedralEndCarrier =>
    g.inner z v v) (dihedralEndMap_metric_pullback.{u} ε L hε hL b A)
  rw [localPullMetric_inner (I := 𝓡 3) (J := 𝓡 3) _ _ _ z v v] at h
  exact h
theorem dihedralEnd_ball_edist_eq (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : dihedralEndCarrier) (r : ℝ≥0) (hr : 0 < r)
    (hmargin : dihedralEndHeight p + 3 * (r : ℝ) ≤ L / 2)
    (x y : dihedralEndCarrier) (hx : x ∈ riemannianBallOf (dihedralEndMetric ε hε) p r)
    (hy : y ∈ riemannianBallOf (dihedralEndMetric ε hε) p r) :
    riemannianEDistOf (dihedralEndMetric ε hε) x y =
      riemannianEDistOf (dihedralMetric.{u} ε L hε hL)
        (dihedralEndMap L hL b A x) (dihedralEndMap L hL b A y) := by
  let gM := dihedralEndMetric ε hε
  let gQ := dihedralMetric.{u} ε L hε hL
  have hrR : 0 < (r : ℝ) := hr
  have hp : dihedralEndHeight p < L / 2 := by linarith
  obtain ⟨jm, hjm, hsrc, htgt, hfun, hpm, hmetric, hballs⟩ :=
    exists_dihedralEndPointedMetricChart ε L hε hL b A p hp
  have hfn : (jm.toPartialEquiv : dihedralEndCarrier →
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) =
      dihedralEndMap.{u} L hL b A := hfun
  have hfwd (z w : dihedralEndCarrier) :
      riemannianEDistOf gQ (jm z) (jm w) ≤ riemannianEDistOf gM z w := by
    have h := edistOf_localPullMetric_le gQ jm hjm z w
    rwa [hmetric] at h
  have hxsrc : x ∈ jm.source := hballs r hrR (by linarith) hx
  have hysrc : y ∈ jm.source := hballs r hrR (by linarith) hy
  have htarget : riemannianBallOf gQ (jm p) (3 * (r : ℝ)) ⊆ jm.target := by
    rw [hfun, htgt]
    exact dihedralEndTargetBall_image ε L (3 * (r : ℝ)) hε hL b A p (by positivity) hmargin
  have hinner (z : dihedralEndCarrier) (v : TangentSpace (𝓡 3) z) :
      gQ.inner (jm z) (mfderiv (𝓡 3) (𝓡 3) jm z v)
        (mfderiv (𝓡 3) (𝓡 3) jm z v) = gM.inner z v v := by
    rw [hfn]
    exact dihedralEndMap_inner.{u} ε L hε hL b A z v
  have hinverse := DifferentialGeometry.PartialDiffeomorph.metric_upper_symm_of_metric_lower
    jm gM gQ (V := jm.source) (L := 1) (fun _q hq => hq)
    (fun z _ v => by rw [one_pow, one_mul, hinner z v])
  have hdx := (hfwd p x).trans_lt hx
  have hdy := (hfwd p y).trans_lt hy
  let d := max (riemannianEDistOf gQ (jm p) (jm x)).toReal
    (riemannianEDistOf gQ (jm p) (jm y)).toReal
  have hd0 : 0 ≤ d := le_max_of_le_left ENNReal.toReal_nonneg
  have hdr : d < (r : ℝ) := max_lt (ENNReal.toReal_lt_of_lt_ofReal hdx)
    (ENNReal.toReal_lt_of_lt_ofReal hdy)
  let a := (d + (r : ℝ)) / 2
  let R := (3 * a + 3 * (r : ℝ)) / 2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hda : d ≤ a := by dsimp [a]; linarith
  have har : a < (r : ℝ) := by dsimp [a]; linarith
  have hbuffer : 3 * a < R := by dsimp [R]; linarith
  have hRr : R < 3 * (r : ℝ) := by dsimp [R]; linarith
  have hsource : riemannianClosedBallOf gQ (jm p) R ⊆ jm.symm.source := by
    intro z hz
    apply htarget
    exact hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hRr)
  have hxT : jm x ∈ riemannianClosedBallOf gQ (jm p) a := by
    have hfin : riemannianEDistOf gQ (jm p) (jm x) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdx.le
    calc
      _ = ENNReal.ofReal (riemannianEDistOf gQ (jm p) (jm x)).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans hda)
  have hyT : jm y ∈ riemannianClosedBallOf gQ (jm p) a := by
    have hfin : riemannianEDistOf gQ (jm p) (jm y) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdy.le
    calc
      _ = ENNReal.ofReal (riemannianEDistOf gQ (jm p) (jm y)).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans hda)
  have hupper (z : (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) (hz : z ∈ riemannianClosedBallOf gQ (jm p) R)
      (v : TangentSpace (𝓡 3) z) :
      gM.inner (jm.symm z) (mfderiv (𝓡 3) (𝓡 3) jm.symm z v)
        (mfderiv (𝓡 3) (𝓡 3) jm.symm z v) ≤ 1 ^ 2 * gQ.inner z v v := by
    apply hinverse z
    have hz' := hsource hz
    change z ∈ jm.target at hz'
    rw [htgt, ← hfun, ← hsrc] at hz'
    exact hz'
  have hinv := edistOf_map_le_of_metric_upper_on_buffered_ball
    gQ gM jm.symm (jm p) (jm x) (jm y) ha0 hbuffer (by norm_num : (0 : ℝ) < 1)
      hsource hupper hxT hyT
  have hix : jm.symm.toPartialEquiv (jm.toPartialEquiv x) = x := jm.left_inv hxsrc
  have hiy : jm.symm.toPartialEquiv (jm.toPartialEquiv y) = y := jm.left_inv hysrc
  rw [hix, hiy, ENNReal.ofReal_one, one_mul] at hinv
  have heq := le_antisymm hinv (hfwd x y)
  simpa only [hfun] using heq
theorem dihedralEnd_ball_image (ε L r : ℝ) (hε : 0 < ε) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : dihedralEndCarrier) (hr : 0 < r) (hmargin : dihedralEndHeight p + 3 * r ≤ L / 2) :
    dihedralEndMap.{u} L hL b A '' riemannianBallOf (dihedralEndMetric ε hε) p r =
      riemannianBallOf (dihedralMetric ε L hε hL) (dihedralEndMap L hL b A p) r := by
  let gM := dihedralEndMetric ε hε
  let gQ := dihedralMetric.{u} ε L hε hL
  have hp : dihedralEndHeight p < L / 2 := by linarith
  obtain ⟨jm, hjm, hsrc, htgt, hfun, hpm, hmetric, hballs⟩ :=
    exists_dihedralEndPointedMetricChart ε L hε hL b A p hp
  have hfn : (jm.toPartialEquiv : dihedralEndCarrier →
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) =
      dihedralEndMap.{u} L hL b A := hfun
  have htarget : riemannianBallOf gQ (jm p) (3 * r) ⊆ jm.target := by
    rw [hfun, htgt]
    exact dihedralEndTargetBall_image ε L (3 * r) hε hL b A p (by positivity) hmargin
  have hinverse := DifferentialGeometry.PartialDiffeomorph.metric_upper_symm_of_metric_lower
    jm gM gQ (V := jm.source) (L := 1) (fun _q hq => hq)
    (fun z _hz v => by
      rw [one_pow, one_mul, hfn]
      exact (dihedralEndMap_inner.{u} ε L hε hL b A z v).symm.le)
  have hsource : riemannianClosedBallOf gQ (jm p) (2 * r) ⊆ jm.symm.source := by
    intro z hz
    apply htarget
    exact hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hupper (z : (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) (hz : z ∈ riemannianClosedBallOf gQ (jm p) (2 * r))
      (v : TangentSpace (𝓡 3) z) :
      gM.inner (jm.symm z) (mfderiv (𝓡 3) (𝓡 3) jm.symm z v)
        (mfderiv (𝓡 3) (𝓡 3) jm.symm z v) ≤ 1 ^ 2 * gQ.inner z v v := by
    apply hinverse z
    have hz' := hsource hz
    change z ∈ jm.target at hz'
    rw [htgt, ← hfun, ← hsrc] at hz'
    exact hz'
  have himage : (jm : dihedralEndCarrier → _) '' riemannianBallOf gM p r =
      riemannianBallOf gQ (jm p) r := by
    apply Set.Subset.antisymm
    · rintro q ⟨z, hz, rfl⟩
      have hd := edistOf_localPullMetric_le gQ jm hjm p z
      rw [hmetric] at hd
      exact hd.trans_lt hz
    · intro q hq
      have hqt : q ∈ jm.target := htarget
        (hq.trans ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)))
      have hq2 : riemannianEDistOf gQ (jm p) q < ENNReal.ofReal (2 * r) :=
        hq.trans ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
      have hi := edistOf_map_le_of_metric_upper_on_ball gQ gM jm.symm (jm p) q
        (by positivity : 0 < 2 * r) (by norm_num : (0 : ℝ) < 1) hsource hupper hq2
      have hip : jm.symm.toPartialEquiv (jm.toPartialEquiv p) = p := jm.left_inv hpm
      rw [hip, ENNReal.ofReal_one, one_mul] at hi
      exact ⟨jm.symm q, hi.trans_lt hq, jm.right_inv' hqt⟩
  simpa only [hfun] using himage
theorem exists_dihedralEndPointedApprox (ε L R δ : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (b : Bool) (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : dihedralEndCarrier) (hδ : 0 < δ) (hδR : δ < R)
    (hmargin : dihedralEndHeight p + 9 * R ≤ L / 2) :
    let _modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
    let _targetMetric : MetricSpace
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
      inducedMetricSpace (dihedralMetric ε L hε hL)
    @Nonempty (GC.MetricGeometry.PointedBallApprox (dihedralEndMap.{u} L hL b A p) p R δ) := by
  let gM := dihedralEndMetric ε hε
  let gQ := dihedralMetric.{u} ε L hε hL
  let _modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace gM
  let _targetMetric : MetricSpace
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
    inducedMetricSpace gQ
  let F := dihedralEndMap.{u} L hL b A
  have hR : 0 < R := hδ.trans hδR
  have hdist (x y : dihedralEndCarrier)
      (hx : dist x p ≤ 2 * R) (hy : dist y p ≤ 2 * R) : dist (F x) (F y) = dist x y := by
    have hxB : x ∈ riemannianBallOf gM p (3 * R) := by
      rw [← inducedMetricSpace_ball gM p]
      exact lt_of_le_of_lt hx (by linarith)
    have hyB : y ∈ riemannianBallOf gM p (3 * R) := by
      rw [← inducedMetricSpace_ball gM p]
      exact lt_of_le_of_lt hy (by linarith)
    have he := dihedralEnd_ball_edist_eq ε L hε hL b A p ⟨3 * R, by positivity⟩
      (by change 0 < 3 * R; positivity)
      (by change dihedralEndHeight p + 3 * (3 * R) ≤ L / 2; nlinarith) x y hxB hyB
    exact congrArg ENNReal.toReal he.symm
  have himage : F '' Metric.ball p (2 * R) = Metric.ball (F p) (2 * R) := by
    rw [inducedMetricSpace_ball gM p, inducedMetricSpace_ball gQ (F p)]
    exact dihedralEnd_ball_image ε L (2 * R) hε hL b A p (by positivity) (by linarith)
  let f : GC.MetricGeometry.PointedBallApprox p (F p) (2 * R) (δ / 4) := {
    error_pos := by positivity
    error_lt_radius := by linarith
    toFun := fun x => F x
    basepoint := rfl
    distortion := fun x y => by
      rw [hdist x y x.property y.property, sub_self, abs_zero]
      positivity
    coverage := fun y hy => by
      have hyB : y ∈ Metric.ball (F p) (2 * R) := by rw [Metric.mem_ball]; linarith
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
theorem dihedralEnd_pointedGH (ε : ℝ) (hε : 0 < ε) (L c : ℕ → ℝ) (hL : ∀ i, 0 < L i)
    (b : Bool) (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (cInf : ℝ)
    (hLt : Filter.Tendsto L Filter.atTop Filter.atTop)
    (hc : Filter.Tendsto c Filter.atTop (nhds cInf))
    (A : ℕ → EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    let modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
    let targetMetrics : ∀ _i : ℕ, MetricSpace
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
      fun i => inducedMetricSpace (dihedralMetric ε (L i) hε (hL i))
    @GC.MetricGeometry.PointedGHConverges
      (fun _i : ℕ =>
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier)
      targetMetrics dihedralEndCarrier modelMetric
      (fun i => dihedralEndMap (L i) (hL i) b (A i)
        (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, c i))))
      (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, cInf))) := by
  let modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
  let targetMetrics : ∀ _i : ℕ, MetricSpace
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
    fun i => inducedMetricSpace (dihedralMetric ε (L i) hε (hL i))
  let p : ℝ → dihedralEndCarrier := fun t =>
    dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, t))
  have hp : Continuous p :=
    (dihedralEndProjection_localDiffeomorph.contMDiff.continuous.comp
      sphereCylinderRechartDiffeomorph.continuous).comp (continuous_const.prodMk continuous_id)
  have hpc : Filter.Tendsto (fun i => p (c i)) Filter.atTop (nhds (p cInf)) :=
    (hp.tendsto cInf).comp hc
  have hHt : Filter.Tendsto (fun i => dihedralEndHeight (p (c i))) Filter.atTop
      (nhds (dihedralEndHeight (p cInf))) :=
    (dihedralEndHeight_continuous.tendsto (p cInf)).comp hpc
  have hdist : Filter.Tendsto (fun i => dist (p (c i)) (p cInf)) Filter.atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hpc
  refine ⟨riemannianMetricComplete_iff_inducedMetricSpace.mp (dihedralEndMetric_complete ε hε), ?_⟩
  intro R δ hδ hδR
  filter_upwards [Filter.Tendsto.eventually_ge_atTop hLt
      (2 * (dihedralEndHeight (p cInf) + 1 + 9 * R)),
    hHt.eventually (eventually_lt_nhds (by linarith :
      dihedralEndHeight (p cInf) < dihedralEndHeight (p cInf) + 1)),
    hdist.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < δ / 4))] with i hiL hiH hiD
  let _currentMetric : MetricSpace
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
    targetMetrics i
  obtain ⟨f⟩ := exists_dihedralEndPointedApprox ε (L i) R (δ / 2) hε (hL i) b (A i)
    (p (c i)) (by positivity) (by linarith) (by linarith)
  have hE : δ / 2 + 2 * dist (p (c i)) (p cInf) < δ := by linarith
  let repaired := f.repairTarget (p cInf) dist_nonneg le_rfl (hE.trans hδR)
  exact ⟨repaired.enlargeError hE.le hδR⟩
def dihedralEndLimitPartial (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) dihedralEndCarrier
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞ :=
  Classical.choose (exists_dihedralEndMovingPartial.{u} L hL b A σ s)
theorem dihedralEndLimitPartial_spec (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    (dihedralEndLimitPartial.{u} L hL b A σ s).source = dihedralEndMovingDomain L σ s ∧
    (dihedralEndLimitPartial.{u} L hL b A σ s).target =
      dihedralEndMovingMap L hL b A σ s '' dihedralEndMovingDomain L σ s ∧
    (dihedralEndLimitPartial.{u} L hL b A σ s : dihedralEndCarrier → _) =
      dihedralEndMovingMap L hL b A σ s :=
  Classical.choose_spec (exists_dihedralEndMovingPartial.{u} L hL b A σ s)
theorem dihedralEndLimitPartial_pullback_on (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ)
    (U : TopologicalSpace.Opens dihedralEndCarrier)
    (hU : (U : Set dihedralEndCarrier) ⊆ (dihedralEndLimitPartial.{u} L hL b A σ s).source) :
    PartialDiffeomorph.pullbackMetricOn (dihedralEndLimitPartial.{u} L hL b A σ s) U hU
      (dihedralMetric ε L hε hL) =
      (Diffeomorph.pullbackMetricCross (dihedralEndMetric ε hε)
        (dihedralOddShearDiffeomorph σ s)).restrictOpen U := by
  let jm := dihedralEndLimitPartial.{u} L hL b A σ s
  have hfn : (jm.toPartialEquiv : dihedralEndCarrier →
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) =
      dihedralEndMovingMap.{u} L hL b A σ s := (dihedralEndLimitPartial_spec.{u} L hL b A σ s).2.2
  have hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (jm : dihedralEndCarrier → _) := by
    rw [hfn]
    exact dihedralEndMovingMap_localDiffeomorph L hL b A σ s
  have hmetric : localPullMetric (dihedralMetric ε L hε hL) jm hjm =
      Diffeomorph.pullbackMetricCross (dihedralEndMetric ε hε)
        (dihedralOddShearDiffeomorph σ s) := by
    simpa only [hfn] using dihedralEndMovingMap_metric_pullback.{u} ε L hε hL b A σ s
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  rw [PartialDiffeomorph.pullbackMetricOn_inner, SmoothRiemannianMetric.restrictOpen_inner]
  have h := congrArg (fun g : SmoothRiemannianMetric (𝓡 3) dihedralEndCarrier =>
    g.inner (z : dihedralEndCarrier) v w) hmetric
  rw [localPullMetric_inner (I := 𝓡 3) (J := 𝓡 3) _ jm hjm (z : dihedralEndCarrier) v w] at h
  exact h
theorem dihedralEndShear_CInf (ε : ℝ) (hε : 0 < ε)
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℕ → ℝ)
    (hs : Filter.Tendsto s Filter.atTop (nhds 0)) :
    CheegerGromovCompactness.MetricCInfConvergenceOnCompacts
      (fun i => Diffeomorph.pullbackMetricCross (dihedralEndMetric ε hε)
        (dihedralOddShearDiffeomorph σ (s i)))
      (dihedralEndMetric ε hε) (dihedralEndMetric ε hε) := by
  intro K hK k δ hδ
  have ht := dihedralOddShear_metric_convergence ε hε σ s hs (dihedralEndMetric ε hε) K hK k
  exact Filter.eventually_atTop.mp (ht.eventually (eventually_lt_nhds hδ))
theorem exists_dihedralEnd_nativeCharts (ε : ℝ) (hε : 0 < ε) (L c : ℕ → ℝ) (hL : ∀ i, 0 < L i)
    (b : Bool) (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (cInf : ℝ)
    (hLt : Filter.Tendsto L Filter.atTop Filter.atTop)
    (hc : Filter.Tendsto c Filter.atTop (nhds cInf))
    (A : ℕ → EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    let _modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
    ∃ jm : ∀ _i, PartialDiffeomorph (𝓡 3) (𝓡 3) dihedralEndCarrier
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
      (∀ i, jm i (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, cInf))) =
        dihedralEndMap (L i) (hL i) b (A i)
          (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, c i)))) ∧
      ∀ r : ℝ, 0 < r → ∃ i0 : ℕ,
        ∃ hsub : ∀ l, ((⟨Metric.ball
          (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, cInf))) r,
            Metric.isOpen_ball⟩ : TopologicalSpace.Opens dihedralEndCarrier) :
              Set dihedralEndCarrier)
              ⊆ (jm (l + i0)).source,
        ∀ K : Set (⟨Metric.ball
          (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, cInf))) r,
            Metric.isOpen_ball⟩ : TopologicalSpace.Opens dihedralEndCarrier),
          IsCompact K → CheegerGromovCompactness.MetricCPConvergenceOn K 1
            (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i0)) _ (hsub l)
              (dihedralMetric ε (L (l + i0)) hε (hL (l + i0))))
            ((dihedralEndMetric ε hε).restrictOpen _)
            ((dihedralEndMetric ε hε).restrictOpen _) := by
  let _modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
  let _endProper : ProperSpace dihedralEndCarrier :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete (dihedralEndMetric_complete ε hε)
  let _endSecondCountable : SecondCountableTopology dihedralEndCarrier :=
    EMetric.secondCountable_of_sigmaCompact dihedralEndCarrier
  let p := dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, cInf))
  let s : ℕ → ℝ := fun i => c i - cInf
  have hs : Filter.Tendsto s Filter.atTop (nhds 0) := by
    simpa only [s, sub_self] using hc.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _i : ℕ => cInf) Filter.atTop (nhds cInf))
  let jm (i : ℕ) := dihedralEndLimitPartial.{u} (L i) (hL i) b (A i) σ (s i)
  have hanchor (i : ℕ) : jm i p =
      dihedralEndMap (L i) (hL i) b (A i)
        (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, c i))) := by
    have hfn := (dihedralEndLimitPartial_spec.{u} (L i) (hL i) b (A i) σ (s i)).2.2
    calc
      _ = dihedralEndMovingMap (L i) (hL i) b (A i) σ (s i) p := congrFun hfn p
      _ = _ := by
        change dihedralEndMap (L i) (hL i) b (A i)
          (dihedralOddShearDiffeomorph σ (c i - cInf)
            (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, cInf)))) = _
        rw [dihedralOddShearDiffeomorph_anchor]
        have ht : cInf + (c i - cInf) = c i := by ring
        rw [ht]
  refine ⟨jm, hanchor, ?_⟩
  intro r hr
  let U : TopologicalSpace.Opens dihedralEndCarrier := ⟨Metric.ball p r, Metric.isOpen_ball⟩
  let _endLocalCompact : LocallyCompactSpace dihedralEndCarrier := inferInstance
  let _openLocalCompact : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let _openSecondCountable : SecondCountableTopology U := inferInstance
  let _openSigma : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hsmall : ∀ᶠ i in Filter.atTop, |s i| < 1 := by
    have h := (continuous_abs.tendsto (0 : ℝ)).comp hs
    exact h.eventually (by
      simpa only [abs_zero] using eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge := Filter.Tendsto.eventually_ge_atTop hLt (2 * (dihedralEndHeight p + r + 1))
  obtain ⟨i0, hi0⟩ := Filter.eventually_atTop.mp (hlarge.and hsmall)
  have hsub : ∀ l, (U : Set dihedralEndCarrier) ⊆ (jm (l + i0)).source := by
    intro l x hx
    have hbounds := hi0 (l + i0) (by omega)
    change x ∈ (dihedralEndLimitPartial.{u} (L (l + i0)) (hL (l + i0)) b (A (l + i0))
      σ (s (l + i0))).source
    rw [(dihedralEndLimitPartial_spec.{u} (L (l + i0)) (hL (l + i0)) b (A (l + i0))
      σ (s (l + i0))).1]
    apply dihedralEndMovingDomain_ball_subset ε (L (l + i0)) r hε σ (s (l + i0)) p hr
      (by linarith [hbounds.1, hbounds.2])
    change x ∈ Metric.ball p r at hx
    rwa [inducedMetricSpace_ball (dihedralEndMetric ε hε) p] at hx
  refine ⟨i0, hsub, ?_⟩
  intro K hK
  have hshift : StrictMono (fun l : ℕ => l + i0) := by
    intro i j hij
    exact Nat.add_lt_add_right hij i0
  have hconv := ((dihedralEndShear_CInf ε hε σ s hs).comp_subseq hshift).restrictOpen U
  have heq : (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i0)) U (hsub l)
        (dihedralMetric ε (L (l + i0)) hε (hL (l + i0)))) =
      (fun l => (Diffeomorph.pullbackMetricCross (dihedralEndMetric ε hε)
        (dihedralOddShearDiffeomorph σ (s (l + i0)))).restrictOpen U) := by
    funext l
    exact dihedralEndLimitPartial_pullback_on ε (L (l + i0)) hε (hL (l + i0)) b (A (l + i0))
      σ (s (l + i0)) U (hsub l)
  rw [heq]
  exact hconv K hK 1

end DifferentialGeometry.Geometry.Collapse
