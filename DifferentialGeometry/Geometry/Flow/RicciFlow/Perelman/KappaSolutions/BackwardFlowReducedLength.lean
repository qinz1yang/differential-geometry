import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.GradientIdentities
import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTailEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowCompactness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Lipschitz
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Analysis.Calculus.Compactness.LocalArzelaAscoli

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

omit [NeZero (Module.finrank ℝ E)] in
private theorem rescaled_metric_inner_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p q : F.M)
    {tau t T A : ℝ} (htau : 0 < tau) (ht : t ∈ Icc 1 T)
    (hbase : redLength F.S 0 p q tau ≤ A) (v : TangentSpace I q) :
    (scaleMetric (tau * t)⁻¹ (inv_pos.mpr (mul_pos htau (zero_lt_one.trans_le ht.1)))
      (F.S.base.metric (-(tau * t)))).inner q v v ≤
        Real.exp (3 * A * (T - 1)) *
          (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))).inner q v v := by
  have hscalar := (scalar_le_three_mul_redLength_div_of_ancient F hF p q htau).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbase (by norm_num)) htau.le)
  have hA : 0 ≤ A := by
    obtain ⟨B, hB⟩ := hF.globalScalarBound
    have hz := (hB (-tau) (neg_nonpos.mpr htau.le) q).1
    have hh := (le_div_iff₀ htau).mp hscalar
    nlinarith
  have htt : tau ≤ tau * t := by nlinarith only [htau, ht.1]
  have hm := metric_inner_le_exp_scalar_bound_of_ancient F hF
    (neg_le_neg htt) (neg_nonpos.mpr htau.le) q hscalar v
  have hexp : (3 * A / tau) * (-tau - -(tau * t)) ≤ 3 * A * (T - 1) := by
    calc
      _ = 3 * A * (t - 1) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [ht.2]) (by positivity)
  have hm' := hm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
    (metric_inner_self_nonneg _ _ _))
  simp only [scaleMetric_inner]
  calc
    _ ≤ tau⁻¹ * (F.S.base.metric (-(tau * t))).inner q v v :=
      mul_le_mul_of_nonneg_right (inv_anti₀ htau htt) (metric_inner_self_nonneg _ _ _)
    _ ≤ tau⁻¹ * (Real.exp (3 * A * (T - 1)) * (F.S.base.metric (-tau)).inner q v v) :=
      mul_le_mul_of_nonneg_left hm' (inv_nonneg.mpr htau.le)
    _ = _ := by ring

private theorem eventually_redLength_at_one_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
    (C : MetricConvergenceData Phi)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ i in atTop, ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint R,
      redLength F.S 0 p (Phi.map i x) (tau (phi i)) ≤
        (Real.sqrt A + Real.sqrt 3 / 2 * (2 * R)) ^ 2 := by
  filter_upwards [Phi.eventually_edist_map_le_on_closed_ball C href hcomplete P.basepoint hR
    (by norm_num : (1 : ℝ) < 2)] with i hi
  intro x hx
  have hbp : P.basepoint ∈ riemannianClosedBallOf P.metric P.basepoint R := by
    change riemannianEDistOf P.metric P.basepoint P.basepoint ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact zero_le
  have hd := (hi.2 P.basepoint hbp x hx).trans
    (mul_le_mul le_rfl hx (zero_le) (zero_le))
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hd
  have hd' : riemannianEDistOf
      (scaleMetric (tau (phi i))⁻¹ (inv_pos.mpr (htau (phi i))) (F.S.base.metric (-tau (phi i))))
      (q (phi i)) (Phi.map i x) ≤ ENNReal.ofReal (2 * R) := by
    simpa only [PointedRiemannianConvergenceMaps.map, Phi.basepoint_map] using hd
  exact redLength_le_of_rescaled_distance_le F hF p _ _ (htau (phi i))
    (by positivity) (hbase (phi i)) hd'

private theorem eventually_sqrt_redLength_spatial_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) [PreconnectedSpace P.M]
    {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
    (C : MetricConvergenceData Phi)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) {R T : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ≥0, ∀ᶠ i in atTop, ∀ t ∈ Icc 1 T,
      ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint R,
      ∀ y ∈ riemannianClosedBallOf P.metric P.basepoint R,
        |Real.sqrt (redLength F.S 0 p (Phi.map i x) (tau (phi i) * t)) -
          Real.sqrt (redLength F.S 0 p (Phi.map i y) (tau (phi i) * t))| ≤
            (K : ℝ) * (riemannianEDistOf P.metric x y).toReal := by
  let B := (Real.sqrt A + Real.sqrt 3 / 2 * (2 * (3 * R + 1))) ^ 2
  let L := Real.sqrt (2 * Real.exp (3 * B * (T - 1)))
  have hL : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hL2 : L ^ 2 = 2 * Real.exp (3 * B * (T - 1)) := Real.sq_sqrt (by positivity)
  let K : ℝ≥0 := ⟨Real.sqrt 3 / 2 * L, by positivity⟩
  have hmetricComplete : RiemannianMetricComplete (I := I) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  let S := riemannianClosedBallOf P.metric P.basepoint (3 * R + 1)
  have hS : IsCompact S := hmetricComplete.closedEBall_isCompact P.basepoint (3 * R + 1)
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href S hS 1 one_pos
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop N,
    eventually_redLength_at_one_le F hF p tau htau q hbase P Phi C href hcomplete
      (show 0 ≤ 3 * R + 1 by linarith)] with i hi hlength
  intro t ht x hx y hy
  have htt : 0 < tau (phi i) * t := mul_pos (htau _) (zero_lt_one.trans_le ht.1)
  let g := scaleMetric (tau (phi i) * t)⁻¹ (inv_pos.mpr htt)
    (F.S.base.metric (-(tau (phi i) * t)))
  have hupper : ∀ z ∈ S, ∀ v : TangentSpace I z,
      g.inner (Phi.map i z) (mfderiv I I (Phi.map i) z v) (mfderiv I I (Phi.map i) z v) ≤
        L ^ 2 * P.metric.inner z v v := by
    intro z hz v
    have hm := rescaled_metric_inner_le F hF p (Phi.map i z) (htau _) ht (hlength z hz)
      (mfderiv I I (Phi.map i) z v)
    have hquad : ((backwardSliceSequence F tau htau q).obj (phi i)).metric.inner (Phi.map i z)
        (mfderiv I I (Phi.map i) z v) (mfderiv I I (Phi.map i) z v) ≤
          2 * P.metric.inner z v v := by
      have hh := (abs_le.mp ((hN i hi).2 z hz v)).2
      linarith
    calc
      _ ≤ Real.exp (3 * B * (T - 1)) *
          ((backwardSliceSequence F tau htau q).obj (phi i)).metric.inner (Phi.map i z)
            (mfderiv I I (Phi.map i) z v) (mfderiv I I (Phi.map i) z v) := hm
      _ ≤ Real.exp (3 * B * (T - 1)) * (2 * P.metric.inner z v v) :=
        mul_le_mul_of_nonneg_left hquad (Real.exp_pos _).le
      _ = _ := by rw [hL2]; ring
  have hd := edistOf_map_le_of_metric_upper_on_buffered_ball P.metric g
    (Phi.partialDiffeomorph i) P.basepoint x y hR (by linarith) hL (hN i hi).1 hupper hx hy
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (riemannianEDistOf_ne_top P.metric x y)) hd
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL.le] at hreal
  calc
    _ ≤ Real.sqrt 3 / 2 * (riemannianEDistOf g (Phi.map i x) (Phi.map i y)).toReal :=
      abs_sqrt_redLength_sub_le_rescaled_distance F hF p _ _ htt
    _ ≤ Real.sqrt 3 / 2 * (L * (riemannianEDistOf P.metric x y).toReal) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = _ := by
      change Real.sqrt 3 / 2 * (L * _) = (Real.sqrt 3 / 2 * L) * _
      ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem backward_length_nonneg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p q : F.M)
    {tau : ℝ} (htau : 0 < tau) : 0 ≤ redLength F.S 0 p q tau := by
  obtain ⟨B, hB⟩ := hF.globalScalarBound
  apply div_nonneg _ (by positivity)
  apply lCost_nonneg_of_scalar_nonneg F.S 0 htau.le
  intro t ht y
  simpa only [zero_sub] using (hB (-t) (neg_nonpos.mpr ht.1) y).1

private theorem eventually_redLength_space_time_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) [PreconnectedSpace P.M]
    {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
    (C : MetricConvergenceData Phi)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) {R T : ℝ} (hR : 0 ≤ R) (hT : 1 ≤ T) :
    ∃ K : ℝ≥0, ∀ᶠ i in atTop, ∀ s ∈ Icc 1 T, ∀ t ∈ Icc 1 T,
      ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint R,
      ∀ y ∈ riemannianClosedBallOf P.metric P.basepoint R,
        |redLength F.S 0 p (Phi.map i x) (tau (phi i) * s) -
          redLength F.S 0 p (Phi.map i y) (tau (phi i) * t)| ≤
            (K : ℝ) * ((riemannianEDistOf P.metric x y).toReal + |s - t|) := by
  let B := (Real.sqrt A + Real.sqrt 3 / 2 * (2 * R)) ^ 2
  obtain ⟨Kt, hKt⟩ := exists_lipschitzOnWith_redLength_rescaled_time F hF p (A := B) hT
  obtain ⟨Ks, hKs⟩ := eventually_sqrt_redLength_spatial_bound
    F hF p tau htau q hbase P Phi C href hcomplete (T := T) hR
  let M := B + (Kt : ℝ) * (T - 1)
  let K : ℝ≥0 := ⟨(Ks : ℝ) * (2 * Real.sqrt M) + Kt, by positivity⟩
  refine ⟨K, ?_⟩
  filter_upwards [hKs, eventually_redLength_at_one_le F hF p tau htau q hbase
    P Phi C href hcomplete hR] with i hspace hbound
  have htime (x : P.M) (hx : x ∈ riemannianClosedBallOf P.metric P.basepoint R) :=
    hKt (tau (phi i)) (htau _) (Phi.map i x) (hbound x hx)
  have hvalues (x : P.M) (hx : x ∈ riemannianClosedBallOf P.metric P.basepoint R)
      (t : ℝ) (ht : t ∈ Icc 1 T) : redLength F.S 0 p (Phi.map i x) (tau (phi i) * t) ≤ M := by
    have h := (htime x hx).dist_le_mul t ht 1 ⟨le_rfl, hT⟩
    simp only [Real.dist_eq, mul_one, abs_of_nonneg (sub_nonneg.mpr ht.1)] at h
    have hb : redLength F.S 0 p (Phi.map i x) (tau (phi i)) ≤ B := hbound x hx
    have htB := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 1) Kt.coe_nonneg
    have hh := le_abs_self (redLength F.S 0 p (Phi.map i x) (tau (phi i) * t) -
      redLength F.S 0 p (Phi.map i x) (tau (phi i)))
    dsimp [M]
    linarith
  intro s hs t ht x hx y hy
  let X := redLength F.S 0 p (Phi.map i x) (tau (phi i) * s)
  let Y := redLength F.S 0 p (Phi.map i y) (tau (phi i) * s)
  have hX0 : 0 ≤ X := backward_length_nonneg F hF p _
    (mul_pos (htau _) (zero_lt_one.trans_le hs.1))
  have hY0 : 0 ≤ Y := backward_length_nonneg F hF p _
    (mul_pos (htau _) (zero_lt_one.trans_le hs.1))
  have hsum : Real.sqrt X + Real.sqrt Y ≤ 2 * Real.sqrt M := by
    linarith only [Real.sqrt_le_sqrt (hvalues x hx s hs), Real.sqrt_le_sqrt (hvalues y hy s hs)]
  have hspace' : |X - Y| ≤ (Ks : ℝ) * (2 * Real.sqrt M) *
      (riemannianEDistOf P.metric x y).toReal := by
    calc
      |X - Y| = |Real.sqrt X - Real.sqrt Y| * (Real.sqrt X + Real.sqrt Y) := by
        have hxy : X - Y = (Real.sqrt X - Real.sqrt Y) * (Real.sqrt X + Real.sqrt Y) := by
          nlinarith only [Real.sq_sqrt hX0, Real.sq_sqrt hY0]
        rw [hxy, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt X + Real.sqrt Y)]
      _ ≤ ((Ks : ℝ) * (riemannianEDistOf P.metric x y).toReal) * (2 * Real.sqrt M) :=
        mul_le_mul (hspace s hs x hx y hy) hsum (by positivity) (by positivity)
      _ = _ := by ring
  have htime' := (htime y hy).dist_le_mul s hs t ht
  change |Y - redLength F.S 0 p (Phi.map i y) (tau (phi i) * t)| ≤ (Kt : ℝ) * |s - t| at htime'
  calc
    _ ≤ |X - Y| + |Y - redLength F.S 0 p (Phi.map i y) (tau (phi i) * t)| :=
      abs_sub_le _ _ _
    _ ≤ (Ks : ℝ) * (2 * Real.sqrt M) * (riemannianEDistOf P.metric x y).toReal +
        (Kt : ℝ) * |s - t| := add_le_add hspace' htime'
    _ ≤ _ := by
      change _ ≤ ((Ks : ℝ) * (2 * Real.sqrt M) + Kt) *
        ((riemannianEDistOf P.metric x y).toReal + |s - t|)
      have hcross1 := mul_nonneg (show 0 ≤ (Ks : ℝ) * (2 * Real.sqrt M) by positivity)
        (abs_nonneg (s - t))
      have hcross2 := mul_nonneg Kt.coe_nonneg
        (ENNReal.toReal_nonneg (a := riemannianEDistOf P.metric x y))
      nlinarith only [hcross1, hcross2]

theorem exists_reducedLength_limit_on_rescaled_time_interval
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) [PreconnectedSpace P.M]
    {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
    (C : MetricConvergenceData Phi)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (psi : ℕ → ℕ) (ell : C(P.M × Icc (1 : ℝ) T, ℝ)), StrictMono psi ∧
      (∀ z, 0 ≤ ell z) ∧ ell (P.basepoint, ⟨1, le_rfl, hT⟩) ≤ A ∧
      (∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
        ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint R,
        ∀ y ∈ riemannianClosedBallOf P.metric P.basepoint R,
        ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
          (K : ℝ) * ((riemannianEDistOf P.metric x y).toReal + |(s : ℝ) - t|)) ∧
      ∀ S : Set (P.M × Icc (1 : ℝ) T), IsCompact S → TendstoUniformlyOn
        (fun i z => redLength F.S 0 p (Phi.map (psi i) z.1) (tau (phi (psi i)) * z.2)) ell atTop S := by
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : PseudoMetricSpace P.M := P.metric.toPseudoMetricSpace
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let z0 : P.M × Icc (1 : ℝ) T := (P.basepoint, ⟨1, le_rfl, hT⟩)
  let f : ℕ → P.M × Icc (1 : ℝ) T → ℝ :=
    fun i z => redLength F.S 0 p (Phi.map i z.1) (tau (phi i) * z.2)
  have hball {R : ℝ} (hR : 0 ≤ R) {x : P.M} (hx : x ∈ Metric.closedBall P.basepoint R) :
      x ∈ riemannianClosedBallOf P.metric P.basepoint R := by
    change edist P.basepoint x ≤ ENNReal.ofReal R
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR, dist_comm]
    exact hx
  have hLip (R : ℝ) (hR : 0 ≤ R) : ∃ K : ℝ≥0, ∀ᶠ i in atTop,
      LipschitzOnWith K (f i) (Metric.closedBall z0 R) := by
    obtain ⟨K, hK⟩ := eventually_redLength_space_time_bound F hF p tau htau q hbase
      P Phi C href hcomplete hR hT
    refine ⟨2 * K, ?_⟩
    filter_upwards [hK] with i hi
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxP : x.1 ∈ Metric.closedBall P.basepoint R :=
      (le_max_left _ _).trans (Metric.mem_closedBall.mp hx)
    have hyP : y.1 ∈ Metric.closedBall P.basepoint R :=
      (le_max_left _ _).trans (Metric.mem_closedBall.mp hy)
    have h := hi x.2 x.2.property y.2 y.2.property x.1 (hball hR hxP) y.1 (hball hR hyP)
    change |f i x - f i y| ≤ (K : ℝ) * (dist x.1 y.1 + dist x.2 y.2) at h
    change |f i x - f i y| ≤ ((2 * K : ℝ≥0) : ℝ) * dist x y
    rw [NNReal.coe_mul, NNReal.coe_ofNat, Prod.dist_eq]
    apply h.trans
    have hd : dist x.1 y.1 + dist x.2 y.2 ≤ 2 * max (dist x.1 y.1) (dist x.2 y.2) := by
      linarith only [le_max_left (dist x.1 y.1) (dist x.2 y.2),
        le_max_right (dist x.1 y.1) (dist x.2 y.2)]
    nlinarith only [mul_le_mul_of_nonneg_left hd K.coe_nonneg]
  have hnonneg (i : ℕ) (z : P.M × Icc (1 : ℝ) T) : 0 ≤ f i z :=
    backward_length_nonneg F hF p _ (mul_pos (htau _) (zero_lt_one.trans_le z.2.property.1))
  have hbdd : ∃ B : ℝ, ∀ᶠ i in atTop, |f i z0| ≤ B := by
    refine ⟨A, Eventually.of_forall fun i => ?_⟩
    rw [abs_of_nonneg (hnonneg i z0)]
    simpa only [f, z0, mul_one, PointedRiemannianConvergenceMaps.map, Phi.basepoint_map]
      using hbase (phi i)
  obtain ⟨psi, ell, hpsi, _, hconv⟩ :=
    ArzelaAscoli.exists_locallyLipschitz_subseq_limit_of_eventually_lipschitzOn_closedBall
      f z0 hLip hbdd
  have hpoint (z : P.M × Icc (1 : ℝ) T) : Tendsto (fun i => f (psi i) z) atTop (𝓝 (ell z)) :=
    (hconv {z} isCompact_singleton).tendsto_at (mem_singleton z)
  refine ⟨psi, ell, hpsi,
    fun z => ge_of_tendsto (hpoint z) (Eventually.of_forall fun i => hnonneg (psi i) z),
    ?_, ?_, hconv⟩
  · apply le_of_tendsto (hpoint z0)
    exact Eventually.of_forall fun i => by
      simpa only [f, z0, mul_one, PointedRiemannianConvergenceMaps.map, Phi.basepoint_map]
        using hbase (phi (psi i))
  · intro R hR
    obtain ⟨K, hK⟩ := eventually_redLength_space_time_bound F hF p tau htau q hbase
      P Phi C href hcomplete hR hT
    refine ⟨K, fun x hx y hy s t => ?_⟩
    apply le_of_tendsto ((hpoint (x, s)).sub (hpoint (y, t))).abs
    filter_upwards [hpsi.tendsto_atTop hK] with i hi
    exact hi s s.property t t.property x hx y hy

private def backwardFlowZeroMaps
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) phi) :
    PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) (L.atTime 0) phi where
  partialDiffeomorph := Phi.partialDiffeomorph
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem exists_metricConvergence_of_heq_maps
    {X Y : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hXY : X = Y)
    {Phi : PointedRiemannianConvergenceMaps X P phi}
    {Psi : PointedRiemannianConvergenceMaps Y P phi}
    (hmap : HEq Phi.partialDiffeomorph Psi.partialDiffeomorph)
    (C : MetricConvergenceData Phi)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) :
    ∃ C0 : MetricConvergenceData Psi,
      ∀ k, (C0.domain k).referenceMetric = (C0.domain k).limitMetric := by
  subst Y
  have heq : Phi = Psi := by
    cases Phi
    cases Psi
    cases eq_of_heq hmap
    rfl
  subst Psi
  exact ⟨C, href⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem exists_backward_flow_zero_metric_convergence
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) phi)
    (C : MetricConvergenceData (Phi.atTime (I := I)
      (X := backwardFlowSequence F tau htau q) (L := L) 0))
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) :
    ∃ C0 : MetricConvergenceData (backwardFlowZeroMaps F tau htau q L Phi),
      ∀ k, (C0.domain k).referenceMetric = (C0.domain k).limitMetric := by
  exact exists_metricConvergence_of_heq_maps
    (backwardFlowSequence_atZero F tau htau q) HEq.rfl C href

theorem abs_sqrt_backward_flow_limit_redLength_sub_le_distance
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M] {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {t : ℝ} (ht : t < 1)
    (C : MetricConvergenceData (Phi.atTime (I := I) (X := backwardFlowSequence F tau htau q) (L := L) t))
    (href : ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric)
    (hcomplete : MetricComplete (L.atTime t))
    (ell : L.M → ℝ)
    (hell : ∀ x, Tendsto
      (fun n => redLength F.S 0 p (Phi.map n x) (tau (subseq n) * (1 - t))) atTop (𝓝 (ell x)))
    (x y : L.M) :
    |Real.sqrt (ell x) - Real.sqrt (ell y)| ≤ Real.sqrt 3 / (2 * Real.sqrt (1 - t)) *
      (riemannianEDistOf (L.S.base.metric t) x y).toReal := by
  have htheta : 0 < 1 - t := sub_pos.mpr ht
  let _ : TopologicalSpace F.M := F.topology
  let _ : ChartedSpace H F.M := F.charted
  let _ : IsManifold I ∞ F.M := F.smooth
  let X := (backwardFlowSequence F tau htau q).atTime t
  let P := L.atTime t
  let _ : PreconnectedSpace P.M := inferInstanceAs (PreconnectedSpace L.M)
  let Psi : PointedRiemannianConvergenceMaps X P subseq := Phi.atTime (I := I) (X := backwardFlowSequence F tau htau q) (L := L) t
  let f : ∀ n : ℕ, (X.obj n).M → ℝ :=
    fun n z => Real.sqrt (redLength F.S 0 p z (tau n * (1 - t)))
  let K : ℝ≥0 := ⟨Real.sqrt 3 / (2 * Real.sqrt (1 - t)), by positivity⟩
  have hLip (n : ℕ) (a b : F.M) : |f n a - f n b| ≤
      (K : ℝ) * (riemannianEDistOf (X.obj n).metric a b).toReal := by
    have h := abs_sqrt_redLength_sub_le_rescaled_distance F hF p a b (mul_pos (htau n) htheta)
    change |Real.sqrt (redLength F.S 0 p a (tau n * (1 - t))) -
      Real.sqrt (redLength F.S 0 p b (tau n * (1 - t)))| ≤ (K : ℝ) *
        (riemannianEDistOf (scaleMetric (tau n)⁻¹ (inv_pos.mpr (htau n))
          (F.S.base.metric (-tau n + t / (tau n)⁻¹))) a b).toReal
    rw [show -tau n + t / (tau n)⁻¹ = -(tau n * (1 - t)) by rw [div_inv_eq_mul]; ring]
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
    convert h using 1
    change (Real.sqrt 3 / (2 * Real.sqrt (1 - t))) *
      (Real.sqrt (tau n)⁻¹ * (riemannianEDistOf (F.S.base.metric (-(tau n * (1 - t)))) a b).toReal) = _
    rw [Real.sqrt_inv, Real.sqrt_inv, Real.sqrt_mul (htau n).le]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr htheta)]
  have hpoint (z : P.M) : Tendsto (fun n => f (subseq n) (Psi.map n z))
      atTop (𝓝 (Real.sqrt (ell z))) := Real.continuous_sqrt.continuousAt.tendsto.comp (hell z)
  have hbdd : ∃ B : ℝ, ∀ᶠ n in atTop, |f (subseq n) (X.obj (subseq n)).basepoint| ≤ B := by
    obtain ⟨B, hB⟩ := (hpoint P.basepoint).abs.isBoundedUnder_le.eventually_le
    refine ⟨B, hB.mono fun n hn => ?_⟩
    have hbase : Psi.map n P.basepoint = (X.obj (subseq n)).basepoint := Psi.basepoint_map n
    rwa [hbase] at hn
  obtain ⟨psi, g, hpsi, hg, hconv⟩ :=
    Psi.exists_lipschitz_subseq_limit C href hcomplete f K hLip hbdd
  have heq (z : P.M) : g z = Real.sqrt (ell z) :=
    tendsto_nhds_unique ((hconv {z} isCompact_singleton).tendsto_at (mem_singleton z))
      ((hpoint z).comp hpsi.tendsto_atTop)
  have hh := hg (show P.M from x) (show P.M from y)
  rw [heq, heq] at hh
  exact hh

theorem backward_flow_limit_redLength_le_quadratic_distance
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M] {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (C : MetricConvergenceData (Phi.atTime (I := I) (X := backwardFlowSequence F tau htau q) (L := L) 0))
    (href : ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric)
    (hcomplete : MetricComplete (L.atTime 0))
    {T : ℝ} (hT : 1 ≤ T) (ell : L.M × Icc (1 : ℝ) T → ℝ)
    (hell : ∀ w, Tendsto
      (fun n => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) atTop (𝓝 (ell w)))
    (x : L.M) (theta : Icc (1 : ℝ) T) :
    ell (x, theta) ≤ (1 + 3 * T ^ 2) *
      (Real.sqrt (ell (L.basepoint, ⟨1, le_rfl, hT⟩)) + Real.sqrt 3 / 2 *
        (riemannianEDistOf (L.S.base.metric 0) L.basepoint x).toReal) ^ 2 := by
  let oneTime : Icc (1 : ℝ) T := ⟨1, le_rfl, hT⟩
  have htime : ell (x, theta) ≤ (1 + 3 * T ^ 2) * ell (x, oneTime) := by
    apply le_of_tendsto_of_tendsto (hell (x, theta)) ((hell (x, oneTime)).const_mul _)
    exact Eventually.of_forall fun n => by
      simpa only [oneTime, mul_one] using redLength_le_mul_on_rescaled_time_interval
        F hF p (Phi.map n x) (htau (subseq n)) theta.property
  have hnonneg : 0 ≤ ell (x, oneTime) := by
    apply ge_of_tendsto (hell (x, oneTime))
    exact Eventually.of_forall fun n => by
      simpa only [oneTime, mul_one] using
        backward_length_nonneg F hF p (Phi.map n x) (htau (subseq n))
  have h := abs_sqrt_backward_flow_limit_redLength_sub_le_distance
    F hF p tau htau q L Phi (t := 0) zero_lt_one C href hcomplete
    (fun y => ell (y, oneTime))
    (fun y => by simpa only [oneTime, sub_zero] using hell (y, oneTime)) L.basepoint x
  simp only [sub_zero, Real.sqrt_one, mul_one] at h
  have hroot : Real.sqrt (ell (x, oneTime)) ≤ Real.sqrt (ell (L.basepoint, oneTime)) +
      Real.sqrt 3 / 2 * (riemannianEDistOf (L.S.base.metric 0) L.basepoint x).toReal := by
    linarith only [(abs_le.mp h).1]
  have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hroot
  rw [Real.sq_sqrt hnonneg] at hsquare
  exact htime.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))

theorem normGradSqFun_backward_flow_limit_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M] {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {t : ℝ} (ht : t < 1)
    (C : MetricConvergenceData (Phi.atTime (I := I) (X := backwardFlowSequence F tau htau q) (L := L) t))
    (href : ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric)
    (hcomplete : MetricComplete (L.atTime t))
    (ell : L.M → ℝ)
    (hell : ∀ x, Tendsto
      (fun n => redLength F.S 0 p (Phi.map n x) (tau (subseq n) * (1 - t))) atTop (𝓝 (ell x)))
    (x : L.M) : Geometry.Operator.normGradSqFun (L.S.base.metric t) ell x ≤ 3 * ell x / (1 - t) := by
  have htheta : 0 < 1 - t := sub_pos.mpr ht
  have hell0 (y : L.M) : 0 ≤ ell y := by
    apply ge_of_tendsto (hell y)
    exact Eventually.of_forall fun n =>
      backward_length_nonneg F hF p (Phi.map n y) (mul_pos (htau (subseq n)) htheta)
  let K : ℝ≥0 := ⟨Real.sqrt 3 / (2 * Real.sqrt (1 - t)), by positivity⟩
  have hLip (y z : L.M) : edist (Real.sqrt (ell y)) (Real.sqrt (ell z)) ≤
      (K : ENNReal) * riemannianEDistOf (L.S.base.metric t) y z := by
    have h := abs_sqrt_backward_flow_limit_redLength_sub_le_distance
      F hF p tau htau q L Phi ht C href hcomplete ell hell y z
    have h' : |Real.sqrt (ell y) - Real.sqrt (ell z)| ≤
        (K : ℝ) * (riemannianEDistOf (L.S.base.metric t) y z).toReal := h
    have he := ENNReal.ofReal_le_ofReal h'
    rw [ENNReal.ofReal_mul K.coe_nonneg,
      ENNReal.ofReal_toReal (riemannianEDistOf_ne_top (L.S.base.metric t) y z)] at he
    simpa only [edist_dist, Real.dist_eq, ENNReal.coe_nnreal_eq] using he
  have h := Geometry.Riemannian.grad_norm_sq_le_of_sqrt_lipschitz (L.S.base.metric t) hell0 hLip x
  calc
    _ ≤ 4 * (K : ℝ) ^ 2 * ell x := h
    _ = _ := by
      change 4 * (Real.sqrt 3 / (2 * Real.sqrt (1 - t))) ^ 2 * ell x = 3 * ell x / (1 - t)
      rw [div_pow, mul_pow, Real.sq_sqrt htheta.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      field_simp
      ring

theorem normGradSqFun_backward_flow_limit_perelmanDensity_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M] {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {t : ℝ} (ht : t < 1)
    (C : MetricConvergenceData (Phi.atTime (I := I) (X := backwardFlowSequence F tau htau q) (L := L) t))
    (href : ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric)
    (hcomplete : MetricComplete (L.atTime t))
    (ell : L.M → ℝ)
    (hell : ∀ x, Tendsto
      (fun n => redLength F.S 0 p (Phi.map n x) (tau (subseq n) * (1 - t))) atTop (𝓝 (ell x)))
    (x : L.M) : Geometry.Operator.normGradSqFun (L.S.base.metric t)
      (Entropy.perelmanDensity (Module.finrank ℝ E) (1 - t) ell) x ≤
        3 * ell x / (1 - t) * Entropy.perelmanDensity (Module.finrank ℝ E) (1 - t) ell x ^ 2 := by
  have heq : Geometry.Operator.normGradSqFun (L.S.base.metric t)
      (Entropy.perelmanDensity (Module.finrank ℝ E) (1 - t) ell) x =
        Entropy.perelmanDensity (Module.finrank ℝ E) (1 - t) ell x ^ 2 *
          Geometry.Operator.normGradSqFun (L.S.base.metric t) ell x :=
    Entropy.density_grad_sq (L.S.base.metric t) (Module.finrank ℝ E) (1 - t) ell x
  rw [heq]
  have h := normGradSqFun_backward_flow_limit_redLength_le
    F hF p tau htau q L Phi ht C href hcomplete ell hell x
  calc
    _ ≤ Entropy.perelmanDensity (Module.finrank ℝ E) (1 - t) ell x ^ 2 *
        (3 * ell x / (1 - t)) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := mul_comm _ _

theorem exists_backward_flow_limit_perelmanDensity_gradient_le_linear_distance
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M] {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ} (hT : 1 ≤ T)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime (I := I) (X := backwardFlowSequence F tau htau q) (L := L) t),
        ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (ell : L.M × Icc (1 : ℝ) T → ℝ)
    (hell : ∀ w, Tendsto
      (fun n => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) atTop (𝓝 (ell w))) :
    ∃ C : ℝ≥0, ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Real.sqrt (Geometry.Operator.normGradSqFun (L.S.base.metric (1 - theta))
        (Entropy.perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta))) x) ≤
          C * (1 + (riemannianEDistOf (L.S.base.metric 0) L.basepoint x).toReal) *
            Entropy.perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta)) x := by
  let A := Real.sqrt (ell (L.basepoint, ⟨1, le_rfl, hT⟩))
  let B := Real.sqrt 3 / 2
  let K := 1 + 3 * T ^ 2
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let C : ℝ≥0 := ⟨Real.sqrt (3 * K) * (A + B), by positivity⟩
  refine ⟨C, ?_⟩
  intro theta x
  have ht : 1 - (theta : ℝ) ∈ Icc (1 - T) (0 : ℝ) :=
    ⟨sub_le_sub_left theta.property.2 1, sub_nonpos.mpr theta.property.1⟩
  have hzero : (0 : ℝ) ∈ Icc (1 - T) (0 : ℝ) := ⟨sub_nonpos.mpr hT, le_rfl⟩
  have htheta : 0 < (theta : ℝ) := zero_lt_one.trans_le theta.property.1
  obtain ⟨C0, href0⟩ := hconv 0 hzero
  obtain ⟨Ct, hreft⟩ := hconv (1 - theta) ht
  have hg := normGradSqFun_backward_flow_limit_perelmanDensity_le F hF p tau htau q L Phi
    (t := 1 - theta) (by linarith) Ct hreft (hcomplete _ ht)
    (fun y => ell (y, theta)) (fun y => by simpa only [sub_sub_cancel] using hell (y, theta)) x
  simp only [sub_sub_cancel] at hg
  have hq := backward_flow_limit_redLength_le_quadratic_distance
    F hF p tau htau q L Phi C0 href0 (hcomplete 0 hzero) hT ell hell x theta
  let r := (riemannianEDistOf (L.S.base.metric 0) L.basepoint x).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hl0 : 0 ≤ ell (x, theta) := by
    apply ge_of_tendsto (hell (x, theta))
    exact Eventually.of_forall fun n => backward_length_nonneg F hF p (Phi.map n x)
      (mul_pos (htau (subseq n)) htheta)
  let u := Entropy.perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta)) x
  have hu : 0 ≤ u := by
    exact le_of_lt (mul_pos (Entropy.prefactor_pos (Module.finrank ℝ E) htheta) (Real.exp_pos _))
  have hlin : A + B * r ≤ (A + B) * (1 + r) := by
    nlinarith [mul_nonneg hA hr]
  have hsq : (A + B * r) ^ 2 ≤ ((A + B) * (1 + r)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hlin
  have hq' : ell (x, theta) ≤ K * ((A + B) * (1 + r)) ^ 2 :=
    hq.trans (mul_le_mul_of_nonneg_left hsq hK)
  have hdiv : 3 * ell (x, theta) / (theta : ℝ) ≤ 3 * ell (x, theta) :=
    div_le_self (by positivity) theta.property.1
  have hsqC : ((C : ℝ) * (1 + r) * u) ^ 2 =
      3 * K * ((A + B) * (1 + r)) ^ 2 * u ^ 2 := by
    change (Real.sqrt (3 * K) * (A + B) * (1 + r) * u) ^ 2 = _
    simp only [mul_pow, Real.sq_sqrt (show 0 ≤ 3 * K by positivity)]
    ring
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  change Geometry.Operator.normGradSqFun _ _ x ≤ ((C : ℝ) * (1 + r) * u) ^ 2
  rw [hsqC]
  exact hg.trans ((mul_le_mul_of_nonneg_right hdiv (sq_nonneg u)).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [hq']) (sq_nonneg u)))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

theorem exists_backward_flow_reducedLength_limit_with_uniform_metric_convergence
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    {T : ℝ} (hT : 1 ≤ T) :
    let X := backwardFlowSequence F tau htau q
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∃ Phi : PointedCGHMaps (I := I) X (L.atTime 0) phi,
        ConnectedSpace L.M ∧ (∀ t : ℝ, t ≤ 0 → MetricComplete (L.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∃ C : MetricConvergenceData (I := I) (Phi.atTime (I := I) (X := X) (L := L) t),
          (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I)
            (Phi.atTime (I := I) (X := X) (L := L) t) k) ∧
          (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)) ∧
        ∃ (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M),
          (∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
            ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
              ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
                (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner
                  (Phi.map i x) (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)) ∧
          (∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
            ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ i ≥ N,
              ∀ t ∈ Icc a b,
                metricDerivNormSupOn K r (G i t) (L.S.base.metric t) R < epsilon) ∧
        ∃ ell : C(L.M × Icc (1 : ℝ) T, ℝ),
          (∀ z, 0 ≤ ell z) ∧ ell (L.basepoint, ⟨1, le_rfl, hT⟩) ≤ A ∧
          (∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
            ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
            ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
            ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
              (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|)) ∧
          ∀ S : Set (L.M × Icc (1 : ℝ) T), IsCompact S → TendstoUniformlyOn
            (fun i z => redLength F.S 0 p (Phi.map i z.1) (tau (phi i) * z.2)) ell atTop S := by
  let X := backwardFlowSequence F tau htau q
  obtain ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconv, R, G, hG, hmetric⟩ :=
    exists_backward_flow_compactness_with_uniform_metric_convergence F hF p tau htau q hbase
  let _ : ConnectedSpace L.M := hconnected
  let _ : ConnectedSpace (L.atTime 0).M := hconnected
  let Phi0 := backwardFlowZeroMaps F tau htau q L Phi
  obtain ⟨C, _, href⟩ := hconv 0 le_rfl
  obtain ⟨C0, href0⟩ := exists_backward_flow_zero_metric_convergence F tau htau q L Phi C
    (fun k => href k)
  obtain ⟨psi, ell, hpsi, hnonneg, hbaseLimit, hLip, hpotential⟩ :=
    exists_reducedLength_limit_on_rescaled_time_interval F hF p tau htau q hbase
      (L.atTime 0) Phi0 C0 href0 (hcomplete 0 le_rfl) hT
  refine ⟨L, phi ∘ psi, hphi.comp hpsi, Phi.compSubseq psi hpsi, hconnected, hcomplete,
    ?_, R, (fun i t => G (psi i) t), ?_, ?_, ell, hnonneg, hbaseLimit, hLip, hpotential⟩
  · intro t ht
    obtain ⟨C, hcanonical, href⟩ := hconv t ht
    refine ⟨C.compSubseq psi hpsi, ?_, ?_⟩
    · intro i
      change MetricSourceData.compSubseq psi hpsi i (C.domain (psi i)) = _
      rw [hcanonical]
      rfl
    · intro i
      exact href (psi i)
  · intro K hK
    exact hpsi.tendsto_atTop.eventually (hG K hK)
  · intro a b hab K hK r epsilon hepsilon
    obtain ⟨N, hN⟩ := hmetric a b hab K hK r epsilon hepsilon
    exact ⟨N, fun i hi t ht => hN (psi i) (hi.trans (hpsi.id_le i)) t ht⟩

theorem exists_backward_flow_reducedLength_limit
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A)
    {T : ℝ} (hT : 1 ≤ T) :
    let X := backwardFlowSequence F tau htau q
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∃ Phi : PointedCGHMaps (I := I) X (L.atTime 0) phi,
        ConnectedSpace L.M ∧ (∀ t : ℝ, t ≤ 0 → MetricComplete (L.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∃ C : MetricConvergenceData (I := I) (Phi.atTime (I := I) (X := X) (L := L) t),
          (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I)
            (Phi.atTime (I := I) (X := X) (L := L) t) k) ∧
          (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)) ∧
        ∃ ell : C(L.M × Icc (1 : ℝ) T, ℝ),
          (∀ z, 0 ≤ ell z) ∧ ell (L.basepoint, ⟨1, le_rfl, hT⟩) ≤ A ∧
          (∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
            ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
            ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
            ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
              (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|)) ∧
          ∀ S : Set (L.M × Icc (1 : ℝ) T), IsCompact S → TendstoUniformlyOn
            (fun i z => redLength F.S 0 p (Phi.map i z.1) (tau (phi i) * z.2)) ell atTop S := by
  obtain ⟨L, phi, hphi, Phi, hconn, hcomp, hconv, R, G, hG, hmetric, hell⟩ :=
    exists_backward_flow_reducedLength_limit_with_uniform_metric_convergence
      F hF p tau htau q hbase hT
  exact ⟨L, phi, hphi, Phi, hconn, hcomp, hconv, hell⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
