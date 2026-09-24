import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

theorem PointedRiemannianConvergenceMaps.eventually_edist_map_le_on_closed_ball
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) (p : P.M) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 1 < L) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric p A ⊆ F.source i ∧
      ∀ x ∈ riemannianClosedBallOf P.metric p A,
        ∀ y ∈ riemannianClosedBallOf P.metric p A,
          riemannianEDistOf (X.obj (phi i)).metric (F.map i x) (F.map i y) ≤
            ENNReal.ofReal L * riemannianEDistOf P.metric x y := by
  have hmetricComplete : RiemannianMetricComplete (I := I) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  let K := riemannianClosedBallOf (I := I) P.metric p (3 * A + 1)
  have hK : IsCompact K := hmetricComplete.closedEBall_isCompact p (3 * A + 1)
  have heps : 0 < L ^ 2 - 1 := by nlinarith
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href K hK
    (L ^ 2 - 1) heps
  filter_upwards [eventually_ge_atTop N] with i hi
  have hin : riemannianClosedBallOf (I := I) P.metric p A ⊆ K :=
    fun _ hx => hx.trans (ENNReal.ofReal_le_ofReal (by linarith))
  refine ⟨hin.trans (hN i hi).1, fun x hx y hy => ?_⟩
  have hupper : ∀ z ∈ K, ∀ v : TangentSpace I z,
      (X.obj (phi i)).metric.inner (F.map i z)
          (mfderiv I I (F.map i) z v) (mfderiv I I (F.map i) z v) ≤
        L ^ 2 * P.metric.inner z v v := by
    intro z hz v
    have herr := (abs_le.mp ((hN i hi).2 z hz v)).2
    nlinarith
  exact edistOf_map_le_of_metric_upper_on_buffered_ball
    P.metric (X.obj (phi i)).metric (F.partialDiffeomorph i) p x y hA
    (by linarith : 3 * A < 3 * A + 1) (by linarith : 0 < L)
    (hN i hi).1 hupper hx hy

theorem PointedRiemannianConvergenceMaps.eventually_image_closed_ball_subset
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) (p : P.M) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 1 < L) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric p A ⊆ F.source i ∧
      F.map i '' riemannianClosedBallOf P.metric p A ⊆
        riemannianClosedBallOf (X.obj (phi i)).metric (F.map i p) (L * A) := by
  filter_upwards [F.eventually_edist_map_le_on_closed_ball C href hcomplete p hA hL]
    with i hi
  refine ⟨hi.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hp : p ∈ riemannianClosedBallOf P.metric p A := by
    change riemannianEDistOf P.metric p p ≤ ENNReal.ofReal A
    rw [riemannianEDistOf_self]
    exact bot_le
  calc
    _ ≤ ENNReal.ofReal L * riemannianEDistOf P.metric p x := hi.2 p hp x hx
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal A := mul_le_mul' le_rfl hx
    _ = ENNReal.ofReal (L * A) := (ENNReal.ofReal_mul (by linarith : 0 ≤ L)).symm


omit [CompleteSpace E] in
theorem PointedRiemannianConvergenceMaps.exists_eventually_image_compact_subset_ball_of_metric_upper
    [PreconnectedSpace P.M]
    (F : PointedRiemannianConvergenceMaps X P phi)
    (hcomplete : MetricComplete P) {L : ℝ} (hL : 0 < L)
    (hupper : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace I z,
        (X.obj (phi i)).metric.inner (F.map i z)
          (mfderiv I I (F.map i) z v) (mfderiv I I (F.map i) z v) ≤
          L ^ 2 * P.metric.inner z v v)
    {K : Set P.M} (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ i in atTop, K ⊆ F.source i ∧
      F.map i '' K ⊆
        riemannianClosedBallOf (X.obj (phi i)).metric (X.obj (phi i)).basepoint A := by
  have hcont : Continuous (fun x : P.M =>
      (riemannianEDistOf P.metric P.basepoint x).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ENNReal.continuousAt_toReal
      (riemannianEDistOf_ne_top P.metric P.basepoint x)).comp
      (Geometry.Riemannian.continuous_riemannianEDist P.metric P.basepoint).continuousAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.continuousOn
  let R := max B 0 + 1
  have hR : 0 < R := by dsimp only [R]; linarith [le_max_right B 0]
  have hKR : K ⊆ riemannianClosedBallOf P.metric P.basepoint R := by
    intro x hx
    apply (ENNReal.toReal_le_toReal (riemannianEDistOf_ne_top P.metric P.basepoint x)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hR.le]
    exact (hB ⟨x, hx, rfl⟩).trans (by dsimp only [R]; linarith [le_max_left B 0])
  have hc : RiemannianMetricComplete (I := I) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  let B := riemannianClosedBallOf P.metric P.basepoint (3 * R + 1)
  have hBcompact : IsCompact B := hc.closedEBall_isCompact _ _
  obtain ⟨N, hN⟩ := F.source_exhausts.subset B hBcompact
  refine ⟨L * R, mul_pos hL hR, ?_⟩
  filter_upwards [hupper B hBcompact, eventually_ge_atTop N] with i hi hNi
  have hin : K ⊆ B := hKR.trans (riemannianClosedBallOf_mono _ _ (by linarith))
  refine ⟨hin.trans (hN i hNi), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hp : P.basepoint ∈ riemannianClosedBallOf P.metric P.basepoint R := by
    change riemannianEDistOf P.metric P.basepoint P.basepoint ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le
  have hdist := edistOf_map_le_of_metric_upper_on_buffered_ball
    P.metric (X.obj (phi i)).metric (F.partialDiffeomorph i) P.basepoint
    P.basepoint y hR.le (by linarith : 3 * R < 3 * R + 1) hL (hN i hNi) hi hp (hKR hy)
  change riemannianEDistOf (X.obj (phi i)).metric (X.obj (phi i)).basepoint (F.map i y) ≤ _
  rw [← F.basepoint_map i]
  exact hdist.trans ((mul_le_mul' le_rfl (hKR hy)).trans_eq
    (ENNReal.ofReal_mul hL.le).symm)

theorem PointedRiemannianConvergenceMaps.exists_eventually_image_compact_subset_ball
    [PreconnectedSpace P.M]
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) {K : Set P.M} (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ i in atTop, K ⊆ F.source i ∧
      F.map i '' K ⊆
        riemannianClosedBallOf (X.obj (phi i)).metric (X.obj (phi i)).basepoint A := by
  apply F.exists_eventually_image_compact_subset_ball_of_metric_upper hcomplete
    (by norm_num : (0 : ℝ) < 2) ?_ hK
  intro K' hK'
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href K' hK'
    3 (by norm_num)
  filter_upwards [eventually_ge_atTop N] with i hi
  intro z hz v
  have herr := (abs_le.mp ((hN i hi).2 z hz v)).2
  nlinarith

theorem PointedRiemannianConvergenceMaps.eventually_ball_subset_image_closed_ball
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) (p : P.M) {A R L : ℝ}
    (hL : 1 < L) (hmargin : L * A < R) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric p R ⊆ F.source i ∧
      riemannianBallOf (X.obj (phi i)).metric (F.map i p) A ⊆
        F.map i '' riemannianClosedBallOf P.metric p R := by
  let _ : TopologicalSpace.MetrizableSpace P.M := _root_.Manifold.metrizableSpace I P.M
  have hc : RiemannianMetricComplete (I := I) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  let K := riemannianClosedBallOf P.metric p R
  have hK : IsCompact K := hc.closedEBall_isCompact p R
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith)
  have heps : 0 < 1 - (L ^ 2)⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ hLsq).mpr (by nlinarith))
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href K hK
    (1 - (L ^ 2)⁻¹) heps
  filter_upwards [eventually_ge_atTop N] with i hi
  let _ : TopologicalSpace.MetrizableSpace (X.obj (phi i)).M :=
    _root_.Manifold.metrizableSpace I (X.obj (phi i)).M
  refine ⟨(hN i hi).1, ?_⟩
  apply PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower
    P.metric (X.obj (phi i)).metric (F.partialDiffeomorph i)
    (r := (R - L * A) / 2) (C := L) (by linarith) hK (hN i hi).1
  · intro z hz v
    have hh := (abs_le.mp ((hN i hi).2 z hz v)).1
    have hquad : (L ^ 2)⁻¹ * P.metric.inner z v v ≤
        (X.obj (phi i)).metric.inner (F.map i z)
          (mfderiv I I (F.map i) z v) (mfderiv I I (F.map i) z v) := by
      linarith
    calc
      _ = L ^ 2 * ((L ^ 2)⁻¹ * P.metric.inner z v v) := by
        rw [← mul_assoc, mul_inv_cancel₀ hLsq.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hquad (sq_nonneg L)
  · change riemannianEDistOf P.metric p p < ENNReal.ofReal ((R - L * A) / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  · linarith


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem PointedRiemannianConvergenceMaps.exists_eventually_image_compact_subset_inner_ball
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f) {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (hupper : ∀ K : Set L.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I x,
        (X.obj (f i)).metric.inner (F.map i x)
          (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) ≤
            C ^ 2 * L.metric.inner x v v)
    {K : Set L.M} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ R < rho ∧ ∀ᶠ i in atTop,
      K ⊆ F.source i ∧ F.map i '' K ⊆ riemannianBallOf (X.obj (f i)).metric (X.obj (f i)).basepoint R := by
  have hdistfinite (x : L.M) : riemannianEDistOf L.metric L.basepoint x ≠ ⊤ := ne_top_of_lt (hradial x)
  have hcontinuous : Continuous (fun x : L.M => (riemannianEDistOf L.metric L.basepoint x).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ENNReal.continuousAt_toReal (hdistfinite x)).comp
      (Geometry.Riemannian.continuous_riemannianEDist L.metric L.basepoint).continuousAt
  have hnear : ∃ r : ℝ, 0 < r ∧ r < rho ∧ K ⊆ riemannianBallOf L.metric L.basepoint r := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨rho / 2, half_pos hrho, half_lt_self hrho, empty_subset _⟩
    obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hcontinuous.continuousOn
    have hdx : (riemannianEDistOf L.metric L.basepoint x).toReal < rho :=
      ENNReal.toReal_lt_of_lt_ofReal (hradial x)
    obtain ⟨r, hr, hrrho⟩ := exists_between hdx
    have hrpos : 0 < r := ENNReal.toReal_nonneg.trans_lt hr
    refine ⟨r, hrpos, hrrho, fun y hy => ?_⟩
    exact (ENNReal.lt_ofReal_iff_toReal_lt (hdistfinite y)).mpr ((hmax hy).trans_lt hr)
  obtain ⟨r, hr, hrrho, hKr⟩ := hnear
  let R := (r + rho) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hRrho : R < rho := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  let C := R / r
  have hC : 1 < C := (one_lt_div hr).mpr hrR
  let B := (r + R) / 2
  have hrB : r < B := by dsimp [B]; linarith
  have hB : 0 < B := hr.trans hrB
  have hBrho : B < rho := by dsimp [B]; linarith
  have hcpt := hcompact B hB.le hBrho
  obtain ⟨N, hN⟩ := F.source_exhausts.subset _ hcpt
  refine ⟨R, hR, hRrho, ?_⟩
  filter_upwards [hupper _ hcpt C hC, eventually_ge_atTop N] with i hi hNi
  have hsource := hN i hNi
  have hKsource : K ⊆ F.source i := fun x hx => hsource
    ((hKr hx).le.trans (ENNReal.ofReal_le_ofReal hrB.le))
  refine ⟨hKsource, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hdx : riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal r := hKr hx
  have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    L.metric (X.obj (f i)).metric (F.partialDiffeomorph i) L.basepoint x hB (zero_lt_one.trans hC)
    hsource hi (hdx.trans_le (ENNReal.ofReal_le_ofReal hrB.le))
  rw [F.basepoint_map i] at hd
  change riemannianEDistOf (X.obj (f i)).metric (X.obj (f i)).basepoint (F.map i x) < _
  apply hd.trans_lt
  calc
    _ < ENNReal.ofReal C * ENNReal.ofReal r :=
      (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hC))
        ENNReal.ofReal_ne_top).mpr hdx
    _ = ENNReal.ofReal R := by rw [← ENNReal.ofReal_mul (zero_lt_one.trans hC).le]; congr 1; exact div_mul_cancel₀ R hr.ne'



end DifferentialGeometry.CheegerGromovCompactness
