import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterBalls_CX8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterRealized_CX8
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalMetricExtraction
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Metric.PullbackScaling

set_option autoImplicit false

/-!
# CH12-CX8: extracting a linked parabolic limit from survivor flows

The compactness input uses the intrinsic metrics of the open survivor balls. Its volume
hypothesis follows from the original single-time seed, and its compactness hypothesis from
a strictly smaller closed ball in the compact ambient slice. Only a local limit is extracted.
-/

noncomputable section
open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12
universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

open private ObservedHistory.exists_small_volume_radius
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- Any late seeded sequence with uniformly controlled, realized survivor flows has a centre
with arbitrarily small Ricci defect. This is the contradiction kernel for O5's C1 statement. -/
theorem exists_center_defect_lt_of_survivors_CX8
    {P : OrientedThreeStage.{u}} {g₀ : P.Metric} {F : GC.Interface.RawSurgery P g₀}
    {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (S : LatePointSequence_S13 F) {a v b θ K : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hba : b ≤ a) (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 0 < K)
    (hseed : ∀ n, HasNormalizedSeed_S13 (S.slices n) (S.point n) a v)
    (W : ∀ n, Opens (S.slices n).stage.Carrier)
    (h : ∀ n, ℝ → SmoothRiemannianMetric ThreeModel (W n))
    (hW : ∀ n, (W n : Set (S.slices n).stage.Carrier) =
      riemannianBallOf (S.slices n).normalizedMetric (S.point n) (2 * b))
    (hsol : ∀ n, IsSolutionOn (flowOn_O7 (h n) θ hθ.le))
    (hzero : ∀ n, h n 0 = (S.slices n).normalizedMetric.restrictOpen (W n))
    (hcurv : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ x : W n, curvDerivNormSq 0 (h n s) x ≤ K ^ 2)
    (hreal : ∀ n, ∀ s ∈ Icc (-θ) 0, ∃ (X : OrientedThreeStage.{u}) (m : X.Metric)
      (f : W n → X.Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f),
      Function.Injective f ∧
      h n s = scaleMetric (S.slices n).time⁻¹ (inv_pos.mpr (S.slices n).positive)
        (localPullMetric m f hf) ∧
      (∀ x : X.Carrier, -3 / (2 * ((S.slices n).time * (1 + s) + Hp.scalarShift)) ≤
        metricScalarAt m x) ∧
      metricDeficit_O7 m Hp.scalarShift ((S.slices n).time * (1 + s)) =
        metricDeficit_O7 (GC.LongTime.postMetric F.observation ((S.slices n).time * (1 + s)))
          Hp.scalarShift ((S.slices n).time * (1 + s)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, NormalizedRicciDefect_S13 (S.slices n) (S.point n) < ε := by
  have hp (n : ℕ) : S.point n ∈ W n := by
    change S.point n ∈ (W n : Set _)
    rw [hW]
    change riemannianEDistOf _ _ _ < ENNReal.ofReal (2 * b)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    { obj := fun n => { M := W n, metric := h n 0, basepoint := ⟨S.point n, hp n⟩ } }
  have hconn : ∀ n, ConnectedSpace (X.obj n).M := by
    intro n
    have hpath : IsPathConnected (W n : Set (S.slices n).stage.Carrier) := by
      rw [hW]
      exact isPathConnected_riemannianBallOf _ _ (by positivity)
    exact isConnected_iff_connectedSpace.mp hpath.isConnected
  obtain ⟨r, hr, -, hrb, hrK, -⟩ :=
    ObservedHistory.exists_small_volume_radius (r := 0) (R' := b / 32) (C := K) (K := 0)
      (by positivity) hK.le le_rfl
  have hrb' : r ≤ b / 32 := by linarith
  obtain ⟨κ, hκ, hvol⟩ := seed_volume_on_open_ball_CX8.{u} v hv
  have hcompact : ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint b) := by
    apply Eventually.of_forall
    intro n
    change IsCompact (riemannianClosedBallOf (h n 0) ⟨S.point n, hp n⟩ b)
    rw [hzero]
    apply FILL910.isCompact_riemannianClosedBallOf_restrictOpen_of_subset
    intro x hx
    rw [hW]
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  have hvol' : ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf
      (X.obj n).metric (X.obj n).basepoint r,
      ENNReal.ofReal (κ * r ^ Module.finrank ℝ ThreeSpace) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
          (riemannianBallOf (X.obj n).metric x r) := by
    apply Eventually.of_forall
    intro n x hx
    change x ∈ riemannianClosedBallOf (h n 0) ⟨S.point n, hp n⟩ r at hx
    change ENNReal.ofReal (κ * r ^ Module.finrank ℝ ThreeSpace) ≤ ballVolume (h n 0) x r
    rw [hzero] at hx ⊢
    simpa using hvol _ (S.slices n).normalizedMetric (S.point n) hb hba
      (hseed n).1 (hseed n).2 (W n) (hW n) (hp n) r hr (by linarith) x hx
  obtain ⟨φ, hφ, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Φ, G,
      hV, hq, hsource, hbase, -, -, -, -, L, hLS, hmetricL, -, ρ, hρ, g, hgzero, hgsol, hconv⟩ :=
    exists_local_flow_limit_of_curvature_bound_and_volume_lower_bound X
      (fun n => flowOn_O7 (h n) θ hθ.le) hsol hconn
      (R := b) (r := r) (a := r) (κ := κ) (K := K)
      hr.le hr (by linarith) hκ hK hrK (by linarith : -θ < 0)
      (fun _ hs => hs) (fun _ hs => hs) (fun _ => rfl) hcompact
      (Eventually.of_forall fun n s hs x _ => hcurv n s hs x) hvol'
  let : TopologicalSpace Q := top
  let : ChartedSpace ThreeSpace Q := charts
  let : IsManifold ThreeModel ∞ Q := hman
  let : T2Space Q := hT2
  let : SecondCountableTopology Q := hsecond
  let : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace ThreeSpace Q
  let : SigmaCompactSpace Q := inferInstance
  let f (n : ℕ) : V → (X.obj (φ n)).M := fun x => Φ n (x : Q)
  have hf (n : ℕ) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f n) := by
    intro x
    exact IsLocalDiffeomorphAt.comp ThreeModel (X.obj (φ n)).M
      (isLocalDiffeomorph_subtype_val V x)
      ((Φ n).isLocalDiffeomorphAt ThreeModel ThreeModel ∞ (hsource n (subset_closure x.property)))
  have hfinj (n : ℕ) : Function.Injective (f n) := by
    intro x y hxy
    exact Subtype.ext ((Φ n).injOn (hsource n (subset_closure x.property))
      (hsource n (subset_closure y.property)) hxy)
  have hpull (n : ℕ) (s : ℝ) :
      (L n).base.metric s = localPullMetric (h (φ n) s) (f n) (hf n) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hd (v : TangentSpace ThreeModel x) :
        mfderiv ThreeModel ThreeModel (f n) x v =
          mfderiv ThreeModel ThreeModel (Φ n) (x : Q) v := by
      have hc := mfderiv_comp_apply x
        (((Φ n).isLocalDiffeomorphAt ThreeModel ThreeModel ∞
          (hsource n (subset_closure x.property))).mdifferentiableAt (by simp))
        ((isLocalDiffeomorph_subtype_val V x).mdifferentiableAt (by simp))
      simpa only [f, Function.comp_def, mfderiv_subtype_val_apply] using hc v
    rw [localPullMetric_inner, hd v, hd w]
    exact hmetricL n s x v w
  have hhalf : 0 < θ / 2 := half_pos hθ
  have hsub : Icc (-(θ / 2)) 0 ⊆ Icc (-θ) 0 :=
    fun _ hs => ⟨by linarith [hs.1], hs.2⟩
  simp only [add_zero, neg_div] at hgsol hconv
  have hgsol' : IsSolutionOn (flowOn_O7 g (θ / 2) hhalf.le) := by
    exact isSolutionOn_timeRestrict hgsol
      (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
      (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
  have hLS' : ∀ n, IsSolutionOn (flowOn_O7 (fun s => (L (ρ n)).base.metric s) (θ / 2) hhalf.le) := by
    intro n
    exact isSolutionOn_timeRestrict (hLS (ρ n)) hsub (fun _ hs => ⟨by linarith [hs.1], hs.2⟩)
  have hcurv' : ∀ n, ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x : V,
      curvDerivNormSq 0 ((L (ρ n)).base.metric s) x ≤ K ^ 2 := by
    intro n s hs x
    rw [hpull, curvDerivNormSq_localPullMetric]
    exact hcurv (φ (ρ n)) s (hsub hs) _
  have hreal' : ∀ n, ∀ s ∈ Icc (-(θ / 2)) 0,
      ∃ (Y : OrientedThreeStage.{u}) (m : Y.Metric)
        (k : V → Y.Carrier) (hk : IsLocalDiffeomorph ThreeModel ThreeModel ∞ k),
        Function.Injective k ∧
        (L (ρ n)).base.metric s = scaleMetric (S.slices (φ (ρ n))).time⁻¹
          (inv_pos.mpr (S.slices (φ (ρ n))).positive) (localPullMetric m k hk) ∧
        (∀ x : Y.Carrier, -3 / (2 * ((S.slices (φ (ρ n))).time * (1 + s) + Hp.scalarShift)) ≤
          metricScalarAt m x) ∧
        metricDeficit_O7 m Hp.scalarShift ((S.slices (φ (ρ n))).time * (1 + s)) =
          metricDeficit_O7 (GC.LongTime.postMetric F.observation
            ((S.slices (φ (ρ n))).time * (1 + s))) Hp.scalarShift
              ((S.slices (φ (ρ n))).time * (1 + s)) := by
    intro n s hs
    obtain ⟨Y, m, k, hk, hinj, hm, hlow, hdef⟩ := hreal (φ (ρ n)) s (hsub hs)
    refine ⟨Y, m, k ∘ f (ρ n), isLocalDiffeomorph_comp hk (hf (ρ n)),
      hinj.comp (hfinj (ρ n)), ?_, hlow, hdef⟩
    rw [hpull, hm, localPullMetric_scaleMetric, localPullMetric_comp]
  have hev := eventually_defect_lt_of_realized_limit_CX8 Hp g
    (fun n s => (L (ρ n)).base.metric s) hhalf (by linarith) hK.le hgsol' hLS' hcurv'
    (fun A hA ε hε => by simpa only [hgzero] using hconv A hA 2 ε hε)
    (fun n => (S.slices (φ (ρ n))).time) (fun n => (S.slices (φ (ρ n))).positive)
    (S.times_tendsto.comp (hφ.comp hρ).tendsto_atTop) hreal' ⟨q, hq⟩ ε hε
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨φ (ρ n), ?_⟩
  rw [hpull, defectSet_localPullMetric_CX8] at hn
  change sSup (defectSet_O5 (h (φ (ρ n)) 0) (Φ (ρ n) q)) < ε at hn
  rw [hbase] at hn
  change sSup (defectSet_O5 (h (φ (ρ n)) 0) ⟨S.point (φ (ρ n)), hp (φ (ρ n))⟩) < ε at hn
  rw [hzero, defectSet_restrictOpen_CX8] at hn
  exact hn

end GC.LongTime.Ch12
