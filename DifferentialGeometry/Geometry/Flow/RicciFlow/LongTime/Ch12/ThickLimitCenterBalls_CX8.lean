import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueVolumeTest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

set_option autoImplicit false

/-!
# CH12-CX8: volume and compactness inside the survivor ball

The restriction has its intrinsic Riemannian distance. Equality of small-ball volumes is
proved by the local-isometry ball-image theorem, with a compact buffer inside the open set.
-/

noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12
universe u

private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

private local instance {M : Type*} [TopologicalSpace M] (U : Opens M) : MeasurableSpace U := borel U
private local instance {M : Type*} [TopologicalSpace M] (U : Opens M) : BorelSpace U := ⟨rfl⟩

open private ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

/-- Equality of intrinsic and ambient small-ball volumes, with an explicit compact buffer. -/
theorem ballVolume_restrictOpen_of_buffer_CX8
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Opens M) (x : U)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hsub : riemannianClosedBallOf g (x : M) R ⊆ U) :
    ballVolume (g.restrictOpen U) x r = ballVolume g (x : M) r := by
  have hcompact := ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen g U x R hsub
  have himage := image_riemannianBallOf_localPullMetric g (Subtype.val : U → M)
    (isLocalDiffeomorph_subtype_val U) Subtype.val_injective x hr hrR
    (by simpa only [localPullMetric_subtype_val] using hcompact)
  have hmeas : MeasurableSet (riemannianBallOf (g.restrictOpen U) x r) :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ x) continuous_const).measurableSet
  have hvol := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (g.restrictOpen U) g (Subtype.val : U → M) (isLocalDiffeomorph_subtype_val U)
    Subtype.val_injective (fun y v w => by simp only [SmoothRiemannianMetric.restrictOpen_inner,
      mfderiv_subtype_val_apply]) hmeas
  simp only [localPullMetric_subtype_val] at himage
  rw [himage] at hvol
  exact hvol

/-- The original seed gives uniform small-ball volume in the intrinsic survivor metric. -/
theorem seed_volume_on_open_ball_CX8 (v : ℝ) (hv : 0 < v) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
        (g : SmoothRiemannianMetric ThreeModel M) (p : M) {a b : ℝ},
        0 < b → b ≤ a →
        (∀ q ∈ riemannianBallOf g p a, SectionalBoundedBelowAt g q (-(a ^ 2)⁻¹)) →
        ENNReal.ofReal (v * a ^ 3) ≤ ballVolume g p a →
        ∀ (U : Opens M), (U : Set M) = riemannianBallOf g p (2 * b) →
        ∀ hp : p ∈ U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ b / 16 →
        ∀ x ∈ riemannianClosedBallOf (g.restrictOpen U) ⟨p, hp⟩ ρ,
          ENNReal.ofReal (κ * ρ ^ 3) ≤ ballVolume (g.restrictOpen U) x ρ := by
  obtain ⟨κ, hκ, hvol⟩ := local_volume_of_volume_test_O3.{u} v hv
  refine ⟨κ, hκ, ?_⟩
  intro M _ _ _ _ _ g p a b hb hba hsec hseed U hU hp ρ hρ hρb x hx
  have ha : 0 < a := hb.trans_le hba
  have hpx : riemannianEDistOf g p (x : M) ≤ ENNReal.ofReal ρ :=
    (riemannianEDistOf_le_restrictOpen g U ⟨p, hp⟩ x).trans hx
  have hρa : ρ < a / 8 := by linarith
  have hpx' : riemannianEDistOf g p (x : M) < ENNReal.ofReal (a / 8) :=
    hpx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hρa)
  have hpp : p ∈ riemannianBallOf g p (a / 8) := by
    change riemannianEDistOf g p p < ENNReal.ofReal (a / 8)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hsub : riemannianClosedBallOf g (x : M) b ⊆ U := by
    intro y hy
    rw [hU]
    calc riemannianEDistOf g p y
        ≤ riemannianEDistOf g p (x : M) + riemannianEDistOf g (x : M) y :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal ρ + ENNReal.ofReal b := add_le_add hpx hy
      _ = ENNReal.ofReal (ρ + b) := (ENNReal.ofReal_add hρ.le hb.le).symm
      _ < ENNReal.ofReal (2 * b) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  rw [ballVolume_restrictOpen_of_buffer_CX8 g U x hρ (by linarith : ρ < b) hsub]
  have h := hvol M g p a ha hsec hseed p hpp x hpx' ρ hρ hρa.le
  simpa only [ballVolume, ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_pow hρ.le] using h

end GC.LongTime.Ch12
