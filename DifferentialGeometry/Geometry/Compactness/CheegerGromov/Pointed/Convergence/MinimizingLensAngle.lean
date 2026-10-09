import DifferentialGeometry.Geometry.Comparison.Toponogov.CompactLensAngle
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ForwardDistance

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
universe u
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
  {F : PointedRiemannianConvergenceMaps X P f}

theorem eventually_lt_comparisonAngle_of_pointed_distance_lenses
    [ConnectedSpace P.M]
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) (hsec : HasNonnegativeSectionalCurvature P.metric)
    (y p z : P.M) (u v : ∀ i, (X.obj (f i)).M) {r θ : ℝ} (hr : 0 < r)
    (hrp : r < metricDistance P.metric y p) (hrz : r < metricDistance P.metric y z)
    (hu : ∀ᶠ i in atTop,
      riemannianEDistOf (X.obj (f i)).metric (F.map i y) (u i) = ENNReal.ofReal r ∧
      metricDistance (X.obj (f i)).metric (u i) (F.map i p) =
        metricDistance (X.obj (f i)).metric (F.map i y) (F.map i p) - r)
    (hv : ∀ᶠ i in atTop,
      riemannianEDistOf (X.obj (f i)).metric (F.map i y) (v i) = ENNReal.ofReal r ∧
      metricDistance (X.obj (f i)).metric (v i) (F.map i z) =
        metricDistance (X.obj (f i)).metric (F.map i y) (F.map i z) - r)
    (hθ : θ < comparisonAngle (metricDistance P.metric y p)
      (metricDistance P.metric y z) (metricDistance P.metric p z)) :
    ∀ᶠ i in atTop, θ < comparisonAngle r r
      (metricDistance (X.obj (f i)).metric (u i) (v i)) := by
  have hfixed : IsCompact ({y, p, z} : Set P.M) := (isCompact_singleton.insert p).insert y
  obtain ⟨R, hR, hcapture⟩ := F.exists_eventually_image_compact_subset_ball C href hcomplete hfixed
  let ρ := R + r
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hfixedBall : ∀ᶠ i in atTop, ∀ x ∈ ({y, p, z} : Set P.M),
      F.map i x ∈ riemannianClosedBallOf (X.obj (f i)).metric (X.obj (f i)).basepoint ρ := by
    filter_upwards [hcapture] with i hi
    intro x hx
    exact (hi.2 ⟨x, hx, rfl⟩).trans (ENNReal.ofReal_le_ofReal (by dsimp [ρ]; linarith))
  have hsamples : ∀ᶠ i in atTop,
      u i ∈ riemannianClosedBallOf (X.obj (f i)).metric (X.obj (f i)).basepoint ρ ∧
      v i ∈ riemannianClosedBallOf (X.obj (f i)).metric (X.obj (f i)).basepoint ρ := by
    filter_upwards [hcapture, hu, hv] with i hi hui hvi
    have hcenter := hi.2 ⟨y, by simp, rfl⟩
    constructor
    · calc
        riemannianEDistOf (X.obj (f i)).metric (X.obj (f i)).basepoint (u i) ≤
            riemannianEDistOf (X.obj (f i)).metric (X.obj (f i)).basepoint (F.map i y) +
            riemannianEDistOf (X.obj (f i)).metric (F.map i y) (u i) :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal R + ENNReal.ofReal r := add_le_add hcenter hui.1.le
        _ = ENNReal.ofReal ρ := (ENNReal.ofReal_add hR.le hr.le).symm
    · calc
        riemannianEDistOf (X.obj (f i)).metric (X.obj (f i)).basepoint (v i) ≤
            riemannianEDistOf (X.obj (f i)).metric (X.obj (f i)).basepoint (F.map i y) +
            riemannianEDistOf (X.obj (f i)).metric (F.map i y) (v i) :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal R + ENNReal.ofReal r := add_le_add hcenter hvi.1.le
        _ = ENNReal.ofReal ρ := (ENNReal.ofReal_add hR.le hr.le).symm
  have hinverse : ∀ᶠ i in atTop, ∀ x ∈ ({y, p, z} : Set P.M),
      (F.partialDiffeomorph i).symm (F.map i x) = x := by
    filter_upwards [hcapture] with i hi
    exact fun x hx => (F.partialDiffeomorph i).left_inv (hi.1 hx)
  let U := fun i => (F.partialDiffeomorph i).symm (u i)
  let V := fun i => (F.partialDiffeomorph i).symm (v i)
  have hyU : Tendsto (fun i => metricDistance P.metric y (U i)) atTop (𝓝 r) := by
    have hs : Tendsto (fun i => metricDistance (X.obj (f i)).metric (F.map i y) (u i))
        atTop (𝓝 r) := tendsto_const_nhds.congr' (hu.mono fun i hi => by
      dsimp only [metricDistance]
      rw [hi.1, ENNReal.toReal_ofReal hr.le])
    have h := (tendsto_pointed_inverse_distance C href hcomplete ρ hρ
      (fun i => F.map i y) u (by
        filter_upwards [hfixedBall, hsamples] with i hi hi'
        exact ⟨hi y (by simp), hi'.1⟩) r hs).1
    exact h.congr' (hinverse.mono fun i hi => by rw [hi y (by simp)]; rfl)
  have hyV : Tendsto (fun i => metricDistance P.metric y (V i)) atTop (𝓝 r) := by
    have hs : Tendsto (fun i => metricDistance (X.obj (f i)).metric (F.map i y) (v i))
        atTop (𝓝 r) := tendsto_const_nhds.congr' (hv.mono fun i hi => by
      dsimp only [metricDistance]
      rw [hi.1, ENNReal.toReal_ofReal hr.le])
    have h := (tendsto_pointed_inverse_distance C href hcomplete ρ hρ
      (fun i => F.map i y) v (by
        filter_upwards [hfixedBall, hsamples] with i hi hi'
        exact ⟨hi y (by simp), hi'.2⟩) r hs).1
    exact h.congr' (hinverse.mono fun i hi => by rw [hi y (by simp)]; rfl)
  have hUp : Tendsto (fun i => metricDistance P.metric (U i) p)
      atTop (𝓝 (metricDistance P.metric y p - r)) := by
    have hs := (tendsto_pointed_map_distance C href hcomplete y p).sub_const r
    have hs' : Tendsto (fun i => metricDistance (X.obj (f i)).metric (u i) (F.map i p))
        atTop (𝓝 (metricDistance P.metric y p - r)) := hs.congr' (hu.mono fun _ hi => hi.2.symm)
    have h := (tendsto_pointed_inverse_distance C href hcomplete ρ hρ u
      (fun i => F.map i p) (by
        filter_upwards [hfixedBall, hsamples] with i hi hi'
        exact ⟨hi'.1, hi p (by simp)⟩) _ hs').1
    exact h.congr' (hinverse.mono fun i hi => by rw [hi p (by simp)]; rfl)
  have hVz : Tendsto (fun i => metricDistance P.metric (V i) z)
      atTop (𝓝 (metricDistance P.metric y z - r)) := by
    have hs := (tendsto_pointed_map_distance C href hcomplete y z).sub_const r
    have hs' : Tendsto (fun i => metricDistance (X.obj (f i)).metric (v i) (F.map i z))
        atTop (𝓝 (metricDistance P.metric y z - r)) := hs.congr' (hv.mono fun _ hi => hi.2.symm)
    have h := (tendsto_pointed_inverse_distance C href hcomplete ρ hρ v
      (fun i => F.map i z) (by
        filter_upwards [hfixedBall, hsamples] with i hi hi'
        exact ⟨hi'.2, hi z (by simp)⟩) _ hs').1
    exact h.congr' (hinverse.mono fun i hi => by rw [hi z (by simp)]; rfl)
  obtain ⟨hK, hmem⟩ := eventually_pointed_inverse_pair_in_compact_ball
    C href hcomplete ρ hρ u v hsamples
  have herror := (tendsto_pointed_inverse_distance_sub_source C href hcomplete ρ hρ u v hsamples).neg
  exact eventually_lt_comparisonAngle_of_compact_riemannian_distance_lenses P.metric
    ⟨MetricComplete.complete P hcomplete⟩ hsec hK y p z U V
    (fun i => metricDistance (X.obj (f i)).metric (u i) (v i)) hr hrp hrz
    (hmem.mono fun _ hi => ⟨hi.2.2.1, hi.2.2.2⟩) hyU hyV hUp hVz
    (by simpa only [neg_sub, neg_zero, metricDistance, U, V] using herror) hθ

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
