import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistanceError
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem tendsto_pointed_map_distance [PreconnectedSpace L.M]
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (p q : L.M) :
    Tendsto (fun k =>
      (riemannianEDistOf (I := I) (X.obj (subseq k)).metric (Φ.map k p) (Φ.map k q)).toReal)
      atTop (𝓝 (riemannianEDistOf (I := I) L.metric p q).toReal) := by
  have hcompact : IsCompact ({p, q} : Set L.M) := isCompact_singleton.insert p
  obtain ⟨rho, hrho, hcapture⟩ :=
    Φ.exists_eventually_image_compact_subset_ball C hreference hcomplete hcompact
  have hball : ∀ᶠ k in atTop,
      Φ.map k p ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho ∧
      Φ.map k q ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho := by
    filter_upwards [hcapture] with k hk
    exact ⟨hk.2 ⟨p, by simp, rfl⟩, hk.2 ⟨q, by simp, rfl⟩⟩
  have herror := tendsto_pointed_inverse_distance_sub_source C hreference hcomplete
    rho hrho.le (fun k => Φ.map k p) (fun k => Φ.map k q) hball
  have hinverse : ∀ᶠ k in atTop,
      (Φ.partialDiffeomorph k).symm (Φ.map k p) = p ∧
      (Φ.partialDiffeomorph k).symm (Φ.map k q) = q := by
    filter_upwards [hcapture] with k hk
    exact ⟨(Φ.partialDiffeomorph k).left_inv (hk.1 (by simp)),
      (Φ.partialDiffeomorph k).left_inv (hk.1 (by simp))⟩
  have hconstant : Tendsto (fun k =>
      (riemannianEDistOf (I := I) L.metric p q).toReal -
      (riemannianEDistOf (I := I) (X.obj (subseq k)).metric (Φ.map k p) (Φ.map k q)).toReal)
      atTop (𝓝 0) := herror.congr' (hinverse.mono fun k hk => by rw [hk.1, hk.2])
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds (x := (riemannianEDistOf (I := I) L.metric p q).toReal)).sub hconstant

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
