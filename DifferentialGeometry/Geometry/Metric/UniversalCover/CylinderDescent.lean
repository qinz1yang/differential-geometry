import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Topology.Covering.SimplyConnected
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderCoverDescentSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

theorem cylinderCover_projection_mfderiv
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (p : SphereTwo × ℝ) (v : TangentSpace CylinderI p) :
    mfderiv CylinderI I (fun q : SphereTwo × ℝ => UniversalCover.proj (Psi q)) p v =
      mfderiv CylinderI I Psi p v := by
  change mfderiv CylinderI I
    ((UniversalCover.proj : UniversalCover M → M) ∘ Psi) p v = _
  rw [mfderiv_comp_apply p
    (UniversalCover.hasMFDerivAt_proj (I := I) (Psi p)).mdifferentiableAt
    (Psi.mdifferentiable (by decide) p) v,
    (UniversalCover.hasMFDerivAt_proj (I := I) (Psi p)).mfderiv]
  rfl

theorem cylinderCover_projection_inner (g : SmoothRiemannianMetric I M)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (p : SphereTwo × ℝ) (v w : TangentSpace CylinderI p) :
    g.inner (UniversalCover.proj (Psi p))
        (mfderiv CylinderI I (fun q : SphereTwo × ℝ => UniversalCover.proj (Psi q)) p v)
        (mfderiv CylinderI I (fun q : SphereTwo × ℝ => UniversalCover.proj (Psi q)) p w) =
      (UniversalCover.liftedMetric (I := I) g).inner (Psi p)
        (mfderiv CylinderI I Psi p v) (mfderiv CylinderI I Psi p w) := by
  rw [cylinderCover_projection_mfderiv, cylinderCover_projection_mfderiv]
  rfl

variable [FiniteDimensional ℝ E] [I.Boundaryless]

theorem cylinderCover_exists_diffeomorph_of_injective
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hinjective : Function.Injective
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p)))
    (hsurjective : Function.Surjective
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p))) :
    ∃ d : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ M,
      ∀ p : SphereTwo × ℝ, d p = UniversalCover.proj (Psi p) := by
  have hlocal : IsLocalDiffeomorph CylinderI I ∞
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p)) :=
    isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I) (M := M))
      Psi.isLocalDiffeomorph
  exact ⟨hlocal.diffeomorphOfBijective ⟨hinjective, hsurjective⟩, fun _ => rfl⟩

theorem cylinderCover_exists_fixed_metric_diffeomorph
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b)
    (hinjective : Function.Injective
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p)))
    (hsurjective : Function.Surjective
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p))) :
    ∃ d : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ M,
      (∀ p : SphereTwo × ℝ, d p = UniversalCover.proj (Psi p)) ∧
      ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (g t).inner (d (x, s))
            (mfderiv CylinderI I d (x, s) (v, a))
            (mfderiv CylinderI I d (x, s) (w, b)) =
          (2 * (T - t)) * (sphereMetric).inner x v w + a * b := by
  obtain ⟨d, hd⟩ := cylinderCover_exists_diffeomorph_of_injective Psi hinjective hsurjective
  refine ⟨d, hd, ?_⟩
  have hfun : (d : SphereTwo × ℝ → M) =
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p)) := funext hd
  intro t ht x s v w a b
  rw [hfun]
  exact (cylinderCover_projection_inner (g t) Psi (x, s) (v, a) (w, b)).trans
    (hproduct t ht x s v w a b)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem cylinderCover_projection_bijective_of_simplyConnected [SimplyConnectedSpace M]
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M) :
    Function.Bijective (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p)) :=
  (UniversalCover.proj_isCoveringMap (X := M)).bijective_sc.comp Psi.bijective

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
