import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **(S1)** The buffered core map restricted to its open domain is an injective local
diffeomorphism (the hypotheses shape of `ball_subset_image_of_metric_lower_on_opens`). -/
theorem bufferedMap_localDiffeo_S35 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : B.domain i t => B.map i t ht x) ∧
      Function.Injective (fun x : B.domain i t => B.map i t ht x) := by
  have hemb := B.embedding i t ht
  refine ⟨?_, hemb.isEmbedding.injective⟩
  exact isLocalDiffeomorph_of_injective_mfderiv _ hemb.contMDiff
    (fun q => injective_mfderiv_of_isImmersionAt _ _ _ q
      (hemb.isImmersion.isImmersionAt q)) rfl

/-- **(S3)** First exit: with the C⁰ lower comparison on the closed `h`-ball of radius `R`
(inside the domain), the ambient ball of radius `R / L` about `φ y` lies in `φ` of that closed
ball. -/
theorem ambient_ball_subset_image_S35 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t)
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation t).Carrier)
    (y : (B.model i).Carrier) (hy : y ∈ B.domain i t) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsource : riemannianClosedBallOf (B.model i).metric y R ⊆ (B.domain i t : Set _))
    (hlower : ∀ x ∈ riemannianClosedBallOf (B.model i).metric y R,
      ∀ v : TangentSpace (𝓡 3) x, (B.model i).metric.inner x v v ≤
        L ^ 2 * gb.inner (B.map i t ht x) (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x v)
          (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x v)) :
    riemannianBallOf gb (B.map i t ht y) (R / L) ⊆
      B.map i t ht '' riemannianClosedBallOf (B.model i).metric y R := by
  obtain ⟨hf, hinj⟩ := bufferedMap_localDiffeo_S35 B i t ht
  have hcap := DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens gb (B.model i).metric (B.domain i t)
    (fun x : B.domain i t => B.map i t ht x) hf hinj ⟨y, hy⟩ hR hL
    ((B.model i).complete.closedEBall_isCompact y R) hsource (fun x hx v => by
      have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) (B.map i t ht) x.val :=
        ((B.smooth i t ht).mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt
          ((B.domain i t).isOpen.mem_nhds x.2)
      have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun x : B.domain i t => B.map i t ht x) x =
          (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x.val).comp
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : B.domain i t → _) x) :=
        mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) (B.domain i t) x).mdifferentiableAt
      rw [hcomp]
      simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
      exact hlower x.val hx v)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hcap hz
  exact ⟨x.val, hx, rfl⟩

end GC.LongTime.Ch12
