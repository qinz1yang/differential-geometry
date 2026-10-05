import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcSublevel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcAnnulus

/-!
The SAME actual original ball annulus has the native plane-sphere interval parameter domain.
Only its circle parameter is retargeted by the existing homeomorphism; all points remain original.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

def loopBallAnnulusNative (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Set.Icc (0 : ℝ) 1) : SphereCarrier.{0} :=
  loopBallAnnulus (sphereCircleHomeomorph_GARC q.1,q.2)

theorem loopBallAnnulusNative_continuous : Continuous loopBallAnnulusNative :=
  loopBallAnnulus_continuous.comp
    ((sphereCircleHomeomorph_GARC.continuous.comp continuous_fst).prodMk continuous_snd)

theorem loopBallAnnulusNative_injective : Function.Injective loopBallAnnulusNative := by
  intro q r he
  have hp := loopBallAnnulus_injective he
  apply Prod.ext
  · exact sphereCircleHomeomorph_GARC.injective (congrArg Prod.fst hp)
  · exact congrArg (fun v : Circle × Set.Icc (0 : ℝ) 1 => v.2) hp

theorem loopBallAnnulusNative_range :
    Set.range loopBallAnnulusNative = Set.range loopBallAnnulus := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨(sphereCircleHomeomorph_GARC q.1,q.2),rfl⟩
  · rintro ⟨⟨θ,t⟩,rfl⟩
    refine ⟨(sphereCircleHomeomorph_GARC.symm θ,t),?_⟩
    change loopBallAnnulus (sphereCircleHomeomorph_GARC
      (sphereCircleHomeomorph_GARC.symm θ),t) = loopBallAnnulus (θ,t)
    rw [sphereCircleHomeomorph_GARC.apply_symm_apply]

theorem loopBallAnnulusNative_projection (q : Metric.sphere
    (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1) :
    ∃ hd : loopBallAnnulusNative q ∈ loopCircleDomain,
      loopCircleProjection ⟨loopBallAnnulusNative q,hd⟩ = loopBallArcBase q.2 :=
  ⟨loopBallAnnulus_domain (sphereCircleHomeomorph_GARC q.1) q.2,
    loopBallAnnulus_projection (sphereCircleHomeomorph_GARC q.1) q.2⟩

theorem loopBallAnnulusNative_end (b : Bool) :
    loopBallAnnulusNative '' {q | q.2 = iccEnd b} =
      Set.range (fun θ : Circle => loopBallAnnulus (θ,iccEnd b)) := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    refine ⟨sphereCircleHomeomorph_GARC q.1,?_⟩
    change loopBallAnnulus (sphereCircleHomeomorph_GARC q.1,iccEnd b) =
      loopBallAnnulus (sphereCircleHomeomorph_GARC q.1,q.2)
    rw [hq]
  · rintro ⟨θ,rfl⟩
    refine ⟨(sphereCircleHomeomorph_GARC.symm θ,iccEnd b),rfl,?_⟩
    change loopBallAnnulus (sphereCircleHomeomorph_GARC
      (sphereCircleHomeomorph_GARC.symm θ),iccEnd b) = loopBallAnnulus (θ,iccEnd b)
    rw [sphereCircleHomeomorph_GARC.apply_symm_apply]

theorem loopBallAnnulus_projection_range :
    Set.range loopBallAnnulus = loopCircleLift (Set.range loopBallArcBase) := by
  ext p
  constructor
  · rintro ⟨⟨θ,t⟩,rfl⟩
    refine ⟨⟨loopBallAnnulus (θ,t),loopBallAnnulus_domain θ t⟩,?_,rfl⟩
    exact ⟨t,(loopBallAnnulus_projection θ t).symm⟩
  · rintro ⟨q,⟨t,ht⟩,he⟩
    have hf : p ∈ loopCircleLift {loopBallArcBase t} := ⟨q,ht.symm,he⟩
    rw [← loopBallAnnulus_fibre t] at hf
    obtain ⟨u,_,hup⟩ := hf
    exact ⟨u,hup⟩

theorem loopBallAnnulusNative_region (q : Metric.sphere
    (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1) :
    loopBallAnnulusNative q ∈ loopCircleRegion := by
  let θ := sphereCircleHomeomorph_GARC q.1
  refine ⟨⟨loopBallAnnulusNative q,loopBallAnnulus_domain θ q.2⟩,?_,rfl⟩
  change loopCircleProjection ⟨loopBallAnnulus (θ,q.2),loopBallAnnulus_domain θ q.2⟩
    ∈ loopCircleCornerBase
  rw [loopBallAnnulus_projection]
  exact loopBallArcBase_cornerBase q.2

end GC.GraphManifold.Assembly
