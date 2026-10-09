import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapTransitions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate
import DifferentialGeometry.Topology.Manifold.ClosedBall.Diffeomorph
import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Manifold.Orientation.TopForm

/-!
Signed spherical cap charts carry the original core orientation. Actual ball reflections realize
its required cap sign while keeping the standard ambient Euclidean ball orientation fixed.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance sphereCapOrientationBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance sphereCapOrientationBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private abbrev SphereCapOrientationE3 := EuclideanSpace ℝ (Fin 3)

def sphereCapEuclideanOrientation : Orientation ℝ SphereCapOrientationE3 (Fin 3) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation

private def sphereCapAmbientOrientation : ManifoldOrientation (𝓡 3) SphereCapOrientationE3 3 :=
  Classical.choose (exists_manifoldOrientation_eq_of_compatibleOrientation (𝓡 3) (by simp)
    (fun x : SphereCapOrientationE3 => sphereCapEuclideanOrientation)
    (DifferentialGeometry.Manifold.Orientation.isCompatibleOrientation_model
      sphereCapEuclideanOrientation))

private theorem sphereCapAmbientOrientation_apply (x : SphereCapOrientationE3) :
    sphereCapAmbientOrientation.orientation x = sphereCapEuclideanOrientation :=
  congrFun (Classical.choose_spec (exists_manifoldOrientation_eq_of_compatibleOrientation
    (𝓡 3) (by simp) (fun y : SphereCapOrientationE3 => sphereCapEuclideanOrientation)
    (DifferentialGeometry.Manifold.Orientation.isCompatibleOrientation_model
      sphereCapEuclideanOrientation))) x

def sphereCapBallStandardOrientation : ManifoldOrientation (𝓡∂ 3) (ClosedCell 3) 3 :=
  manifoldOrientationPullback (𝓡∂ 3) (𝓡 3) (by simp)
    (Subtype.val : ClosedCell 3 → SphereCapOrientationE3)
    (isSmoothEmbedding_closedCell_inclusion 2).contMDiff
    (closedCell_inclusion_mfderiv_bijective 2) sphereCapAmbientOrientation

theorem sphereCapBallStandardOrientation_inclusion (x : ClosedCell 3) :
    Orientation.map (Fin 3)
      (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → SphereCapOrientationE3)
        (closedCell_inclusion_mfderiv_bijective 2) x).toLinearEquiv
      (sphereCapBallStandardOrientation.orientation x) = sphereCapEuclideanOrientation :=
  (orientation_map_manifoldOrientationPullback (𝓡∂ 3) (𝓡 3) (by simp)
    (Subtype.val : ClosedCell 3 → SphereCapOrientationE3)
    (isSmoothEmbedding_closedCell_inclusion 2).contMDiff
    (closedCell_inclusion_mfderiv_bijective 2) sphereCapAmbientOrientation x).trans
      (sphereCapAmbientOrientation_apply x.val)

private def sphereCapAmbientReflection :
    SphereCapOrientationE3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ SphereCapOrientationE3 :=
  (ContinuousLinearEquiv.neg ℝ).toDiffeomorph

private theorem sphereCapAmbientReflection_ball :
    sphereCapAmbientReflection '' Metric.closedBall (0 : SphereCapOrientationE3) 1 =
      Metric.closedBall (0 : SphereCapOrientationE3) 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [sphereCapAmbientReflection, Metric.mem_closedBall, dist_zero_right] using hy
  · intro hx
    refine ⟨-x, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_zero_right] using hx
    · change - -x = x
      exact neg_neg x

def sphereCapBallReflection : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  closedCellDiffeomorph sphereCapAmbientReflection sphereCapAmbientReflection_ball

def sphereCapBoundaryReflection : ClosureSphere.{u} ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u} :=
  ((uliftDiffeomorph (𝓡 2) SphereTwo).symm.trans
    (sphereAntipodalDiffeomorph (n := 2))).trans (uliftDiffeomorph (𝓡 2) SphereTwo)

theorem sphereCapBallReflection_apply (x : ClosedCell 3) :
    (sphereCapBallReflection x).val = -x.val := rfl

theorem sphereCapBoundaryReflection_apply (z : ClosureSphere.{u}) :
    (sphereCapBoundaryReflection z).down.val = -z.down.val := rfl

theorem sphereCapBallReflection_boundary (z : ClosureSphere.{u}) :
    sphereCapBallReflection (closureSphereToBall z) =
      closureSphereToBall (sphereCapBoundaryReflection z) := by
  apply Subtype.ext
  rfl

private theorem sphereCapEuclideanNeg_map
    (o : Orientation ℝ SphereCapOrientationE3 (Fin 3)) :
    Orientation.map (Fin 3) (LinearEquiv.neg ℝ) o = -o := by
  apply (Orientation.map_eq_neg_iff_det_neg o (LinearEquiv.neg ℝ) (by simp)).mpr
  have he : (LinearEquiv.neg ℝ : SphereCapOrientationE3 ≃ₗ[ℝ] SphereCapOrientationE3).toLinearMap =
      (-1 : ℝ) • (LinearMap.id : SphereCapOrientationE3 →ₗ[ℝ] SphereCapOrientationE3) := by
    ext v
    simp
  rw [he, LinearMap.det_smul, LinearMap.det_id]
  norm_num

set_option backward.isDefEq.respectTransparency false in
theorem sphereCapBallReflection_preservesOrientation :
    sphereCapBallReflection.preservesOrientation sphereCapBallStandardOrientation
      sphereCapBallStandardOrientation.opposite := by
  intro x
  let A := fun y : ClosedCell 3 =>
    (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → SphereCapOrientationE3)
      (closedCell_inclusion_mfderiv_bijective 2) y).toLinearEquiv
  let D : SphereCapOrientationE3 ≃ₗ[ℝ] SphereCapOrientationE3 :=
    (sphereCapBallReflection.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have hc : D.trans (A (sphereCapBallReflection x)) = (A x).trans (LinearEquiv.neg ℝ) := by
    apply LinearEquiv.ext
    intro v
    have hi := (isSmoothEmbedding_closedCell_inclusion 2).contMDiff.mdifferentiableAt
      (by simp) (x := sphereCapBallReflection x)
    have hd := sphereCapBallReflection.contMDiff.mdifferentiableAt (by simp) (x := x)
    have h := mfderiv_comp_apply x hi hd v
    have hf : (Subtype.val : ClosedCell 3 → SphereCapOrientationE3) ∘ sphereCapBallReflection =
        fun y : ClosedCell 3 => -y.val := rfl
    rw [hf] at h
    have hix := (isSmoothEmbedding_closedCell_inclusion 2).contMDiff.mdifferentiableAt
      (by simp) (x := x)
    change (mfderiv (𝓡∂ 3) (𝓡 3)
      (-(Subtype.val : ClosedCell 3 → SphereCapOrientationE3)) x) v = _ at h
    rw [hix.hasMFDerivAt.neg.mfderiv] at h
    exact h.symm
  apply (Orientation.map (Fin 3) (A (sphereCapBallReflection x))).injective
  change Orientation.map (Fin 3) (A (sphereCapBallReflection x))
    (Orientation.map (Fin 3) D (sphereCapBallStandardOrientation.orientation x)) =
      Orientation.map (Fin 3) (A (sphereCapBallReflection x))
        (-sphereCapBallStandardOrientation.orientation (sphereCapBallReflection x))
  rw [← DifferentialGeometry.orientation_map_trans, hc,
    DifferentialGeometry.orientation_map_trans, sphereCapBallStandardOrientation_inclusion,
    sphereCapEuclideanNeg_map, Orientation.map_neg, sphereCapBallStandardOrientation_inclusion]

def sphereCapSignedReferenceOrientation :
    ManifoldOrientation sphereSignedCollarModel (ClosureSphere.{u} × ℝ) 3 :=
  productOrientation (𝓡 2) 𝓘(ℝ, ℝ) (by norm_num) (by norm_num)
    (uliftOrientation (𝓡 2) SphereTwo (sphereOrientation 2 (by norm_num))) realLineOrientation

section PatchSigns

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

private theorem exists_sphereCapPatchPullback
    (d : PartialDiffeomorph I J M N ∞) (hdim : Module.finrank ℝ E = 3)
    (O : ManifoldOrientation J N 3) :
    ∃ P : ManifoldOrientation I (⟨d.source, d.open_source⟩ : Opens M) 3,
      ∀ p, Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d p.property)
        (P.orientation p) = O.orientation (d p.val) := by
  let U : Opens M := ⟨d.source, d.open_source⟩
  have hs : ContMDiff I J ∞ (fun p : U => d p.val) := by
    intro p
    rw [contMDiffAt_subtype_iff]
    exact d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds p.property)
  have hb : ∀ p : U, Bijective (mfderiv I J (fun q : U => d q.val) p) := by
    intro p
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact (carrierSurgeryPatchTangentEquiv d p.property).bijective
  obtain ⟨P, hp⟩ := exists_manifoldOrientation_pullback I J hdim (fun p : U => d p.val) hs hb O
  refine ⟨P, fun p => ?_⟩
  have he : (differentialEquivOfBijective I J (fun q : U => d q.val) hb p).toLinearEquiv =
      carrierSurgeryPatchTangentEquiv d p.property := by
    ext v
    change mfderiv I J (fun q : U => d q.val) p v = mfderiv I J d p.val v
    rw [DifferentialGeometry.mfderiv_restrict_open]
    rfl
  rw [← he]
  exact hp p

private theorem exists_sphereCapPatchSourceSign
    (d : PartialDiffeomorph I J M N ∞) (OS : ManifoldOrientation I M 3)
    (ON : ManifoldOrientation J N 3) (hpre : IsPreconnected d.source)
    (p0 : (⟨d.source, d.open_source⟩ : Opens M)) :
    ∃ O : ManifoldOrientation I M 3, (O = OS ∨ O = OS.opposite) ∧
      ∀ (p : M) (hp : p ∈ d.source),
        Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp)
        (O.orientation p) = ON.orientation (d p) := by
  let U : Opens M := ⟨d.source, d.open_source⟩
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hpre
  obtain ⟨P, hP⟩ := exists_sphereCapPatchPullback d OS.dimension_eq ON
  have hc : Fintype.card (Fin 3) = Module.finrank ℝ E := by
    simpa using OS.dimension_eq.symm
  rcases Orientation.eq_or_eq_neg (P.orientation p0) (OS.orientation p0.val) hc with hp | hp
  · have he : P = OS.restrictOpen U := ManifoldOrientation.eq_of_eq_at P
      (OS.restrictOpen U) p0 hp
    refine ⟨OS, Or.inl rfl, fun p hp => ?_⟩
    have h := hP ⟨p, hp⟩
    rw [he] at h
    exact h
  · have he : P = (OS.restrictOpen U).opposite := ManifoldOrientation.eq_of_eq_at P
      (OS.restrictOpen U).opposite p0 hp
    refine ⟨OS.opposite, Or.inr rfl, fun p hp => ?_⟩
    have h := hP ⟨p, hp⟩
    rw [he] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
private theorem exists_sphereCapPatchTargetSign
    (d : PartialDiffeomorph I J M N ∞) (OS : ManifoldOrientation I M 3)
    (ON : ManifoldOrientation J N 3) (hpre : IsPreconnected d.source)
    (p0 : (⟨d.source, d.open_source⟩ : Opens M)) :
    ∃ O : ManifoldOrientation J N 3, (O = ON ∨ O = ON.opposite) ∧
      ∀ (p : M) (hp : p ∈ d.source),
        Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp)
        (OS.orientation p) = O.orientation (d p) := by
  let U : Opens M := ⟨d.source, d.open_source⟩
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hpre
  obtain ⟨P, hP⟩ := exists_sphereCapPatchPullback d OS.dimension_eq ON
  have hc : Fintype.card (Fin 3) = Module.finrank ℝ E := by
    simpa using OS.dimension_eq.symm
  rcases Orientation.eq_or_eq_neg (P.orientation p0) (OS.orientation p0.val) hc with hp | hp
  · have he : P = OS.restrictOpen U := ManifoldOrientation.eq_of_eq_at P
      (OS.restrictOpen U) p0 hp
    refine ⟨ON, Or.inl rfl, fun p hp => ?_⟩
    have h := hP ⟨p, hp⟩
    rw [he] at h
    exact h
  · have he : P = (OS.restrictOpen U).opposite := ManifoldOrientation.eq_of_eq_at P
      (OS.restrictOpen U).opposite p0 hp
    refine ⟨ON.opposite, Or.inr rfl, fun p hp => ?_⟩
    have h := hP ⟨p, hp⟩
    change Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp)
      (P.orientation ⟨p, hp⟩) = ON.orientation (d p) at h
    rw [he, ManifoldOrientation.opposite_orientation,
      ManifoldOrientation.restrictOpen_orientation, Orientation.map_neg] at h
    exact (neg_neg (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hp)
      (OS.orientation p))).symm.trans (congrArg Neg.neg h)

end PatchSigns

local instance sphereCapOrientationSpherePreconnected : PreconnectedSpace ClosureSphere.{u} := by
  let : PreconnectedSpace SphereTwo := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1)
  infer_instance

namespace MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

private theorem sphereCapCoreTransition_preconnected (i : Fin B.sphereCount) :
    IsPreconnected (B.sphereCapCoreTransition i).source := by
  rw [B.sphereCapCoreTransition_source]
  exact isPreconnected_univ.prod isPreconnected_Ioo

private theorem sphereCapBallTransition_preconnected :
    IsPreconnected sphereCapBallTransition.{u}.source := by
  rw [sphereCapBallTransition_source]
  exact isPreconnected_univ.prod isPreconnected_Ioo

theorem exists_sphereCapOrientations (i : Fin B.sphereCount) :
    ∃ O : ManifoldOrientation sphereSignedCollarModel (ClosureSphere.{u} × ℝ) 3,
    ∃ V : ManifoldOrientation (𝓡∂ 3) (ClosedCell 3) 3,
    ∃ D : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3,
    ∃ A : ClosureSphere.{u} ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u},
      ((D = Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞ ∧
        A = Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞) ∨
       (D = sphereCapBallReflection ∧ A = sphereCapBoundaryReflection)) ∧
      (∀ z, D (closureSphereToBall z) = closureSphereToBall (A z)) ∧
      D.preservesOrientation sphereCapBallStandardOrientation V ∧
      (∀ (p : ClosureSphere.{u} × ℝ) (hp : p ∈ (B.sphereCapCoreTransition i).source),
        Orientation.map (Fin 3)
          (carrierSurgeryPatchTangentEquiv (B.sphereCapCoreTransition i) hp)
          (O.orientation p) = C.orientation.orientation (B.sphereCapCoreTransition i p)) ∧
      (∀ (p : ClosureSphere.{u} × ℝ) (hp : p ∈ sphereCapBallTransition.source),
        Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv sphereCapBallTransition hp)
          (O.orientation p) = V.orientation (sphereCapBallTransition p)) := by
  let z : ClosureSphere.{u} := Classical.choice inferInstance
  have hcore0 : (z, (1 / 2 : ℝ)) ∈ (B.sphereCapCoreTransition i).source := by
    rw [B.sphereCapCoreTransition_source]
    constructor <;> norm_num
  have hball0 : (z, (-1 / 2 : ℝ)) ∈ sphereCapBallTransition.source := by
    rw [sphereCapBallTransition_source]
    constructor <;> norm_num
  obtain ⟨O, hO, hcore⟩ := exists_sphereCapPatchSourceSign (B.sphereCapCoreTransition i)
    sphereCapSignedReferenceOrientation C.orientation (B.sphereCapCoreTransition_preconnected i)
      ⟨(z, 1 / 2), hcore0⟩
  obtain ⟨V, hV, hball⟩ := exists_sphereCapPatchTargetSign sphereCapBallTransition O
    sphereCapBallStandardOrientation sphereCapBallTransition_preconnected ⟨(z, -1 / 2), hball0⟩
  rcases hV with hpos | hneg
  · subst V
    exact ⟨O, sphereCapBallStandardOrientation, Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞,
      Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞, Or.inl ⟨rfl, rfl⟩, fun z => rfl,
      Diffeomorph.preservesOrientation_refl sphereCapBallStandardOrientation, hcore, hball⟩
  · subst V
    exact ⟨O, sphereCapBallStandardOrientation.opposite, sphereCapBallReflection,
      sphereCapBoundaryReflection, Or.inr ⟨rfl, rfl⟩, sphereCapBallReflection_boundary,
      sphereCapBallReflection_preservesOrientation, hcore, hball⟩

end MixedBoundaryCertificate

end GC.GraphManifold
