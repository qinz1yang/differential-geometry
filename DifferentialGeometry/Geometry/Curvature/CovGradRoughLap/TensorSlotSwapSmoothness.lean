import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.TensorSlotSwap
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSSectionCalculus
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
omit [T2Space M] in
private theorem tangentBilinFlip_curry_apply_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI := tensorRSBundle_topology (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_vector (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun z : M => TensorRSSpace r (t + 2) I z)⟯)
      (Yv Yu : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r t I z) x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x) (Yu x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv Yu
  have hA :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r (t + 1)).comp Z.contMDiff
  have h1 := ContMDiff.clm_bundle_apply (b := id) hA Yu.contMDiff
  have h2 :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r t).comp h1
  have h3 := ContMDiff.clm_bundle_apply (b := id) h2 Yv.contMDiff
  refine h3.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem tangentBilinFlip_curry_apply_contMDiff (r t : ℕ)
    :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundle_topology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_fiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun z : M => TensorRSSpace r (t + 2) I z)⟯)
      (Yv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r t I z) x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r t I z)
    (φ := fun x => tangentBilinFlip (I := I) (M := M)
      (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))
  intro Yu
  exact tangentBilinFlip_curry_apply_apply_contMDiff (I := I) (M := M) r t Z Yv Yu

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem swapTwoCurryFib_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundle_topology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_fiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun x : M => TensorRSSpace r (t + 2) I x)⟯)
      (Yv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 1) I z) x
        (swapTwoCurryFib (I := I) (M := M) r t x (Z x) (Yv x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv
  have hflip := tangentBilinFlip_curry_apply_contMDiff (I := I) (M := M) r t Z Yv
  letI : NormedAddCommGroup (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 1)
  letI : NormedSpace ℝ (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedSpace r (t + 1)
  letI := tensorRSBundle_topology (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_vector (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 1)
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
      ((covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph ∘
        (fun x : M => (⟨x, tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x)⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r t ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r t I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph.contMDiff.comp hflip
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r t x
      (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x)),
    swapTwoCurryFib_apply (I := I) (M := M) r t x (Z x) (Yv x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem swapTwoCurryFib_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundle_topology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_fiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
      (fun x : M => TensorRSSpace r (t + 2) I x)⟯,
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r (t + 1) I z) x
        (swapTwoCurryFib (I := I) (M := M) r t x (Z x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r (t + 1) I z)
    (φ := fun x => swapTwoCurryFib (I := I) (M := M) r t x (Z x))
  intro Yv
  exact swapTwoCurryFib_apply_contMDiff (I := I) (M := M) r t Z Yv

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
omit [T2Space M] in
private lemma swapTwoFib_fromCurry (r t : ℕ) (x : M)
    (T : TensorRSSpace r (t + 2) I x) :
    covGradBundleEquiv (I := I) (M := M) r (t + 1) x
        (swapTwoCurryFib (I := I) (M := M) r t x T) =
      swapTwoFib (I := I) (M := M) r t x T :=
  (swapTwoFib_apply (I := I) (M := M) r t x T).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem swapTwoFib_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI := tensorRSBundle_topology (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_vector (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 2)
    ∀ Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
      (fun x : M => TensorRSSpace r (t + 2) I x)⟯,
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z) x
        (swapTwoFib (I := I) (M := M) r t x (Z x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z
  have hΨ := swapTwoCurryFib_contMDiff (I := I) (M := M) r t Z
  letI : NormedAddCommGroup (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 1)
  letI : NormedSpace ℝ (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedSpace r (t + 1)
  letI := tensorRSBundle_topology (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_vector (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 1)
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E)) ∞
      ((covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph ∘
        (fun x : M => (⟨x,
          swapTwoCurryFib (I := I) (M := M) r t x (Z x)⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r (t + 1) I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph.contMDiff.comp hΨ
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r (t + 1) x _]
  exact congrArg (TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E) x)
    (swapTwoFib_fromCurry (I := I) (M := M) r t x (Z x))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem swapTwoFib_contMDiff (r t : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r (t + 2) I z) x
        (swapTwoFib (I := I) (M := M) r t x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (t + 2) I z)
    (V₂ := fun z : M => TensorRSSpace r (t + 2) I z)
    (φ := fun x => swapTwoFib (I := I) (M := M) r t x)
  intro Z
  exact swapTwoFib_apply_contMDiff (I := I) (M := M) r t Z

set_option backward.isDefEq.respectTransparency false in

noncomputable def swapTwoSec (r t : ℕ) :
    HomTensorRSField (E := E) (M := M) r (t + 2) (t + 2) I where
  toFun := fun x : M => swapTwoFib (I := I) (M := M) r t x
  contMDiff_toFun := swapTwoFib_contMDiff (I := I) (M := M) r t

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
lemma swapTwoSec_apply (r t : ℕ) (x : M) :
    (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
      swapTwoSec (I := I) (M := M) (E := E) r t x) = swapTwoFib (I := I) (M := M) r t x := rfl

end Curvature
end Geometry
end DifferentialGeometry
