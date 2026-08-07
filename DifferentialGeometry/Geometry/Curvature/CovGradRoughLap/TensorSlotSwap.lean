import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.SecondCovGradEvaluation
open DifferentialGeometry.Geometry.Curvature



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

private noncomputable def chooseCcThrough (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M)
    (T : TensorRSSpace r a I x) : SmoothCcTensor g r a where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
      Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
    letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
      (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma chooseCcThrough_eq (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M)
    (T : TensorRSSpace r a I x) :
    (chooseCcThrough (I := I) (M := M) g r a x T).toSection x = T :=
  letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
  letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
    (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x T)

set_option backward.isDefEq.respectTransparency false in

noncomputable def curryLastTwoTensorSlots (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x :=
  (((covGradBundleEquiv (I := I) (M := M) r t x).symm :
      TensorRSSpace r (t + 1) I x ≃L[ℝ] (TangentSpace I x →L[ℝ] TensorRSSpace r t I x))
        : TensorRSSpace r (t + 1) I x →L[ℝ] (TangentSpace I x →L[ℝ] TensorRSSpace r t I x)).comp
    ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma twoSlotPeel_eval (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x)
    (u w : TangentSpace I x) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          curryLastTwoTensorSlots (I := I) (M := M) r t x T u w) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
        (Fin.cons u (Fin.cons w m)) := by
  have h1 : curryLastTwoTensorSlots (I := I) (M := M) r t x T u w =
      (covGradBundleEquiv (I := I) (M := M) r t x).symm
        ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T u) w := by
    rw [curryLastTwoTensorSlots, ContinuousLinearMap.comp_apply]
    rfl
  rw [h1]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r t x
    ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T u) w D m]
  exact covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r (t + 1) x T u D (Fin.cons w m)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma twoSlotPeel_add (r t : ℕ) (x : M) (T T' : TensorRSSpace r (t + 2) I x) :
    curryLastTwoTensorSlots (I := I) (M := M) r t x (T + T') =
      curryLastTwoTensorSlots (I := I) (M := M) r t x T + curryLastTwoTensorSlots (I := I) (M := M)
        r t x T' := by
  rw [curryLastTwoTensorSlots, curryLastTwoTensorSlots, curryLastTwoTensorSlots,
    map_add ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm) T T',
    ContinuousLinearMap.comp_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma twoSlotPeel_smul (r t : ℕ) (x : M) (c : ℝ) (T : TensorRSSpace r (t + 2) I x) :
    curryLastTwoTensorSlots (I := I) (M := M) r t x (c • T) =
      c • curryLastTwoTensorSlots (I := I) (M := M) r t x T := by
  rw [curryLastTwoTensorSlots, curryLastTwoTensorSlots,
    map_smul ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm) c T,
    ContinuousLinearMap.comp_smul]



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[reducible] def tangentSpaceFiniteDimensional {x : M} :
    FiniteDimensional ℝ (TangentSpace I x) := by
  unfold TangentSpace
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
@[reducible] def tangentSpaceT2 {x : M} : T2Space (TangentSpace I x) := by
  unfold TangentSpace
  infer_instance

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[reducible] def tensorRSSpaceFiniteDimensional {r t : ℕ} {x : M} :
    FiniteDimensional ℝ (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
@[reducible] def tensorRSSpaceT2 {r t : ℕ} {x : M} : T2Space (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  infer_instance

set_option backward.isDefEq.respectTransparency true in

noncomputable def tangentBilinFlip {r t : ℕ} {x : M}
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    tangentSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TangentSpace I x) := tangentSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun a => LinearMap.toContinuousLinearMap
        { toFun := fun b => P b a
          map_add' := fun b b' => by rw [map_add, ContinuousLinearMap.add_apply]
          map_smul' := fun c b => by rw [map_smul, ContinuousLinearMap.smul_apply]; rfl }
      map_add' := fun a a' => by
        refine ContinuousLinearMap.ext (fun b => ?_)
        change P b (a + a') = _
        rw [map_add (P b), ContinuousLinearMap.add_apply]
        rfl
      map_smul' := fun c a => by
        refine ContinuousLinearMap.ext (fun b => ?_)
        change P b (c • a) = _
        rw [map_smul (P b), ContinuousLinearMap.smul_apply]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma tangentBilinFlip_apply {r t : ℕ} {x : M}
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x)
    (a b : TangentSpace I x) :
    tangentBilinFlip (I := I) (M := M) P a b = P b a := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma tangentBilinFlip_add {r t : ℕ} {x : M}
    (P P' : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    tangentBilinFlip (I := I) (M := M) (P + P') =
      tangentBilinFlip (I := I) (M := M) P + tangentBilinFlip (I := I) (M := M) P' := by
  refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
  have h1 : tangentBilinFlip (I := I) (M := M) (P + P') a b = (P + P') b a :=
    tangentBilinFlip_apply (P + P') a b
  have h2 : ((tangentBilinFlip (I := I) (M := M) P +
      tangentBilinFlip (I := I) (M := M) P') a) b = P b a + P' b a := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      tangentBilinFlip_apply, tangentBilinFlip_apply]
  rw [h1, h2, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma tangentBilinFlip_smul {r t : ℕ} {x : M} (c : ℝ)
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    tangentBilinFlip (I := I) (M := M) (c • P) =
      c • tangentBilinFlip (I := I) (M := M) P := by
  refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
  have h1 : tangentBilinFlip (I := I) (M := M) (c • P) a b = (c • P) b a :=
    tangentBilinFlip_apply (c • P) a b
  have h2 : ((c • tangentBilinFlip (I := I) (M := M) P) a) b = c • P b a := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      tangentBilinFlip_apply]
  rw [h1, h2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in

noncomputable def swapTwoCurryFib (r t : ℕ) (x : M)
    (T : TensorRSSpace r (t + 2) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace r (t + 1) I x :=
  (((covGradBundleEquiv (I := I) (M := M) r t x) :
      (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x) :
        (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
          TensorRSSpace r (t + 1) I x).comp
    (tangentBilinFlip (I := I) (M := M)
      (curryLastTwoTensorSlots (I := I) (M := M) r t x T))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma swapTwoCurryFib_apply (r t : ℕ) (x : M)
    (T : TensorRSSpace r (t + 2) I x) (v : TangentSpace I x) :
    swapTwoCurryFib (I := I) (M := M) r t x T v =
      covGradBundleEquiv (I := I) (M := M) r t x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x T) v) := rfl

set_option backward.isDefEq.respectTransparency false in

noncomputable def swapTwoFib (r t : ℕ) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun T =>
        covGradBundleEquiv (I := I) (M := M) r (t + 1) x
          (swapTwoCurryFib (I := I) (M := M) r t x T)
      map_add' := fun T T' => by
        rw [swapTwoCurryFib, swapTwoCurryFib, swapTwoCurryFib,
          twoSlotPeel_add, tangentBilinFlip_add, ContinuousLinearMap.comp_add,
          map_add (covGradBundleEquiv (I := I) (M := M) r (t + 1) x)]
      map_smul' := fun c T => by
        rw [swapTwoCurryFib, swapTwoCurryFib,
          twoSlotPeel_smul, tangentBilinFlip_smul, ContinuousLinearMap.comp_smul,
          map_smul (covGradBundleEquiv (I := I) (M := M) r (t + 1) x)]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma swapTwoFib_apply (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x) :
    swapTwoFib (I := I) (M := M) r t x T =
      covGradBundleEquiv (I := I) (M := M) r (t + 1) x
        (swapTwoCurryFib (I := I) (M := M) r t x T) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma swapTwoFib_eval (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x)
    (a b : TangentSpace I x) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
          swapTwoFib (I := I) (M := M) r t x T) D) (Fin.cons a (Fin.cons b m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
        (Fin.cons b (Fin.cons a m)) := by
  rw [swapTwoFib_apply]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r (t + 1) x _ D
    (Fin.cons a (Fin.cons b m))]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' a (Fin.cons b m)]
  rw [show swapTwoCurryFib (I := I) (M := M) r t x T a =
    covGradBundleEquiv (I := I) (M := M) r t x
      (tangentBilinFlip (I := I) (M := M) (curryLastTwoTensorSlots (I := I) (M := M) r t x T) a)
    from rfl]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r t x _ D (Fin.cons b m)]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' b m]
  rw [tangentBilinFlip_apply]
  exact twoSlotPeel_eval (I := I) (M := M) r t x T b a D m

end Curvature
end Geometry
end DifferentialGeometry
