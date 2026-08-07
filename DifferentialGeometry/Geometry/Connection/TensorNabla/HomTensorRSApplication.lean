import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomTensorRSRiemannian
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[reducible] private def fullHomTangentSpaceFiniteDimensional {x : M} :
    FiniteDimensional ℝ (TangentSpace I x) :=
  Tensor0SBundle.tangentSpace_finiteDimensional x

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[reducible] private def fullHomTensorRSSpaceFiniteDimensional {r t : ℕ} {x : M} :
    FiniteDimensional ℝ (TensorRSSpace r t I x) :=
  Tensor0SBundle.tensorRSSpace_finiteDimensional r t x

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
@[reducible] private def fullHomTensorRSSpaceT2 {r t : ℕ} {x : M} :
    T2Space (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  exact ContinuousLinearMap.instT2Space

set_option backward.isDefEq.respectTransparency false in

def homTensorRSApplyFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    TensorRSSpace r c I x :=
  Ψ x (W.toSection x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem appFullRSFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        (homTensorRSApplyFib (I := I) (M := M) g r a c Ψ W x)) :=
  ContMDiff.clm_bundle_apply (b := id) hΨ W.toSection.contMDiff

set_option backward.isDefEq.respectTransparency false in

def homTensorRSApply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r c where
  toSection :=
    { toFun := fun x : M => homTensorRSApplyFib (I := I) (M := M) g r a c Ψ W x
      contMDiff_toFun := appFullRSFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
@[simp] lemma appFullRS_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) :
    (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x = Ψ x (W.toSection x) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem appFullRS_add_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W₁ W₂ : SmoothCcTensor g r a) :
    homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ (W₁ + W₂) =
      homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁ + homTensorRSApply (I := I) (M := M) g r a
        c Ψ hΨ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁ +
        homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x) =
      (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁).toSection x +
        (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection, appFullRS_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace r a I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [map_add (Ψ x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
theorem appFullRS_smul_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (k : ℝ) (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ (k • W) =
      k • homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x) =
      k • (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection]
  rw [show ((k • W).toSection x : TensorRSSpace r a I x) = k • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [map_smul (Ψ x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem appFullRSFib_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ₁ Ψ₂ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    homTensorRSApplyFib (I := I) (M := M) g r a c (fun y => Ψ₁ y + Ψ₂ y) W x =
      homTensorRSApplyFib (I := I) (M := M) g r a c Ψ₁ W x +
        homTensorRSApplyFib (I := I) (M := M) g r a c Ψ₂ W x := by
  rw [homTensorRSApplyFib, homTensorRSApplyFib, homTensorRSApplyFib, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

noncomputable def slotInsertHomTensorRSFib (_g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) :
    TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (a + 1) I x) :=
    fullHomTensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (a + 1) I x) :=
    fullHomTensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        covGradBundleEquiv (I := I) (M := M) r c x
          (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_add, map_add (covGradBundleEquiv (I := I) (M := M) r c x)]
      map_smul' := fun k D => by
        rw [map_smul (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_smul, map_smul (covGradBundleEquiv (I := I) (M := M) r c x)]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[simp] lemma slotExtendFullFib_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x) :
    slotInsertHomTensorRSFib (I := I) (M := M) g r a c x A D =
      covGradBundleEquiv (I := I) (M := M) r c x
        (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slotExtendFullFib_apply_eval (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x)
    (Dlow : Tensor0SSpace r I x) (v0 : TangentSpace I x) (vs : Fin c → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          slotInsertHomTensorRSFib (I := I) (M := M) g r a c x A D) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          A ((covGradBundleEquiv (I := I) (M := M) r a x).symm D v0)) Dlow) vs := by
  rw [slotExtendFullFib_apply (I := I) (M := M) g r a c x A D]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r c x
    (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) = vs := by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) 0 = v0 := by simp [Fin.cons_zero]
  rw [htail, hhead, ContinuousLinearMap.comp_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem slotExtendFullFib_apply_apply_contMDiff (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (a + 1)
    letI : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModel_normedSpace r (a + 1)
    letI := tensorRSBundle_topology (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_fiber (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
    ∀ (D : Cₛ^∞⟮I; TensorRSModel r (a + 1) ℝ E,
        (fun z : M => TensorRSSpace r (a + 1) I z)⟯)
      (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        ((Ψ x) ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x) (Y x)))) := by
  letI : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (a + 1)
  letI : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModel_normedSpace r (a + 1)
  letI := tensorRSBundle_topology (I := I) (M := M) r (a + 1)
  letI := tensorRSBundle_fiber (I := I) (M := M) r (a + 1)
  letI := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
  letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
  intro D Y
  have hH :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r a).comp D.contMDiff
  have hstep1 := ContMDiff.clm_bundle_apply (b := id) hH Y.contMDiff
  have hstep2 := ContMDiff.clm_bundle_apply (b := id) hΨ hstep1
  refine hstep2.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem slotExtendFullFib_apply_contMDiff (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (a + 1)
    letI : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModel_normedSpace r (a + 1)
    letI := tensorRSBundle_topology (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_fiber (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
    ∀ (D : Cₛ^∞⟮I; TensorRSModel r (a + 1) ℝ E,
      (fun z : M => TensorRSSpace r (a + 1) I z)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x
        ((Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))) := by
  letI : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (a + 1)
  letI : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModel_normedSpace r (a + 1)
  letI := tensorRSBundle_topology (I := I) (M := M) r (a + 1)
  letI := tensorRSBundle_fiber (I := I) (M := M) r (a + 1)
  letI := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
  letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
  intro D
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r c I z)
    (φ := fun x => (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))
  intro Y
  exact slotExtendFullFib_apply_apply_contMDiff (I := I) (M := M) r a c Ψ hΨ D Y

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem covGradBundleEquiv_section_contMDiff (r c : ℕ)
    (G : Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r c I x)
    (hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x (G x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (c + 1) I z) x
        (covGradBundleEquiv (I := I) (M := M) r c x (G x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (c + 1)
  letI : NormedSpace ℝ (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedSpace r (c + 1)
  letI := tensorRSBundle_topology (I := I) (M := M) r (c + 1)
  letI := tensorRSBundle_fiber (I := I) (M := M) r (c + 1)
  letI := tensorRSBundle_vector (I := I) (M := M) r (c + 1)
  letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (c + 1)
  have hcomp :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph.contMDiff.comp hG
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r c x (G x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
theorem slotExtendFullFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (a + 1) I z →L[ℝ] TensorRSSpace r (c + 1) I z) x
        (slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (a + 1) I z)
    (V₂ := fun z : M => TensorRSSpace r (c + 1) I z)
    (φ := fun x => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
  intro D
  have hG := slotExtendFullFib_apply_contMDiff (I := I) (M := M) r a c Ψ hΨ D
  have hcov := covGradBundleEquiv_section_contMDiff (I := I) (M := M) r c
    (fun x => (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x))) hG
  refine hcov.congr ?_
  intro x
  rfl

end Connection
end Geometry
end DifferentialGeometry

end
