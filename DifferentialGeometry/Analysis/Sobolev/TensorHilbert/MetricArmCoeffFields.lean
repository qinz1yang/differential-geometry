import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricInverseDifferenceSlotCoefficient
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.TensorRSNabla
open DifferentialGeometry.TensorMultilinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
def connArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  -(((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) (TangentSpace I x)).flip
      (metricComparisonEndo (I := I) g₀ g₁ x)).comp
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] in
@[simp] lemma connArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    connArmEndo (I := I) g₀ g₁ x v0 w =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x w) v0 := by
  rw [connArmEndo, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

def sharpArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (endoCovariantDerivative (I := I) (M := M) g₀)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) x
    - connArmEndo (I := I) g₀ g₁ x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    sharpArmEndo (I := I) g₀ g₁ x v0 w =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    connArmEndo_apply, endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]
  abel

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma endoCov_eq_connArm_add_sharpArm (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v0 =
      connArmEndo (I := I) g₀ g₁ x v0 + sharpArmEndo (I := I) g₀ g₁ x v0 := by
  apply ContinuousLinearMap.ext; intro w
  rw [ContinuousLinearMap.add_apply, connArmEndo_apply, sharpArmEndo_apply,
    endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem leviCivitaSection_contMDiff_aux (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  rw [← contMDiffOn_univ]
  exact LeviCivita_section_contMDiffOn_univ (I := I) g hσ'

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem connArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (connArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (W x)) (V0 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
      (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W) V0.contMDiff
  refine (hconn.neg_section).congr (fun x => ?_)
  rw [connArmEndo_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem sharpArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hendo : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x))) := by
    have hΛcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun
            (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (W y)) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀
          (endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁) W))
        V0.contMDiff
    have hcovWsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀ W.contMDiff) V0.contMDiff
    have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((gInvDiffRaisedEndoField (I := I) g₀ g₁ x)
            ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x)))) :=
      endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁)
        ⟨_, hcovWsec⟩
    refine (hΛcovW.sub_section hcovW).congr (fun x => ?_)
    rw [endoCovariantDerivative_apply (I := I) (M := M) g₀
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) W x (V0 x)]
    rfl
  refine (hendo.sub_section (connArmEndo_inner_contMDiff (I := I) g₀ g₁ V0 W)).congr (fun x => ?_)
  rw [show sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x) =
      (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x)
      - connArmEndo (I := I) g₀ g₁ x (V0 x) (W x) from by
    rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  rfl

set_option backward.isDefEq.respectTransparency false in
def connArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
          (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
          (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma connArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
        (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sharpArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
        (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
def connArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
          (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
          (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma connArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
        (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sharpArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
        (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

private local instance tangentEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x) (σ₁₂ := RingHom.id ℝ)

private local instance tangentBilinearEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x →L[ℝ] TangentSpace I x)
    (σ₁₂ := RingHom.id ℝ)

private local instance tensor0STotalSpaceTopology (s : ℕ) :
    TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s

def bilinEndoCovariantDerivative (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I (E →L[ℝ] (E →L[ℝ] E))
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

instance bilinEndoCovariantDerivative_contMDiff (g : SmoothRiemannianMetric I M) :
    (bilinEndoCovariantDerivative (I := I) (M := M) g).ContMDiffCovariantDerivative ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem bilinEndoCovariantDerivative_apply (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) (Y x) =
      (endoCovariantDerivative (I := I) (M := M) g) (fun y => (Arm y) (Y y)) x v -
        (Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g) Arm Y x v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
theorem armField_inner_contMDiff
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (Arm x (V0 x) (W x))) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (Arm x (V0 x))) :=
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff V0.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) h1 W.contMDiff

set_option backward.isDefEq.respectTransparency false in
def armSlotEndoCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g (s + 1) (s + 1 + 1) where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) s (fun x : M => Arm x)
          (fun V0 W => armField_inner_contMDiff (I := I) (M := M) Arm V0 W) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
@[simp] lemma armSlotEndoCc_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoCc (I := I) (M := M) g s Arm).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
theorem bilinEndoField_contMDiff
    (Arm : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := fun z : M => TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] TangentSpace I z)) x
        (Arm x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E →L[ℝ] E) (V₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) from
      Arm x))
  intro V0
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] TangentSpace I x from Arm x (V0 x)))
  intro W
  exact harm V0 W

def connArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => connArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => connArmEndo (I := I) g₀ g₁ x)
      (connArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

def sharpArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => sharpArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
      (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma connArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connArmEndoField (I := I) g₀ g₁ x = connArmEndo (I := I) g₀ g₁ x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma sharpArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    sharpArmEndoField (I := I) g₀ g₁ x = sharpArmEndo (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma connArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1
      (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1
      (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma connArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0
      (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmEndoCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0
      (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmEndoCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma curry_armSlotFib_eq_slotInsert (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (A : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x Arm A)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) A := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun vt => ?_)
  rw [tensor0S_curry_apply_eval, armSlotFib_apply_eval]
  simp only [Fin.cons_zero]
  rfl

end Sobolev
end Analysis
end DifferentialGeometry

end
