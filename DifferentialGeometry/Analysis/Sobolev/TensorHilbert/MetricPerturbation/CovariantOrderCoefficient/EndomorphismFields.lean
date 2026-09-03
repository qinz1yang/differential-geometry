import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseMetricSlotCoefficient
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Analysis.Sobolev
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
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
def connTermEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  -(((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) (TangentSpace I x)).flip
      (metricComparisonEndomorphism (I := I) g₀ g₁ x)).comp
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connTermEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    connTermEndo (I := I) g₀ g₁ x v0 w =
      - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (metricComparisonEndomorphism (I := I) g₀ g₁ x w) v0 := by
  rw [connTermEndo, neg_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

def sharpTermEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (endoCovariantDerivative (I := I) (M := M) g₀)
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x
    - connTermEndo (I := I) g₀ g₁ x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma sharpTermEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    sharpTermEndo (I := I) g₀ g₁ x v0 w =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  rw [sharpTermEndo, sub_apply, sub_apply,
    connTermEndo_apply, endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]
  abel

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma endoCov_eq_connTerm_add_sharpTerm (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    (endoCovariantDerivative (I := I) (M := M) g₀)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x v0 =
      connTermEndo (I := I) g₀ g₁ x v0 + sharpTermEndo (I := I) g₀ g₁ x v0 := by
  apply ContinuousLinearMap.ext; intro w
  rw [add_apply, connTermEndo_apply, sharpTermEndo_apply,
    endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connTermEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (connTermEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (metricComparisonEndomorphism (I := I) g₀ g₁ x (W x)) (V0 x))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀
      (metricComparisonEndomorphism_section_contMDiff (I := I) g₀ g₁ W) V0.contMDiff
  refine (hconn.neg_section).congr (fun x => ?_)
  rw [connTermEndo_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem sharpTermEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (sharpTermEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hendo : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x (V0 x) (W x))) := by
    have hΛcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun
            (fun y : M => (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ y) (W y)) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀
          (endoApplySection_contMDiff (I := I) (M := M) (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) W))
        V0.contMDiff
    have hcovWsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀ W.contMDiff) V0.contMDiff
    have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x)
            ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x)))) :=
      endoApplySection_contMDiff (I := I) (M := M) (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)
        ⟨_, hcovWsec⟩
    refine (hΛcovW.sub_section hcovW).congr (fun x => ?_)
    rw [endoCovariantDerivative_apply (I := I) (M := M) g₀
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) W x (V0 x)]
    rfl
  refine (hendo.sub_section (connTermEndo_inner_contMDiff (I := I) g₀ g₁ V0 W)).congr (fun x => ?_)
  rw [show sharpTermEndo (I := I) g₀ g₁ x (V0 x) (W x) =
      (endoCovariantDerivative (I := I) (M := M) g₀)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x (V0 x) (W x)
      - connTermEndo (I := I) g₀ g₁ x (V0 x) (W x) from by
    rw [sharpTermEndo, sub_apply, sub_apply]]
  rfl

def connTermCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
          (connTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => connTermEndo (I := I) g₀ g₁ x)
          (connTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

def sharpTermCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
          (sharpTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => sharpTermEndo (I := I) g₀ g₁ x)
          (sharpTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma connTermCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connTermCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
        (connTermEndo (I := I) g₀ g₁ x)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma sharpTermCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpTermCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x
        (sharpTermEndo (I := I) g₀ g₁ x)) := rfl

def connTermEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
          (connTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => connTermEndo (I := I) g₀ g₁ x)
          (connTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

def sharpTermEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
          (sharpTermEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => sharpTermEndo (I := I) g₀ g₁ x)
          (sharpTermEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma connTermEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connTermEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
        (connTermEndo (I := I) g₀ g₁ x)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma sharpTermEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpTermEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x
        (sharpTermEndo (I := I) g₀ g₁ x)) := rfl

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
  Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s

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
omit [SigmaCompactSpace M] in
theorem bilinEndoCovariantDerivative_apply (g : SmoothRiemannianMetric I M)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    ((bilinEndoCovariantDerivative (I := I) (M := M) g) Term x v) (Y x) =
      (endoCovariantDerivative (I := I) (M := M) g) (fun y => (Term y) (Y y)) x v -
        (Term x) ((LeviCivita (I := I) g) (fun y => Y y) x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g) Term Y x v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem termField_inner_contMDiff
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (Term x (V0 x) (W x))) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (Term x (V0 x))) :=
    ContMDiff.clm_bundle_apply (b := id) Term.contMDiff V0.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) h1 W.contMDiff

def bilinearSlotInsertionCoefficient (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g (s + 1) (s + 1 + 1) where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Term x))
      contMDiff_toFun :=
        termSlotFib_contMDiff (I := I) (M := M) s (fun x : M => Term x)
          (fun V0 W => termField_inner_contMDiff (I := I) (M := M) Term V0 W) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] lemma termSlotEndoCc_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (bilinearSlotInsertionCoefficient (I := I) (M := M) g s Term).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Term x)) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem bilinEndoField_contMDiff
    (Term : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Term x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := fun z : M => TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] TangentSpace I z)) x
        (Term x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E →L[ℝ] E) (V₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) from
      Term x))
  intro V0
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] TangentSpace I x from Term x (V0 x)))
  intro W
  exact harm V0 W

def connTermEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => connTermEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => connTermEndo (I := I) g₀ g₁ x)
      (connTermEndo_inner_contMDiff (I := I) g₀ g₁)⟩

def sharpTermEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => sharpTermEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => sharpTermEndo (I := I) g₀ g₁ x)
      (sharpTermEndo_inner_contMDiff (I := I) g₀ g₁)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma connTermEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connTermEndoField (I := I) g₀ g₁ x = connTermEndo (I := I) g₀ g₁ x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma sharpTermEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    sharpTermEndoField (I := I) g₀ g₁ x = sharpTermEndo (I := I) g₀ g₁ x := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma connTermCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connTermCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 1
      (connTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connTermCc_toSection, termSlotEndoCc_toSection, connTermEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma sharpTermCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpTermCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 1
      (sharpTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpTermCc_toSection, termSlotEndoCc_toSection, sharpTermEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma connTermEndoCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connTermEndoCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 0
      (connTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connTermEndoCc_toSection, termSlotEndoCc_toSection, connTermEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma sharpTermEndoCc_eq_termSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpTermEndoCc (I := I) g₀ g₁ = bilinearSlotInsertionCoefficient (I := I) (M := M) g₀ 0
      (sharpTermEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpTermEndoCc_toSection, termSlotEndoCc_toSection, sharpTermEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma curry_termSlotFib_eq_slotInsert (s : ℕ) (x : M)
    (Term : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (A : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x Term A)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Term v0) A := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (s + 1) x).injective
  refine ContinuousMultilinearMap.ext (fun vt => ?_)
  change Tensor0SSpace.eval
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x Term A)) v0) vt =
    Tensor0SSpace.eval
      (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Term v0) A) vt
  rw [tensor0S_curry_apply_eval, termSlotFib_apply_eval]
  simp only [Fin.cons_zero]
  rfl

end Sobolev
end Analysis
end DifferentialGeometry

end
