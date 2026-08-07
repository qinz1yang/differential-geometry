import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSSectionCalculus
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[reducible] private def fullHomTensorRSSpaceFiniteDimensional {r t : ℕ} {x : M} :
    FiniteDimensional ℝ (TensorRSSpace r t I x) :=
  Tensor0SBundle.tensorRSSpace_finiteDimensional r t x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
@[reducible] private def fullHomTensorRSSpaceT2 {r t : ℕ} {x : M} :
    T2Space (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  exact ContinuousLinearMap.instT2Space

set_option backward.isDefEq.respectTransparency false in

private noncomputable def chooseSecAtFull
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    SmoothCcTensor g r a where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
      Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
    letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
      (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma chooseSecAtFull_eq
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    (chooseSecAtFull (I := I) (M := M) g r a x v).toSection x = v :=
  letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
  letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
    (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private noncomputable def valueLocalLinearHomFib
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (x : M) : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
  letI : (b : M) → NormedAddCommGroup (TensorRSSpace r a I b) := fun b =>
    Tensor0SBundle.tensorRSSpace_normedAddCommGroup r a b
  letI : (b : M) → NormedSpace ℝ (TensorRSSpace r a I b) := fun b =>
    Tensor0SBundle.tensorRSSpace_normedSpace r a b
  letI : NormedAddCommGroup (TensorRSSpace r c I x) :=
    Tensor0SBundle.tensorRSSpace_normedAddCommGroup r c x
  letI : NormedSpace ℝ (TensorRSSpace r c I x) :=
    Tensor0SBundle.tensorRSSpace_normedSpace r c x
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun v : TensorRSSpace r a I x =>
        (F (chooseSecAtFull (I := I) (M := M) g r a x v)).toSection x
      map_add' := fun v w => by
        have hsum : (chooseSecAtFull (I := I) (M := M) g r a x (v + w)).toSection x =
            (chooseSecAtFull (I := I) (M := M) g r a x v +
              chooseSecAtFull (I := I) (M := M) g r a x w).toSection x := by
          rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
            chooseSecAtFull_eq, chooseSecAtFull_eq, chooseSecAtFull_eq]
        rw [hloc _ _ x hsum, hadd]
      map_smul' := fun k v => by
        have hsm : (chooseSecAtFull (I := I) (M := M) g r a x (k • v)).toSection x =
            (k • chooseSecAtFull (I := I) (M := M) g r a x v).toSection x := by
          rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
            chooseSecAtFull_eq, chooseSecAtFull_eq]
        rw [hloc _ _ x hsm, hsmul]
        rfl }

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma valueLocalLinearHomFib_apply
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (W : SmoothCcTensor g r a) (x : M) :
    valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (W.toSection x) =
      (F W).toSection x := by
  letI : (b : M) → NormedAddCommGroup (TensorRSSpace r a I b) := fun b =>
    Tensor0SBundle.tensorRSSpace_normedAddCommGroup r a b
  letI : (b : M) → NormedSpace ℝ (TensorRSSpace r a I b) := fun b =>
    Tensor0SBundle.tensorRSSpace_normedSpace r a b
  letI : NormedAddCommGroup (TensorRSSpace r c I x) :=
    Tensor0SBundle.tensorRSSpace_normedAddCommGroup r c x
  letI : NormedSpace ℝ (TensorRSSpace r c I x) :=
    Tensor0SBundle.tensorRSSpace_normedSpace r c x
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceT2 (I := I) (M := M)
  rw [valueLocalLinearHomFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  exact hloc _ W x (chooseSecAtFull_eq (I := I) (M := M) g r a x (W.toSection x))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem valueLocalLinearHomFib_contMDiff
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x
        (valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := TensorRSModel r a ℝ E) (V₁ := fun z : M => TensorRSSpace r a I z)
    (F₂ := TensorRSModel r c ℝ E) (V₂ := fun z : M => TensorRSSpace r c I z)
    (φ := fun x => valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)
  intro Z
  set Wσ : SmoothCcTensor g r a := ⟨Z, HasCompactSupport.of_compactSpace _⟩ with hWσ
  have hpt : ∀ x : M, valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (Z x) =
      (F Wσ).toSection x := fun x =>
    valueLocalLinearHomFib_apply (I := I) (M := M) g r a c F hadd hsmul hloc Wσ x
  refine (F Wσ).toSection.contMDiff.congr ?_
  intro x
  exact (congrArg (TotalSpace.mk' (TensorRSModel r c ℝ E)
    (E := fun z : M => TensorRSSpace r c I z) x) (hpt x)).symm ▸ rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
theorem exists_value_local_appFullSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x) :
    ∃ Θ : HomTensorRSField (E := E) (M := M) r a c I,
      ∀ (W : SmoothCcTensor g r a), F W = homTensorRSFieldApply (I := I) (M := M) g r a c Θ W := by
  refine ⟨{ toFun := fun x : M =>
              valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x
            contMDiff_toFun :=
              valueLocalLinearHomFib_contMDiff (I := I) (M := M) g r a c F hadd hsmul hloc }, fun W
                => ?_⟩
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection]
  exact (valueLocalLinearHomFib_apply (I := I) (M := M) g r a c F hadd hsmul hloc W x).symm
end Connection
end Geometry
end DifferentialGeometry

end
