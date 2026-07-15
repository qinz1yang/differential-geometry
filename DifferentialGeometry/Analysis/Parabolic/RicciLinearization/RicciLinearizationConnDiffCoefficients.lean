import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Tensor.Multilinear.ModelProductContinuousBilinear

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def permOfImages {n : ℕ} (f g : Fin n → Fin n)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Equiv.Perm (Fin n) :=
  ⟨f, g, h₁, h₂⟩

private def perm2_10 : Equiv.Perm (Fin 2) :=
  permOfImages ![1, 0] ![1, 0] (by decide) (by decide)

private def perm3_102 : Equiv.Perm (Fin 3) :=
  permOfImages ![1, 0, 2] ![1, 0, 2] (by decide) (by decide)

private def perm3_120 : Equiv.Perm (Fin 3) :=
  permOfImages ![1, 2, 0] ![2, 0, 1] (by decide) (by decide)

private def perm4_0312 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 3, 1, 2] ![0, 2, 3, 1] (by decide) (by decide)

private def perm4_0213 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 2, 1, 3] ![0, 2, 1, 3] (by decide) (by decide)

private def perm4_2301 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide)

private def perm4_1302 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 3, 0, 2] ![2, 0, 3, 1] (by decide) (by decide)

private def perm4_1203 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 2, 0, 3] ![2, 0, 1, 3] (by decide) (by decide)

private def perm4_3012 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 0, 1, 2] ![1, 2, 3, 0] (by decide) (by decide)

private def perm4_2013 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 0, 1, 3] ![1, 2, 0, 3] (by decide) (by decide)

private def perm4_3201 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 2, 0, 1] ![2, 3, 1, 0] (by decide) (by decide)

private def perm4_3102 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 1, 0, 2] ![2, 1, 3, 0] (by decide) (by decide)

private def perm4_2103 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 1, 0, 3] ![2, 1, 0, 3] (by decide) (by decide)

private def perm4_0231 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 2, 3, 1] ![0, 3, 1, 2] (by decide) (by decide)

private def perm4_0321 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 3, 2, 1] ![0, 3, 2, 1] (by decide) (by decide)

noncomputable def slotPermCLM {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x : M) :
    Tensor0SBundle.Tensor0SSpace d I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          ρ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem slotPermCLM_apply {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace d I x) :
    slotPermCLM (I := I) ρ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [slotPermCLM]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def tensorProdWithCLM (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) :
    Tensor0SBundle.Tensor0SSpace k I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (m + k) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I)
      (m + k) x).symm.toContinuousLinearMap.comp
    ((Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        (Tensor0SBundle.Tensor0SSpace.toModel P)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) k x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem tensorProdWithCLM_apply (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) (Q : Tensor0SBundle.Tensor0SSpace k I x) :
    tensorProdWithCLM (I := I) m k x P Q =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
          (Tensor0SBundle.Tensor0SSpace.toModel P)
          (Tensor0SBundle.Tensor0SSpace.toModel Q)) := by
  rw [tensorProdWithCLM]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Bundle.continuousMultilinearMap.modelProductL_apply]
  rfl

noncomputable def tensorProdPairCLM (m k : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace m I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace k I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (m + k) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.Tensor0SSpace m I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun P => tensorProdWithCLM (I := I) m k x P
      map_add' := fun P₁ P₂ => by
        apply ContinuousLinearMap.ext
        intro Q
        have hsplit : Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
            (Tensor0SBundle.Tensor0SSpace.toModel P₁ + Tensor0SBundle.Tensor0SSpace.toModel P₂)
            (Tensor0SBundle.Tensor0SSpace.toModel Q) =
          Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P₁) (Tensor0SBundle.Tensor0SSpace.toModel Q)
            + Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P₂)
              (Tensor0SBundle.Tensor0SSpace.toModel Q) := by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.add_apply, add_mul]
        rw [ContinuousLinearMap.add_apply, tensorProdWithCLM_apply, tensorProdWithCLM_apply,
          tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_add, hsplit]
        exact map_add
          ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (m + k) x).symm) _ _
      map_smul' := fun c P => by
        apply ContinuousLinearMap.ext
        intro Q
        have hsplit : Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
            (c • Tensor0SBundle.Tensor0SSpace.toModel P)
            (Tensor0SBundle.Tensor0SSpace.toModel Q) =
          c • Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P)
              (Tensor0SBundle.Tensor0SSpace.toModel Q) := by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.smul_apply, smul_eq_mul]
          ring
        rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, tensorProdWithCLM_apply,
          tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul, hsplit]
        exact map_smul
          ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (m + k) x).symm) c _ }

set_option linter.unusedSectionVars false in

@[simp] theorem tensorProdPairCLM_apply (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) :
    tensorProdPairCLM (I := I) m k x P = tensorProdWithCLM (I := I) m k x P := rfl

noncomputable def contractUnitCLM (n : ℕ) (x : M) :
    Tensor0SBundle.TensorRSSpace 1 (n + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace n I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) n x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply ℝ (Tensor0SBundle.Tensor0SModel n ℝ E)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))).comp
      ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 n x).toContinuousLinearMap.comp
        (show Tensor0SBundle.TensorRSSpace 1 (n + 1) I x →L[ℝ]
            Tensor0SBundle.TensorRSSpace 0 n I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 n x)))

noncomputable def connContrCLM (m k : ℕ) (x : M)
    (B : Tensor0SBundle.TensorRSSpace 1 (k + 1) I x) :
    Tensor0SBundle.Tensor0SSpace (m + 1) I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace (m + 1 + k) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.Tensor0SSpace (m + 1) I x) := inferInstance
  (contractUnitCLM (I := I) (m + 1 + k) x).comp
    (LinearMap.toContinuousLinearMap
      { toFun := fun D =>
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)
        map_add' := fun D₁ D₂ => by
          simp only [← tensorProdPairCLM_apply]
          rw [map_add, ContinuousLinearMap.add_comp]
        map_smul' := fun c D => by
          simp only [← tensorProdPairCLM_apply, RingHom.id_apply]
          rw [map_smul, ContinuousLinearMap.smul_comp] })

noncomputable def linearizedRicciConnDiffOrder1CLM (x : M)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  -((slotPermCLM (I := I) perm4_0312 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_102 x))
      + (slotPermCLM (I := I) perm4_0213 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_120 x))
      + (slotPermCLM (I := I) perm4_2301 x).comp (connContrCLM (I := I) 2 1 x A)
      + (slotPermCLM (I := I) perm4_1302 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_102 x))
      + (slotPermCLM (I := I) perm4_1203 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_120 x)))

noncomputable def linearizedRicciConnDiffOrder0CLM (x : M)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x)
    (DA : Tensor0SBundle.TensorRSSpace 1 3 I x) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  ((slotPermCLM (I := I) perm4_3201 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_102 x).comp (connContrCLM (I := I) 1 1 x A)))
      + (slotPermCLM (I := I) perm4_2301 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_102 x).comp
            ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm2_10 x))))
      + (slotPermCLM (I := I) perm4_3102 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_120 x).comp (connContrCLM (I := I) 1 1 x A)))
      + (slotPermCLM (I := I) perm4_1302 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm2_10 x)))
      + (slotPermCLM (I := I) perm4_1203 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (connContrCLM (I := I) 1 1 x A))
      + (slotPermCLM (I := I) perm4_2103 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_120 x).comp
            ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm2_10 x)))))
    - (slotPermCLM (I := I) perm4_3012 x).comp (connContrCLM (I := I) 1 2 x DA)
    - (slotPermCLM (I := I) perm4_2013 x).comp
      ((connContrCLM (I := I) 1 2 x DA).comp (slotPermCLM (I := I) perm2_10 x))

noncomputable def ricciCometricFourTraceCLM (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ((1 : ℝ) / 2) •
    ((cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm4_0231 x)
      + (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm4_0321 x)
      - cometricDoubleTraceFib (I := I) g₁ 2 x
      - (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm4_2301 x))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem domDomCongrSectionContMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
          Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ
      (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option linter.unusedSectionVars false in

theorem slotPermCLM_field_contMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (slotPermCLM (I := I) ρ x (Z x))) := by
  refine (domDomCongrSectionContMDiff (I := I) ρ Z hZ).congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t)
    (slotPermCLM_apply (I := I) ρ x (Z x))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem tensorProdWithCLM_field_contMDiff (m k : ℕ)
    (P : ∀ x : M, Tensor0SBundle.Tensor0SSpace m I x)
    (Q : ∀ x : M, Tensor0SBundle.Tensor0SSpace k I x)
    (hP : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x (P x)))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel k ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x (Q x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z) x
        (tensorProdWithCLM (I := I) m k x (P x) (Q x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) m
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) k
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (m + k)
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z)]
  have hP' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel m ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀).mp (hP x₀)
  have hQ' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel k ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).mp (hQ x₀)
  have h_combine : ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E) ∞
      (fun x => Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SBundle.Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀ ⟨x, P x⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨x, Q x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := Bundle.continuousMultilinearMap.modelProductL
        (𝕜 := ℝ) (F := E) m k)).clm_apply hP').clm_apply hQ'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  apply ContinuousMultilinearMap.ext
  intro v
  rw [Bundle.continuousMultilinearMap.modelProductL_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hsymmL
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
      (Tensor0SBundle.Tensor0SSpace.toModel (P x))
      (Tensor0SBundle.Tensor0SSpace.toModel (Q x)))
      (fun i => symmL (v i)) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem connContrCLM_field_contMDiff (m k : ℕ)
    (Bf : ∀ x : M, Tensor0SBundle.TensorRSSpace 1 (k + 1) I x)
    (hBf : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (k + 1) I z) x (Bf x)))
    (Df : ∀ x : M, Tensor0SBundle.Tensor0SSpace (m + 1) I x)
    (hDf : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1) I z) x (Df x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) x
        (connContrCLM (I := I) m k x (Bf x) (Df x))) := by
  have hΨ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I z) x
        (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) x (Df x)).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (F₂ := Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z)
      (φ := fun x : M =>
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) x (Df x)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x))
    intro om
    have hBom : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace (k + 1) I z) x
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x) (om x))) :=
      ContMDiff.clm_bundle_apply (b := id) hBf om.contMDiff
    have hprod := tensorProdWithCLM_field_contMDiff (I := I) (m + 1) (k + 1)
      (fun x => Df x)
      (fun x => (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x) (om x))
      hDf hBom
    refine hprod.congr (fun x => ?_)
    exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z) x t) rfl
  have hTr := contractTraceField_contMDiff (I := I) 0 (m + 1 + k)
    (fun x : M =>
      (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) x (Df x)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x)))
    hΨ
  have hEval := ContMDiff.clm_bundle_apply (b := id) hTr
    (unitZeroSec (I := I) (M := M)).contMDiff
  refine hEval.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder1CLM_field_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 3 I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
        (linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x))) := by
  have hAsm := (connDiffSection (I := I) g₁ g₀).toSection.contMDiff
  have hpre102 := slotPermCLM_field_contMDiff (I := I) perm3_102 Z hZ
  have hpre120 := slotPermCLM_field_contMDiff (I := I) perm3_120 Z hZ
  have h₁ := slotPermCLM_field_contMDiff (I := I) perm4_0312 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x (Z x)) hpre102)
  have h₂ := slotPermCLM_field_contMDiff (I := I) perm4_0213 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x (Z x)) hpre120)
  have h₃ := slotPermCLM_field_contMDiff (I := I) perm4_2301 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => Z x) hZ)
  have h₄ := slotPermCLM_field_contMDiff (I := I) perm4_1302 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x (Z x)) hpre102)
  have h₅ := slotPermCLM_field_contMDiff (I := I) perm4_1203 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x (Z x)) hpre120)
  have hsum := ((((h₁.add_section h₂).add_section h₃).add_section h₄).add_section h₅).neg_section
  refine hsum.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder0CLM_field_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 2 I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
        (linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x) (Z x))) := by
  have hAsm := (connDiffSection (I := I) g₁ g₀).toSection.contMDiff
  have hDAsm := (covGrad (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g₁ g₀)).toSection.contMDiff
  have hZswap := slotPermCLM_field_contMDiff (I := I) perm2_10 Z hZ
  have hinnJ := connContrCLM_field_contMDiff (I := I) 1 1
    (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
    (fun x => Z x) hZ
  have hinnJ' := connContrCLM_field_contMDiff (I := I) 1 1
    (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
    (fun x => slotPermCLM (I := I) perm2_10 x (Z x)) hZswap
  have hu₃ := slotPermCLM_field_contMDiff (I := I) perm4_3201 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x)))
      (slotPermCLM_field_contMDiff (I := I) perm3_102 _ hinnJ))
  have hu₄ := slotPermCLM_field_contMDiff (I := I) perm4_2301 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)
          (slotPermCLM (I := I) perm2_10 x (Z x))))
      (slotPermCLM_field_contMDiff (I := I) perm3_102 _ hinnJ'))
  have hu₅ := slotPermCLM_field_contMDiff (I := I) perm4_3102 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x)))
      (slotPermCLM_field_contMDiff (I := I) perm3_120 _ hinnJ))
  have hu₆ := slotPermCLM_field_contMDiff (I := I) perm4_1302 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)
        (slotPermCLM (I := I) perm2_10 x (Z x)))
      hinnJ')
  have hu₇ := slotPermCLM_field_contMDiff (I := I) perm4_1203 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => connContrCLM (I := I) 1 1 x
        ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x))
      hinnJ)
  have hu₈ := slotPermCLM_field_contMDiff (I := I) perm4_2103 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)
          (slotPermCLM (I := I) perm2_10 x (Z x))))
      (slotPermCLM_field_contMDiff (I := I) perm3_120 _ hinnJ'))
  have hu₁ := slotPermCLM_field_contMDiff (I := I) perm4_3012 _
    (connContrCLM_field_contMDiff (I := I) 1 2
      (fun x => (covGrad (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) g₁ g₀)).toSection x) hDAsm
      (fun x => Z x) hZ)
  have hu₂ := slotPermCLM_field_contMDiff (I := I) perm4_2013 _
    (connContrCLM_field_contMDiff (I := I) 1 2
      (fun x => (covGrad (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) g₁ g₀)).toSection x) hDAsm
      (fun x => slotPermCLM (I := I) perm2_10 x (Z x)) hZswap)
  have hsum := (((((((hu₃.add_section hu₄).add_section hu₅).add_section
    hu₆).add_section hu₇).add_section hu₈).sub_section hu₁).sub_section hu₂)
  refine hsum.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem ricciCometricFourTraceCLM_field_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 4 I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (ricciCometricFourTraceCLM (I := I) g₁ x (Z x))) := by
  have ha := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2)
    (slotPermCLM_field_contMDiff (I := I) perm4_0231 Z hZ)
  have hb := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2)
    (slotPermCLM_field_contMDiff (I := I) perm4_0321 Z hZ)
  have hc := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hZ
  have hd := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2)
    (slotPermCLM_field_contMDiff (I := I) perm4_2301 Z hZ)
  have hcomb := (((ha.add_section hb).sub_section hc).sub_section hd).const_smul_section
    (a := ((1 : ℝ) / 2))
  refine hcomb.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

noncomputable def linearizedRicciConnDiffOrder1Fib (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (ricciCometricFourTraceCLM (I := I) g₁ x).comp
    (linearizedRicciConnDiffOrder1CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x))

noncomputable def linearizedRicciConnDiffOrder0Fib (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (ricciCometricFourTraceCLM (I := I) g₁ x).comp
    (linearizedRicciConnDiffOrder0CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x)
      ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder1Fib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x : M => linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x)
  intro Y
  have hE1 := linearizedRicciConnDiffOrder1CLM_field_contMDiff (I := I) g₀ g₁
    (fun x => Y x) Y.contMDiff
  have hCK := ricciCometricFourTraceCLM_field_contMDiff (I := I) g₁
    (fun x => linearizedRicciConnDiffOrder1CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x) (Y x)) hE1
  refine hCK.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxRecDepth 8000 in

theorem linearizedRicciConnDiffOrder0Fib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x : M => linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x)
  intro Y
  have hE0 := linearizedRicciConnDiffOrder0CLM_field_contMDiff (I := I) g₀ g₁
    (fun x => Y x) Y.contMDiff
  have hCK := ricciCometricFourTraceCLM_field_contMDiff (I := I) g₁
    (fun x => linearizedRicciConnDiffOrder0CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x)
      ((covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I) g₁ g₀)).toSection x) (Y x)) hE0
  refine hCK.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

noncomputable def linearizedRicciConnDiffOrder1CoeffField
    (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from
          linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x)
      contMDiff_toFun := linearizedRicciConnDiffOrder1Fib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

noncomputable def linearizedRicciConnDiffOrder0CoeffField
    (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x)
      contMDiff_toFun := linearizedRicciConnDiffOrder0Fib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem linearizedRicciConnDiffOrder1CoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        linearizedRicciConnDiffOrder1Fib (I := I) g₀ g₁ x) := rfl

set_option linter.unusedSectionVars false in

@[simp] theorem linearizedRicciConnDiffOrder0CoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        linearizedRicciConnDiffOrder0Fib (I := I) g₀ g₁ x) := rfl

def linearizedRicciConnDiffOrder1Coeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s)

def linearizedRicciConnDiffOrder0Coeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s)

set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder0Coeff_eq_base_add_sub
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
            - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s) := by
  abel

set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder1Coeff_eq_base_add_sub
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
            - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s) := by
  abel

private def velocitySecondCovGradCc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection
  hasCompactSupport :=
    (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).hasCompactSupport

set_option linter.unusedSectionVars false in

private lemma unitModel_smul_two (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]

set_option linter.unusedSectionVars false in

private lemma unitModel_add_two (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x =
      unitModel (I := I) (M := M) g₀ 2 S x + unitModel (I := I) (M := M) g₀ 2 S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in

private lemma unitModel_add_two_apply (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  rw [unitModel_add_two, ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in

private lemma ccTensorBilin_sub_two (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (b : M) (p q : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (T - T') b p q =
      ccTensorBilin (I := I) g₀ T b p q - ccTensorBilin (I := I) g₀ T' b p q := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  have hmulti : (ccTensorMultilinear (I := I) g₀ (T - T') b : Tensor0SBundle.Tensor0SSpace 2 I b) =
      (ccTensorMultilinear (I := I) g₀ T b : Tensor0SBundle.Tensor0SSpace 2 I b)
        - (ccTensorMultilinear (I := I) g₀ T' b : Tensor0SBundle.Tensor0SSpace 2 I b) := by
    unfold ccTensorMultilinear
    rw [SmoothCcTensor.toSection_sub]
    rfl
  have hmodel : ccTensorModel (I := I) g₀ (T - T') b =
      ccTensorModel (I := I) g₀ T b - ccTensorModel (I := I) g₀ T' b := by
    unfold ccTensorModel
    rw [hmulti, Tensor0SBundle.Tensor0SSpace.toModel_sub]
  rw [hmodel, ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in

private lemma symmS_eq_self_of_symm (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ S x u w = ccTensorBilin (I := I) g₀ S x w u) :
    symmS (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [symmS, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

set_option linter.unusedSectionVars false in

private lemma zero_mem_realizedSmallSet' {δ δ' : ℝ} (hδ'_lt : δ' < 1) :
    (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') := by
  change |1 - (0 : ℝ)| * δ' + |(0 : ℝ)| * δ < 1
  rw [sub_zero, abs_one, abs_zero, one_mul, zero_mul, add_zero]
  exact hδ'_lt

set_option linter.unusedSectionVars false in

private lemma dualToCotangent_smul_c {x : M} (c : ℝ) (α : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (c • α)
      = c • dualToCotangent (I := I) (x := x) α := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_smul, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

set_option linter.unusedSectionVars false in

private lemma ccTensorBilin_smul_c (g : SmoothRiemannianMetric I M) (c : ℝ)
    (S : SmoothCcTensor g 0 2) (b : M) (p q : TangentSpace I b) :
    ccTensorBilin (I := I) g (c • S) b p q = c * ccTensorBilin (I := I) g S b p q := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply]
  have hmulti : (ccTensorMultilinear (I := I) g (c • S) b : Tensor0SBundle.Tensor0SSpace 2 I b) =
      c • (ccTensorMultilinear (I := I) g S b : Tensor0SBundle.Tensor0SSpace 2 I b) := by
    unfold ccTensorMultilinear
    rw [SmoothCcTensor.toSection_smul]
    rfl
  have hmodel : ccTensorModel (I := I) g (c • S) b = c • ccTensorModel (I := I) g S b := by
    unfold ccTensorModel
    rw [hmulti, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  rw [hmodel, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in

private lemma iteratedCovGrad_smul_c (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in

private lemma unitModel_smul_gen (g : SmoothRiemannianMetric I M) {n : ℕ}
    (c : ℝ) (W : SmoothCcTensor g 0 n) (x : M) :
    unitModel (I := I) (M := M) g n (c • W) x =
      c • unitModel (I := I) (M := M) g n W x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]

set_option linter.unusedSectionVars false in

private lemma koszulPair_eq_smul_dual_linearizedKoszul
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (Zf Yf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    koszulCovGradCovec (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedFam (I := I) g₀ T T' hδ hδ' 0)
        Zf Yf b =
      ((0 : ℝ) - s) • dualToCotangent (I := I)
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Yf b) (Zf b)) := by
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs)
  have h0mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    zero_mem_realizedSmallSet' hδ'_lt
  have hcd := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    (s₀ := s) (s := 0) hsmem h0mem b (Yf b) (Zf b)
  rw [koszulCovGradCovec, hcd]
  have hlm : ((realizedFam (I := I) g₀ T T' hδ hδ' 0).inner b
      (((0 : ℝ) - s) •
        metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 0) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Yf b) (Zf b)))).toLinearMap =
      ((0 : ℝ) - s) •
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Yf b) (Zf b)) := by
    apply LinearMap.ext
    intro z
    rw [LinearMap.smul_apply]
    change ((realizedFam (I := I) g₀ T T' hδ hδ' 0).inner b
      (((0 : ℝ) - s) • metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 0) b _)) z = _
    rw [map_smul, ContinuousLinearMap.smul_apply, inner_metricSharp]
  rw [hlm, dualToCotangent_smul_c]

set_option linter.unusedSectionVars false in

private lemma unitEval_bilin_eq (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (y : M) (m : Fin 2 → TangentSpace I y) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
          S.toSection y) (unitZeroSec (I := I) (M := M) y)) m =
      ccTensorBilin (I := I) g S y (m 0) (m 1) := by
  have hm : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ccTensorBilin_apply]
  rw [show ccTensorModel (I := I) g S y ![m 0, m 1] =
      Tensor0SBundle.Tensor0SSpace.toModel
        (ccTensorMultilinear (I := I) g S y : Tensor0SBundle.Tensor0SSpace 2 I y)
        ![m 0, m 1] from rfl]
  conv_lhs => rw [hm]
  rfl

set_option linter.unusedSectionVars false in

private lemma velocity_unitEval_domDomCongr_swap
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) :
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y) =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
          (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
            (unitZeroSec (I := I) (M := M) y)) := by
  apply Tensor0SBundle.tensor0SSpace_ext 2 y
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hswapargs : (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I y) ℝ from
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y)) (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) =
      ccTensorBilin (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (m 1) (m 0) := by
    rw [unitEval_bilin_eq (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y]
    congr 1
  rw [unitEval_bilin_eq (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y]
  rw [hswapargs]
  rw [show ccTensorBilin (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (m 0) (m 1) =
      ccTensorBilin (I := I) g₀
        (symmS (I := I) (M := M) g₀ (T - T')) y (m 0) (m 1) from rfl]
  rw [show ccTensorBilin (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (m 1) (m 0) =
      ccTensorBilin (I := I) g₀
        (symmS (I := I) (M := M) g₀ (T - T')) y (m 1) (m 0) from rfl]
  rw [ccTensorBilin_symmS, ccTensorBilin_symmS,
    ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  ring

set_option linter.unusedSectionVars false in

private lemma unitEval_tensorSectionMDiffAt (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) :
    TensorSectionMDiffAt (I := I) n
      (fun y : M =>
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y from
          W.toSection y) (unitZeroSec (I := I) (M := M) y)) x := by
  have hsm := ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff
  exact ((hsm x).mdifferentiableAt (by simp))

set_option linter.unusedSectionVars false in

private lemma unitModel_covGrad_eval (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (x : M) (v : Fin (n + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (n + 1) (covGrad (I := I) (M := M) g 0 n W) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        (show Tensor0SBundle.Tensor0SSpace n I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace n I y from
                W.toSection y) (unitZeroSec (I := I) (M := M) y)) x (v 0))
        (Matrix.vecTail v) := by
  rw [unitModel]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 n W x
    (unitZeroSec (I := I) (M := M) x) v]
  congr 1
  rw [tensorCovDerivAt_def]
  rw [TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) 0 n
    (LeviCivita (I := I) g) W.toSection (unitZeroSec (I := I) (M := M)) x (v 0)]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
      (fun y : M => unitZeroSec (I := I) (M := M) y) x (v 0)) = 0 from
    Tensor0SNabla.tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x (v 0)]
  rw [map_zero, sub_zero]

set_option linter.unusedSectionVars false in

private lemma inverseMetricSharpFib_dualToCotangent (g : SmoothRiemannianMetric I M)
    (x : M) (φ : Module.Dual ℝ (TangentSpace I x)) :
    inverseMetricSharpFib (I := I) g x (dualToCotangent (I := I) φ) =
      metricSharp (I := I) g x φ := by
  rw [inverseMetricSharpFib_apply, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]

set_option linter.unusedSectionVars false in

private lemma cotangentToCLM_smul_c {x : M} (c : ℝ) (β : Tensor0SBundle.Tensor0SSpace 1 I x) :
    cotangentToCLM (I := I) (c • β) = c • cotangentToCLM (I := I) β := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.smul_apply]
  rw [show (cotangentToCLM (I := I) (c • β)) w = cotangentToDual (I := I) (c • β) w from rfl]
  rw [show (cotangentToCLM (I := I) β) w = cotangentToDual (I := I) β w from rfl]
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rfl

set_option linter.unusedSectionVars false in

private lemma toModel_apply_tangent {n : ℕ} (x : M)
    (D : Tensor0SBundle.Tensor0SSpace n I x) (m : Fin n → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel D m =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin n => TangentSpace I x) ℝ from D) m := rfl

set_option linter.unusedSectionVars false in

private theorem cotangentCov_linearizedKoszul_eval
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))).toFun
        (fun b : M => cotangentToCLM (I := I)
          (dualToCotangent (I := I)
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Y b) (Z b)))) x (X x)) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
                (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
                (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
              (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
              ![(LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                  (fun b => Z b) x (X x), Y x, ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![Z x, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Y b) x (X x), ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![(LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Y b) x (X x), Z x, ζ]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![Y x, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Z b) x (X x), ζ]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![ζ, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Z b) x (X x), Y x]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
                (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
                  (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x
                ![ζ, Z x, (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
                    (fun b => Y b) x (X x)]) := by
  classical
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs)
  have h0mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    zero_mem_realizedSmallSet' hδ'_lt
  have hsne : (0 : ℝ) - s ≠ 0 := by
    have h0 : (0 : ℝ) - s < 0 := by linarith [hs.1]
    exact ne_of_lt h0
  have hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (((0 : ℝ) - s) • realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b u w =
        (realizedFam (I := I) g₀ T T' hδ hδ' 0).inner b u w -
          (realizedFam (I := I) g₀ T T' hδ hδ' s).inner b u w := by
    intro b u w
    rw [ccTensorBilin_smul_c,
      realizedVelocityCc_bilin (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s b u w]
    have haff := realizedFam_inner_affine (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (s₀ := s) (s := 0) hsmem h0mem b u w
    linarith [haff]
  have h996 := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedFam (I := I) g₀ T T' hδ hδ' 0)
    (((0 : ℝ) - s) • realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) hbil X Y Z x ζ
  rw [cotangentToDual_dualToCotangent] at h996
  have hθ₀ : (fun b : M => cotangentToCLM (I := I)
        (dualToCotangent (I := I)
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Y b) (Z b)))) =
      ((0 : ℝ) - s)⁻¹ • (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' 0) Z Y b)) := by
    funext b
    rw [Pi.smul_apply,
      koszulPair_eq_smul_dual_linearizedKoszul (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs Z Y b,
      cotangentToCLM_smul_c, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  have hsc := (cotangentCov
      (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))).isCovariantDerivativeOnUniv.smul_const
    (σ := fun b : M => cotangentToCLM (I := I)
      (koszulCovGradCovec (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedFam (I := I) g₀ T T' hδ hδ' 0) Z Y b))
    (x := x) (((0 : ℝ) - s)⁻¹)
    (koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedFam (I := I) g₀ T T' hδ hδ' 0) Z Y x)
    (Set.mem_univ x)
  rw [ContinuousLinearMap.coe_coe] at h996
  rw [hθ₀, hsc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h996]
  rw [iteratedCovGrad_smul_c, covGrad_smul, unitModel_smul_gen, unitModel_smul_gen]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  field_simp

set_option linter.unusedSectionVars false in

private lemma velocity_covGrad_swap12
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, c] =
      unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, c, b] := by
  rw [unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x ![a, b, c],
    (unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x ![a, c, b])]
  simp only [Matrix.cons_val_zero, Matrix.tail_cons]
  have hnat := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 1
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (Equiv.swap (0 : Fin 2) 1)
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    x a
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x)
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x)
    (fun y => velocity_unitEval_domDomCongr_swap (I := I) g₀ T T' hδ hδ' s y)
  rw [toModel_apply_tangent, toModel_apply_tangent]
  have happ := congrArg
    (fun (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ) =>
      T ![b, c]) hnat
  dsimp only at happ
  rw [ContinuousMultilinearMap.domDomCongr_apply] at happ
  have hvec : (fun i => (![b, c] : Fin 2 → TangentSpace I x) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![c, b] := by
    funext i
    fin_cases i <;> simp
  rw [hvec] at happ
  exact happ

set_option linter.unusedSectionVars false in

private lemma velocity_covGrad_unitEval_domDomCongr_swap12
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) :
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
        (unitZeroSec (I := I) (M := M) y) =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I y) ℝ from
          (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
            (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
            (unitZeroSec (I := I) (M := M) y)) := by
  apply Tensor0SBundle.tensor0SSpace_ext 3 y
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have h1 : ∀ (mm : Fin 3 → TangentSpace I y),
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I y) ℝ from
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
          (unitZeroSec (I := I) (M := M) y)) mm =
      unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) y mm := fun mm => rfl
  rw [h1, h1]
  have hm : m = ![m 0, m 1, m 2] := by
    funext i
    fin_cases i <;> simp
  have hmσ : (fun i => m ((Equiv.swap (1 : Fin 3) 2) i)) = ![m 0, m 2, m 1] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [hmσ]
  conv_lhs => rw [hm]
  exact velocity_covGrad_swap12 (I := I) g₀ T T' hδ hδ' s y (m 0) (m 1) (m 2)

set_option linter.unusedSectionVars false in

private lemma velocity_secondCovGrad_swap23
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (a b c d : TangentSpace I x) :
    unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
        (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, c, d] =
      unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
        (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, d, c] := by
  have hunf : iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) =
      covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 3
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) := rfl
  rw [hunf]
  rw [unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, c, d],
    (unitModel_covGrad_eval (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![a, b, d, c])]
  simp only [Matrix.cons_val_zero, Matrix.tail_cons]
  have hnat := tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) 2
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (Equiv.swap (1 : Fin 3) 2)
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    (fun y : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
        (unitZeroSec (I := I) (M := M) y))
    x a
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x)
    (unitEval_tensorSectionMDiffAt (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x)
    (fun y => velocity_covGrad_unitEval_domDomCongr_swap12 (I := I) g₀ T T' hδ hδ' s y)
  rw [toModel_apply_tangent, toModel_apply_tangent]
  have happ := congrArg
    (fun (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ) =>
      T ![b, c, d]) hnat
  dsimp only at happ
  rw [ContinuousMultilinearMap.domDomCongr_apply] at happ
  have hvec : (fun i => (![b, c, d] : Fin 3 → TangentSpace I x) ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![b, d, c] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [hvec] at happ
  exact happ

set_option linter.unusedSectionVars false in

private lemma lkc_eq_endpoint_flat
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (b : M) (u ζ : TangentSpace I b) :
    linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b u ζ =
      (1 - s)⁻¹ •
        ((realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ)).toLinearMap := by
  classical
  have h1mem : (1 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    one_mem_realizedSmallSet hδ_lt
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs)
  have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs.2)
  ext z
  have hkey := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    hsmem h1mem b u ζ
  have hinner : (realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ) z =
      (1 - s) *
        linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b u ζ z := by
    rw [hkey, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, inner_metricSharp]
  rw [LinearMap.smul_apply]
  rw [show (((realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ)).toLinearMap) z =
      (realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) b u ζ) z from rfl]
  rw [hinner, smul_eq_mul]
  field_simp

set_option linter.unusedSectionVars false in

private lemma lkc_basis_contMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  have hΛ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' 1) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      Z.contMDiff Y.contMDiff
  have hflat : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) b
        (g0FlatCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1) b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)) hΛ
  set Kf : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E,
      (fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)⟯ :=
    ⟨fun b : M => g0FlatCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1) b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)), hflat⟩ with hKf
  have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Kf α j
  have heq : ∀ b ∈ (chartAt H α).source,
      linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b) =
        (1 - s)⁻¹ *
          Tensor0SBundle.Tensor0SSpace.toModel (Kf b)
            (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) := by
    intro b _
    rw [lkc_eq_endpoint_flat (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs b (Z b) (Y b)]
    rw [LinearMap.smul_apply, smul_eq_mul]
    congr 1
  have hcomb : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (1 - s)⁻¹ *
        Tensor0SBundle.Tensor0SSpace.toModel (Kf b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source :=
    contMDiffOn_const.mul hbase
  exact hcomb.congr heq

set_option linter.unusedSectionVars false in

private lemma sharpPsi_contMDiff
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)))) := by
  apply metricSharp_contMDiff_total (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (cv := fun b : M =>
      linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b))
  intro α j
  exact lkc_basis_contMDiffOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs Y Z α j

set_option linter.unusedSectionVars false in

private theorem covDerivLinearizedConn_inner_towers
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
          (fun b => X b) (fun b => Y b) (fun b => Z b) x) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
            (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Y x, Z x, ζ]
          + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, Z x, Y x, ζ]
          - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![X x, ζ, Y x, Z x]) := by
  classical
  have hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) y)
          (dualToCotangent (I := I)
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y))))) x := by
    have hfun : (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) y)
          (dualToCotangent (I := I)
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y))))) =
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
          (metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) y
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y)))) := by
      funext y
      rw [inverseMetricSharpFib_dualToCotangent]
    rw [hfun]
    exact ((sharpPsi_contMDiff (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs Y Z x).mdifferentiableAt
      (by simp))
  have hpar := inverseMetricSharpField_covGrad_eq_zero
    (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (fun y : M => dualToCotangent (I := I)
      (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y (Z y) (Y y)))
    hβ (X x)
  have hfield : (fun b : M =>
      linearizedConnSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)) =
      (fun b : M => (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b)
        (dualToCotangent (I := I)
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) b (Z b) (Y b)))) := by
    funext b
    rw [inverseMetricSharpFib_dualToCotangent]
    rfl
  rw [covDerivLinearizedConn]
  rw [map_sub, map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rw [hfield, hpar]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    ContinuousLinearMap.coe_coe]
  rw [cotangentCov_linearizedKoszul_eval (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs X Z Y x ζ]
  rw [show linearizedConnSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x (Z x)
      (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (fun b => X b) (fun b => Y b) x) =
    metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
      (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x (Z x)
        (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (fun b => X b) (fun b => Y b) x)) from rfl]
  rw [show linearizedConnSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x
      (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (fun b => X b) (fun b => Z b) x) (Y x) =
    metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
      (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) x
        (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (fun b => X b) (fun b => Z b) x) (Y x)) from rfl]
  rw [inner_metricSharp, inner_metricSharp]
  rw [linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  rw [covApply_apply, covApply_apply]
  ring

private def perm4_1023 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 0, 2, 3] ![1, 0, 2, 3] (by decide) (by decide)

set_option linter.unusedSectionVars false in

private lemma vec4_update_zero {F : Type*} (a b c d z : F) :
    Function.update ![a, b, c, d] 0 z = ![z, b, c, d] := by
  funext k
  fin_cases k <;> simp [Function.update]

set_option linter.unusedSectionVars false in

private lemma vec4_update_three {F : Type*} (a b c d z : F) :
    Function.update ![a, b, c, d] 3 z = ![a, b, c, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

private def cmmSlotPairCLM (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun om => ContinuousMultilinearMap.toContinuousLinearMap
        (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![(0 : E), p, q, om] (0 : Fin 4)
      map_add' := fun om om' => by
        apply ContinuousLinearMap.ext
        intro u
        rw [ContinuousLinearMap.add_apply]
        change (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            (Function.update ![(0 : E), p, q, om + om'] 0 u) =
          (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
              (Function.update ![(0 : E), p, q, om] 0 u) +
            (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
              (Function.update ![(0 : E), p, q, om'] 0 u)
        rw [vec4_update_zero, vec4_update_zero, vec4_update_zero]
        have hupd : (![u, p, q, om + om'] : Fin 4 → E) =
            Function.update ![u, p, q, om] 3 (om + om') := by
          rw [vec4_update_three]
        rw [hupd]
        rw [ContinuousMultilinearMap.map_update_add
          (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![u, p, q, om] 3 om om']
        rw [vec4_update_three, vec4_update_three]
      map_smul' := fun c om => by
        apply ContinuousLinearMap.ext
        intro u
        rw [RingHom.id_apply, ContinuousLinearMap.smul_apply]
        change (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            (Function.update ![(0 : E), p, q, (c • om)] 0 u) =
          c • (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
              (Function.update ![(0 : E), p, q, om] 0 u)
        rw [vec4_update_zero, vec4_update_zero]
        have hupd : (![u, p, q, (c • om)] : Fin 4 → E) =
            Function.update ![u, p, q, om] 3 (c • om) := by
          rw [vec4_update_three]
        rw [hupd]
        rw [ContinuousMultilinearMap.map_update_smul
          (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![u, p, q, om] 3 c om]
        rw [vec4_update_three] }

set_option linter.unusedSectionVars false in

private lemma cmmSlotPairCLM_apply (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q om u : E) :
    cmmSlotPairCLM (E := E) D p q om u = D ![u, p, q, om] := by
  change (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
      (Function.update ![(0 : E), p, q, om] 0 u) = D ![u, p, q, om]
  rw [vec4_update_zero]

private def sharpCovCLM (g₁ : SmoothRiemannianMetric I M) (x : M) :
    (E →L[ℝ] ℝ) →L[ℝ] E :=
  (cometricLmodel (I := I) g₁ x).comp (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E))

set_option linter.unusedSectionVars false in

private lemma sharpCovCLM_apply (g₁ : SmoothRiemannianMetric I M) (x : M) (φ : E →L[ℝ] ℝ) :
    sharpCovCLM (I := I) (M := M) g₁ x φ =
      cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) := rfl

set_option linter.unusedSectionVars false in

private lemma inner_sharpCovCLM (g₁ : SmoothRiemannianMetric I M) (x : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I x) :
    g₁.inner x (sharpCovCLM (I := I) (M := M) g₁ x φ) u = φ (u : E) := by
  rw [sharpCovCLM_apply]
  exact cometricLmodel_covectorOfCLM_inner (I := I) g₁ x φ u

set_option linter.unusedSectionVars false in

private lemma cDualBasis_eq_coord (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E)) :
    B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
  rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
    (congrFun (Module.Basis.coe_dualBasis B) k)

set_option linter.unusedSectionVars false in

private lemma sharp_dual_coeff_symm (g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (k l : Fin (Module.finrank ℝ E)) :
    B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) =
      B.cDualBasis k (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l)) := by
  rw [← inner_sharpCovCLM (I := I) g₁ x (B.cDualBasis l)
    (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))]
  rw [← inner_sharpCovCLM (I := I) g₁ x (B.cDualBasis k)
    (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l))]
  exact g₁.symm x _ _

set_option linter.unusedSectionVars false in

private lemma sharpCov_basis_expand (g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (k : Fin (Module.finrank ℝ E)) :
    sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k) =
      ∑ l : Fin (Module.finrank ℝ E),
        (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) • B l := by
  have hl : ∀ l : Fin (Module.finrank ℝ E),
      B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) =
        B.repr (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) l := by
    intro l
    rw [cDualBasis_eq_coord]
    rfl
  rw [show (∑ l : Fin (Module.finrank ℝ E),
      (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) • B l) =
      ∑ l : Fin (Module.finrank ℝ E),
        (B.repr (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) l) • B l from
    Finset.sum_congr rfl (fun l _ => by rw [hl l])]
  exact (B.sum_repr (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))).symm

set_option linter.unusedSectionVars false in

private lemma bilinCLM_diag_swap (g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (Λ : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E),
        Λ (B k) (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) =
      ∑ k : Fin (Module.finrank ℝ E),
        Λ (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)) (B k) := by
  have hexp : ∀ k, sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k) =
      ∑ l : Fin (Module.finrank ℝ E),
        (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) • B l :=
    fun k => sharpCov_basis_expand (I := I) g₁ x B k
  calc
    (∑ k : Fin (Module.finrank ℝ E),
        Λ (B k) (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k)))
        = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) *
              Λ (B k) (B l) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          conv_lhs => rw [hexp k]
          rw [map_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [map_smul, smul_eq_mul]
    _ = ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            (B.cDualBasis l (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis k))) *
              Λ (B k) (B l) := Finset.sum_comm
    _ = ∑ l : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            (B.cDualBasis k (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l))) *
              Λ (B k) (B l) := by
          refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [sharp_dual_coeff_symm (I := I) g₁ x B l k]
    _ = ∑ l : Fin (Module.finrank ℝ E),
            Λ (sharpCovCLM (I := I) (M := M) g₁ x (B.cDualBasis l)) (B l) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          conv_rhs => rw [hexp l]
          rw [map_sum, ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in

private lemma slotPair_trace_basis_indep (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q : E) :
    (∑ i : Fin (Module.finrank ℝ E),
        D ![(chartModelBasis E i : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![(Module.finBasis ℝ E k : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k)] := by
  have h := cDualBasis_trace_basis_indep (chartModelBasis E)
    ((cmmSlotPairCLM (E := E) D p q).comp (sharpCovCLM (I := I) (M := M) g₁ x))
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).comp (sharpCovCLM (I := I) (M := M) g₁ x))
        ((chartModelBasis E).cDualBasis k) (chartModelBasis E k)) =
      ∑ i : Fin (Module.finrank ℝ E),
        D ![(chartModelBasis E i : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((chartModelBasis E).cDualBasis i)] from
    Finset.sum_congr rfl (fun i _ => by
      rw [ContinuousLinearMap.comp_apply, cmmSlotPairCLM_apply])] at h
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).comp (sharpCovCLM (I := I) (M := M) g₁ x))
        ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![(Module.finBasis ℝ E k : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k)] from
    Finset.sum_congr rfl (fun k _ => by
      rw [ContinuousLinearMap.comp_apply, cmmSlotPairCLM_apply])] at h
  exact h

set_option linter.unusedSectionVars false in

private lemma slotPair_trace_master (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (p q : E) :
    (∑ i : Fin (Module.finrank ℝ E),
        D ![(chartModelBasis E i : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k), p, q,
          (Module.finBasis ℝ E k : E)] := by
  rw [slotPair_trace_basis_indep (I := I) g₁ x D p q]
  have hswap := bilinCLM_diag_swap (I := I) g₁ x (Module.finBasis ℝ E)
    ((cmmSlotPairCLM (E := E) D p q).flip)
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).flip) ((Module.finBasis ℝ E) k)
        (sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k))) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![(Module.finBasis ℝ E k : E), p, q,
          sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k)] from
    Finset.sum_congr rfl (fun k _ => by
      rw [ContinuousLinearMap.flip_apply, cmmSlotPairCLM_apply])] at hswap
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      ((cmmSlotPairCLM (E := E) D p q).flip)
        (sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k))
        ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        D ![sharpCovCLM (I := I) (M := M) g₁ x ((Module.finBasis ℝ E).cDualBasis k), p, q,
          (Module.finBasis ℝ E k : E)] from
    Finset.sum_congr rfl (fun k _ => by
      rw [ContinuousLinearMap.flip_apply, cmmSlotPairCLM_apply])] at hswap
  exact hswap

set_option linter.unusedSectionVars false in

private lemma appCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ Ψ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (Φ - Ψ) W =
      appCc (I := I) (M := M) g r s Φ W - appCc (I := I) (M := M) g r s Ψ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ W - appCc (I := I) (M := M) g r s Ψ W).toSection x) =
      (appCc (I := I) (M := M) g r s Φ W).toSection x -
        (appCc (I := I) (M := M) g r s Ψ W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ - Ψ).toSection x : Tensor0SBundle.TensorRSSpace r s I x) =
      Φ.toSection x - Ψ.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option linter.unusedSectionVars false in

private lemma appCc_smul_left' (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : Tensor0SBundle.TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in

private lemma unitModel_sub_gen (g : SmoothRiemannianMetric I M) {n : ℕ}
    (S S' : SmoothCcTensor g 0 n) (x : M) :
    unitModel (I := I) (M := M) g n (S - S') x =
      unitModel (I := I) (M := M) g n S x - unitModel (I := I) (M := M) g n S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]

private def perm4_1032 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 0, 3, 2] ![1, 0, 3, 2] (by decide) (by decide)

set_option linter.unusedSectionVars false in

private lemma domDomCongr_0312_eval (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (a b c d : E) :
    ContinuousMultilinearMap.domDomCongr perm4_0312
      (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![a, b, c, d] = D ![a, d, b, c] := by
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in

private lemma domDomCongr_1032_eval (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (a b c d : E) :
    ContinuousMultilinearMap.domDomCongr perm4_1032
      (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![a, b, c, d] = D ![b, a, d, c] := by
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in

private lemma domDomCongr_1203_eval (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (a b c d : E) :
    ContinuousMultilinearMap.domDomCongr perm4_1203
      (D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ![a, b, c, d] = D ![b, c, a, d] := by
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in

private lemma finCons_vec3_eq {F : Type*} (a b c d : F) :
    (Fin.cons a ![b, c, d] : Fin 4 → F) = ![a, b, c, d] := by
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in

private lemma finCons_cons_pair_eq {F : Type*} (a b : F) (v : Fin 2 → F) :
    (Fin.cons a (Fin.cons b v) : Fin 4 → F) = ![a, b, v 0, v 1] := by
  funext i
  fin_cases i <;> rfl

private theorem linearizedRicciAt_eq_lichnerowicz_velocitySecondCovGrad
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v := by
  classical
  have hD4rfl : ∀ (m : Fin 4 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x m := fun m => rfl
  have hconv : ∀ k : Fin (Module.finrank ℝ E),
      sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k) =
        cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)) := fun k => rfl
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v =
      (1 / 2 : ℝ) *
        ((∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k])
          + (∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k])
          - (∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1]))
      - (1 / 2 : ℝ) *
          (∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k]) := by
    rw [show linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) -
          (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl]
    rw [appCc_sub_left, appCc_smul_left', unitModel_sub_gen, unitModel_smul_gen,
      ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x v]
    rw [traceHessianCoeff_appCc_eq (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x v]
    have hterm : ∀ k : Fin (Module.finrank ℝ E),
        (unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![v 0, v 1, (Module.finBasis ℝ E) k])
          + unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 1, v 0, (Module.finBasis ℝ E) k])
          - unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) v))) =
        (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k]
          + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k]
          - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1]) := by
      intro k
      rw [← hconv k]
      rw [finCons_vec3_eq (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k)) (v 0) (v 1) ((Module.finBasis ℝ E) k)]
      rw [finCons_vec3_eq (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k)) (v 1) (v 0) ((Module.finBasis ℝ E) k)]
      rw [finCons_cons_pair_eq (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k)) ((Module.finBasis ℝ E) k) v]
      rw [hD4rfl, hD4rfl, hD4rfl]
    have htrace : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace 4 I x from
                (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
                (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v)) =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
      intro k
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      have hargs : (fun i => (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v) : Fin 4 → TangentSpace I x)
          (traceHessianSlotPerm i)) =
        ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
        funext i
        fin_cases i <;> rfl
      rw [hargs]
      exact hD4rfl _
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        (unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![v 0, v 1, (Module.finBasis ℝ E) k])
          + unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 1, v 0, (Module.finBasis ℝ E) k])
          - unitModel (I := I) (M := M) g₀ 4 (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) v)))) =
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1]) from
      Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace 4 I x from
                (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
                (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v))) =
        ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] from
      Finset.sum_congr rfl (fun k _ => htrace k)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hRHS]
  have hks := linearizedRicciAt_eq_palatini_covDeriv (I := I) (g₀ := g₀) (T := T) (T' := T')
    (x := x) (v := v 0) (w := v 1) hδ_lt hδ hδ'_lt hδ' (s₀ := s) hs
  rw [hks]
  have hsum : ∀ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x (v 1)) x
          - covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x)) i =
      ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1])) := by
    intro i
    have hrepr : ∀ (W : TangentSpace I x),
        ((chartModelBasis E).repr W) i =
          (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x W (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) := by
      intro W
      rw [(realizedFam (I := I) g₀ T T' hδ hδ' s).symm x W (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)), inner_sharpCovCLM, cDualBasis_eq_coord]
      rfl
    rw [map_sub, Finsupp.sub_apply, hrepr, hrepr]
    set Bi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hBi
    set V0f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hV0f
    set V1f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 1),
        smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩ with hV1f
    have hBix : (Bi x : TangentSpace I x) = (chartModelBasis E) i := smoothExtensionTangent_eq (I := I) x ((chartModelBasis E) i)
    have hV0x : (V0f x : TangentSpace I x) = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
    have hV1x : (V1f x : TangentSpace I x) = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
    have hA := covDerivLinearizedConn_inner_towers (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs
      Bi V0f V1f x (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i))
    have hB := covDerivLinearizedConn_inner_towers (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs
      V0f Bi V1f x (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i))
    rw [hBix, hV0x, hV1x] at hA hB
    have hA' : (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
          (smoothExtensionTangent (I := I) x (v 0))
          (smoothExtensionTangent (I := I) x (v 1)) x) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) =
        (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1]) := hA
    have hB' : (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
          (smoothExtensionTangent (I := I) x (v 0))
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
          (smoothExtensionTangent (I := I) x (v 1)) x) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) =
        (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1]) := hB
    rw [hA', hB']
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
        (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x (v 1)) x
          - covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)
            (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x)) i) =
    ∑ i : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1])
        - (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            + unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]
            - unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1])) from
    Finset.sum_congr rfl (fun i _ => hsum i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hTA1 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k] :=
    slotPair_trace_master (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 0) (v 1)
  have hTA2 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, v 1, v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 1, v 0, (Module.finBasis ℝ E) k] :=
    slotPair_trace_master (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 1) (v 0)
  have hTA3 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1] := by
    have hcan : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1] =
          ContinuousMultilinearMap.domDomCongr perm4_0312
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] := by
      intro i
      rw [domDomCongr_0312_eval]
    have hcan' : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr perm4_0312
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k] =
          unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k, v 0, v 1] := by
      intro k
      rw [domDomCongr_0312_eval]
    rw [show (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![(chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 0, v 1]) =
        ∑ i : Fin (Module.finrank ℝ E),
          ContinuousMultilinearMap.domDomCongr perm4_0312
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] from
      Finset.sum_congr rfl (fun i _ => hcan i)]
    rw [slotPair_trace_master (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 0) (v 1)]
    exact Finset.sum_congr rfl (fun k _ => hcan' k)
  have hTB2 : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ k : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
    have hcan : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] =
          ContinuousMultilinearMap.domDomCongr perm4_1203
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] := by
      intro i
      rw [domDomCongr_1203_eval]
    have hcan' : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr perm4_1203
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), v 0, v 1, (Module.finBasis ℝ E) k] =
          unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((Module.finBasis ℝ E).cDualBasis k), (Module.finBasis ℝ E) k] := by
      intro k
      rw [domDomCongr_1203_eval]
    rw [show (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, v 1, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
        ∑ i : Fin (Module.finrank ℝ E),
          ContinuousMultilinearMap.domDomCongr perm4_1203
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
            ![(chartModelBasis E) i, v 0, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] from
      Finset.sum_congr rfl (fun i _ => hcan i)]
    rw [slotPair_trace_master (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ (v 0) (v 1)]
    exact Finset.sum_congr rfl (fun k _ => hcan' k)
  have hmid : (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)]) =
      ∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1] := by
    have hstep1 : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)] = unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 1] := by
      intro i
      exact velocity_secondCovGrad_swap23 (I := I) g₀ T T' hδ hδ' s x (v 0) ((chartModelBasis E) i)
        (v 1) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i))
    have hswap := bilinCLM_diag_swap (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x (chartModelBasis E)
      ((cmmSlotPairCLM (E := E)
        (ContinuousMultilinearMap.domDomCongr perm4_1032
          (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
    have hL : ∀ i : Fin (Module.finrank ℝ E),
        ((cmmSlotPairCLM (E := E)
          (ContinuousMultilinearMap.domDomCongr perm4_1032
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
          ((chartModelBasis E) i) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 1] := by
      intro i
      rw [ContinuousLinearMap.flip_apply, cmmSlotPairCLM_apply, domDomCongr_1032_eval]
    have hR : ∀ i : Fin (Module.finrank ℝ E),
        ((cmmSlotPairCLM (E := E)
          (ContinuousMultilinearMap.domDomCongr perm4_1032
            (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
          (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) ((chartModelBasis E) i) =
        unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1] := by
      intro i
      rw [ContinuousLinearMap.flip_apply, cmmSlotPairCLM_apply, domDomCongr_1032_eval]
    calc (∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, v 1, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)])
        = ∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, (chartModelBasis E) i, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), v 1] :=
          Finset.sum_congr rfl (fun i _ => hstep1 i)
      _ = ∑ i : Fin (Module.finrank ℝ E),
            ((cmmSlotPairCLM (E := E)
              (ContinuousMultilinearMap.domDomCongr perm4_1032
                (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
              ((chartModelBasis E) i) (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) :=
          Finset.sum_congr rfl (fun i _ => (hL i).symm)
      _ = ∑ i : Fin (Module.finrank ℝ E),
            ((cmmSlotPairCLM (E := E)
              (ContinuousMultilinearMap.domDomCongr perm4_1032
                (unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) (v 0) (v 1)).flip)
              (sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i)) ((chartModelBasis E) i) := hswap
      _ = ∑ i : Fin (Module.finrank ℝ E), unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 4
              (iteratedCovGrad (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2 2
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x ![v 0, sharpCovCLM (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  ((chartModelBasis E).cDualBasis i), (chartModelBasis E) i, v 1] :=
          Finset.sum_congr rfl (fun i _ => hR i)
  rw [hTA1, hTA2, hTA3, hTB2, hmid]
  ring

set_option linter.unusedSectionVars false

lemma toModel_empty_eq_iso {y : M} (T : Tensor0SBundle.Tensor0SSpace 0 I y)
    (m : Fin 0 → TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel T m = Tensor0SNabla.tensor0Iso I M y T := by
  have h0 : Tensor0SNabla.tensor0Iso I M y T =
      (continuousMultilinearCurryFin0 ℝ E ℝ)
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 0 y) T) := rfl
  rw [h0, continuousMultilinearCurryFin0_apply]
  exact congrArg _ (funext fun i => i.elim0)

lemma curried_tsmdiffAt (n : ℕ)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace (n + 1) I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (n + 1) W x)
    (Y : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) n
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) n W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel n ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace n I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

lemma deriv0_eq_extDeriv (g : SmoothRiemannianMetric I M)
    (sc : Π y : M, Tensor0SBundle.Tensor0SSpace 0 I y) (x : M) (v : TangentSpace I x) :
    Tensor0SNabla.tensor0Iso I M x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) sc x v) =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M sc) x v := by
  rw [Tensor0SNabla.tensor0SCovariantDerivative_apply_zero]
  exact (Tensor0SNabla.tensor0Iso I M x).apply_symm_apply _

lemma curried2_toModel_eval
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SNabla.scalarFn I M
        (fun z : M => Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M W w (Yf w)) z (Zf z)) y =
      Tensor0SBundle.Tensor0SSpace.toModel (W y) ![Yf y, Zf y] := by
  rw [show Tensor0SNabla.scalarFn I M
      (fun z : M => Tensor0SNabla.curriedSection I M
        (fun w : M => Tensor0SNabla.curriedSection I M W w (Yf w)) z (Zf z)) y =
      Tensor0SNabla.tensor0Iso I M y
        (Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M W w (Yf w)) y (Zf y)) from rfl]
  rw [← toModel_empty_eq_iso (I := I) (M := M) _ (fun i : Fin 0 => i.elim0)]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SNabla.curriedSection I M W y (Yf y)) (v0 := Zf y)
    (vs := (fun i : Fin 0 => i.elim0))]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := W y) (v0 := Yf y) (vs := Fin.cons (Zf y) (fun i : Fin 0 => i.elim0))]
  exact congrArg _ (funext fun i => by fin_cases i <;> rfl)

lemma curried3_toModel_eval
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y)
    (Bf Cf Df : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SNabla.scalarFn I M
        (fun z : M => Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) w (Cf w)) z (Df z)) y =
      Tensor0SBundle.Tensor0SSpace.toModel (W y) ![Bf y, Cf y, Df y] := by
  rw [show Tensor0SNabla.scalarFn I M
      (fun z : M => Tensor0SNabla.curriedSection I M
        (fun w : M => Tensor0SNabla.curriedSection I M
          (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) w (Cf w)) z (Df z)) y =
      Tensor0SNabla.tensor0Iso I M y
        (Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) w (Cf w)) y (Df y)) from rfl]
  rw [← toModel_empty_eq_iso (I := I) (M := M) _ (fun i : Fin 0 => i.elim0)]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SNabla.curriedSection I M
      (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) y (Cf y)) (v0 := Df y)
    (vs := (fun i : Fin 0 => i.elim0))]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SNabla.curriedSection I M W y (Bf y)) (v0 := Cf y)
    (vs := Fin.cons (Df y) (fun i : Fin 0 => i.elim0))]
  rw [Tensor0SNabla.curriedSection_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := W y) (v0 := Bf y)]
  exact congrArg _ (funext fun i => by fin_cases i <;> rfl)

lemma peel2_core (g : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) 2 W x)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g) W x v)
        ![Yf x, Zf x] =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M W z (Yf z)) y (Zf y))) x v
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![(LeviCivita (I := I) g).toFun (fun y => Yf y) x v, Zf x]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![Yf x, (LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
  classical
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 1 W hW
    Yf v ![Zf x]
  have hWY : TensorSectionMDiffAt (I := I) 1
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Yf y)) x :=
    curried_tsmdiffAt (I := I) (M := M) 1 W hW Yf
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 0
    (fun y : M => Tensor0SNabla.curriedSection I M W y (Yf y)) hWY
    Zf v (fun i : Fin 0 => i.elim0)
  have hcons1 : (Fin.cons (Yf x) ![Zf x] : Fin 2 → TangentSpace I x) = ![Yf x, Zf x] := by
    funext i; fin_cases i <;> rfl
  have hcons2 : (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Yf y) x v) ![Zf x] :
      Fin 2 → TangentSpace I x) =
      ![(LeviCivita (I := I) g).toFun (fun y => Yf y) x v, Zf x] := by
    funext i; fin_cases i <;> rfl
  rw [hcons1, hcons2] at hpeel1
  have hcons3 : (Fin.cons (Zf x) (fun i : Fin 0 => i.elim0) : Fin 1 → TangentSpace I x) =
      ![Zf x] := by
    funext i
    fin_cases i
    rfl
  rw [hcons3] at hpeel2
  have hcorr2 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W x (Yf x))
      (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Zf y) x v) (fun i : Fin 0 => i.elim0)) =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Yf x, (LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
    rw [Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W x) (v0 := Yf x)]
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
  have hd0 : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M W z (Yf z)) y (Zf y)) x v)
      (fun i : Fin 0 => i.elim0) =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
        (fun y : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M W z (Yf z)) y (Zf y))) x v := by
    rw [toModel_empty_eq_iso (I := I) (M := M)]
    exact deriv0_eq_extDeriv (I := I) (M := M) g _ x v
  rw [hpeel1, hpeel2, hcorr2, hd0]
  ring

lemma peel3_core (g : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) 3 W x)
    (Bf Cf Df : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g) W x v)
        ![Bf x, Cf x, Df x] =
      extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M W u (Bf u)) z (Cf z)) y (Df y))) x v
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![(LeviCivita (I := I) g).toFun (fun y => Bf y) x v, Cf x, Df x]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![Bf x, (LeviCivita (I := I) g).toFun (fun y => Cf y) x v, Df x]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![Bf x, Cf x, (LeviCivita (I := I) g).toFun (fun y => Df y) x v] := by
  classical
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 2 W hW
    Bf v ![Cf x, Df x]
  have hWB : TensorSectionMDiffAt (I := I) 2
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Bf y)) x :=
    curried_tsmdiffAt (I := I) (M := M) 2 W hW Bf
  have hcons1 : (Fin.cons (Bf x) ![Cf x, Df x] : Fin 3 → TangentSpace I x) =
      ![Bf x, Cf x, Df x] := by
    funext i; fin_cases i <;> rfl
  have hcons2 : (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Bf y) x v) ![Cf x, Df x] :
      Fin 3 → TangentSpace I x) =
      ![(LeviCivita (I := I) g).toFun (fun y => Bf y) x v, Cf x, Df x] := by
    funext i; fin_cases i <;> rfl
  rw [hcons1, hcons2] at hpeel1
  have hpeelrest := peel2_core (I := I) (M := M) g
    (fun y : M => Tensor0SNabla.curriedSection I M W y (Bf y)) hWB Cf Df v
  have hcorrC : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W x (Bf x))
      ![(LeviCivita (I := I) g).toFun (fun y => Cf y) x v, Df x] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Bf x, (LeviCivita (I := I) g).toFun (fun y => Cf y) x v, Df x] := by
    rw [Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W x) (v0 := Bf x)]
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
  have hcorrD : Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SNabla.curriedSection I M W x (Bf x))
      ![Cf x, (LeviCivita (I := I) g).toFun (fun y => Df y) x v] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Bf x, Cf x, (LeviCivita (I := I) g).toFun (fun y => Df y) x v] := by
    rw [Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W x) (v0 := Bf x)]
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
  rw [hpeel1, hpeelrest, hcorrC, hcorrD]
  ring

lemma bridge02_eval (gA gB : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y) {x : M}
    (hW : TensorSectionMDiffAt (I := I) 2 W x)
    (v p q : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) gA) W x v)
        ![p, q] =
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) gB) W x v)
          ![p, q]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![PDE.DeTurck.connDiff (I := I) gA gB x p v, q]
        - Tensor0SBundle.Tensor0SSpace.toModel (W x)
            ![p, PDE.DeTurck.connDiff (I := I) gA gB x q v] := by
  classical
  obtain ⟨Yf, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x p
  obtain ⟨Zf, hZx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x q
  have hA := peel2_core (I := I) (M := M) gA W hW Yf Zf v
  have hB := peel2_core (I := I) (M := M) gB W hW Yf Zf v
  have hcdY := PDE.DeTurck.connDiff_apply (I := I) gA gB (σ := fun y => Yf y)
    Yf.mdifferentiableAt v
  have hcdZ := PDE.DeTurck.connDiff_apply (I := I) gA gB (σ := fun y => Zf y)
    Zf.mdifferentiableAt v
  have hsplitY : Tensor0SBundle.Tensor0SSpace.toModel (W x)
      ![(LeviCivita (I := I) gA).toFun (fun y => Yf y) x v, Zf x] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![(LeviCivita (I := I) gB).toFun (fun y => Yf y) x v, Zf x]
      + Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![PDE.DeTurck.connDiff (I := I) gA gB x (Yf x) v, Zf x] := by
    have hAB : (LeviCivita (I := I) gA).toFun (fun y => Yf y) x v =
        (LeviCivita (I := I) gB).toFun (fun y => Yf y) x v
          + PDE.DeTurck.connDiff (I := I) gA gB x (Yf x) v := by
      rw [hcdY]; abel
    rw [hAB]
    have hupd : ∀ z : TangentSpace I x,
        (![z, Zf x] : Fin 2 → TangentSpace I x) = Function.update ![0, Zf x] 0 z := by
      intro z
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hupd, hupd ((LeviCivita (I := I) gB).toFun (fun y => Yf y) x v),
      hupd (PDE.DeTurck.connDiff (I := I) gA gB x (Yf x) v)]
    exact ContinuousMultilinearMap.map_update_add _ _ 0 _ _
  have hsplitZ : Tensor0SBundle.Tensor0SSpace.toModel (W x)
      ![Yf x, (LeviCivita (I := I) gA).toFun (fun y => Zf y) x v] =
      Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Yf x, (LeviCivita (I := I) gB).toFun (fun y => Zf y) x v]
      + Tensor0SBundle.Tensor0SSpace.toModel (W x)
        ![Yf x, PDE.DeTurck.connDiff (I := I) gA gB x (Zf x) v] := by
    have hAB : (LeviCivita (I := I) gA).toFun (fun y => Zf y) x v =
        (LeviCivita (I := I) gB).toFun (fun y => Zf y) x v
          + PDE.DeTurck.connDiff (I := I) gA gB x (Zf x) v := by
      rw [hcdZ]; abel
    rw [hAB]
    have hupd : ∀ z : TangentSpace I x,
        (![Yf x, z] : Fin 2 → TangentSpace I x) = Function.update ![Yf x, 0] 1 z := by
      intro z
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hupd, hupd ((LeviCivita (I := I) gB).toFun (fun y => Zf y) x v),
      hupd (PDE.DeTurck.connDiff (I := I) gA gB x (Zf x) v)]
    exact ContinuousMultilinearMap.map_update_add _ _ 1 _ _
  rw [← hYx, ← hZx]
  rw [hA, hB, hsplitY, hsplitZ]
  ring

lemma exists_covector_section_eq (x : M) (β : Tensor0SBundle.Tensor0SSpace 1 I x) :
    ∃ om : Cₛ^(⊤ : ℕ∞)⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E,
        (fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)⟯, om x = β := by
  letI : TopologicalSpace (TotalSpace (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y)) :=
    Tensor0SBundle.tensor0SBundle_topology 1
  letI : FiberBundle (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) := Tensor0SBundle.tensor0SBundle_fiber 1
  letI : VectorBundle ℝ (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) := Tensor0SBundle.tensor0SBundle_vector 1
  letI : ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) (Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) I :=
    Tensor0SBundle.tensor0SBundle_smooth _ 1
  exact ContMDiffSection.exists_eq_at x β

lemma covDerivConnDiff_expand (g₁ g₀ : SmoothRiemannianMetric I M)
    (Xf Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (LeviCivita (I := I) g₀).toFun
        (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) x (Xf x) =
      covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x))
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x)) (Zf x) := by
  have hexpand : covDerivConnDiff (I := I) g₀ g₁
      (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x =
      (LeviCivita (I := I) g₀).toFun
          (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) x (Xf x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x)) (Zf x) := rfl
  rw [hexpand]
  abel

lemma covDerivConnDiff_symm23 (g₁ g₀ : SmoothRiemannianMetric I M)
    (Xf Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x =
      covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Yf y) (fun y => Zf y) x := by
  have h1 : covDerivConnDiff (I := I) g₀ g₁
      (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x =
      (LeviCivita (I := I) g₀).toFun
          (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) x (Xf x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Yf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x)) (Zf x) := rfl
  have h2 : covDerivConnDiff (I := I) g₀ g₁
      (fun y => Xf y) (fun y => Yf y) (fun y => Zf y) x =
      (LeviCivita (I := I) g₀).toFun
          (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Zf y) (Yf y)) x (Xf x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Zf x)
            ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x)) (Yf x) := rfl
  rw [h1, h2]
  have hsec : (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Zf y) (Yf y)) =
      (fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y)) := by
    funext y
    exact PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ y (Zf y) (Yf y)
  rw [hsec]
  rw [PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x (Zf x)
    ((LeviCivita (I := I) g₀).toFun (fun y => Yf y) x (Xf x))]
  rw [PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x
    ((LeviCivita (I := I) g₀).toFun (fun y => Zf y) x (Xf x)) (Yf x)]
  abel

def connDiffVecField (g₁ g₀ : SmoothRiemannianMetric I M)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun y : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y),
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Yf.contMDiff Zf.contMDiff⟩

@[simp] lemma connDiffVecField_apply (g₁ g₀ : SmoothRiemannianMetric I M)
    (Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    connDiffVecField (I := I) (M := M) g₁ g₀ Yf Zf y =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Yf y) (Zf y) := rfl

lemma extDerivFun_sub' {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    extDerivFun (I := I) (f - g) x = extDerivFun (I := I) f x - extDerivFun (I := I) g x := by
  have h := extDerivFun_add (I := I) (g := f - g) (g' := g) (hf.sub hg) hg
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

lemma modelTensorWithCovectorFirst_zero_unit
    (α : Tensor0SBundle.Tensor0SModel 1 ℝ E) :
    Tensor0SBundle.model_tensorWithCovector_first (𝕜 := ℝ) (E := E) 0 α
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) = α := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [Tensor0SBundle.model_tensorWithCovector_first]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, mul_one]
  exact congrArg α (funext fun j => rfl)

lemma connContrCLM_toModel_apply (m k : ℕ) (x : M)
    (B : Tensor0SBundle.TensorRSSpace 1 (k + 1) I x)
    (D : Tensor0SBundle.Tensor0SSpace (m + 1) I x) (u : Fin (m + 1 + k) → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (connContrCLM (I := I) m k x B D) u =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd (k + 1)) *
          (Tensor0SBundle.TensorRSSpace.toModel B
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis i)))
            (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd (m + 1)) := by
  classical
  have h0 : connContrCLM (I := I) m k x B D =
      contractUnitCLM (I := I) (m + 1 + k) x
        (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)) := rfl
  rw [h0]
  set Ψ : Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x :=
    (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
      (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D).comp
        (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)) with hΨ
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
      (contractUnitCLM (I := I) (m + 1 + k) x Ψ) =
      (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 (m + 1 + k)
        (Tensor0SBundle.TensorRSSpace.toModel Ψ))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl
  have hTB : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.TensorRSSpace.toModel Ψ
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i)) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (m + 1) (k + 1)
        (Tensor0SBundle.Tensor0SSpace.toModel D)
        (Tensor0SBundle.TensorRSSpace.toModel B
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i))) := by
    intro i
    set β := Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      ((Module.finBasis ℝ E).cDualBasis i) with hβ
    rw [show β = Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) from
      (Tensor0SBundle.Tensor0SSpace.toModel_ofModel (I := I) (x := x) β).symm]
    rw [← toModel_tensorRS_apply (I := I) 1 (m + 1 + k + 1) x Ψ
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)]
    rw [← toModel_tensorRS_apply (I := I) 1 (k + 1) x B
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)]
    rw [show (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I x from Ψ)
          (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) =
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D)
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)
            (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)) from rfl]
    rw [tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [hA, Tensor0SBundle.model_contract_trace_apply, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SBundle.model_contract_covariant_bilinear_apply,
    Tensor0SBundle.model_contract_contravariant_first_bilinear_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    modelTensorWithCovectorFirst_zero_unit, hTB i]
  exact Bundle.continuousMultilinearMap.modelProduct_apply (m + 1) (k + 1)
    (Tensor0SBundle.Tensor0SSpace.toModel D)
    (Tensor0SBundle.TensorRSSpace.toModel B
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis i)))
    (Fin.cons ((Module.finBasis ℝ E) i) u)

lemma sum_cons_coeff_collapse {n : ℕ} {x : M}
    (D : Tensor0SBundle.Tensor0SSpace (n + 1) I x)
    (w : Fin n → E) (c : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons ((Module.finBasis ℝ E) i) w) * c i) =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Fin.cons (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i) w) := by
  classical
  have hupd : ∀ z : E, (Fin.cons z w : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) w) 0 z := by
    intro z
    rw [Fin.update_cons_zero]
  rw [hupd (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i)]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel D
      (Function.update (Fin.cons (0 : E) w) 0
        (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i)) =
      (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap
        (Function.update (Fin.cons (0 : E) w) 0
          (∑ i : Fin (Module.finrank ℝ E), c i • (Module.finBasis ℝ E) i)) from rfl]
  rw [MultilinearMap.map_update_sum]
  refine (Finset.sum_congr rfl (fun i _ => ?_)).symm
  rw [MultilinearMap.map_update_smul]
  rw [show (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap
      (Function.update (Fin.cons (0 : E) w) 0 ((Module.finBasis ℝ E) i)) =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update (Fin.cons (0 : E) w) 0 ((Module.finBasis ℝ E) i)) from rfl]
  rw [← hupd ((Module.finBasis ℝ E) i)]
  rw [smul_eq_mul, mul_comm]

lemma sum_cons_cDual_collapse {n : ℕ} {x : M}
    (D : Tensor0SBundle.Tensor0SSpace (n + 1) I x) (w : Fin n → E) (V : E) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons ((Module.finBasis ℝ E) i) w) *
          ((Module.finBasis ℝ E).cDualBasis i) V) =
      Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons V w) := by
  classical
  have hV : (∑ i : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis i) V • (Module.finBasis ℝ E) i) = V := by
    have hci : ∀ i : Fin (Module.finrank ℝ E),
        ((Module.finBasis ℝ E).cDualBasis i) V = (Module.finBasis ℝ E).repr V i := by
      intro i
      rw [cDualBasis_eq_coord]
      rfl
    rw [show (∑ i : Fin (Module.finrank ℝ E),
        ((Module.finBasis ℝ E).cDualBasis i) V • (Module.finBasis ℝ E) i) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr V i) • (Module.finBasis ℝ E) i from
      Finset.sum_congr rfl (fun i _ => by rw [hci i])]
    exact (Module.finBasis ℝ E).sum_repr V
  rw [sum_cons_coeff_collapse (I := I) (M := M) D w
    (fun i => ((Module.finBasis ℝ E).cDualBasis i) V), hV]

lemma connDiff_model_coeff (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (w : Fin 2 → E) :
    (Tensor0SBundle.TensorRSSpace.toModel
        (show Tensor0SBundle.TensorRSSpace 1 2 I x from
          (connDiffSection (I := I) g₁ g₀).toSection x)
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i))) w =
      ((Module.finBasis ℝ E).cDualBasis i)
        ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((w 0 : E)) ((w 1 : E)) : TangentSpace I x) : E) := by
  classical
  set β := Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
    ((Module.finBasis ℝ E).cDualBasis i) with hβdef
  have h1 : Tensor0SBundle.TensorRSSpace.toModel
      (show Tensor0SBundle.TensorRSSpace 1 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) β =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (connDiffSection (I := I) g₁ g₀).toSection x)
          (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)) := by
    rw [toModel_tensorRS_apply (I := I) 1 2 x _
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β),
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [h1]
  rw [show (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      (connDiffSection (I := I) g₁ g₀).toSection x)
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) =
      connDiffPairing (I := I) g₁ g₀ x
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β) from rfl]
  rw [toModel_apply_tangent (I := I) (M := M) x _ (fun j => ((w j : E) : TangentSpace I x))]
  rw [show (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
      connDiffPairing (I := I) g₁ g₀ x
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β))
      (fun j => ((w j : E) : TangentSpace I x)) =
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
        (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((w 0 : E)) ((w 1 : E))) from rfl]
  rw [show (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
      (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((w 0 : E)) ((w 1 : E))) =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
        (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((w 0 : E)) ((w 1 : E)) : TangentSpace I x) : E)) from rfl]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [hβdef, Tensor0SBundle.model_covectorOfCLM_apply]

private lemma consCast21 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.castAdd 2 : Fin 3 → E) = ![z, u 0, u 1] := by
  funext j
  fin_cases j <;> rfl

private lemma consNat21 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.natAdd 3 : Fin 2 → E) = ![u 2, u 3] := by
  funext j
  fin_cases j <;> rfl

private lemma consCast11 (z : E) (u : Fin 3 → E) :
    (Fin.cons z u ∘ Fin.castAdd 2 : Fin 2 → E) = ![z, u 0] := by
  funext j
  fin_cases j <;> rfl

private lemma consNat11 (z : E) (u : Fin 3 → E) :
    (Fin.cons z u ∘ Fin.natAdd 2 : Fin 2 → E) = ![u 1, u 2] := by
  funext j
  fin_cases j <;> rfl

private lemma consCast12 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.castAdd 3 : Fin 2 → E) = ![z, u 0] := by
  funext j
  fin_cases j <;> rfl

private lemma consNat12 (z : E) (u : Fin 4 → E) :
    (Fin.cons z u ∘ Fin.natAdd 2 : Fin 3 → E) = ![u 1, u 2, u 3] := by
  funext j
  fin_cases j <;> rfl

lemma connContr21_insert (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) (u : Fin 4 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 2 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) u =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 2 : E)) ((u 3 : E)) :
            TangentSpace I x) : E), u 0, u 1] := by
  classical
  rw [connContrCLM_toModel_apply (I := I) (M := M) 2 1 x _ D u]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd 2) *
        (Tensor0SBundle.TensorRSSpace.toModel
            (show Tensor0SBundle.TensorRSSpace 1 2 I x from
              (connDiffSection (I := I) g₁ g₀).toSection x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd 3) =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) ![u 0, u 1]) *
        ((Module.finBasis ℝ E).cDualBasis i)
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 2 : E)) ((u 3 : E)) :
            TangentSpace I x) : E) := by
    intro i
    rw [consCast21, consNat21, connDiff_model_coeff (I := I) (M := M) g₁ g₀ x i (![u 2, u 3])]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [sum_cons_cDual_collapse (I := I) (M := M) D ![u 0, u 1]
    ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 2 : E)) ((u 3 : E)) : TangentSpace I x) : E)]
  rfl

lemma connContr11_insert (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (u : Fin 3 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 1 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) u =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) :
            TangentSpace I x) : E), u 0] := by
  classical
  rw [connContrCLM_toModel_apply (I := I) (M := M) 1 1 x _ D u]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd 2) *
        (Tensor0SBundle.TensorRSSpace.toModel
            (show Tensor0SBundle.TensorRSSpace 1 2 I x from
              (connDiffSection (I := I) g₁ g₀).toSection x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd 2) =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) ![u 0]) *
        ((Module.finBasis ℝ E).cDualBasis i)
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) :
            TangentSpace I x) : E) := by
    intro i
    rw [consCast11, consNat11, connDiff_model_coeff (I := I) (M := M) g₁ g₀ x i (![u 1, u 2])]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [sum_cons_cDual_collapse (I := I) (M := M) D ![u 0]
    ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x ((u 1 : E)) ((u 2 : E)) : TangentSpace I x) : E)]
  rfl

def rs13ContrVec (x : M) (B : Tensor0SBundle.TensorRSSpace 1 3 I x)
    (q : Fin 3 → E) : E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((Tensor0SBundle.TensorRSSpace.toModel B
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i))) q) • (Module.finBasis ℝ E) i

lemma connContr12_insert (x : M) (B : Tensor0SBundle.TensorRSSpace 1 3 I x)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (u : Fin 4 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (connContrCLM (I := I) 1 2 x B D) u =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![rs13ContrVec (I := I) (M := M) x B ![u 1, u 2, u 3], u 0] := by
  classical
  rw [connContrCLM_toModel_apply (I := I) (M := M) 1 2 x B D u]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.castAdd 3) *
        (Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i)))
          (Fin.cons ((Module.finBasis ℝ E) i) u ∘ Fin.natAdd 2) =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Fin.cons ((Module.finBasis ℝ E) i) ![u 0]) *
        ((Tensor0SBundle.TensorRSSpace.toModel B
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis i))) ![u 1, u 2, u 3]) := by
    intro i
    rw [consCast12, consNat12]
    rw [show (![((Module.finBasis ℝ E) i : E), u 0] : Fin 2 → E) =
        Fin.cons ((Module.finBasis ℝ E) i) ![u 0] from
      funext fun j => by fin_cases j <;> rfl]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [sum_cons_coeff_collapse (I := I) (M := M) D ![u 0]
    (fun i => (Tensor0SBundle.TensorRSSpace.toModel B
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis i))) ![u 1, u 2, u 3])]
  rfl

lemma rs13ContrVec_covGrad_eq (g₁ g₀ : SmoothRiemannianMetric I M)
    (Xf Yf Zf : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    rs13ContrVec (I := I) (M := M) x
        (show Tensor0SBundle.TensorRSSpace 1 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
        ![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] =
      ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
        TangentSpace I x) : E) := by
  classical
  have hcoeff : ∀ i : Fin (Module.finrank ℝ E),
      (Tensor0SBundle.TensorRSSpace.toModel
          (show Tensor0SBundle.TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)))
        ![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] =
      ((Module.finBasis ℝ E).cDualBasis i)
        ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
          TangentSpace I x) : E) := by
    intro i
    set β := Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      ((Module.finBasis ℝ E).cDualBasis i) with hβdef
    obtain ⟨om, homx⟩ := exists_covector_section_eq (I := I) (M := M) x
      (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
    have h1 : Tensor0SBundle.TensorRSSpace.toModel
        (show Tensor0SBundle.TensorRSSpace 1 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x) β =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            (om x)) := by
      rw [homx]
      rw [toModel_tensorRS_apply (I := I) 1 3 x _
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β),
        Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [h1]
    have h2 := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) (M := M) g₁ g₀ om Xf Yf Zf x
    rw [show (Fin.cons (Xf x) (Fin.cons (Yf x) ![Zf x]) : Fin 3 → TangentSpace I x) =
        (fun j => (![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] j : TangentSpace I x)) from by
      funext j
      fin_cases j <;> rfl] at h2
    rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          (om x))
        ![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
          ((Zf x : TangentSpace I x) : E)] =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            (om x))
          (fun j => (![((Xf x : TangentSpace I x) : E), ((Yf x : TangentSpace I x) : E),
            ((Zf x : TangentSpace I x) : E)] j : TangentSpace I x)) from rfl]
    rw [h2, homx]
    rw [show (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
        (fun _ : Fin 1 => covDerivConnDiff (I := I) g₀ g₁
          (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x) β)
          (fun _ : Fin 1 => ((covDerivConnDiff (I := I) g₀ g₁
            (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x : TangentSpace I x) : E)) from rfl]
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [hβdef, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [rs13ContrVec]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hcoeff i])]
  have hci : ∀ i : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis i)
        ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
          TangentSpace I x) : E) =
      (Module.finBasis ℝ E).repr
        ((covDerivConnDiff (I := I) g₀ g₁ (fun y => Xf y) (fun y => Zf y) (fun y => Yf y) x :
          TangentSpace I x) : E) i := by
    intro i
    rw [cDualBasis_eq_coord]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => by rw [hci i])]
  exact (Module.finBasis ℝ E).sum_repr _

private lemma slotPerm4_0312_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0312 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, d, b, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_0213_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0213 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, c, b, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_2301_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_2301 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![c, d, a, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_1302_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_1302 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, d, a, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_1203_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_1203 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, c, a, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_3201_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_3201 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![d, c, a, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_3102_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_3102 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![d, b, a, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_2103_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_2103 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![c, b, a, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_3012_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_3012 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![d, a, b, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_2013_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_2013 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![c, a, b, d] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_0231_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0231 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, c, d, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm4_0321_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x)
    (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm4_0321 x D) ![a, b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![a, d, c, b] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm3_102_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (a b c : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm3_102 x D) ![a, b, c] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, a, c] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm3_120_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 3 I x)
    (a b c : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm3_120 x D) ![a, b, c] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, c, a] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

private lemma slotPerm2_10_toModel (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x)
    (a b : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotPermCLM (I := I) perm2_10 x D) ![a, b] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![b, a] := by
  rw [slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

lemma connContr21_insert' (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) (p q r s : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 2 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) ![p, q, r, s] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s, p, q] :=
  connContr21_insert (I := I) (M := M) g₁ g₀ x D ![p, q, r, s]

lemma connContr11_insert' (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (p q r : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (connContrCLM (I := I) 1 1 x
          ((connDiffSection (I := I) g₁ g₀).toSection x) D) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x q r, p] :=
  connContr11_insert (I := I) (M := M) g₁ g₀ x D ![p, q, r]

lemma connContr12_insert' (x : M) (B : Tensor0SBundle.TensorRSSpace 1 3 I x)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (p q r s : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (connContrCLM (I := I) 1 2 x B D) ![p, q, r, s] =
      Tensor0SBundle.Tensor0SSpace.toModel D
        ![rs13ContrVec (I := I) (M := M) x B ![q, r, s], p] :=
  connContr12_insert (I := I) (M := M) x B D ![p, q, r, s]

private lemma order1CLM_toModel_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (Z : Tensor0SBundle.Tensor0SSpace 3 I x) (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x) Z) ![a, b, c, d] =
      -(Tensor0SBundle.Tensor0SSpace.toModel Z
          ![a, PDE.DeTurck.connDiff (I := I) g₁ g₀ x b c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![a, c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x b d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b, c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![b, PDE.DeTurck.connDiff (I := I) g₁ g₀ x a c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel Z
            ![b, c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x a d]) := by
  rw [linearizedRicciConnDiffOrder1CLM]
  rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_neg, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [slotPerm4_0312_toModel, slotPerm4_0213_toModel, slotPerm4_2301_toModel,
    slotPerm4_1302_toModel, slotPerm4_1203_toModel]
  rw [connContr21_insert', connContr21_insert', connContr21_insert',
    connContr21_insert', connContr21_insert']
  rw [slotPerm3_102_toModel, slotPerm3_120_toModel, slotPerm3_102_toModel,
    slotPerm3_120_toModel]

private lemma order0CLM_toModel_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (hT : Tensor0SBundle.Tensor0SSpace 2 I x) (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
          hT) ![a, b, c, d] =
      (Tensor0SBundle.Tensor0SSpace.toModel hT
          ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x b
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a c), d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x a c,
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x b d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![PDE.DeTurck.connDiff (I := I) g₁ g₀ x b c,
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x a d]
        + Tensor0SBundle.Tensor0SSpace.toModel hT
            ![c, PDE.DeTurck.connDiff (I := I) g₁ g₀ x b
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a d)])
      - Tensor0SBundle.Tensor0SSpace.toModel hT
          ![rs13ContrVec (I := I) (M := M) x
            ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            ![a, b, c], d]
      - Tensor0SBundle.Tensor0SSpace.toModel hT
          ![c, rs13ContrVec (I := I) (M := M) x
            ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            (![a, b, d])] := by
  rw [linearizedRicciConnDiffOrder0CLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply]
  simp only [Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  rw [slotPerm4_3201_toModel, slotPerm4_2301_toModel, slotPerm4_3102_toModel,
    slotPerm4_1302_toModel, slotPerm4_1203_toModel, slotPerm4_2103_toModel,
    slotPerm4_3012_toModel, slotPerm4_2013_toModel]
  rw [connContr21_insert', connContr21_insert', connContr21_insert',
    connContr21_insert', connContr21_insert', connContr21_insert']
  rw [connContr12_insert', connContr12_insert']
  rw [slotPerm3_102_toModel, slotPerm3_102_toModel, slotPerm3_120_toModel,
    slotPerm3_120_toModel]
  rw [connContr11_insert', connContr11_insert', connContr11_insert',
    connContr11_insert', connContr11_insert', connContr11_insert']
  rw [slotPerm2_10_toModel, slotPerm2_10_toModel, slotPerm2_10_toModel,
    slotPerm2_10_toModel]

lemma covGradUnit_toModel_eval (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) (y : M) (p : TangentSpace I y)
    (w : Fin n → TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (n + 1) I y from
          (covGrad (I := I) (M := M) g 0 n W).toSection y)
          (unitZeroSec (I := I) (M := M) y))
        (Fin.cons p w) =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g)
          (fun z : M =>
            (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ]
                Tensor0SBundle.Tensor0SSpace n I z from
              W.toSection z) (unitZeroSec (I := I) (M := M) z)) y p) w := by
  have h := unitModel_covGrad_eval (I := I) (M := M) g n W y (Fin.cons p w)
  rw [show unitModel (I := I) (M := M) g (n + 1) (covGrad (I := I) (M := M) g 0 n W) y
      (Fin.cons p w) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (n + 1) I y from
          (covGrad (I := I) (M := M) g 0 n W).toSection y)
          (unitZeroSec (I := I) (M := M) y))
        (Fin.cons p w) from rfl] at h
  rw [h]
  rw [show (Fin.cons p w : Fin (n + 1) → TangentSpace I y) 0 = p from rfl]
  rw [show Matrix.vecTail (Fin.cons p w : Fin (n + 1) → TangentSpace I y) = w from
    Matrix.tail_cons p w]

private def hUnitSec (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y :=
  fun y : M =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
      (symmS (I := I) (M := M) g₀ (T - T')).toSection y) (unitZeroSec (I := I) (M := M) y)

private lemma hUnitSec_tsmdiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (y : M) :
    TensorSectionMDiffAt (I := I) 2 (hUnitSec (I := I) (M := M) g₀ T T') y :=
  unitEval_tensorSectionMDiffAt (I := I) (M := M) g₀ 2
    (symmS (I := I) (M := M) g₀ (T - T')) y

private def kZeroSec (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y :=
  fun y : M =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
      (covGrad (I := I) (M := M) g₀ 0 2
        (symmS (I := I) (M := M) g₀ (T - T'))).toSection y)
      (unitZeroSec (I := I) (M := M) y)

private lemma kZeroSec_tsmdiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (y : M) :
    TensorSectionMDiffAt (I := I) 3 (kZeroSec (I := I) (M := M) g₀ T T') y :=
  unitEval_tensorSectionMDiffAt (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) (M := M) g₀ (T - T'))) y

private def kOneSec (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : Π y : M, Tensor0SBundle.Tensor0SSpace 3 I y :=
  fun y : M =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I y from
      (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection y)
      (unitZeroSec (I := I) (M := M) y)

private lemma kOneSec_tsmdiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) :
    TensorSectionMDiffAt (I := I) 3 (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s) y :=
  unitEval_tensorSectionMDiffAt (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
    (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) y

private lemma kZeroSec_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (y : M) (p q r : TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel (kZeroSec (I := I) (M := M) g₀ T T' y) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (hUnitSec (I := I) (M := M) g₀ T T') y p) ![q, r] := by
  have h := covGradUnit_toModel_eval (I := I) (M := M) g₀ 2
    (symmS (I := I) (M := M) g₀ (T - T')) y p ![q, r]
  rw [show (Fin.cons p ![q, r] : Fin 3 → TangentSpace I y) = ![p, q, r] from
    funext fun j => by fin_cases j <;> rfl] at h
  exact h

private lemma kOneSec_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) (p q r : TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s y) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2
          (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (hUnitSec (I := I) (M := M) g₀ T T') y p) ![q, r] := by
  have h := covGradUnit_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) 2
    (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s) y p ![q, r]
  rw [show (Fin.cons p ![q, r] : Fin 3 → TangentSpace I y) = ![p, q, r] from
    funext fun j => by fin_cases j <;> rfl] at h
  rw [show (fun z : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I z from
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s).toSection z)
        (unitZeroSec (I := I) (M := M) z)) =
      hUnitSec (I := I) (M := M) g₀ T T' from rfl] at h
  exact h

private lemma kSec_bridge (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (y : M) (p q r : TangentSpace I y) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s y) ![p, q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel (kZeroSec (I := I) (M := M) g₀ T T' y) ![p, q, r]
        - Tensor0SBundle.Tensor0SSpace.toModel (hUnitSec (I := I) (M := M) g₀ T T' y)
            ![PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y q p, r]
        - Tensor0SBundle.Tensor0SSpace.toModel (hUnitSec (I := I) (M := M) g₀ T T' y)
            ![q, PDE.DeTurck.connDiff (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y r p] := by
  rw [kOneSec_eval (I := I) (M := M) g₀ T T' hδ hδ' s y p q r,
    kZeroSec_eval (I := I) (M := M) g₀ T T' y p q r]
  exact bridge02_eval (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    (hUnitSec (I := I) (M := M) g₀ T T')
    (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' y) p q r

private lemma velFibre_toModel_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3
          (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s) x (m 0)) ![m 1, m 2, m 3] := by
  have hm : m = Fin.cons (m 0) ![m 1, m 2, m 3] := by
    funext j
    fin_cases j <;> rfl
  have h := covGradUnit_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) 3
    (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)) x (m 0) ![m 1, m 2, m 3]
  rw [show (fun z : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I z from
        (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s)).toSection z)
        (unitZeroSec (I := I) (M := M) z)) =
      kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s from rfl] at h
  rw [show unitModel (I := I) (M := M) g₀ 4
      (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 3
            (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 2
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s))).toSection x)
          (unitZeroSec (I := I) (M := M) x)) m from rfl]
  conv_lhs => rw [hm]
  exact h

private lemma w2Fibre_toModel_eval (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
          (kZeroSec (I := I) (M := M) g₀ T T') x (m 0)) ![m 1, m 2, m 3] := by
  have hm : m = Fin.cons (m 0) ![m 1, m 2, m 3] := by
    funext j
    fin_cases j <;> rfl
  have h := covGradUnit_toModel_eval (I := I) (M := M) g₀ 3
    (covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) (M := M) g₀ (T - T')))
    x (m 0) ![m 1, m 2, m 3]
  rw [show (fun z : M =>
      (show Tensor0SBundle.Tensor0SSpace 0 I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I z from
        (covGrad (I := I) (M := M) g₀ 0 2
          (symmS (I := I) (M := M) g₀ (T - T'))).toSection z)
        (unitZeroSec (I := I) (M := M) z)) =
      kZeroSec (I := I) (M := M) g₀ T T' from rfl] at h
  rw [show unitModel (I := I) (M := M) g₀ 4
      (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (covGrad (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2
              (symmS (I := I) (M := M) g₀ (T - T')))).toSection x)
          (unitZeroSec (I := I) (M := M) x)) m from rfl]
  conv_lhs => rw [hm]
  exact h

lemma toModel3_add_slot0 {x : M} (T : Tensor0SBundle.Tensor0SSpace 3 I x)
    (p p' q r : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p + p', q, r] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p', q, r] := by
  have hupd : ∀ z : TangentSpace I x,
      (![z, q, r] : Fin 3 → TangentSpace I x) = Function.update ![0, q, r] 0 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (p + p'), hupd p, hupd p']
  exact ContinuousMultilinearMap.map_update_add _ _ 0 _ _

lemma toModel3_add_slot1 {x : M} (T : Tensor0SBundle.Tensor0SSpace 3 I x)
    (p q q' r : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p, q + q', r] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p, q', r] := by
  have hupd : ∀ z : TangentSpace I x,
      (![p, z, r] : Fin 3 → TangentSpace I x) = Function.update ![p, 0, r] 1 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (q + q'), hupd q, hupd q']
  exact ContinuousMultilinearMap.map_update_add _ _ 1 _ _

lemma toModel3_add_slot2 {x : M} (T : Tensor0SBundle.Tensor0SSpace 3 I x)
    (p q r r' : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r + r'] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p, q, r'] := by
  have hupd : ∀ z : TangentSpace I x,
      (![p, q, z] : Fin 3 → TangentSpace I x) = Function.update ![p, q, 0] 2 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (r + r'), hupd r, hupd r']
  exact ContinuousMultilinearMap.map_update_add _ _ 2 _ _

lemma toModel2_add_slot0 {x : M} (T : Tensor0SBundle.Tensor0SSpace 2 I x)
    (p p' q : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p + p', q] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p', q] := by
  have hupd : ∀ z : TangentSpace I x,
      (![z, q] : Fin 2 → TangentSpace I x) = Function.update ![0, q] 0 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (p + p'), hupd p, hupd p']
  exact ContinuousMultilinearMap.map_update_add _ _ 0 _ _

lemma toModel2_add_slot1 {x : M} (T : Tensor0SBundle.Tensor0SSpace 2 I x)
    (p q q' : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel T ![p, q + q'] =
      Tensor0SBundle.Tensor0SSpace.toModel T ![p, q]
        + Tensor0SBundle.Tensor0SSpace.toModel T ![p, q'] := by
  have hupd : ∀ z : TangentSpace I x,
      (![p, z] : Fin 2 → TangentSpace I x) = Function.update ![p, 0] 1 z := by
    intro z
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hupd (q + q'), hupd q, hupd q']
  exact ContinuousMultilinearMap.map_update_add _ _ 1 _ _

set_option maxHeartbeats 3200000 in

private theorem kOneSec_deriv_eq_threeArm_kernel (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (a b c d : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3
          (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s) x a) ![b, c, d] =
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
            (kZeroSec (I := I) (M := M) g₀ T T') x a) ![b, c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel
            (linearizedRicciConnDiffOrder1CLM (I := I) x
              ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
              (kZeroSec (I := I) (M := M) g₀ T T' x)) ![a, b, c, d]
        + Tensor0SBundle.Tensor0SSpace.toModel
            (linearizedRicciConnDiffOrder0CLM (I := I) x
              ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
              ((covGrad (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
              (hUnitSec (I := I) (M := M) g₀ T T' x)) ![a, b, c, d] := by
  classical
  obtain ⟨Af, hAx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x a
  obtain ⟨Bf, hBx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x b
  obtain ⟨Cf, hCx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x c
  obtain ⟨Df, hDx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x d
  rw [← hAx, ← hBx, ← hCx, ← hDx]
  have hL := peel3_core (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s)
    (kOneSec_tsmdiffAt (I := I) (M := M) g₀ T T' hδ hδ' s x) Bf Cf Df (Af x)
  have hR := peel3_core (I := I) (M := M) g₀
    (kZeroSec (I := I) (M := M) g₀ T T')
    (kZeroSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Bf Cf Df (Af x)
  have hDB : (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
      (fun y => Bf y) x (Af x) =
      (LeviCivita (I := I) g₀).toFun (fun y => Bf y) x (Af x)
        + PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
            (Bf x) (Af x) := by
    rw [PDE.DeTurck.connDiff_apply (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
      (σ := fun y => Bf y) Bf.mdifferentiableAt (Af x)]
    abel
  have hDC : (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
      (fun y => Cf y) x (Af x) =
      (LeviCivita (I := I) g₀).toFun (fun y => Cf y) x (Af x)
        + PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
            (Cf x) (Af x) := by
    rw [PDE.DeTurck.connDiff_apply (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
      (σ := fun y => Cf y) Cf.mdifferentiableAt (Af x)]
    abel
  have hDD : (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)).toFun
      (fun y => Df y) x (Af x) =
      (LeviCivita (I := I) g₀).toFun (fun y => Df y) x (Af x)
        + PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
            (Df x) (Af x) := by
    rw [PDE.DeTurck.connDiff_apply (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
      (σ := fun y => Df y) Df.mdifferentiableAt (Af x)]
    abel
  rw [hDB, hDC, hDD, toModel3_add_slot0, toModel3_add_slot1, toModel3_add_slot2] at hL
  rw [kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      ((LeviCivita (I := I) g₀).toFun (fun y => Bf y) x (Af x)) (Cf x) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Bf x) (Af x)) (Cf x) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) ((LeviCivita (I := I) g₀).toFun (fun y => Cf y) x (Af x)) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Cf x) (Af x)) (Df x),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) (Cf x) ((LeviCivita (I := I) g₀).toFun (fun y => Df y) x (Af x)),
    kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s x
      (Bf x) (Cf x) (PDE.DeTurck.connDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Df x) (Af x))] at hL
  have hexpC1 := peel2_core (I := I) (M := M) g₀
    (hUnitSec (I := I) (M := M) g₀ T T')
    (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x)
    (connDiffVecField (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf)
    Df (Af x)
  have hexpC2 := peel2_core (I := I) (M := M) g₀
    (hUnitSec (I := I) (M := M) g₀ T T')
    (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Cf
    (connDiffVecField (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf)
    (Af x)
  rw [show (fun y : M =>
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) y) =
      (fun y : M => PDE.DeTurck.connDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y (Cf y) (Bf y)) from rfl] at hexpC1
  rw [covDerivConnDiff_expand (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Cf Bf x] at hexpC1
  rw [show ((connDiffVecField (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) x : TangentSpace I x) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Cf x) (Bf x) from rfl] at hexpC1
  rw [toModel2_add_slot0, toModel2_add_slot0] at hexpC1
  rw [← kZeroSec_eval (I := I) (M := M) g₀ T T' x (Af x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Cf x) (Bf x)) (Df x)] at hexpC1
  rw [show (fun y : M =>
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y) =
      (fun y : M => PDE.DeTurck.connDiff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y (Df y) (Bf y)) from rfl] at hexpC2
  rw [covDerivConnDiff_expand (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Df Bf x] at hexpC2
  rw [show ((connDiffVecField (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) x : TangentSpace I x) =
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (Df x) (Bf x) from rfl] at hexpC2
  rw [toModel2_add_slot1, toModel2_add_slot1] at hexpC2
  rw [← kZeroSec_eval (I := I) (M := M) g₀ T T' x (Af x) (Cf x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Df x) (Bf x))] at hexpC2
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Bf x) (Af x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Cf x) (Af x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Df x) (Af x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Cf x) (Bf x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Cf x) (Bf x)] at hexpC1
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Df x) (Bf x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    x (Df x) (Bf x)] at hexpC2
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Cf x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Bf x))] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x (Df x)
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Bf x))] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Cf x)) (Bf x)] at hL
  rw [PDE.DeTurck.connDiff_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
      (Af x) (Df x)) (Bf x)] at hL
  rw [covDerivConnDiff_symm23 (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Cf Bf x] at hexpC1
  rw [covDerivConnDiff_symm23 (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Df Bf x] at hexpC2
  have hscal : ∀ y : M,
      Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s) u (Bf u)) z (Cf z)) y' (Df y')) y =
      Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (kZeroSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y')) y
        - Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (hUnitSec (I := I) (M := M) g₀ T T') z
                ((connDiffVecField (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y')) y
        - Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (hUnitSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
              ((connDiffVecField (I := I) (M := M)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y')) y := by
    intro y
    rw [curried3_toModel_eval (I := I) (M := M)
      (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s) Bf Cf Df y]
    rw [curried3_toModel_eval (I := I) (M := M)
      (kZeroSec (I := I) (M := M) g₀ T T') Bf Cf Df y]
    rw [curried2_toModel_eval (I := I) (M := M)
      (hUnitSec (I := I) (M := M) g₀ T T')
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) Df y]
    rw [curried2_toModel_eval (I := I) (M := M)
      (hUnitSec (I := I) (M := M) g₀ T T') Cf
      (connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y]
    rw [show ((connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) y : TangentSpace I y) =
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y
          (Cf y) (Bf y) from rfl]
    rw [show ((connDiffVecField (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y : TangentSpace I y) =
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ y
          (Df y) (Bf y) from rfl]
    rw [kSec_bridge (I := I) (M := M) g₀ T T' hδ hδ' s y (Bf y) (Cf y) (Df y)]
  have hMD0 : MDifferentiableAt I 𝓘(ℝ)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (kZeroSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y'))) x :=
    (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section I M _).mpr
      (curried_tsmdiffAt (I := I) (M := M) 0 _
        (curried_tsmdiffAt (I := I) (M := M) 1 _
          (curried_tsmdiffAt (I := I) (M := M) 2 _
            (kZeroSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Bf) Cf) Df)
  have hMDC1 : MDifferentiableAt I 𝓘(ℝ)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (hUnitSec (I := I) (M := M) g₀ T T') z
            ((connDiffVecField (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y'))) x :=
    (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section I M _).mpr
      (curried_tsmdiffAt (I := I) (M := M) 0 _
        (curried_tsmdiffAt (I := I) (M := M) 1 _
          (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x)
          (connDiffVecField (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf)) Df)
  have hMDC2 : MDifferentiableAt I 𝓘(ℝ)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (hUnitSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
          ((connDiffVecField (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y'))) x :=
    (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section I M _).mpr
      (curried_tsmdiffAt (I := I) (M := M) 0 _
        (curried_tsmdiffAt (I := I) (M := M) 1 _
          (hUnitSec_tsmdiffAt (I := I) (M := M) g₀ T T' x) Cf)
        (connDiffVecField (I := I) (M := M)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf))
  have hExt : extDerivFun (I := I)
      (Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s) u (Bf u)) z (Cf z)) y' (Df y'))) x
        (Af x) =
      extDerivFun (I := I)
        (Tensor0SNabla.scalarFn I M
          (fun y' : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M
                (kZeroSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y'))) x (Af x)
      - extDerivFun (I := I)
          (Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (hUnitSec (I := I) (M := M) g₀ T T') z
                ((connDiffVecField (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y'))) x (Af x)
      - extDerivFun (I := I)
          (Tensor0SNabla.scalarFn I M
            (fun y' : M => Tensor0SNabla.curriedSection I M
              (fun z : M => Tensor0SNabla.curriedSection I M
                (hUnitSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
              ((connDiffVecField (I := I) (M := M)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y'))) x (Af x) := by
    have hfx : Tensor0SNabla.scalarFn I M
        (fun y' : M => Tensor0SNabla.curriedSection I M
          (fun z : M => Tensor0SNabla.curriedSection I M
            (fun u : M => Tensor0SNabla.curriedSection I M
              (kOneSec (I := I) (M := M) g₀ T T' hδ hδ' s) u (Bf u)) z (Cf z)) y' (Df y')) =
        (Tensor0SNabla.scalarFn I M
          (fun y' : M => Tensor0SNabla.curriedSection I M
            (fun z : M => Tensor0SNabla.curriedSection I M
              (fun u : M => Tensor0SNabla.curriedSection I M
                (kZeroSec (I := I) (M := M) g₀ T T') u (Bf u)) z (Cf z)) y' (Df y'))
          - Tensor0SNabla.scalarFn I M
              (fun y' : M => Tensor0SNabla.curriedSection I M
                (fun z : M => Tensor0SNabla.curriedSection I M
                  (hUnitSec (I := I) (M := M) g₀ T T') z
                  ((connDiffVecField (I := I) (M := M)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Cf Bf) z)) y' (Df y')))
          - Tensor0SNabla.scalarFn I M
              (fun y' : M => Tensor0SNabla.curriedSection I M
                (fun z : M => Tensor0SNabla.curriedSection I M
                  (hUnitSec (I := I) (M := M) g₀ T T') z (Cf z)) y'
                ((connDiffVecField (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Df Bf) y')) := by
      funext y
      have h := hscal y
      rw [h]
      rfl
    rw [hfx]
    rw [extDerivFun_sub' (I := I) (hMD0.sub hMDC1) hMDC2,
      extDerivFun_sub' (I := I) hMD0 hMDC1]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  have hE1 := order1CLM_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (kZeroSec (I := I) (M := M) g₀ T T' x) (Af x) (Bf x) (Cf x) (Df x)
  have hE0 := order0CLM_toModel_eval (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
    (hUnitSec (I := I) (M := M) g₀ T T' x) (Af x) (Bf x) (Cf x) (Df x)
  rw [rs13ContrVec_covGrad_eq (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Bf Cf x,
    rs13ContrVec_covGrad_eq (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ Af Bf Df x] at hE0
  linarith [hL, hR, hExt, hexpC1, hexpC2, hE1, hE0]

private lemma lichnerowiczFib_toModel_eq_fourTrace (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (P : Tensor0SBundle.Tensor0SSpace 4 I x)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x) P) v =
      Tensor0SBundle.Tensor0SSpace.toModel
        (ricciCometricFourTraceCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) x P) v := by
  classical
  have hsplit : (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x) P =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P
      - (1 / 2 : ℝ) •
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P) := by
    rw [show (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)
          - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl]
    have hts : ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x :
        Tensor0SBundle.TensorRSSpace 4 2 I x) =
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x
          - (1 / 2 : ℝ) • (traceHessianCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x := by
      rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
    rw [hts]
    rfl
  rw [hsplit]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      (ricciArmPrincipalCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P =
      ricciArmPrincipalCoeffFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x P from rfl]
  rw [ricciArmPrincipalCoeffFib_toModel,
    combinedTrace42Model_apply (E := E)
      (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)]
  rw [show (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      (traceHessianCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) P =
      traceHessianFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x P from rfl]
  rw [traceHessianFib_toModel,
    modelDoubleTrace_apply (E := E) 2
      (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)]
  rw [ricciCometricFourTraceCLM]
  rw [ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply]
  rw [cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel,
    cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel]
  rw [slotPermCLM_apply, slotPermCLM_apply, slotPermCLM_apply]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [modelDoubleTrace_apply, modelDoubleTrace_apply, modelDoubleTrace_apply,
    modelDoubleTrace_apply]
  have h0231 : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr perm4_0231
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ![v 0, v 1, (Module.finBasis ℝ E) k]) := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  have h0321 : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr perm4_0321
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ![v 1, v 0, (Module.finBasis ℝ E) k]) := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  have h2301 : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr perm4_2301
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        ![v 0, v 1,
          cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k] := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  have hth : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel P)
        (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v)) =
      Tensor0SBundle.Tensor0SSpace.toModel P
        ![v 0, v 1,
          cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k] := by
    intro k
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (funext fun j => by fin_cases j <;> rfl)
  rw [Finset.sum_congr rfl (fun k _ => h0231 k), Finset.sum_congr rfl (fun k _ => h0321 k),
    Finset.sum_congr rfl (fun k _ => h2301 k), Finset.sum_congr rfl (fun k _ => hth k)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

set_option maxRecDepth 16000 in
set_option linter.unusedVariables false in
set_option linter.style.show false in

private theorem lichnerowicz_velocitySecondCovGrad_eq_threeArm_symm
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))) x v
        + unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 3 2
              (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))) x v
        + unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v := by
  classical
  have hVel : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 4 I x from
      (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 4 I x from
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
        (unitTensor (I := I) (M := M) x)
      + linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          (kZeroSec (I := I) (M := M) g₀ T T' x)
      + linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
          (hUnitSec (I := I) (M := M) g₀ T T' x) := by
    apply Tensor0SBundle.tensor0SSpace_ext 4 x
    intro m
    have h2 := velFibre_toModel_eval (I := I) (M := M) g₀ T T' hδ hδ' s x m
    have h3 := kOneSec_deriv_eq_threeArm_kernel (I := I) (M := M) g₀ T T' hδ hδ' s x
      (m 0) (m 1) (m 2) (m 3)
    have h4 := w2Fibre_toModel_eval (I := I) (M := M) g₀ T T' x m
    have hm4 : m = ![m 0, m 1, m 2, m 3] := by
      funext j
      fin_cases j <;> rfl
    show unitModel (I := I) (M := M) g₀ 4
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s) x m =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x)
        + linearizedRicciConnDiffOrder1CLM (I := I) x
            ((connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
            (kZeroSec (I := I) (M := M) g₀ T T' x)
        + linearizedRicciConnDiffOrder0CLM (I := I) x
            ((connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
            ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
            (hUnitSec (I := I) (M := M) g₀ T T' x)) m
    rw [Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
    rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x)) m =
        unitModel (I := I) (M := M) g₀ 4
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (symmS (I := I) (M := M) g₀ (T - T'))) x m from rfl]
    rw [h2, h4, h3, ← hm4]
  rw [show unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
        (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s)) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 4 I x from
            (velocitySecondCovGradCc (I := I) g₀ T T' hδ hδ' s).toSection x)
            (unitTensor (I := I) (M := M) x))) v from rfl]
  rw [hVel, map_add, map_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  rw [lichnerowiczFib_toModel_eq_fourTrace (I := I) (M := M) g₀ T T' hδ hδ' s x
      (linearizedRicciConnDiffOrder1CLM (I := I) x
        ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
        (kZeroSec (I := I) (M := M) g₀ T T' x)) v,
    lichnerowiczFib_toModel_eq_fourTrace (I := I) (M := M) g₀ T T' hδ hδ' s x
      (linearizedRicciConnDiffOrder0CLM (I := I) x
        ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
        ((covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
        (hUnitSec (I := I) (M := M) g₀ T T' x)) v]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 4 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x))) v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (symmS (I := I) (M := M) g₀ (T - T')))) x v from rfl]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
      (ricciCometricFourTraceCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
        (linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          (kZeroSec (I := I) (M := M) g₀ T T' x))) v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2
          (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 1
            (symmS (I := I) (M := M) g₀ (T - T')))) x v from rfl]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
      (ricciCometricFourTraceCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
        (linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)).toSection x)
          (hUnitSec (I := I) (M := M) g₀ T T' x))) v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (symmS (I := I) (M := M) g₀ (T - T')))) x v from rfl]
  ring

theorem linearizedRicciAt_eq_threeArm_connDiffCoeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
                  + (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
                      - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s))
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s
                  + (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
                      - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s))
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2
                (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  intro s hs x v
  have hsubsymm : ∀ (b : M) (p q : TangentSpace I b),
      ccTensorBilin (I := I) g₀ (T - T') b p q = ccTensorBilin (I := I) g₀ (T - T') b q p := by
    intro b p q
    rw [ccTensorBilin_sub_two, ccTensorBilin_sub_two, hTsymm b p q, hT'symm b p q]
  have hcollapse : symmS (I := I) (M := M) g₀ (T - T') = T - T' :=
    symmS_eq_self_of_symm (I := I) (M := M) g₀ (T - T') hsubsymm
  rw [← linearizedRicciConnDiffOrder0Coeff_eq_base_add_sub (I := I) g₀ T T' hδ hδ' s,
    ← linearizedRicciConnDiffOrder1Coeff_eq_base_add_sub (I := I) g₀ T T' hδ hδ' s]
  rw [unitModel_add_two_apply, unitModel_add_two_apply]
  rw [← hcollapse]
  rw [linearizedRicciAt_eq_lichnerowicz_velocitySecondCovGrad (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' hs x v,
    lichnerowicz_velocitySecondCovGrad_eq_threeArm_symm (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' hs x v]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
