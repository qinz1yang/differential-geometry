import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SecondGradient
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CorrectionFields.PointwiseBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CoefficientFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.PathLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Curvature.DecompositionMonomialBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConnectionDifference.Coefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Algebra.InputSlotSymmetrization
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def ricciContractionKernelBilin (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        (-(1 / 2) : ℝ) •
          (smoothCcTensorBilinForm (I := I) g₀ S x
              (riemannOp (LeviCivita (I := I) g₀) x v0 p q)
            + (smoothCcTensorBilinForm (I := I) g₀ S x q).comp
                (riemannOp (LeviCivita (I := I) g₀) x v0 p))
      map_add' := fun v0 v0' => by
        rw [show riemannOp (LeviCivita (I := I) g₀) x (v0 + v0') =
            riemannOp (LeviCivita (I := I) g₀) x v0 +
              riemannOp (LeviCivita (I := I) g₀) x v0' from
          (riemannOp (LeviCivita (I := I) g₀) x).map_add v0 v0']
        simp only [add_apply, map_add, ContinuousLinearMap.comp_add,
          smul_add]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply,
          show riemannOp (LeviCivita (I := I) g₀) x (c • v0) =
            c • riemannOp (LeviCivita (I := I) g₀) x v0 from
          (riemannOp (LeviCivita (I := I) g₀) x).map_smul c v0]
        simp only [smul_apply, map_smul, ContinuousLinearMap.comp_smul]
        rw [← smul_add, smul_comm] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricciContractionKernelBilin_apply (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q v0 v1 : TangentSpace I x) :
    ricciContractionKernelBilin (I := I) g₀ S x p q v0 v1 =
      (-(1 / 2) : ℝ) *
        (smoothCcTensorBilinForm (I := I) g₀ S x
            (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1
          + smoothCcTensorBilinForm (I := I) g₀ S x q
              (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)) := by
  rw [ricciContractionKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

def frameRicciContractionKernel (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (-(1 / 2) : ℝ) •
    ((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) ℝ
        ((smoothCcTensorBilinForm (I := I) g₀ S x).flip v1)).comp
        (riemannOp (LeviCivita (I := I) g₀) x v0)
      + (smoothCcTensorBilinForm (I := I) g₀ S x).flip.comp
          ((riemannOp (LeviCivita (I := I) g₀) x v0).flip v1))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma frameRicciContractionKernel_apply (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 p q : TangentSpace I x) :
    frameRicciContractionKernel (I := I) g₀ S x v0 v1 p q =
      ricciContractionKernelBilin (I := I) g₀ S x p q v0 v1 := by
  rw [ricciContractionKernelBilin_apply, frameRicciContractionKernel]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]

def ricciContractionSummandFib (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E (ricciContractionKernelBilin (I := I) g₀ S x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma ricciContractionSummandFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (ricciContractionSummandFib (I := I) g₀ S x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        ricciContractionKernelBilin (I := I) g₀ S x p q (v 0) (v 1) := by
  with_unfolding_all
    rw [ricciContractionSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk, Tensor0SSpace.toModel_smul, smul_apply,
      Tensor0SSpace.toModel_ofModel, smul_eq_mul]
    rfl

def ricciContractionBiContrFibFixedFrame (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    ricciContractionSummandFib (I := I) g₀ S x (B a x) (B b x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciContractionBiContrFibFixedFrame_toModel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (ricciContractionBiContrFibFixedFrame (I := I) g₀ S B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          ricciContractionKernelBilin (I := I) g₀ S x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [ricciContractionBiContrFibFixedFrame, sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, ricciContractionSummandFib_toModel]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciContractionKernelBilin_homSection_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (ricciContractionKernelBilin (I := I) g₀ S x (p x) (q x))) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ricciContractionKernelBilin (I := I) g₀ S x (p x) (q x))
  intro V0
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ricciContractionKernelBilin (I := I) g₀ S x (p x) (q x) (V0 x))
  intro W
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => smoothCcTensorBilinForm (I := I) g₀ S x
        (riemannSec (LeviCivita (I := I) g₀) V0 p q x) (W x)) :=
    ccTensorBilin_scalar_contMDiff (I := I) g₀ S
      ⟨fun b => riemannSec (LeviCivita (I := I) g₀) V0 p q b,
        riemannSec_contMDiff (cov := LeviCivita (I := I) g₀) V0.contMDiff hp hq⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => smoothCcTensorBilinForm (I := I) g₀ S x (q x)
        (riemannSec (LeviCivita (I := I) g₀) V0 p W x)) :=
    ccTensorBilin_scalar_contMDiff (I := I) g₀ S
      ⟨fun b => q b, hq⟩
      ⟨fun b => riemannSec (LeviCivita (I := I) g₀) V0 p W b,
        riemannSec_contMDiff (cov := LeviCivita (I := I) g₀) V0.contMDiff hp W.contMDiff⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (-(1 / 2) : ℝ) *
        (smoothCcTensorBilinForm (I := I) g₀ S x
            (riemannSec (LeviCivita (I := I) g₀) V0 p q x) (W x)
          + smoothCcTensorBilinForm (I := I) g₀ S x (q x)
              (riemannSec (LeviCivita (I := I) g₀) V0 p W x))) :=
    contMDiff_const.mul (hs1.add hs2)
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ricciContractionKernelBilin (I := I) g₀ S y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [ricciContractionKernelBilin_apply,
    riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) V0.contMDiff hp hq,
    riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) V0.contMDiff hp W.contMDiff]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciContractionBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (ricciContractionBiContrFibFixedFrame (I := I) g₀ S B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (ricciContractionSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b' => Y b') Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => ricciContractionKernelBilin (I := I) g₀ S x (B a x) (B b x))
      (ricciContractionKernelBilin_homSection_contMDiff (I := I) g₀ S (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => ricciContractionSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  have hcoe1 : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), T2 a b) Finset.univ
  have hcoe2 : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((T2 a b : Π z : M, Tensor0SSpace 2 I z)) :=
    fun a => map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => T2 a b) Finset.univ
  have hStot := (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    T2 a b).contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  have hval : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ricciContractionSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x) := by
    have h1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  rw [ricciContractionBiContrFibFixedFrame, sum_apply]
  rw [show ∑ a : Fin (Module.finrank ℝ E), (∑ b : Fin (Module.finrank ℝ E),
      ricciContractionSummandFib (I := I) g₀ S x (B a x) (B b x)) (Y x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ricciContractionSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x) from
    Finset.sum_congr rfl (fun a _ => sum_apply _ _ _)]
  rw [← hval]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciContractionBiContrFibFixedFrame_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciContractionBiContrFibFixedFrame (I := I) g₀ S B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => ricciContractionBiContrFibFixedFrame (I := I) g₀ S B x)
  intro Y
  exact ricciContractionBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ S B hB Y

def ricciContractionBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ricciContractionBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciContractionBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    ricciContractionBiContrFib (I := I) g₀ g₁ S y =
      ricciContractionBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ricciContractionBiContrFib, ricciContractionBiContrFibFixedFrame_toModel,
    ricciContractionBiContrFibFixedFrame_toModel]
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let e := (tangentSpaceModelContinuousLinearEquiv (I := I) y).toContinuousLinearMap
  let vt : Fin 2 → TangentSpace I y := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v i)
  let Dmodel : E →L[ℝ] E →L[ℝ] ℝ :=
    (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E).symm (Tensor0SSpace.toModel D)
  let Dd : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    (((Dmodel.comp e).flip.comp e).flip)
  with_unfolding_all
    change (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ y a y),
            tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ y b y)]) *
          ricciContractionKernelBilin (I := I) g₀ S y
            (smoothOrthoFrame (I := I) g₁ y a y) (smoothOrthoFrame (I := I) g₁ y b y)
            (vt 0) (vt 1)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ x₀ a y),
            tangentSpaceModelContinuousLinearEquiv (I := I) y
              (smoothOrthoFrame (I := I) g₁ x₀ b y)]) *
          ricciContractionKernelBilin (I := I) g₀ S y
            (smoothOrthoFrame (I := I) g₁ x₀ a y) (smoothOrthoFrame (I := I) g₁ x₀ b y)
            (vt 0) (vt 1)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf a),
            tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf b)]) *
          ricciContractionKernelBilin (I := I) g₀ S y (Bf a) (Bf b) (vt 0) (vt 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRicciContractionKernel (I := I) g₀ S y (vt 0) (vt 1) (Bf a) (Bf b) *
          Dd (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRicciContractionKernel_apply]
    dsimp only [Dd, Dmodel, e]
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRicciContractionKernel (I := I) g₀ S y (vt 0) (vt 1)) Dd
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciContractionBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciContractionBiContrFib (I := I) g₀ g₁ S x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciContractionBiContrFibFixedFrame (I := I) g₀ S
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    ricciContractionBiContrFibFixedFrame_contMDiff (I := I) g₀ S
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (ricciContractionBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ S x₀ hy))

def ricciContractionRemainderField (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciContractionBiContrFib (I := I) g₀ g₁ S x))
      contMDiff_toFun := ricciContractionBiContrFib_contMDiff (I := I) g₀ g₁ S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem ricciContractionRemainderField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    (ricciContractionRemainderField (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciContractionBiContrFib (I := I) g₀ g₁ S x)) := rfl


omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciContractionRemainderField_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciContractionRemainderField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciContractionRemainderField_toSection]
  have hzero : ricciContractionBiContrFib (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ricciContractionBiContrFib, ricciContractionBiContrFibFixedFrame_toModel]
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          ricciContractionKernelBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) = 0 from
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
        let p : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x a x
        let q : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x b x
        let v0 : TangentSpace I x :=
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)
        let v1 : TangentSpace I x :=
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)
        have hk : ricciContractionKernelBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
            p q v0 v1 = 0 := by
          rw [ricciContractionKernelBilin_apply,
            ccTensorBilin_zero, ccTensorBilin_zero,
            zero_add, mul_zero]
        with_unfolding_all
          change (Tensor0SSpace.toModel D
              ![(tangentSpaceModelContinuousLinearEquiv (I := I) x) p,
                (tangentSpaceModelContinuousLinearEquiv (I := I) x) q]) *
              ricciContractionKernelBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
                p q v0 v1 = 0
        rw [hk, mul_zero]))]
    simp only [zero_apply, Tensor0SSpace.toModel_zero]
  rw [hzero]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
