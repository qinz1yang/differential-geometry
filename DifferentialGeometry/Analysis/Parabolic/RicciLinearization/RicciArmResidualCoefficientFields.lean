import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldInputSlotSymmetrization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def metricCcTensorFib (g : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun m => g.inner x (m 0) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_add,
            ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_smul,
            ContinuousLinearMap.smul_apply]
      cont := ((g.inner x).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1) }
    : Tensor0SSpace 2 I x)

set_option linter.unusedSectionVars false in
@[simp] lemma metricCcTensorFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → TangentSpace I x) :
    metricCcTensorFib (I := I) g x m = g.inner x (m 0) (m 1) := rfl

set_option linter.unusedSectionVars false in
theorem metricCcTensorFib_section_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x (metricCcTensorFib (I := I) g x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (metricCcTensorFib (I := I) g x :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (Y (σ 0) x) (Y (σ 1) x)) x₀ :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g (Y (σ 0)) (Y (σ 1))).contMDiffAt
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 2, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change g.inner x (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1]

def metricCcTensor (g₀ g : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞
      (letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I)
        (M := M) 2
       (⟨fun x => metricCcTensorFib (I := I) g x,
         metricCcTensorFib_section_contMDiff (I := I) g⟩ :
        Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2))
  hasCompactSupport := HasCompactSupport.of_compactSpace _

def metricDifferenceCcTensor (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀

@[simp] theorem metricDifferenceCcTensor_self (g₀ : SmoothRiemannianMetric I M) :
    metricDifferenceCcTensor (I := I) (M := M) g₀ g₀ = 0 :=
  sub_self _

def ccTensorUnitValueSection (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    Π y : M, Tensor0SSpace 2 I y :=
  fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y)
      (unitZeroSec (I := I) (M := M) y)

theorem ccTensorUnitValueSection_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) y
        (ccTensorUnitValueSection (I := I) (M := M) g T y)) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 2 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    T.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff

set_option linter.unusedSectionVars false in
/-- Evaluates the covariant metric tensor, tagged over `g₀`, on two tangent
vectors. -/
theorem metricCcTensor_apply (g₀ g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x v w =
      g.inner x v w := by
  have hround : ccTensorMultilinear (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x =
      metricCcTensorFib (I := I) g x := by
    unfold ccTensorMultilinear metricCcTensor
    rw [MixedSection.toMultilinearSection_fromMultilinearSection]
    rfl
  rw [ccTensorBilin_apply]
  unfold ccTensorModel
  rw [hround]
  rfl

def gInvDiffQuadResidualField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connDiffBiContrCoeffField (I := I) (M := M) g₁ g₀ g₁ g₀

set_option linter.unusedSectionVars false in
@[simp] theorem gInvDiffQuadResidualField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) := rfl

set_option linter.unusedSectionVars false in

theorem gInvDiffQuadResidualField_self (g₀ : SmoothRiemannianMetric I M) :
    gInvDiffQuadResidualField (I := I) (M := M) g₀ g₀ = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [gInvDiffQuadResidualField_toSection]
  have hzero : connDiffBiContrFib (I := I) g₀ g₀ g₀ g₀ x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show connDiffBiContrFib (I := I) g₀ g₀ g₀ g₀ x =
        connDiffBiContrFibFixedFrame (I := I) g₀ g₀ g₀ g₀
          (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [connDiffBiContrFibFixedFrame_toModel]
    have hconn : PDE.DeTurck.connDiff (I := I) g₀ g₀ = 0 :=
      PDE.DeTurck.connDiff_self (I := I) g₀
    simp only [hconn, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero,
      zero_mul, Finset.sum_const_zero,
      Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  rw [hzero]
  rfl

def connDiffAACommKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0)
          - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p)
      map_add' := fun v0 v0' => by
        simp only [map_add, ContinuousLinearMap.add_apply]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply]
        simp only [map_smul, ContinuousLinearMap.smul_apply]
        rw [smul_sub] }

set_option linter.unusedSectionVars false in
@[simp] lemma connDiffAACommKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0) v1
        - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p) v1 := by
  rw [connDiffAACommKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.sub_apply]

def frameConnDiffAACommKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        haveI : FiniteDimensional ℝ (TangentSpace I x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        LinearMap.toContinuousLinearMap
          { toFun := fun q => connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1
            map_add' := fun q q' => by
              rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply,
                connDiffAACommKernelBilin_apply]
              simp only [map_add, ContinuousLinearMap.add_apply]
              ring
            map_smul' := fun c q => by
              rw [RingHom.id_apply, connDiffAACommKernelBilin_apply,
                connDiffAACommKernelBilin_apply]
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring }
      map_add' := fun p p' => by
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply,
          connDiffAACommKernelBilin_apply]
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      map_smul' := fun c p => by
        rw [RingHom.id_apply]
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

set_option linter.unusedSectionVars false in
@[simp] lemma frameConnDiffAACommKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (v0 v1 p q : TangentSpace I x) :
    frameConnDiffAACommKernel (I := I) g₀ g₁ x v0 v1 p q =
      connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1 := by
  rw [frameConnDiffAACommKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def connDiffAACommSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (connDiffAACommKernelBilin (I := I) g₀ g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] lemma connDiffAACommSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffAACommSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        connDiffAACommKernelBilin (I := I) g₀ g₁ x p q (v 0) (v 1) := by
  rw [connDiffAACommSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def connDiffAACommBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

set_option linter.unusedSectionVars false in
lemma connDiffAACommBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          connDiffAACommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [connDiffAACommBiContrFibFixedFrame, ContinuousLinearMap.sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connDiffAACommSummandFib_toModel]

theorem connDiffAACommKernelBilin_homSection_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (connDiffAACommKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connDiffAACommKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connDiffAACommKernelBilin (I := I) g₀ g₁ x (p x) (q x) (V0 x))
  intro W
  have hAqp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hq hp
  have hAAqpV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b)) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hAqp V0.contMDiff
  have hAqV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hq V0.contMDiff
  have hAAqVp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b)) (p b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hAqV hp
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b)) (V0 b), hAAqpV⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b)) (p b), hAAqVp⟩
      ⟨fun b => W b, W.contMDiff⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)
        - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    hs1.sub hs2
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connDiffAACommKernelBilin (I := I) g₀ g₁ y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connDiffAACommKernelBilin_apply]
  rfl

theorem connDiffAACommBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
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
      (fun x => connDiffAACommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (connDiffAACommKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M =>
          connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
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
        connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) := by
    have h1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  rw [connDiffAACommBiContrFibFixedFrame, ContinuousLinearMap.sum_apply]
  rw [show ∑ a : Fin (Module.finrank ℝ E), (∑ b : Fin (Module.finrank ℝ E),
      connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)) (Y x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) from
    Finset.sum_congr rfl (fun a _ => ContinuousLinearMap.sum_apply _ _ _)]
  rw [← hval]

theorem connDiffAACommBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM
          (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact connDiffAACommBiContrFibFixedFrame_apply_section_contMDiff
    (I := I) g₀ g₁ B hB Y

def connDiffAACommBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₁ x) x

set_option linter.unusedSectionVars false in

lemma connDiffAACommBiContrFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffAACommBiContrFib (I := I) g₀ g₁ x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          connDiffAACommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel]

theorem connDiffAACommBiContrFib_eq_fixedFrame_on_nbhd
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connDiffAACommBiContrFib (I := I) g₀ g₁ y =
      connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel,
    connDiffAACommBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          connDiffAACommKernelBilin (I := I) g₀ g₁ y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnDiffAACommKernel (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnDiffAACommKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameConnDiffAACommKernel (I := I) g₀ g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem connDiffAACommBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    connDiffAACommBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connDiffAACommBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

def ricciArmOrder0AACommCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x))
      contMDiff_toFun := connDiffAACommBiContrFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciArmOrder0AACommCoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x)) := rfl

set_option linter.unusedSectionVars false in

theorem connDiffAACommBiContrFib_self (g₀ : SmoothRiemannianMetric I M) (x : M) :
    connDiffAACommBiContrFib (I := I) g₀ g₀ x = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel]
  have hconn : PDE.DeTurck.connDiff (I := I) g₀ g₀ = 0 :=
    PDE.DeTurck.connDiff_self (I := I) g₀
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel D
        ![(smoothOrthoFrame (I := I) g₀ x a x : E),
          (smoothOrthoFrame (I := I) g₀ x b x : E)]) *
        connDiffAACommKernelBilin (I := I) g₀ g₀ x
          (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₀ x b x)
          (v 0) (v 1)) = 0 from
    Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
      rw [connDiffAACommKernelBilin_apply]
      simp only [hconn, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero,
        sub_self, mul_zero]))]
  simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0AACommCoeffField_self (g₀ : SmoothRiemannianMetric I M) :
    ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₀ = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmOrder0AACommCoeffField_toSection, connDiffAACommBiContrFib_self]
  rfl

private lemma vec3_upd_zero {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 0 z = ![z, b, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_upd_one {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 1 z = ![a, z, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_upd_two {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 2 z = ![a, b, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

set_option linter.unusedSectionVars false in

lemma linearizedKoszulCovec_add_fst (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (u u' ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x (u + u') ζ =
      linearizedKoszulCovec (I := I) g' S x u ζ +
        linearizedKoszulCovec (I := I) g' S x u' ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.add_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply,
    linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ, u + u', z] = G ![ζ, u, z] + G ![ζ, u', z] := by
    have h := G.map_update_add ![ζ, u, z] 1 u u'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  have h2 : G ![u + u', ζ, z] = G ![u, ζ, z] + G ![u', ζ, z] := by
    have h := G.map_update_add ![u, ζ, z] 0 u u'
    rwa [vec3_upd_zero, vec3_upd_zero, vec3_upd_zero] at h
  have h3 : G ![z, ζ, u + u'] = G ![z, ζ, u] + G ![z, ζ, u'] := by
    have h := G.map_update_add ![z, ζ, u] 2 u u'
    rwa [vec3_upd_two, vec3_upd_two, vec3_upd_two] at h
  rw [h1, h2, h3]
  ring

set_option linter.unusedSectionVars false in

lemma linearizedKoszulCovec_smul_fst (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x (c • u) ζ =
      c • linearizedKoszulCovec (I := I) g' S x u ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ, c • u, z] = c • G ![ζ, u, z] := by
    have h := G.map_update_smul ![ζ, u, z] 1 c u
    rwa [vec3_upd_one, vec3_upd_one] at h
  have h2 : G ![c • u, ζ, z] = c • G ![u, ζ, z] := by
    have h := G.map_update_smul ![u, ζ, z] 0 c u
    rwa [vec3_upd_zero, vec3_upd_zero] at h
  have h3 : G ![z, ζ, c • u] = c • G ![z, ζ, u] := by
    have h := G.map_update_smul ![z, ζ, u] 2 c u
    rwa [vec3_upd_two, vec3_upd_two] at h
  rw [h1, h2, h3]
  simp only [smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in

lemma linearizedKoszulCovec_add_snd (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (u ζ ζ' : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x u (ζ + ζ') =
      linearizedKoszulCovec (I := I) g' S x u ζ +
        linearizedKoszulCovec (I := I) g' S x u ζ' := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.add_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply,
    linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ + ζ', u, z] = G ![ζ, u, z] + G ![ζ', u, z] := by
    have h := G.map_update_add ![ζ, u, z] 0 ζ ζ'
    rwa [vec3_upd_zero, vec3_upd_zero, vec3_upd_zero] at h
  have h2 : G ![u, ζ + ζ', z] = G ![u, ζ, z] + G ![u, ζ', z] := by
    have h := G.map_update_add ![u, ζ, z] 1 ζ ζ'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  have h3 : G ![z, ζ + ζ', u] = G ![z, ζ, u] + G ![z, ζ', u] := by
    have h := G.map_update_add ![z, ζ, u] 1 ζ ζ'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  rw [h1, h2, h3]
  ring

set_option linter.unusedSectionVars false in

lemma linearizedKoszulCovec_smul_snd (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x u (c • ζ) =
      c • linearizedKoszulCovec (I := I) g' S x u ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![c • ζ, u, z] = c • G ![ζ, u, z] := by
    have h := G.map_update_smul ![ζ, u, z] 0 c ζ
    rwa [vec3_upd_zero, vec3_upd_zero] at h
  have h2 : G ![u, c • ζ, z] = c • G ![u, ζ, z] := by
    have h := G.map_update_smul ![u, ζ, z] 1 c ζ
    rwa [vec3_upd_one, vec3_upd_one] at h
  have h3 : G ![z, c • ζ, u] = c • G ![z, ζ, u] := by
    have h := G.map_update_smul ![z, ζ, u] 1 c ζ
    rwa [vec3_upd_one, vec3_upd_one] at h
  rw [h1, h2, h3]
  simp only [smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in

lemma linearizedKoszulCovec_zero_weight (g' : SmoothRiemannianMetric I M) (x : M)
    (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' (0 : SmoothCcTensor g' 0 2) x u ζ = 0 := by
  apply LinearMap.ext
  intro z
  rw [linearizedKoszulCovec_apply, LinearMap.zero_apply]
  have hzero : covGrad (I := I) (M := M) g' 0 2 (0 : SmoothCcTensor g' 0 2) = 0 :=
    covGrad_zero (I := I) (M := M) g' 0 2
  rw [hzero]
  have hunit : ∀ v : Fin 3 → TangentSpace I x,
      unitModel (I := I) (M := M) g' 3 (0 : SmoothCcTensor g' 0 3) x v = 0 := by
    intro v
    rw [unitModel]
    have h0 : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (0 : SmoothCcTensor g' 0 3).toSection x) = 0 := rfl
    rw [h0, ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero]
    rfl
  rw [hunit ![ζ, u, z], hunit ![u, ζ, z], hunit ![z, ζ, u]]
  ring

def sharpRaisedKoszulVec (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (u ζ : TangentSpace I x) : TangentSpace I x :=
  metricSharp (I := I) g₁ x (linearizedKoszulCovec (I := I) g₀ S x u ζ)

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_add_fst (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u u' ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x (u + u') ζ =
      sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ +
        sharpRaisedKoszulVec (I := I) g₀ g₁ S x u' ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, sharpRaisedKoszulVec,
    linearizedKoszulCovec_add_fst, metricSharp_def, metricSharp_def, metricSharp_def, map_add]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_smul_fst (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x (c • u) ζ =
      c • sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, linearizedKoszulCovec_smul_fst,
    metricSharp_def, metricSharp_def, map_smul]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_add_snd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u ζ ζ' : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x u (ζ + ζ') =
      sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ +
        sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ' := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, sharpRaisedKoszulVec,
    linearizedKoszulCovec_add_snd, metricSharp_def, metricSharp_def, metricSharp_def, map_add]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_smul_snd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x u (c • ζ) =
      c • sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, linearizedKoszulCovec_smul_snd,
    metricSharp_def, metricSharp_def, map_smul]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x u ζ = 0 := by
  rw [sharpRaisedKoszulVec, linearizedKoszulCovec_zero_weight, metricSharp_def, map_zero]

def sharpGradKoszulKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0))
          + (g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)).comp
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p))
        - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p))
          + (g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)).comp
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0))
      map_add' := fun v0 v0' => by
        rw [sharpRaisedKoszulVec_add_snd, map_add, map_add, map_add,
          ContinuousLinearMap.add_comp,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v0 + v0') =
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 +
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0' from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_add v0 v0',
          ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.comp_add]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply, sharpRaisedKoszulVec_smul_snd, map_smul, map_smul, map_smul,
          ContinuousLinearMap.smul_comp,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • v0) =
            c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_smul c v0,
          ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.comp_smul]
        rw [smul_sub, smul_add, smul_add] }

set_option linter.unusedSectionVars false in
@[simp] lemma sharpGradKoszulKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q v0 v1 : TangentSpace I x) :
    sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1 =
      (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)) v1
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1))
      - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)) v1
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1)) := by
  rw [sharpGradKoszulKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]

def frameSharpGradKoszulKernel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        haveI : FiniteDimensional ℝ (TangentSpace I x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        LinearMap.toContinuousLinearMap
          { toFun := fun q => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1
            map_add' := fun q q' => by
              rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
                sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_add_fst,
                sharpRaisedKoszulVec_add_fst]
              simp only [map_add, ContinuousLinearMap.add_apply]
              ring
            map_smul' := fun c q => by
              rw [RingHom.id_apply, sharpGradKoszulKernelBilin_apply,
                sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_smul_fst,
                sharpRaisedKoszulVec_smul_fst]
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring }
      map_add' := fun p p' => by
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
          sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_add_snd,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p + p') =
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x p +
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x p' from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_add p p']
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      map_smul' := fun c p => by
        rw [RingHom.id_apply]
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
          sharpRaisedKoszulVec_smul_snd,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • p) =
            c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x p from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_smul c p]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

set_option linter.unusedSectionVars false in
@[simp] lemma frameSharpGradKoszulKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 p q : TangentSpace I x) :
    frameSharpGradKoszulKernel (I := I) g₀ g₁ S x v0 v1 p q =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1 := by
  rw [frameSharpGradKoszulKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def sharpGradKoszulSummandFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] lemma sharpGradKoszulSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (sharpGradKoszulSummandFib (I := I) g₀ g₁ S x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q (v 0) (v 1) := by
  rw [sharpGradKoszulSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def sharpGradKoszulBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x)

set_option linter.unusedSectionVars false in
lemma sharpGradKoszulBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x D) v =
      (2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [sharpGradKoszulBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, sharpGradKoszulSummandFib_toModel]

private lemma unitValueCovGrad3_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection y)
          (unitZeroSec (I := I) (M := M) y))) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 3 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 3 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g₀ 0 2 S).toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    (covGrad (I := I) (M := M) g₀ 0 2 S).toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff

private lemma linearizedKoszulCovec_basis_contMDiffOn_generic
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        linearizedKoszulCovec (I := I) g₀ S b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  set W₃ : ∀ b : M, Tensor0SSpace 3 I b := fun b =>
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 3 I b from
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection b)
      (unitZeroSec (I := I) (M := M) b) with hW₃def
  have hW₃ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y (W₃ y)) :=
    unitValueCovGrad3_contMDiff (I := I) (M := M) g₀ S
  intro b hb
  have hb_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb
  have hbasisAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y => chartBasisVecFiber (I := I) α j y)) b := by
    have h := chartBasisVec_contMDiffOn (I := I) α j
    have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    exact (h b hb_base).contMDiffAt (hopen.mem_nhds hb_base)
  have hEval : ∀ (v : Fin 3 → ∀ y : M, TangentSpace I y)
      (_ : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% (v i)) b),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => Tensor0SSpace.toModel (W₃ y) (fun i : Fin 3 => v i y)) b :=
    fun v hv => TensorMultilinear.contMDiffAt_section_apply (n := 3) W₃
      (hW₃.contMDiffAt) v hv
  have h1 := hEval ![fun y => Y y, fun y => Z y, fun y => chartBasisVecFiber (I := I) α j y]
    (by
      intro i
      fin_cases i
      · exact Y.contMDiff.contMDiffAt
      · exact Z.contMDiff.contMDiffAt
      · exact hbasisAt)
  have h2 := hEval ![fun y => Z y, fun y => Y y, fun y => chartBasisVecFiber (I := I) α j y]
    (by
      intro i
      fin_cases i
      · exact Z.contMDiff.contMDiffAt
      · exact Y.contMDiff.contMDiffAt
      · exact hbasisAt)
  have h3 := hEval ![fun y => chartBasisVecFiber (I := I) α j y, fun y => Y y, fun y => Z y]
    (by
      intro i
      fin_cases i
      · exact hbasisAt
      · exact Y.contMDiff.contMDiffAt
      · exact Z.contMDiff.contMDiffAt)
  have hcomb : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => (1 / 2 : ℝ) *
        (Tensor0SSpace.toModel (W₃ y)
            (fun i : Fin 3 => (![fun y' => Y y', fun y' => Z y',
              fun y' => chartBasisVecFiber (I := I) α j y'] : Fin 3 → ∀ y' : M,
                TangentSpace I y') i y)
          + Tensor0SSpace.toModel (W₃ y)
              (fun i : Fin 3 => (![fun y' => Z y', fun y' => Y y',
                fun y' => chartBasisVecFiber (I := I) α j y'] : Fin 3 → ∀ y' : M,
                  TangentSpace I y') i y)
          - Tensor0SSpace.toModel (W₃ y)
              (fun i : Fin 3 => (![fun y' => chartBasisVecFiber (I := I) α j y',
                fun y' => Y y', fun y' => Z y'] : Fin 3 → ∀ y' : M,
                  TangentSpace I y') i y))) b :=
    ContMDiffAt.mul contMDiffAt_const ((h1.add h2).sub h3)
  refine (hcomb.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards with y
  rw [linearizedKoszulCovec_apply]
  have hUM : ∀ v : Fin 3 → TangentSpace I y,
      unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) y v =
        Tensor0SSpace.toModel (W₃ y) v := fun _ => rfl
  rw [hUM, hUM, hUM]
  congr 1
  congr 1
  · congr 1
    · congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  · congr 1
    funext i
    fin_cases i <;> rfl

set_option linter.unusedSectionVars false in

lemma sharpRaisedKoszulVec_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (U Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (U b) (Z b))) := by
  apply metricSharp_contMDiff_total (I := I) g₁
    (cv := fun b : M => linearizedKoszulCovec (I := I) g₀ S b (U b) (Z b))
  intro α j
  exact linearizedKoszulCovec_basis_contMDiffOn_generic (I := I) (M := M) g₀ S Z U α j

theorem sharpGradKoszulKernelBilin_homSection_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x) (V0 x))
  intro W
  have hΨqV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b))) := by
    have h := sharpRaisedKoszulVec_section_contMDiff (I := I) (M := M) g₀ g₁ S
      ⟨fun b => q b, hq⟩ ⟨fun b => V0 b, V0.contMDiff⟩
    exact h
  have hΨqp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b))) := by
    have h := sharpRaisedKoszulVec_section_contMDiff (I := I) (M := M) g₀ g₁ S
      ⟨fun b => q b, hq⟩ ⟨fun b => p b, hp⟩
    exact h
  have hApΨ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b)))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hp hΨqV
  have hApW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b) (W b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hp W.contMDiff
  have hAVΨ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b)))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff hΨqp
  have hAVW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b) (W b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff W.contMDiff
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b)), hApΨ⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x) (W x))) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b), hΨqV⟩
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b) (W b), hApW⟩
  have hs3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b)), hAVΨ⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs4 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (W x))) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b), hΨqp⟩
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b) (W b), hAVW⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x)
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))) (W x)
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x) (W x)))
        - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x)
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))) (W x)
          + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (W x)))) :=
    (hs1.add hs2).sub (hs3.add hs4)
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change sharpGradKoszulKernelBilin (I := I) g₀ g₁ S y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [sharpGradKoszulKernelBilin_apply]
  rfl

theorem sharpGradKoszulBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x))) := by
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
      (fun x => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (B a x) (B b x))
      (sharpGradKoszulKernelBilin_homSection_contMDiff (I := I) g₀ g₁ S (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b with hStot_def
  have hfinal := ContMDiff.smul_section (f := fun _ : M => (2 : ℝ))
    contMDiff_const Stot.contMDiff
  refine hfinal.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
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
  have hval : Stot x = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x) := by
    have h1 : Stot x = ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  have hgoal : sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x (Y x) =
      (2 : ℝ) • Stot x := by
    rw [hval, sharpGradKoszulBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact ContinuousLinearMap.sum_apply _ _ _
  rw [hgoal]
  rfl

theorem sharpGradKoszulBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x)
  intro Y
  exact sharpGradKoszulBiContrFibFixedFrame_apply_section_contMDiff
    (I := I) g₀ g₁ S B hB Y

def sharpGradKoszulBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S (smoothOrthoFrame (I := I) g₁ x) x

theorem sharpGradKoszulBiContrFib_eq_fixedFrame_on_nbhd
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    sharpGradKoszulBiContrFib (I := I) g₀ g₁ S y =
      sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel,
    sharpGradKoszulBiContrFibFixedFrame_toModel]
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ S y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameSharpGradKoszulKernel (I := I) g₀ g₁ S y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameSharpGradKoszulKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameSharpGradKoszulKernel (I := I) g₀ g₁ S y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem sharpGradKoszulBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    sharpGradKoszulBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁ S
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (sharpGradKoszulBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ S x₀ hy))

def ricciArmSharpGradKoszulResidualField (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x))
      contMDiff_toFun := sharpGradKoszulBiContrFib_contMDiff (I := I) g₀ g₁ S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciArmSharpGradKoszulResidualField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x)) := rfl

set_option linter.unusedSectionVars false in

theorem ricciArmSharpGradKoszulResidualField_zero_weight
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmSharpGradKoszulResidualField_toSection]
  have hzero : sharpGradKoszulBiContrFib (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel]
    have hker : ∀ p q : TangentSpace I x,
        sharpGradKoszulKernelBilin (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x p q
          (v 0) (v 1) = 0 := by
      intro p q
      rw [sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_zero_weight,
        sharpRaisedKoszulVec_zero_weight]
      simp only [map_zero, ContinuousLinearMap.zero_apply]
      ring
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) = 0 from
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
        rw [hker]
        ring))]
    rw [mul_zero]
    simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply]
  rw [hzero]
  rfl

set_option linter.unusedSectionVars false in
lemma ccTensorBilin_zero_weight (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  rw [ccTensorBilin_apply, ccTensorModel]
  rw [show (ccTensorMultilinear (I := I) g (0 : SmoothCcTensor g 0 2) x :
      Tensor0SSpace 2 I x) =
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (0 : SmoothCcTensor g 0 2).toSection x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (0 : SmoothCcTensor g 0 2).toSection x) = 0 from rfl]
  rw [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero]
  rfl

def ricciFoldKernelBilin (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        (-(1 / 2) : ℝ) •
          (ccTensorBilin (I := I) g₀ S x
              (riemannOp (LeviCivita (I := I) g₀) x v0 p q)
            + (ccTensorBilin (I := I) g₀ S x q).comp
                (riemannOp (LeviCivita (I := I) g₀) x v0 p))
      map_add' := fun v0 v0' => by
        rw [show riemannOp (LeviCivita (I := I) g₀) x (v0 + v0') =
            riemannOp (LeviCivita (I := I) g₀) x v0 +
              riemannOp (LeviCivita (I := I) g₀) x v0' from
          (riemannOp (LeviCivita (I := I) g₀) x).map_add v0 v0']
        simp only [ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.comp_add,
          smul_add]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply,
          show riemannOp (LeviCivita (I := I) g₀) x (c • v0) =
            c • riemannOp (LeviCivita (I := I) g₀) x v0 from
          (riemannOp (LeviCivita (I := I) g₀) x).map_smul c v0]
        simp only [ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.comp_smul]
        rw [← smul_add, smul_comm] }

set_option linter.unusedSectionVars false in
@[simp] lemma ricciFoldKernelBilin_apply (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q v0 v1 : TangentSpace I x) :
    ricciFoldKernelBilin (I := I) g₀ S x p q v0 v1 =
      (-(1 / 2) : ℝ) *
        (ccTensorBilin (I := I) g₀ S x
            (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1
          + ccTensorBilin (I := I) g₀ S x q
              (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)) := by
  rw [ricciFoldKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

def frameRicciFoldKernel (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (-(1 / 2) : ℝ) •
    ((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) ℝ
        ((ccTensorBilin (I := I) g₀ S x).flip v1)).comp
        (riemannOp (LeviCivita (I := I) g₀) x v0)
      + (ccTensorBilin (I := I) g₀ S x).flip.comp
          ((riemannOp (LeviCivita (I := I) g₀) x v0).flip v1))

set_option linter.unusedSectionVars false in
@[simp] lemma frameRicciFoldKernel_apply (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 p q : TangentSpace I x) :
    frameRicciFoldKernel (I := I) g₀ S x v0 v1 p q =
      ricciFoldKernelBilin (I := I) g₀ S x p q v0 v1 := by
  rw [ricciFoldKernelBilin_apply, frameRicciFoldKernel]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]

def ricciFoldSummandFib (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (ricciFoldKernelBilin (I := I) g₀ S x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] lemma ricciFoldSummandFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (ricciFoldSummandFib (I := I) g₀ S x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        ricciFoldKernelBilin (I := I) g₀ S x p q (v 0) (v 1) := by
  rw [ricciFoldSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def ricciFoldBiContrFibFixedFrame (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x)

set_option linter.unusedSectionVars false in
lemma ricciFoldBiContrFibFixedFrame_toModel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          ricciFoldKernelBilin (I := I) g₀ S x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [ricciFoldBiContrFibFixedFrame, ContinuousLinearMap.sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, ricciFoldSummandFib_toModel]

theorem ricciFoldKernelBilin_homSection_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (ricciFoldKernelBilin (I := I) g₀ S x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ricciFoldKernelBilin (I := I) g₀ S x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ricciFoldKernelBilin (I := I) g₀ S x (p x) (q x) (V0 x))
  intro W
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilin (I := I) g₀ S x
        (riemannSec (LeviCivita (I := I) g₀) V0 p q x) (W x)) :=
    ccTensorBilin_scalar_contMDiff (I := I) g₀ S
      ⟨fun b => riemannSec (LeviCivita (I := I) g₀) V0 p q b,
        riemannSec_contMDiff (cov := LeviCivita (I := I) g₀) V0.contMDiff hp hq⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilin (I := I) g₀ S x (q x)
        (riemannSec (LeviCivita (I := I) g₀) V0 p W x)) :=
    ccTensorBilin_scalar_contMDiff (I := I) g₀ S
      ⟨fun b => q b, hq⟩
      ⟨fun b => riemannSec (LeviCivita (I := I) g₀) V0 p W b,
        riemannSec_contMDiff (cov := LeviCivita (I := I) g₀) V0.contMDiff hp W.contMDiff⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (-(1 / 2) : ℝ) *
        (ccTensorBilin (I := I) g₀ S x
            (riemannSec (LeviCivita (I := I) g₀) V0 p q x) (W x)
          + ccTensorBilin (I := I) g₀ S x (q x)
              (riemannSec (LeviCivita (I := I) g₀) V0 p W x))) :=
    contMDiff_const.mul (hs1.add hs2)
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ricciFoldKernelBilin (I := I) g₀ S y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [ricciFoldKernelBilin_apply,
    riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) V0.contMDiff hp hq,
    riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) V0.contMDiff hp W.contMDiff]
  rfl

theorem ricciFoldBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x))) := by
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
      (fun x => ricciFoldKernelBilin (I := I) g₀ S x (B a x) (B b x))
      (ricciFoldKernelBilin_homSection_contMDiff (I := I) g₀ S (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x)
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
        ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x) := by
    have h1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  rw [ricciFoldBiContrFibFixedFrame, ContinuousLinearMap.sum_apply]
  rw [show ∑ a : Fin (Module.finrank ℝ E), (∑ b : Fin (Module.finrank ℝ E),
      ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x)) (Y x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x) from
    Finset.sum_congr rfl (fun a _ => ContinuousLinearMap.sum_apply _ _ _)]
  rw [← hval]

theorem ricciFoldBiContrFibFixedFrame_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x)
  intro Y
  exact ricciFoldBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ S B hB Y

def ricciFoldBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x

theorem ricciFoldBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    ricciFoldBiContrFib (I := I) g₀ g₁ S y =
      ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ricciFoldBiContrFib, ricciFoldBiContrFibFixedFrame_toModel,
    ricciFoldBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          ricciFoldKernelBilin (I := I) g₀ S y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRicciFoldKernel (I := I) g₀ S y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRicciFoldKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRicciFoldKernel (I := I) g₀ S y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem ricciFoldBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciFoldBiContrFib (I := I) g₀ g₁ S x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciFoldBiContrFibFixedFrame (I := I) g₀ S
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    ricciFoldBiContrFibFixedFrame_contMDiff (I := I) g₀ S
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (ricciFoldBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ S x₀ hy))

def ricciArmRicciFoldRemainderField (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciFoldBiContrFib (I := I) g₀ g₁ S x))
      contMDiff_toFun := ricciFoldBiContrFib_contMDiff (I := I) g₀ g₁ S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciArmRicciFoldRemainderField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciFoldBiContrFib (I := I) g₀ g₁ S x)) := rfl

set_option linter.unusedSectionVars false in

theorem ricciArmRicciFoldRemainderField_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmRicciFoldRemainderField_toSection]
  have hzero : ricciFoldBiContrFib (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ricciFoldBiContrFib, ricciFoldBiContrFibFixedFrame_toModel]
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          ricciFoldKernelBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) = 0 from
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
        rw [ricciFoldKernelBilin_apply, ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
        ring))]
    simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply]
  rw [hzero]
  rfl

def bgRDiffRefoldRemainderField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  appCcRS (I := I) (M := M) g₀ 2 2 2
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
        - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
      (ccSlotSwapField (I := I) (M := M) g₀)
    + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
    - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)

set_option linter.unusedSectionVars false in

theorem bgRDiffRefoldRemainderField_self (g₀ : SmoothRiemannianMetric I M) :
    bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₀ = 0 := by
  rw [bgRDiffRefoldRemainderField, metricDifferenceCcTensor_self, sub_self,
    appCcRS_zero_left, ricciArmSharpGradKoszulResidualField_zero_weight,
    ricciArmRicciFoldRemainderField_zero_weight, smul_zero, add_zero, sub_zero]

set_option linter.unusedSectionVars false in
private lemma inner_ext_vec (g : SmoothRiemannianMetric I M) (x : M) {a b : TangentSpace I x}
    (h : ∀ z : TangentSpace I x, g.inner x a z = g.inner x b z) : a = b := by
  apply (metricFlatMap (I := I) g x).injective
  apply LinearMap.ext
  intro z
  rw [metricFlatMap_apply, metricFlatMap_apply]
  exact h z

private lemma toModel_slotSwapFib_pair (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x)
    (u w : E) :
    Tensor0SBundle.Tensor0SSpace.toModel (slotSwapFib (I := I) (M := M) x D) ![u, w] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![w, u] := by
  rw [slotSwapFib_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in
private lemma unitModel_sub_loc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A - B) x =
      unitModel (I := I) (M := M) g s A x - unitModel (I := I) (M := M) g s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]

set_option linter.unusedSectionVars false in
private lemma unitModel_add_loc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A + B) x =
      unitModel (I := I) (M := M) g s A x + unitModel (I := I) (M := M) g s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
private lemma unitModel_smul_loc (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (A : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • A) x =
      c • unitModel (I := I) (M := M) g s A x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]

set_option linter.unusedSectionVars false in
private theorem foldOrthoFrame_basis_at_center (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x)
        (smoothOrthoFrame (I := I) g x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (smoothOrthoFrame (I := I) g x k x)
        (c j • smoothOrthoFrame (I := I) g x j x) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

set_option linter.unusedSectionVars false in
private theorem foldOrthoFrame_expansion_at_center (g : SmoothRiemannianMetric I M)
    (x : M) (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x i x) •
        smoothOrthoFrame (I := I) g x i x := by
  classical
  obtain ⟨bse, hbse⟩ := foldOrthoFrame_basis_at_center (I := I) (M := M) g x
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x)
        (smoothOrthoFrame (I := I) g x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x j x) = bse.repr u j := by
    intro j
    rw [g.symm x u (smoothOrthoFrame (I := I) g x j x)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g.inner x (smoothOrthoFrame (I := I) g x j x)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g.inner x u (smoothOrthoFrame (I := I) g x i x) •
          smoothOrthoFrame (I := I) g x i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

set_option linter.unusedSectionVars false in
private lemma foldInvSharpKoszul_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) := by
  apply inner_ext_vec (I := I) (M := M) g₁ x
  intro z
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ z, cotangentToDualLinear_apply,
    koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x z]

private lemma vec2_upd_zero {F : Type*} (a b z : F) :
    Function.update ![a, b] 0 z = ![z, b] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec2_upd_one {F : Type*} (a b z : F) :
    Function.update ![a, b] 1 z = ![a, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

set_option linter.unusedSectionVars false in
private lemma foldTensor0sClmExtUnit {s : ℕ} {x : M}
    {φ ψ : Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D, map_smul, map_smul, h]

set_option linter.unusedSectionVars false in
private lemma foldCoeff_eq_unitScalarRSLift (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) :
    (P.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x)) := by
  have h : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      P.toSection x) =
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        unitScalarRSLift (I := I) (M := M) x
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from P.toSection x)
            (unitZeroSec (I := I) (M := M) x))) := by
    apply foldTensor0sClmExtUnit (I := I) (M := M)
    rw [unitScalarRSLift_apply_unit]
  exact h

set_option linter.unusedSectionVars false in
private lemma foldG2_pair_antisym (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (x : M) (c d : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
        ![X x, Y x, c, d]
      - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
          ![Y x, X x, c, d] =
    -(ccTensorBilin (I := I) g₀ P x (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c) d
      + ccTensorBilin (I := I) g₀ P x c (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d)) := by
  classical
  have hicg : iteratedCovGrad (I := I) g₀ 0 2 2 P =
      covGrad (I := I) (M := M) g₀ 0 (2 + 1) (covGrad (I := I) (M := M) g₀ 0 2 P) := rfl
  have hconsXY : (![X x, Y x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (X x) (Fin.cons (Y x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hconsYX : (![Y x, X x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (Y x) (Fin.cons (X x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hXY := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 P hX hY x ![c, d]
  have hYX := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 P hY hX x ![c, d]
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 0 2 P)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := by
    intro v
    rw [unitModel, hicg]
    rfl
  rw [hUM ![X x, Y x, c, d], hUM ![Y x, X x, c, d], hconsXY, hconsYX, hXY, hYX]
  have hdiff : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => P.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) ![c, d]
      - Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => P.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) ![c, d]
      = Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          riemannOp (tensorCov (I := I) g₀ 0 2) x (X x) (Y x)
            ((P.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)))
          (unitZeroSec (I := I) (M := M) x)) ![c, d] := by
    rw [← tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g₀ 0 2 hX hY
      P.toSection.contMDiff]
    rw [show (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => P.toSection y) x -
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => P.toSection y) x)) =
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => P.toSection y) x) -
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => P.toSection y) x) from rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hdiff]
  rw [show ((P.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x)) from
    foldCoeff_eq_unitScalarRSLift (I := I) (M := M) g₀ P x]
  rw [riemannOp_tensorCov_unitScalarRSLift_unitEval (I := I) (M := M) g₀ 2 x (X x) (Y x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      P.toSection x) (unitZeroSec (I := I) (M := M) x))]
  set Xb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b => X b, hX⟩ with hXb_def
  set Yb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b => Y b, hY⟩ with hYb_def
  set AP : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y := fun y =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
      P.toSection y) (unitZeroSec (I := I) (M := M) y) with hAP_def
  have hAP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) y (AP y)) := by
    exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I) (IB := I) (b := id)
      (ϕ := fun y : M =>
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I y from P.toSection y))
      (v := fun y : M => unitZeroSec (I := I) (M := M) y)
      P.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff
  have hop : riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M 2
        (LeviCivita (I := I) g₀)) x (X x) (Y x) (AP x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
        (fun b => Xb b) (fun b => Yb b) AP x :=
    riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
      hX hY hAP_smooth
  rw [show ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from P.toSection x)
        (unitZeroSec (I := I) (M := M) x)) = AP x from rfl]
  rw [hop]
  rw [riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g₀ 2 Xb Yb AP hAP_smooth x ![c, d]]
  rw [Fin.sum_univ_two]
  rw [show (![c, d] : Fin 2 → TangentSpace I x) 0 = c from rfl,
    show (![c, d] : Fin 2 → TangentSpace I x) 1 = d from rfl,
    vec2_upd_zero, vec2_upd_one]
  have hbase : ∀ u : TangentSpace I x,
      baseSlotCurv (I := I) g₀ Xb Yb x u =
        riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) u := by
    intro u
    rw [baseSlotCurv]
    have hu := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      (X := fun b => Xb b) (Y := fun b => Yb b)
      (Z := fun b => smoothExtensionTangent (I := I) x u b) (x := x)
      hX hY (smoothExtensionTangent_contMDiff (I := I) x u)
    beta_reduce at hu
    rw [smoothExtensionTangent_eq (I := I) x u] at hu
    exact hu.symm
  rw [hbase c, hbase d]
  have hAPtoModel : ∀ (m : Fin 2 → TangentSpace I x),
      Tensor0SBundle.Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        ccTensorBilin (I := I) g₀ P x (m 0) (m 1) := by
    intro m
    have h1 : Tensor0SBundle.Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        unitModel (I := I) (M := M) g₀ 2 P x m := rfl
    rw [h1, show m = ![m 0, m 1] from funext (fun i => by fin_cases i <;> rfl),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rfl
  rw [show Tensor0SBundle.Tensor0SSpace.toModel (AP x)
        ![(riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c : E), (d : E)] =
      ccTensorBilin (I := I) g₀ P x (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c) d from
    hAPtoModel ![riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c, d]]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel (AP x)
        ![(c : E), (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d : E)] =
      ccTensorBilin (I := I) g₀ P x c (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d) from
    hAPtoModel ![c, riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d]]

set_option linter.unusedSectionVars false in
private lemma foldBilinSymm_eq_of_symm (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x v w := by
  rw [ccTensorBilinSymm_apply, ← hPsymm x v w]
  ring

set_option linter.unusedSectionVars false in
private lemma foldSkew_pointwise (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v)
    (x : M) (u p q z : TangentSpace I x) :
    g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x u p q) z =
      - g₁.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
        + (ccTensorBilin (I := I) g₀ P x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
          + ccTensorBilin (I := I) g₀ P x (riemannOp (LeviCivita (I := I) g₀) x u p q) z) := by
  have hskew := riemannOp_metric_skew (I := I) g₀ x u p q z
  have h1 := htie x (riemannOp (LeviCivita (I := I) g₀) x u p q) z
  have h2 := htie x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
  rw [foldBilinSymm_eq_of_symm (I := I) (M := M) g₀ P hPsymm] at h1 h2
  have hg : g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x u p q) z =
      - g₀.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z) := by
    linarith [hskew]
  rw [h1, hg]
  have h2' : g₀.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z) =
      g₁.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
        - ccTensorBilin (I := I) g₀ P x q (riemannOp (LeviCivita (I := I) g₀) x u p z) := by
    rw [h2]; ring
  rw [h2']
  ring

set_option linter.unusedSectionVars false in
private lemma foldCompleteness_slot2 (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (p omv : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel D ![(p : E), (omv : E)] =
      ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) *
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![(p : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] := by
  classical
  have hexp : omv = ∑ b : Fin (Module.finrank ℝ E),
      g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
        smoothOrthoFrame (I := I) g₁ x b x :=
    foldOrthoFrame_expansion_at_center (I := I) (M := M) g₁ x omv
  have hkey : Tensor0SBundle.Tensor0SSpace.toModel D
      (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
        ((∑ b : Fin (Module.finrank ℝ E),
          g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
            smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)) =
      ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) *
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![(p : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] := by
    have hsum : Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
          (∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
              ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))) =
        ∑ b : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
            (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
              (g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
                ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))) :=
      (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.map_update_sum
        Finset.univ 1 (fun b => g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))
        (![(p : E), (p : E)] : Fin 2 → E)
    rw [show ((∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) =
      ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) from rfl]
    rw [hsum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hsm : Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
          (g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
            ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))) =
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          Tensor0SBundle.Tensor0SSpace.toModel D
            (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
              ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)) :=
      (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.map_update_smul
        (![(p : E), (p : E)] : Fin 2 → E) 1
        (g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x))
        ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
    rw [hsm, vec2_upd_one, smul_eq_mul]
  have hfinal : (![(p : E), (omv : E)] : Fin 2 → E) =
      Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
        ((∑ b : Fin (Module.finrank ℝ E),
          g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
            smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) := by
    rw [vec2_upd_one]
    exact congrArg (fun t : TangentSpace I x => (![(p : E), (t : E)] : Fin 2 → E)) hexp
  rw [hfinal, hkey]

set_option linter.unusedSectionVars false in
private lemma foldCore_pointwise (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (Xs As Bs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (z : TangentSpace I x) :
    g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (Xs x) (As x) (Bs x)) z =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (Xs x) (As x) (Bs x)) z
      + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ P)) x
              ![Xs x, As x, Bs x, z]
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ P)) x
                ![As x, Xs x, Bs x, z]
            + unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ P)) x
                ![Xs x, Bs x, As x, z]
            + unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ P)) x
                ![As x, z, Xs x, Bs x]
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ P)) x
                ![Xs x, z, As x, Bs x]
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ P)) x
                ![As x, Bs x, Xs x, z])
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x))
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (Xs x))
      + g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x))
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (As x)) := by
  classical
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => Xs b)) := Xs.contMDiff
  have hA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => As b)) := As.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => Bs b)) := Bs.contMDiff
  have hop1 : riemannOp (LeviCivita (I := I) g₁) x (Xs x) (As x) (Bs x) =
      riemannSec (LeviCivita (I := I) g₁)
        (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x := by
    have h := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁)
      (X := fun b : M => Xs b) (Y := fun b : M => As b) (Z := fun b : M => Bs b) (x := x)
      hX hA hB
    exact h
  have hop0 : riemannOp (LeviCivita (I := I) g₀) x (Xs x) (As x) (Bs x) =
      riemannSec (LeviCivita (I := I) g₀)
        (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x := by
    have h := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      (X := fun b : M => Xs b) (Y := fun b : M => As b) (Z := fun b : M => Bs b) (x := x)
      hX hA hB
    exact h
  have hfold := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    (X := fun b : M => Xs b) (Y := fun b : M => As b) (Z := fun b : M => Bs b)
    hX hA hB (LeviCivita_torsion_eq_zero (I := I) g₀) x
  have hinner := congrArg (fun t : TangentSpace I x => g₁.inner x t z) hfold
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    at hinner
  have hc1 := covDerivConnDiff_g1inner_eq_half_secondCovGrad_sub_connDiffSq (I := I) (M := M)
    g₀ g₁ P htie Xs Bs As x z
  have hc2 := covDerivConnDiff_g1inner_eq_half_secondCovGrad_sub_connDiffSq (I := I) (M := M)
    g₀ g₁ P htie As Bs Xs x z
  have hcdd1 : covDerivConnDiff (I := I) g₀ g₁
      (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x := rfl
  have hcdd2 : covDerivConnDiff (I := I) g₀ g₁
      (fun b : M => As b) (fun b : M => Xs b) (fun b : M => Bs b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => As b) (fun b : M => Xs b) (fun b : M => Bs b) x := rfl
  rw [hcdd1] at hc1
  rw [hcdd2] at hc2
  have hsharpz1 : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Xs
        ⟨smoothExtensionTangent (I := I) x z,
          smoothExtensionTangent_contMDiff (I := I) x z⟩ x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (Xs x) := by
    rw [foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ Xs
      ⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ x]
    rw [show ((⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothExtensionTangent (I := I) x z x from rfl]
    rw [smoothExtensionTangent_eq (I := I) x z]
  have hsharpz2 : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ As
        ⟨smoothExtensionTangent (I := I) x z,
          smoothExtensionTangent_contMDiff (I := I) x z⟩ x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (As x) := by
    rw [foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ As
      ⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ x]
    rw [show ((⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothExtensionTangent (I := I) x z x from rfl]
    rw [smoothExtensionTangent_eq (I := I) x z]
  have hsharpAB : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ As Bs x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x) :=
    foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ As Bs x
  have hsharpXB : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Xs Bs x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x) :=
    foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ Xs Bs x
  rw [hsharpz1, hsharpAB] at hc1
  rw [hsharpz2, hsharpXB] at hc2
  have hdel1 : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
      (fun b : M => As b) (fun b : M => Bs b) x =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x) := rfl
  have hdel2 : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
      (fun b : M => Xs b) (fun b : M => Bs b) x =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x) := rfl
  have hDelta1 : CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₀) x
      (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => As b) (fun b : M => Bs b) x) ((fun b : M => Xs b) x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x)) (Xs x) := by
    rw [hdel1]
    rfl
  have hDelta2 : CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₀) x
      (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => Xs b) (fun b : M => Bs b) x) ((fun b : M => As b) x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x)) (As x) := by
    rw [hdel2]
    rfl
  rw [hDelta1, hDelta2] at hinner
  rw [hop1, hop0]
  rw [hinner, hc1, hc2]
  ring

set_option linter.unusedSectionVars false in
private lemma foldToModel_slot2_neg (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x)
    (p w : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel D ![(p : E), (-w : E)] =
      - Tensor0SBundle.Tensor0SSpace.toModel D ![(p : E), (w : E)] := by
  have hbase : (![(p : E), (-w : E)] : Fin 2 → E) =
      Function.update (![(p : E), (w : E)] : Fin 2 → E) 1 ((-1 : ℝ) • (w : E)) := by
    rw [vec2_upd_one]
    funext i
    fin_cases i
    · rfl
    · show (-w : E) = (-1 : ℝ) • (w : E)
      rw [neg_one_smul]
  rw [hbase]
  have hsm := (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.map_update_smul
    (![(p : E), (w : E)] : Fin 2 → E) 1 (-1 : ℝ) ((w : E))
  rw [show (Tensor0SBundle.Tensor0SSpace.toModel D)
      (Function.update (![(p : E), (w : E)] : Fin 2 → E) 1 ((-1 : ℝ) • (w : E))) =
    (-1 : ℝ) • (Tensor0SBundle.Tensor0SSpace.toModel D)
      (Function.update (![(p : E), (w : E)] : Fin 2 → E) 1 ((w : E))) from hsm]
  rw [vec2_upd_one, smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in
private lemma foldMovingTraceRow (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x) (u z : TangentSpace I x)
    (a : Fin (Module.finrank ℝ E)) :
    ∑ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x u
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) z =
      Tensor0SBundle.Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₁ x a x) u z : E)] +
      ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          (ccTensorBilin (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x)
              (riemannOp (LeviCivita (I := I) g₀) x u
                (smoothOrthoFrame (I := I) g₁ x a x) z)
            + ccTensorBilin (I := I) g₀ P x
                (riemannOp (LeviCivita (I := I) g₀) x u
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x)) z) := by
  classical
  set Ba := smoothOrthoFrame (I := I) g₁ x a x with hBa_def
  set Rz : TangentSpace I x := riemannOp (LeviCivita (I := I) g₀) x u Ba z with hRz_def
  have hstep : ∀ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          ![(Ba : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x u Ba
          (smoothOrthoFrame (I := I) g₁ x b x)) z =
      - (g₁.inner x Rz (smoothOrthoFrame (I := I) g₁ x b x) *
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![(Ba : E), (smoothOrthoFrame (I := I) g₁ x b x : E)])
        + Tensor0SBundle.Tensor0SSpace.toModel D
            ![(Ba : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          (ccTensorBilin (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x) Rz
            + ccTensorBilin (I := I) g₀ P x
                (riemannOp (LeviCivita (I := I) g₀) x u Ba
                  (smoothOrthoFrame (I := I) g₁ x b x)) z) := by
    intro b
    rw [foldSkew_pointwise (I := I) (M := M) g₀ g₁ P htie hPsymm x u Ba
      (smoothOrthoFrame (I := I) g₁ x b x) z]
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x b x) Rz]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hstep b)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_neg_distrib]
  rw [← foldCompleteness_slot2 (I := I) (M := M) g₁ x D Ba Rz]
  have hswap2 : riemannOp (LeviCivita (I := I) g₀) x Ba u z = -Rz := by
    rw [hRz_def]
    exact riemannOp_swap (cov := LeviCivita (I := I) g₀) x Ba u z
  rw [hswap2, foldToModel_slot2_neg (I := I) (M := M) x D Ba Rz]

set_option linter.unusedSectionVars false in
private lemma foldQuadruplePatterns (x : M) (p q c d : TangentSpace I x) :
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2) i)) = ![(c : E), (q : E), (p : E), (d : E)]) ∧
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((Equiv.swap (1 : Fin 4) 3) i)) = ![(p : E), (d : E), (c : E), (q : E)]) ∧
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) i)) =
      ![(c : E), (d : E), (p : E), (q : E)]) ∧
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((1 : Equiv.Perm (Fin 4)) i)) = ![(p : E), (q : E), (c : E), (d : E)]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · funext i
      fin_cases i <;> rfl

set_option linter.unusedSectionVars false in
private lemma foldKernelTerm_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (Wsec : Π b : M, Tensor0SBundle.Tensor0SSpace 2 I b)
    (hWsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) b (Wsec b)))
    (G : SmoothCcTensor g₀ 0 4) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁ Wsec hWsec
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) G) x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel (Wsec x)
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ((1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 G x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 G x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 G x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 G x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1])) := by
  classical
  set Guv : Tensor0SBundle.Tensor0SSpace 4 I x :=
    (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
      G.toSection x) (unitTensor (I := I) (M := M) x) with hGuv_def
  have hopen : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2
        (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁ Wsec hWsec
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) G) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁ Wsec hWsec
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1).toSection x) Guv) v := by
    rw [unitModel, appCc_toSection]
    rfl
  rw [hopen]
  rw [curvatureRefoldKernelCoeffField_toSection_eq_kernelFib_sum (I := I) (M := M)
    g₀ g₁ Wsec hWsec _ _ _ _ x]
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SBundle.Tensor0SSpace.toModelL_apply,
    ← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SBundle.Tensor0SSpace.toModelL_apply]
  rw [curvatureRefoldKernelFib]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [curvatureRefoldMonomialFib_toModel, curvatureRefoldMonomialFib_toModel,
    curvatureRefoldMonomialFib_toModel, curvatureRefoldMonomialFib_toModel]
  have hbr : ∀ w : Fin 4 → TangentSpace I x,
      Tensor0SBundle.Tensor0SSpace.toModel Guv (fun i => (w i : E)) =
        unitModel (I := I) (M := M) g₀ 4 G x w := fun w => rfl
  set Ba := smoothOrthoFrame (I := I) g₁ x a x
  set Bb := smoothOrthoFrame (I := I) g₁ x b x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![v 0, Bb, Ba, v 1] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2) i)) =
      (fun i => (((![v 0, Bb, Ba, v 1] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![v 0, Bb, Ba, v 1]
  have hB : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (1 : Fin 4) 3) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![Ba, v 1, v 0, Bb] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (1 : Fin 4) 3) i)) =
      (fun i => (((![Ba, v 1, v 0, Bb] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![Ba, v 1, v 0, Bb]
  have hC : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![v 0, v 1, Ba, Bb] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) i)) =
      (fun i => (((![v 0, v 1, Ba, Bb] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![v 0, v 1, Ba, Bb]
  have hD : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((1 : Equiv.Perm (Fin 4)) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![Ba, Bb, v 0, v 1] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((1 : Equiv.Perm (Fin 4)) i)) =
      (fun i => (((![Ba, Bb, v 0, v 1] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![Ba, Bb, v 0, v 1]
  rw [hA, hB, hC, hD]
  rw [smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in
private lemma foldDonorWeight_eq (g₀ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 W x
        (fun j : Fin 2 => if j = 0 then p else q) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) ![(p : E), (q : E)] := by
  rw [show (fun j : Fin 2 => if j = 0 then p else q) = ![p, q] from
    funext (fun j => by fin_cases j <;> rfl)]
  rfl

set_option linter.unusedSectionVars false in
private lemma foldSwapBgR_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (appCcRS (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
            (ccSlotSwapField (I := I) (M := M) g₀)) W) x v =
      (∑ c : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x c x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₁ x c x) (v 0) (v 1) : E)])
      - (∑ c : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x c x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₀ x c x) (v 0) (v 1) : E)]) := by
  classical
  set Wuv : Tensor0SBundle.Tensor0SSpace 2 I x :=
    (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x) with hWuv_def
  have hopen : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 2 2
        (appCcRS (I := I) (M := M) g₀ 2 2 2
          (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
          (ccSlotSwapField (I := I) (M := M) g₀)) W) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          ((ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)).toSection x)
          (slotSwapFib (I := I) (M := M) x Wuv)) v := by
    rw [unitModel, appCc_toSection]
    rfl
  rw [hopen]
  have hsub : ((ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
      - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)).toSection x =
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁).toSection x
      - (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀).toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [hsub]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      ((ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁).toSection x
        - (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀).toSection x)) =
    (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁).toSection x)
    - (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀).toSection x) from rfl]
  rw [ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  congr 1
  · rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁).toSection x)
        (slotSwapFib (I := I) (M := M) x Wuv) =
      bgRBiContrFib (I := I) g₀ g₁ x (slotSwapFib (I := I) (M := M) x Wuv) from rfl]
    rw [show bgRBiContrFib (I := I) g₀ g₁ x =
      bgRBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₁ x) x from rfl]
    rw [bgRBiContrFibFixedFrame_toModel]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact toModel_slotSwapFib_pair (I := I) (M := M) x Wuv _ _
  · rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀).toSection x)
        (slotSwapFib (I := I) (M := M) x Wuv) =
      bgRBiContrFib (I := I) g₀ g₀ x (slotSwapFib (I := I) (M := M) x Wuv) from rfl]
    rw [show bgRBiContrFib (I := I) g₀ g₀ x =
      bgRBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [bgRBiContrFibFixedFrame_toModel]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact toModel_slotSwapFib_pair (I := I) (M := M) x Wuv _ _

set_option linter.unusedSectionVars false in
private lemma unitModel_smul_apply_loc (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (A : SmoothCcTensor g 0 s) (x : M) (v : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g s (c • A) x v =
      c * unitModel (I := I) (M := M) g s A x v := by
  rw [unitModel_smul_loc, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
private lemma unitModel_sub_apply_loc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) (v : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g s (A - B) x v =
      unitModel (I := I) (M := M) g s A x v - unitModel (I := I) (M := M) g s B x v := by
  rw [unitModel_sub_loc, ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in
private lemma foldPsi_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hsymmS : symmS (I := I) (M := M) g₀ P = P)
    (x : M) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ P x u ζ =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ := by
  apply inner_ext_vec (I := I) (M := M) g₁ x
  intro z
  rw [sharpRaisedKoszulVec, inner_metricSharp (I := I) g₁ x _ z,
    linearizedKoszulCovec_apply,
    connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x u ζ z, hsymmS]

set_option linter.unusedSectionVars false in
private lemma foldQuadKernel_split (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hsymmS : symmS (I := I) (M := M) g₀ P = P)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 v0)
      + g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 p) =
    connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1
      + sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x p q v0 v1 := by
  rw [connDiffAACommKernelBilin_apply, sharpGradKoszulKernelBilin_apply]
  rw [foldPsi_eq_connDiff (I := I) (M := M) g₀ g₁ P htie hsymmS x q v0,
    foldPsi_eq_connDiff (I := I) (M := M) g₀ g₁ P htie hsymmS x q p]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x _ p]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0 =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x _ v0]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 v0 =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1 from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x v1 v0]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 p =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1 from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x v1 p]
  ring

set_option linter.unusedSectionVars false in
private lemma foldQtrue_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁) W) x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          connDiffAACommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [show unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 2 2
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁) W) x =
    Tensor0SBundle.Tensor0SSpace.toModel
      (connDiffAACommBiContrFib (I := I) g₀ g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) from by
    rw [unitModel, appCc_toSection]
    rfl]
  rw [connDiffAACommBiContrFib_toModel]

set_option linter.unusedSectionVars false in
private lemma foldSGK_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ P) W) x v =
      (2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [show unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 2 2
        (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ P) W) x =
    Tensor0SBundle.Tensor0SSpace.toModel
      (sharpGradKoszulBiContrFib (I := I) g₀ g₁ P x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) from by
    rw [unitModel, appCc_toSection]
    rfl]
  rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel]

set_option linter.unusedSectionVars false in
private lemma foldRF_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ P) W) x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [show unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 2 2
        (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ P) W) x =
    Tensor0SBundle.Tensor0SSpace.toModel
      (ricciFoldBiContrFib (I := I) g₀ g₁ P x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) from by
    rw [unitModel, appCc_toSection]
    rfl]
  rw [ricciFoldBiContrFib, ricciFoldBiContrFibFixedFrame_toModel]

set_option linter.unusedSectionVars false in
private lemma foldHtie_zero (g₀ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (v w : TangentSpace I y),
      g₀.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) y v w := by
  intro y v w
  rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  ring

set_option linter.unusedSectionVars false in
private lemma foldPsymm_zero (g₀ : SmoothRiemannianMetric I M) :
    ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x v w =
        ccTensorBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x w v := by
  intro x v w
  rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]

set_option linter.unusedSectionVars false in
private theorem foldAppCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (Φ₁ - Φ₂) W =
      appCc (I := I) (M := M) g r s Φ₁ W - appCc (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ₁ W
      - appCc (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (appCc (I := I) (M := M) g r s Φ₁ W).toSection x -
        (appCc (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) =
      Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option linter.unusedSectionVars false in
private theorem foldSymmS_eq_self (g₀ : SmoothRiemannianMetric I M)
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

set_option linter.unusedVariables false in

theorem ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v)
    (W : SmoothCcTensor g₀ 0 2) :
    (1 / 2 : ℝ) •
        (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W
          - appCc (I := I) (M := M) g₀ 2 2
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) W) =
      appCc (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
            + (appCcRS (I := I) (M := M) g₀ 2 2 2
                  (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
                    - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
                  (ccSlotSwapField (I := I) (M := M) g₀)
                + (1 / 2 : ℝ) •
                    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ P
                - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ P)) W
        + appCc (I := I) (M := M) g₀ 4 2
            (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁
              (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
            (iteratedCovGrad (I := I) g₀ 0 2 2 P) := by
  classical
  have hsymmS : symmS (I := I) (M := M) g₀ P = P :=
    foldSymmS_eq_self (I := I) (M := M) g₀ P hPsymm
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2, foldAppCc_sub_left (I := I) (M := M) g₀ 2 2,
    appCc_add_left (I := I) (M := M) g₀ 2 2, appCc_smul_left (I := I) (M := M) g₀ 2 2]
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_smul_apply_loc (I := I) (M := M) g₀ 2 (1 / 2 : ℝ) _ x v,
    unitModel_sub_apply_loc (I := I) (M := M) g₀ 2 _ _ x v]
  rw [unitModel_add_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.add_apply,
    unitModel_add_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.add_apply,
    unitModel_sub_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply,
    unitModel_add_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.add_apply,
    unitModel_smul_apply_loc (I := I) (M := M) g₀ 2 (1 / 2 : ℝ) _ x v]
  rw [ricciArmOrder0RiemannCoeff_appCc_eq (I := I) (M := M) g₀ g₁ W x v,
    ricciArmOrder0RiemannCoeff_appCc_eq (I := I) (M := M) g₀ g₀ W x v]
  rw [foldQtrue_eval (I := I) (M := M) g₀ g₁ W x v,
    foldSwapBgR_eval (I := I) (M := M) g₀ g₁ W x v,
    foldSGK_eval (I := I) (M := M) g₀ g₁ P W x v,
    foldRF_eval (I := I) (M := M) g₀ g₁ P W x v,
    foldKernelTerm_eval (I := I) (M := M) g₀ g₁
      (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
      (iteratedCovGrad (I := I) g₀ 0 2 2 P) x v]
  have hWkernel : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] := fun a b => rfl
  have hdonor1 : (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      g₁.inner x
          (riemannOp (LeviCivita (I := I) g₁) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
        unitModel (I := I) (M := M) g₀ 2 W x
          (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
            else smoothOrthoFrame (I := I) g₁ x b x)) =
      (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          g₁.inner x
            (riemannOp (LeviCivita (I := I) g₁) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) := by
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [foldDonorWeight_eq (I := I) (M := M) g₀ W x]
    ring
  have hdonor0 : (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      g₀.inner x
          (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₀ x b x)) (v 1) *
        unitModel (I := I) (M := M) g₀ 2 W x
          (fun j => if j = 0 then smoothOrthoFrame (I := I) g₀ x a x
            else smoothOrthoFrame (I := I) g₀ x b x)) =
      (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          g₀.inner x
            (riemannOp (LeviCivita (I := I) g₀) x (v 0)
              (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₀ x b x)) (v 1)) := by
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [foldDonorWeight_eq (I := I) (M := M) g₀ W x]
    ring
  rw [hdonor1, hdonor0]
  have hker2 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
              ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                smoothOrthoFrame (I := I) g₁ x a x, v 1]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                  smoothOrthoFrame (I := I) g₁ x b x]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                  smoothOrthoFrame (I := I) g₁ x b x]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![smoothOrthoFrame (I := I) g₁ x a x,
                  smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1]))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ((1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1])) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
      rw [hWkernel a b]))
  rw [hker2]
  have hfold : ∀ a b : Fin (Module.finrank ℝ E),
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) =
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)
        + (1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x a x,
                  smoothOrthoFrame (I := I) g₁ x b x, v 1]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x, v 1])
        + (1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1])
        + (connDiffAACommKernelBilin (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
              (v 0) (v 1)
            + sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
                (v 0) (v 1)) := by
    intro a b
    have h := foldCore_pointwise (I := I) (M := M) g₀ g₁ P htie
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
      ⟨smoothOrthoFrame (I := I) g₁ x a, smoothOrthoFrame_smooth (I := I) g₁ x a⟩
      ⟨smoothOrthoFrame (I := I) g₁ x b, smoothOrthoFrame_smooth (I := I) g₁ x b⟩
      x (v 1)
    rw [hsymmS] at h
    rw [show ((⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothExtensionTangent (I := I) x (v 0) x from rfl] at h
    rw [show ((⟨smoothOrthoFrame (I := I) g₁ x a, smoothOrthoFrame_smooth (I := I) g₁ x a⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothOrthoFrame (I := I) g₁ x a x from rfl] at h
    rw [show ((⟨smoothOrthoFrame (I := I) g₁ x b, smoothOrthoFrame_smooth (I := I) g₁ x b⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothOrthoFrame (I := I) g₁ x b x from rfl] at h
    rw [smoothExtensionTangent_eq (I := I) x (v 0)] at h
    have hq := foldQuadKernel_split (I := I) (M := M) g₀ g₁ P htie hsymmS x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) (v 0) (v 1)
    linarith [h, hq]
  have hric : ∀ a b : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
              ![v 0, smoothOrthoFrame (I := I) g₁ x a x,
                smoothOrthoFrame (I := I) g₁ x b x, v 1]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![smoothOrthoFrame (I := I) g₁ x a x, v 0,
                  smoothOrthoFrame (I := I) g₁ x b x, v 1]) =
        ricciFoldKernelBilin (I := I) g₀ P x
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
          (v 0) (v 1) := by
    intro a b
    have h := foldG2_pair_antisym (I := I) (M := M) g₀ P
      (X := smoothExtensionTangent (I := I) x (v 0))
      (Y := smoothOrthoFrame (I := I) g₁ x a)
      (smoothExtensionTangent_contMDiff (I := I) x (v 0))
      (smoothOrthoFrame_smooth (I := I) g₁ x a)
      x (smoothOrthoFrame (I := I) g₁ x b x) (v 1)
    rw [smoothExtensionTangent_eq (I := I) x (v 0)] at h
    rw [ricciFoldKernelBilin_apply]
    linarith [h]
  have hcomb : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) =
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)
      + Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)
      + Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ((1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1]))
      + (Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          connDiffAACommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)
        + Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) := by
    intro a b
    have e := hfold a b
    rw [hric a b] at e
    rw [e]
    ring
  have hS1 := Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) =>
    Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) =>
      hcomb a b))
  simp only [Finset.sum_add_distrib] at hS1
  have hrow1 : ∀ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) =
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₁ x a x) (v 0) (v 1) : E)] +
        ∑ b : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
              ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                (smoothOrthoFrame (I := I) g₁ x b x : E)] *
            (ccTensorBilin (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x)
                (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                  (smoothOrthoFrame (I := I) g₁ x a x) (v 1))
              + ccTensorBilin (I := I) g₀ P x
                  (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                    (smoothOrthoFrame (I := I) g₁ x a x)
                    (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) :=
    fun a => foldMovingTraceRow (I := I) (M := M) g₀ g₁ P htie hPsymm x
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x)) (v 0) (v 1) a
  have hpt : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        (ccTensorBilin (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x)
            (riemannOp (LeviCivita (I := I) g₀) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x) (v 1))
          + ccTensorBilin (I := I) g₀ P x
              (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                (smoothOrthoFrame (I := I) g₁ x a x)
                (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) =
      (-2 : ℝ) *
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) := by
    intro a b
    rw [ricciFoldKernelBilin_apply]
    ring
  have hrowsum1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) =
      (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₁ x a x) (v 0) (v 1) : E)])
      + (-2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) := by
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hrow1 a)]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hpt a b))]
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
      (Finset.mul_sum Finset.univ _ (-2 : ℝ)).symm)]
    rw [(Finset.mul_sum Finset.univ _ (-2 : ℝ)).symm]
  have hrow0 : ∀ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₀ x b x)) (v 1) =
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₀ x a x) (v 0) (v 1) : E)] := by
    intro a
    have h := foldMovingTraceRow (I := I) (M := M) g₀ g₀ (0 : SmoothCcTensor g₀ 0 2)
      (foldHtie_zero (I := I) (M := M) g₀) (foldPsymm_zero (I := I) (M := M) g₀) x
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x)) (v 0) (v 1) a
    have hz : (∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          (ccTensorBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
              (smoothOrthoFrame (I := I) g₀ x b x)
              (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                (smoothOrthoFrame (I := I) g₀ x a x) (v 1))
            + ccTensorBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
                (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                  (smoothOrthoFrame (I := I) g₀ x a x)
                  (smoothOrthoFrame (I := I) g₀ x b x)) (v 1))) = 0 :=
      Finset.sum_eq_zero (fun b _ => by
        rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
        ring)
    rw [h, hz, add_zero]
  have hrowsum0 := Finset.sum_congr rfl
    (fun a (_ : a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) => hrow0 a)
  rw [hS1, hrowsum1, hrowsum0]
  ring

set_option maxHeartbeats 3200000

def ccTensorFourUnitValueSection (g : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) : Π y : M, Tensor0SSpace 4 I y :=
  fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 4 I y from G.toSection y)
      (unitZeroSec (I := I) (M := M) y)

set_option linter.unusedSectionVars false in
theorem ccTensorFourUnitValueSection_contMDiff (g : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) y
        (ccTensorFourUnitValueSection (I := I) (M := M) g G y)) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 4 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 4 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 4 I y from G.toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    G.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff

private def refoldKernelArgumentPairEvalCLM (x : M) (v : Fin 2 → E) :
    Tensor0SSpace 2 I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

set_option linter.unusedSectionVars false in
private lemma refoldKernelArgumentPairEvalCLM_apply (x : M) (v : Fin 2 → E)
    (D : Tensor0SSpace 2 I x) :
    refoldKernelArgumentPairEvalCLM (I := I) (M := M) x v D =
      Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

def refoldKernelContractionMonomialFibFixedFrame (Gs : Π b : M, Tensor0SSpace 4 I b)
    (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    (refoldKernelArgumentPairEvalCLM (I := I) (M := M) x
        ![(B a x : E), (B b x : E)]).smulRight
      (leadingPairFeedFib (I := I) (M := M) 2 x (B a x) (B b x)
        (slotPerm4Fib (I := I) (M := M) x σ (Gs x)))

set_option linter.unusedSectionVars false in

lemma refoldKernelContractionMonomialFibFixedFrame_apply
    (Gs : Π b : M, Tensor0SSpace 4 I b) (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) :
    refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M) Gs σ B x D =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        curvatureRefoldMonomialFib (I := I) (M := M) x
          (Tensor0SSpace.toModel (𝕜 := ℝ) D ![(B a x : E), (B b x : E)]) σ
          (B a x) (B b x) (Gs x) := by
  rw [refoldKernelContractionMonomialFibFixedFrame, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply, refoldKernelArgumentPairEvalCLM_apply,
    curvatureRefoldMonomialFib_apply]

set_option linter.unusedSectionVars false in
lemma refoldKernelContractionMonomialFibFixedFrame_toModel
    (Gs : Π b : M, Tensor0SSpace 4 I b) (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M) Gs σ B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) D ![(B a x : E), (B b x : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ) (Gs x)
            (fun i => (Fin.cons ((B a x : E)) (Fin.cons ((B b x : E)) v) : Fin 4 → E)
              (σ i)) := by
  classical
  rw [refoldKernelContractionMonomialFibFixedFrame_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, curvatureRefoldMonomialFib_toModel]

private theorem refoldKernelContractionMonomialFibFixedFrame_apply_section_contMDiff
    (Gs : Π b : M, Tensor0SSpace 4 I b)
    (hGs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) b (Gs b)))
    (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M) Gs σ B x (Y x))) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  set Gσ : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun z : M => Tensor0SSpace 4 I z⟯ :=
    { toFun := fun x : M => slotPerm4Fib (I := I) (M := M) x σ (Gs x)
      contMDiff_toFun := by
        have h := slotPerm4Fib_apply_section_contMDiff (I := I) (M := M) σ
          ({ toFun := fun x : M => Gs x
             contMDiff_toFun := hGs } :
            Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun z : M => Tensor0SSpace 4 I z⟯)
        exact h }
    with hGσ_def
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          ((refoldKernelArgumentPairEvalCLM (I := I) (M := M) x
              ![(B a x : E), (B b x : E)]).smulRight
            (leadingPairFeedFib (I := I) (M := M) 2 x (B a x) (B b x)
              (slotPerm4Fib (I := I) (M := M) x σ (Gs x))) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (𝕜 := ℝ) (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
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
    have hfeed1 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
          (E := fun z : M => Tensor0SSpace 3 I z) x
          (Tensor0SPartialEval.tensor0SPartialEval I M (s := 3)
            (fun z => Gσ z) (fun z => B a z) x)) :=
      Tensor0SPartialEval.contMDiff_tensor0SPartialEval I M (s := 3)
        (fun z => Gσ z) Gσ.contMDiff (fun z => B a z) (hB a)
    set Z3 : Cₛ^∞⟮I; Tensor0SModel 3 ℝ E, fun z : M => Tensor0SSpace 3 I z⟯ :=
      { toFun := fun x : M => Tensor0SPartialEval.tensor0SPartialEval I M (s := 3)
          (fun z => Gσ z) (fun z => B a z) x
        contMDiff_toFun := hfeed1 }
      with hZ3_def
    have hfeed2 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (Tensor0SPartialEval.tensor0SPartialEval I M (s := 2)
            (fun z => Z3 z) (fun z => B b z) x)) :=
      Tensor0SPartialEval.contMDiff_tensor0SPartialEval I M (s := 2)
        (fun z => Z3 z) Z3.contMDiff (fun z => B b z) (hB b)
    have hsmul := ContMDiff.smul_section
      (f := fun x : M => Tensor0SSpace.toModel (𝕜 := ℝ) (Y x) ![(B a x : E), (B b x : E)])
      (s := fun x : M => Tensor0SPartialEval.tensor0SPartialEval I M (s := 2)
        (fun z => Z3 z) (fun z => B b z) x)
      hscalar hfeed2
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M =>
          (refoldKernelArgumentPairEvalCLM (I := I) (M := M) x
              ![(B a x : E), (B b x : E)]).smulRight
            (leadingPairFeedFib (I := I) (M := M) 2 x (B a x) (B b x)
              (slotPerm4Fib (I := I) (M := M) x σ (Gs x))) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [refoldKernelContractionMonomialFibFixedFrame, hStot_def]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

private def kcInnerPairBilin (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (L X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
private lemma kcInnerPairBilin_apply (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    kcInnerPairBilin (I := I) x K L X Y Y' = K X Y * L X Y' := by
  rw [kcInnerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private def kcOuterPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l * K X (chartModelBasis E k)) •
          (ContinuousLinearMap.flip L (chartModelBasis E l))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

set_option linter.unusedSectionVars false in
private lemma kcOuterPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    kcOuterPairBilin (I := I) g x K L X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (chartModelBasis E k) * L X' (chartModelBasis E l)) := by
  rw [kcOuterPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

private theorem kc_double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (chartModelBasis E m) (chartModelBasis E k) *
            L (chartModelBasis E n) (chartModelBasis E l))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      kcOuterPairBilin (I := I) g x K L (B a) (B a) := by
    intro a
    rw [kcOuterPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (kcInnerPairBilin (I := I) x K L (B a)) B hB
    simp only [kcInnerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (kcOuterPairBilin (I := I) g x K L) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [kcOuterPairBilin_apply]

private theorem kc_double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * L (C a) (C b) := by
  rw [kc_double_frame_bilin_trace_eq_fixed (I := I) g x K L B hB,
    kc_double_frame_bilin_trace_eq_fixed (I := I) g x K L C hC]

private def kcToModelEvalCLM (s : ℕ) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

set_option linter.unusedSectionVars false in
private lemma kcToModelEvalCLM_apply (s : ℕ) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    kcToModelEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

private def kcPairFeedScalarCLM (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (kcToModelEvalCLM (I := I) (M := M) s x v).comp
        (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x
          ((tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          map_smul] }

set_option linter.unusedSectionVars false in
private lemma kcPairFeedScalarCLM_apply (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) (p q : TangentSpace I x) :
    kcPairFeedScalarCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel (𝕜 := ℝ) G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [kcPairFeedScalarCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, kcToModelEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p) (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := G) (v0 := p) (vs := Fin.cons (q : E) v)]

def refoldKernelContractionMonomialBiContrFib (g₁ : SmoothRiemannianMetric I M)
    (Gs : Π b : M, Tensor0SSpace 4 I b) (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M) Gs σ
    (smoothOrthoFrame (I := I) g₁ x) x

theorem refoldKernelContractionMonomialBiContrFib_eq_fixedFrame_on_nbhd
    (g₁ : SmoothRiemannianMetric I M) (Gs : Π b : M, Tensor0SSpace 4 I b)
    (σ : Equiv.Perm (Fin 4)) (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    refoldKernelContractionMonomialBiContrFib (I := I) (M := M) g₁ Gs σ y =
      refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M) Gs σ
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [refoldKernelContractionMonomialBiContrFib,
    refoldKernelContractionMonomialFibFixedFrame_toModel,
    refoldKernelContractionMonomialFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) D ![(Bf a : E), (Bf b : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ) (Gs y)
            (fun i => (Fin.cons ((Bf a : E)) (Fin.cons ((Bf b : E)) v) : Fin 4 → E)
              (σ i)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        kcPairFeedScalarCLM (I := I) (M := M) 0 y D ![] (Bf a) (Bf b) *
          kcPairFeedScalarCLM (I := I) (M := M) 2 y
            (slotPerm4Fib (I := I) (M := M) y σ (Gs y)) v (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [kcPairFeedScalarCLM_apply, kcPairFeedScalarCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact kc_double_frame_bilin_trace_indep (I := I) g₁ y
    (kcPairFeedScalarCLM (I := I) (M := M) 0 y D ![])
    (kcPairFeedScalarCLM (I := I) (M := M) 2 y (slotPerm4Fib (I := I) (M := M) y σ (Gs y)) v)
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem refoldKernelContractionMonomialBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (Gs : Π b : M, Tensor0SSpace 4 I b)
    (hGs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) b (Gs b)))
    (σ : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (refoldKernelContractionMonomialBiContrFib (I := I) (M := M)
          g₁ Gs σ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M)
          Gs σ (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ := by
    have h_glob : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
          (E := fun z : M => TensorRSSpace 2 2 I z) x
          (TensorRSSpace.ofCLM (refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M)
            Gs σ (smoothOrthoFrame (I := I) g₁ x₀) x))) := by
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
        (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
        (φ := fun x : M => refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M)
          Gs σ (smoothOrthoFrame (I := I) g₁ x₀) x)
      intro Y
      exact refoldKernelContractionMonomialFibFixedFrame_apply_section_contMDiff
        (I := I) (M := M) Gs hGs σ (smoothOrthoFrame (I := I) g₁ x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) Y
    exact h_glob x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (refoldKernelContractionMonomialBiContrFib_eq_fixedFrame_on_nbhd (I := I) (M := M)
        g₁ Gs σ x₀ hy))

def refoldKernelContractionMonomialField (g₀ g₁ : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g₀ 0 4) (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (refoldKernelContractionMonomialBiContrFib (I := I) (M := M)
            g₁ (ccTensorFourUnitValueSection (I := I) (M := M) g₀ G) σ x))
      contMDiff_toFun := refoldKernelContractionMonomialBiContrFib_contMDiff (I := I) (M := M)
        g₁ (ccTensorFourUnitValueSection (I := I) (M := M) g₀ G)
        (ccTensorFourUnitValueSection_contMDiff (I := I) (M := M) g₀ G) σ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem refoldKernelContractionMonomialField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (refoldKernelContractionMonomialBiContrFib (I := I) (M := M)
          g₁ (ccTensorFourUnitValueSection (I := I) (M := M) g₀ G) σ x)) := rfl

def refoldKernelContractionField (g₀ g₁ : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g₀ 0 4) (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g₀ 2 2 :=
  (1 / 2 : ℝ) •
    (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₁
      + refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₂
      - refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₃
      - refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₄)

set_option linter.unusedSectionVars false in

theorem refoldKernelContractionField_toSection_eq_kernelFib_sum
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (refoldKernelContractionField (I := I) (M := M)
          g₀ g₁ G σ₁ σ₂ σ₃ σ₄).toSection x) D =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        curvatureRefoldKernelFib (I := I) (M := M) x
          (Tensor0SSpace.toModel (𝕜 := ℝ) D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)])
          σ₁ σ₂ σ₃ σ₄
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
          (ccTensorFourUnitValueSection (I := I) (M := M) g₀ G x) := by
  classical
  rw [refoldKernelContractionField, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_add, Pi.add_apply]
  set Gs : Π b : M, Tensor0SSpace 4 I b :=
    ccTensorFourUnitValueSection (I := I) (M := M) g₀ G with hGs_def
  set F : Equiv.Perm (Fin 4) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Tensor0SSpace 2 I x :=
    fun σ a b => curvatureRefoldMonomialFib (I := I) (M := M) x
      (Tensor0SSpace.toModel (𝕜 := ℝ) D
        ![(smoothOrthoFrame (I := I) g₁ x a x : E),
          (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (Gs x) with hF_def
  have happly : ∀ σ : Equiv.Perm (Fin 4),
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ).toSection x) D =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ a b := by
    intro σ
    exact refoldKernelContractionMonomialFibFixedFrame_apply (I := I) (M := M) Gs σ
      (smoothOrthoFrame (I := I) g₁ x) x D
  change (1 / 2 : ℝ) •
      (((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₁).toSection x)
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₂).toSection x)
        - (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₃).toSection x)
        - (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₄).toSection x))
        D) = _
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, happly σ₁, happly σ₂, happly σ₃, happly σ₄]
  have hker : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      curvatureRefoldKernelFib (I := I) (M := M) x
        (Tensor0SSpace.toModel (𝕜 := ℝ) D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)])
        σ₁ σ₂ σ₃ σ₄
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (Gs x)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) • (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hF_def]
    rw [show curvatureRefoldKernelFib (I := I) (M := M) x
        (Tensor0SSpace.toModel (𝕜 := ℝ) D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)])
        σ₁ σ₂ σ₃ σ₄
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) =
        (1 / 2 : ℝ) •
          (curvatureRefoldMonomialFib (I := I) (M := M) x
              (Tensor0SSpace.toModel (𝕜 := ℝ) D
                ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                  (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₁
              (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            + curvatureRefoldMonomialFib (I := I) (M := M) x
                (Tensor0SSpace.toModel (𝕜 := ℝ) D
                  ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                    (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₂
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            - curvatureRefoldMonomialFib (I := I) (M := M) x
                (Tensor0SSpace.toModel (𝕜 := ℝ) D
                  ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                    (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₃
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            - curvatureRefoldMonomialFib (I := I) (M := M) x
                (Tensor0SSpace.toModel (𝕜 := ℝ) D
                  ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                    (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₄
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x))
        from rfl]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [hker]
  have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) • (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
      (1 / 2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.smul_sum]
  have hdist : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₁ a b)
        + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₂ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₃ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₄ a b) := by
    have hinner : ∀ a : Fin (Module.finrank ℝ E),
        (∑ b : Fin (Module.finrank ℝ E),
          (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
        (∑ b : Fin (Module.finrank ℝ E), F σ₁ a b)
          + (∑ b : Fin (Module.finrank ℝ E), F σ₂ a b)
          - (∑ b : Fin (Module.finrank ℝ E), F σ₃ a b)
          - (∑ b : Fin (Module.finrank ℝ E), F σ₄ a b) := by
      intro a
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsplit, hdist]

theorem refoldKernelContractionField_zero_argument (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 4) σ₁ σ₂ σ₃ σ₄ = 0 := by
  classical
  have hmono : ∀ σ : Equiv.Perm (Fin 4),
      refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
        (0 : SmoothCcTensor g₀ 0 4) σ = 0 := by
    intro σ
    refine SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    rw [refoldKernelContractionMonomialField_toSection]
    have hGs : ccTensorFourUnitValueSection (I := I) (M := M) g₀
        (0 : SmoothCcTensor g₀ 0 4) x = 0 := by
      rw [ccTensorFourUnitValueSection]
      rw [show ((0 : SmoothCcTensor g₀ 0 4).toSection x) = 0 from by
        rw [show (0 : SmoothCcTensor g₀ 0 4) =
            (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 4) from (zero_smul ℝ _).symm,
          SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
          zero_smul]]
      rfl
    have hzero : refoldKernelContractionMonomialBiContrFib (I := I) (M := M) g₁
        (ccTensorFourUnitValueSection (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 4))
        σ x = 0 := by
      apply ContinuousLinearMap.ext
      intro D
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      rw [refoldKernelContractionMonomialBiContrFib,
        refoldKernelContractionMonomialFibFixedFrame_toModel]
      rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel (𝕜 := ℝ) D
              ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                (smoothOrthoFrame (I := I) g₁ x b x : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ)
              (ccTensorFourUnitValueSection (I := I) (M := M) g₀
                (0 : SmoothCcTensor g₀ 0 4) x)
              (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) : Fin 4 → E)
                (σ i))) = 0 from
        Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
          rw [hGs, Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply,
            mul_zero]))]
      simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
        ContinuousMultilinearMap.zero_apply]
    rw [hzero]
    rfl
  rw [refoldKernelContractionField, hmono σ₁, hmono σ₂, hmono σ₃, hmono σ₄]
  rw [show (0 : SmoothCcTensor g₀ 2 2) + 0 - 0 - 0 = 0 from by abel, smul_zero]

set_option linter.unusedSectionVars false in
private theorem foldIteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma foldIteratedCovGrad_zero_arg (g₀ : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g₀ r s j (0 : SmoothCcTensor g₀ r s) = 0 := by
  rw [show (0 : SmoothCcTensor g₀ r s) = (0 : ℝ) • (0 : SmoothCcTensor g₀ r s) from
      (zero_smul ℝ _).symm,
    foldIteratedCovGrad_smul_real, zero_smul]

theorem refoldKernelContractionField_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionField (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2 (0 : SmoothCcTensor g₀ 0 2)) σ₁ σ₂ σ₃ σ₄ = 0 := by
  rw [foldIteratedCovGrad_zero_arg (I := I) (M := M) g₀ 0 2 2,
    refoldKernelContractionField_zero_argument]

theorem refoldKernelContractionField_self (g₀ : SmoothRiemannianMetric I M)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionField (I := I) (M := M) g₀ g₀
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₀)) σ₁ σ₂ σ₃ σ₄ = 0 := by
  rw [metricDifferenceCcTensor_self, refoldKernelContractionField_zero_weight]

set_option linter.unusedSectionVars false in

theorem appCc_refoldKernelContractionField
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g₀ 0 2) :
    appCc (I := I) (M := M) g₀ 2 2
        (refoldKernelContractionField (I := I) (M := M) g₀ g₁ G σ₁ σ₂ σ₃ σ₄) W =
      appCc (I := I) (M := M) g₀ 4 2
        (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
          σ₁ σ₂ σ₃ σ₄) G := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  rw [unitModel, unitModel]
  refine congrArg Tensor0SSpace.toModel ?_
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCc (I := I) (M := M) g₀ 2 2
        (refoldKernelContractionField (I := I) (M := M) g₀ g₁ G σ₁ σ₂ σ₃ σ₄)
        W).toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (refoldKernelContractionField (I := I) (M := M) g₀ g₁ G σ₁ σ₂ σ₃ σ₄).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCc (I := I) (M := M) g₀ 4 2
        (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
          σ₁ σ₂ σ₃ σ₄) G).toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
          σ₁ σ₂ σ₃ σ₄).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [refoldKernelContractionField_toSection_eq_kernelFib_sum (I := I) (M := M)
    g₀ g₁ G σ₁ σ₂ σ₃ σ₄ x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))]
  rw [curvatureRefoldKernelCoeffField_toSection_eq_kernelFib_sum (I := I) (M := M)
    g₀ g₁ (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
    (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W) σ₁ σ₂ σ₃ σ₄ x]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma foldMetricCcTensor_unitModel_apply (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem foldPerturbation_eq_metricDifference (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v) :
    P = metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ := by
  have hsymm : symmS (I := I) (M := M) g₀ P = P :=
    foldSymmS_eq_self (I := I) (M := M) g₀ P hPsymm
  have hmd : metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
      symmS (I := I) (M := M) g₀ P := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    rw [show metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
        metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀
        from rfl]
    rw [unitModel_sub_loc (I := I) (M := M) g₀ 2
      (metricCcTensor (I := I) (M := M) g₀ g₁) (metricCcTensor (I := I) (M := M) g₀ g₀) x]
    rw [ContinuousMultilinearMap.sub_apply]
    rw [foldMetricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      foldMetricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
    rw [show unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ P) x m =
        unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ P) x ![m 0, m 1] from by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ P) x (m 0) (m 1)]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rw [htie x (m 0) (m 1)]
    ring
  rw [hmd, hsymm]

private theorem foldCcTensor22_ext_of_appCc (g₀ : SmoothRiemannianMetric I M)
    (C D : SmoothCcTensor g₀ 2 2)
    (h : ∀ W : SmoothCcTensor g₀ 0 2,
      appCc (I := I) (M := M) g₀ 2 2 C W = appCc (I := I) (M := M) g₀ 2 2 D W) : C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  refine tensorRSSpace_ext 2 2 x (fun u => ?_)
  set V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u))
    with hV_def
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW₀_def
  have h1 : (appCc (I := I) (M := M) g₀ 2 2 C W₀).toSection x =
      (appCc (I := I) (M := M) g₀ 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
          (unitTensor (I := I) (M := M) x)) := by
    have h1' := congrArg (fun (T : TensorRSSpace 0 2 I x) =>
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T)
        (unitTensor (I := I) (M := M) x)) h1
    exact h1'
  have hWval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (unitTensor (I := I) (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW, hV_def]
    change ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
          (1 : ℝ)) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hWval] at h2
  exact h2

set_option linter.unusedSectionVars false in

private theorem foldHalfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v) :
    (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) =
      ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
        + bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁
        + refoldKernelContractionField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := foldPerturbation_eq_metricDifference (I := I) (M := M) g₀ g₁ P htie hPsymm
  rw [hP]
  refine foldCcTensor22_ext_of_appCc (I := I) (M := M) g₀ _ _ (fun W => ?_)
  have hprim :=
    ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient
      (I := I) (M := M) g₀ g₁ P htie hPsymm W
  rw [hP] at hprim
  rw [appCc_smul_left (I := I) (M := M) g₀ 2 2, foldAppCc_sub_left (I := I) (M := M) g₀ 2 2]
  rw [hprim]
  rw [show (appCcRS (I := I) (M := M) g₀ 2 2 2
        (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
          - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
        (ccSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
      - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
          (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)) =
      bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁ from rfl]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
    (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
      + bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
    (refoldKernelContractionField (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
    (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) W]
  rw [appCc_refoldKernelContractionField (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2
      (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
    (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 W]

set_option linter.unusedSectionVars false in

theorem linearizedRicciConnDiffOrder0RiemannHalfBackgroundDifferenceCombinationInputSymm_eq_residualFieldSum
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v) :
    ccInputSymm (I := I) (M := M) g₀
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)) =
      ccInputSymm (I := I) (M := M) g₀
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSymm (I := I) (M := M) g₀
            (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
        + ccInputSymm (I := I) (M := M) g₀
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSymm (I := I) (M := M) g₀
            (refoldKernelContractionField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) := by
  rw [foldHalfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (I := I) (M := M) g₀ g₁ P htie hPsymm]
  rw [ccInputSymm_add (I := I) (M := M) g₀, ccInputSymm_add (I := I) (M := M) g₀,
    ccInputSymm_add (I := I) (M := M) g₀]
  abel

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
