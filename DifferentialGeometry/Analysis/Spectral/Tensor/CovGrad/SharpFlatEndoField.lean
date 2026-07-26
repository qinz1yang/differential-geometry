import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier

/-!
# Sharp-flat covector endomorphism field

This file packages the smooth covector endomorphism `g₀♭ ∘ g₁♯` below the
connection-difference jet tower.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The metric-flat operator field is smooth as a Hom-bundle section. -/
theorem g0FlatField_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₀ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SSpace 1 I z)
    (φ := fun x : M => g0FlatCLM (I := I) g₀ x)
  intro Z
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (g0FlatCLM (I := I) g₀ x (Z x) :
        Bundle.continuousMultilinearMap ℝ 1 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (Z x) (Y (σ 0) x)) x₀ := by
    have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b, g₀.inner b (Z b) (Y (σ 0) b)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
      (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
        g₀.contMDiff.contMDiffOn Z.contMDiff.contMDiffOn
        (Y (σ 0)).contMDiff.contMDiffOn x₀ (mem_univ x₀)).contMDiffAt univ_mem
    rw [Bundle.contMDiffAt_totalSpace] at h_total
    exact h_total.2
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change (g0FlatCLM (I := I) g₀ x (Z x)) (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) = _
  rw [show (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) =
      (fun _ : Fin 1 => e₁.symmL ℝ x (b (σ 0))) from by
    funext j; fin_cases j; rfl]
  rw [hframe0]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

/-- The fibre family `g₀♭ ∘ g₁♯` is smooth as a covector-endomorphism section. -/
theorem sharpFlatEndoCcFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] Tensor0SSpace 1 I z) x
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun z : M => Tensor0SSpace 1 I z)
    (F₂ := Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SSpace 1 I z)
    (φ := fun x : M => (g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₁ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₁) Y.contMDiff
  have hflatsharpY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) g₀) hsharpY
  refine hflatsharpY.congr (fun x => ?_)
  rfl

/-- The smooth covector endomorphism `g₀♭ ∘ g₁♯`, tagged by `g₀`. -/
def sharpFlatEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 1 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))
      contMDiff_toFun := sharpFlatEndoCcFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] lemma sharpFlatEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpFlatEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x)) := rfl

/-- Scalar evaluation of the sharp-flat covector endomorphism. -/
theorem sharpFlatEndo_eval (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) w =
      cotangentToDual (I := I) om (gInvRaisedEndo (I := I) g₀ g₁ x w) := by
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM, inner_sharp_mixed (I := I) (M := M)]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
