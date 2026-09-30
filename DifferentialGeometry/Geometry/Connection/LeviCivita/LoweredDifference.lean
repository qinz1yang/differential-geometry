import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Bundle.Section
import Mathlib.Tactic.FinCases

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Multilinear
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def metricLoweredConnectionDifferenceCovector (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) (m 2)
      map_update_add' := by
        have h01 : (0 : Fin 3) ≠ 1 := by decide
        have h02 : (0 : Fin 3) ≠ 2 := by decide
        have h10 : (1 : Fin 3) ≠ 0 := by decide
        have h12 : (1 : Fin 3) ≠ 2 := by decide
        have h20 : (2 : Fin 3) ≠ 0 := by decide
        have h21 : (2 : Fin 3) ≠ 1 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h10, h12, h20, h21, not_false_eq_true,
            map_add, add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 3) ≠ 1 := by decide
        have h02 : (0 : Fin 3) ≠ 2 := by decide
        have h10 : (1 : Fin 3) ≠ 0 := by decide
        have h12 : (1 : Fin 3) ≠ 2 := by decide
        have h20 : (2 : Fin 3) ≠ 0 := by decide
        have h21 : (2 : Fin 3) ≠ 1 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h10, h12, h20, h21, not_false_eq_true,
            map_smul, smul_apply]
      cont := by
        have hconn : Continuous (fun m : Fin 3 → TangentSpace I x =>
            PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) :=
          ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x).continuous.comp
            (continuous_apply 0)).clm_apply (continuous_apply 1)
        exact ((g₀.inner x).continuous.comp hconn).clm_apply (continuous_apply 2) }
    : Tensor0SSpace 3 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma metricLoweredConnectionDifferenceCovector_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    metricLoweredConnectionDifferenceCovector (I := I) g₀ g₁ x m =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma metricLoweredConnectionDifference_scalar_contMDiffAt (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 V1 V2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (V0 x) (V1 x)) (V2 x)) x₀ := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (V0 x) (V1 x))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g₀ V0.contMDiff V1.contMDiff
  have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M =>
        (⟨b, g₀.inner b (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (V0 b) (V1 b)) (V2 b)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
    (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g₀.contMDiff.contMDiffOn hconn.contMDiffOn V2.contMDiff.contMDiffOn x₀
      (mem_univ x₀)).contMDiffAt univ_mem
  rw [Bundle.contMDiffAt_totalSpace] at h_total
  exact h_total.2

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricLoweredConnectionDifferenceCovector_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) x (metricLoweredConnectionDifferenceCovector (I := I) g₀ g₁ x)) := by
  classical
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (metricLoweredConnectionDifferenceCovector (I := I) g₀ g₁ x :
        Bundle.continuousMultilinearMap ℝ 3 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Y (σ 0) x) (Y (σ 1) x)) (Y (σ 2) x)) x₀ :=
    metricLoweredConnectionDifference_scalar_contMDiffAt (I := I) g₀ g₁ (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact e₁.symmL_apply hx₁ (b (σ 0))
  have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
    rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact e₁.symmL_apply hx₁ (b (σ 1))
  have hframe2 : e₁.symmL ℝ x (b (σ 2)) = (Y (σ 2)) x := by
    rw [hYx (σ 2), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact e₁.symmL_apply hx₁ (b (σ 2))
  change g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1)))) (e₁.symmL ℝ x (b (σ 2))) = _
  rw [hframe0, hframe1, hframe2]

def metricLoweredConnectionDifferenceField (g₀ g₁ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricLoweredConnectionDifferenceCovector (I := I) g₀ g₁ x,
    metricLoweredConnectionDifferenceCovector_contMDiff (I := I) g₀ g₁⟩

end DifferentialGeometry.Geometry.Connection
