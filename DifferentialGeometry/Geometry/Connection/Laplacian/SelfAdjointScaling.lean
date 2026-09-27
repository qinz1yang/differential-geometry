import DifferentialGeometry.Geometry.Connection.TensorNabla.Congruence
import DifferentialGeometry.Geometry.Connection.Laplacian.Congruence
import DifferentialGeometry.Geometry.Connection.Laplacian.Scaling

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Curvature
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem rawBundleConnLap_selfAdjoint_scaleMetric_const_smul
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (D C : CovariantDerivative I F V) (hD : D.IsMetricCompatible) (hC : C.IsMetricCompatible)
    (hDs : ContMDiffCovariantDerivative D ∞)
    (hDC : ∀ (σ : ∀ x, V x) (x : M),
      MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x → C σ x = D σ x)
    (a : ℝ) :
    let P := selfAdjointSubbundle (I := I) (F := F)
      (V := V) (n := ∞)
    letI := P.totalSpaceTopology
    letI := P.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin P.rank → ℝ, fun y => P.fiber y⟯) (x : M),
      rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
        (scaleMetric c hc g) (C.selfAdjoint hC)
        (fun y => a • A y) x =
      (c⁻¹ * a) • rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
        g (D.selfAdjoint hD) A x := by
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let : ∀ y, CompleteSpace (V y) := fun y => FiniteDimensional.complete ℝ (V y)
  let P := selfAdjointSubbundle (I := I) (F := F)
    (V := V) (n := ∞)
  let := P.totalSpaceTopology
  let normP : ∀ y, NormedAddCommGroup (P.fiber y) := fun y => inferInstance
  let spaceP : ∀ y, NormedSpace ℝ (P.fiber y) := fun y => inferInstance
  let := P.fiberBundle
  let := P.vector_bundle
  let := P.contMDiffVectorBundle
  dsimp only
  intro A x
  have hSC (σ : Cₛ^∞⟮I; Fin P.rank → ℝ, fun y => P.fiber y⟯) (y : M) :
      C.selfAdjoint hC σ y = D.selfAdjoint hD σ y := by
    apply ContinuousLinearMap.ext
    intro X
    exact selfAdjoint_apply_congr C D hC hD (fun σ hσ => hDC σ y hσ) σ X
  let := hDs
  let := contMDiff_selfAdjoint D hD
  let DS := D.selfAdjoint hD
  let CS := C.selfAdjoint hC
  let B : Cₛ^∞⟮I; Fin P.rank → ℝ, fun y => P.fiber y⟯ :=
    ⟨fun y => a • A y, A.contMDiff.const_smul_section⟩
  have hLap := rawBundleConnLap_congr DS CS inferInstance
    (fun σ y => (hSC σ y).symm) (scaleMetric c hc g) B x
  exact hLap.symm.trans (@rawBundleConnLap_scaleMetric_const_smul
    E _ _ _ H _ I M _ _ _ _ (Fin P.rank → ℝ) _ _ (fun y => P.fiber y) _
    normP spaceP _ _ _ _ c hc g DS inferInstance A
    (A.contMDiff.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) a x)

end DifferentialGeometry.Geometry.Connection
