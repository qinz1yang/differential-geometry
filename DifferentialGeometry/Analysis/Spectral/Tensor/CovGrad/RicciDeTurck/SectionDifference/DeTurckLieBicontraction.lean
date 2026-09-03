import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.KoszulCovariantDerivative
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnectionDifferenceCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnectionDifferencePalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.KoszulSecondCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.PrincipalEndomorphismTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.SymmetrizedReindexedCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ReindexingArmDecomposition
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.RiemannFixedFrameBicontraction
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def deTurckConnectionDifferenceCovDeriv (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
    - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
        ((LeviCivita (I := I) g₁).toFun (fun b => Y b) x (X x)) (Z x)
    - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x)
        ((LeviCivita (I := I) g₁).toFun (fun b => Z b) x (X x))

noncomputable def deTurckVFCovDeriv (g₁ g_bg : SmoothRiemannianMetric I M)
    (X : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x (X x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifferenceOp_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b)) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b))
  intro Z
  exact PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g_bg Y.contMDiff Z.contMDiff

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceOp_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b)) x :=
  (connectionDifferenceOp_homSection_contMDiff (I := I) g₁ g_bg).contMDiffAt.mdifferentiableAt (by simp)

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifference_pairing_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b))) x := by
  have h1 : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun b => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b))) x :=
    MDifferentiableAt.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E)
      (E₁ := fun z : M => TangentSpace I z)
      (E₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
      (b := fun b : M => b)
      (ϕ := fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b) (v := fun b => Y b)
      (connectionDifferenceOp_mdiffAt (I := I) g₁ g_bg x) hY
  exact MDifferentiableAt.clm_bundle_apply
    (F₁ := E) (F₂ := E)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z)
    (b := fun b : M => b)
    (ϕ := fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b)) (v := fun b => Z b) h1 hZ

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieCovariantDerivativeA_tensorialAt_Y (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Z : Π b : M, TangentSpace I b) (x : M)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    TensorialAt I E
      (fun Y : Π b : M, TangentSpace I b =>
        deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X Y Z x) x where
  smul {f Y} hf hY := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfYG : (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b ((f • Y) b) (Z b)) = f • G := by
      funext b
      change PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (f b • Y b) (Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul, smul_apply]
    change cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b ((f • Y) b) (Z b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun (f • Y) x (X x)) (Z x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x ((f • Y) x) (cov.toFun Z x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfYG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hY hf (Set.mem_univ x)]
    have hfY_x : (f • Y) x = f x • Y x := rfl
    rw [hfY_x]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Y Y'} hY hY' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGY' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y' b) (Z b))) x :=
      connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hY' hZ
    have hadd_fun : (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) =
        (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y' b) (Z b)) := by
      funext b
      change PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b + Y' b) (Z b) =
        PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y' b) (Z b)
      rw [ContinuousLinearMap.map_add, add_apply]
    change cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun (Y + Y') x (X x)) (Z x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x ((Y + Y') x) (cov.toFun Z x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y' b) (Z b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y' x (X x)) (Z x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y' x) (cov.toFun Z x (X x)))
    rw [hadd_fun, hcovOn.add hGY hGY' (Set.mem_univ x)]
    rw [hcovOn.add hY hY' (Set.mem_univ x)]
    have hYY'_x : (Y + Y') x = Y x + Y' x := rfl
    rw [hYY'_x]
    simp only [add_apply, ContinuousLinearMap.map_add]
    abel

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieCovariantDerivativeA_tensorialAt_Z (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (x : M)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x) :
    TensorialAt I E
      (fun Z : Π b : M, TangentSpace I b =>
        deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X Y Z x) x where
  smul {f Z} hf hZ := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfZG : (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) ((f • Z) b)) = f • G := by
      funext b
      change PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (f b • Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul]
    change cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) ((f • Z) b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((f • Z) x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x) (cov.toFun (f • Z) x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfZG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hZ hf (Set.mem_univ x)]
    have hfZ_x : (f • Z) x = f x • Z x := rfl
    rw [hfZ_x]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Z Z'} hZ hZ' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGZ' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z' b))) x :=
      connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hY hZ'
    have hadd_fun : (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) =
        (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z' b)) := by
      funext b
      change PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b + Z' b) =
        PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z' b)
      rw [ContinuousLinearMap.map_add]
    change cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((Z + Z') x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x) (cov.toFun (Z + Z') x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (Y b) (Z' b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z' x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (Y x) (cov.toFun Z' x (X x)))
    rw [hadd_fun, hcovOn.add hGZ hGZ' (Set.mem_univ x)]
    rw [hcovOn.add hZ hZ' (Set.mem_univ x)]
    have hZZ'_x : (Z + Z') x = Z x + Z' x := rfl
    rw [hZZ'_x]
    simp only [add_apply, ContinuousLinearMap.map_add]
    abel

noncomputable def connectionDifferenceCovDerivOp (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂ (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (A := TangentSpace I x)
    (fun Y Z => deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x) x
    (fun Z hZ => deTurckLieCovariantDerivativeA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (fun Y hY => deTurckLieCovariantDerivativeA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q =
      deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0)
        (smoothExtensionTangent (I := I) x p)
        (smoothExtensionTangent (I := I) x q) x := by
  have hp := smoothExtensionTangent_mdiff (I := I) x p x
  have hq := smoothExtensionTangent_mdiff (I := I) x q x
  have h := TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovariantDerivativeA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovariantDerivativeA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := smoothExtensionTangent (I := I) x p)
    (τ := smoothExtensionTangent (I := I) x q) hp hq
  rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq] at h
  exact h

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieConnectionDifferenceDerivativeCovKernel_apply_field (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) (V_field W_field : Π b : M, TangentSpace I b)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 (V_field x) (W_field x) =
      deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0) V_field W_field x :=
  TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovariantDerivativeA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovariantDerivativeA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := V_field) (τ := W_field) hV hW

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeA_X_congr (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) (hXX : X x = X' x) :
    deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X Y Z x =
      deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X' Y Z x := by
  rw [deTurckConnectionDifferenceCovDeriv, deTurckConnectionDifferenceCovDeriv, hXX]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeA_X_add (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) :
    deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg (X + X') Y Z x =
      deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X Y Z x +
        deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X' Y Z x := by
  have h : (X + X') x = X x + X' x := rfl
  unfold deTurckConnectionDifferenceCovDeriv
  rw [h]
  simp only [map_add, add_apply]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeA_X_smul (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z cX : Π b : M, TangentSpace I b) (c : ℝ) (x : M) (hcX : cX x = c • X x) :
    deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg cX Y Z x =
      c • deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X Y Z x := by
  unfold deTurckConnectionDifferenceCovDeriv
  rw [hcX]
  simp only [map_smul, smul_apply]
  rw [smul_sub, smul_sub]

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieConnectionDifferenceDerivativeCovKernel_add_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v0' p q : TangentSpace I x) :
    connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (v0 + v0') p q =
      connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q + connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0' p
        q := by
  rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend, deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend, deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend]
  rw [deTurckLieCovariantDerivativeA_X_congr (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x (v0 + v0'))
      (smoothExtensionTangent (I := I) x v0 + smoothExtensionTangent (I := I) x v0')
      _ _ x (by
        change smoothExtensionTangent (I := I) x (v0 + v0') x =
          smoothExtensionTangent (I := I) x v0 x + smoothExtensionTangent (I := I) x v0' x
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq, smoothExtensionTangent_eq])]
  rw [deTurckLieCovariantDerivativeA_X_add]

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieConnectionDifferenceDerivativeCovKernel_smul_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v0 p q : TangentSpace I x) :
    connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (c • v0) p q = c • connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
      v0 p q := by
  rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend, deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend]
  rw [deTurckLieCovariantDerivativeA_X_smul (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) _ _
      (smoothExtensionTangent (I := I) x (c • v0)) c x (by
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq])]

def connectionDifferenceCovDerivKernelBilin (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q)
      map_add' := fun v0 v0' => by
        rw [deTurckLieConnectionDifferenceDerivativeCovKernel_add_left, map_add]
      map_smul' := fun c v0 => by
        rw [deTurckLieConnectionDifferenceDerivativeCovKernel_smul_left, map_smul, RingHom.id_apply] }

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem deTurckLieConnectionDifferenceDerivativeKernelBilin_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    connectionDifferenceCovDerivKernelBilin (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q) v1 := by
  rw [connectionDifferenceCovDerivKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

def connectionDifferenceCovDerivKernelBilinSym (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  connectionDifferenceCovDerivKernelBilin (I := I) g₁ g_bg x p q +
    ContinuousLinearMap.flip (connectionDifferenceCovDerivKernelBilin (I := I) g₁ g_bg x p q)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckLieConnectionDifferenceDerivativeKernelBilinSym_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [connectionDifferenceCovDerivKernelBilinSym, add_apply, add_apply,
    ContinuousLinearMap.flip_apply, deTurckLieConnectionDifferenceDerivativeKernelBilin_apply, deTurckLieConnectionDifferenceDerivativeKernelBilin_apply]

def deTurckLieConnectionDifferenceDerivativeSummandFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel E (connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem deTurckLieConnectionDifferenceDerivativeSummandFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (deTurckLieConnectionDifferenceDerivativeSummandFib (I := I) g₁ g_bg x p q D) v =
      (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x q]) *
        (g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)) p q)
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) +
          g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) p q)
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))) := by
  rw [deTurckLieConnectionDifferenceDerivativeSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, smul_apply, Tensor0SSpace.toModel_ofModel,
    smul_eq_mul]
  change Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
          tangentSpaceModelContinuousLinearEquiv (I := I) x q] *
      connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x p q
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) = _
  rw [connectionDifferenceCovDerivKernelBilinSym]
  rfl

def connectionDifferenceCovDerivBiContrFibFixedFrame (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    deTurckLieConnectionDifferenceDerivativeSummandFib (I := I) g₁ g_bg x (B a x) (B b x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg B x D) v =
      (-1 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)) (B a x) (B b x))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) +
          g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) (B a x) (B b x))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))) *
          Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (B a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x (B b x)] := by
  classical
  rw [connectionDifferenceCovDerivBiContrFibFixedFrame, smul_apply,
    Tensor0SSpace.toModel_smul,
    smul_apply, smul_eq_mul]
  apply congrArg (fun z : ℝ => (-1 : ℝ) * z)
  rw [sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, deTurckLieConnectionDifferenceDerivativeSummandFib_toModel]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeA_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (V0 p q : Π b : M, TangentSpace I b)
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg V0 p q b)) := by
  have hcd_pq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg y (p y) (q y))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g_bg hp hq
  have hterm1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0
        (fun y => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg y (p y) (q y)) b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hcd_pq
  have hcovV0p : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 p b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hp
  have hcovV0q : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 q b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hq
  have hterm2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b
        (covApply (LeviCivita (I := I) g₁) V0 p b) (q b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g_bg hcovV0p hq
  have hterm3 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (p b)
        (covApply (LeviCivita (I := I) g₁) V0 q b))) :=
    PDE.DeTurck.connectionDifference_contMDiff (I := I) g₁ g_bg hp hcovV0q
  refine ((hterm1.sub_section hterm2).sub_section hterm3).congr (fun b => ?_)
  rfl

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieConnectionDifferenceDerivativeCovKernel_apply_field3 (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (V0 V_field W_field : Π b : M, TangentSpace I b)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (V0 x) (V_field x) (W_field x) =
      deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg V0 V_field W_field x := by
  rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_field (I := I) g₁ g_bg x (V0 x) V_field W_field hV hW]
  exact deTurckLieCovariantDerivativeA_X_congr (I := I) g₁ g_bg
    (smoothExtensionTangent (I := I) x (V0 x)) V0 V_field W_field x
    (smoothExtensionTangent_eq (I := I) x (V0 x))

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieConnectionDifferenceDerivativeKernelScalar_global (g₁ g_bg : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovariantDerivativeA_section_contMDiff (I := I) g₁ g_bg V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₁.inner x
        (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg V0 p q x) (W x)) := by
    funext x
    rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_field3 (I := I) g₁ g_bg x V0 p q
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeKernelBilinSym_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))
  intro V0
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x (p x) (q x) (V0 x))
  intro W
  have h_scalar0 := deTurckLieConnectionDifferenceDerivativeKernelScalar_global (I := I) g₁ g_bg V0.contMDiff W.contMDiff hp hq
  have h_scalar1 := deTurckLieConnectionDifferenceDerivativeKernelScalar_global (I := I) g₁ g_bg W.contMDiff V0.contMDiff hp hq
  have h_scalar := h_scalar0.add h_scalar1
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [deTurckLieConnectionDifferenceDerivativeKernelBilinSym_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_apply_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (deTurckLieConnectionDifferenceDerivativeSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
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
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))
      (deTurckLieConnectionDifferenceDerivativeKernelBilinSym_homSection_contMDiff (I := I) g₁ g_bg (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x)
          (connectionDifferenceCovDerivKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => deTurckLieConnectionDifferenceDerivativeSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [connectionDifferenceCovDerivBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
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
  rw [hsum, smul_apply, sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg B x)
  intro Y
  exact deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ g_bg B hB Y

def frameConnectionDifferenceCovDerivKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        ContinuousLinearMap.comp ((g₁.inner x).flip v1) (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p)
          +
        ContinuousLinearMap.comp ((g₁.inner x).flip v0) (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v1 p)
      map_add' := fun p p' => by
        ext q
        simp only [add_apply, ContinuousLinearMap.comp_apply,
          (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0).map_add p p',
          (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v1).map_add p p', add_apply,
          map_add]
        ring
      map_smul' := fun c p => by
        ext q
        simp only [smul_apply, ContinuousLinearMap.comp_apply,
          RingHom.id_apply, (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0).map_smul c p,
          (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v1).map_smul c p, map_smul,
          add_apply, smul_apply, smul_eq_mul]
        ring }

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem frameConnectionDifferenceCovariantDerivativeKernel_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameConnectionDifferenceCovDerivKernel (I := I) g₁ g_bg x v0 v1 p q =
      g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [frameConnectionDifferenceCovDerivKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

def connectionDifferenceCovDerivBiContrFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x

section

private local instance frameTangentSpaceNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) := by
  change NormedAddCommGroup E
  infer_instance

private local instance frameTangentSpaceNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x) := by
  change NormedSpace ℝ E
  infer_instance

private def frameBilinFormToModel (x : M) :
    (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
  DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel (TangentSpace I x)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem frameBilinFormToModel_symm_apply (x : M)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ)
    (v w : TangentSpace I x) :
    (frameBilinFormToModel (I := I) x).symm T v w = T ![v, w] := by
  exact DifferentialGeometry.Tensor.Multilinear.biForm₂ToModel_symm_apply (TangentSpace I x) T v w

end

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieConnectionDifferenceDerivativeBiContrFib_eq_fixedFrame_on_nbhd_aux
    (g₁ g_bg : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg y =
      connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀)
        y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  let DModel := Tensor0SSpace.toModel D
  rw [connectionDifferenceCovDerivBiContrFib,
    deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel,
    deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel]
  apply congrArg (fun z : ℝ => (-1 : ℝ) * z)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner y (connectionDifferenceCovDerivOp (I := I) g₁ g_bg y
            ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 0)) (Bf a) (Bf b))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 1)) +
          g₁.inner y (connectionDifferenceCovDerivOp (I := I) g₁ g_bg y
            ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 1)) (Bf a) (Bf b))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 0))) *
          DModel
            ![tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf a),
              tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf b)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnectionDifferenceCovDerivKernel (I := I) g₁ g_bg y
            ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 0))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 1)) (Bf a) (Bf b) *
          (frameBilinFormToModel (I := I) y).symm DModel (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnectionDifferenceCovariantDerivativeKernel_apply (I := I) g₁ g_bg y
      ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 1)) (Bf a) (Bf b),
      frameBilinFormToModel_symm_apply (I := I) y DModel (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameConnectionDifferenceCovDerivKernel (I := I) g₁ g_bg y
      ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v 1)))
    ((frameBilinFormToModel (I := I) y).symm DModel)
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeBiContrFib_eq_fixedFrame_on_nbhd
    (g₁ g_bg : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg y =
      connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg
        (smoothOrthoFrame (I := I) g₁ x₀) y :=
  deTurckLieConnectionDifferenceDerivativeBiContrFib_eq_fixedFrame_on_nbhd_aux
    (I := I) g₁ g_bg x₀ hy

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_contMDiff (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (deTurckLieConnectionDifferenceDerivativeBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ g_bg x₀ hy))

def deTurckVectorFieldCovariantDerivativeEndomorphism (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVectorFieldCovariantDerivativeEndomorphism_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x v =
      deTurckVFCovDeriv (I := I) g₁ g_bg (smoothExtensionTangent (I := I) x v) x := by
  rw [deTurckVectorFieldCovariantDerivativeEndomorphism, deTurckVFCovDeriv, smoothExtensionTangent_eq]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x)) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x : M => deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x)
  intro Y
  have hdvf : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
        : Π b : M, TangentSpace I b) b)) :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hcov := covApply_contMDiff (cov := LeviCivita (I := I) g₁)
    (X := fun b => Y b)
    (T := fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
      : Π b : M, TangentSpace I b) b)
    Y.contMDiff hdvf
  exact hcov

def deTurckLieCovariantDerivativeInsertionFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeInsertionFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0
            (tangentLinearMapToModel
              (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1
            (tangentLinearMapToModel
              (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) (v 1))) := by
  rw [deTurckLieCovariantDerivativeInsertionFib, add_apply, Tensor0SSpace.toModel_add,
    add_apply,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

omit [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieCovariantDerivativeInsertionFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 0
    (fun x => deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x)
    (deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff (I := I) g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 1
    (fun x => deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x)
    (deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff (I := I) g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieCovariantDerivativeInsertionFib]
  rfl

def deTurckLieFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x + deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckLieFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))) := by
  classical
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x)))
    (deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff (I := I) g₁ g_bg)
    (deTurckLieCovariantDerivativeInsertionFib_contMDiff (I := I) g₁ g_bg)
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieFib]
  rfl

def deTurckLieCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckLieCoeffField_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem exists_ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ∃ R_Lie : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 R_Lie W) x v =
          (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                    else smoothOrthoFrame (I := I) g₁ x b x) *
                (g₁.inner x
                    (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                        (v 1)
                  + g₁.inner x
                    (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                        (v 0)))
            + (unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then
                    deTurckVFCovDeriv (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0)) x
                    else v 1)
                + unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then v 0
                    else deTurckVFCovDeriv (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  classical
  refine ⟨deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg, fun W x v => ?_⟩
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  let vModel : Fin 2 → E := fun i => v i
  rw [deTurckLieFib, add_apply, Tensor0SSpace.toModel_add]
  change Tensor0SSpace.toModel
      (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x D) vModel +
    Tensor0SSpace.toModel
      (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x D) vModel = _
  congr 1
  · rw [connectionDifferenceCovDerivBiContrFib, deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                    (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))
                    from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend, deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp <;> rfl
  · rw [deTurckLieCovariantDerivativeInsertionFib_toModel]
    rw [tangentLinearMapToModel_apply, tangentLinearMapToModel_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply,
      deTurckVectorFieldCovariantDerivativeEndomorphism_apply,
      deTurckVectorFieldCovariantDerivativeEndomorphism_apply,
      tangentSpaceModelContinuousLinearEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j
      · simp; rfl
      · simp; rfl
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j
      · simp; rfl
      · simp; rfl

noncomputable def ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem ricciArmOrder0DeTurckLieCoeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl


omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciArmOrder0DeTurckLieCoeff_operatorFieldApplication_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg) W)
        x v =
      (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                    (v 0)))
        + (unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then
                deTurckVFCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0)) x
                else v 1)
            + unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then v 0
                else deTurckVFCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0DeTurckLieCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  let vModel : Fin 2 → E := fun i => v i
  rw [deTurckLieFib, add_apply, Tensor0SSpace.toModel_add]
  change Tensor0SSpace.toModel
      (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x D) vModel +
    Tensor0SSpace.toModel
      (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x D) vModel = _
  congr 1
  · rw [connectionDifferenceCovDerivBiContrFib, deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
                    (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))
                    from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend, deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp <;> rfl
  · rw [deTurckLieCovariantDerivativeInsertionFib_toModel]
    rw [tangentLinearMapToModel_apply, tangentLinearMapToModel_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply,
      deTurckVectorFieldCovariantDerivativeEndomorphism_apply,
      deTurckVectorFieldCovariantDerivativeEndomorphism_apply,
      tangentSpaceModelContinuousLinearEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j
      · simp; rfl
      · simp; rfl
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j
      · simp; rfl
      · simp; rfl

noncomputable def symmAbsorbedOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))


omit [SigmaCompactSpace M] in
theorem symmAbsorbedOrder0DeTurckLieCoeff_operatorFieldApplication_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_operatorFieldApplication_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
