import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnectionDifferenceQuadraticBound

import DifferentialGeometry.Geometry.Metric.Convergence.LaplacianDifference
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeAlgebra
import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelDiffKoszulDeriv
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle

noncomputable section

open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance tensorRSNormedAddCommGroupOfRiemannianBundle
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y)] (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TensorRSSpace r s I y) x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem covGrad_connectionDifferenceSection_flat_eval_eq_inner
    (g₂ g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₂ 1 2 (connectionDifferenceSection (I := I) g₁ g₂)).toSection x)
          (g0FlatCLM (I := I) g₂ x
            (covDerivConnectionDifference (I := I) g₂ g₁
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)))
        (Fin.cons v (Fin.cons u ![w])) =
      g₂.inner x
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x) := by
  classical
  set A : TangentSpace I x :=
    covDerivConnectionDifference (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  set Xsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXsec_def
  set Ysec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec_def
  set Zsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hZsec_def
  have hXx : Xsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hA_bridge : covDerivConnectionDifference (I := I) g₂ g₁ Xsec Zsec Ysec x = A := by
    rw [hA_def]; rfl
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) x
    (g0FlatCLM (I := I) g₂ x A)
  have hbridge := connectionDifferenceSection_covGrad_eq_covDerivConnectionDifference (I := I) g₁ g₂ om Xsec Ysec Zsec x
  rw [hom, hXx, hYx, hZx, hA_bridge] at hbridge
  have hflatA : (g0FlatCLM (I := I) g₂ x A) (fun _ : Fin 1 => A) = g₂.inner x A A := by
    rw [show (g0FlatCLM (I := I) g₂ x A) (fun _ : Fin 1 => A) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₂ x A) A from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₂ x A A]
  rw [hflatA] at hbridge
  rw [hA_def]
  exact hbridge

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem covDerivConnectionDifference_fibreNorm_le
    (g₂ g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 1 3 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₂ 1 3
    Real.sqrt (g₂.inner x
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)) ≤
      ‖((covGrad (I := I) (M := M) g₂ 1 2 (connectionDifferenceSection (I := I) g₁ g₂)).toSection x :
          Tensor0SBundle.TensorRSSpace 1 3 I x)‖ *
        Real.sqrt (g₂.inner x v v) * Real.sqrt (g₂.inner x w w) *
          Real.sqrt (g₂.inner x u u) := by
  classical
  let instW : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 1 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₂ 1 3
  set W : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₂ 1 2 (connectionDifferenceSection (I := I) g₁ g₂)).toSection x with hW_def
  set A : TangentSpace I x :=
    covDerivConnectionDifference (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  have hAA_nn : 0 ≤ g₂.inner x A A := metric_inner_self_nonneg (I := I) (M := M) g₂ x A
  set NA : ℝ := Real.sqrt (g₂.inner x A A) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hbridge := covGrad_connectionDifferenceSection_flat_eval_eq_inner (I := I) (M := M) g₂ g₁ x v w u
  rw [← hA_def, ← hW_def] at hbridge
  have hprim := abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt
    (I := I) (M := M) g₂ x W A v u w
  rw [hbridge] at hprim
  rw [abs_of_nonneg hAA_nn] at hprim
  have hAA_sq : g₂.inner x A A = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hAA_nn]
  have hvv_nn : 0 ≤ g₂.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₂ x v
  have hww_nn : 0 ≤ g₂.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g₂ x w
  have huu_nn : 0 ≤ g₂.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₂ x u
  set Sv : ℝ := Real.sqrt (g₂.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₂.inner x w w) with hSw_def
  set Su : ℝ := Real.sqrt (g₂.inner x u u) with hSu_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSu_nn : 0 ≤ Su := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Su * Sw := by
    have hp := hprim
    rw [hAA_sq] at hp
    rw [Real.sqrt_sq hNA_nn] at hp
    exact hp
  rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
  · rw [← hNA0]
    exact mul_nonneg (mul_nonneg (mul_nonneg hNW_nn hSv_nn) hSw_nn) hSu_nn
  · have hkey : NA * NA ≤ NA * (NW * Sv * Su * Sw) := by
      rw [show NA * NA = NA ^ 2 from by ring]
      refine le_trans hprim' ?_
      apply le_of_eq; ring
    have hcancel := le_of_mul_le_mul_left hkey hNApos
    calc NA ≤ NW * Sv * Su * Sw := hcancel
      _ = NW * Sv * Sw * Su := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem field_eq_mcd1
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
        (Tensor0SBundle.metricTensorField (I := I) g₁)
        (DifferentialGeometry.Geometry.Connection.metricField_totalReg (I := I) g₁ g₂))
      = metricCovDeriv (I := I) g₁ g₂ 1 := by
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  apply DFunLike.ext
  intro x
  rw [Tensor0SBundle.totalNabla0S_apply]
  exact (metricCovDerivStep_apply (I := I) g₂ 0
    (Tensor0SBundle.metricTensorField (I := I) g₁) x).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem nabla3_eq_mcd2
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) W
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
          (Tensor0SBundle.metricTensorField (I := I) g₁)
          (DifferentialGeometry.Geometry.Connection.metricField_totalReg (I := I) g₁ g₂)) x slots
      = metricCovDeriv (I := I) g₁ g₂ 2 x (Fin.cons (W x) slots) := by
  rw [field_eq_mcd1 (I := I) g₁ g₂,
    show metricCovDeriv (I := I) g₁ g₂ 2
        = metricCovDerivStep (I := I) g₂ 1 (metricCovDeriv (I := I) g₁ g₂ 1) from rfl,
    metricCovDerivStep_apply]
  exact (Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    3 (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) W
    (metricCovDeriv (I := I) g₁ g₂ 1) x slots).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_normSq0S_comp
    {K : Set M} {g₂ g₁ : SmoothRiemannianMetric I M} {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    {x : M} (hx : x ∈ K) (s : ℕ)
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x s A) ≤
      Real.sqrt (Λ ^ s) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x s A) := by
  obtain ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn (I := I) (K := K) (g := g₂) (h := g₁)
      (C := Λ) hEq hx
  have hsq : Tensor0SBundle.normSq0S (I := I) g₁ x s A
      ≤ Λ ^ s * Tensor0SBundle.normSq0S (I := I) g₂ x s A :=
    Tensor0SBundle.normSq0S_diag_le (I := I) (g := g₂) (h := g₁) (x := x) (s := s)
      basis μ Λ hginv hhinv hμ_nonneg hμ_le A
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x s A)
      ≤ Real.sqrt (Λ ^ s * Tensor0SBundle.normSq0S (I := I) g₂ x s A) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Λ ^ s) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x s A) := by
        rw [Real.sqrt_mul (pow_nonneg (le_trans zero_le_one hEq.1) s)]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lcDiff_covOne_le
    {K : Set M} (g h : SmoothRiemannianMetric I M) {C : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K) :
    Real.sqrt
        (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
            (leviCivitaConnectionOfMetric (I := I) h)
            (leviCivitaConnectionOfMetric (I := I) g) x)) ≤
      (3 / 2 : ℝ) * (Real.sqrt (C ^ 3) * metricCovDerivNorm (I := I) 1 h g x) := by
  classical
  obtain ⟨_, basis, hhinv, _, _, _⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn (I := I)
      (metricUniformEquivalentOn_symm (I := I) hEq) hx
  exact diff_le_covOne_basis_ref_lc (I := I) h g hx C hEq basis hhinv


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connectionDifference_gJet_le
    {K : Set M} {g₂ g₁ : SmoothRiemannianMetric I M} {Λ Λ' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    {x : M} (hx : x ∈ K) (w u : TangentSpace I x) :
    Real.sqrt (g₂.inner x
        ((CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x u) w)
        ((CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x u) w)) ≤
      (3 / 2 * Λ ^ 3 * Λ') *
        Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u) := by
  classical
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hL0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : (0 : ℝ) ≤ Λ := le_of_lt hL0
  have hJ1 : metricCovDerivNorm (I := I) 1 g₁ g₂ x ≤ Λ' := hJet1 x hx
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) hJ1
  have hs2 : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hLnn
  have hs3 : Real.sqrt (Λ ^ 3) = Λ * Real.sqrt Λ := by
    rw [show Λ ^ 3 = Λ ^ 2 * Λ by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hLnn]
  have hvec : ∀ z : TangentSpace I x,
      Real.sqrt (g₁.inner x z z) ≤
        Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := by
    intro z
    calc
      Real.sqrt (g₁.inner x z z) ≤ Real.sqrt (Λ * g₂.inner x z z) :=
        Real.sqrt_le_sqrt (hEq.2 x hx z).2
      _ = Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := Real.sqrt_mul hLnn _
  have hout : ∀ z : TangentSpace I x,
      Real.sqrt (g₂.inner x z z) ≤
        Real.sqrt Λ * Real.sqrt (g₁.inner x z z) := by
    intro z
    have h := (hEq.2 x hx z).1
    have h' : g₂.inner x z z ≤ Λ * g₁.inner x z z := by
      have h2 := mul_le_mul_of_nonneg_left h hLnn
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hL0), one_mul] at h2
      exact h2
    calc
      Real.sqrt (g₂.inner x z z) ≤ Real.sqrt (Λ * g₁.inner x z z) :=
        Real.sqrt_le_sqrt h'
      _ = Real.sqrt Λ * Real.sqrt (g₁.inner x z z) := Real.sqrt_mul hLnn _
  have hNA :
      Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤
        3 / 2 * (Λ * Real.sqrt Λ * Λ') := by
    have h := lcDiff_covOne_le (I := I) g₂ g₁ hEq hx
    rw [hs3] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ1
        (mul_nonneg hLnn (Real.sqrt_nonneg _)))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
  let A : TangentSpace I x :=
    (CovariantDerivative.difference
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x u) w
  have hg1 :
      Real.sqrt (g₁.inner x A A) ≤
        Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
          Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    dsimp only [A]
    exact Tensor0SBundle.connectionDifferenceVec_norm_le (I := I) g₁
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) w u
  have hstep :
      Real.sqrt (g₁.inner x A A) ≤
        3 / 2 * (Λ * Real.sqrt Λ * Λ') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)) := by
    refine le_trans hg1 ?_
    exact mul_le_mul
      (mul_le_mul hNA (hvec w) (Real.sqrt_nonneg _) (by positivity))
      (hvec u) (Real.sqrt_nonneg _) (by positivity)
  change Real.sqrt (g₂.inner x A A) ≤ _
  calc
    Real.sqrt (g₂.inner x A A) ≤
        Real.sqrt Λ * Real.sqrt (g₁.inner x A A) := hout A
    _ ≤ Real.sqrt Λ *
        (3 / 2 * (Λ * Real.sqrt Λ * Λ') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u))) :=
      mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)
    _ = (3 / 2 * Λ ^ 3 * Λ') *
        Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u) := by
      linear_combination
        (3 / 2 * Λ' * (Real.sqrt Λ ^ 2 + Λ) *
          (Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u)) * Λ) * hs2


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem covDerivConnectionDifference_g1_le
    (g₂ g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    Real.sqrt (g₁.inner x
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)) ≤
      (3 / 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
            (metricCovDeriv (I := I) g₁ g₂ 2 x)) +
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
              (metricCovDeriv (I := I) g₁ g₂ 1 x)) *
            Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x))) *
        Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x w w) *
          Real.sqrt (g₁.inner x u u) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₁ x
  set B : TangentSpace I x :=
    covDerivConnectionDifference (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hBdef
  set Wsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hWsec
  set Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hXsec
  set Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec
  set Zsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x B)
      (smoothExtensionTangent_contMDiff (I := I) x B) with hZsec
  have hWx : Wsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hXx : Xsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = B := smoothExtensionTangent_eq (I := I) x B
  have hAbr : covDerivConnectionDifference (I := I) g₂ g₁ Wsec Xsec Ysec x = B := by rw [hBdef]; rfl
  have hkos := DifferentialGeometry.Geometry.Connection.connectionDifference_koszul_deriv
    (I := I) g₁ g₂ Wsec Xsec Ysec Zsec x
  rw [hAbr, hXx, hYx, hZx] at hkos
  rw [nabla3_eq_mcd2 (I := I) g₁ g₂ Wsec x ![w, u, B],
    nabla3_eq_mcd2 (I := I) g₁ g₂ Wsec x ![u, w, B],
    nabla3_eq_mcd2 (I := I) g₁ g₂ Wsec x ![B, w, u], hWx] at hkos
  set Avec : TangentSpace I x :=
    CovariantDerivative.difference
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁)
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) x u w with hAvec
  have h4 : Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) Wsec
        (Tensor0SBundle.metricTensorField (I := I) g₁) x ![Avec, B]
      = metricCovDeriv (I := I) g₁ g₂ 1 x (Fin.cons v ![Avec, B]) := by
    have h := (metricCovDeriv_one_apply_section (I := I) g₁ g₂ Wsec x ![Avec, B]).symm
    rw [hWx] at h
    exact h
  rw [h4] at hkos
  have hcs4 : ∀ a b c d : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 2 x (Fin.cons a ![b, c, d])| ≤
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4 (metricCovDeriv (I := I) g₁ g₂ 2 x)) *
          (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
            Real.sqrt (g₁.inner x c c) * Real.sqrt (g₁.inner x d d)) := by
    intro a b c d
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 4 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 2 x) (Fin.cons a ![b, c, d])
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 4, Real.sqrt (g₁.inner x (![a, b, c, d] i) (![a, b, c, d] i))) = _
    simp [Fin.prod_univ_four]
  have hcs3 : ∀ a b c : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 1 x (Fin.cons a ![b, c])| ≤
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3 (metricCovDeriv (I := I) g₁ g₂ 1 x)) *
          (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
            Real.sqrt (g₁.inner x c c)) := by
    intro a b c
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 3 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 1 x) (Fin.cons a ![b, c])
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 3, Real.sqrt (g₁.inner x (![a, b, c] i) (![a, b, c] i))) = _
    simp [Fin.prod_univ_three]
  have hSA : Real.sqrt (g₁.inner x Avec Avec) ≤
      Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    rw [hAvec]
    exact Tensor0SBundle.connectionDifferenceVec_norm_le (I := I) g₁
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) w u
  have hBB_nn : 0 ≤ g₁.inner x B B := metric_inner_self_nonneg (I := I) (M := M) g₁ x B
  have hBBsq : g₁.inner x B B = Real.sqrt (g₁.inner x B B) ^ 2 := (Real.sq_sqrt hBB_nn).symm
  rw [hBBsq] at hkos
  have hT1 := hcs4 v w u B
  have hT2 := hcs4 v u w B
  have hT3 := hcs4 v B w u
  have hT4 := hcs3 v Avec B
  have hT4' : |metricCovDeriv (I := I) g₁ g₂ 1 x (Fin.cons v ![Avec, B])| ≤
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3 (metricCovDeriv (I := I) g₁ g₂ 1 x)) *
          Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
        (Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x w w) *
          Real.sqrt (g₁.inner x u u) * Real.sqrt (g₁.inner x B B)) := by
    refine le_trans hT4 ?_
    have hstep :
        Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x Avec Avec) *
            Real.sqrt (g₁.inner x B B) ≤
          Real.sqrt (g₁.inner x v v) *
            (Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
                (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
              Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u)) *
            Real.sqrt (g₁.inner x B B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSA (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    calc _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
              (metricCovDeriv (I := I) g₁ g₂ 1 x)) *
            (Real.sqrt (g₁.inner x v v) *
              (Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
                  (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
                Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u)) *
              Real.sqrt (g₁.inner x B B)) :=
          mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)
      _ = _ := by ring
  have habs1 := le_abs_self (metricCovDeriv (I := I) g₁ g₂ 2 x (Fin.cons v ![w, u, B]))
  have habs2 := le_abs_self (metricCovDeriv (I := I) g₁ g₂ 2 x (Fin.cons v ![u, w, B]))
  have habs3 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 2 x (Fin.cons v ![B, w, u]))
  have habs4 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 1 x (Fin.cons v ![Avec, B]))
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (g₁.inner x B B)) with hSB0 | hSBpos
  · rw [← hSB0]
    positivity
  · have hmul :
        Real.sqrt (g₁.inner x B B) * (2 * Real.sqrt (g₁.inner x B B)) ≤
          Real.sqrt (g₁.inner x B B) *
            ((3 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
                  (metricCovDeriv (I := I) g₁ g₂ 2 x)) +
                2 * (Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
                      (metricCovDeriv (I := I) g₁ g₂ 1 x)) *
                    Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
                      (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                        (leviCivitaConnectionOfMetric (I := I) g₁)
                        (leviCivitaConnectionOfMetric (I := I) g₂) x)))) *
              (Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x w w) *
                Real.sqrt (g₁.inner x u u))) := by
      nlinarith [hkos, hT1, hT2, hT3, hT4', habs1, habs2, habs3, habs4]
    have hdiv := le_of_mul_le_mul_left hmul hSBpos
    linarith


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem covDerivConnectionDifference_gJet_le
    {K : Set M} {g₂ g₁ : SmoothRiemannianMetric I M} {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    {x : M} (hx : x ∈ K) (v w u : TangentSpace I x) :
    Real.sqrt (g₂.inner x
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnectionDifference (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)) ≤
      3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) *
        Real.sqrt (g₂.inner x v v) * Real.sqrt (g₂.inner x w w) *
          Real.sqrt (g₂.inner x u u) := by
  classical
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hL0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : (0 : ℝ) ≤ Λ := le_of_lt hL0
  have hJ1 : metricCovDerivNorm (I := I) 1 g₁ g₂ x ≤ Λ' := hJet1 x hx
  have hJ2 : metricCovDerivNorm (I := I) 2 g₁ g₂ x ≤ Λ'' := hJet2 x hx
  have hJ1nn : (0 : ℝ) ≤ metricCovDerivNorm (I := I) 1 g₁ g₂ x := Real.sqrt_nonneg _
  have hJ2nn : (0 : ℝ) ≤ metricCovDerivNorm (I := I) 2 g₁ g₂ x := Real.sqrt_nonneg _
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans hJ1nn hJ1
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans hJ2nn hJ2
  have hs2 : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hLnn
  have hs4 : Real.sqrt (Λ ^ 4) = Λ ^ 2 := by
    rw [show Λ ^ 4 = (Λ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hs3 : Real.sqrt (Λ ^ 3) = Λ * Real.sqrt Λ := by
    rw [show Λ ^ 3 = Λ ^ 2 * Λ by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hLnn]
  have hcoefnn : (0 : ℝ) ≤ Λ * Real.sqrt Λ * Λ' :=
    mul_nonneg (mul_nonneg hLnn (Real.sqrt_nonneg _)) hL'nn
  have hcore := covDerivConnectionDifference_g1_le (I := I) g₂ g₁ x v w u
  have hM2 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
      (metricCovDeriv (I := I) g₁ g₂ 2 x)) ≤ Λ ^ 2 * Λ'' := by
    have hcomp := sqrt_normSq0S_comp (I := I) hEq hx 4 (metricCovDeriv (I := I) g₁ g₂ 2 x)
    rw [hs4] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 4
      (metricCovDeriv (I := I) g₁ g₂ 2 x)) ≤ Λ'' from hJ2) (by positivity)
  have hM1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
      (metricCovDeriv (I := I) g₁ g₂ 1 x)) ≤ Λ * Real.sqrt Λ * Λ' := by
    have hcomp := sqrt_normSq0S_comp (I := I) hEq hx 3 (metricCovDeriv (I := I) g₁ g₂ 1 x)
    rw [hs3] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 3
        (metricCovDeriv (I := I) g₁ g₂ 1 x)) ≤ Λ' from hJ1)
      (mul_nonneg hLnn (Real.sqrt_nonneg _))
  have hNA : Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤
      3 / 2 * (Λ * Real.sqrt Λ * Λ') := by
    have h := lcDiff_covOne_le (I := I) g₂ g₁ hEq hx
    rw [hs3] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ1 (mul_nonneg hLnn (Real.sqrt_nonneg _)))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hM2nn : (0 : ℝ) ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
    (metricCovDeriv (I := I) g₁ g₂ 2 x)) := Real.sqrt_nonneg _
  have hM1nn : (0 : ℝ) ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
    (metricCovDeriv (I := I) g₁ g₂ 1 x)) := Real.sqrt_nonneg _
  have hNAnn : (0 : ℝ) ≤ Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
    (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) := Real.sqrt_nonneg _
  set M2 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
    (metricCovDeriv (I := I) g₁ g₂ 2 x)) with hM2def
  set M1 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
    (metricCovDeriv (I := I) g₁ g₂ 1 x)) with hM1def
  set NA := Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
    (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNAdef
  set B : TangentSpace I x :=
    covDerivConnectionDifference (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hBdef
  have hbr : 3 / 2 * M2 + M1 * NA ≤ 3 / 2 * Λ ^ 2 * (Λ'' + Λ * Λ' ^ 2) := by
    have hprod : M1 * NA ≤ (Λ * Real.sqrt Λ * Λ') * (3 / 2 * (Λ * Real.sqrt Λ * Λ')) :=
      mul_le_mul hM1 hNA hNAnn hcoefnn
    have heq1 : (Λ * Real.sqrt Λ * Λ') * (3 / 2 * (Λ * Real.sqrt Λ * Λ'))
        = 3 / 2 * Λ ^ 3 * Λ' ^ 2 := by
      linear_combination (3 / 2 * Λ ^ 2 * Λ' ^ 2) * hs2
    rw [heq1] at hprod
    nlinarith [hM2, hprod]
  have hbrnn : (0 : ℝ) ≤ 3 / 2 * M2 + M1 * NA :=
    add_nonneg (by linarith) (mul_nonneg hM1nn hNAnn)
  have hvec : ∀ z : TangentSpace I x,
      Real.sqrt (g₁.inner x z z) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := by
    intro z
    calc Real.sqrt (g₁.inner x z z) ≤ Real.sqrt (Λ * g₂.inner x z z) :=
          Real.sqrt_le_sqrt (hEq.2 x hx z).2
      _ = Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := Real.sqrt_mul hLnn _
  have hBcomp : Real.sqrt (g₂.inner x B B) ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x B B) := by
    have h := (hEq.2 x hx B).1
    have h' : g₂.inner x B B ≤ Λ * g₁.inner x B B := by
      have h2 := mul_le_mul_of_nonneg_left h hLnn
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hL0), one_mul] at h2
      exact h2
    calc Real.sqrt (g₂.inner x B B) ≤ Real.sqrt (Λ * g₁.inner x B B) := Real.sqrt_le_sqrt h'
      _ = Real.sqrt Λ * Real.sqrt (g₁.inner x B B) := Real.sqrt_mul hLnn _
  have hvwu : Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x w w) *
        Real.sqrt (g₁.inner x u u) ≤
      Real.sqrt Λ * Real.sqrt (g₂.inner x v v) * (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)) := by
    have p1 : Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x w w) ≤
        Real.sqrt Λ * Real.sqrt (g₂.inner x v v) * (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) :=
      mul_le_mul (hvec v) (hvec w) (Real.sqrt_nonneg _) (by positivity)
    exact mul_le_mul p1 (hvec u) (Real.sqrt_nonneg _) (by positivity)
  have hfin : Real.sqrt (g₁.inner x B B) ≤
      3 / 2 * Λ ^ 2 * (Λ'' + Λ * Λ' ^ 2) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x v v) * (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u))) := by
    refine le_trans hcore ?_
    have h1 := mul_le_mul_of_nonneg_left hvwu hbrnn
    have h2 := mul_le_mul_of_nonneg_right hbr
      (show (0 : ℝ) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x v v) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)) by positivity)
    linarith [h1, h2]
  calc Real.sqrt (g₂.inner x B B) ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x B B) := hBcomp
    _ ≤ Real.sqrt Λ * (3 / 2 * Λ ^ 2 * (Λ'' + Λ * Λ' ^ 2) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x v v) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)))) :=
        mul_le_mul_of_nonneg_left hfin (Real.sqrt_nonneg _)
    _ = 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) *
          Real.sqrt (g₂.inner x v v) * Real.sqrt (g₂.inner x w w) *
            Real.sqrt (g₂.inner x u u) := by
        linear_combination (3 / 2 * Λ ^ 2 * (Λ'' + Λ * Λ' ^ 2) * Real.sqrt (g₂.inner x v v) *
          Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u) *
          (Real.sqrt Λ ^ 2 + Λ)) * hs2

end Curvature
end Geometry
end DifferentialGeometry

end
