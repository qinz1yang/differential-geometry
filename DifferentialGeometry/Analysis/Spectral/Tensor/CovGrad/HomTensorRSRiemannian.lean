import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle
import DifferentialGeometry.Bundle.HomNorm
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Order.Compact
open DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature


noncomputable section


open Bundle Manifold Set IsManifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap Filter
open scoped Manifold Topology ContDiff BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

private local instance tensorRSRiemannianNormedAddCommGroup_local
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

section FibrewiseBound

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
lemma homTensorRS_riemannianFiberNormSq_clm_apply_le
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (v : TensorRSSpace r a I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
    riemannianFiberNormSq (I := I) (M := M) g r c x (A v) ≤
      ‖A‖ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  let instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
  let instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
  rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r c x (A v),
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r a x v]
  have hle : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  calc ‖A v‖ ^ 2 ≤ (‖A‖ * ‖v‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := by ring

end FibrewiseBound

section OpNormContinuity

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem continuous_homTensorRS_opNorm
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
    Continuous (fun x : M => ‖Ψ x‖) := by
  let instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
  let instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
  exact Continuous.hom_bundle_opNorm
    (F₁ := TensorRSModel r a ℝ E) (F₂ := TensorRSModel r c ℝ E)
    (E₁ := fun z : M => TensorRSSpace r a I z) (E₂ := fun z : M => TensorRSSpace r c I z)
    hΨ.continuous

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ C := by
  let instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
  let instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
  have hcont : Continuous (fun x : M => ‖Ψ x‖) :=
    continuous_homTensorRS_opNorm (I := I) (M := M) g r a c Ψ hΨ
  have hcont_sq : Continuous (fun x : M => ‖Ψ x‖ ^ 2) := hcont.pow 2
  obtain ⟨C₀, hC₀⟩ := (isCompact_range hcont_sq).bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  exact le_trans (hC₀ (Set.mem_range_self x)) (le_max_left _ _)

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_continuous_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
    ∃ N : M → ℝ, Continuous N ∧ (∀ x : M, 0 ≤ N x) ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ N x := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  exact ⟨fun _ => C, continuous_const, fun _ => hC_nonneg, hC_bound⟩

end OpNormContinuity

section Payoff

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)


omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  let instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r a
  let instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r c
  obtain ⟨N, hN_cont, hN_nonneg, hN_bound⟩ :=
    exists_continuous_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨N, hN_cont, hN_nonneg, fun x v => ?_⟩
  refine le_trans (homTensorRS_riemannianFiberNormSq_clm_apply_le
    (I := I) (M := M) g r a c x (Ψ x) v) ?_
  exact mul_le_mul_of_nonneg_right (hN_bound x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)


omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  obtain ⟨Cop, hCop_cont, hCop_nn, hCop_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
      (I := I) (M := M) g r a c Ψ hΨ
  have hCpt := (isCompact_univ (X := M)).image hCop_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v => ?_⟩
  have hCop_le : Cop x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  refine le_trans (hCop_bound x v) ?_
  exact mul_le_mul_of_nonneg_right hCop_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

end Payoff

end DifferentialGeometry.Analysis.Spectral
