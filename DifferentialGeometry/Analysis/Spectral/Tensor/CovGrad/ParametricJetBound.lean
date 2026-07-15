import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth

/-!
# Compact-slab bounds for parametric tensor jets

This file turns joint spacetime smoothness of a fixed-background tensor family
into one fibre-norm envelope for every spatial covariant-derivative order on a
fixed compact time slab.  The slab is chosen before the derivative order, so a
single slab can support an entire family of order-dependent constants.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open Tensor0SBundle TensorRSNabla

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- The intrinsic squared fibre norm of a jointly smooth fixed-background
tensor family is jointly continuous on every smaller time set. -/
theorem joint_rfns_cont
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r s p.2
        ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
  have hsub : (K ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ x, hKS ht⟩
  have hswap : Continuous (fun p : ℝ × M => (p.2, p.1)) := by
    fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.2
        ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswap.continuousOn hsub).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hinner : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ)
        (E := fun x : M =>
          TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2))
      (K ×ˢ (Set.univ : Set M)) :=
    ((tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g₀ r s).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))
      (K ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂
      (F₁ := TensorRSModel r s ℝ E) (F₂ := TensorRSModel r s ℝ E)
      (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hinner hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))).mp
      (happ p hp)).2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g₀ r s x ((Φ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]

/-- Joint smoothness is preserved by every fixed number of spatial covariant
derivatives with respect to the fixed background metric. -/
theorem covGrad_iter_joint
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r (s + i) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + i) I z) p.1
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
      exact covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (s + j)
        (fun t => iteratedCovGrad (I := I) g₀ r s j (Φ t)) S ih

/-- Every fixed spatial covariant jet of a jointly smooth tensor family has a
jointly continuous squared fibre norm on a smaller time set. -/
theorem joint_jet_rfns
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) :=
  joint_rfns_cont (I := I) (M := M) g₀ r (s + i)
    (fun t => iteratedCovGrad (I := I) g₀ r s i (Φ t)) hKS
    (covGrad_iter_joint (I := I) (M := M) g₀ r s i Φ S hjoint)

/-- On one compact time slab, every spatial covariant-derivative order of a
jointly smooth fixed-background tensor family has an order-dependent uniform
intrinsic squared fibre-norm bound. -/
theorem joint_jet_bdd
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ i t, t ∈ K → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) ≤ B i := by
  classical
  have hprod : IsCompact (K ×ˢ (Set.univ : Set M)) :=
    hK.prod isCompact_univ
  have hex : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ∈ K → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) ≤ C := by
    intro i
    let F : ℝ × M → ℝ := fun p =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2)
    have hcont : ContinuousOn F (K ×ˢ (Set.univ : Set M)) :=
      joint_jet_rfns (I := I) (M := M) g₀ r s i Φ hKS hjoint
    obtain ⟨C₀, hC₀⟩ := (hprod.image_of_continuousOn hcont).bddAbove
    refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
    intro t ht x
    refine le_trans (hC₀ ?_) (le_max_left _ _)
    exact ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩
  choose B hB_nonneg hB using hex
  exact ⟨B, hB_nonneg, hB⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
