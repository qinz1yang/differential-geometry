import DifferentialGeometry.Topology.Manifold.LinearModelChange
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportTarget
import DifferentialGeometry.Topology.Manifold.ModelTransportDiffeomorph

/-!
The existing linear model change preserves smooth maps and embeddings in both directions.
Its actual chart derivative is conjugated by the same continuous linear equivalence.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Manifold

variable {E F E₀ H H' H₀ M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H₀]
  [TopologicalSpace M] [ChartedSpace H₀ M] [TopologicalSpace N] [ChartedSpace H N]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
  (e : H ≃ₜ H') (L : E ≃L[ℝ] F) (hc : ∀ y, J (e y) = L (I y))
  (I₀ : ModelWithCorners ℝ E₀ H₀)

include hc in
theorem isSmoothEmbedding_chartedSpaceTransHomeomorph_target_iff {n : ℕ∞ω} {f : M → N} :
    let _chartedModelChange := chartedSpaceTransHomeomorph (M := N) e
    IsSmoothEmbedding I₀ J n f ↔ IsSmoothEmbedding I₀ I n f := by
  let _chartedModelChange := chartedSpaceTransHomeomorph (M := N) e
  constructor
  · intro hf
    refine ⟨?_, hf.isEmbedding⟩
    apply IsImmersionOfComplement.isImmersion (F := hf.isImmersion.complement)
    intro x
    let h := hf.isImmersion.isImmersionOfComplement_complement x
    let c := h.codChart.trans e.symm.toOpenPartialHomeomorph
    have hs : c.source = h.codChart.source := by simp [c]
    have hcanc : c.trans e.toOpenPartialHomeomorph = h.codChart := by
      rw [show c = h.codChart.trans e.symm.toOpenPartialHomeomorph from rfl,
        OpenPartialHomeomorph.trans_assoc, ← Homeomorph.trans_toOpenPartialHomeomorph,
        Homeomorph.symm_trans_self]
      exact OpenPartialHomeomorph.trans_refl _
    have hcm : c ∈ IsManifold.maximalAtlas I n N := by
      apply (mem_maximalAtlas_chartedSpaceTransHomeomorph I J e L hc).mp
      rw [hcanc]
      exact h.codChart_mem_maximalAtlas
    apply IsImmersionAtOfComplement.mk_of_charts (h.equiv.trans L.symm) h.domChart c
      h.mem_domChart_source (hs.symm ▸ h.mem_codChart_source)
      h.domChart_mem_maximalAtlas hcm
    · intro y hy
      rw [Set.mem_preimage, hs]
      exact h.source_subset_preimage_source hy
    · intro y hy
      change I (e.symm (h.codChart (f ((h.domChart.extend I₀).symm y)))) =
        L.symm (h.equiv (y, 0))
      apply L.injective
      rw [L.apply_symm_apply, ← hc, e.apply_symm_apply]
      exact h.writtenInCharts hy
  · exact isSmoothEmbedding_chartedSpaceTransHomeomorph_target I J e L hc I₀

end DifferentialGeometry.Manifold

namespace DifferentialGeometry.Manifold.LinearModelChange
variable {E F E₀ H₀ M X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [TopologicalSpace H₀] [TopologicalSpace M] [ChartedSpace H₀ M]
  [TopologicalSpace X] [ChartedSpace E X]
  (L : E ≃L[ℝ] F) (I₀ : ModelWithCorners ℝ E₀ H₀)

variable {I₀} in
theorem contMDiff_toLinearModelChange_iff {n : ℕ∞ω} {f : M → X} :
    ContMDiff I₀ 𝓘(ℝ, F) n (fun x => ofBase L (f x)) ↔ ContMDiff I₀ 𝓘(ℝ, E) n f :=
  contMDiff_chartedSpaceTransHomeomorph_iff (M := X) (N := M) 𝓘(ℝ, E) 𝓘(ℝ, F) L.toHomeomorph L
    (fun y => Eq.refl (L y)) I₀

variable {I₀} in
theorem contMDiff_fromLinearModelChange_iff {n : ℕ∞ω} {f : X → M} :
    ContMDiff 𝓘(ℝ, F) I₀ n (fun x => f (toBase L x)) ↔ ContMDiff 𝓘(ℝ, E) I₀ n f :=
  contMDiff_chartedSpaceTransHomeomorph_source_iff (N := X) (M := M)
    𝓘(ℝ, E) 𝓘(ℝ, F) L.toHomeomorph L
    (fun y => Eq.refl (L y)) I₀

variable {I₀} in
theorem isSmoothEmbedding_toLinearModelChange_iff {n : ℕ∞ω} {f : M → X} :
    IsSmoothEmbedding I₀ 𝓘(ℝ, F) n (fun x => ofBase L (f x)) ↔
      IsSmoothEmbedding I₀ 𝓘(ℝ, E) n f :=
  isSmoothEmbedding_chartedSpaceTransHomeomorph_target_iff (N := X) (M := M)
    𝓘(ℝ, E) 𝓘(ℝ, F) L.toHomeomorph L
    (fun y => Eq.refl (L y)) I₀

variable {I₀} in
theorem isSmoothEmbedding_fromLinearModelChange_iff {n : ℕ∞ω} {f : X → M} :
    IsSmoothEmbedding 𝓘(ℝ, F) I₀ n (fun x => f (toBase L x)) ↔
      IsSmoothEmbedding 𝓘(ℝ, E) I₀ n f :=
  isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff (N := X) (M := M)
    𝓘(ℝ, E) 𝓘(ℝ, F) L.toHomeomorph L
    (fun y => Eq.refl (L y)) I₀

theorem mfderiv_toLinearModelChange {f : M → X} (x : M) :
    mfderiv I₀ 𝓘(ℝ, F) (fun y => ofBase L (f y)) x =
      L.toContinuousLinearMap.comp (mfderiv I₀ 𝓘(ℝ, E) f x) :=
  mfderiv_chartedSpaceTransHomeomorph (M := X) (N := M)
    𝓘(ℝ, E) 𝓘(ℝ, F) L.toHomeomorph L (fun y => Eq.refl (L y)) I₀

omit [TopologicalSpace M] [ChartedSpace H₀ M] in
private theorem mfderiv_toBase_eq (x : X) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (toBase L (X := X)) (ofBase L x) =
      L.symm.toContinuousLinearMap := by
  let D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) X (LinearModelChange X L) ∞ :=
    diffeomorphTransHomeomorph (M := X) 𝓘(ℝ, E) 𝓘(ℝ, F)
    L.toHomeomorph L (fun y => Eq.refl (L y)) ∞
  have h := mfderiv_comp x (D.symm.mdifferentiable (by simp) (D x))
    (D.mdifferentiable (by simp) x)
  have hD : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) D x = L.toContinuousLinearMap :=
    diffeomorphTransHomeomorph_mfderiv (M := X) 𝓘(ℝ, E) 𝓘(ℝ, F)
    L.toHomeomorph L (fun y => Eq.refl (L y)) ∞ x
  have hid : (D.symm : LinearModelChange X L → X) ∘ D = id :=
    funext D.symm_apply_apply
  rw [hid, mfderiv_id, hD] at h
  ext v
  change F at v
  have hv := congrArg (fun A : E →L[ℝ] E => A (L.symm v)) h
  change L.symm v =
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (toBase L) (ofBase L x)) (L (L.symm v)) at hv
  rw [L.apply_symm_apply] at hv
  exact hv.symm

theorem mfderiv_fromLinearModelChange {f : X → M} (x : X)
    (hf : MDifferentiableAt 𝓘(ℝ, E) I₀ f x) :
    mfderiv 𝓘(ℝ, F) I₀ (fun y => f (toBase L y)) (ofBase L x) =
      (mfderiv 𝓘(ℝ, E) I₀ f x).comp L.symm.toContinuousLinearMap := by
  let D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) X (LinearModelChange X L) ∞ :=
    diffeomorphTransHomeomorph (M := X) 𝓘(ℝ, E) 𝓘(ℝ, F)
    L.toHomeomorph L (fun y => Eq.refl (L y)) ∞
  have h := mfderiv_comp (ofBase L x) hf (D.symm.mdifferentiable (by simp) (ofBase L x))
  change mfderiv 𝓘(ℝ, F) I₀ (fun y => f (toBase L y)) (ofBase L x) =
    (mfderiv 𝓘(ℝ, E) I₀ f x).comp
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (toBase L) (ofBase L x)) at h
  rw [mfderiv_toBase_eq] at h
  exact h

end DifferentialGeometry.Manifold.LinearModelChange
