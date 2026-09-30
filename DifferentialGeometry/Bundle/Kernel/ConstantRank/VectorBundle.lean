import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import DifferentialGeometry.Bundle.SmoothSubbundle.VectorBundle
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
noncomputable section

open scoped ContDiff Manifold

namespace Bundle

variable {X : Type*} {d : ℕ}

abbrev MatrixKernelFiber (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) : Type _ :=
  LinearMap.ker (A x).mulVecLin

def matrixKernelInclusion (A : X → Matrix (Fin d) (Fin d) ℝ) (r : ℕ) :
    TotalSpace (Fin (d - r) → ℝ) (MatrixKernelFiber A) → X × (Fin d → ℝ) :=
  fun z => (z.proj, z.snd.1)

theorem matrixKernelInclusion_injective
    (A : X → Matrix (Fin d) (Fin d) ℝ) (r : ℕ) :
    Function.Injective (matrixKernelInclusion A r) := by
  rintro ⟨p, v⟩ ⟨q, w⟩ h
  have hp : p = q := congrArg Prod.fst h
  subst q
  have hv : v = w := Subtype.ext (congrArg Prod.snd h)
  subst w
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  (A : X → Matrix (Fin d) (Fin d) ℝ) (r : ℕ)

private theorem contMDiff_matrix_mulVecLin
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j)) :
    ContMDiff I 𝓘(ℝ, (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) ∞
      (fun x => (A x).mulVecLin.toContinuousLinearMap) := by
  have hcols : ContMDiff I 𝓘(ℝ, Fin d → Fin d → ℝ) ∞
      (fun x j i => A x i j) :=
    contMDiff_pi_space.mpr fun j => contMDiff_pi_space.mpr fun i => hA i j
  have h := (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Fin d → ℝ)
    (Fin d)).symm.toContinuousLinearMap.contMDiff.comp hcols
  refine h.congr ?_
  intro x
  apply ContinuousLinearMap.ext
  intro v
  change (A x).mulVecLin v = (LinearEquiv.piRing ℝ (Fin d → ℝ) (Fin d) ℝ).symm
    (fun j i => A x i j) v
  rw [LinearEquiv.piRing_symm_apply]
  ext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem contMDiff_matrix_hom_section
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j)) :
    ContMDiff I (I.prod 𝓘(ℝ, (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) ∞
      (fun x => TotalSpace.mk' ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
        (E := fun x => Trivial X (Fin d → ℝ) x →L[ℝ] Trivial X (Fin d → ℝ) x)
        x (A x).mulVecLin.toContinuousLinearMap) := by
  intro x
  apply (contMDiffAt_hom_bundle (F₁ := Fin d → ℝ) (F₂ := Fin d → ℝ) _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  simpa only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using
      contMDiff_matrix_mulVecLin A hA x

def matrixKernelSubbundle
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    ContMDiffVectorSubbundle (I := I) (F := Fin d → ℝ)
      (V := Trivial X (Fin d → ℝ)) (n := ∞) :=
  ContMDiffVectorSubbundle.kernel (F₂ := Fin d → ℝ)
    (V₂ := Trivial X (Fin d → ℝ))
    (fun x => (A x).mulVecLin.toContinuousLinearMap)
    (contMDiff_matrix_hom_section A hA) (d - r) (fun x => by
      have h := (A x).mulVecLin.finrank_range_add_finrank_ker
      change (A x).rank + Module.finrank ℝ (LinearMap.ker (A x).mulVecLin) =
        Module.finrank ℝ (Fin d → ℝ) at h
      rw [hr x, Module.finrank_pi, Fintype.card_fin] at h
      change Module.finrank ℝ (LinearMap.ker (A x).mulVecLin) = d - r
      omega)

@[simp]
theorem matrixKernelSubbundle_fiber
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) (x : X) :
    (matrixKernelSubbundle A r hA hr).fiber x = LinearMap.ker (A x).mulVecLin := rfl

@[simp]
theorem matrixKernelSubbundle_rank
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    (matrixKernelSubbundle A r hA hr).rank = d - r := rfl

def constantRankKernelPrebundle
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    VectorPrebundle ℝ (Fin (d - r) → ℝ) (MatrixKernelFiber A) :=
  (matrixKernelSubbundle A r hA hr).vectorPrebundle

theorem constantRankKernel_isContMDiff
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    let a := constantRankKernelPrebundle A r hA hr
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ContMDiffVectorBundle ∞ (Fin (d - r) → ℝ) (MatrixKernelFiber A) I :=
  (matrixKernelSubbundle A r hA hr).contMDiffVectorBundle

theorem matrixKernelInclusion_contMDiff
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    let a := constantRankKernelPrebundle A r hA hr
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ContMDiff (I.prod 𝓘(ℝ, Fin (d - r) → ℝ)) (I.prod 𝓘(ℝ, Fin d → ℝ)) ∞
      (matrixKernelInclusion A r) := by
  let S := matrixKernelSubbundle A r hA hr
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let e := Trivial.trivialization X (Fin d → ℝ)
  let _ : MemTrivializationAtlas e := ⟨by
    change e ∈ {Trivial.trivialization X (Fin d → ℝ)}
    exact Set.mem_singleton _⟩
  have he : ContMDiff (I.prod 𝓘(ℝ, Fin d → ℝ)) (I.prod 𝓘(ℝ, Fin d → ℝ)) ∞ e := by
    apply contMDiffOn_univ.mp
    exact e.contMDiffOn (IB := I) (n := ∞)
  exact he.comp S.contMDiff_subtypeVal

theorem matrixKernelInclusion_isEmbedding
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    let a := constantRankKernelPrebundle A r hA hr
    let _ := a.totalSpaceTopology
    Topology.IsEmbedding (matrixKernelInclusion A r) := by
  let S := matrixKernelSubbundle A r hA hr
  let _ := S.totalSpaceTopology
  exact (Trivial.homeomorphProd X (Fin d → ℝ)).isEmbedding.comp S.isEmbedding_subtypeVal

end Bundle

end
