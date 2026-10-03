import DifferentialGeometry.Bundle.SmoothSubbundle.Hom
import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
variable [VectorBundle ℝ F V] {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]

namespace ContMDiffVectorSubbundle

theorem exists_orthogonal
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (g : ContMDiffRiemannianMetric I n F V) :
    ∃ T : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n),
      T.rank = Module.finrank ℝ F - S.rank ∧
      ∀ x v, v ∈ T.fiber x ↔ ∀ w ∈ S.fiber x, g.inner x w v = 0 := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  let _ : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let A := fun x => ((g.inner x).comp (S.fiber x).subtypeL).flip
  have hinc := ContMDiff.clm_bundle_of_map
    (φ := fun x => (S.fiber x).subtypeL) S.contMDiff_subtypeVal
  have hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] (Fin S.rank → ℝ) →L[ℝ] ℝ)) n
      (fun x => TotalSpace.mk' (F →L[ℝ] (Fin S.rank → ℝ) →L[ℝ] ℝ) x (A x)) :=
    (g.contMDiff.clm_bundle_comp hinc).clm_bundle_flip
  have hmem (x : M) (v : V x) : v ∈ (A x).ker ↔
      ∀ w ∈ S.fiber x, g.inner x w v = 0 := by
    change (A x) v = 0 ↔ _
    constructor
    · intro hv w hw
      exact congrArg (fun L : S.fiber x →L[ℝ] ℝ => L ⟨w, hw⟩) hv
    · intro hv
      ext w
      exact hv w w.property
  have hker (x : M) : (A x).ker = (S.fiber x)ᗮ := by
    ext v
    rw [hmem, Submodule.mem_orthogonal]
    rfl
  have hfin (x : M) : Module.finrank ℝ (V x) = Module.finrank ℝ F :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt F V x)).toLinearEquiv.finrank_eq
  let _ (x : M) : FiniteDimensional ℝ (V x) :=
    FiniteDimensional.of_injective
      ((trivializationAt F V x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt F V x)).toLinearMap
      ((trivializationAt F V x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt F V x)).injective
  have hrank (x : M) : Module.finrank ℝ (A x).ker = Module.finrank ℝ F - S.rank := by
    rw [hker]
    have heq := (S.fiber x).finrank_add_finrank_orthogonal
    rw [S.finrank_fiber, hfin] at heq
    omega
  obtain ⟨T, hT, hfiber⟩ := exists_smooth_kernel A hA _ hrank
  exact ⟨T, hT, fun x v => by rw [hfiber x, hmem]⟩

end ContMDiffVectorSubbundle
