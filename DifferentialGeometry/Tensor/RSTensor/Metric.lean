/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.RSTensor.Contract
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option linter.style.longLine false

/-!
# Riemannian Metric on a Smooth Manifold

We define `RiemannianMetric` on a smooth manifold `M` as a `ContMDiffRiemannianMetric`
from Mathlib, specialized to the tangent bundle of `M`.

## Main Definitions

* `RiemannianMetric I n M` : a smooth Riemannian metric on `M`, i.e. a smoothly varying
  family of inner products on the tangent spaces of `M`.
* `RiemannianMetric.to02Tensor` : convert a Riemannian metric to a smooth (0,2)-tensor field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (n : WithTop ℕ∞)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-- A Riemannian metric on a smooth manifold `M` is a `ContMDiffRiemannianMetric` on the
tangent bundle, i.e. a smoothly varying family of inner products on the tangent spaces. -/
abbrev RiemannianMetric := Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)

private noncomputable def to02Tensor_eCLM :
    (E →L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ :=
  (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap

private noncomputable def to02Tensor_uCLM :
    (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap

section Aux
variable {I} {n} {M}

/-- The forward trivialization of the tangent bundle at `x₀`, viewed as a non-dependent
`(E →L[ℝ] E)`-valued function. -/
noncomputable def trivializationAt_clmAtFun (x₀ : M) : M → (E →L[ℝ] E) :=
  fun x => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x

set_option linter.unusedSectionVars false in
/-- The second component of the trivialization `e₀` is jointly smooth on the total space.
Since `(e₀ p).2 = clmAt(e₀, p.1) p.2`, this says `(b, v) ↦ clmAt(e₀, b) v` is `C^n`
as a map from the total space manifold to `E`. -/
lemma contMDiffOn_trivializationAt_snd {x₀ : M} :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) n
      (fun p : TotalSpace E (TangentSpace I) =>
        (trivializationAt E (TangentSpace I) x₀ p).2)
      (trivializationAt E (TangentSpace I) x₀).source :=
  contMDiff_snd.comp_contMDiffOn (trivializationAt E (TangentSpace I) x₀).contMDiffOn

/-- For each `v : E`, the pointwise evaluation `b ↦ clmAt(e₀, b) v` is `C^n` on `baseSet`.
This follows from `contMDiffOn_trivializationAt_snd` (joint smoothness of
`(b, v) ↦ clmAt(e₀, b) v` on the total space) together with the fact that `clmAt(e₀, b)`
is linear in `v` for each `b`. -/
lemma contMDiffOn_trivializationAt_clmAt_apply {x₀ : M} (v : E) :
    ContMDiffOn I 𝓘(ℝ, E) n
      (fun x => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x v)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  sorry

/-- The forward trivialization `continuousLinearMapAt` of the tangent bundle at `x₀`
varies C^n-smoothly within the base set.
Uses `contMDiffOn_trivializationAt_clmAt_apply` (pointwise smoothness for each `v`)
and `contDiff_clm_apply_iff` (a CLM-valued function from a finite-dimensional space is C^n
iff all pointwise evaluations are). -/
theorem contMDiffWithinAt_trivializationAt_clmAt (n : WithTop ℕ∞) {x₀ : M} :
    ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) n
      (trivializationAt_clmAtFun (I := I) (M := M) x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet x₀ := by
  sorry

end Aux

set_option maxHeartbeats 800000 in
/-- In local coordinates at `x₀`, the `(0,2)`-tensor obtained from a Riemannian metric is
`uCLM` applied to the local coordinates of the curried inner product section. -/
private lemma to02Tensor_trivialization_eq {x₀ x : M}
    (g : RiemannianMetric I n M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    let gI := Bundle.ContMDiffRiemannianMetric.inner g
    (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (fun y => Tensor0SBundle.Tensor0SSpace 2 I y) x₀
      ⟨x, ((to02Tensor_eCLM (E := E)).comp (gI x)).uncurryLeft⟩).2
      =
    (to02Tensor_uCLM (E := E)) ((to02Tensor_eCLM (E := E)).comp
      ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, gI x⟩).2)) := by
  dsimp
  let e₀ := trivializationAt E (TangentSpace I) x₀
  ext m
  change (((e₀.continuousMultilinearMap ℝ 2)
      ⟨x, ((to02Tensor_eCLM (E := E)).comp
        ((Bundle.ContMDiffRiemannianMetric.inner g) x)).uncurryLeft⟩).2) m = _
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.uncurryLeft_apply]
  have hx' : x ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp⟩
  rw [hom_trivializationAt_apply]
  change (to02Tensor_eCLM (E := E)) (((Bundle.ContMDiffRiemannianMetric.inner g) x)
      ((Trivialization.symmL ℝ e₀ x) (m 0)))
      (Fin.tail fun i => (Trivialization.symmL ℝ e₀ x) (m i)) =
    (to02Tensor_eCLM (E := E)) (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x
      ((Bundle.ContMDiffRiemannianMetric.inner g) x) (m 0))
      (Fin.tail m)
  rw [ContinuousLinearMap.inCoordinates_eq hx hx']
  simp [to02Tensor_eCLM, hom_trivializationAt, Trivialization.continuousLinearMap_apply]
  rfl

/-- Convert a Riemannian metric to a smooth (0,2)-tensor field. At each point `x`, the
inner product `g.inner x : TₓM →L[ℝ] TₓM →L[ℝ] ℝ` is uncurried into a continuous
bilinear form `TₓM × TₓM → ℝ`, i.e. a (0,2)-tensor. -/
def RiemannianMetric.to02Tensor {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    (g : RiemannianMetric I n M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (I := I) (M := M) (n := n) 2 := by
  unfold Tensor0SBundle.Tensor0SField
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  let eCLM := to02Tensor_eCLM (E := E)
  let uCLM := to02Tensor_uCLM (E := E)
  let gI := Bundle.ContMDiffRiemannianMetric.inner g
  exact ⟨fun x => (eCLM.comp (gI x)).uncurryLeft, by
    haveI := Tensor0SBundle.tensor0SBundle_smooth
      (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := n) 2
    intro x₀; rw [contMDiffAt_section]
    have hTriv := (contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        (s := gI) (x₀ := x₀)).mp (g.contMDiff.contMDiffAt (x := x₀))
    have hCurried :
        ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) n
          (fun x => eCLM.comp ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
            (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀
            ⟨x, gI x⟩).2)) x₀ := by
      exact (contMDiffAt_const (c := eCLM)).clm_comp hTriv
    refine (uCLM.contMDiffAt.comp x₀ hCurried).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
    exact to02Tensor_trivialization_eq (I := I) (n := n) (M := M) (g := g) (x := x)
      (x₀ := x₀) hx⟩

end
