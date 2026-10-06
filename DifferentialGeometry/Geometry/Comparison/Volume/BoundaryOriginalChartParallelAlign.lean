import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartParallelField
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

set_option autoImplicit false

noncomputable section

open Bundle Filter
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.VectorField
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [FiniteDimensional ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ ∞ M₁] [IsManifold I₁ 1 M₁] [T2Space M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [I₂.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] [IsManifold I₂ 1 M₂] [T2Space M₂]


private theorem x124_chartTangent_cast
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x y : M}
    (hxy : x = y) (w : TangentSpace I y) :
    (hxy.symm ▸ w : TangentSpace I x) = w := by
  cases hxy
  rfl

omit [IsManifold I₁ 1 M₁] in
/-- Pull back a smooth parallel field along any curve in the target patch. -/
theorem partialIsometry_pullback_parallel_on_target
    (g : SmoothRiemannianMetric I₁ M₁) (h : SmoothRiemannianMetric I₂ M₂)
    (Φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞)
    (hmet : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I₁ x,
      h.inner (Φ x) (mfderiv I₁ I₂ Φ x v) (mfderiv I₁ I₂ Φ x w) =
        g.inner x v w)
    (δ : ℝ → M₂) (W : ∀ s, TangentSpace I₂ (δ s)) {t : ℝ}
    (ht : δ t ∈ Φ.target)
    (hδ : MDifferentiableAt 𝓘(ℝ, ℝ) I₂ δ t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I₂.tangent 2
      (fun s => (⟨δ s, W s⟩ : TangentBundle I₂ M₂)) t)
    (hparallel : covDerivAlong h δ W t = 0) :
    covDerivAlong g (fun s => Φ.symm (δ s))
      (fun s => mfderiv I₂ I₁ (Φ.symm : M₂ → M₁) (δ s) (W s)) t = 0 := by
  let γ : ℝ → M₁ := fun s => Φ.symm (δ s)
  let V : ∀ s, TangentSpace I₁ (γ s) := fun s =>
    mfderiv I₂ I₁ (Φ.symm : M₂ → M₁) (δ s) (W s)
  let q : ℝ → TangentBundle I₂ M₂ := fun s => ⟨δ s, W s⟩
  let T := tangentMap I₂ I₁ (Φ.symm : M₂ → M₁)
  have hsymm : ContMDiffAt I₂ I₁ ∞ (Φ.symm : M₂ → M₁) (δ t) :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds ht)
  have hT : ContMDiffAt I₂.tangent I₁.tangent 2 T (q t) :=
    DifferentialGeometry.VectorField.contMDiffAt_tangentMap hsymm (by norm_num)
  have hVbundle : ContMDiffAt 𝓘(ℝ, ℝ) I₁.tangent 2
      (fun s => (⟨γ s, V s⟩ : TangentBundle I₁ M₁)) t := by
    have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I₁.tangent 2 (fun s => T (q s)) t :=
      hT.comp t hW
    simpa only [T, tangentMap, q, γ, V] using hcomp
  have hsource : γ t ∈ Φ.source := Φ.map_target' ht
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I₁ γ t :=
    (mdifferentiableAt_tangentField_iff.mp
      (hVbundle.mdifferentiableAt (by norm_num))).1
  have hVdiff : DifferentiableAt ℝ (chartRepAt (I := I₁) γ V t) t :=
    differentiableAt_chartRepAt_of_contMDiffAt_two hVbundle
  have hcurve : (fun s => Φ (γ s)) =ᶠ[𝓝 t] δ := by
    filter_upwards [hδ.continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds ht)] with s hs
    exact Φ.right_inv' hs
  classical
  let W' : ∀ s, TangentSpace I₂ (Φ (γ s)) := fun s =>
    if heq : Φ (γ s) = δ s then heq.symm ▸ W s else 0
  have hWvec : ∀ᶠ s in 𝓝 t, (W' s : E₂) = (W s : E₂) := by
    filter_upwards [hcurve] with s hs
    have hval := x124_chartTangent_cast (I := I₂) (M := M₂) hs (W s)
    simpa only [W', dite_eq_left hs] using
      congrArg (fun z : TangentSpace I₂ (Φ (γ s)) => (z : E₂)) hval
  have hfield : ∀ᶠ s in 𝓝 t,
      mfderiv I₁ I₂ Φ (γ s) (V s) = W' s := by
    filter_upwards [hδ.continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds ht), hWvec] with s hs hws
    have hsource' : γ s ∈ Φ.source := Φ.map_target' hs
    have hpoint : Φ (γ s) = δ s := by
      change Φ (Φ.symm (δ s)) = δ s
      exact Φ.right_inv' hs
    have hinv := inverse_mfderiv_partialDiffeomorph Φ
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) hsource'
    rw [hpoint] at hinv
    have hfieldVec : (mfderiv I₁ I₂ Φ (γ s) (V s) : E₂) = (W s : E₂) := by
      change mfderiv I₁ I₂ Φ (γ s)
        (mfderiv I₂ I₁ (Φ.symm : M₂ → M₁) (δ s) (W s)) = W s
      rw [← hinv]
      exact (isInvertible_mfderiv_partialDiffeomorph Φ
        (by simp : (∞ : WithTop ℕ∞) ≠ 0) hsource').self_apply_inverse (W s)
    have hcast := x124_chartTangent_cast (I := I₂) (M := M₂) hpoint (W s)
    have hcastVec : ((hpoint.symm ▸ W s : TangentSpace I₂ (Φ (γ s))) : E₂) =
        (W s : E₂) := congrArg (fun z : TangentSpace I₂ (Φ (γ s)) => (z : E₂)) hcast
    have hfield0 : mfderiv I₁ I₂ Φ (γ s) (V s) = W' s := by
      simp only [W', dite_eq_left hpoint]
      change (mfderiv I₁ I₂ Φ (γ s) (V s) : E₂) =
        ((hpoint.symm ▸ W s : TangentSpace I₂ (Φ (γ s))) : E₂)
      exact hfieldVec.trans hcastVec.symm
    exact hfield0
  have hparallel' := covDerivAlong_congr_curve (I := I₂) h
    (γ := fun s => Φ (γ s)) (γ' := δ) W' W
    hcurve hWvec
  have hparallel'' := covDerivAlong_congr_of_eventuallyEq (I := I₂) h
    (fun s => Φ (γ s)) hfield
  exact partialIsometry_reflects_parallel g h Φ hmet γ V hsource hγ hVdiff
    (hparallel''.trans (hparallel'.trans hparallel))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
