import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartParallel
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence

set_option autoImplicit false

noncomputable section

open Bundle Filter
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.VectorField
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
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

/-- Pull a smooth target-parallel field back through an original-corner chart isometry.
The total tangent field provides the exact regularity needed by covariant naturality. -/
theorem partialIsometry_pullback_parallel_bundle
    (g : SmoothRiemannianMetric I₁ M₁) (h : SmoothRiemannianMetric I₂ M₂)
    (Φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞)
    (hmet : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I₁ x,
      h.inner (Φ x) (mfderiv I₁ I₂ Φ x v) (mfderiv I₁ I₂ Φ x w) =
        g.inner x v w)
    (γ : ℝ → M₁) (W : ∀ s, TangentSpace I₂ (Φ (γ s))) {t : ℝ}
    (hsource : γ t ∈ Φ.source)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I₁ γ t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I₂.tangent 2
      (fun s => (⟨Φ (γ s), W s⟩ : TangentBundle I₂ M₂)) t)
    (hparallel : covDerivAlong h (fun s => Φ (γ s)) W t = 0) :
    covDerivAlong g γ
      (fun s => mfderiv I₂ I₁ (Φ.symm : M₂ → M₁) (Φ (γ s)) (W s)) t = 0 := by
  let V : ∀ s, TangentSpace I₁ (γ s) := fun s =>
    mfderiv I₂ I₁ (Φ.symm : M₂ → M₁) (Φ (γ s)) (W s)
  let q : ℝ → TangentBundle I₂ M₂ := fun s => ⟨Φ (γ s), W s⟩
  let TM := tangentMap I₂ I₁ (Φ.symm : M₂ → M₁)
  have htarget : Φ (γ t) ∈ Φ.target := Φ.map_source' hsource
  have hsymm : ContMDiffAt I₂ I₁ ∞ (Φ.symm : M₂ → M₁) (Φ (γ t)) :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds htarget)
  have hTM : ContMDiffAt I₂.tangent I₁.tangent 2 TM (q t) :=
    DifferentialGeometry.VectorField.contMDiffAt_tangentMap hsymm (by norm_num)
  have hT : ContMDiffAt 𝓘(ℝ, ℝ) I₁.tangent 2 (fun s => TM (q s)) t :=
    hTM.comp t hW
  have hsourceNhd : ∀ᶠ s in 𝓝 t, γ s ∈ Φ.source :=
    hγ.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hsource)
  have hEq : (fun s => TM (q s)) =ᶠ[𝓝 t]
      (fun s => (⟨γ s, V s⟩ : TangentBundle I₁ M₁)) := by
    filter_upwards [hsourceNhd] with s hs
    have hbase : Φ.symm (Φ (γ s)) = γ s := Φ.left_inv' hs
    apply Bundle.TotalSpace.ext hbase
    exact heq_of_eq rfl
  have hVbundle : ContMDiffAt 𝓘(ℝ, ℝ) I₁.tangent 2
      (fun s => (⟨γ s, V s⟩ : TangentBundle I₁ M₁)) t :=
    hT.congr_of_eventuallyEq hEq.symm
  have hV : DifferentiableAt ℝ (chartRepAt (I := I₁) γ V t) t :=
    differentiableAt_chartRepAt_of_contMDiffAt_two hVbundle
  have hfieldEq : (fun s => mfderiv I₁ I₂ Φ (γ s) (V s)) =ᶠ[𝓝 t] W := by
    filter_upwards [hsourceNhd] with s hs
    have hinv := inverse_mfderiv_partialDiffeomorph Φ
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) hs
    change mfderiv I₁ I₂ Φ (γ s)
      (mfderiv I₂ I₁ (Φ.symm : M₂ → M₁) (Φ (γ s)) (W s)) = W s
    rw [← hinv]
    exact (isInvertible_mfderiv_partialDiffeomorph Φ
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) hs).self_apply_inverse (W s)
  have hparallel' := covDerivAlong_congr_of_eventuallyEq h
    (fun s => Φ (γ s)) hfieldEq
  exact partialIsometry_reflects_parallel g h Φ hmet γ V hsource hγ hV
    (hparallel'.trans hparallel)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
