import DifferentialGeometry.Topology.VectorField.RegularChartSplice
import DifferentialGeometry.Topology.VectorField.ChartIndexHomotopy
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I ∞ M]
  (c : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
    (EuclideanSpace ℝ (Fin (d + 1))) ∞)

theorem exists_regular_chart_splice_interiorIndexSum_eq
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)))
    (hVreg : ∀ x, ∀ hz : V x = 0,
      (linearizationAtZero ((hV x).mdifferentiableAt (by simp)) hz).det ≠ 0)
    (hWreg : ∀ x, ∀ hz : W x = 0,
      (linearizationAtZero ((hW x).mdifferentiableAt (by simp)) hz).det ≠ 0)
    (hVfinite : {x | V x = 0}.Finite)
    (hVisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVint : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (a : EuclideanSpace ℝ (Fin (d + 1))) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRt : closedBall a R ⊆ c.target) {S : Set M} (hS : IsCompact S)
    (hagree : ∀ x ∈ S, V =ᶠ[𝓝 x] W) :
    ∃ (G : ∀ x : M, TangentSpace I x)
      (hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)))
      (hGfinite : {x | G x = 0}.Finite)
      (hGisolated : ∀ x, G x = 0 → HasContinuousIsolatedZero I G x)
      (hGint : ∀ x, G x = 0 → I.IsInteriorPoint x),
      (∀ x ∈ c.symm '' closedBall a r, G x = W x) ∧
      (∀ x ∉ c.symm '' closedBall a R, G =ᶠ[𝓝 x] V) ∧
      (∀ x ∈ S, G =ᶠ[𝓝 x] W) ∧
      (∀ x, ∀ hz : G x = 0,
        (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).det ≠ 0) ∧
      interiorIndexSum I G hGfinite hGisolated hGint =
        interiorIndexSum I V hVfinite hVisolated hVint := by
  obtain ⟨s, hs, havoid⟩ := (Ioo_infinite hrR).exists_notMem_finite
    (hVfinite.image (fun x => dist (c x) a))
  have hst : closedBall a s ⊆ c.target := (closedBall_subset_closedBall hs.2.le).trans hRt
  have hzeroFree : ∀ y ∈ sphere a s, V (c.symm y) ≠ 0 := by
    intro y hy hz
    apply havoid
    refine ⟨c.symm y, hz, ?_⟩
    change dist (c (c.symm y)) a = s
    erw [c.right_inv (hst (sphere_subset_closedBall hy))]
    exact mem_sphere.mp hy
  obtain ⟨G, hG, hinner, houter, hprotected, hgerm, hGint, hGreg, hGiso, hGfinite⟩ :=
    exists_regular_chart_splice I c V W hV hW hVreg hWreg hVint a hr hs.1 hst hS hagree
  refine ⟨G, hG, hGfinite, hGiso, hGint, hinner, ?_,
    fun x hx => (hprotected x hx).trans (hagree x hx), hGreg, ?_⟩
  · intro x hx
    exact hgerm x (fun h => hx (image_mono (closedBall_subset_closedBall hs.2.le) h))
  · let e : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
        (EuclideanSpace ℝ (Fin (d + 1))) M 1 := {
      c.symm with
      contMDiffOn_toFun := c.symm.contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := c.symm.contMDiffOn_invFun.of_le (by simp) }
    apply (interiorIndexSum_eq_of_parametrization_boundary_eq I e hst
      V hV.continuous.continuousOn (hr.trans hs.1) hVfinite hVisolated hVint
      G hG.continuous.continuousOn hGfinite hGiso hGint hzeroFree ?_
      (fun x hx => (hgerm x hx).symm)).symm
    intro y hy
    apply (houter (c.symm y) ?_).symm
    rintro ⟨z, hz, hzy⟩
    have hzt := hst (ball_subset_closedBall hz)
    have hyt := hst (sphere_subset_closedBall hy)
    have hzy' : z = y := c.symm.injOn hzt hyt hzy
    subst z
    exact (not_lt_of_ge (mem_sphere.mp hy).ge) hz

end Poincare.VectorField
