import DifferentialGeometry.Geometry.Connection.OrthonormalFrame
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]

private theorem contMDiffAt_coframe_apply
    (q : ∀ x, V x ≃ₗᵢ[ℝ] F) {x : M}
    (hq : ∀ w : F, ContMDiffAt I (I.prod 𝓘(ℝ, F)) 1
      (fun y => (⟨y, (q y).symm w⟩ : TotalSpace F V)) x)
    {Z : ∀ y, V y}
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 1
      (fun y => (⟨y, Z y⟩ : TotalSpace F V)) x) :
    ContMDiffAt I 𝓘(ℝ, F) 1 (fun y => q y (Z y)) x := by
  let e := trivializationAt F V x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  let A : M → F →L[ℝ] F := fun y =>
    (e.continuousLinearMapAt ℝ y).comp (q y).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hA : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) 1 A x := by
    apply contMDiffAt_clm_of_pointwise
    intro w
    have h := (e.contMDiffAt_iff (IB := I) (e.mem_source.mpr he)).mp (hq w)
    apply h.2.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy ((q y).symm w)
  have hinv : (A x).IsInvertible := by
    refine ⟨(q x).symm.toContinuousLinearEquiv.trans (e.continuousLinearEquivAt ℝ x he), ?_⟩
    apply ContinuousLinearMap.ext
    intro w
    change e.continuousLinearEquivAt ℝ x he ((q x).symm w) =
      e.continuousLinearMapAt ℝ x ((q x).symm w)
    rw [e.coe_continuousLinearEquivAt_eq]
  have hAi := hinv.contDiffAt_map_inverse.comp_contMDiffAt hA
  have hz : ContMDiffAt I 𝓘(ℝ, F) 1
      (fun y => e.continuousLinearMapAt ℝ y (Z y)) x := by
    apply ((e.contMDiffAt_iff (IB := I) (e.mem_source.mpr he)).mp hZ).2.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy (Z y)
  have hqZ : ContMDiffAt I 𝓘(ℝ, F) 1 (fun y => q y (Z y)) x := by
    have hh := hAi.clm_apply hz
    apply hh.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    have hAe : A y = ((q y).symm.toContinuousLinearEquiv.trans
        (e.continuousLinearEquivAt ℝ y hy)).toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro w
      change e.continuousLinearMapAt ℝ y ((q y).symm w) =
        e.continuousLinearEquivAt ℝ y hy ((q y).symm w)
      rw [e.coe_continuousLinearEquivAt_eq]
    dsimp only [Function.comp_def]
    rw [hAe, ContinuousLinearMap.inverse_equiv]
    change q y (Z y) = q y ((e.continuousLinearEquivAt ℝ y hy).symm
      (e.continuousLinearMapAt ℝ y (Z y)))
    rw [e.symm_continuousLinearEquivAt_eq, e.symmL_continuousLinearMapAt hy]
  exact hqZ

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [ContMDiffVectorBundle ∞ F V I]

theorem coframe_homBundleCovariantDerivative
    (cov : CovariantDerivative I F V)
    (q : ∀ x, V x ≃ₗᵢ[ℝ] F) {x : M}
    (hq : ∀ w : F, ContMDiffAt I (I.prod 𝓘(ℝ, F)) 1
      (fun y => (⟨y, (q y).symm w⟩ : TotalSpace F V)) x)
    {A : ∀ y, V y →L[ℝ] V y}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F)) 1
      (fun y => TotalSpace.mk' (F →L[ℝ] F) y (A y)) x) (X : TangentSpace I x) :
    (q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
        cov cov A x X).comp (q x).symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      mvfderiv I (fun y => (q y).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((A y).comp (q y).symm.toContinuousLinearEquiv.toContinuousLinearMap)) x X -
      (cov.coframeConnectionForm q x X).comp
        ((q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((A x).comp (q x).symm.toContinuousLinearEquiv.toContinuousLinearMap)) +
      ((q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((A x).comp (q x).symm.toContinuousLinearEquiv.toContinuousLinearMap)).comp
          (cov.coframeConnectionForm q x X) := by
  let B : M → F →L[ℝ] F := fun y => (q y).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((A y).comp (q y).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hB : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F) B x := by
    apply ContMDiffAt.mdifferentiableAt (n := 1) _ (by simp)
    apply contMDiffAt_clm_of_pointwise
    intro w
    exact contMDiffAt_coframe_apply q hq (hA.clm_bundle_apply (hq w))
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hh := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M F V F V cov cov A (hA.mdifferentiableAt (by simp)) Y.mdifferentiableAt
      ((hq w).mdifferentiableAt (by simp))
  rw [hY] at hh
  have hv := cov.coframe_covariantDerivative q hq
    ((hA.clm_bundle_apply (hq w)).mdifferentiableAt (by simp)) X
  have hw := cov.coframeConnectionForm_apply q hq X w
  rw [cov.connector_mfderiv_section ((hq w).mdifferentiableAt (by simp))] at hw
  have hd := congrArg (fun L => L X)
    (hB.mvfderiv_clm_apply (mdifferentiableAt_const (c := w)))
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hd
  change q x ((DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
    cov cov A x X) ((q x).symm w)) =
      mvfderiv I B x X w - cov.coframeConnectionForm q x X (B x w) +
        B x (cov.coframeConnectionForm q x X w)
  rw [hh, map_sub, hv]
  change mvfderiv I (fun y => B y w) x X - cov.coframeConnectionForm q x X (B x w) -
    q x (A x (cov (fun y => (q y).symm w) x X)) = _
  rw [hd, hw]
  change _ = _ + q x (A x ((q x).symm (-q x (cov (fun y => (q y).symm w) x X))))
  rw [map_neg, (q x).symm_apply_apply, map_neg, map_neg, sub_eq_add_neg]

end CovariantDerivative
