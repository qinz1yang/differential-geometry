import DifferentialGeometry.Geometry.Connection.AlongCurve
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle I 1 F V] in
private theorem differentiableWithinAt_coord_along
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    {J : Set ℝ} {t : ℝ} (he : γ t ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t) :
    DifferentiableWithinAt ℝ (fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)) J t := by
  have h := (e.mdifferentiableWithinAt_totalSpace_iff I
    (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) (e.mem_source.mpr he)).mp hZ
  apply mdifferentiableWithinAt_iff_differentiableWithinAt.mp
  apply h.2.congr_of_eventuallyEq
  · filter_upwards [h.1.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he)] with s hs
    exact e.continuousLinearMapAt_apply_of_mem ℝ hs (Z s)
  · exact e.continuousLinearMapAt_apply_of_mem ℝ he (Z t)

theorem IsMetricCompatible.derivAlongWithin_inner
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {J : Set ℝ} {t : ℝ}
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J t)
    (hW : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, W s⟩ : TotalSpace F V)) J t) :
    derivWithin (fun s => inner ℝ (Z s) (W s)) J t =
      inner ℝ (cov.derivAlongWithin γ Z J t) (W t) +
        inner ℝ (Z t) (cov.derivAlongWithin γ W J t) := by
  classical
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  swap
  · simp only [derivWithin_zero_of_not_uniqueDiffWithinAt hJ,
      cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ Z hJ,
      cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ W hJ,
      inner_zero_left, inner_zero_right, zero_add]
  let e := trivializationAt F V (γ t)
  have he : γ t ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t)
  let z : ℝ → F := fun s => e.continuousLinearMapAt ℝ (γ s) (Z s)
  let w : ℝ → F := fun s => e.continuousLinearMapAt ℝ (γ s) (W s)
  let B : M → F →L[ℝ] F →L[ℝ] ℝ := fun x =>
    (innerSL ℝ : V x →L[ℝ] V x →L[ℝ] ℝ).bilinearComp (e.symmL ℝ x) (e.symmL ℝ x)
  have hsection (v : F) : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 1
      (fun x => (⟨x, e.symmL ℝ x v⟩ : TotalSpace F V)) (γ t) := by
    rw [e.contMDiffAt_section_iff he]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with x hx
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hx]
    exact e.continuousLinearMapAt_symmL hx v
  have hB : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) 1 B (γ t) := by
    apply contMDiffAt_clm_of_pointwise
    intro v
    apply contMDiffAt_clm_of_pointwise
    intro u
    exact (hsection v).inner_bundle (hsection u)
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ J t :=
    ((e.mdifferentiableWithinAt_totalSpace_iff I
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) (e.mem_source.mpr he)).mp hZ).1
  have hBdiff : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) B (γ t) :=
    hB.mdifferentiableAt (by simp)
  have hBcomp : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)
      (fun s => B (γ s)) J t := hBdiff.comp_mdifferentiableWithinAt t hγ
  have hBγ : DifferentiableWithinAt ℝ (fun s => B (γ s)) J t := by
    rwa [mdifferentiableWithinAt_iff_differentiableWithinAt] at hBcomp
  have hz := differentiableWithinAt_coord_along e he hZ
  have hw := differentiableWithinAt_coord_along e he hW
  have heq : (fun s => inner ℝ (Z s) (W s)) =ᶠ[𝓝[J] t]
      (fun s => B (γ s) (z s) (w s)) := by
    filter_upwards [hγ.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he)] with s hs
    simp only [B, z, w, ContinuousLinearMap.bilinearComp_apply,
      e.symmL_continuousLinearMapAt hs, innerSL_apply_apply]
  have heq₀ : inner ℝ (Z t) (W t) = B (γ t) (z t) (w t) := by
    simp only [B, z, w, ContinuousLinearMap.bilinearComp_apply,
      e.symmL_continuousLinearMapAt he, innerSL_apply_apply]
  have hD : derivWithin (fun s => inner ℝ (Z s) (W s)) J t =
      derivWithin (fun s => B (γ s)) J t (z t) (w t) +
        B (γ t) (derivWithin z J t) (w t) + B (γ t) (z t) (derivWithin w J t) := by
    rw [heq.derivWithin_eq heq₀, derivWithin_clm_apply (hBγ.clm_apply hz) hw,
      derivWithin_clm_apply hBγ hz, add_apply]
  let X := mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)
  have hfixed : derivWithin (fun s => B (γ s)) J t (z t) (w t) =
      mvfderiv I (fun x => B x (z t) (w t)) (γ t) X := by
    have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => B x (z t) (w t)) (γ t) :=
      ((hsection (z t)).inner_bundle (hsection (w t))).mdifferentiableAt (by simp)
    have h := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] ℝ =>
      L ((NormedSpace.fromTangentSpace t).symm 1))
      (mvfderiv_comp_mfderivWithin t hf hγ hJ.uniqueMDiffWithinAt)
    rw [DifferentialGeometry.mvfderivWithin_model_apply_eq_fderivWithin] at h
    change derivWithin (fun s => B (γ s) (z t) (w t)) J t = _ at h
    rw [derivWithin_clm_apply (hBγ.clm_apply (differentiableWithinAt_const (z t)))
      (differentiableWithinAt_const (w t)),
      derivWithin_clm_apply hBγ (differentiableWithinAt_const (z t))] at h
    simp only [derivWithin_fun_const, Pi.zero_apply, map_zero, add_zero] at h
    exact h
  have hcon (v : F) : cov (fun x => e.symmL ℝ x v) (γ t) X =
      e.symmL ℝ (γ t) (cov.connectionForm e (γ t) X v) := by
    rw [cov.connectionForm_apply e he]
    exact (e.symmL_continuousLinearMapAt he _).symm
  have hmetric := hcov.mvfderiv_inner_eq
    (Function.update (fun x => (0 : TangentSpace I x)) (γ t) X)
    ((hsection (z t)).mdifferentiableAt (by simp))
    ((hsection (w t)).mdifferentiableAt (by simp))
  simp only [Function.update_self, hcon] at hmetric
  change mvfderiv I (fun x => B x (z t) (w t)) (γ t) X =
    B (γ t) (cov.connectionForm e (γ t) X (z t)) (w t) +
      B (γ t) (z t) (cov.connectionForm e (γ t) X (w t)) at hmetric
  have hz₀ : e.symmL ℝ (γ t) (z t) = Z t := e.symmL_continuousLinearMapAt he (Z t)
  have hw₀ : e.symmL ℝ (γ t) (w t) = W t := e.symmL_continuousLinearMapAt he (W t)
  rw [cov.derivAlongWithin_eq e he hZ, cov.derivAlongWithin_eq e he hW, ← hz₀, ← hw₀]
  simp only [e.continuousLinearMapAt_symmL he]
  change derivWithin (fun s => inner ℝ (Z s) (W s)) J t =
    B (γ t) (derivWithin z J t + cov.connectionForm e (γ t) X (z t)) (w t) +
      B (γ t) (z t) (derivWithin w J t + cov.connectionForm e (γ t) X (w t))
  rw [hD, hfixed, hmetric]
  simp only [map_add, add_apply]
  ring

theorem IsMetricCompatible.inner_eq_of_parallel
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {J : Set ℝ} (hJ : Convex ℝ J)
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace F V)) J)
    (hW : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, W s⟩ : TotalSpace F V)) J)
    (hZpar : ∀ t ∈ J, cov.derivAlongWithin γ Z J t = 0)
    (hWpar : ∀ t ∈ J, cov.derivAlongWithin γ W J t = 0)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    inner ℝ (Z s) (W s) = inner ℝ (Z t) (W t) := by
  have hdiff : DifferentiableOn ℝ (fun r => inner ℝ (Z r) (W r)) J := by
    simpa only [mdifferentiableOn_iff_differentiableOn] using hZ.inner_bundle hW
  have hbound : ∀ r ∈ J, ‖derivWithin (fun q => inner ℝ (Z q) (W q)) J r‖ ≤ 0 := by
    intro r hr
    rw [hcov.derivAlongWithin_inner (hZ r hr) (hW r hr), hZpar r hr, hWpar r hr]
    simp only [inner_zero_left, inner_zero_right, zero_add, norm_zero, le_refl]
  have h := hJ.norm_image_sub_le_of_norm_derivWithin_le hdiff hbound ht hs
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h

end CovariantDerivative
