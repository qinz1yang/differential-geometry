import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.RiemannianMetricTensor
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

private local instance sourceC1 : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance targetC1 : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)

private local instance : TopologicalSpace
    (TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y)) :=
  tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem localPullInner_inCoordinates
    (g : SmoothRiemannianMetric J N) (f : M → N) (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hfx : f x ∈ (trivializationAt F (TangentSpace J) (f x₀)).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x (localPullInner g f x) =
      pullbackForm
        (ContinuousLinearMap.inCoordinates F (TangentSpace J) (F →L[ℝ] ℝ)
          (fun y => TangentSpace J y →L[ℝ] ℝ) (f x₀) (f x) (f x₀) (f x)
          (g.inner (f x)), inTangentCoordinates I J id f (mfderiv I J f) x₀ x) := by
  let e := trivializationAt E (TangentSpace I) x₀
  let e' := trivializationAt F (TangentSpace J) (f x₀)
  have hD (v : E) :
      e'.symm (f x) (inTangentCoordinates I J id f (mfderiv I J f) x₀ x v) =
        mfderiv I J f x (e.symm x v) := by
    rw [← e'.symmL_apply (R := ℝ) hfx]
    change e'.symmL ℝ (f x)
      (e'.continuousLinearMapAt ℝ (f x)
        (mfderiv I J f x (e.symmL ℝ x v))) = _
    rw [e'.symmL_continuousLinearMapAt (R := ℝ) hfx, e.symmL_apply hx]
  ext v w
  rw [pullbackForm_apply, inCoordinates_apply_eq₂ hx hx (by simp),
    inCoordinates_apply_eq₂ hfx hfx (by simp)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
  rw [localPullInner_apply, hD, hD]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A map of class `C^(n+1)` gives a raw pullback bilinear field of class `C^n`
at the same point. No immersion or infinitely smooth map is assumed. -/
theorem contMDiffAt_localPullInner_of_contMDiffAt
    (g : SmoothRiemannianMetric J N) {f : M → N} {x : M} {n : ℕ}
    (hf : ContMDiffAt I J (n + 1) f x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y => (⟨y, localPullInner g f y⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) x := by
  let B (z : N) := ContinuousLinearMap.inCoordinates F (TangentSpace J) (F →L[ℝ] ℝ)
    (fun y => TangentSpace J y →L[ℝ] ℝ) (f x) z (f x) z (g.inner z)
  let D (y : M) := inTangentCoordinates I J id f (mfderiv I J f) x y
  have hB : ContMDiffAt J 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n B (f x) :=
    (contMDiffAt_hom_bundle _).mp
      ((g.contMDiff.contMDiffAt (x := f x)).of_le (by simp)) |>.2
  have hfn : ContMDiffAt I J n f x := hf.of_le (by exact_mod_cast Nat.le_succ n)
  have hD : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) n D x :=
    hf.mfderiv_const (by simp)
  have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n
      (fun y => pullbackForm (B (f y), D y)) x :=
    ((pullbackForm.contDiff.of_le (by simp)).contMDiff.contMDiffAt).comp x
      ((hB.comp x hfn).prodMk_space hD)
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, hcomp.congr_of_eventuallyEq ?_⟩
  have hsource : ∀ᶠ y in 𝓝 x, y ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)
  have htarget : ∀ᶠ y in 𝓝 x,
      f y ∈ (trivializationAt F (TangentSpace J) (f x)).baseSet :=
    hf.continuousAt ((trivializationAt F (TangentSpace J) (f x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F (TangentSpace J) (f x)))
  filter_upwards [hsource, htarget] with y hy hfy
  exact localPullInner_inCoordinates g f x y hy hfy

private theorem tensor02_trivialization_eq {x₀ x : M}
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y) x₀
      ⟨x, ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp
        A).uncurryLeft⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm
        ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp
          ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
            (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
            x₀ ⟨x, A⟩).2)) := by
  let e := trivializationAt E (TangentSpace I) x₀
  ext v
  change (((e.continuousMultilinearMap ℝ 2)
    ⟨x, ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp
      A).uncurryLeft⟩).2) v = _
  rw [Trivialization.continuousMultilinearMap_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hom_trivializationAt_apply]
  change A (e.symmL ℝ x (v 0)) (e.symmL ℝ x (Fin.tail v 0)) =
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x A (v 0) (Fin.tail v 0)
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [e, Trivialization.symmL_apply (trivializationAt E (TangentSpace I) x₀) hx,
    Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]

private theorem contMDiffAt_tensor02_of_bilinear {n : ℕ} {x : M}
    (A : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y => (⟨y, A y⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) n
      (fun y : M => (⟨y,
        ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp
          (A y)).uncurryLeft⟩ : TotalSpace (Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SSpace 2 I y))) x := by
  let L₁ := (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap
  let L₂ := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap
  have hcoeff := (contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x).mp hA
  have hcurried := (contMDiffAt_const (c := L₁)).clm_comp hcoeff
  have hconverted := L₂.contMDiffAt.comp x hcurried
  apply (contMDiffAt_section (F := Tensor0SModel 2 ℝ E)
    (E := fun y : M => Tensor0SSpace 2 I y) x).mpr
  apply hconverted.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  exact tensor02_trivialization_eq (A y) hy

omit [FiniteDimensional ℝ F] in
/-- The actual raw pullback error against a smooth reference metric has the
finite regularity supplied by the original map. This is the tensor used in
the finite cusp metric-error hypothesis. -/
theorem contMDiffAt_localPullMetricError_of_contMDiffAt
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    {f : M → N} {x : M} {n : ℕ} (hf : ContMDiffAt I J (n + 1) f x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) n
      (fun y : M => (⟨y,
        ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g f y - G.inner y)).uncurryLeft⟩ :
            TotalSpace (Tensor0SModel 2 ℝ E) (fun y : M => Tensor0SSpace 2 I y))) x := by
  apply contMDiffAt_tensor02_of_bilinear
  exact (contMDiffAt_localPullInner_of_contMDiffAt g hf).sub_section
    ((G.contMDiff.contMDiffAt (x := x)).of_le (by simp))

end DifferentialGeometry
