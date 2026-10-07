import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Bundle.TangentSpace
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.Derivative

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Coordinates

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A joint endpoint/time graph is a C2 local diffeomorphism when its actual
spatial endpoint differential is bijective. The parameter model may differ from
the manifold model, and no infinite smoothness is inferred. -/
theorem isLocalDiffeomorphAt_parameter_graph_of_slice_bijective_two
    {alpha : P × ℝ → M} {z : P} {b : ℝ}
    (halpha : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I 2 alpha (z, b))
    (hslice : Function.Bijective
      (mfderiv 𝓘(ℝ, P) I (fun w => alpha (w, b)) z)) :
    IsLocalDiffeomorphAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 2
      (fun q : P × ℝ => (alpha q, q.2)) (z, b) := by
  let _ : CompleteSpace P := FiniteDimensional.complete ℝ P
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let J := 𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)
  let K := I.prod 𝓘(ℝ, ℝ)
  let F : P × ℝ → M × ℝ := fun q => (alpha q, q.2)
  let A : P →L[ℝ] E := mfderiv 𝓘(ℝ, P) I (fun w => alpha (w, b)) z
  let B : ℝ →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ) I (fun r => alpha (z, r)) b
  let D : (P × ℝ) →L[ℝ] (E × ℝ) := mfderiv J K F (z, b)
  have hdiff : MDifferentiableAt J I alpha (z, b) :=
    halpha.mdifferentiableAt (by norm_num)
  have hD (v : P × ℝ) : D v = (A v.1 + B v.2, v.2) := by
    have hsnd : MDifferentiableAt J 𝓘(ℝ, ℝ) (Prod.snd : P × ℝ → ℝ) (z, b) :=
      mdifferentiableAt_snd
    change mfderiv J K (fun q : P × ℝ => (alpha q, q.2)) (z, b) v = _
    rw [mfderiv_prodMk hdiff hsnd, mfderiv_snd]
    change (mfderiv J I alpha (z, b) v, v.2) = (A v.1 + B v.2, v.2)
    apply Prod.ext
    · exact mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, P)) (I' := 𝓘(ℝ, ℝ))
        (I'' := I) (f := alpha) (p := (z, b)) (v := v) hdiff
    · rfl
  have hDinj : Function.Injective D := by
    intro v w hvw
    rw [hD, hD] at hvw
    have hvw2 : v.2 = w.2 := congrArg (fun x : E × ℝ => x.2) hvw
    have hvw1 : A v.1 + B v.2 = A w.1 + B w.2 :=
      congrArg (fun x : E × ℝ => x.1) hvw
    rw [hvw2] at hvw1
    have hAvw : A v.1 = A w.1 := add_right_cancel hvw1
    exact Prod.ext (hslice.1 hAvw) hvw2
  have hDsurj : Function.Surjective D := by
    intro w
    obtain ⟨v, hv⟩ := hslice.2 (w.1 - B w.2)
    refine ⟨(v, w.2), ?_⟩
    rw [hD]
    apply Prod.ext
    · change A v + B w.2 = w.1
      rw [show A v = w.1 - B w.2 from hv, sub_add_cancel]
    · rfl
  let L : (P × ℝ) ≃L[ℝ] (E × ℝ) := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hDinj) (LinearMap.range_eq_top.mpr hDsurj)
  have hDinv : (mfderiv J K F (z, b)).IsInvertible := ⟨L, rfl⟩
  exact contMDiffAt_isLocalDiffeomorphAt_of_mfderiv (by norm_num) (by decide)
    (halpha.prodMk contMDiffAt_snd) hDinv

/-- The terminal exponential germ produced by a joint variation supplies the
required endpoint inverse. Its linear isomorphism is the chosen endpoint frame,
not a shooting-map differential or an additional nonconjugacy hypothesis. -/
theorem isLocalDiffeomorphAt_parameter_graph_of_exponential_germ_two
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (q : M) (B : P ≃L[ℝ] E)
    {alpha : P × ℝ → M} {b : ℝ}
    (halpha : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I 2 alpha (0, b))
    (hexp : (fun z => alpha (z, b)) =ᶠ[𝓝 (0 : P)]
      (fun z => DifferentialGeometry.Geometry.Riemannian.Exponential.expMap
        g q (show TangentSpace I q from B z))) :
    alpha (0, b) = q ∧
      IsLocalDiffeomorphAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 2
        (fun z : P × ℝ => (alpha z, z.2)) (0, b) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcenter : alpha (0, b) = q := by
    have hh := hexp.self_of_nhds
    have hzero : (show TangentSpace I q from B (0 : P)) =
        (0 : TangentSpace I q) := by
      change B (0 : P) = (0 : E)
      exact B.map_zero
    exact hh.trans ((congrArg
      (DifferentialGeometry.Geometry.Riemannian.Exponential.expMap g q) hzero).trans
        (DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_zero g q))
  let ex : E → M := fun w =>
    DifferentialGeometry.Geometry.Riemannian.Exponential.expMap
      g q (show TangentSpace I q from w)
  have hexMD : MDifferentiableAt 𝓘(ℝ, E) I ex 0 :=
    (DifferentialGeometry.Geometry.Riemannian.Exponential.contMDiffAt_expMap g q
      (DifferentialGeometry.Geometry.Riemannian.Exponential.zero_mem_expDomain g q)).mdifferentiableAt
        (by simp)
  have hexD : mfderiv 𝓘(ℝ, E) I ex 0 = ContinuousLinearMap.id ℝ E :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.mfderiv_expMap_at_zero g q
  let Blin : P →L[ℝ] E := B.toContinuousLinearMap
  have hBMD : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, E) Blin 0 :=
    Blin.differentiableAt.mdifferentiableAt
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, P)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (0 : P) (by simpa only [map_zero] using hexMD) hBMD
  have hsliced : (mfderiv 𝓘(ℝ, P) I (fun z => alpha (z, b)) 0 : P →L[ℝ] E) =
      B.toContinuousLinearMap := by
    rw [hexp.mfderiv_eq]
    change mfderiv 𝓘(ℝ, P) I (ex ∘ Blin) 0 = B.toContinuousLinearMap
    rw [hcomp, map_zero, hexD, mfderiv_eq_fderiv, Blin.fderiv]
    ext z
    rfl
  refine ⟨hcenter, isLocalDiffeomorphAt_parameter_graph_of_slice_bijective_two halpha ?_⟩
  rw [hsliced]
  exact B.bijective

end DifferentialGeometry.Coordinates
