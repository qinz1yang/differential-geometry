import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Topology.Manifold.OpenSubtype

noncomputable section

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

open Connection Riemannian.Geodesic Riemannian.CovariantDerivativeAlong

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem covariantAcceleration_opens_eq_deriv_deriv_add
    (U : TopologicalSpace.Opens F) (G : SmoothRiemannianMetric 𝓘(ℝ, F) U)
    {c : ℝ → U} (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ c) (t : ℝ) :
    (covariantAcceleration G c t : F) =
      deriv (deriv (fun s => (c s : F))) t +
        chartChristoffelContraction G (c t)
          (deriv (fun s => (c s : F)) t)
          (deriv (fun s => (c s : F)) t) (c t) := by
  have h := covariantAcceleration_modelCoord G c t hc
  have heq : Riemannian.AlongCurve.chartCurve (I := 𝓘(ℝ, F)) (c t) c =
      fun s => (c s : F) := by
    funext s
    change extChartAt 𝓘(ℝ, F) (c t) (c s) = (c s : F)
    rfl
  have hpoint : extChartAt 𝓘(ℝ, F) (c t) (c t) = (c t : F) := rfl
  rw [heq, hpoint] at h
  change @Eq F (covariantAcceleration G c t)
    (deriv (deriv (fun s => (c s : F))) t +
      chartChristoffelContraction G (c t)
        (deriv (fun s => (c s : F)) t)
        (deriv (fun s => (c s : F)) t) (c t))
  simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using h


variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless]
    [IsManifold I ∞ M] in
private theorem fderiv_comp_embedding_apply
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {P : F → F} {x : M} (hP : DifferentiableAt ℝ P (e x))
    (hPe : P ∘ e = e) (v : TangentSpace I x) :
    fderiv ℝ P (e x) (mfderiv I 𝓘(ℝ, F) e x v) =
      mfderiv I 𝓘(ℝ, F) e x v := by
  have hd := mfderiv_comp x hP.mdifferentiableAt (he.mdifferentiable (by simp) x)
  rw [hPe, mfderiv_eq_fderiv] at hd
  exact (congrArg (fun L : E →L[ℝ] F => L v) hd).symm

theorem retraction_christoffel_residual_eq_zero_open
    (g : SmoothRiemannianMetric I M) {U : TopologicalSpace.Opens F}
    (G : SmoothRiemannianMetric 𝓘(ℝ, F) U)
    {e : M → U} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hgeo : hasVanishingSecondFundamentalFormAlongCurves g G e)
    {P : F → F} (hPe : P ∘ (fun x => (e x : F)) = (fun x => (e x : F)))
    (x : M) (hP : ContDiffAt ℝ 2 P (e x : F)) (v : TangentSpace I x) :
    let w : F := mfderiv I 𝓘(ℝ, F) e x v
    let Γ := chartChristoffelContraction G (e x) w w (e x)
    Γ - fderiv ℝ P (e x : F) Γ + fderiv ℝ (fderiv ℝ P) (e x : F) w w = 0 := by
  let eVal : M → F := fun y => (e y : F)
  have heVal : ContMDiff I 𝓘(ℝ, F) ∞ eVal := contMDiff_subtype_val.comp he
  obtain ⟨γ, hγ, _, hv⟩ := exists_contMDiff_curve_with_velocity_range_subset
    (I := I) BoundarylessManifold.isInteriorPoint v (Filter.univ_mem : Set.univ ∈ 𝓝 x)
  let c : ℝ → U := e ∘ γ
  let cVal : ℝ → F := fun t => (c t : F)
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ c := he.comp hγ
  have hcVal : ContDiff ℝ ∞ cVal := (contMDiff_subtype_val.comp hc).contDiff
  have hxU : c 0 = e x := congrArg e (congrArg Bundle.TotalSpace.proj hv)
  have hx : cVal 0 = (e x : F) := congrArg (fun y : U => (y : F)) hxU
  have hvel : deriv cVal 0 = mfderiv I 𝓘(ℝ, F) e x v := by
    have hd := mfderiv_comp 0 (heVal.mdifferentiable (by simp) (γ 0))
      (hγ.mdifferentiable (by simp) 0)
    have htotal := congrArg
      (fun q : TangentBundle I M => (mfderiv I 𝓘(ℝ, F) eVal q.1 q.2 : F)) hv
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (eVal ∘ γ) 0 1 = _
    rw [hd]
    rw [mfderiv_subtypeVal_comp (I := I) (J := 𝓘(ℝ, F)) e x] at htotal
    exact htotal
  have hPc : P ∘ cVal = cVal := by
    funext t
    exact congrFun hPe (γ t)
  have hsecond := iteratedDeriv_vcomp_two
    (show ContDiffAt ℝ 2 P (cVal 0) by simpa only [hx] using hP)
    (hcVal.contDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ ∞))
  simp only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
    Function.iterate_zero_apply, iteratedFDeriv_two_apply, hPc] at hsecond
  have hacc : (covariantAcceleration G c 0 : F) =
      (mfderiv I 𝓘(ℝ, F) e (γ 0) (covariantAcceleration g γ 0) : F) :=
    hgeo.covariantAcceleration_comp γ 0 hγ
  have hfix : fderiv ℝ P (cVal 0) (covariantAcceleration G c 0) =
      covariantAcceleration G c 0 := by
    rw [hacc]
    have hh := fderiv_comp_embedding_apply heVal
      (show DifferentiableAt ℝ P (eVal (γ 0)) by
        simpa only [show eVal (γ 0) = cVal 0 from rfl, hx] using
          hP.differentiableAt (by norm_num)) hPe (covariantAcceleration g γ 0)
    rw [show mfderiv I 𝓘(ℝ, F) eVal (γ 0) = mfderiv I 𝓘(ℝ, F) e (γ 0) from
      mfderiv_subtypeVal_comp e (γ 0)] at hh
    exact hh
  rw [covariantAcceleration_opens_eq_deriv_deriv_add U G hc, map_add] at hfix
  have hH := eq_sub_iff_add_eq.mpr hsecond.symm
  have hres : chartChristoffelContraction G (c 0) (deriv cVal 0) (deriv cVal 0) (c 0) -
      fderiv ℝ P (cVal 0)
        (chartChristoffelContraction G (c 0) (deriv cVal 0) (deriv cVal 0) (c 0)) +
      fderiv ℝ (fderiv ℝ P) (cVal 0) (deriv cVal 0) (deriv cVal 0) = 0 := by
    rw [hH]
    calc
      _ = (deriv (deriv cVal) 0 +
          chartChristoffelContraction G (c 0) (deriv cVal 0) (deriv cVal 0) (c 0)) -
        (fderiv ℝ P (cVal 0) (deriv (deriv cVal) 0) +
          fderiv ℝ P (cVal 0)
            (chartChristoffelContraction G (c 0) (deriv cVal 0) (deriv cVal 0) (c 0))) := by abel
      _ = 0 := sub_eq_zero.mpr hfix.symm
  rw [hxU, hx, hvel] at hres
  exact hres

theorem retraction_christoffel_residual_fderiv_eq_zero_open
    (g : SmoothRiemannianMetric I M) {U : TopologicalSpace.Opens F}
    (G : SmoothRiemannianMetric 𝓘(ℝ, F) U)
    {e : M → U} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hgeo : hasVanishingSecondFundamentalFormAlongCurves g G e)
    {r : F → M} (hleft : ∀ x, r ((e x : F)) = x) {z : F}
    (hr : MDifferentiableAt 𝓘(ℝ, F) I r z)
    (hP : ContDiffAt ℝ 2 (fun y => (e (r y) : F)) (e (r z) : F)) (v : F) :
    let P := fun y => (e (r y) : F)
    let w := fderiv ℝ P z v
    let Γ := chartChristoffelContraction G (e (r z)) w w (e (r z))
    Γ - fderiv ℝ P (e (r z) : F) Γ + fderiv ℝ (fderiv ℝ P) (e (r z) : F) w w = 0 := by
  let P : F → F := fun y => (e (r y) : F)
  have hPe : P ∘ (fun x => (e x : F)) = (fun x => (e x : F)) := by
    funext x
    dsimp [P]
    rw [hleft]
  have hvel : fderiv ℝ P z v =
      (mfderiv I 𝓘(ℝ, F) e (r z) (mfderiv 𝓘(ℝ, F) I r z v) : F) := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ((fun x => (e x : F)) ∘ r) z v = _
    have heVal : ContMDiff I 𝓘(ℝ, F) ∞ (fun x => (e x : F)) :=
      contMDiff_subtype_val.comp he
    rw [mfderiv_comp z (heVal.mdifferentiable (by simp) (r z)) hr,
      mfderiv_subtypeVal_comp e (r z)]
    rfl
  have h := retraction_christoffel_residual_eq_zero_open g G he hgeo hPe (r z) hP
    (mfderiv 𝓘(ℝ, F) I r z v)
  dsimp [P] at h ⊢
  rw [hvel]
  exact h


theorem retraction_christoffel_residual_eq_zero_of_extension
    (g : SmoothRiemannianMetric I M) {U : TopologicalSpace.Opens F}
    (G : SmoothRiemannianMetric 𝓘(ℝ, F) U)
    {e : M → U} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hgeo : hasVanishingSecondFundamentalFormAlongCurves g G e)
    {r : U → M} (hleft : ∀ x, r (e x) = x) {z : U}
    (hr : MDifferentiableAt 𝓘(ℝ, F) I r z)
    {P : F → F} (hPext : ∀ y : U, P y = (e (r y) : F))
    (hP : ContDiffAt ℝ 2 P (e (r z) : F)) (v : F) :
    let w := fderiv ℝ P (z : F) v
    let Γ := chartChristoffelContraction G (e (r z)) w w (e (r z))
    Γ - fderiv ℝ P (e (r z) : F) Γ + fderiv ℝ (fderiv ℝ P) (e (r z) : F) w w = 0 := by
  have hPe : P ∘ (fun x => (e x : F)) = (fun x => (e x : F)) := by
    funext x
    simp only [Function.comp_apply, hPext, hleft]
  have hvel : fderiv ℝ P (z : F) v =
      (mfderiv I 𝓘(ℝ, F) e (r z) (mfderiv 𝓘(ℝ, F) I r z v) : F) := by
    have heVal : ContMDiff I 𝓘(ℝ, F) ∞ (fun x => (e x : F)) :=
      contMDiff_subtype_val.comp he
    have hrestrict : (fun y : U => P y) = (fun x => (e x : F)) ∘ r := funext hPext
    have hd := mfderiv_comp z (heVal.mdifferentiable (by simp) (r z)) hr
    rw [← hrestrict, mfderiv_restrict_open P U z, mfderiv_eq_fderiv,
      mfderiv_subtypeVal_comp e (r z)] at hd
    exact congrArg (fun L : F →L[ℝ] F => L v) hd
  have h := retraction_christoffel_residual_eq_zero_open g G he hgeo hPe (r z) hP
    (mfderiv 𝓘(ℝ, F) I r z v)
  dsimp only at h ⊢
  rw [hvel]
  exact h

end DifferentialGeometry.Geometry
