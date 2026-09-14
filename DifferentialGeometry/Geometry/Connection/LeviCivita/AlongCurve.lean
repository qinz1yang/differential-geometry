import DifferentialGeometry.Geometry.Connection.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionContraction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

open Riemannian.Geodesic
open Riemannian.AlongCurve
open Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem connectionForm_leviCivita_apply
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (X : TangentSpace I x) (v : E) :
    (LeviCivita g).connectionForm (trivializationAt E (TangentSpace I) α) x X v =
      chartChristoffelContraction g α (trivToE (I := I) α x X) v (extChartAt I α x) := by
  let e := trivializationAt E (TangentSpace I) α
  have he : x ∈ e.baseSet := chartLeviCivitaGoodSet_mem_baseSet hx
  let σ := fun y => e.symmL ℝ y v
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% σ) x := by
    rw [e.mdifferentiableAt_section_iff I σ he]
    apply (mdifferentiableAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact e.continuousLinearMapAt_symmL hy v
  have hrepr (y : M) (hy : y ∈ e.baseSet) : chartESectionRepr (I := I) α σ y = v := by
    rw [chartE_section_repr_eq_trivToE]
    exact e.continuousLinearMapAt_symmL hy v
  have hconst : (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α x)]
      fun _ => v := by
    filter_upwards [isOpen_interior.mem_nhds
      (chartLeviCivitaGoodSet_extChartAt_mem_interior hx)] with z hz
    apply hrepr
    have h := (extChartAt I α).map_target (interior_subset hz)
    simpa only [e, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using h
  have hD : fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) = 0 := by
    rw [hconst.fderiv_eq, fderiv_const_apply]
  rw [CovariantDerivative.connectionForm_apply _ _ he,
    LeviCivita_chart_apply g α hx hσ X, chartLeviCivita_apply g α σ hx X,
    hD, zero_apply, zero_add, hrepr x he]
  change e.continuousLinearMapAt ℝ x
    (e.symmL ℝ x (christoffelCorrection g α x v X)) = _
  rw [e.continuousLinearMapAt_symmL he, correction_eq_contr]

theorem derivAlongWithin_leviCivita_eq_covDerivAlong
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (Z : ∀ r, TangentSpace I (γ r)) {J : Set ℝ} {t : ℝ}
    (hJ : J ∈ 𝓝 t) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hint : I.IsInteriorPoint (γ t)) :
    (LeviCivita g).derivAlongWithin γ Z J t = covDerivAlong g γ Z t := by
  have hgood : γ t ∈ chartLeviCivitaGoodSet (I := I) (γ t) :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨mem_extChartAt_source _,
      mem_baseSet_trivializationAt E (TangentSpace I) _, I.isInteriorPoint_iff.mp hint⟩
  have hvel : trivToE (I := I) (γ t) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t ((NormedSpace.fromTangentSpace t).symm 1)) =
        deriv (chartCurve (I := I) (γ t) γ) t := by
    have h :=
      Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) hγ (γ t) (mem_chart_source H (γ t))
    change trivToE (I := I) (γ t) (γ t)
      ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) = _
    rw [trivToE, h]
    exact fderiv_apply_one_eq_deriv
  simp only [CovariantDerivative.derivAlongWithin, covDerivAlong_def, chartCovDerivAlong_def,
    derivWithin_of_mem_nhds hJ, mfderivWithin_of_mem_nhds hJ]
  rw [connectionForm_leviCivita_apply g (γ t) hgood, hvel]
  rfl

theorem derivAlongWithin_velocity_eq_zero_of_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {J : Set ℝ} {t : ℝ}
    (hJ : J ∈ 𝓝 t) (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hint : I.IsInteriorPoint (γ t)) (hgeo : HasGeodesicEquationAt g γ t) :
    (LeviCivita g).derivAlongWithin γ
      (fun r => mfderivWithin 𝓘(ℝ, ℝ) I γ J r
        ((NormedSpace.fromTangentSpace r).symm 1)) J t = 0 := by
  have heq : ∀ᶠ r in 𝓝[J] t,
      mfderivWithin 𝓘(ℝ, ℝ) I γ J r ((NormedSpace.fromTangentSpace r).symm 1) =
        mfderiv 𝓘(ℝ, ℝ) I γ r ((NormedSpace.fromTangentSpace r).symm 1) := by
    filter_upwards [(eventually_mem_nhds_iff.mpr hJ).filter_mono nhdsWithin_le_nhds] with r hr
    rw [mfderivWithin_of_mem_nhds hr]
  rw [(LeviCivita g).derivAlongWithin_congr_of_eventuallyEq heq
    (by rw [mfderivWithin_of_mem_nhds hJ])]
  rw [derivAlongWithin_leviCivita_eq_covDerivAlong g γ _ hJ
    (hγ.mdifferentiableAt (by norm_num)) hint]
  exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ t hγ hgeo

end DifferentialGeometry.Geometry.Connection

namespace CovariantDerivative

open DifferentialGeometry (SmoothRiemannianMetric)
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem hessian_apply_velocity_of_hasGeodesicEquationAt
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {σ : ∀ x, V x} {J : Set ℝ} {t : ℝ}
    (hJ : J ∈ 𝓝 t) (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) (γ t))
    (hint : I.IsInteriorPoint (γ t)) (hgeo : HasGeodesicEquationAt g γ t) :
    let velocity := mfderivWithin 𝓘(ℝ, ℝ) I γ J t
      ((NormedSpace.fromTangentSpace t).symm 1)
    cov.hessian (LeviCivita g) σ (γ t) velocity velocity =
      cov.derivAlongWithin γ
        (fun r => cov.derivAlongWithin γ (fun u => σ (γ u)) J r) J t := by
  have h := cov.derivAlongWithin_derivAlongWithin_section hcov (LeviCivita g) hJ hγ hσ
  dsimp only at h ⊢
  rw [derivAlongWithin_velocity_eq_zero_of_hasGeodesicEquationAt g γ hJ hγ hint hgeo,
    map_zero, add_zero] at h
  exact h.symm

end CovariantDerivative


namespace DifferentialGeometry.Geometry.Connection

open Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem derivAlongWithin_leviCivita_eq_covDerivAlong_of_mdifferentiableAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (Z : ∀ r, TangentSpace I (γ r)) {J : Set ℝ} {t : ℝ}
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
      (fun s => (⟨γ s, Z s⟩ : TangentBundle I M)) t)
    (hint : I.IsInteriorPoint (γ t)) :
    (LeviCivita g).derivAlongWithin γ Z J t = covDerivAlong g γ Z t := by
  rw [(LeviCivita g).derivAlongWithin_mono hZ.mdifferentiableWithinAt hJ (subset_univ J)]
  exact derivAlongWithin_leviCivita_eq_covDerivAlong g γ Z (by simp)
    ((mdifferentiableAt_totalSpace I _).mp hZ).1 hint

end DifferentialGeometry.Geometry.Connection
