import DifferentialGeometry.Geometry.Metric.RicciSoliton.ScalarRigidity
import DifferentialGeometry.Geometry.Comparison.HessianAlongGeodesic
import DifferentialGeometry.Geometry.Comparison.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Existence
import DifferentialGeometry.Geometry.Exponential.RadialFlat

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open Riemannian
open Riemannian.CovariantDerivativeAlong
open Riemannian.Exponential
open Riemannian.Geodesic
open Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] [ConnectedSpace M] in
private theorem mfderiv_comp_add_apply
    {γ : Real → M} (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (b t : Real) :
    (mfderiv 𝓘(Real, Real) I (fun s => γ (s + b)) t (1 : Real) : E) =
      (mfderiv 𝓘(Real, Real) I γ (t + b) (1 : Real) : E) := by
  have hshift : HasMFDerivAt 𝓘(Real, Real) 𝓘(Real, Real)
      (fun s : Real => s + b) t (ContinuousLinearMap.id Real Real) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    exact (hasFDerivAt_id t).add_const b
  have hγat : HasMFDerivAt 𝓘(Real, Real) I γ (t + b)
      (mfderiv 𝓘(Real, Real) I γ (t + b)) :=
    (hγ.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := (hγat.comp t hshift).mfderiv
  change (mfderiv 𝓘(Real, Real) I
      (γ ∘ fun s : Real => s + b) t (1 : Real) : E) =
    (mfderiv 𝓘(Real, Real) I γ (t + b) (1 : Real) : E)
  rw [hcomp]
  change (mfderiv 𝓘(Real, Real) I γ (t + b))
      ((ContinuousLinearMap.id Real Real) (1 : Real)) =
    (mfderiv 𝓘(Real, Real) I γ (t + b)) (1 : Real)
  simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_gradFun_along_geodesic_eq_smul_velocity_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    {γ : Real → M} (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ)
    {t₀ : Real} (hcrit : gradFun (I := I) g f (γ t₀) = 0)
    (t : Real) :
    gradFun (I := I) g f (γ t) =
      ((t - t₀) / 2) •
        (mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] TangentSpace I (γ t)) 1 := by
  let V : (s : Real) → TangentSpace I (γ s) :=
    fun s => gradFun (I := I) g f (γ s)
  let W : (s : Real) → TangentSpace I (γ s) :=
    fun s => (mfderiv 𝓘(Real, Real) I γ s (1 : Real) : E)
  let a : Real → Real := fun s => (s - t₀) / 2
  let A : (s : Real) → TangentSpace I (γ s) :=
    fun s => a s • W s
  let D : (s : Real) → TangentSpace I (γ s) :=
    fun s => V s - A s
  let Z : (s : Real) → TangentSpace I (γ s) :=
    fun s => 0
  have hgrad : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (T% fun z => gradFun (I := I) g f z) :=
    gradFun_contMDiff_total_section (I := I) g f.contMDiff
  have hVdiff (s : Real) :
      DifferentiableAt Real (chartRepAt (I := I) γ V s) s := by
    simpa only [V] using
      chartRepAt_restrict_differentiableAt (I := I) (hγ.of_le (by simp))
        (fun z => gradFun (I := I) g f z) (hgrad.of_le (by simp)) s
  have hWdiff (s : Real) :
      DifferentiableAt Real (chartRepAt (I := I) γ W s) s := by
    simpa only [W] using
      velocity_chartRepAt_differentiableAt (I := I) γ hγ s
  have hadiff (s : Real) : DifferentiableAt Real a s := by
    dsimp only [a]
    fun_prop
  have hA_rep (s : Real) :
      chartRepAt (I := I) γ A s =
        fun r => a r • chartRepAt (I := I) γ W s r := by
    exact chartRepAt_smulFun (I := I) γ a W s
  have hAdiff (s : Real) :
      DifferentiableAt Real (chartRepAt (I := I) γ A s) s := by
    rw [hA_rep]
    exact (hadiff s).smul (hWdiff s)
  have hnegAdiff (s : Real) :
      DifferentiableAt Real
        (chartRepAt (I := I) γ (fun r => (-1 : Real) • A r) s) s := by
    rw [chartRepAt_smul]
    exact (hAdiff s).const_smul (-1)
  have hDdiff (s : Real) :
      DifferentiableAt Real (chartRepAt (I := I) γ D s) s := by
    have hD : D = fun r => V r + (-1 : Real) • A r := by
      funext r
      dsimp only [D]
      rw [sub_eq_add_neg]
      simp
    rw [hD, chartRepAt_add]
    exact (hVdiff s).add (hnegAdiff s)
  have hZdiff (s : Real) :
      DifferentiableAt Real (chartRepAt (I := I) γ Z s) s := by
    have hrep : chartRepAt (I := I) γ Z s = fun _ => (0 : E) := by
      funext r
      simp [Z, chartRepAt]
    rw [hrep]
    fun_prop
  have hVcov (s : Real) :
      covDerivAlong (I := I) g γ V s = (1 / 2 : Real) • W s := by
    rw [show V = fun r => gradFun (I := I) g f (γ r) from rfl]
    rw [covDerivAlong_restrict_eq_leviCivita (I := I) g γ
      (fun z => gradFun (I := I) g f z) s hγ
      (hgrad.contMDiffAt.mdifferentiableAt (by simp))]
    exact
      normalizedGradientRicciSoliton_cov_gradFun_eq_half_smul_of_scalar_eq_zero
        (I := I) h hx (γ s) (W s)
  have hWcov (s : Real) :
      covDerivAlong (I := I) g γ W s = 0 := by
    simpa only [W] using
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g γ s
          (hγ.contMDiffAt.of_le
            (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
          (hgeo s)
  have haderiv (s : Real) : deriv a s = 1 / 2 := by
    simp [a]
  have hAcov (s : Real) :
      covDerivAlong (I := I) g γ A s = (1 / 2 : Real) • W s := by
    rw [show A = fun r => a r • W r from rfl]
    rw [covDerivAlong_smulFun (I := I) g γ a W s
      (hadiff s) (hWdiff s), haderiv s, hWcov s]
    simp
  have hDcov (s : Real) :
      covDerivAlong (I := I) g γ D s = 0 := by
    have hD : D = fun r => V r + (-1 : Real) • A r := by
      funext r
      dsimp only [D]
      rw [sub_eq_add_neg]
      simp
    rw [hD]
    rw [covDerivAlong_add (I := I) g γ V
      (fun r => (-1 : Real) • A r) s (hVdiff s) (hnegAdiff s)]
    rw [covDerivAlong_smul (I := I) g γ (-1 : Real) A s,
      hVcov s, hAcov s]
    simp
  have hZcov (s : Real) :
      covDerivAlong (I := I) g γ Z s = 0 := by
    simpa only [Z] using covDerivAlong_zero (I := I) g γ s
  have ht₀ : t₀ ∈ Set.Icc (min t₀ t) (max t₀ t) := by
    constructor
    · exact min_le_left t₀ t
    · exact le_max_left t₀ t
  have ht : t ∈ Set.Icc (min t₀ t) (max t₀ t) := by
    constructor
    · exact min_le_right t₀ t
    · exact le_max_right t₀ t
  have hDzero : D t₀ = Z t₀ := by
    change V t₀ - A t₀ = 0
    have hVzero : V t₀ = 0 := hcrit
    rw [hVzero]
    simp [A, a]
  have hparallel :=
    parallel_transport_unique_of_eq_at_point (I := I) g γ
      (N := 2) le_rfl
        (hγ.of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) D Z
      (fun s _ => hDdiff s) (fun s _ => hZdiff s)
      (fun s _ => hDcov s) (fun s _ => hZcov s)
      ht₀ hDzero t ht
  change V t - A t = 0 at hparallel
  exact sub_eq_zero.mp hparallel

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_potential_along_geodesic_eq_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    {γ : Real → M} (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ)
    {t₀ : Real} (hcrit : gradFun (I := I) g f (γ t₀) = 0)
    (t : Real) :
    f (γ t) = f (γ t₀) +
      (g.inner (γ t₀)
          ((mfderiv 𝓘(Real, Real) I γ t₀ :
            Real →L[Real] TangentSpace I (γ t₀)) 1)
          ((mfderiv 𝓘(Real, Real) I γ t₀ :
            Real →L[Real] TangentSpace I (γ t₀)) 1) / 4) *
        (t - t₀) ^ 2 := by
  let c : Real :=
    g.inner (γ t₀)
      ((mfderiv 𝓘(Real, Real) I γ t₀ :
        Real →L[Real] TangentSpace I (γ t₀)) 1)
      ((mfderiv 𝓘(Real, Real) I γ t₀ :
        Real →L[Real] TangentSpace I (γ t₀)) 1)
  let q : Real → Real := fun s => f (γ t₀) + (c / 4) * (s - t₀) ^ 2
  have hspeed (s : Real) :
      g.inner (γ s)
          ((mfderiv 𝓘(Real, Real) I γ s :
            Real →L[Real] TangentSpace I (γ s)) 1)
          ((mfderiv 𝓘(Real, Real) I γ s :
            Real →L[Real] TangentSpace I (γ s)) 1) = c := by
    exact (Riemannian.HopfRinow.isGeodesicOn_speedSq_const
      (I := I) g (t₀ := t₀) (t₁ := s) isOpen_univ
      (hgeo.isGeodesicOn Set.univ)
      ((hγ.of_le (by simp)).contMDiffOn) (Set.subset_univ _)).symm
  have hfg : ContDiff Real ∞ (f ∘ γ) :=
    contMDiff_iff_contDiff.mp (f.contMDiff.comp hγ)
  have hfgDiff : Differentiable Real (f ∘ γ) :=
    hfg.differentiable (by simp)
  have hfgDeriv (s : Real) :
      deriv (f ∘ γ) s = ((s - t₀) / 2) * c := by
    rw [deriv_comp_eq_inner_grad_velocity (I := I) g f.contMDiff hγ s,
      normalizedGradientRicciSoliton_gradFun_along_geodesic_eq_smul_velocity_of_scalar_eq_zero
        (I := I) h hx hγ hgeo hcrit s,
      (g.inner (γ s)).map_smul, smul_apply, smul_eq_mul, hspeed s]
  have hfgHas (s : Real) :
      HasDerivAt (f ∘ γ) (((s - t₀) / 2) * c) s := by
    rw [← hfgDeriv s]
    exact (hfgDiff s).hasDerivAt
  have hqHas (s : Real) :
      HasDerivAt q (((s - t₀) / 2) * c) s := by
    have hraw := (hasDerivAt_const s (f (γ t₀))).add
      ((((hasDerivAt_id s).sub_const t₀).pow 2).const_mul (c / 4))
    exact (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => by simp [q])).congr_deriv (by
        simp only [id_eq]
        ring)
  have hdiffHas (s : Real) :
      HasDerivAt ((f ∘ γ) - q) 0 s := by
    simpa only [sub_self] using (hfgHas s).sub (hqHas s)
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hdiffHas s).differentiableAt)
    (fun s => (hdiffHas s).deriv) t t₀
  have hzero : (f ∘ γ) t - q t = 0 := by
    calc
      (f ∘ γ) t - q t = ((f ∘ γ) - q) t := by rw [Pi.sub_apply]
      _ = ((f ∘ γ) - q) t₀ := hconst
      _ = (f ∘ γ) t₀ - q t₀ := by rw [Pi.sub_apply]
      _ = 0 := by simp [q]
  change (f ∘ γ) t = (f ∘ γ) t₀ + (c / 4) * (t - t₀) ^ 2
  exact sub_eq_zero.mp hzero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_riemannOp_velocity_eq_zero_along_geodesic_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    {γ : Real → M} (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ)
    {t₀ : Real} (hcrit : gradFun (I := I) g f (γ t₀) = 0)
    (t : Real) (v w : TangentSpace I (γ t)) :
    riemannOp (LeviCivita (I := I) g) (γ t) v w
      ((mfderiv 𝓘(Real, Real) I γ t :
        Real →L[Real] TangentSpace I (γ t)) 1) = 0 := by
  by_cases ht : t = t₀
  · subst t
    let δ : Real → M := fun s => γ (s + t₀)
    have hδ : ContMDiff 𝓘(Real, Real) I ∞ δ := by
      exact hγ.comp (contDiff_id.add contDiff_const).contMDiff
    have hδgeo : IsGeodesic (I := I) g δ := by
      simpa only [δ] using isGeodesic_comp_add hgeo t₀
    have hδcrit : gradFun (I := I) g f (δ 0) = 0 := by
      change gradFun (I := I) g f (γ (0 + t₀)) = 0
      rw [zero_add]
      exact hcrit
    obtain ⟨V, hV0, hVdiff, _⟩ :=
      Riemannian.Variation.exists_parallel_transport_on_Icc
        (I := I) g δ (N := 2) le_rfl
          (hδ.of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)))
          (L := 1) one_pos v
    obtain ⟨W, hW0, hWdiff, _⟩ :=
      Riemannian.Variation.exists_parallel_transport_on_Icc
        (I := I) g δ (N := 2) le_rfl
          (hδ.of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)))
          (L := 1) one_pos w
    let U : (s : Real) → TangentSpace I (δ s) := fun s =>
      (mfderiv 𝓘(Real, Real) I γ (s + t₀) (1 : Real) : E)
    let Z : (s : Real) → TangentSpace I (δ s) := fun _ => 0
    have hUeq (s : Real) : U s =
        (mfderiv 𝓘(Real, Real) I δ s (1 : Real) : E) :=
      (mfderiv_comp_add_apply (I := I) hγ t₀ s).symm
    have hUdiff (s : Real) :
        DifferentiableAt Real (chartRepAt (I := I) δ U s) s := by
      have hUfun : U = fun r =>
          (mfderiv 𝓘(Real, Real) I δ r (1 : Real) : E) :=
        funext hUeq
      rw [hUfun]
      exact velocity_chartRepAt_differentiableAt (I := I) δ hδ s
    have hZdiff (s : Real) :
        DifferentiableAt Real (chartRepAt (I := I) δ Z s) s := by
      have hrep : chartRepAt (I := I) δ Z s = fun _ => (0 : E) := by
        funext r
        simp [Z, chartRepAt]
      rw [hrep]
      fun_prop
    have hδC1 : ContMDiffOn 𝓘(Real, Real) I 1 δ (Set.Icc 0 1) :=
      (hδ.of_le (by simp)).contMDiffOn
    have hVcont : ContinuousOn
        (fun s => (TotalSpace.mk' E (δ s) (V s) : TangentBundle I M))
        (Set.Icc 0 1) :=
      sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
        (I := I) δ V hδC1 hVdiff
    have hWcont : ContinuousOn
        (fun s => (TotalSpace.mk' E (δ s) (W s) : TangentBundle I M))
        (Set.Icc 0 1) :=
      sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
        (I := I) δ W hδC1 hWdiff
    have hUcont : ContinuousOn
        (fun s => (TotalSpace.mk' E (δ s) (U s) : TangentBundle I M))
        (Set.Icc 0 1) :=
      sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
        (I := I) δ U hδC1 (fun s _ => hUdiff s)
    have hZcont : ContinuousOn
        (fun s => (TotalSpace.mk' E (δ s) (Z s) : TangentBundle I M))
        (Set.Icc 0 1) :=
      sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
        (I := I) δ Z hδC1 (fun s _ => hZdiff s)
    let A : Real → TangentBundle I M := fun s =>
      TotalSpace.mk' E (δ s)
        (riemannOp (LeviCivita (I := I) g) (δ s) (V s) (W s) (U s))
    let B : Real → TangentBundle I M := fun s =>
      TotalSpace.mk' E (δ s) (Z s)
    have hAcont : ContinuousOn A (Set.Icc 0 1) := by
      simpa only [A] using
        riemannOp_along_curve_continuousOn (I := I) g
          hδ.continuous.continuousOn hVcont hWcont hUcont
    have hBcont : ContinuousOn B (Set.Icc 0 1) := by
      simpa only [B] using hZcont
    have hAB : Set.EqOn A B (Set.Ioc 0 1) := by
      intro s hs
      have hgrad :=
        normalizedGradientRicciSoliton_gradFun_along_geodesic_eq_smul_velocity_of_scalar_eq_zero
          (I := I) h hx hδ hδgeo hδcrit s
      have hnull :=
        normalizedGradientRicciSoliton_riemannOp_gradFun_eq_zero_of_scalar_eq_zero
          (I := I) h hx (δ s) (V s) (W s)
      rw [hgrad,
        (riemannOp (LeviCivita (I := I) g) (δ s) (V s) (W s)).map_smul]
        at hnull
      have hsne : s / 2 ≠ 0 := div_ne_zero (ne_of_gt hs.1) (by norm_num)
      have hscoef : (s - 0) / 2 ≠ 0 := by simpa using hsne
      have hcurvVel :
          riemannOp (LeviCivita (I := I) g) (δ s) (V s) (W s)
            ((mfderiv 𝓘(Real, Real) I δ s (1 : Real) : E)) = 0 :=
        (smul_eq_zero.mp hnull).resolve_left hscoef
      have hcurv :
          riemannOp (LeviCivita (I := I) g) (δ s) (V s) (W s) (U s) = 0 := by
        rw [hUeq s]
        exact hcurvVel
      exact TotalSpace.ext rfl (heq_of_eq hcurv)
    have hclosure : Set.Icc (0 : Real) 1 ⊆ closure (Set.Ioc 0 1) := by
      rw [closure_Ioc (by norm_num : (0 : Real) ≠ 1)]
    have hABclosed : Set.EqOn A B (Set.Icc 0 1) :=
      hAB.of_subset_closure hAcont hBcont Set.Ioc_subset_Icc_self hclosure
    have htotal := hABclosed (show (0 : Real) ∈ Set.Icc 0 1 by norm_num)
    have hfiber :
        riemannOp (LeviCivita (I := I) g) (δ 0) (V 0) (W 0) (U 0) = 0 := by
      exact eq_of_heq (TotalSpace.mk.inj htotal).2
    have hzeroadd : (0 : Real) + t₀ = t₀ := zero_add t₀
    dsimp only [U, δ] at hfiber hV0 hW0
    rw [hzeroadd] at hfiber hV0 hW0
    rw [hV0, hW0] at hfiber
    exact hfiber
  · have hnull :=
      normalizedGradientRicciSoliton_riemannOp_gradFun_eq_zero_of_scalar_eq_zero
        (I := I) h hx (γ t) v w
    rw [normalizedGradientRicciSoliton_gradFun_along_geodesic_eq_smul_velocity_of_scalar_eq_zero
          (I := I) h hx hγ hgeo hcrit t,
      (riemannOp (LeviCivita (I := I) g) (γ t) v w).map_smul] at hnull
    have hcoef : (t - t₀) / 2 ≠ 0 :=
      div_ne_zero (sub_ne_zero.mpr ht) (by norm_num)
    exact (smul_eq_zero.mp hnull).resolve_left hcoef

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_expMapIntrinsic_mfderiv_inner_of_scalar_eq_zero
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    {p : M} (hcrit : gradFun (I := I) g f p = 0)
    (u v w : TangentSpace I p) :
    g.inner (expMapIntrinsic (I := I) g hEnorm p u)
        (mfderiv 𝓘(Real, E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) (u : E) (v : E))
        (mfderiv 𝓘(Real, E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) (u : E) (w : E)) =
      g.inner p v w := by
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hγ : ContMDiff 𝓘(Real, Real) I ∞ γ := by
    simpa only [γ] using intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hgeo : IsGeodesic (I := I) g γ := by
    intro t
    simpa only [γ] using intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u t
  have hcrit0 : gradFun (I := I) g f (γ 0) = 0 := by
    rw [show γ 0 = p from intrinsicGeodesic_zero (I := I) g hEnorm p u]
    exact hcrit
  apply expMapIntrinsic_mfderiv_inner_of_radial_curvature_zero
    (I := I) g hEnorm p u v w
  intro t ht X
  exact
    normalizedGradientRicciSoliton_riemannOp_velocity_eq_zero_along_geodesic_of_scalar_eq_zero
      (I := I) h hx hγ hgeo hcrit0 t X (curveVelocity (I := I) γ t)

end DifferentialGeometry.Geometry
