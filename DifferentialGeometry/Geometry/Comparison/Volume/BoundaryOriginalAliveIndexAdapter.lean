import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryShiftedJacobiIndexV2
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.IndexForm
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Minimizer

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold RealInnerProductSpace Topology
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

private theorem x124_adapter_deriv_affine
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (a ℓ t : ℝ) :
    deriv (fun q => f (a + ℓ * q)) t = ℓ • deriv f (a + ℓ * t) := by
  have houter : HasDerivAt f (deriv f (a + ℓ * t)) (a + ℓ * t) :=
    (hf.differentiable (by simp) (a + ℓ * t)).hasDerivAt
  have hinner : HasDerivAt (fun q : ℝ => a + ℓ * q) ℓ t := by
    convert (hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul ℓ) using 1
    · funext q
      simp only [Pi.add_apply, id_eq]
    · ring
  simpa [Function.comp_def] using (houter.scomp t hinner).deriv

private theorem x124_adapter_affine_indexForm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {R : ℝ → F →L[ℝ] F} {W V : ℝ → F} (a ℓ s t : ℝ) :
    DifferentialGeometry.Analysis.ODE.indexForm
        (fun q => ℓ ^ 2 • R (a + ℓ * q)) s t
        (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q))
        (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q)) =
      ℓ * DifferentialGeometry.Analysis.ODE.indexForm
        R (a + ℓ * s) (a + ℓ * t) W V W V := by
  have hpoint (q : ℝ) :
      DifferentialGeometry.Analysis.ODE.indexIntegrand
          (fun q => ℓ ^ 2 • R (a + ℓ * q))
          (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q))
          (fun q => W (a + ℓ * q)) (fun q => ℓ • V (a + ℓ * q)) q =
        ℓ ^ 2 * DifferentialGeometry.Analysis.ODE.indexIntegrand
          R W V W V (a + ℓ * q) := by
    simp only [DifferentialGeometry.Analysis.ODE.indexIntegrand, smul_apply,
      real_inner_smul_left, real_inner_smul_right]
    ring
  unfold DifferentialGeometry.Analysis.ODE.indexForm
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  calc
    ℓ ^ 2 * (∫ q in s..t, DifferentialGeometry.Analysis.ODE.indexIntegrand
        R W V W V (a + ℓ * q)) =
        ℓ * (ℓ * ∫ q in s..t, DifferentialGeometry.Analysis.ODE.indexIntegrand
          R W V W V (a + ℓ * q)) := by ring
    _ = ℓ * ∫ q in a + ℓ * s..a + ℓ * t,
        DifferentialGeometry.Analysis.ODE.indexIntegrand R W V W V q := by
      have hchange := intervalIntegral.smul_integral_comp_add_mul
        (a := s) (b := t)
        (fun q => DifferentialGeometry.Analysis.ODE.indexIntegrand R W V W V q) ℓ a
      simpa only [smul_eq_mul] using congrArg (fun x : ℝ => ℓ * x) hchange

/-- The coefficient index form in an actual parallel normal frame is nonnegative on a
minimizing segment of the genuine interior metric. -/
theorem boundaryOriginal_actualSegment_index_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {J : ModelWithCorners ℝ E E} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold J ∞ N] [T2Space N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric J N) (Γ : ℝ → N) (L : ℝ)
    (hL : 0 ≤ L) (hΓ : ContMDiff 𝓘(ℝ, ℝ) J ∞ Γ)
    (hgeo : IsGeodesicOn (I := J) g Γ (Icc 0 L))
    (hmin : ∀ η : ℝ → N, ContMDiffOn 𝓘(ℝ) J 1 η (Icc 0 L) →
      η 0 = Γ 0 → η L = Γ L →
      arcLength (I := J) g Γ 0 L ≤ arcLength (I := J) g η 0 L)
    (hUnit : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (Γ t) (mfderiv 𝓘(ℝ) J Γ t 1) (mfderiv 𝓘(ℝ) J Γ t 1) = 1)
    (F : ι → ∀ t : ℝ, TangentSpace J (Γ t))
    (hFbundle : ∀ i, ContMDiff 𝓘(ℝ, ℝ) J.tangent ∞
      (fun t => TotalSpace.mk' E (Γ t) (F i t)))
    (hFdiff : ∀ i t, t ∈ Icc (0 : ℝ) L →
      DifferentiableAt ℝ (chartRepAt (I := J) Γ (F i) t) t)
    (hFpar : ∀ i t, t ∈ Icc (0 : ℝ) L →
      covDerivAlong (I := J) g Γ (F i) t = 0)
    (hFON : ∀ t, t ∈ Icc (0 : ℝ) L → ∀ i j,
      g.inner (Γ t) (F i t) (F j t) = if i = j then 1 else 0)
    (hFperp : ∀ t, t ∈ Icc (0 : ℝ) L → ∀ i,
      g.inner (Γ t) (F i t) (mfderiv 𝓘(ℝ) J Γ t 1) = 0)
    (Z : ℝ → EuclideanSpace ℝ ι) (hZ : ContDiff ℝ ∞ Z)
    (hZ0 : Z 0 = 0) (hZL : Z L = 0) :
    0 ≤ DifferentialGeometry.Analysis.ODE.indexForm
      (perpCurvOp (I := J) g Γ F) 0 L Z (deriv Z) Z (deriv Z) := by
  let V : ∀ t : ℝ, TangentSpace J (Γ t) :=
    fun t => perpFrameLift (I := J) F Z t
  have hVbundle : ContMDiff 𝓘(ℝ, ℝ) J.tangent (8 : ℕ)
      (fun t => TotalSpace.mk' E (Γ t) (V t)) :=
    (perpLift_smooth (I := J) hΓ F Z hZ hFbundle).of_le
      (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hVperp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      g.inner (Γ t) (V t) (mfderiv 𝓘(ℝ) J Γ t 1) = 0 :=
    perpLift_perp (I := J) g F Z t (mfderiv 𝓘(ℝ) J Γ t 1)
      (fun i => hFperp t ht i)
  have hgeomIndex := indexForm_nonneg_of_minimising_geodesic (I := J) g Γ L V hL
    hVbundle hgeo hmin hUnit hVperp
      (perpLift_zero (I := J) F Z 0 hZ0)
      (perpLift_zero (I := J) F Z L hZL)
  have hindexEq : indexForm (I := J) g Γ 0 L V V =
      DifferentialGeometry.Analysis.ODE.indexForm
        (perpCurvOp (I := J) g Γ F) 0 L Z (deriv Z) Z (deriv Z) := by
    exact perpLift_indexForm (I := J) g Γ F Z Z 0 L
      (fun t _ => (hZ.differentiable (by simp)).differentiableAt)
      (fun t _ => (hZ.differentiable (by simp)).differentiableAt)
      (fun i t ht => hFdiff i t (by simpa only [uIcc_of_le hL] using ht))
      (fun i t ht => hFpar i t (by simpa only [uIcc_of_le hL] using ht))
      (fun t ht i j => hFON t (by simpa only [uIcc_of_le hL] using ht) i j)
  rw [← hindexEq]
  exact hgeomIndex

/-- A physical minimizing segment shifted by `a > 0` supplies the geometric index inequality
for the same pole-ray coefficient frame on `[a, 1]`. -/
theorem boundaryOriginal_shifted_actual_index_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {J : ModelWithCorners ℝ E E} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold J ∞ N] [T2Space N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric J N) (Γ : ℝ → N)
    (R : ℝ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (F : ι → ∀ t : ℝ, TangentSpace J (Γ t)) (a : ℝ)
    (ha : a ∈ Ioo (0 : ℝ) 1)
    (hΓ : ContMDiff 𝓘(ℝ, ℝ) J ∞ Γ)
    (hgeo : IsGeodesicOn (I := J) g Γ (Icc 0 (1 - a)))
    (hmin : ∀ η : ℝ → N, ContMDiffOn 𝓘(ℝ) J 1 η (Icc 0 (1 - a)) →
      η 0 = Γ 0 → η (1 - a) = Γ (1 - a) →
      arcLength (I := J) g Γ 0 (1 - a) ≤ arcLength (I := J) g η 0 (1 - a))
    (hUnit : ∀ t ∈ Icc (0 : ℝ) (1 - a),
      g.inner (Γ t) (mfderiv 𝓘(ℝ) J Γ t 1) (mfderiv 𝓘(ℝ) J Γ t 1) = 1)
    (hFbundle : ∀ i, ContMDiff 𝓘(ℝ, ℝ) J.tangent ∞
      (fun t => TotalSpace.mk' E (Γ t) (F i t)))
    (hFdiff : ∀ i t, t ∈ Icc (0 : ℝ) (1 - a) →
      DifferentiableAt ℝ (chartRepAt (I := J) Γ (F i) t) t)
    (hFpar : ∀ i t, t ∈ Icc (0 : ℝ) (1 - a) →
      covDerivAlong (I := J) g Γ (F i) t = 0)
    (hFON : ∀ t, t ∈ Icc (0 : ℝ) (1 - a) → ∀ i j,
      g.inner (Γ t) (F i t) (F j t) = if i = j then 1 else 0)
    (hFperp : ∀ t, t ∈ Icc (0 : ℝ) (1 - a) → ∀ i,
      g.inner (Γ t) (F i t) (mfderiv 𝓘(ℝ) J Γ t 1) = 0)
    (hRmatch : ∀ t, t ∈ Icc (0 : ℝ) (1 - a) →
      perpCurvOp (I := J) g Γ F t = R (a + t))
    (Z : ℝ → EuclideanSpace ℝ ι) (hZ : ContDiff ℝ ∞ Z)
    (hZa : Z a = 0) (hZ1 : Z 1 = 0) :
    0 ≤ DifferentialGeometry.Analysis.ODE.indexForm R a 1 Z (deriv Z) Z (deriv Z) := by
  let W : ℝ → EuclideanSpace ℝ ι := fun t => Z (a + t)
  have hW : ContDiff ℝ ∞ W := by
    exact hZ.comp (contDiff_const.add contDiff_id)
  have hW0 : W 0 = 0 := by simpa [W] using hZa
  have hWL : W (1 - a) = 0 := by
    change Z (a + (1 - a)) = 0
    rw [show a + (1 - a) = 1 by ring, hZ1]
  have hcurveIndex := boundaryOriginal_actualSegment_index_nonneg g Γ (1 - a)
    (sub_nonneg.mpr ha.2.le) hΓ hgeo hmin hUnit F hFbundle hFdiff hFpar hFON hFperp
    W hW hW0 hWL
  have hderiv (t : ℝ) : deriv W t = deriv Z (a + t) := by
    have h := x124_adapter_deriv_affine hZ a 1 t
    simpa only [W, one_smul, one_mul] using h
  have hframeCurveIndex :
      DifferentialGeometry.Analysis.ODE.indexForm
        (perpCurvOp (I := J) g Γ F) 0 (1 - a) W (deriv W) W (deriv W) =
      DifferentialGeometry.Analysis.ODE.indexForm
        (fun t => R (a + t)) 0 (1 - a) W (fun t => deriv Z (a + t))
          W (fun t => deriv Z (a + t)) := by
    unfold DifferentialGeometry.Analysis.ODE.indexForm
    have hderivEq : deriv W = fun t => deriv Z (a + t) := funext hderiv
    rw [hderivEq]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) (1 - a) := by
      rwa [uIcc_of_le (sub_nonneg.mpr ha.2.le)] at ht
    simp only [DifferentialGeometry.Analysis.ODE.indexIntegrand]
    rw [hRmatch t ht']
  have htranslate := x124_adapter_affine_indexForm
    (a := a) (ℓ := 1) (s := 0) (t := 1 - a) (R := R) (W := Z) (V := deriv Z)
  have htranslate' :
      DifferentialGeometry.Analysis.ODE.indexForm
        (fun t => R (a + t)) 0 (1 - a) W (fun t => deriv Z (a + t))
          W (fun t => deriv Z (a + t)) =
        DifferentialGeometry.Analysis.ODE.indexForm R a 1 Z (deriv Z) Z (deriv Z) := by
    simpa [W, one_pow, one_smul, zero_add, one_mul, sub_add_cancel] using htranslate
  calc
    0 ≤ DifferentialGeometry.Analysis.ODE.indexForm
        (perpCurvOp (I := J) g Γ F) 0 (1 - a) W (deriv W) W (deriv W) :=
      hcurveIndex
    _ = DifferentialGeometry.Analysis.ODE.indexForm
        (fun t => R (a + t)) 0 (1 - a) W (fun t => deriv Z (a + t))
          W (fun t => deriv Z (a + t)) := hframeCurveIndex
    _ = DifferentialGeometry.Analysis.ODE.indexForm R a 1 Z (deriv Z) Z (deriv Z) :=
      htranslate'

/-- On an actual interior ray, a Jacobi coefficient field cannot vanish again before a later
positive-start minimizing segment whose geometric index form is nonnegative. The coefficient
operator is the curvature operator of the same ray in its same parallel frame. -/
theorem boundaryOriginal_alive_noConj_of_actual_index
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {J : ModelWithCorners ℝ E E} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold J ∞ N] [T2Space N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric J N) (γ : ℝ → N)
    (F : ι → ∀ t : ℝ, TangentSpace J (γ t))
    (R : ℝ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    {y v : ℝ → EuclideanSpace ℝ ι} (c : ℝ)
    (hFdiff : ∀ i t, 0 < t →
      DifferentiableAt ℝ (chartRepAt (I := J) γ (F i) t) t)
    (hFpar : ∀ i t, 0 < t →
      covDerivAlong (I := J) g γ (F i) t = 0)
    (hFON : ∀ t, 0 < t → ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then 1 else 0)
    (hFperp : ∀ t, 0 < t → ∀ i,
      g.inner (γ t) (F i t) (curveVelocity (I := J) γ t) = 0)
    (hRmatch : ∀ t, 0 < t →
      R t = perpCurvOp (I := J) g γ F t)
    (hRcont : ContinuousOn R (Icc (0 : ℝ) 1))
    (hRsym : ∀ s, ∀ x x' : EuclideanSpace ℝ ι,
      ⟪R s x, x'⟫ = ⟪x, R s x'⟫)
    (hsol : IsJacobiFieldOn R 0 1 y v)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hy : ContDiff ℝ ∞ y) (hya : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0)
    (hactualIndex : ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
      ∀ Z : ℝ → EuclideanSpace ℝ ι, ContDiff ℝ ∞ Z → Z a = 0 → Z 1 = 0 →
      0 ≤ indexForm (I := J) g γ a 1
        (perpFrameLift (I := J) F Z)
        (perpFrameLift (I := J) F Z)) : False := by
  have _hFperp := hFperp
  obtain ⟨a, ha, ha2, Z, hZ, hZa, hZ1, hnegative⟩ :=
    IsJacobiFieldOn.exists_contDiff_indexForm_neg_shifted_actual
      hsol hc hRcont hRsym hy hya hyc hne
  have ha1 : a < 1 := by nlinarith
  have hnonneg := hactualIndex a ⟨ha, ha1⟩ Z hZ hZa hZ1
  have hframeIndex := perpLift_indexForm (I := J) g γ F Z Z a 1
    (fun t ht => by
      have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha1.le] at ht
      exact (hZ.differentiable (by simp)).differentiableAt)
    (fun t ht => by
      have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha1.le] at ht
      exact (hZ.differentiable (by simp)).differentiableAt)
    (fun i t ht => by
      have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha1.le] at ht
      exact hFdiff i t (lt_of_lt_of_le ha ht'.1))
    (fun i t ht => by
      have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha1.le] at ht
      exact hFpar i t (lt_of_lt_of_le ha ht'.1))
    (fun t ht i j => by
      have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha1.le] at ht
      exact hFON t (lt_of_lt_of_le ha ht'.1) i j)
  have hcurv : ∀ s ∈ Icc a 1, R s = perpCurvOp (I := J) g γ F s := by
    intro s hs
    exact hRmatch s (lt_of_lt_of_le ha hs.1)
  have hrewrite : indexForm R a 1 Z (deriv Z) Z (deriv Z) =
      indexForm (perpCurvOp (I := J) g γ F) a 1 Z (deriv Z) Z (deriv Z) := by
    unfold DifferentialGeometry.Analysis.ODE.indexForm
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc a 1 := by rwa [uIcc_of_le ha1.le] at hs
    unfold DifferentialGeometry.Analysis.ODE.indexIntegrand
    rw [hcurv s hs']
  rw [hrewrite] at hnegative
  rw [hframeIndex] at hnonneg
  exact (not_lt_of_ge hnonneg) hnegative

/-- The shifted index contradiction can be fed by genuine minimizing positive-start segments.
The segment curve and its parallel normal frame carry the actual interior metric index form. -/
theorem boundaryOriginal_alive_noConj_of_shifted_minimizers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {J : ModelWithCorners ℝ E E} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold J ∞ N] [T2Space N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric J N) (γ : ℝ → N)
    (F : ι → ∀ t : ℝ, TangentSpace J (γ t))
    (R : ℝ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    {y v : ℝ → EuclideanSpace ℝ ι} (c : ℝ)
    (hFdiff : ∀ i t, 0 < t →
      DifferentiableAt ℝ (chartRepAt (I := J) γ (F i) t) t)
    (hFpar : ∀ i t, 0 < t →
      covDerivAlong (I := J) g γ (F i) t = 0)
    (hFON : ∀ t, 0 < t → ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then 1 else 0)
    (hFperp : ∀ t, 0 < t → ∀ i,
      g.inner (γ t) (F i t) (curveVelocity (I := J) γ t) = 0)
    (hRmatch : ∀ t, 0 < t → R t = perpCurvOp (I := J) g γ F t)
    (hRcont : ContinuousOn R (Icc (0 : ℝ) 1))
    (hRsym : ∀ s, ∀ x x' : EuclideanSpace ℝ ι,
      ⟪R s x, x'⟫ = ⟪x, R s x'⟫)
    (hsol : IsJacobiFieldOn R 0 1 y v)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hy : ContDiff ℝ ∞ y) (hya : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0)
    (hminSegments : ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
      ∃ Γ : ℝ → N,
        ContMDiff 𝓘(ℝ, ℝ) J ∞ Γ ∧
        (∀ t ∈ Icc (0 : ℝ) (1 - a), Γ t = γ (a + t)) ∧
        IsGeodesicOn (I := J) g Γ (Icc 0 (1 - a)) ∧
        (∀ η : ℝ → N, ContMDiffOn 𝓘(ℝ) J 1 η (Icc 0 (1 - a)) →
          η 0 = Γ 0 → η (1 - a) = Γ (1 - a) →
          arcLength (I := J) g Γ 0 (1 - a) ≤ arcLength (I := J) g η 0 (1 - a)) ∧
        (∀ t ∈ Icc (0 : ℝ) (1 - a),
          g.inner (Γ t) (mfderiv 𝓘(ℝ) J Γ t 1)
            (mfderiv 𝓘(ℝ) J Γ t 1) = 1) ∧
        ∃ F' : ι → ∀ t : ℝ, TangentSpace J (Γ t),
          (∀ i, ContMDiff 𝓘(ℝ, ℝ) J.tangent ∞
            (fun t => TotalSpace.mk' E (Γ t) (F' i t))) ∧
          (∀ i t, t ∈ Icc (0 : ℝ) (1 - a) →
            DifferentiableAt ℝ (chartRepAt (I := J) Γ (F' i) t) t) ∧
          (∀ i t, t ∈ Icc (0 : ℝ) (1 - a) →
            covDerivAlong (I := J) g Γ (F' i) t = 0) ∧
          (∀ t, t ∈ Icc (0 : ℝ) (1 - a) → ∀ i j,
            g.inner (Γ t) (F' i t) (F' j t) = if i = j then 1 else 0) ∧
          (∀ t, t ∈ Icc (0 : ℝ) (1 - a) → ∀ i,
            g.inner (Γ t) (F' i t) (mfderiv 𝓘(ℝ) J Γ t 1) = 0) ∧
          (∀ t, t ∈ Icc (0 : ℝ) (1 - a) →
            perpCurvOp (I := J) g Γ F' t = R (a + t))) : False := by
  have hactualIndex : ∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
      ∀ Z : ℝ → EuclideanSpace ℝ ι, ContDiff ℝ ∞ Z → Z a = 0 → Z 1 = 0 →
      0 ≤ indexForm (I := J) g γ a 1
        (perpFrameLift (I := J) F Z) (perpFrameLift (I := J) F Z) := by
    intro a ha Z hZ hZa hZ1
    obtain ⟨Γ, hΓ, _hΓeq, hgeo, hmin, hUnit, F', hFbundle', hFdiff', hFpar',
      hFON', hFperp', hRmatch'⟩ := hminSegments a ha
    have hcoef := boundaryOriginal_shifted_actual_index_nonneg
      g Γ R F' a ha hΓ hgeo hmin hUnit hFbundle' hFdiff' hFpar' hFON' hFperp'
      hRmatch' Z hZ hZa hZ1
    have hindexEq : indexForm (I := J) g γ a 1
        (perpFrameLift (I := J) F Z) (perpFrameLift (I := J) F Z) =
      DifferentialGeometry.Analysis.ODE.indexForm
        (perpCurvOp (I := J) g γ F) a 1 Z (deriv Z) Z (deriv Z) := by
      exact perpLift_indexForm (I := J) g γ F Z Z a 1
        (fun t _ => (hZ.differentiable (by simp)).differentiableAt)
        (fun t _ => (hZ.differentiable (by simp)).differentiableAt)
        (fun i t ht => by
          have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha.2.le] at ht
          exact hFdiff i t (lt_of_lt_of_le ha.1 ht'.1))
        (fun i t ht => by
          have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha.2.le] at ht
          exact hFpar i t (lt_of_lt_of_le ha.1 ht'.1))
        (fun t ht i j => by
          have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha.2.le] at ht
          exact hFON t (lt_of_lt_of_le ha.1 ht'.1) i j)
    have hRtoActual : DifferentialGeometry.Analysis.ODE.indexForm
        R a 1 Z (deriv Z) Z (deriv Z) =
      DifferentialGeometry.Analysis.ODE.indexForm
        (perpCurvOp (I := J) g γ F) a 1 Z (deriv Z) Z (deriv Z) := by
      unfold DifferentialGeometry.Analysis.ODE.indexForm
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Icc a 1 := by rwa [uIcc_of_le ha.2.le] at ht
      unfold DifferentialGeometry.Analysis.ODE.indexIntegrand
      rw [hRmatch t (lt_of_lt_of_le ha.1 ht'.1)]
    rw [hindexEq, ← hRtoActual]
    exact hcoef
  exact boundaryOriginal_alive_noConj_of_actual_index g γ F R c hFdiff hFpar hFON
    hFperp hRmatch hRcont hRsym hsol hc hy hya hyc hne hactualIndex

private theorem boundaryOriginalAdapter_infty_ne_zero :
    (∞ : WithTop ℕ∞) ≠ 0 := by simp

/-- The same index contradiction, explicitly over the intrinsic interior and the original
corner metric. The pole limit is in the original manifold, while curvature and index are taken
from `boundaryInteriorAtlasMetric g`, the true restriction of that metric. -/
theorem boundaryOriginal_cornerPole_noConj_of_actual_index
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (p : M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryOriginalAdapter_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    I.IsBoundaryPoint p →
    ∀ (γ : ℝ → U)
      (F : Fin 2 → ∀ t, TangentSpace (𝓘(ℝ, E)) (γ t))
      (R : ℝ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      {y v : ℝ → EuclideanSpace ℝ (Fin 2)} (c : ℝ),
      Tendsto (fun t : ℝ => ((γ t : U) : M)) (𝓝[>] (0 : ℝ)) (𝓝 p) →
      (∀ i t, 0 < t → DifferentiableAt ℝ
        (chartRepAt (I := 𝓘(ℝ, E)) γ (F i) t) t) →
      (∀ i t, 0 < t → covDerivAlong (I := 𝓘(ℝ, E)) k γ (F i) t = 0) →
      (∀ t, 0 < t → ∀ i j,
        k.inner (γ t) (F i t) (F j t) = if i = j then 1 else 0) →
      (∀ t, 0 < t → ∀ i,
        k.inner (γ t) (F i t) (curveVelocity (I := 𝓘(ℝ, E)) γ t) = 0) →
      (∀ t, 0 < t → R t = perpCurvOp (I := 𝓘(ℝ, E)) k γ F t) →
      ContinuousOn R (Icc (0 : ℝ) 1) →
      (∀ s, ∀ x x' : EuclideanSpace ℝ (Fin 2),
        ⟪R s x, x'⟫ = ⟪x, R s x'⟫) →
      IsJacobiFieldOn R 0 1 y v → c ∈ Ioo (0 : ℝ) 1 →
      ContDiff ℝ ∞ y → y 0 = 0 → y c = 0 →
      (∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0) →
      (∀ a : ℝ, a ∈ Ioo (0 : ℝ) 1 →
        ∀ Z : ℝ → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ Z →
          Z a = 0 → Z 1 = 0 →
          0 ≤ indexForm (I := 𝓘(ℝ, E)) k γ a 1
            (perpFrameLift (I := 𝓘(ℝ, E)) F Z)
            (perpFrameLift (I := 𝓘(ℝ, E)) F Z)) → False := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    boundaryOriginalAdapter_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro hp γ F R y v c hPole hFdiff hFpar hFON hFperp hRmatch hRcont hRsym
    hsol hc hy hya hyc hne hactualIndex
  have _hboundary := hp
  have _hlimit := hPole
  exact boundaryOriginal_alive_noConj_of_actual_index k γ F R c
    hFdiff hFpar hFON hFperp hRmatch hRcont hRsym hsol hc hy hya hyc hne hactualIndex

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
