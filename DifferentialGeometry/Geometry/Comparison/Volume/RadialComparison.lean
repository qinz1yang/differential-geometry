import DifferentialGeometry.Geometry.Comparison.Volume.LocalRicci
import DifferentialGeometry.Geometry.Comparison.Volume.ModelRiccati
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.IntrinsicLocal
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Pole

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Volume
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] [T2Space M] in
theorem hasDerivAt_modelDensityRatio
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (K t : ℝ) (d : ℕ)
    (ht : modelRadiusAdmissible K t)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hpos : 0 < (curveGram (I := I) g γ V t).det)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    HasDerivAt
      (fun r => curveDensity (I := I) g γ V r / modelDensity K d r)
      ((curveDensity (I := I) g γ V t / modelDensity K d t) *
        (curveMean (I := I) g γ V t - modelMeanCurv K d t)) t := by
  have hden : HasDerivAt (curveDensity (I := I) g γ V)
      (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t) t := by
    refine (hasDerivAt_symmDen (I := I) hn g γ V t hγ hVdiff hpos hW).congr_deriv ?_
    rw [curveMean, curveShape]
  have hmodel : modelDensity K d t ≠ 0 := (modelDensity_pos ht).ne'
  have h := hden.fun_div (hasDerivAt_modelDensity K d t) hmodel
  refine h.congr_deriv ?_
  rw [modelDensityDeriv_eq_mean ht]
  field_simp [hmodel]

omit [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] [T2Space M] in
theorem curveModelRatio_anti
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (K b : ℝ) (d : ℕ)
    (hadm : ∀ t ∈ Ioo (0 : ℝ) b, modelRadiusAdmissible K t)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hLI : ∀ t ∈ Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t)
    (hW : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0)
    (hmean : ∀ t ∈ Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤ modelMeanCurv K d t) :
    AntitoneOn
      (fun t => curveDensity (I := I) g γ V t / modelDensity K d t)
      (Ioo (0 : ℝ) b) := by
  let R : ℝ → ℝ := fun t =>
    curveDensity (I := I) g γ V t / modelDensity K d t
  have hR : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt R
        (R t * (curveMean (I := I) g γ V t - modelMeanCurv K d t)) t := by
    intro t ht
    simpa only [R] using
      hasDerivAt_modelDensityRatio (I := I) hn g γ V K t d (hadm t ht)
        (hγ t ht) (hVdiff t ht)
        (curveGram_det_pos (I := I) g γ V t (hLI t ht)) (hW t ht)
  have hRpos : ∀ t ∈ Ioo (0 : ℝ) b, 0 < R t := by
    intro t ht
    exact div_pos (curveDensity_pos (I := I) g γ V t (hLI t ht))
      (modelDensity_pos (hadm t ht))
  have hdiff : DifferentiableOn ℝ R (Ioo (0 : ℝ) b) := by
    intro t ht
    exact (hR t ht).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) b,
      R t * (curveMean (I := I) g γ V t - modelMeanCurv K d t) ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos (hRpos t ht).le
      (sub_nonpos.mpr (hmean t ht))
  have hanti : AntitoneOn R (Ioo (0 : ℝ) b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 b) hdiff.continuousOn ?_ ?_
    · simpa using hdiff
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) b := by simpa using ht
      rw [(hR t ht').deriv]
      exact hderiv t ht'
  simpa only [R] using hanti

omit [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
theorem mean_riccati_const_on
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t K a : ℝ)
    (u : TangentSpace I (γ t))
    (huvel : curveVelocity (I := I) γ t = u)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (ha : 0 < a)
    (hu : g.inner (γ t) u u = a ^ 2)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hDVperp : ∀ i,
      g.inner (γ t) u (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t)
    (e : Fin (Module.finrank ℝ E - 1) → TangentSpace I (γ t))
    (hON : ∀ i j, g.inner (γ t) (e i) (e j) = if i = j then 1 else 0)
    (hEperp : ∀ i, g.inner (γ t) (e i) u = 0)
    (hRic :
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) *
          g.inner (γ t) u u ≤
        ricciTensor (I := I) g (γ t) u u) :
    HasDerivAt (curveMean (I := I) g γ V)
        (-Matrix.trace ((curveGram (I := I) g γ V t)⁻¹ *
            curveCurvGram (I := I) g γ V t) -
          Matrix.trace ((curveShape (I := I) g γ V t) ^ 2)) t ∧
      -Matrix.trace ((curveGram (I := I) g γ V t)⁻¹ *
          curveCurvGram (I := I) g γ V t) -
        Matrix.trace ((curveShape (I := I) g γ V t) ^ 2) ≤
      -((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K * a ^ 2 -
        (curveMean (I := I) g γ V t) ^ 2 /
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
  have hupos : 0 < g.inner (γ t) u u := by
    rw [hu]
    positivity
  have hderiv := hasDerivAt_mean_perp (I := I) hn g γ V t u hcard hupos
    hVperp hDVperp hγ hVdiff hDVdiff hLI hW hJ
  refine ⟨hderiv, ?_⟩
  have hcurv := curvTrace_eq_ricci (I := I) g γ V t u huvel hcard hupos
    hVperp hLI e hON hEperp
  have hshape := mean_sq_le_shape (I := I) g γ V t u hcard hupos hVperp
    hDVperp hLI hW e hON hEperp
  have hric := hRic
  rw [hu] at hric
  have hdR : (0 : ℝ) < ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hshapeDiv :
      (curveMean (I := I) g γ V t) ^ 2 /
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) ≤
        Matrix.trace ((curveShape (I := I) g γ V t) ^ 2) := by
    rw [div_le_iff₀ hdR]
    simpa only [mul_comm] using hshape
  rw [hcurv]
  nlinarith

omit [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
theorem curveMean_le_model_on
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (K a b : ℝ)
    (ha : 0 < a)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hadm : ∀ t ∈ Ioo (0 : ℝ) b,
      modelRadiusAdmissible (K * a ^ 2) t)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) b,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = a ^ 2)
    (hVperp : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0)
    (hDVperp : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : ∀ t ∈ Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t)
    (hW : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) b,
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) *
          g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) ≤
        ricciTensor (I := I) g (γ t)
          (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t))
    (hRatioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          modelDensity (K * a ^ 2) (Module.finrank ℝ E - 1) t) :
    ∀ t ∈ Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤
        modelMeanCurv (K * a ^ 2) (Module.finrank ℝ E - 1) t := by
  let d : ℕ := Module.finrank ℝ E - 1
  let m' : ℝ → ℝ := fun t =>
    -Matrix.trace ((curveGram (I := I) g γ V t)⁻¹ *
        curveCurvGram (I := I) g γ V t) -
      Matrix.trace ((curveShape (I := I) g γ V t) ^ 2)
  have hm : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt (curveMean (I := I) g γ V) (m' t) t := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    exact (mean_riccati_const_on (I := I) hn g γ V t K a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp (hRic t ht)).1
  have hmle : ∀ t ∈ Ioo (0 : ℝ) b,
      m' t ≤ -((d : ℝ) * (K * a ^ 2)) -
        curveMean (I := I) g γ V t ^ 2 / (d : ℝ) := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    have h := (mean_riccati_const_on (I := I) hn g γ V t K a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp (hRic t ht)).2
    change m' t ≤ -((d : ℝ) * (K * a ^ 2)) -
      curveMean (I := I) g γ V t ^ 2 / (d : ℝ)
    simpa only [m', d] using (show
      -Matrix.trace ((curveGram (I := I) g γ V t)⁻¹ *
          curveCurvGram (I := I) g γ V t) -
        Matrix.trace ((curveShape (I := I) g γ V t) ^ 2) ≤
          -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (K * a ^ 2)) -
            curveMean (I := I) g γ V t ^ 2 /
              ((Module.finrank ℝ E - 1 : ℕ) : ℝ) by
        convert h using 1
        ring)
  let R : ℝ → ℝ := fun t =>
    curveDensity (I := I) g γ V t / modelDensity (K * a ^ 2) d t
  have hR : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt R
        (R t * (curveMean (I := I) g γ V t -
          modelMeanCurv (K * a ^ 2) d t)) t := by
    intro t ht
    simpa only [R, d] using
      hasDerivAt_modelDensityRatio (I := I) hn g γ V (K * a ^ 2) t d
        (hadm t ht) (hγ t ht) (hVdiff t ht)
        (curveGram_det_pos (I := I) g γ V t (hLI t ht)) (hW t ht)
  have hRpos : ∀ t ∈ Ioo (0 : ℝ) b, 0 < R t := by
    intro t ht
    exact div_pos (curveDensity_pos (I := I) g γ V t (hLI t ht))
      (modelDensity_pos (hadm t ht))
  apply mean_le_model_of_ratio hd hadm hm hmle hR hRpos
  simpa only [R, d] using hRatioLower

omit [T2Space (TangentBundle I M)] in
theorem intrinsicJacobi_linearIndependent_of_not_conj
    {ι : Type*}
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (v : ι → TangentSpace I p)
    (hv : LinearIndependent ℝ v) {t : ℝ} (ht : t ≠ 0)
    (hno : ¬ IsConjVec (I := I) g hEnorm p (t • (u : E))) :
    LinearIndependent ℝ fun i =>
      intrinsicJacobi (I := I) g hEnorm p u (v i) t := by
  let L : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z))
      (t • (u : E))
  have hLinj : Function.Injective L := by
    unfold IsConjVec at hno
    exact Classical.not_not.mp hno
  let a : ℝˣ := Units.mk0 t ht
  let as : ι → ℝˣ := fun _ => a
  have hscaled : LinearIndependent ℝ fun i => t • v i := by
    have has : as • v = fun i => t • v i := by
      funext i
      rfl
    rw [← has]
    exact hv.units_smul as
  have hmapped : LinearIndependent ℝ fun i => L (t • (v i : E)) :=
    hscaled.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hLinj)
  have hfield :
      (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i) t) =
        fun i => L (t • (v i : E)) := by
    funext i
    unfold intrinsicJacobi
    dsimp only [L]
    apply eq_of_heq
    exact heq_of_eq
      (intrinsic_jacobi_at (I := I) g hEnorm p (u : E) (v i : E) t)
  rw [hfield]
  exact hmapped

omit [T2Space (TangentBundle I M)] in
theorem modelPoleLimit
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (K : ℝ)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto
      (fun t => curveDensity (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        modelDensity K (Module.finrank ℝ E - 1) t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcd :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveDensity_pole
      (I := I) g hEnorm p u v hON
  have hmd : Tendsto
      (fun t => modelDensity K (Module.finrank ℝ E - 1) t /
        t ^ (Module.finrank ℝ E - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [modelDensity, div_pow, one_pow] using
      (modelRadiusRatio_tendsto K).pow (Module.finrank ℝ E - 1)
  have hcombine := hcd.div hmd one_ne_zero
  rw [div_one] at hcombine
  refine hcombine.congr' ?_
  filter_upwards [eventually_modelRadiusAdmissible K] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have htpow : 0 < t ^ (Module.finrank ℝ E - 1) := pow_pos ht0 _
  have hmdpos : 0 < modelDensity K (Module.finrank ℝ E - 1) t :=
    modelDensity_pos ht
  simp only [Pi.div_apply]
  field_simp [htpow.ne', hmdpos.ne']

omit [T2Space (TangentBundle I M)] in
theorem intrModelRatioOfFrame_on
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (K b : ℝ)
    (hunit : g.inner p u u = 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hadm : ∀ t ∈ Set.Ioo (0 : ℝ) b, modelRadiusAdmissible K t)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hno : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic :
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      ∀ t ∈ Set.Ioo (0 : ℝ) b,
        (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
    AntitoneOn
      (fun t => curveDensity (I := I) g γ V t /
        modelDensity K (Module.finrank ℝ E - 1) t)
      (Set.Ioo (0 : ℝ) b) := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  have hu : 0 < g.inner p u u := by rw [hunit]; norm_num
  have hv : LinearIndependent ℝ v :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.linIndep_of_ortho
      (I := I) g p v hON
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i =>
    intrinsicJacobi (I := I) g hEnorm p u (v i)
  have hγInf : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hγ : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞) γ t := by
    intro t ht
    exact hγInf.contMDiffAt.of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hspeed : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = (1 : ℝ) ^ 2 := by
    intro t ht
    calc
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) = g.inner p u u := by
        change g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p u) t 1)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p u) t 1) =
            g.inner p u u
        exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
      _ = (1 : ℝ) ^ 2 := by rw [hunit]; norm_num
  have hVdiff : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) t).1
  have hDVdiff : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) t).2
  have hVperp : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicJacobi_perp_ne
        (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
  have hDVperp : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicJacobi_dperp
        (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
  have hLI : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t := by
    intro t ht
    simpa only [γ, V] using
      intrinsicJacobi_linearIndependent_of_not_conj
        (I := I) g hEnorm p u v hv ht.1.ne' (hno t ht)
  have hW : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
    intro t ht i j
    exact wronskian_eq_zero (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ (V i) (V j) (hγInf.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) s).1)
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v j) s).1)
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) s).2)
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v j) s).2)
      (fun s _ => by
        change IsJacobiAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (intrinsicJacobi (I := I) g hEnorm p u (v i)) s
        exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) s)
      (fun s _ => by
        change IsJacobiAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (intrinsicJacobi (I := I) g hEnorm p u (v j)) s
        exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v j : E) s)
      (by simp [V]) (by simp [V]) t ⟨ht.1.le, ht.2.le⟩
  have hJ : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t := by
    intro t ht i
    change IsJacobiAt (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p u)
      (intrinsicJacobi (I := I) g hEnorm p u (v i)) t
    exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) t
  have hRatio : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t / modelDensity K d t := by
    have hlim := modelPoleLimit (I := I) g hEnorm p u K v hON
    have hevent := hlim.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    refine ⟨1 / 2, by norm_num, ?_⟩
    filter_upwards [hevent] with t ht
    simpa only [γ, V, d] using ht.le
  have hRatioScaled : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          modelDensity (K * 1 ^ 2) (Module.finrank ℝ E - 1) t := by
    simpa only [one_pow, mul_one, d] using hRatio
  have hmeanScaled := curveMean_le_model_on
    (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V K 1 b zero_lt_one (Fintype.card_fin d) hd
    (fun t ht => by simpa using hadm t ht) hγ hspeed hVperp hDVperp
    hVdiff hDVdiff hLI hW hJ hRic hRatioScaled
  have hmean : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤ modelMeanCurv K d t := by
    simpa only [one_pow, mul_one] using hmeanScaled
  exact curveModelRatio_anti (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V K b d hadm hγ hVdiff hLI hW hmean

omit [T2Space (TangentBundle I M)] in
theorem intrModelDensity_le_on
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (K b : ℝ)
    (hunit : g.inner p u u = 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hadm : ∀ t ∈ Set.Ioo (0 : ℝ) b, modelRadiusAdmissible K t)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hno : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic :
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      ∀ t ∈ Set.Ioo (0 : ℝ) b,
        (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
    ∀ t ∈ Set.Ioo (0 : ℝ) b,
      curveDensity (I := I) g γ V t ≤
        modelDensity K (Module.finrank ℝ E - 1) t := by
  have hanti := intrModelRatioOfFrame_on (I := I) g hEnorm p u K b hunit hd hadm
    v hON hperp hno hRic
  have hlim := modelPoleLimit (I := I) g hEnorm p u K v hON
  intro γ V t ht
  exact density_le_model_of_ratio_anti hadm hanti hlim t ht

theorem intrHypRatioOfFrame_on
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (q b : ℝ)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hno : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic :
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      ∀ t ∈ Set.Ioo (0 : ℝ) b,
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
    let ell := Real.sqrt (g.inner p u u)
    AntitoneOn
      (fun t => curveDensity (I := I) g γ V t /
        hyperbolicDensity (q * ell) (Module.finrank ℝ E - 1) t)
      (Set.Ioo (0 : ℝ) b) := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  have hv : LinearIndependent ℝ v :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.linIndep_of_ortho
      (I := I) g p v hON
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i =>
    intrinsicJacobi (I := I) g hEnorm p u (v i)
  let ell : ℝ := Real.sqrt (g.inner p u u)
  have hell : 0 < ell := by
    simpa only [ell] using Real.sqrt_pos.2 hu
  have hγInf : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hγ : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞) γ t := by
    intro t ht
    exact hγInf.contMDiffAt.of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hspeed : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = ell ^ 2 := by
    intro t ht
    calc
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) =
          g.inner p u u := by
        change g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p u) t 1)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p u) t 1) =
            g.inner p u u
        exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
      _ = ell ^ 2 := (Real.sq_sqrt hu.le).symm
  have hVdiff : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) t).1
  have hDVdiff : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t := by
    intro t ht i
    simpa only [γ, V] using
      (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) t).2
  have hVperp : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicJacobi_perp_ne
        (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
  have hDVperp : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0 := by
    intro t ht i
    simpa only [γ, V] using
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicJacobi_dperp
        (I := I) g hEnorm p u (v i) ht.1.ne' (hperp i)
  have hLI : ∀ t ∈ Set.Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t := by
    intro t ht
    simpa only [γ, V] using
      intrinsicJacobi_linearIndependent_of_not_conj
        (I := I) g hEnorm p u v hv ht.1.ne' (hno t ht)
  have hW : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
    intro t ht i j
    exact wronskian_eq_zero (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ (V i) (V j) (hγInf.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) s).1)
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v j) s).1)
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) s).2)
      (fun s _ => by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v j) s).2)
      (fun s _ => by
        change IsJacobiAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (intrinsicJacobi (I := I) g hEnorm p u (v i)) s
        exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) s)
      (fun s _ => by
        change IsJacobiAt (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (intrinsicJacobi (I := I) g hEnorm p u (v j)) s
        exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v j : E) s)
      (by simp [V]) (by simp [V]) t ⟨ht.1.le, ht.2.le⟩
  have hJ : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t := by
    intro t ht i
    change IsJacobiAt (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p u)
      (intrinsicJacobi (I := I) g hEnorm p u (v i)) t
    exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) t
  have hRatio : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hyperbolicDensity (q * ell) d t := by
    obtain ⟨C, hC, hraw⟩ :=
      radialRatio_auto (I := I) g p (u : E) (fun i => (v i : E))
        (q * ell) (mul_nonneg hq hell.le) hv
    have hcurve :
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          γ t = radialCurve (I := I) g p (u : E) t := by
      filter_upwards [intrinsic_geodesic_and_jacobi_eventually_eq_radial (I := I) g hEnorm p (u : E) (0 : E)]
        with t ht
      simpa only [γ] using ht.1
    have hfield_i : ∀ i,
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          (V i t : E) =
            (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) := by
      intro i
      filter_upwards [
        intrinsic_geodesic_and_jacobi_eventually_eq_radial (I := I) g hEnorm p (u : E) (v i : E)] with t ht
      simpa only [V] using ht.2
    have hfields :
        ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i,
          (V i t : E) =
            (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) :=
      Filter.eventually_all.2 hfield_i
    refine ⟨C, hC, ?_⟩
    filter_upwards [hraw, hcurve, hfields] with t hrt hct hft
    have hgram :
        curveGram (I := I) g γ V t =
          curveGram (I := I) g
            (radialCurve (I := I) g p (u : E))
            (fun i => radialJacobiField (I := I) g p
              (u : E) (v i : E)) t := by
      ext i j
      simp only [curveGram, Matrix.of_apply]
      rw [hct, hft i, hft j]
    calc
      C ≤ curveDensity (I := I) g
            (radialCurve (I := I) g p (u : E))
            (fun i => radialJacobiField (I := I) g p
              (u : E) (v i : E)) t /
            hyperbolicDensity (q * ell) (Fintype.card (Fin d)) t := hrt
      _ = curveDensity (I := I) g γ V t /
            hyperbolicDensity (q * ell) d t := by
        rw [Fintype.card_fin]
        simp only [curveDensity, hgram]
  have hmean := curveMean_le_on
    (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V q ell b hq hell (Fintype.card_fin d) hd hγ hspeed
    hVperp hDVperp hVdiff hDVdiff hLI hW hJ hRic hRatio
  exact curveRatio_anti (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V (q * ell) b d (mul_nonneg hq hell.le) hγ hVdiff hLI hW hmean

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
