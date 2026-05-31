import RicciFlower.GlobalGeometry.Jacobi
import RicciFlower.GlobalGeometry.Lecture07.FirstVariation
import RicciFlower.GlobalGeometry.SmoothRadialExp
import RicciFlower.LeviCivita.Curvature.LeviCivita
import RicciFlower.Realized.CurvatureProducers
import RicciFlower.Coordinates.GaussLemma

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Gauss lemma

This downstream file records the Jacobi-field scalar core of the Gauss lemma
and pins the later normal-coordinate statement.  The Jacobi layer does not
import coordinates, while the coordinate Gauss-lemma speed calculation should
not import the Jacobi stack, so this file is the assembly layer.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Filter Tensor0SBundle
open scoped Manifold ContDiff Topology

open Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

private theorem convex_const_of_hasDerivAt_zero
    {T : Set Real} (hTconv : Convex Real T)
    {f : Real -> Real}
    (hf : ∀ t ∈ T, HasDerivAt f 0 t)
    {a b : Real} (ha : a ∈ T) (hb : b ∈ T) :
    f a = f b := by
  have hdiff : ∀ t ∈ T, DifferentiableAt Real f t :=
    fun t ht => (hf t ht).differentiableAt
  have hbound : ∀ t ∈ T, ‖fderiv Real f t‖ ≤ (0 : Real) := by
    intro t ht
    rw [(hf t ht).hasFDerivAt.fderiv]
    simp
  have h :=
    hTconv.norm_image_sub_le_of_norm_fderiv_le
      hdiff hbound ha hb
  have hzero : f b - f a = 0 := by
    apply norm_le_zero_iff.mp
    simpa using h
  linarith

/-- Pointwise curvature-skew algebra used by the Jacobi Gauss-lemma argument.

Although the statement is phrased through `velocityAlong I gamma t` because that
is the shape consumed by `curvatureAlongScalarAt`, this lemma does **not** assert
any regularity of `gamma` or use the geometric meaning of that velocity.  It is
only the pointwise identity `<R(J,V)V,V> = 0`, with
`V := velocityAlong I gamma t`, coming from metric skew-adjointness of the
Levi-Civita curvature tensor.  The later derivative statements carry the
smooth-surface/geodesic hypotheses that make `velocityAlong` a genuine velocity.
-/
theorem lc_curvScalar_velocity_zero
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real} :
    curvatureAlongScalarAt (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) g)
        gamma J t
        (dualToCotangent (I := I)
          ((tangentFlatLinear (I := I) g (gamma t))
            (velocityAlong I gamma t))) = 0 := by
  classical
  let cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov ∞ :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g
  let hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (1 : WithTop ℕ∞) :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) g
  let Rm13 : Realized.Tensor13Section (I := I) (M := M) :=
    Riemann.CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Realized.Tensor04Section (I := I) (M := M) :=
    Riemann.CovariantDerivative.rm04Section (I := I) g cov hcov
  have hRm13 : Realized.Rm13RealizesConnection (I := I) cov Rm13 :=
    Realized.rm13Section_realizes (I := I) (M := M) cov hcov
  have hRm04 : Realized.Rm04RealizesConnection (I := I) g cov Rm04 :=
    Realized.rm04Section_realizes (I := I) (M := M) g cov hcov
  have hskew :
      Realized.Rm13MetricSkewAt (I := I) g (gamma t) (Rm13 (gamma t)) :=
    LeviCivita.rm13MetricSkewAt_of_leviCivita_realizes
      (I := I) g hcov1 Rm13 Rm04 hRm13 hRm04
  let V : TangentSpace I (gamma t) := velocityAlong I gamma t
  let a : Real :=
    Rm13 (gamma t)
      (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g (gamma t)) V))
      (RicciFlower.Curvature.vec3 (I := I) (J t) V V)
  have ha : a = -a := by
    simpa [a, V, Realized.Rm13MetricSkewAt] using hskew V (J t) V V
  have ha0 : a = 0 := by linarith
  simpa [curvatureAlongScalarAt, cov, hcov, Rm13, a, V, velocityAlong] using ha0

/-- The derivative of the Gauss-lemma slope vanishes at a point of a
Levi-Civita geodesic variation whose time-domain is a neighborhood of that
point. -/
theorem gauss_variation_slope_hasDerivAt_zero_of_mem
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} {S T : Set Real} {s0 t : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F S T)
    (hS : S ∈ 𝓝 s0) (hT : T ∈ 𝓝 t) :
    HasDerivAt
      (fun τ : Real =>
        g.inner (timeCurve F s0 τ)
          (Lecture07.dsTimeField (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F (s0, τ))
          (velocityAlong I (timeCurve F s0) τ))
      0 t := by
  classical
  let cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov ∞ :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g
  let hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (1 : WithTop ℕ∞) :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) g
  have hcomm :
        VariationCurvCommAt (I := I) cov hcov F s0 t
          (fun τ => Lecture07.dsTimeField (I := I) cov F (s0, τ)) :=
    jacobi_curvComm_geodesic (I := I) (cov := cov) (hcov := hcov)
      hcov1 hF hgeo hS hT
  rcases hcomm with ⟨A, hAderiv, hscalar⟩
  have hs0 : s0 ∈ S := mem_of_mem_nhds hS
  have ht : t ∈ T := mem_of_mem_nhds hT
  have hvel :
      HasPBCovAccelAt (I := I) cov (timeCurve F s0) t
        (0 : TangentSpace I (timeCurve F s0 t)) := by
    simpa [timeCurve, cov] using hgeo s0 hs0 t ht
  have hprod :=
    RicciFlower.GlobalGeometry.Lecture07.inner_hasDerivAt_of_pbCov (I := I) g
      (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      hAderiv hvel
  have hcurv0 :
      curvatureAlongScalarAt (I := I) cov hcov (timeCurve F s0)
          (variationField I F s0) t
          (dualToCotangent (I := I)
            ((tangentFlatLinear (I := I) g (timeCurve F s0 t))
              (velocityAlong I (timeCurve F s0) t))) = 0 := by
    simpa [cov, hcov, velocityAlong] using
      lc_curvScalar_velocity_zero (I := I) g
        (gamma := timeCurve F s0) (J := variationField I F s0) (t := t)
  have hAinner : g.inner (timeCurve F s0 t) A
      (velocityAlong I (timeCurve F s0) t) = 0 := by
    have hscalar' :=
      hscalar
        (dualToCotangent (I := I)
          ((tangentFlatLinear (I := I) g (timeCurve F s0 t))
            (velocityAlong I (timeCurve F s0) t)))
    rw [hcurv0, add_zero] at hscalar'
    have hflat : g.inner (timeCurve F s0 t)
        (velocityAlong I (timeCurve F s0) t) A = 0 := by
      simpa [cotangentToDual_dualToCotangent, tangentFlatLinear_apply] using hscalar'
    exact (g.symm (timeCurve F s0 t) A
      (velocityAlong I (timeCurve F s0) t)).trans hflat
  refine hprod.congr_deriv ?_
  simpa [cov, velocityAlong] using hAinner

/-- The derivative of the Gauss-lemma slope vanishes along an all-time
Levi-Civita geodesic variation. -/
theorem gauss_variation_slope_hasDerivAt_zero
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} {S : Set Real} {s0 t : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F S Set.univ)
    (hS : S ∈ 𝓝 s0) :
    HasDerivAt
      (fun τ : Real =>
        g.inner (timeCurve F s0 τ)
          (Lecture07.dsTimeField (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F (s0, τ))
          (velocityAlong I (timeCurve F s0) τ))
      0 t :=
  gauss_variation_slope_hasDerivAt_zero_of_mem (I := I) g hF hgeo hS
    (by simp)

/-- Jacobi-field Gauss core from explicit local commutator data.

This is the localized algebraic heart used by radial exponential variations:
once a variation supplies the torsion-swap and curvature-commutator data on the
time interval, the scalar function `<J, gamma'>` is affine.  Unlike
`gauss_variation_inner_affineOn`, this theorem does not require the variation
to be a globally smooth surface; the smoothness work is isolated in the two
explicit hypotheses `htorsion` and `hcurv`. -/
theorem gauss_variation_inner_affineOn_of_comm
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} {S T : Set Real} {s0 : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    (hTconv : Convex Real T)
    (hIcc : Set.Icc (0 : Real) 1 ⊆ T)
    (hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F S T)
    (hS : S ∈ 𝓝 s0)
    (htorsion : ∀ t ∈ T,
      VariationTorsionSwapAt (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F s0 t W)
    (hcurv : ∀ t ∈ T,
      VariationCurvCommAt (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) g)
        F s0 t W) :
    ∀ t : Real, t ∈ T ->
      g.inner (timeCurve F s0 t)
          (variationField I F s0 t) (velocityAlong I (timeCurve F s0) t)
        =
        g.inner (timeCurve F s0 0)
            (variationField I F s0 0) (velocityAlong I (timeCurve F s0) 0)
          + t *
            g.inner (timeCurve F s0 0)
              (W 0) (velocityAlong I (timeCurve F s0) 0) := by
  classical
  let cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov ∞ :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g
  let f : Real -> Real := fun τ =>
    g.inner (timeCurve F s0 τ)
      (variationField I F s0 τ) (velocityAlong I (timeCurve F s0) τ)
  let fp : Real -> Real := fun τ =>
    g.inner (timeCurve F s0 τ) (W τ)
      (velocityAlong I (timeCurve F s0) τ)
  have hs0 : s0 ∈ S := mem_of_mem_nhds hS
  have h0T : (0 : Real) ∈ T := hIcc (by norm_num)
  have hfp_deriv : ∀ τ ∈ T, HasDerivAt fp 0 τ := by
    intro τ hτ
    rcases hcurv τ hτ with ⟨A, hAderiv, hscalar⟩
    have hvel :
        HasPBCovAccelAt (I := I) cov (timeCurve F s0) τ
          (0 : TangentSpace I (timeCurve F s0 τ)) := by
      simpa [timeCurve, cov] using hgeo s0 hs0 τ hτ
    have hprod :=
      RicciFlower.GlobalGeometry.Lecture07.inner_hasDerivAt_of_pbCov (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
        hAderiv hvel
    have hcurv0 :
        curvatureAlongScalarAt (I := I) cov hcov (timeCurve F s0)
            (variationField I F s0) τ
            (dualToCotangent (I := I)
              ((tangentFlatLinear (I := I) g (timeCurve F s0 τ))
                (velocityAlong I (timeCurve F s0) τ))) = 0 := by
      simpa [cov, hcov, velocityAlong] using
        lc_curvScalar_velocity_zero (I := I) g
          (gamma := timeCurve F s0) (J := variationField I F s0) (t := τ)
    have hAinner : g.inner (timeCurve F s0 τ) A
        (velocityAlong I (timeCurve F s0) τ) = 0 := by
      have hscalar' :=
        hscalar
          (dualToCotangent (I := I)
            ((tangentFlatLinear (I := I) g (timeCurve F s0 τ))
              (velocityAlong I (timeCurve F s0) τ)))
      rw [hcurv0, add_zero] at hscalar'
      have hflat : g.inner (timeCurve F s0 τ)
          (velocityAlong I (timeCurve F s0) τ) A = 0 := by
        simpa [cotangentToDual_dualToCotangent, tangentFlatLinear_apply]
          using hscalar'
      exact (g.symm (timeCurve F s0 τ) A
        (velocityAlong I (timeCurve F s0) τ)).trans hflat
    refine hprod.congr_deriv ?_
    simpa [fp, cov, velocityAlong] using hAinner
  have hfp_const : ∀ τ ∈ T, fp τ = fp 0 := by
    intro τ hτ
    exact convex_const_of_hasDerivAt_zero hTconv hfp_deriv hτ h0T
  have hf_deriv : ∀ τ ∈ T, HasDerivAt f (fp τ) τ := by
    intro τ hτ
    have hvel :
        HasPBCovAccelAt (I := I) cov (timeCurve F s0) τ
          (0 : TangentSpace I (timeCurve F s0 τ)) := by
      simpa [timeCurve, cov] using hgeo s0 hs0 τ hτ
    have hprod :=
      RicciFlower.GlobalGeometry.Lecture07.inner_hasDerivAt_of_pbCov (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
        (htorsion τ hτ).1 hvel
    refine hprod.congr_deriv ?_
    simp [fp]
  let c : Real := fp 0
  have hf_c : ∀ τ ∈ T, HasDerivAt f c τ := by
    intro τ hτ
    exact (hf_deriv τ hτ).congr_deriv (hfp_const τ hτ)
  let l : Real -> Real := fun τ => f τ - c * τ
  have hl_deriv : ∀ τ ∈ T, HasDerivAt l 0 τ := by
    intro τ hτ
    have hlin : HasDerivAt (fun r : Real => c * r) c τ := by
      simpa using (hasDerivAt_id τ).const_mul c
    have h := (hf_c τ hτ).sub hlin
    refine h.congr_deriv ?_
    ring
  have hl_const : ∀ τ ∈ T, l τ = l 0 := by
    intro τ hτ
    exact convex_const_of_hasDerivAt_zero hTconv hl_deriv hτ h0T
  intro t ht
  have hlt := hl_const t ht
  change f t = f 0 + t * c
  dsimp [l] at hlt
  nlinarith

/-- Jacobi-field Gauss core on an open convex time-domain containing `[0,1]`:
`<J,γ'>` is affine in the curve parameter.  The slope is expressed using the
canonical first derivative field `dsTimeField = D_t J` at time `0`.

The neighborhood hypothesis on `T` is what lets the existing Jacobi
commutator/torsion APIs produce ordinary `HasDerivAt` statements.  Closed
interval consumers should choose an open convex time-domain containing the
closed interval they need. -/
theorem gauss_variation_inner_affineOn
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} {S T : Set Real} {s0 : Real}
    (hF : SmoothSurface (I := I) F)
    (hTconv : Convex Real T)
    (hTnhds : ∀ t ∈ T, T ∈ 𝓝 t)
    (hIcc : Set.Icc (0 : Real) 1 ⊆ T)
    (hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F S T)
    (hS : S ∈ 𝓝 s0) :
    ∀ t : Real, t ∈ T ->
      g.inner (timeCurve F s0 t)
          (variationField I F s0 t) (velocityAlong I (timeCurve F s0) t)
        =
        g.inner (timeCurve F s0 0)
            (variationField I F s0 0) (velocityAlong I (timeCurve F s0) 0)
          + t *
            g.inner (timeCurve F s0 0)
              (Lecture07.dsTimeField (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F (s0, 0))
              (velocityAlong I (timeCurve F s0) 0) := by
  classical
  let cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let f : Real -> Real := fun τ =>
    g.inner (timeCurve F s0 τ)
      (variationField I F s0 τ) (velocityAlong I (timeCurve F s0) τ)
  let fp : Real -> Real := fun τ =>
    g.inner (timeCurve F s0 τ)
      (Lecture07.dsTimeField (I := I) cov F (s0, τ))
      (velocityAlong I (timeCurve F s0) τ)
  have hs0 : s0 ∈ S := mem_of_mem_nhds hS
  have h0T : (0 : Real) ∈ T := hIcc (by norm_num)
  have hfp_deriv : ∀ τ ∈ T, HasDerivAt fp 0 τ := by
    intro τ hτ
    simpa [fp, cov] using
      gauss_variation_slope_hasDerivAt_zero_of_mem (I := I) g hF hgeo hS
        (hTnhds τ hτ)
  have hfp_const : ∀ τ ∈ T, fp τ = fp 0 := by
    intro τ hτ
    exact convex_const_of_hasDerivAt_zero hTconv hfp_deriv hτ h0T
  have hf_deriv : ∀ τ ∈ T, HasDerivAt f (fp τ) τ := by
    intro τ hτ
    have hswap :
        VariationTorsionSwapAt (I := I) cov F s0 τ
          (fun r => Lecture07.dsTimeField (I := I) cov F (s0, r)) :=
      jacobi_torsionSwap_smooth (I := I) (cov := cov)
        (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree (I := I) g)
        hF
    have hvel :
        HasPBCovAccelAt (I := I) cov (timeCurve F s0) τ
          (0 : TangentSpace I (timeCurve F s0 τ)) := by
      simpa [timeCurve, cov] using hgeo s0 hs0 τ hτ
    have hprod :=
      RicciFlower.GlobalGeometry.Lecture07.inner_hasDerivAt_of_pbCov (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
        hswap.1 hvel
    refine hprod.congr_deriv ?_
    simp [fp, cov]
  let c : Real := fp 0
  have hf_c : ∀ τ ∈ T, HasDerivAt f c τ := by
    intro τ hτ
    exact (hf_deriv τ hτ).congr_deriv (hfp_const τ hτ)
  let l : Real -> Real := fun τ => f τ - c * τ
  have hl_deriv : ∀ τ ∈ T, HasDerivAt l 0 τ := by
    intro τ hτ
    have hlin : HasDerivAt (fun r : Real => c * r) c τ := by
      simpa using (hasDerivAt_id τ).const_mul c
    have h := (hf_c τ hτ).sub hlin
    refine h.congr_deriv ?_
    ring
  have hl_const : ∀ τ ∈ T, l τ = l 0 := by
    intro τ hτ
    exact convex_const_of_hasDerivAt_zero hTconv hl_deriv hτ h0T
  intro t ht
  have hlt := hl_const t ht
  change f t = f 0 + t * c
  dsimp [l] at hlt
  nlinarith

/-- Jacobi-field Gauss core for all-time Levi-Civita geodesic variations:
`<J,γ'>` is affine in the curve parameter.  The slope is expressed using the
canonical first derivative field `dsTimeField = D_t J` at time `0`. -/
theorem gauss_variation_inner_affine
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} {S : Set Real} {s0 : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F S Set.univ)
    (hS : S ∈ 𝓝 s0) :
    ∀ t : Real,
      g.inner (timeCurve F s0 t)
          (variationField I F s0 t) (velocityAlong I (timeCurve F s0) t)
        =
        g.inner (timeCurve F s0 0)
            (variationField I F s0 0) (velocityAlong I (timeCurve F s0) 0)
          + t *
            g.inner (timeCurve F s0 0)
              (Lecture07.dsTimeField (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F (s0, 0))
              (velocityAlong I (timeCurve F s0) 0) := by
  intro t
  exact gauss_variation_inner_affineOn (I := I) g hF
    (T := Set.univ) convex_univ
    (by intro τ hτ; simp)
    (by intro τ hτ; trivial)
    hgeo hS t trivial

/-- Private assembly bridge for the normalized radial Gauss lemma.

All Jacobi algebra and endpoint field identifications are discharged here.  The
remaining producers are exactly the local torsion/curvature commutator data for
the radial variation and the initial mixed-derivative value `W 0 = w`. -/
private theorem gaussNorm_of_comm
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {u w : TangentSpace I x}
    (hu : u ∈ Metric.ball (0 : TangentSpace I x) D.radius)
    (W : VectorFieldAlong I (timeCurve (D.variation u w) 0))
    (htorsion : ∀ t ∈ Set.Icc (0 : Real) 1,
      VariationTorsionSwapAt (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (D.variation u w) 0 t W)
    (hcurv : ∀ t ∈ Set.Icc (0 : Real) 1,
      VariationCurvCommAt (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) g)
        (D.variation u w) 0 t W)
    (hW0 : W 0 = w) :
    g.inner (D.exp u)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
      =
    g.inner x u w := by
  classical
  rcases D.varMem (v := u) (w := w) hu with ⟨δ, hδ, hδmem⟩
  have hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      (D.variation u w) (Metric.ball (0 : Real) δ) (Set.Icc (0 : Real) 1) :=
    D.variationGeo hδmem
  have hS : Metric.ball (0 : Real) δ ∈ 𝓝 (0 : Real) :=
    Metric.ball_mem_nhds _ hδ
  have haff := gauss_variation_inner_affineOn_of_comm (I := I) g
    (S := Metric.ball (0 : Real) δ) (T := Set.Icc (0 : Real) 1)
    (s0 := 0) (W := W)
    (convex_Icc (0 : Real) 1) (Set.Subset.rfl) hgeo hS htorsion hcurv
    1 (by norm_num)
  have hbase1 : timeCurve (D.variation u w) 0 1 = D.exp u := by
    simp [timeCurve, SmoothRadialExp.variation, SmoothRadialExp.variationArg]
  have hbase0 : timeCurve (D.variation u w) 0 0 = x := by
    simpa [timeCurve] using D.variation_zero u w 0
  have hvar1 := D.varField_one (v := u) (w := w) hu
  have htime1 := D.timeVel_one (v := u) (w := w) hu
  have hvar0 := D.varField_zero u w
  have htime0 := D.timeVel_zero (v := u) (w := w) hu
  have htime1' :
      curveVelocity I (timeCurve (D.variation u w) 0) 1 =
        (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u := by
    simpa [velocityAlong] using htime1
  have htime0' :
      curveVelocity I (timeCurve (D.variation u w) 0) 0 = u := by
    simpa [velocityAlong] using htime0
  have hraw :
      g.inner (D.exp u)
        ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
        ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u)
        =
      g.inner x w u := by
    rw [hbase1, hbase0, hvar1, hvar0, hW0, htime1, htime0] at haff
    have hzero : g.inner x (0 : TangentSpace I x) u = 0 := by simp
    calc
      g.inner (D.exp u)
          ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
          ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u)
          =
        g.inner x (0 : TangentSpace I x) u + 1 * g.inner x w u := haff
      _ = g.inner x w u := by rw [hzero, zero_add, one_mul]
  calc
    g.inner (D.exp u)
        ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u)
        ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
        =
      g.inner (D.exp u)
        ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
        ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u) :=
        g.symm (D.exp u)
          ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u)
          ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
    _ = g.inner x w u := hraw
    _ = g.inner x u w := g.symm x w u

/-- Normalized radial form of the Gauss lemma from a ball-based smooth radial
exponential package.

This is the book-facing bridge at the correct abstraction layer.  The checked
Jacobi scalar calculation is already available above; the remaining proof
obligation is to identify the local radial variation
`F(s,t) = D.exp (t • (u + s • w))` with the manifold derivatives of `D.exp`
and to produce the local torsion/curvature commutator data without extending
`D.exp` outside its ball source. -/
theorem gaussNormRadial
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {u w : TangentSpace I x}
    (hu : u ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    g.inner (D.exp u)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
      =
    g.inner x u w := by
  rcases D.variationCommData (u := u) (w := w) hu with
    ⟨W, htorsion, hcurv, hW0⟩
  exact gaussNorm_of_comm (I := I) g D hu W htorsion hcurv hW0

/-- Positive-radius GSM 7.29 radial form.

The radial vector at `r • V` is represented by `V`; the proof is just the
linear rescaling of `gaussNormRadial`.  The endpoint case `r = 0` additionally
needs the zero-derivative identity for the exponential map and is kept out of
this positive-radius theorem. -/
theorem gaussRadial_pos
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {V W : TangentSpace I x} {r : Real}
    (hr : 0 < r)
    (hrV : r • V ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    g.inner (D.exp (r • V))
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) V)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) W)
      =
    g.inner x V W := by
  let dExp :=
    mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)
  have hnorm := gaussNormRadial (I := I) g D (u := r • V) (w := W) hrV
  have hdExp : dExp (r • V) = r • dExp V := by
    exact map_smul dExp r V
  have hscale :
      r * g.inner (D.exp (r • V)) (dExp V) (dExp W) =
        r * g.inner x V W := by
    simpa [dExp, hdExp, smul_eq_mul] using hnorm
  nlinarith

/-- GSM 7.29 radial form from the normalized radial Gauss lemma. -/
theorem gaussRadial
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {V W : TangentSpace I x} {r : Real}
    (hr : 0 ≤ r)
    (hrV : r • V ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    g.inner (D.exp (r • V))
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) V)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) W)
      =
    g.inner x V W := by
  rcases lt_or_eq_of_le hr with hrpos | rfl
  · exact gaussRadial_pos (I := I) g D hrpos hrV
  · have hV := D.mfderiv_zero_apply V
    have hW := D.mfderiv_zero_apply W
    rw [zero_smul]
    rw [hV, hW, D.exp_zero]

/-- Squared-length consequence of the radial Gauss lemma. -/
theorem gaussRadial_self
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {V : TangentSpace I x} {r : Real}
    (hr : 0 ≤ r)
    (hrV : r • V ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    g.inner (D.exp (r • V))
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) V)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) V)
      =
    g.inner x V V :=
  gaussRadial (I := I) g D (V := V) (W := V) hr hrV

/-- Orthogonality consequence of the radial Gauss lemma. -/
theorem gaussRadial_perp
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {V W : TangentSpace I x} {r : Real}
    (hr : 0 ≤ r)
    (hrV : r • V ∈ Metric.ball (0 : TangentSpace I x) D.radius)
    (hVW : g.inner x V W = 0) :
    g.inner (D.exp (r • V))
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) V)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp (r • V)) W)
      =
    0 := by
  rw [gaussRadial (I := I) g D (V := V) (W := W) hr hrV, hVW]

/-- Book-facing normalized Gauss lemma for a smooth radial exponential package. -/
theorem gaussLemma
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {u w : TangentSpace I x}
    (hu : u ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    g.inner (D.exp u)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) u)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp u) w)
      =
    g.inner x u w :=
  gaussNormRadial (I := I) g D (u := u) (w := w) hu

/-- Normal-coordinate compatibility frontier for the Gauss lemma.

The current `NormalCoordinateData` contains a topological endpoint map but not
the smooth exponential differential, nor the bridge identifying that
differential with the variation field of `F(s,t)=exp(t • (v+s•w))`.  Those
exp-differential facts are the remaining normal-coordinate frontier. -/
theorem gaussNormal_frontier
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (N : Coordinates.NormalCoordinateData (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) N.radius) :
    g.inner (N.exp v)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I N.exp v) v)
      ((mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I N.exp v) w)
      =
    g.inner x v w := by
  -- Frontier: construct the smooth radial exponential variation and identify
  -- its variation field with the two displayed `mfderiv` terms.
  sorry

end GlobalGeometry
end RicciFlower
