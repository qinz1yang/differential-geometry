import RicciFlower.GlobalGeometry.Jacobi.FrameCurvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Geodesic variation identities

Formal torsion-swap and curvature-commutator identities for smooth geodesic variations.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Filter Tensor0SBundle RicciFlower.Curvature
open scoped Manifold ContDiff Topology

open Lecture07
open RicciFlower.Tensor.SlotAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-! ## Formal geodesic-variation identities -/

/-- A geodesic variation on a rectangle of parameter values. -/
def IsGeodesicVariationOn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (S T : Set Real) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T,
    HasPBCovAccelAt (I := I) cov (timeCurve F s) t 0

/-- Torsion/mixed-derivative swap data at one point of a variation.

`W` is both the time covariant derivative of the variation field and the
parameter covariant derivative of the time field.  This is the canonical
pullback version of `D_t S = D_s T`. -/
def VariationTorsionSwapAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 t : Real)
    (W : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  HasPBCovAlongAt (I := I) cov (timeCurve F s0)
      (variationField I F s0) t (W t) ∧
    HasPBCovAlongAt (I := I) cov (paramCurve F t)
      (paramRestrictField I F (timeField I F) t) s0 (W t)

/-- Curvature commutator data after differentiating the geodesic equation.

Together with `VariationTorsionSwapAt`, this supplies the second derivative of
the variation field and the curvature term in the Jacobi equation. -/
def VariationCurvCommAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (F : Surface M) (s0 t : Real)
    (W : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  ∃ A : TangentSpace I (timeCurve F s0 t),
    HasPBCovAlongAt (I := I) cov (timeCurve F s0) W t A ∧
      ∀ α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 (timeCurve F s0 t),
        cotangentToDual (I := I) α A +
            curvatureAlongScalarAt (I := I) cov hcov
              (timeCurve F s0) (variationField I F s0) t α = 0

/-- Surface-jet curvature commutator in the centered coordinate frame.

This is the checked bridge from the fixed-frame surface commutator to the
Jacobi-facing `VariationCurvCommAt`.  The remaining producer work is exactly
the scalar surface calculus supplied here as hypotheses: derivatives of the
time/parameter velocity coefficients, derivatives of Christoffel coefficients
along the surface, and mixed-partial equality. -/
private theorem curvComm_surface
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {s t : Real}
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F (timeField I F) Vs
      (fun _ => 0) s t (0 : TangentSpace I (F (s, t))) DtsV)
    (hmem_s : ∀ᶠ σ : Real in 𝓝 s,
      F (σ, t) ∈ Coordinates.coordinateFrameSet (I := I) (F (s, t)))
    (hmem_t : ∀ᶠ τ : Real in 𝓝 t,
      F (s, τ) ∈ Coordinates.coordinateFrameSet (I := I) (F (s, t)))
    (S T Ts St : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (hS :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
            i (F (s, t)) (paramField I F (s, t)) = S i)
    (hT :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
            i (F (s, t)) (timeField I F (s, t)) = T i)
    (hTderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
              i (F (σ, t)) (timeField I F (σ, t)))
          (Ts i) s)
    (hSderiv :
      ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) (F (s, t))).coeff
              i (F (s, τ)) (paramField I F (s, τ)))
          (St i) t)
    (hCs :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun σ : Real =>
            Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (σ, t)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            S a * Realized.christoffelCoordDerivAt (I := I) cov
              (F (s, t)) a i j k) s)
    (hCt :
      ∀ i j k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        HasDerivAt
          (fun τ : Real =>
            Realized.christoffelCoordFun (I := I) cov (F (s, t)) i j k (F (s, τ)))
          (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
            T a * Realized.christoffelCoordDerivAt (I := I) cov
              (F (s, t)) a i j k) t)
    {vt vst vts : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real}
    (hvt_s : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (timeCurve F σ)
          (fun τ => timeField I F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s)
    (hvs : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (timeField I F (σ, t))) Ts s)
    (hvs_t : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (paramCurve F τ)
          (fun σ => timeField I F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t)
    (hvt : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameVec (I := I)
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (timeField I F (s, τ))) vt t)
    (hmix_raw : vst = vts)
    (hmix : Ts = St) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Vs (s, τ)) := by
  classical
  let x : M := F (s, t)
  let e := Coordinates.coordinateTrivializationAt (I := I) x
  let b := Module.finBasis Real E
  let Γs : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
      (paramCurve F t) s (1 : TangentSpace 𝓘(Real, Real) s)
  let Γt : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
      (timeCurve F s) t (1 : TangentSpace 𝓘(Real, Real) t)
  let dΓt_s : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    fun k j =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (Ts i * Realized.christoffelCoordAt (I := I) cov x i j k +
          T i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              S a * Realized.christoffelCoordDerivAt (I := I) cov x a i j k))
  let dΓs_t : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    fun k j =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        (St i * Realized.christoffelCoordAt (I := I) cov x i j k +
          S i *
            (∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
              T a * Realized.christoffelCoordDerivAt (I := I) cov x a i j k))
  have hmem_s_e : ∀ᶠ σ : Real in 𝓝 s, F (σ, t) ∈ e.baseSet := by
    simpa [e, x, Coordinates.coordinateTrivializationAt] using hmem_s
  have hmem_t_e : ∀ᶠ τ : Real in 𝓝 t, F (s, τ) ∈ e.baseSet := by
    simpa [e, x, Coordinates.coordinateTrivializationAt] using hmem_t
  have hΓt_deriv : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t (1 : TangentSpace 𝓘(Real, Real) t))
      dΓt_s s := by
    have h := gammaT_deriv_s_mat (I := I) cov x F s t hmem_s T S Ts
      (by simpa [x] using hT) (by simpa [x] using hTderiv)
      (by simpa [x, Realized.christoffelCoordAt, Realized.christoffelCoordFun] using hCs)
    simpa [dΓt_s, e, b, x, surfaceTimeCurve, timeCurve,
      Realized.christoffelCoordAt, Realized.christoffelCoordFun] using h
  have hΓs_deriv : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s (1 : TangentSpace 𝓘(Real, Real) s))
      dΓs_t t := by
    have h := gammaS_deriv_t_mat (I := I) cov x F s t hmem_t S T St
      (by simpa [x] using hS) (by simpa [x] using hSderiv)
      (by simpa [x, Realized.christoffelCoordAt, Realized.christoffelCoordFun] using hCt)
    simpa [dΓs_t, e, b, x, surfaceParamCurve, paramCurve,
      Realized.christoffelCoordAt, Realized.christoffelCoordFun] using h
  have hvt_s' : HasDerivAt
      (fun σ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => timeField I F (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s := by
    simpa [e, b, x, surfaceTimeCurve, timeCurve] using hvt_s
  have hvs_t' : HasDerivAt
      (fun τ : Real =>
        Lecture07.frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => timeField I F (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t := by
    simpa [e, b, x, surfaceParamCurve, paramCurve] using hvs_t
  have hvs' : HasDerivAt
      (fun σ : Real => Lecture07.frameVec (I := I) e b (timeField I F (σ, t)))
      Ts s := by
    simpa [e, b, x] using hvs
  have hvt' : HasDerivAt
      (fun τ : Real => Lecture07.frameVec (I := I) e b (timeField I F (s, τ)))
      vt t := by
    simpa [e, b, x] using hvt
  have hvec_raw := hjet.frame_dts_neg_vec (I := I) (cov := cov)
    (hDst := by rfl) (e := e) (b := b) hmem_s_e hmem_t_e
    hΓt_deriv hvt_s' hvs' hΓs_deriv hvs_t' hvt' hmix_raw
  have hvec : DtsV =
      -Lecture07.frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
        (timeField I F (s, t)) := by
    simpa [Γs, Γt, e, b, x, surfaceParamCurve, surfaceTimeCurve,
      paramCurve, timeCurve] using hvec_raw
  refine ⟨DtsV, ?_, ?_⟩
  · simpa [HasPBTimeCovDerivAt, surfaceTimeCurve, timeCurve] using
      hjet.has_time_param
  · intro α
    have hcurv : cotangentToDual (I := I) α
          (Lecture07.frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
            (timeField I F (s, t))) =
        curvatureAlongScalarAt (I := I) cov hcov
          (timeCurve F s) (variationField I F s) t α := by
      have hΓs_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            Γs m j =
              ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (variationField I F s t) i *
                  Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) i j m := by
        intro m j
        have h := frameGammaMat_coord (I := I) cov (paramCurve F t) s j m
        simpa [Γs, e, b, x, timeCurve, paramCurve, variationField] using h
      have hΓt_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            Γt m j =
              ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (curveVelocity I (timeCurve F s) t) k *
                  Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) k j m := by
        intro m j
        have h := frameGammaMat_coord (I := I) cov (timeCurve F s) t j m
        simpa [Γt, e, b, x, timeCurve] using h
      have hSrepr :
          ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                (variationField I F s t) i = S i := by
        intro i
        rw [← hS i]
        have hcoeff :=
          Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord (I := I)
            (F (s, t)) (paramField I F (s, t)) i
        simpa [timeCurve, variationField, paramField] using hcoeff.symm
      have hTrepr :
          ∀ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                (curveVelocity I (timeCurve F s) t) i = T i := by
        intro i
        rw [← hT i]
        have hcoeff :=
          Coordinates.coordinateFrameAt_coeff_eq_toBasis_coord (I := I)
            (F (s, t)) (timeField I F (s, t)) i
        simpa [timeCurve, timeField] using hcoeff.symm
      have hDΓt_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              dΓt_s m j =
              ∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (Ts k * Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) k j m +
                  (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (curveVelocity I (timeCurve F s) t) k *
                    (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                      (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                        (variationField I F s t) i *
                        Realized.christoffelCoordDerivAt (I := I) cov
                          (timeCurve F s t) i k j m)) := by
        intro m j
        dsimp [dΓt_s, x]
        simp_rw [← hTrepr, ← hSrepr]
        simp [timeCurve]
      have hDΓs_val :
          ∀ m j : Coordinates.CoordinateIdx (𝕜 := Real) E,
            dΓs_t m j =
              ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
                (St i * Realized.christoffelCoordAt (I := I) cov (timeCurve F s t) i j m +
                  (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                    (variationField I F s t) i *
                    (∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
                      (Coordinates.coordinateFrameAt_toBasis (I := I) (timeCurve F s t)).repr
                        (curveVelocity I (timeCurve F s) t) k *
                        Realized.christoffelCoordDerivAt (I := I) cov
                          (timeCurve F s t) k i j m)) := by
        intro m j
        dsimp [dΓs_t, x]
        simp_rw [← hTrepr, ← hSrepr]
        simp [timeCurve]
      have hmain := curvVec_scalar_deriv (I := I) (cov := cov) (hcov := hcov)
        hcov1 (gamma := timeCurve F s) (J := variationField I F s) (t := t)
        Γs Γt dΓt_s dΓs_t Ts St α
        hΓs_val hΓt_val hDΓt_val hDΓs_val hmix
      simpa [e, b, Γs, Γt, x, timeCurve, timeField] using hmain
    let R : TangentSpace I (timeCurve F s t) :=
      Lecture07.frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
        (timeField I F (s, t))
    have hdual :
        cotangentToDual (I := I) α (-R) + cotangentToDual (I := I) α R = 0 := by
      rw [map_neg]
      exact neg_add_cancel _
    have hcurvR :
        cotangentToDual (I := I) α R =
          curvatureAlongScalarAt (I := I) cov hcov
            (timeCurve F s) (variationField I F s) t α := by
      simpa [R] using hcurv
    rw [hvec]
    change cotangentToDual (I := I) α (-R) +
        curvatureAlongScalarAt (I := I) cov hcov
          (timeCurve F s) (variationField I F s) t α = 0
    rw [← hcurvR]
    exact hdual

/-- Smooth-surface producer for the Jacobi curvature commutator.

All fixed-coordinate scalar data required by `curvComm_surface` is produced in
`Lecture07.SurfaceCalculus`; this theorem keeps `VariationCurvCommAt` free of
coordinate-calculus hypotheses. -/
private theorem curvComm_smooth
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F (timeField I F) Vs
      (fun _ => 0) s t (0 : TangentSpace I (F (s, t))) DtsV) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Vs (s, τ)) := by
  let jet := Lecture07.SmoothSurface.coordSurfJet
    (I := I) (cov := cov) hcov1 hF s t
  exact curvComm_surface (I := I) (cov := cov) (hcov := hcov) hcov1
    (F := F) (s := s) (t := t) (Vs := Vs) (DtsV := DtsV)
    hjet
    (by simpa [jet] using jet.hmem_s)
    (by simpa [jet] using jet.hmem_t)
    jet.S jet.T jet.Ts jet.St
    (by
      intro i
      simpa [jet, paramField, Lecture07.surfaceParamField] using jet.hS i)
    (by
      intro i
      simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hT i)
    (by
      intro i
      simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hTderiv i)
    (by
      intro i
      simpa [jet, paramField, Lecture07.surfaceParamField] using jet.hSderiv i)
    (by
      intro i j k
      simpa [jet] using jet.hCs i j k)
    (by
      intro i j k
      simpa [jet] using jet.hCt i j k)
    (by simpa [jet, timeCurve, Lecture07.surfaceTimeCurve,
      timeField, Lecture07.surfaceTimeField] using jet.hvt_s)
    (by simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hvs)
    (by simpa [jet, paramCurve, Lecture07.surfaceParamCurve,
      timeField, Lecture07.surfaceTimeField] using jet.hvs_t)
    (by simpa [jet, timeField, Lecture07.surfaceTimeField] using jet.hvt)
    (by simpa [jet] using jet.hmix_raw)
    (by simpa [jet] using jet.hmix)

/-- A set-level geodesic variation gives the corresponding time-acceleration
germ at any interior point of the parameter rectangle. -/
theorem IsGeodesicVariationOn.geoGerm
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {S T : Set Real} {s t : Real}
    (hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hS : S ∈ 𝓝 s) (hT : T ∈ 𝓝 t) :
    ∀ᶠ q : Real × Real in 𝓝 (s, t),
      HasPBCovAccelAt (I := I) cov (timeCurve F q.1) q.2
        (0 : TangentSpace I (F q)) := by
  have hfst : Tendsto Prod.fst (𝓝 ((s, t) : Real × Real)) (𝓝 s) :=
    continuousAt_fst.tendsto
  have hsnd : Tendsto Prod.snd (𝓝 ((s, t) : Real × Real)) (𝓝 t) :=
    continuousAt_snd.tendsto
  filter_upwards [hfst.eventually hS, hsnd.eventually hT] with q hqS hqT
  simpa [timeCurve] using hgeo q.1 hqS q.2 hqT

/-- The time part of the surface 2-jet produced by a geodesic variation.

The remaining inputs specify the parameter derivative field `Vs = D_s T` and
its time derivative at the point. -/
private theorem timeJet_of_geo
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hgeo :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBCovAccelAt (I := I) cov (timeCurve F q.1) q.2
          (0 : TangentSpace I (F q)))
    (hVs :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBParamCovDerivAt (I := I) cov F (timeField I F)
          q.1 q.2 (Vs q))
    (hDts : HasPBTimeCovDerivAt (I := I) cov F Vs s t DtsV) :
    HasPBSurfaceCovDeriv2At (I := I) cov F (timeField I F) Vs
      (fun _ => 0) s t (0 : TangentSpace I (F (s, t))) DtsV := by
  refine
    { has_param_germ := ?_
      has_time_germ := ?_
      has_param_time := ?_
      has_time_param := hDts }
  · exact hVs
  · filter_upwards [hgeo] with q hq
    simpa [HasPBTimeCovDerivAt, HasPBCovAccelAt, timeField,
      Lecture07.surfaceTimeCurve, timeCurve, velocityAlong] using hq
  · have hparam : MDifferentiableAt 𝓘(Real, Real) I
        (Lecture07.surfaceParamCurve F t) s := by
      simpa [SmoothSurface] using hF.mdiffAt_param (I := I) s t
    exact HasPBParamCovDerivAt.zero (I := I) (cov := cov) hparam

/-- Smooth geodesic-variation curvature commutator from a parameter-derivative
surface field. -/
private theorem curvComm_geo
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    {Vs : SurfaceField I F} {DtsV : TangentSpace I (F (s, t))}
    (hgeo :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBCovAccelAt (I := I) cov (timeCurve F q.1) q.2
          (0 : TangentSpace I (F q)))
    (hVs :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBParamCovDerivAt (I := I) cov F (timeField I F)
          q.1 q.2 (Vs q))
    (hDts : HasPBTimeCovDerivAt (I := I) cov F Vs s t DtsV) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Vs (s, τ)) :=
  curvComm_smooth (I := I) (cov := cov) (hcov := hcov) hcov1 hF
    (timeJet_of_geo (I := I) (cov := cov) hF hgeo hVs hDts)

/-- Smooth-surface torsion swap for a torsion-free connection.

The field is the canonical coordinate/frame-defined `D_s T` field supplied by
the surface-calculus producer. -/
theorem jacobi_torsionSwap_smooth
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {s t : Real}
    (hF : SmoothSurface (I := I) F) :
    VariationTorsionSwapAt (I := I) cov F s t
      (fun τ => Lecture07.dsTimeField (I := I) cov F (s, τ)) := by
  constructor
  · have h := Lecture07.SmoothSurface.hasTime_param_eq_dsTime
      (I := I) (cov := cov) htf hF s t
    simpa [HasPBTimeCovDerivAt, timeCurve, variationField, paramField,
      Lecture07.surfaceTimeCurve, Lecture07.surfaceParamField] using h
  · have h := Lecture07.SmoothSurface.hasParam_dsTime
      (I := I) (cov := cov) hF s t
    simpa [HasPBParamCovDerivAt, paramCurve, paramRestrictField, timeField,
      Lecture07.surfaceParamCurve, Lecture07.surfaceTimeField] using h

/-- Local-on-open smooth-surface torsion swap for a torsion-free connection.

This is the local version needed by ball-defined radial exponential variations:
the surface only has to be smooth on an open source containing the point. -/
theorem jacobi_torsionSwap_contMDiffOn
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {U : Set (Real × Real)} {s t : Real}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    (hp : (s, t) ∈ U) :
    VariationTorsionSwapAt (I := I) cov F s t
      (fun τ => Lecture07.dsTimeField (I := I) cov F (s, τ)) := by
  constructor
  · have h := Lecture07.hasTime_param_eq_dsTime_of_contMDiffOn
      (I := I) (cov := cov) htf hU hF hp
    simpa [HasPBTimeCovDerivAt, timeCurve, variationField, paramField,
      Lecture07.surfaceTimeCurve, Lecture07.surfaceParamField] using h
  · have h := Lecture07.hasParam_dsTime_of_contMDiffOn
      (I := I) (cov := cov) hU hF hp
    simpa [HasPBParamCovDerivAt, paramCurve, paramRestrictField, timeField,
      Lecture07.surfaceParamCurve, Lecture07.surfaceTimeField] using h

/-- Local-on-open geodesic-variation curvature commutator with the canonical
`D_s T` field.

This is the local counterpart of `jacobi_curvComm_geodesic`: instead of a
globally smooth surface and a rectangular geodesic variation, it needs
smoothness on an open source plus an ordinary geodesic germ near `(s,t)`. -/
theorem jacobi_curvComm_contMDiffOn_of_geoGerm
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {U : Set (Real × Real)} {s t : Real}
    (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) I ∞ F U)
    (hp : (s, t) ∈ U)
    (hgeo :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBCovAccelAt (I := I) cov (timeCurve F q.1) q.2
          (0 : TangentSpace I (F q))) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Lecture07.dsTimeField (I := I) cov F (s, τ)) := by
  let DtsV : TangentSpace I (F (s, t)) :=
    Lecture07.dtdsTimeFieldIn (I := I) cov (F (s, t)) F s t
  have hUevent : ∀ᶠ q : Real × Real in 𝓝 (s, t), q ∈ U :=
    hU.mem_nhds hp
  have hVs :
      ∀ᶠ q : Real × Real in 𝓝 (s, t),
        HasPBParamCovDerivAt (I := I) cov F (timeField I F)
          q.1 q.2 (Lecture07.dsTimeField (I := I) cov F q) := by
    filter_upwards [hUevent] with q hq
    simpa [timeField, Lecture07.surfaceTimeField] using
      Lecture07.hasParam_dsTime_of_contMDiffOn
        (I := I) (cov := cov) hU hF hq
  have hDts :
      HasPBTimeCovDerivAt (I := I) cov F
        (Lecture07.dsTimeField (I := I) cov F)
        s t DtsV := by
    simpa [DtsV, Lecture07.HasPBTimeCovDerivAt] using
      Lecture07.hasTime_dsTime_of_contMDiffOn
        (I := I) (cov := cov) hcov1 hU hF hp
  have hjet :
      HasPBSurfaceCovDeriv2At (I := I) cov F (timeField I F)
        (Lecture07.dsTimeField (I := I) cov F) (fun _ => 0)
        s t (0 : TangentSpace I (F (s, t))) DtsV := by
    refine
      { has_param_germ := hVs
        has_time_germ := ?_
        has_param_time := ?_
        has_time_param := hDts }
    · filter_upwards [hgeo] with q hq
      simpa [HasPBTimeCovDerivAt, HasPBCovAccelAt, timeField,
        Lecture07.surfaceTimeCurve, timeCurve, velocityAlong] using hq
    · have hFat : ContMDiffAt 𝓘(Real, Real × Real) I ∞ F (s, t) :=
        hF.contMDiffAt (hU.mem_nhds hp)
      have hparam : MDifferentiableAt 𝓘(Real, Real) I
          (Lecture07.surfaceParamCurve F t) s :=
        Lecture07.mdiffAt_param_of_contMDiffAt (I := I) hFat
      exact HasPBParamCovDerivAt.zero (I := I) (cov := cov) hparam
  let jet := Lecture07.coordSurfJet_of_contMDiffOn
    (I := I) (cov := cov) hcov1 hU hF hp
  exact curvComm_surface (I := I) (cov := cov) (hcov := hcov) hcov1
    hjet
    (by simpa [jet] using jet.hmem_s)
    (by simpa [jet] using jet.hmem_t)
    jet.S jet.T jet.Ts jet.St
    (by intro i; simpa [jet, paramField] using jet.hS i)
    (by intro i; simpa [jet, timeField] using jet.hT i)
    (by intro i; simpa [jet, paramField, timeField] using jet.hTderiv i)
    (by intro i; simpa [jet, paramField, timeField] using jet.hSderiv i)
    (by intro i j k; simpa [jet] using jet.hCs i j k)
    (by intro i j k; simpa [jet] using jet.hCt i j k)
    jet.hvt_s jet.hvs jet.hvs_t jet.hvt jet.hmix_raw jet.hmix

/-- Smooth geodesic-variation curvature commutator with the canonical
`D_s T` field. -/
theorem jacobi_curvComm_geodesic
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {F : Surface M} {S T : Set Real} {s t : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hS : S ∈ 𝓝 s) (hT : T ∈ 𝓝 t) :
    VariationCurvCommAt (I := I) cov hcov F s t
      (fun τ => Lecture07.dsTimeField (I := I) cov F (s, τ)) := by
  refine curvComm_geo (I := I) (cov := cov) (hcov := hcov)
    (DtsV := Lecture07.dtdsTimeFieldIn (I := I) cov (F (s, t)) F s t) hcov1
    hF (hgeo.geoGerm (I := I) hS hT) ?_ ?_
  · filter_upwards with q
    simpa [timeField, Lecture07.surfaceTimeField] using
      Lecture07.SmoothSurface.hasParam_dsTime
        (I := I) (cov := cov) hF q.1 q.2
  · simpa [Lecture07.HasPBTimeCovDerivAt] using
      Lecture07.SmoothSurface.hasTime_dsTime
        (I := I) (cov := cov) hcov1 hF s t

end GlobalGeometry
end RicciFlower
