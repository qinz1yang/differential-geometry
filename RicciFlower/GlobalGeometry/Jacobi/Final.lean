import RicciFlower.GlobalGeometry.Jacobi.Variation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Jacobi-field final assembly

Representative-level compatibility lemmas and final Jacobi-field producers.
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

/-! ## Representative-level identities -/

/-- Representative-level torsion swap.

For a torsion-free pair with zero Lie bracket at the point, the two first
covariant derivatives agree.  This is the algebraic core of
`D_t S = D_s T`. -/
private theorem torsionSwap_rep
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {X Y : GlobalVectorField I M} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (htor : cov.torsion x (X x) (Y x) = 0)
    (hbracket : VectorField.mlieBracket I X Y x = 0) :
    (cov Y x) (X x) = (cov X x) (Y x) := by
  have htor_apply := cov.torsion_apply (I := I) (x := x) hX hY
  rw [htor_apply] at htor
  have hsub : (cov Y x) (X x) - (cov X x) (Y x) = 0 := by
    simpa [hbracket, sub_eq_add_neg] using htor
  exact sub_eq_zero.mp hsub

/-- Representative-level producer for the canonical pullback torsion swap.

If ambient fields realize the time and parameter velocity fields near the
surface point, and the torsion and bracket terms vanish there, then
`D_t S = D_s T` in the frame-defined pullback derivative API. -/
theorem torsionSwap_frame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 t : Real} {X Y : GlobalVectorField I M}
    (hγt : MDifferentiableAt 𝓘(Real, Real) I (timeCurve F s0) t)
    (hγs : MDifferentiableAt 𝓘(Real, Real) I (paramCurve F t) s0)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s0, t)))
    (hY : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) Y (F (s0, t)))
    (hTX : SurfaceFieldRealizedByAt (I := I) F (timeField I F) X (s0, t))
    (hSY : SurfaceFieldRealizedByAt (I := I) F (paramField I F) Y (s0, t))
    (htor : cov.torsion (F (s0, t)) (X (F (s0, t))) (Y (F (s0, t))) = 0)
    (hbracket : VectorField.mlieBracket I X Y (F (s0, t)) = 0) :
    VariationTorsionSwapAt (I := I) cov F s0 t
      (fun τ => (cov X (F (s0, τ))) (curveVelocity I (paramCurve F τ) s0)) := by
  let W : VectorFieldAlong I (timeCurve F s0) :=
    fun τ => (cov X (F (s0, τ))) (curveVelocity I (paramCurve F τ) s0)
  have hTX₀ : timeField I F (s0, t) = X (F (s0, t)) :=
    hTX.self_of_nhds
  have hSY₀ : paramField I F (s0, t) = Y (F (s0, t)) :=
    hSY.self_of_nhds
  have hswap_raw :
      (cov Y (F (s0, t))) (X (F (s0, t))) =
        (cov X (F (s0, t))) (Y (F (s0, t))) :=
    torsionSwap_rep (I := I) (cov := cov)
      (X := X) (Y := Y) (x := F (s0, t))
      (mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hX)
      (mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hY)
      htor hbracket
  have hswap :
      (cov Y (F (s0, t))) (curveVelocity I (timeCurve F s0) t) = W t := by
    have h := hswap_raw
    rw [← hTX₀, ← hSY₀] at h
    simpa [W, timeField, paramField, timeCurve, paramCurve] using h
  have htime :
      HasPBCovAlongAt (I := I) cov (timeCurve F s0)
        (variationField I F s0) t (W t) := by
    have hrep :=
      surfTime_frame (I := I) (cov := cov)
        (F := F) (V := paramField I F) (X := Y)
        (s0 := s0) (t := t) hγt hY hSY
    rw [← hswap]
    simpa [timeRestrictField, variationField, paramField] using hrep
  have hparam :
      HasPBCovAlongAt (I := I) cov (paramCurve F t)
        (paramRestrictField I F (timeField I F) t) s0 (W t) := by
    have hrep :=
      surfParam_frame (I := I) (cov := cov)
        (F := F) (V := timeField I F) (X := X)
        (s := s0) (t0 := t) hγs hX hTX
    simpa [W, paramRestrictField, timeField, paramCurve] using hrep
  exact ⟨htime, hparam⟩

/-- Curvature along a curve computed by smooth ambient representatives. -/
private theorem curvScalar_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hX : X (gamma t) = J t)
    (hY : Y (gamma t) = curveVelocity I gamma t)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) :
    curvatureAlongScalarAt (I := I) cov hcov gamma J t α =
      cotangentToDual (I := I) α
        (connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
          (gamma t)) := by
  simpa [curvatureAlongScalarAt, hX, hY] using
    (Riemann.CovariantDerivative.riemannCurvatureAt_apply_smooth
      (I := I) cov hcov X Y Y α)

/-- The cotangent-tested Jacobi scalar equation for the negative curvature
representative. -/
private theorem jacobiScalar_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hX : X (gamma t) = J t)
    (hY : Y (gamma t) = curveVelocity I gamma t)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) :
    cotangentToDual (I := I) α
        (-(connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
          (gamma t))) +
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0 := by
  let R : TangentSpace I (gamma t) :=
    connectionRiemannCurvatureField (I := I) cov
      (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
      (gamma t)
  change cotangentToDual (I := I) α (-R) +
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0
  rw [curvScalar_rep (I := I) (cov := cov) (hcov := hcov)
    (gamma := gamma) (J := J) (t := t) X Y hX hY α]
  have hdual :
      cotangentToDual (I := I) α (-R) + cotangentToDual (I := I) α R = 0 := by
    rw [map_neg]
    exact neg_add_cancel _
  simpa [cotangentToDual_apply] using hdual

/-- A frame-defined curvature commutator value supplies
`VariationCurvCommAt`.

The derivative witness is already in the canonical pullback API; smooth ambient
representatives are used only to identify the pointwise curvature scalar with
RicciFlower's current `riemannCurvatureAt` tensor API. -/
private theorem curvComm_frame
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {s0 t : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    {A : TangentSpace I (timeCurve F s0 t)}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hWA : HasPBCovAlongAt (I := I) cov (timeCurve F s0) W t A)
    (hA : A =
      -(connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
        (timeCurve F s0 t)))
    (hX : X (timeCurve F s0 t) = variationField I F s0 t)
    (hY : Y (timeCurve F s0 t) = curveVelocity I (timeCurve F s0) t) :
    VariationCurvCommAt (I := I) cov hcov F s0 t W := by
  refine ⟨A, hWA, ?_⟩
  intro α
  rw [hA]
  exact jacobiScalar_rep (I := I) (cov := cov) (hcov := hcov)
    (gamma := timeCurve F s0) (J := variationField I F s0) (t := t)
    X Y hX hY α

/-- A representative-level curvature commutator value supplies
`VariationCurvCommAt`. -/
private theorem curvComm_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {s0 t : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    {A : TangentSpace I (timeCurve F s0 t)}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hWA : HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov
      (timeCurve F s0) W t A)
    (hA : A =
      -(connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
        (timeCurve F s0 t)))
    (hX : X (timeCurve F s0 t) = variationField I F s0 t)
    (hY : Y (timeCurve F s0 t) = curveVelocity I (timeCurve F s0) t) :
    VariationCurvCommAt (I := I) cov hcov F s0 t W :=
  curvComm_frame (I := I) (cov := cov) (hcov := hcov)
    (F := F) (s0 := s0) (t := t) (W := W) (A := A)
    X Y hWA.toPBCov hA hX hY

/-- The formal Jacobi-field theorem for a geodesic variation.

The geometric producer of `hswap` and `hcomm` is intentionally kept separate.
For the current representative-based pullback derivative, smooth surface data
alone is not enough; see the note below. -/
theorem jacobi_of_variation
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {S T : Set Real} {s0 : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    (_hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hswap : ∀ t ∈ T, VariationTorsionSwapAt (I := I) cov F s0 t W)
    (hcomm : ∀ t ∈ T, VariationCurvCommAt (I := I) cov hcov F s0 t W) :
    IsJacobiFieldOn (I := I) cov hcov (timeCurve F s0)
      (variationField I F s0) T := by
  intro t ht
  rcases hcomm t ht with ⟨A, hWA, hscalar⟩
  refine ⟨A, ?_, hscalar⟩
  exact ⟨W, (hswap t ht).1, hWA⟩

/-- A smooth torsion-free geodesic variation has a Jacobi variation field. -/
theorem jacobi_of_smooth_geodesic_variation
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {S T : Set Real} {s0 : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hS : S ∈ 𝓝 s0) (hTopen : IsOpen T) :
    IsJacobiFieldOn (I := I) cov hcov
      (timeCurve F s0) (variationField I F s0) T := by
  let W : VectorFieldAlong I (timeCurve F s0) :=
    fun τ => Lecture07.dsTimeField (I := I) cov F (s0, τ)
  refine jacobi_of_variation (I := I) (cov := cov) (hcov := hcov)
    (F := F) (S := S) (T := T) (s0 := s0) (W := W)
    hgeo ?_ ?_
  · intro t _ht
    exact jacobi_torsionSwap_smooth (I := I) (cov := cov) htf hF
  · intro t ht
    exact jacobi_curvComm_geodesic (I := I) (cov := cov) (hcov := hcov)
      hcov1 hF hgeo hS (hTopen.mem_nhds ht)

/-- Levi-Civita specialization of the smooth geodesic-variation Jacobi theorem. -/
theorem jacobi_of_lc_variation
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} {S T : Set Real} {s0 : Real}
    (hF : SmoothSurface (I := I) F)
    (hgeo : IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) F S T)
    (hS : S ∈ 𝓝 s0) (hTopen : IsOpen T) :
    IsJacobiFieldOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) g)
      (timeCurve F s0) (variationField I F s0) T := by
  let cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov ∞ :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g
  have hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (1 : WithTop ℕ∞) :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) g
  have htf : LeviCivita.IsTorsionFree (I := I) cov :=
    LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree (I := I) g
  exact jacobi_of_smooth_geodesic_variation (I := I)
    (cov := cov) (hcov := hcov) hcov1 htf hF hgeo hS hTopen

/-!
The smooth-surface producer above is the canonical route for Jacobi fields.
The representative-level lemmas below are retained as compatibility tools for
older arguments that already provide ambient section representatives.
-/

end GlobalGeometry
end RicciFlower
