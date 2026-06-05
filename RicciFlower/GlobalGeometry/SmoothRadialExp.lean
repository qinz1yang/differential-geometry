import RicciFlower.Coordinates.Normal.Frontier.SmoothEndpoint
import RicciFlower.GlobalGeometry.Jacobi.Variation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smooth radial exponential packages

This file records the honest radial-exponential data needed before the
book-facing Gauss lemma can be assembled.  A smooth local exponential
diffeomorphism only gives an open source near `0`; the Gauss-lemma variation
also needs an explicit ball source, star-shaped domain facts, and the radial
geodesic statement `t ↦ exp (t • u)`.

The ball-domain facts are proved here.  The remaining producer frontier is the
scaling/geodesic bridge from the smooth endpoint map back to spray-backed
radial geodesics and intrinsic pullback acceleration.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Set
open scoped Manifold ContDiff Topology
open RicciFlower.Coordinates
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-- Ball-based smooth radial exponential data at a point.

The source is a metric ball around `0 : T_xM`, not the arbitrary open source of
the local diffeomorphism.  The radial fields record the extra facts needed for
the Gauss lemma: the curve `t ↦ exp (t • u)` has initial velocity `u`, and has
zero Levi-Civita pullback acceleration at every time whose scaled tangent
argument remains in the ball. -/
structure SmoothRadialExp
    (g : SmoothRiemannianMetric I M) (x : M) where
  radius : Real
  radius_pos : 0 < radius
  exp : TangentSpace I x -> M
  exp_smoothOn :
    ContMDiffOn (modelWithCornersSelf Real (TangentSpace I x)) I
      (∞ : WithTop ℕ∞) exp (Metric.ball (0 : TangentSpace I x) radius)
  exp_zero : exp 0 = x
  radial_velocity0 :
    ∀ u ∈ Metric.ball (0 : TangentSpace I x) radius,
      curveVelocity I (fun t : Real => exp (t • u)) 0 = u
  radial_geodesic_mem :
    ∀ u : TangentSpace I x, ∀ t : Real,
      t • u ∈ Metric.ball (0 : TangentSpace I x) radius →
        HasPBCovAccelAt (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (fun s : Real => exp (s • u)) t 0

namespace SmoothRadialExp

/-- The ball source is star-shaped around zero: the radial segment from `0` to
any vector in the ball remains in the ball for `t ∈ [0,1]`. -/
theorem radialMem
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {u : TangentSpace I x} (hu : u ∈ Metric.ball (0 : TangentSpace I x) D.radius)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    t • u ∈ Metric.ball (0 : TangentSpace I x) D.radius := by
  rw [Metric.mem_ball, dist_zero_right] at hu ⊢
  calc
    ‖t • u‖ = |t| * ‖u‖ := norm_smul t u
    _ = t * ‖u‖ := by rw [abs_of_nonneg ht.1]
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg u)
    _ = ‖u‖ := one_mul _
    _ < D.radius := hu

/-- The normalized radial geodesic statement on `[0,1]`, derived from the
open-time radial geodesic field in `SmoothRadialExp`. -/
theorem radial_geodesic
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {u : TangentSpace I x} (hu : u ∈ Metric.ball (0 : TangentSpace I x) D.radius)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    HasPBCovAccelAt (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      (fun s : Real => D.exp (s • u)) t 0 :=
  D.radial_geodesic_mem u t (D.radialMem hu ht)

/-- Small perturbations of an initial vector still give radial segments inside
the ball source, uniformly for `t ∈ [0,1]`. -/
theorem varMem
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    ∃ δ > 0, ∀ s ∈ Metric.ball (0 : Real) δ,
      ∀ t ∈ Set.Icc (0 : Real) 1,
        t • (v + s • w) ∈ Metric.ball (0 : TangentSpace I x) D.radius := by
  have hnhds :
      Metric.ball (0 : TangentSpace I x) D.radius ∈ 𝓝 v :=
    Metric.isOpen_ball.mem_nhds hv
  have hcont :
      ContinuousAt (fun s : Real => v + s • w) 0 := by
    simpa using
      (continuousAt_const.add (continuousAt_id.smul continuousAt_const))
  have hpre :
      {s : Real | v + s • w ∈
        Metric.ball (0 : TangentSpace I x) D.radius} ∈ 𝓝 (0 : Real) :=
    hcont.preimage_mem_nhds (by simpa using hnhds)
  rw [Metric.mem_nhds_iff] at hpre
  rcases hpre with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht
  exact D.radialMem (hδsub hs) ht

/-- The tangent-space argument of the two-parameter radial variation. -/
def variationArg
    {g : SmoothRiemannianMetric I M} {x : M}
    (_D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) : Real × Real -> TangentSpace I x :=
  fun p : Real × Real => p.2 • (v + p.1 • w)

/-- The tangent-space radial-variation argument is a smooth model-space map. -/
theorem variationArg_contDiff
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) :
    ContDiff Real ∞ (D.variationArg v w) := by
  have hlin : ContDiff Real ∞ (fun p : Real × Real => p.1 • w) :=
    contDiff_fst.smul contDiff_const
  have hsum : ContDiff Real ∞ (fun p : Real × Real => v + p.1 • w) :=
    contDiff_const.add hlin
  simpa [variationArg] using contDiff_snd.smul hsum

/-- The natural open source of the radial variation: the parameter pairs whose
tangent-space argument lies in the radial ball. -/
def variationSource
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) : Set (Real × Real) :=
  {p : Real × Real |
    D.variationArg v w p ∈ Metric.ball (0 : TangentSpace I x) D.radius}

/-- The radial variation source is open. -/
theorem variationSource_open
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) :
    IsOpen (D.variationSource v w) := by
  have hopen :
      IsOpen ((D.variationArg v w) ⁻¹'
        Metric.ball (0 : TangentSpace I x) D.radius) :=
    Metric.isOpen_ball.preimage (D.variationArg_contDiff v w).continuous
  simpa [variationSource, Set.preimage] using hopen

/-- The two-parameter radial variation generated by perturbing the initial
vector and running the radial exponential curve. -/
def variation
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) : Surface M :=
  fun p : Real × Real => D.exp (D.variationArg v w p)

/-- Local smoothness of the radial variation on any set where its tangent-space
argument remains in the radial ball source. -/
theorem variation_contMDiffOn
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x} {U : Set (Real × Real)}
    (hU : U ⊆ {p : Real × Real |
      D.variationArg v w p ∈ Metric.ball (0 : TangentSpace I x) D.radius}) :
    ContMDiffOn 𝓘(Real, Real × Real) I ∞ (D.variation v w) U := by
  have harg :
      ContMDiffOn 𝓘(Real, Real × Real)
        (modelWithCornersSelf Real (TangentSpace I x)) ∞
        (D.variationArg v w) U :=
    (D.variationArg_contDiff v w).contMDiff.contMDiffOn
  exact D.exp_smoothOn.comp harg hU

/-- Smoothness of the radial variation on its natural open source. -/
theorem variation_contMDiffOn_source
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) :
    ContMDiffOn 𝓘(Real, Real × Real) I ∞
      (D.variation v w) (D.variationSource v w) :=
  D.variation_contMDiffOn (by intro p hp; simpa [variationSource] using hp)

/-- Product-set version of `varMem`, convenient for local surface arguments. -/
theorem varMem_prod
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    ∃ δ > 0,
      Metric.ball (0 : Real) δ ×ˢ Set.Icc (0 : Real) 1 ⊆
        {p : Real × Real |
          p.2 • (v + p.1 • w) ∈
            Metric.ball (0 : TangentSpace I x) D.radius} := by
  rcases D.varMem (v := v) (w := w) hv with ⟨δ, hδ, hδmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  exact hδmem p.1 hp.1 p.2 hp.2

/-- Small product neighborhoods of the radial line remain in the natural open
source of the radial variation. -/
theorem varMem_prod_source
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    ∃ δ > 0,
      Metric.ball (0 : Real) δ ×ˢ Set.Icc (0 : Real) 1 ⊆
        D.variationSource v w := by
  rcases D.varMem_prod (v := v) (w := w) hv with ⟨δ, hδ, hδsub⟩
  exact ⟨δ, hδ, by simpa [variationSource, variationArg] using hδsub⟩

/-- For small parameter values, the radial variation is a geodesic variation
on the normalized time interval `[0,1]`. -/
theorem variationGeo
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x} {δ : Real}
    (hδmem : ∀ s ∈ Metric.ball (0 : Real) δ,
      ∀ t ∈ Set.Icc (0 : Real) 1,
        t • (v + s • w) ∈
          Metric.ball (0 : TangentSpace I x) D.radius) :
    IsGeodesicVariationOn (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      (D.variation v w) (Metric.ball (0 : Real) δ) (Set.Icc (0 : Real) 1) := by
  intro s hs t ht
  have hu : v + s • w ∈ Metric.ball (0 : TangentSpace I x) D.radius := by
    simpa using hδmem s hs 1 (by norm_num)
  simpa [variation, timeCurve] using
    SmoothRadialExp.radial_geodesic (D := D) (u := v + s • w) hu ht

/-- At time zero the radial variation is the base point, independently of the
variation parameter. -/
theorem variation_zero
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) (s : Real) :
    D.variation v w (s, 0) = x := by
  simp [variation, variationArg, D.exp_zero]

/-- At time zero, the parameter curve of the radial variation is constant at
the base point. -/
theorem paramCurve_zero
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) :
    paramCurve (D.variation v w) 0 = fun _s : Real => x := by
  funext s
  exact D.variation_zero v w s

/-- The variation field at the initial time of a radial variation is zero. -/
theorem varField_zero
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (v w : TangentSpace I x) :
    variationField I (D.variation v w) 0 0 = 0 := by
  change curveVelocity I (paramCurve (D.variation v w) 0) 0 = 0
  rw [D.paramCurve_zero v w]
  simp

/-- At time zero, the time field of the radial variation is the selected
initial vector. -/
theorem timeField_zero_of_mem
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x} {s : Real}
    (hs : v + s • w ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    timeField I (D.variation v w) (s, 0) = v + s • w := by
  have hcurve :
      timeCurve (D.variation v w) s =
        fun t : Real => D.exp (t • (v + s • w)) := by
    funext t
    simp [timeCurve, variation, variationArg]
  rw [timeField, hcurve]
  exact D.radial_velocity0 (v + s • w) hs

/-- Near the central parameter, the initial-time field of the radial variation
is the affine tangent-space path `s ↦ v + s • w`. -/
theorem timeField_zero_eventually
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    (fun s : Real => timeField I (D.variation v w) (s, 0))
      =ᶠ[𝓝 (0 : Real)] fun s : Real => v + s • w := by
  rcases D.varMem (v := v) (w := w) hv with ⟨δ, hδ, hδmem⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Real) hδ] with s hs
  have hsball : v + s • w ∈ Metric.ball (0 : TangentSpace I x) D.radius := by
    simpa using hδmem s hs 1 (by norm_num)
  exact D.timeField_zero_of_mem hsball

/-- Along the constant initial parameter curve `s ↦ F(s,0) = x`, the
covariant derivative of the initial-time field is the ordinary fiber
derivative `w`. -/
theorem paramTime_zero_hasCov
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) :
    HasPBCovAlongAt (I := I) cov (paramCurve (D.variation v w) 0)
      (paramRestrictField I (D.variation v w) (timeField I (D.variation v w)) 0)
      0 w := by
  classical
  let gamma : Curve M := paramCurve (D.variation v w) 0
  let S : VectorFieldAlong I gamma :=
    paramRestrictField I (D.variation v w) (timeField I (D.variation v w)) 0
  let e := coordinateTrivializationAt (I := I) x
  let b := Module.finBasis Real E
  have hxE : x ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hgamma_eq : gamma = fun _s : Real => x := by
    simpa [gamma] using D.paramCurve_zero v w
  have hgamma_zero : gamma 0 = x := by
    rw [hgamma_eq]
  have hgamma :
      MDifferentiableAt 𝓘(Real, Real) I gamma (0 : Real) := by
    rw [hgamma_eq]
    exact mdifferentiableAt_const
  change HasPBCovDerivAt (I := I) (I' := 𝓘(Real, Real)) cov gamma S
    (0 : Real) (1 : TangentSpace 𝓘(Real, Real) (0 : Real)) w
  apply HasPBCovDerivAt.ofFrame (I := I) (I' := 𝓘(Real, Real))
    (e := e) (b := b)
  refine ⟨?_, hgamma, ?_⟩
  · simpa [gamma, hgamma_eq] using hxE
  · intro k
    let ψ : Real -> Real := fun s =>
      e.localFrame_coeff I b k (gamma s) (S s)
    let ψ₀ : Real -> Real := fun s =>
      e.localFrame_coeff I b k x (v + s • w)
    have hψeq : ψ =ᶠ[𝓝 (0 : Real)] ψ₀ := by
      filter_upwards [D.timeField_zero_eventually (v := v) (w := w) hv] with s hs
      have hgammas : gamma s = x := by
        simpa using congrFun hgamma_eq s
      change e.localFrame_coeff I b k (gamma s) (S s) =
        e.localFrame_coeff I b k x (v + s • w)
      rw [hgammas]
      simp [S, paramRestrictField, hs]
    let L : TangentSpace I x →L[Real] Real :=
      LinearMap.toContinuousLinearMap ((e.basisAt b hxE).coord k)
    have hψ₀_eq : ψ₀ = fun s : Real => L (v + s • w) := by
      funext s
      simp [ψ₀, L, localFrame_coeff_eq_basis_repr (I := I) e b hxE k]
    have hline : HasDerivAt (fun s : Real => v + s • w) w (0 : Real) := by
      change HasDerivAt ((fun _ : Real => v) + fun s : Real => s • w) w (0 : Real)
      have h := (hasDerivAt_const (0 : Real) v).add
        ((hasDerivAt_id (0 : Real)).smul_const w)
      simpa only [id_eq, zero_add, one_smul] using h
    have hψ₀ : HasDerivAt ψ₀ (e.localFrame_coeff I b k x w) (0 : Real) := by
      have hcomp := L.hasFDerivAt.comp_hasDerivAt (0 : Real) hline
      rw [hψ₀_eq]
      simpa [Function.comp_def, L,
        localFrame_coeff_eq_basis_repr (I := I) e b hxE k] using hcomp
    have hψ : HasDerivAt ψ (e.localFrame_coeff I b k x w) (0 : Real) :=
      hψ₀.congr_of_eventuallyEq hψeq
    have hdiff :
        MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real) ψ (0 : Real) :=
      hψ.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
    refine ⟨hdiff, ?_⟩
    have hmf_gamma :
        (mfderiv 𝓘(Real, Real) I gamma (0 : Real))
            (1 : TangentSpace 𝓘(Real, Real) (0 : Real)) =
          (0 : TangentSpace I (gamma 0)) := by
      rw [hgamma_eq]
      simp
    have hframeCoeff :
        frameCoeffDeriv (I := I) (I' := 𝓘(Real, Real)) (M := M)
            e b gamma S (0 : Real)
            (1 : TangentSpace 𝓘(Real, Real) (0 : Real)) k =
          e.localFrame_coeff I b k x w := by
      have hmf := hψ.hasFDerivAt.hasMFDerivAt.mfderiv
      rw [frameCoeffDeriv, extDerivFun_real_eq_mfderiv, hmf]
      exact ContinuousLinearMap.toSpanSingleton_apply_one
        (R₁ := Real) (x := e.localFrame_coeff I b k x w)
    have hsum :
        (∑ j : Fin (Module.finrank Real E),
          e.localFrame_coeff I b j (gamma 0) (S 0) *
            frameGamma (I := I) (M := M) cov e b (gamma 0)
              ((mfderiv 𝓘(Real, Real) I gamma (0 : Real))
                (1 : TangentSpace 𝓘(Real, Real) (0 : Real))) j k) = 0 := by
      simp [hmf_gamma, frameGamma]
    calc
      e.localFrame_coeff I b k (gamma 0) w
          = e.localFrame_coeff I b k x w := by rw [hgamma_zero]
      _ =
          frameCoeffDeriv (I := I) (I' := 𝓘(Real, Real)) (M := M)
              e b gamma S (0 : Real)
              (1 : TangentSpace 𝓘(Real, Real) (0 : Real)) k +
            ∑ j : Fin (Module.finrank Real E),
              e.localFrame_coeff I b j (gamma 0) (S 0) *
                frameGamma (I := I) (M := M) cov e b (gamma 0)
                  ((mfderiv 𝓘(Real, Real) I gamma (0 : Real))
                    (1 : TangentSpace 𝓘(Real, Real) (0 : Real))) j k := by
            rw [hframeCoeff, hsum, add_zero]

/-- The time velocity at the initial time of the central radial curve is the
chosen radial vector. -/
theorem timeVel_zero
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    velocityAlong I (timeCurve (D.variation v w) 0) 0 = v := by
  have hcurve :
      timeCurve (D.variation v w) 0 = fun t : Real => D.exp (t • v) := by
    funext t
    simp [timeCurve, variation, variationArg]
  rw [velocityAlong, hcurve]
  exact D.radial_velocity0 v hv

/-- At time one, the velocity of the central radial curve is the differential
of the radial exponential applied to the radial vector. -/
theorem timeVel_one
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    velocityAlong I (timeCurve (D.variation v w) 0) 1 =
      (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp v) v := by
  let J := modelWithCornersSelf Real (TangentSpace I x)
  have hExp : MDifferentiableAt J I D.exp v := by
    exact (D.exp_smoothOn.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt
      (by simp)
  have hExp' : MDifferentiableAt J I D.exp ((1 : Real) • v) := by
    simpa using hExp
  have hline_deriv : HasDerivAt (fun t : Real => t • v) v (1 : Real) := by
    simpa using (hasDerivAt_id (1 : Real)).smul_const v
  have hline :
      MDifferentiableAt 𝓘(Real, Real) J (fun t : Real => t • v) 1 :=
    hline_deriv.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hline_mf :
      (mfderiv 𝓘(Real, Real) J (fun t : Real => t • v) 1)
          (1 : TangentSpace 𝓘(Real, Real) (1 : Real)) = v := by
    have hmf := hline_deriv.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hmf]
    exact ContinuousLinearMap.toSpanSingleton_apply_one
      (R₁ := Real) (x := v)
  have hcurve :
      timeCurve (D.variation v w) 0 = fun t : Real => D.exp (t • v) := by
    funext t
    simp [timeCurve, variation, variationArg]
  rw [velocityAlong, hcurve]
  have h := mfderiv_comp_apply
    (I := 𝓘(Real, Real)) (I' := J) (I'' := I)
    (g := D.exp) (f := fun t : Real => t • v)
    (x := (1 : Real)) (v := (1 : TangentSpace 𝓘(Real, Real) (1 : Real)))
    hExp' hline
  have h1smul : (1 : Real) • v = v := one_smul Real v
  rw [hline_mf, h1smul] at h
  simpa [curveVelocity, Function.comp_def, J] using h

/-- At time one, the variation field of the radial variation is the differential
of the radial exponential applied to the transverse vector. -/
theorem varField_one
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {v w : TangentSpace I x}
    (hv : v ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    variationField I (D.variation v w) 0 1 =
      (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp v) w := by
  let J := modelWithCornersSelf Real (TangentSpace I x)
  have hExp : MDifferentiableAt J I D.exp v := by
    exact (D.exp_smoothOn.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt
      (by simp)
  have hExp' : MDifferentiableAt J I D.exp (v + (0 : Real) • w) := by
    simpa using hExp
  have hline_deriv : HasDerivAt (fun s : Real => v + s • w) w (0 : Real) := by
    change HasDerivAt ((fun _ : Real => v) + fun s : Real => s • w) w (0 : Real)
    have h := (hasDerivAt_const (0 : Real) v).add
      ((hasDerivAt_id (0 : Real)).smul_const w)
    simpa only [id_eq, zero_add, one_smul] using h
  have hline :
      MDifferentiableAt 𝓘(Real, Real) J (fun s : Real => v + s • w) 0 :=
    hline_deriv.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hline_mf :
      (mfderiv 𝓘(Real, Real) J (fun s : Real => v + s • w) 0)
          (1 : TangentSpace 𝓘(Real, Real) (0 : Real)) = w := by
    have hmf := hline_deriv.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hmf]
    exact ContinuousLinearMap.toSpanSingleton_apply_one
      (R₁ := Real) (x := w)
  have hcurve :
      paramCurve (D.variation v w) 1 =
        fun s : Real => D.exp (v + s • w) := by
    funext s
    simp [paramCurve, variation, variationArg]
  change curveVelocity I (paramCurve (D.variation v w) 1) 0 =
    (mfderiv J I D.exp v) w
  rw [hcurve]
  have h := mfderiv_comp_apply
    (I := 𝓘(Real, Real)) (I' := J) (I'' := I)
    (g := D.exp) (f := fun s : Real => v + s • w)
    (x := (0 : Real)) (v := (1 : TangentSpace 𝓘(Real, Real) (0 : Real)))
    hExp' hline
  have h0smul : (0 : Real) • w = 0 := zero_smul Real w
  rw [hline_mf, h0smul, add_zero] at h
  simpa [curveVelocity, Function.comp_def, J] using h

/-- On vectors in the radial ball, the derivative of the radial exponential at
zero is the identity. -/
theorem mfderiv_zero_apply_of_mem
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    {u : TangentSpace I x}
    (hu : u ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp 0) u = u := by
  let J := modelWithCornersSelf Real (TangentSpace I x)
  have h0 : (0 : TangentSpace I x) ∈ Metric.ball (0 : TangentSpace I x) D.radius := by
    simpa [Metric.mem_ball, dist_self] using D.radius_pos
  have hExp :
      MDifferentiableAt J I D.exp (0 : TangentSpace I x) := by
    exact (D.exp_smoothOn.contMDiffAt (Metric.isOpen_ball.mem_nhds h0)).mdifferentiableAt
      (by simp)
  have hline_deriv : HasDerivAt (fun t : Real => t • u) u (0 : Real) := by
    simpa using (hasDerivAt_id (0 : Real)).smul_const u
  have hline :
      MDifferentiableAt 𝓘(Real, Real) J (fun t : Real => t • u) 0 :=
    hline_deriv.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hExp' :
      MDifferentiableAt J I D.exp ((0 : Real) • u) := by
    simpa using hExp
  have hline_mf :
      (mfderiv 𝓘(Real, Real) J (fun t : Real => t • u) 0)
          (1 : TangentSpace 𝓘(Real, Real) (0 : Real)) = u := by
    have hmf := hline_deriv.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hmf]
    exact ContinuousLinearMap.toSpanSingleton_apply_one
      (R₁ := Real) (x := u)
  have hline_fderiv :
      (fderiv Real (fun t : Real => t • u) 0) (1 : Real) = u := by
    have hf := hline_deriv.hasFDerivAt.fderiv
    rw [hf]
    exact ContinuousLinearMap.toSpanSingleton_apply_one
      (R₁ := Real) (x := u)
  have hchain :
      curveVelocity I (fun t : Real => D.exp (t • u)) 0 =
        (mfderiv J I D.exp 0) u := by
    have h := mfderiv_comp_apply
      (I := 𝓘(Real, Real)) (I' := J) (I'' := I)
      (g := D.exp) (f := fun t : Real => t • u)
      (x := (0 : Real)) (v := (1 : TangentSpace 𝓘(Real, Real) (0 : Real)))
      hExp' hline
    have h0smul : (0 : Real) • u = 0 := zero_smul Real u
    rw [hline_mf, h0smul] at h
    simpa [curveVelocity, Function.comp_def, J, hline_mf] using h
  exact hchain.symm.trans (D.radial_velocity0 u hu)

/-- The derivative of the radial exponential at zero is the identity on the
whole model tangent space. -/
theorem mfderiv_zero_apply
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : SmoothRadialExp (I := I) g x)
    (u : TangentSpace I x) :
    (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp 0) u = u := by
  classical
  let c : Real := D.radius / (2 * (‖u‖ + 1))
  have hden_pos : 0 < 2 * (‖u‖ + 1) := by positivity
  have hc_pos : 0 < c := by
    exact div_pos D.radius_pos hden_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hcu_mem : c • u ∈ Metric.ball (0 : TangentSpace I x) D.radius := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc_nonneg]
    have hnorm_lt : ‖u‖ < ‖u‖ + 1 := by linarith [norm_nonneg u]
    have hmul_lt : c * ‖u‖ < c * (‖u‖ + 1) :=
      mul_lt_mul_of_pos_left hnorm_lt hc_pos
    have hc_mul_den : c * (2 * (‖u‖ + 1)) = D.radius := by
      dsimp [c]
      field_simp [hden_pos.ne']
    have hc_mul : c * (‖u‖ + 1) = D.radius / 2 := by
      nlinarith
    calc
      c * ‖u‖ < c * (‖u‖ + 1) := hmul_lt
      _ = D.radius / 2 := hc_mul
      _ < D.radius := by linarith [D.radius_pos]
  have hcu := D.mfderiv_zero_apply_of_mem hcu_mem
  have hmap :
      (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp 0) (c • u) =
        c • (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp 0) u := by
    exact map_smul _ c u
  rw [hmap] at hcu
  have hscaled := congrArg (fun z : TangentSpace I x => c⁻¹ • z) hcu
  have hscaled' :
      c⁻¹ •
          (c • (mfderiv (modelWithCornersSelf Real (TangentSpace I x)) I D.exp 0) u) =
        c⁻¹ • (c • u) := by
    simpa using hscaled
  simpa [smul_smul, inv_mul_cancel₀ hc_ne] using hscaled'

/-- Frontier producer for local radial variations in the Gauss lemma.

For the radial surface `F(s,t) = D.exp (t • (u + s • w))`, this is the exact
local surface-calculus package needed by the Jacobi scalar argument: a field
`W = D_t J = D_s T` along the central radial geodesic, the torsion-swap data,
the curvature-commutator data, and the initial value `W 0 = w`.

The remaining proof should come from localizing the existing smooth-surface
Jacobi producers to the open source `D.variationSource u w`.  The
constant-base calculation at `t = 0` is checked below once torsion-swap data is
available. -/
theorem variationCommData
    {g : SmoothRiemannianMetric I M} {x : M}
    [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (D : SmoothRadialExp (I := I) g x)
    {u w : TangentSpace I x}
    (hu : u ∈ Metric.ball (0 : TangentSpace I x) D.radius) :
    ∃ W : VectorFieldAlong I (timeCurve (D.variation u w) 0),
      (∀ t ∈ Set.Icc (0 : Real) 1,
        VariationTorsionSwapAt (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (D.variation u w) 0 t W) ∧
      (∀ t ∈ Set.Icc (0 : Real) 1,
        VariationCurvCommAt (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
            (I := I) g)
          (D.variation u w) 0 t W) ∧
      W 0 = w := by
  let cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g
  let W : VectorFieldAlong I (timeCurve (D.variation u w) 0) :=
    fun τ => Lecture07.dsTimeField (I := I) cov (D.variation u w) (0, τ)
  have hsource :
      ∀ t ∈ Set.Icc (0 : Real) 1, (0, t) ∈ D.variationSource u w := by
    intro t ht
    simpa [variationSource, variationArg] using D.radialMem hu ht
  have htorsion :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        VariationTorsionSwapAt (I := I) cov (D.variation u w) 0 t W := by
    intro t ht
    exact jacobi_torsionSwap_contMDiffOn (I := I) (cov := cov)
      (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree (I := I) g)
      (D.variationSource_open u w)
      (D.variation_contMDiffOn_source u w)
      (hsource t ht)
  have hcurv :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        VariationCurvCommAt (I := I) cov hcov (D.variation u w) 0 t W := by
    intro t ht
    have hgeoGerm :
        ∀ᶠ q : Real × Real in 𝓝 ((0, t) : Real × Real),
          HasPBCovAccelAt (I := I) cov
            (timeCurve (D.variation u w) q.1) q.2
            (0 : TangentSpace I ((D.variation u w) q)) := by
      have hUevent :
          ∀ᶠ q : Real × Real in 𝓝 ((0, t) : Real × Real),
            q ∈ D.variationSource u w :=
        (D.variationSource_open u w).mem_nhds (hsource t ht)
      filter_upwards [hUevent] with q hq
      have hmem :
          q.2 • (u + q.1 • w) ∈
            Metric.ball (0 : TangentSpace I x) D.radius := by
        simpa [variationSource, variationArg] using hq
      simpa [cov, variation, timeCurve, variationArg] using
        D.radial_geodesic_mem (u + q.1 • w) q.2 hmem
    exact jacobi_curvComm_contMDiffOn_of_geoGerm
      (I := I) (cov := cov) (hcov := hcov)
      (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) g)
      (D.variationSource_open u w)
      (D.variation_contMDiffOn_source u w)
      (hsource t ht)
      hgeoGerm
  refine ⟨W, ?_, ?_, ?_⟩
  · exact htorsion
  · exact hcurv
  · have h0 : (0 : Real) ∈ Set.Icc (0 : Real) 1 := by norm_num
    have hswap := (htorsion 0 h0).2
    have hconst :=
      D.paramTime_zero_hasCov (g := g) (v := u) (w := w) hu cov
    simpa [cov, HasPBCovAlongAt] using
      (HasPBCovDerivAt.unique (I := I) (I' := 𝓘(Real, Real)) hswap hconst)

end SmoothRadialExp

/-- The remaining producer frontier for `SmoothRadialExp`.

This is the precise missing bridge: use the retained projected model-flow data
for the selected smooth endpoint to identify its radial curves with
spray-backed radial geodesics, then convert the coordinate geodesic equation to
intrinsic pullback acceleration.  The package statement above keeps those facts
explicit instead of deriving them from the weaker relation-valued endpoint. -/
private theorem radial_exp_bridge_of_smoothEndpoint
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M)
    {R τ : Real}
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (_hzero :
      manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
          (0 : TangentSpace I x) = x)
    (_hchart : ∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
      extChartAt I x
          (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v) =
        chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x v)
    {a rModel : NNReal}
    (_hrModel : 0 < rModel)
    (_hflow : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) rModel,
      varModelFlow (E := E) Ψ z 0 = z ∧
        ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
          HasDerivWithinAt
            (varModelFlow (E := E) Ψ z)
            (modelSpray (I := I) g x
              (varModelFlow (E := E) Ψ z t))
            (Set.Icc (-(2 * τ)) (2 * τ)) t)
    (_hbound : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) rModel,
      ∀ t : Real,
        varModelFlow (E := E) Ψ z t ∈
          Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) a)
    (_hsrc : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) rModel,
      ∀ t ∈ Set.Icc (-(2 * τ)) (2 * τ),
        varModelFlow (E := E) Ψ z t ∈
          (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x
            (varModelFlow (E := E) Ψ z t)).proj ∈
            (extChartAt I x).source)
    {r : Real}
    (hrsub : Metric.ball (0 : TangentSpace I x) r ⊆
      Metric.ball (0 : TangentSpace I x) R)
    (_hinitSmall : ∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
      initPhase (I := I) x (τ⁻¹ • v) ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel) :
    (∀ u ∈ Metric.ball (0 : TangentSpace I x) r,
      curveVelocity I
        (fun t : Real =>
          manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x (t • u)) 0 = u) ∧
    (∀ u : TangentSpace I x, ∀ t : Real,
      t • u ∈ Metric.ball (0 : TangentSpace I x) r →
        HasPBCovAccelAt (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (fun s : Real =>
            manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x (s • u)) t 0) := by
  -- Frontier: use the retained `varModelFlow` data plus homogeneous scaling
  -- to identify the displayed radial curve with the model-flow trajectory
  -- from `initPhase x (τ⁻¹ • u)` at time `s * τ`; then convert the resulting
  -- fixed-chart coordinate geodesic equation to intrinsic pullback
  -- acceleration.
  sorry

/-- Existence of a ball-based smooth radial exponential package.

The smooth endpoint and ball source are obtained from the flow-retaining smooth
endpoint package.  The only remaining frontier is the radial scaling/geodesic
bridge isolated in `radial_exp_bridge_of_smoothEndpoint`. -/
theorem exists_smoothRadialExp
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (SmoothRadialExp (I := I) g x) := by
  classical
  obtain ⟨R, hR, τ, hτ, Ψ, hzero, hreal, hchart,
    hmodelData, chartLD, hzero_src, hsrc_ball, hchartLD⟩ :=
    exists_varFlow_smooth_endpoint (I := I) g x
  rcases hchartLD with ⟨hchartLD, _hchartDeriv⟩
  rcases hmodelData with
    ⟨a, rModel, hrModel, hinitSmallR, hflow, hbound, hsrc⟩
  have hnhds : chartLD.source ∈ 𝓝 (0 : TangentSpace I x) :=
    chartLD.open_source.mem_nhds hzero_src
  rw [Metric.mem_nhds_iff] at hnhds
  let rChart : Real := Classical.choose hnhds
  have hrChart : 0 < rChart := (Classical.choose_spec hnhds).1
  have hrChartSub :
      Metric.ball (0 : TangentSpace I x) rChart ⊆ chartLD.source :=
    (Classical.choose_spec hnhds).2
  let r : Real := rChart / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hr_le_chart : r ≤ rChart := by
    dsimp [r]
    linarith
  have hrsubChart :
      Metric.ball (0 : TangentSpace I x) r ⊆ chartLD.source := by
    exact fun v hv => hrChartSub (Metric.ball_subset_ball hr_le_chart hv)
  have hrsubR :
      Metric.ball (0 : TangentSpace I x) r ⊆
        Metric.ball (0 : TangentSpace I x) R := by
    exact fun v hv => hsrc_ball (hrsubChart hv)
  have hinitSmall :
      ∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
        initPhase (I := I) x (τ⁻¹ • v) ∈
          Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) rModel := by
    intro v hv
    exact hinitSmallR v (hrsubR hv)
  let exp : TangentSpace I x -> M :=
    manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
  have hbridge :=
    radial_exp_bridge_of_smoothEndpoint (I := I) g x Ψ hzero hchart hrModel
      hflow hbound hsrc hrsubR hinitSmall
  refine ⟨{
    radius := r
    radius_pos := hr
    exp := exp
    exp_smoothOn := ?_
    exp_zero := by simpa [exp] using hzero
    radial_velocity0 := hbridge.1
    radial_geodesic_mem := hbridge.2
  }⟩
  let extTarget : Set (TangentSpace I x) := (extChartAt I x).target
  let symmT : TangentSpace I x -> M := fun w => (extChartAt I x).symm w
  let candidate : TangentSpace I x -> M := fun v => symmT (chartLD v)
  have hchartLD_ext :
      ∀ v, v ∈ Metric.ball (0 : TangentSpace I x) r ->
        chartLD v = extChartAt I x (exp v) := by
    intro v hv
    have hvsrc : v ∈ chartLD.source := hrsubChart hv
    rw [hchartLD v hvsrc]
    exact (hchart v (hrsubR hv)).symm
  have hchart_maps :
      ∀ v, v ∈ Metric.ball (0 : TangentSpace I x) r -> chartLD v ∈ extTarget := by
    intro v hv
    rw [hchartLD_ext v hv]
    exact (extChartAt I x).map_source (by
      have hcoord : exp v ∈ coordinateFrameSet (I := I) x :=
        expAt_mem_source (I := I) (hreal v (hrsubR hv))
      simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source, exp] using hcoord)
  have hsymmT : ContMDiffOn
      (modelWithCornersSelf Real (TangentSpace I x)) I
      (∞ : WithTop ℕ∞) symmT extTarget := by
    change ContMDiffOn (modelWithCornersSelf Real E) I
      (∞ : WithTop ℕ∞) (extChartAt I x).symm (extChartAt I x).target
    exact contMDiffOn_extChartAt_symm (I := I) (x := x) (n := (∞ : WithTop ℕ∞))
  have hcand : ContMDiffOn
      (modelWithCornersSelf Real (TangentSpace I x)) I
      (∞ : WithTop ℕ∞) candidate (Metric.ball (0 : TangentSpace I x) r) := by
    exact hsymmT.comp (chartLD.contMDiffOn_toFun.mono hrsubChart) hchart_maps
  exact hcand.congr (by
    intro v hv
    change exp v = (extChartAt I x).symm (chartLD v)
    rw [hchartLD_ext v hv]
    exact ((extChartAt I x).left_inv (by
      have hcoord : exp v ∈ coordinateFrameSet (I := I) x :=
        expAt_mem_source (I := I) (hreal v (hrsubR hv))
      simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source, exp] using hcoord)).symm)

end GlobalGeometry
end RicciFlower
