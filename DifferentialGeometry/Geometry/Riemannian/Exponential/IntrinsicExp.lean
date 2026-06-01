import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.TangentNormDiamond

set_option linter.unusedSectionVars false

/-!
# The intrinsic exponential map of a complete Riemannian manifold

The chart-fixed exponential map `expMap g p v = maximalGeodesic g p v 1`
(`Exponential/Definition.lean`) follows the geodesic spray written in the single
chart at `p`.  That object is junk once the geodesic leaves `(chartAt H p).source`,
so on a multi-chart manifold `expMap g p v` reverts to `p` for large `v`.

For the metric-geometry program (e.g. the compactness/diameter theorems) one needs
the *intrinsic* exponential map: the value at `t = 1` of the **complete** geodesic
through `p` with initial velocity `v`, where "complete" means defined on all of `ℝ`
via the moving-foot geodesic predicate `IsGeodesic` (chart-independent).

## Main objects

* `exists_complete_geodesic_at_velocity` — existence of a two-sided complete
  geodesic `Γ : ℝ → M` with `Γ 0 = p` and launch velocity `v`.  Built from the
  local seed `exists_isGeodesicOn_Ioo_at_velocity` and the metric-completeness
  forward/backward extension `isGeodesicOn_Ici_of_complete`.
* `intrinsicGeodesic g p v : ℝ → M` — the chosen complete geodesic.
* `expMapIntrinsic g p v : M := intrinsicGeodesic g p v 1` — the intrinsic
  exponential map.

## Status of this file

The forward/backward completeness extension engine
`HopfRinow.isGeodesicOn_Ici_of_complete` is seeded by a geodesic on a
*left-unbounded* interval `Iio b₀`.  The local seed
`exists_isGeodesicOn_Ioo_at_velocity` only produces a geodesic on a *bounded*
interval `Ioo (-δ) δ`.  Bridging the two — an `Ioo`-seeded completeness engine,
or equivalently a two-sided complete-extension producer — is the single missing
analytic input recorded as the residual of
`exists_complete_geodesic_at_velocity` below.  The downstream definitions and
their specification lemmas are stated against that existential so that, once it
is discharged, the intrinsic exponential map is available with no further work.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Velocity enorm bound from a squared-speed bound (the norm-diamond bridge).**
Given the ambient fibre-norm — square-root inner-product compatibility
`hEnorm : ‖·‖ₑ = ENNReal.ofReal (√(g.inner …))` (the same structural fact threaded
throughout the Hopf-Rinow / Bonnet-Myers pipeline as an explicit hypothesis), a
squared `g`-speed bound `g.inner x w w ≤ c²` (with `c ≥ 0`) yields the fibre
enorm bound `‖w‖ₑ ≤ ENNReal.ofReal c`. -/
private lemma velocity_enorm_le_of_speedSq_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {x : M} {w : TangentSpace I x} {c : ℝ}
    (hc : 0 ≤ c) (hle : g.inner x w w ≤ c ^ 2) :
    ‖w‖ₑ ≤ ENNReal.ofReal c := by
  rw [hEnorm x w]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt (g.inner x w w) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hle
    _ = c := by rw [Real.sqrt_sq hc]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`hreg` data for a constant-speed geodesic extending a seed.**  Given a
local seed `η` (a geodesic on `Ioo a₀ δ`, continuous there) whose squared speed
at the launch time `0` is `g.inner (η 0) (η'(0)) (η'(0)) ≤ c²` (with `c ≥ 0`),
and the ambient fibre-norm — square-root inner-product compatibility `hEnorm`,
every geodesic `γ` on `Ioo a₀ b` that is continuous there and agrees with `η` on
the agreement window has constant `g`-speed `≤ c²`, is `C¹`, and has its velocity
enorm bounded by `c`.  This is exactly the per-extension analytic record
`isGeodesicOn_Ici_of_complete_Ioo` consumes. -/
private lemma isGeodesicOn_hreg_record
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {η γ : ℝ → M} {a₀ δ b c : ℝ}
    (ha₀ : a₀ < 0) (hδ : 0 < δ) (hc_nonneg : 0 ≤ c)
    (hηspeed : (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) ≤ c ^ 2)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b))
    (hγ_cont : ContinuousOn γ (Set.Ioo a₀ b)) (hb : 0 < b)
    (hagree : ∀ t, a₀ < t → t < δ → t < b → γ t = η t) :
    ∃ c : ℝ, 0 ≤ c ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo a₀ b) ∧
      (∀ τ ∈ Set.Ioo a₀ b, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ ≤ ENNReal.ofReal c) ∧
      (∀ s ∈ Set.Ioo a₀ b, (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2) := by
  have hagree_nhds : γ =ᶠ[nhds (0 : ℝ)] η := by
    have hwin_open : IsOpen (Set.Ioo a₀ (min δ b)) := isOpen_Ioo
    have hwin_mem : (0 : ℝ) ∈ Set.Ioo a₀ (min δ b) := ⟨ha₀, lt_min hδ hb⟩
    refine Filter.eventually_of_mem (hwin_open.mem_nhds hwin_mem) ?_
    intro t ht
    exact hagree t ht.1 (lt_of_lt_of_le ht.2 (min_le_left _ _))
      (lt_of_lt_of_le ht.2 (min_le_right _ _))
  have hγ0 : γ 0 = η 0 := hagree_nhds.eq_of_nhds
  have hmfderiv0 : mfderiv 𝓘(ℝ, ℝ) I γ 0 = mfderiv 𝓘(ℝ, ℝ) I η 0 :=
    hagree_nhds.mfderiv_eq
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo a₀ b) :=
    HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g isOpen_Ioo hγ hγ_cont
  have hspeedSq : ∀ s ∈ Set.Ioo a₀ b,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
        ≤ c ^ 2 := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Set.Ioo a₀ b := ⟨ha₀, hb⟩
    have hIcc : Set.Icc (min 0 s) (max 0 s) ⊆ Set.Ioo a₀ b := by
      have hmin : min (0 : ℝ) s ∈ Set.Ioo a₀ b := by
        rcases le_total (0 : ℝ) s with h | h
        · rwa [min_eq_left h]
        · rwa [min_eq_right h]
      have hmax : max (0 : ℝ) s ∈ Set.Ioo a₀ b := by
        rcases le_total (0 : ℝ) s with h | h
        · rwa [max_eq_right h]
        · rwa [max_eq_left h]
      exact (Set.ordConnected_Ioo).out hmin hmax
    have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g (t₀ := 0) (t₁ := s)
      isOpen_Ioo hγ hγ_C1 hIcc
    rw [← hconst, hγ0, hmfderiv0]
    exact hηspeed
  refine ⟨c, hc_nonneg, hγ_C1, ?_, hspeedSq⟩
  intro τ hτ
  exact velocity_enorm_le_of_speedSq_le (I := I) g hEnorm hc_nonneg (hspeedSq τ hτ)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Two-sided geodesic completeness.**  On a complete Riemannian manifold,
for every base point `p` and tangent vector `v : T_p M` there is a geodesic
`Γ : ℝ → M` defined on all of `ℝ` with `Γ 0 = p` and launch velocity `v`
(`mfderiv Γ 0 1 = v`).

This is the chart-independent, genuinely complete object that the chart-fixed
`expMap` fails to provide: it follows the moving-foot geodesic equation at every
real time, so it remains valid after the geodesic leaves the home chart at `p`.

The fibre-norm — square-root inner-product compatibility `hEnorm` ties the
ambient bundle norm `‖·‖ₑ` to the metric `g` (the same structural hypothesis
threaded throughout the Hopf-Rinow / Bonnet-Myers pipeline); without it the
ambient norm is unrelated to `g`, so it is a genuine mathematical input rather
than a packaging of the conclusion.

CONSTRUCTION:

* SEED: `HopfRinow.exists_isGeodesicOn_Ioo_at_velocity g p v` gives a local
  geodesic `η` on `Ioo (-δ) δ` with `η 0 = p` and `mfderiv η 0 1 = v`.
* FORWARD: `HopfRinow.isGeodesicOn_Ici_of_complete_Ioo` (the `Ioo`-seeded
  forward-completeness engine) extends `η` to a geodesic on `Ioi (-δ/2)`,
  agreeing with `η` below `δ`.  Its per-extension regularity record is the
  constant-speed `hreg` data supplied by `isGeodesicOn_hreg_record`.
* BACKWARD: the same engine applied to the time-reversal `t ↦ η (-t)` extends
  left; reflecting gives a geodesic on `Iio (δ/2)`.
* GLUE at `0`: both halves agree with `η` on `Ioo (-δ/2) (δ/2)`, so the
  `if t < 0` assembly is a geodesic on all of `ℝ` (checked pointwise by
  locality), preserving the value `p` and velocity `v` at `0`. -/
theorem exists_complete_geodesic_at_velocity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ∃ Γ : ℝ → M, IsGeodesic (I := I) g Γ ∧ Γ 0 = p ∧
      (mfderiv 𝓘(ℝ, ℝ) I Γ 0 (1 : ℝ) : E) = (v : E) ∧ Continuous Γ := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, δ, hδ, hη0, _hηcont0, hηv, hη_mdiff, _hη_src, hη_geo⟩ :=
    HopfRinow.exists_isGeodesicOn_Ioo_at_velocity (I := I) g p v
  have hη_cont : ContinuousOn η (Set.Ioo (-δ) δ) :=
    fun t ht => (hη_mdiff t ht).continuousAt.continuousWithinAt
  have h0_mem_seed : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hη_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I η 0 := hη_mdiff 0 h0_mem_seed
  set a₀ : ℝ := -δ / 2 with ha₀_def
  have ha₀_neg : a₀ < 0 := by rw [ha₀_def]; linarith
  have ha₀_gt : -δ < a₀ := by rw [ha₀_def]; linarith
  set c : ℝ := Real.sqrt ((g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
    (mfderiv 𝓘(ℝ, ℝ) I η 0 1)) with hc_def
  have hspeed0_nonneg : 0 ≤ (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rcases eq_or_ne (mfderiv 𝓘(ℝ, ℝ) I η 0 1) 0 with hz | hz
    · rw [hz]; simp
    · exact (g.pos (η 0) _ hz).le
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hc_sq : c ^ 2 = (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rw [hc_def, Real.sq_sqrt hspeed0_nonneg]
  have hηspeed_le : (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) ≤ c ^ 2 := le_of_eq hc_sq.symm
  have hη_geo' : IsGeodesicOn (I := I) g η (Set.Ioo a₀ δ) :=
    hη_geo.mono (fun t ht => ⟨lt_trans ha₀_gt ht.1, ht.2⟩)
  have hη_cont' : ContinuousOn η (Set.Ioo a₀ δ) :=
    hη_cont.mono (fun t ht => ⟨lt_trans ha₀_gt ht.1, ht.2⟩)
  obtain ⟨Γf, hΓf_geo, hΓf_cont, hΓf_agree⟩ :=
    HopfRinow.isGeodesicOn_Ioi_of_endpointContinuation (I := I) g ha₀_neg hδ
      hη_geo' hη_cont'
      (fun γ b hb hγ hγ_cont hagree => by
        obtain ⟨c', hc'_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ :=
          isGeodesicOn_hreg_record (I := I) g hEnorm ha₀_neg hδ hc_nonneg hηspeed_le
            hγ hγ_cont hb (fun t _ht_a₀ ht_δ ht_b => hagree t ht_δ ht_b)
        exact HopfRinow.hasEndpointContinuation_of_complete (I := I) g
          (lt_trans ha₀_neg hb) hc'_nonneg hγ_smooth hSpeedBound hSpeedSq hγ)
  set ηr : ℝ → M := fun t => η (-t) with hηr_def
  have hηr_geo_full : IsGeodesicOn (I := I) g ηr (Set.Ioo (-δ) δ) := by
    have h := isGeodesicOn_comp_neg (I := I) (g := g) (γ := η) (s := Set.Ioo (-δ) δ) hη_geo
    refine h.mono ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hηr_geo' : IsGeodesicOn (I := I) g ηr (Set.Ioo a₀ δ) :=
    hηr_geo_full.mono (fun t ht => ⟨lt_trans ha₀_gt ht.1, ht.2⟩)
  have hηr_cont' : ContinuousOn ηr (Set.Ioo a₀ δ) := by
    refine ContinuousOn.comp hη_cont (continuous_neg.continuousOn) ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1, ha₀_gt]⟩
  have hηr0 : ηr 0 = p := by simp [hηr_def, neg_zero, hη0]
  have hηr_mfderiv : mfderiv 𝓘(ℝ, ℝ) I ηr 0
      = (mfderiv 𝓘(ℝ, ℝ) I η 0).comp (- ContinuousLinearMap.id ℝ ℝ) := by
    have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s)
        (0 : ℝ) (- ContinuousLinearMap.id ℝ ℝ) := by
      rw [hasMFDerivAt_iff_hasFDerivAt]
      simpa using (hasFDerivAt_id (0 : ℝ)).neg
    have hη_at : HasMFDerivAt 𝓘(ℝ, ℝ) I η (-(0 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I η 0) := by
      rw [neg_zero]; exact hη_mdiff0.hasMFDerivAt
    have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I ηr 0
        ((mfderiv 𝓘(ℝ, ℝ) I η 0).comp (- ContinuousLinearMap.id ℝ ℝ)) :=
      hη_at.comp 0 hneg
    exact hcomp.mfderiv
  have hηr_val : mfderiv 𝓘(ℝ, ℝ) I ηr 0 1 = -(mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rw [hηr_mfderiv]
    change (mfderiv 𝓘(ℝ, ℝ) I η 0) ((- ContinuousLinearMap.id ℝ ℝ) 1)
      = -(mfderiv 𝓘(ℝ, ℝ) I η 0 1)
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
    exact map_neg (mfderiv 𝓘(ℝ, ℝ) I η 0) 1
  have hηr_speed0 : (g.inner (ηr 0)) (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1)
      = (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1) (mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rw [hηr_val, hηr0, hη0]
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  have hηr_speed_le : (g.inner (ηr 0)) (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1) ≤ c ^ 2 := by rw [hηr_speed0]; exact hηspeed_le
  obtain ⟨Γrf, hΓrf_geo, hΓrf_cont, hΓrf_agree⟩ :=
    HopfRinow.isGeodesicOn_Ioi_of_endpointContinuation (I := I) g ha₀_neg hδ
      hηr_geo' hηr_cont'
      (fun γ b hb hγ hγ_cont hagree => by
        obtain ⟨c', hc'_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ :=
          isGeodesicOn_hreg_record (I := I) g hEnorm ha₀_neg hδ hc_nonneg hηr_speed_le
            hγ hγ_cont hb (fun t _ht_a₀ ht_δ ht_b => hagree t ht_δ ht_b)
        exact HopfRinow.hasEndpointContinuation_of_complete (I := I) g
          (lt_trans ha₀_neg hb) hc'_nonneg hγ_smooth hSpeedBound hSpeedSq hγ)
  set Γb : ℝ → M := fun t => Γrf (-t) with hΓb_def
  have hΓb_geo : IsGeodesicOn (I := I) g Γb (Set.Iio (-a₀)) := by
    have h := isGeodesicOn_comp_neg (I := I) (g := g) (γ := Γrf) (s := Set.Ioi a₀)
      hΓrf_geo
    refine h.mono ?_
    intro t ht
    simp only [Set.mem_preimage, Set.mem_Ioi]
    linarith [Set.mem_Iio.mp ht]
  have hΓb_cont : ContinuousOn Γb (Set.Iio (-a₀)) := by
    refine ContinuousOn.comp hΓrf_cont continuous_neg.continuousOn ?_
    intro t ht
    simp only [Set.mem_Ioi]
    linarith [Set.mem_Iio.mp ht]
  have hΓb_agree : ∀ t, -δ < t → Γb t = η t := by
    intro t ht
    have hlt : -t < δ := by linarith
    change Γrf (-t) = η t
    rw [hΓrf_agree (-t) hlt]
    change η (- -t) = η t
    rw [neg_neg]
  have hΓf_agree' : ∀ t, t < δ → Γf t = η t := hΓf_agree
  have hma₀ : -a₀ = δ / 2 := by rw [ha₀_def]; ring
  have hδ2_pos : (0 : ℝ) < δ / 2 := by linarith
  set Γ : ℝ → M := fun t => if t < 0 then Γb t else Γf t with hΓ_def
  have hΓ_eq_η : ∀ t, -δ < t → t < δ → Γ t = η t := by
    intro t ht_lo ht_hi
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · rw [hΓ_def]; simp only [if_pos hlt]; exact hΓb_agree t ht_lo
    · subst heq; rw [hΓ_def]; simp only [lt_irrefl, if_false]
      exact hΓf_agree' 0 hδ
    · rw [hΓ_def]; simp only [if_neg (not_lt.mpr hgt.le)]; exact hΓf_agree' t ht_hi
  have h0_win : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith [hδ], hδ⟩
  have hΓ_nhds_η : Γ =ᶠ[nhds (0 : ℝ)] η := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0_win) ?_
    intro t ht; exact hΓ_eq_η t ht.1 ht.2
  have hΓ_geo : IsGeodesic (I := I) g Γ := by
    intro t
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · have hΓΓb : Γ =ᶠ[nhds t] Γb := by
        refine Filter.eventually_of_mem (isOpen_Iio.mem_nhds hlt) ?_
        intro s hs; rw [hΓ_def]; simp only [if_pos (Set.mem_Iio.mp hs)]
      refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := Γb) ?_ hΓΓb ?_
      · rw [hΓ_def]; simp only [if_pos hlt]
      · exact hΓb_geo t (Set.mem_Iio.mpr (by rw [hma₀]; linarith))
    · subst heq
      refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := η)
        hΓ_nhds_η.eq_of_nhds hΓ_nhds_η ?_
      exact hη_geo 0 h0_mem_seed
    · have hΓΓf : Γ =ᶠ[nhds t] Γf := by
        refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hgt) ?_
        intro s hs; rw [hΓ_def]; simp only [if_neg (not_lt.mpr (le_of_lt (Set.mem_Ioi.mp hs)))]
      refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := Γf) ?_ hΓΓf ?_
      · rw [hΓ_def]; simp only [if_neg (not_lt.mpr hgt.le)]
      · exact hΓf_geo t (Set.mem_Ioi.mpr (lt_trans ha₀_neg hgt))
  have hΓb0 : Γb 0 = p := by
    have := hΓb_agree 0 (by linarith [hδ]); rw [this, hη0]
  have hΓf0 : Γf 0 = p := by
    have := hΓf_agree' 0 hδ; rw [this, hη0]
  have hΓb_cont_Iic : ContinuousOn Γb {x : ℝ | x ≤ 0} := by
    refine hΓb_cont.mono ?_
    intro x hx; exact Set.mem_Iio.mpr (lt_of_le_of_lt hx (by rw [hma₀]; exact hδ2_pos))
  have hΓf_cont_Ici : ContinuousOn Γf {x : ℝ | (0 : ℝ) ≤ x} := by
    refine hΓf_cont.mono ?_
    intro x hx; exact Set.mem_Ioi.mpr (lt_of_lt_of_le ha₀_neg hx)
  have hΓ_cont : Continuous Γ := by
    have hsplice : ∀ x : ℝ, (fun t : ℝ => t) x = (fun _ : ℝ => (0 : ℝ)) x →
        Γb x = Γf x := by
      intro x hx
      have hx0 : x = 0 := hx
      rw [hx0, hΓb0, hΓf0]
    have hglue : Continuous (fun t : ℝ => if t ≤ 0 then Γb t else Γf t) := by
      have := continuous_if_le (f := fun t : ℝ => t) (g := fun _ : ℝ => (0 : ℝ))
        (f' := Γb) (g' := Γf) continuous_id continuous_const
        hΓb_cont_Iic hΓf_cont_Ici hsplice
      simpa using this
    refine hglue.congr (fun t => ?_)
    have hΓt : Γ t = if t < 0 then Γb t else Γf t := by rw [hΓ_def]
    rw [hΓt]
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · rw [if_pos hlt.le, if_pos hlt]
    · subst heq; rw [if_pos le_rfl, if_neg (lt_irrefl 0), hΓf0, hΓb0]
    · rw [if_neg (not_le.mpr hgt), if_neg (not_lt.mpr hgt.le)]
  refine ⟨Γ, hΓ_geo, ?_, ?_, hΓ_cont⟩
  · rw [hΓ_nhds_η.eq_of_nhds, hη0]
  · rw [show mfderiv 𝓘(ℝ, ℝ) I Γ 0 = mfderiv 𝓘(ℝ, ℝ) I η 0 from hΓ_nhds_η.mfderiv_eq]
    exact hηv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic complete geodesic through `p` with launch velocity `v`,
chosen by `exists_complete_geodesic_at_velocity`.  The hypothesis `hEnorm` is the
ambient fibre-norm — square-root inner-product compatibility tying the ambient
bundle norm to `g` (the same structural fact used across the Hopf-Rinow /
Bonnet-Myers pipeline). -/
def intrinsicGeodesic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) : ℝ → M :=
  Classical.choose (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic is a geodesic on all of `ℝ`. -/
theorem intrinsicGeodesic_isGeodesic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    IsGeodesic (I := I) g (intrinsicGeodesic (I := I) g hEnorm p v) :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)).1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic starts at `p` (value at `t = 0`). -/
@[simp] theorem intrinsicGeodesic_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    intrinsicGeodesic (I := I) g hEnorm p v 0 = p :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)).2.1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The launch velocity of the intrinsic geodesic at `t = 0` is `v`. -/
theorem intrinsicGeodesic_mfderiv_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) 0 (1 : ℝ) : E)
      = (v : E) :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)).2.2.1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic exponential map at `p`: the value at `t = 1` of the complete
geodesic through `p` with launch velocity `v`.  Unlike the chart-fixed `expMap`,
this follows the geodesic across charts and is the object used by the
metric-geometry (compactness / diameter) theorems. -/
def expMapIntrinsic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) : M :=
  intrinsicGeodesic (I := I) g hEnorm p v 1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
@[simp] theorem expMapIntrinsic_def
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    expMapIntrinsic (I := I) g hEnorm p v = intrinsicGeodesic (I := I) g hEnorm p v 1 := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Continuity of the intrinsic geodesic.  The complete geodesic
`exists_complete_geodesic_at_velocity` produces is the half-line glue of the
forward / backward cross-chart extensions, each continuous on its open half-line
(the per-extension continuity tracked by `isGeodesicOn_Ioi_of_endpointContinuation`);
the two halves agree at the splice point, so the glue is continuous.  This is the
regularity datum feeding the `C¹`-in-time lemma below. -/
theorem intrinsicGeodesic_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    Continuous (intrinsicGeodesic (I := I) g hEnorm p v) :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)).2.2.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic is `C¹` in time on all of `ℝ`.  A geodesic, continuous
on the open set `Set.univ`, is `ContMDiffOn 𝓘(ℝ,ℝ) I 1` there by
`HopfRinow.isGeodesicOn_contMDiffOn_one`. -/
theorem intrinsicGeodesic_contMDiffOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (intrinsicGeodesic (I := I) g hEnorm p v) Set.univ := by
  refine HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g isOpen_univ ?_ ?_
  · exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn Set.univ
  · exact (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

section AgreementBridge

open DifferentialGeometry.Geometry.Riemannian.AlongCurve

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Chart-`q`-phase ODE for a moving-foot geodesic.**  Fix a chart basepoint
`q : M`.  If `γ` satisfies the moving-foot geodesic equation at every time in an
open neighbourhood `O` of `t`, is continuous there, and keeps its foot in the
chart source `(chartAt H q).source` throughout `O`, then the chart-`q`-phase
curve `c(s) = (chartCurve q γ s, deriv (chartCurve q γ) s)` satisfies, eventually
as `s → t`, the chart-phase geodesic ODE `HasDerivAt c (chartPhaseVF g q (c s)) s`
with `c s` staying inside the chart-target interior product. -/
theorem chartPhase_eventually_of_geodesicOn
    (g : SmoothRiemannianMetric I M) (q : M) {γ : ℝ → M} {O : Set ℝ} {t : ℝ}
    (hO_open : IsOpen O) (htO : t ∈ O)
    (hγ_cont : ContinuousOn γ O)
    (hsrc : ∀ s ∈ O, γ s ∈ (chartAt H q).source)
    (hgeo : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γ s) :
    ∀ᶠ s in 𝓝 t,
      HasDerivAt (fun r => (chartCurve (I := I) q γ r, deriv (chartCurve (I := I) q γ) r))
        (Geodesic.chartPhaseVF (I := I) g q
          (chartCurve (I := I) q γ s, deriv (chartCurve (I := I) q γ) s)) s ∧
      (chartCurve (I := I) q γ s, deriv (chartCurve (I := I) q γ) s)
        ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) := by
  classical
  set w : ℝ → E := chartCurve (I := I) q γ with hw_def
  have hO_nhds : O ∈ 𝓝 t := hO_open.mem_nhds htO
  have hsrc_ev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H q).source := by
    filter_upwards [hO_nhds] with s hs; exact hsrc s hs
  have hγ_contAt : ContinuousAt γ t :=
    (hγ_cont t htO).continuousAt hO_nhds
  have hev_first : ∀ᶠ s in 𝓝 t, HasDerivAt w (deriv w s) s :=
    Geodesic.hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g q
      hγ_contAt (hsrc t htO) (hgeo t htO)
  have hgeo_ev : ∀ᶠ s in 𝓝 t, Geodesic.HasGeodesicEquationAt (I := I) g γ s := by
    filter_upwards [hO_nhds] with s hs; exact hgeo s hs
  have hcontAt_ev : ∀ᶠ s in 𝓝 t, ContinuousAt γ s := by
    filter_upwards [hO_nhds] with s hs
    exact (hγ_cont s hs).continuousAt (hO_open.mem_nhds hs)
  have hev_second : ∀ᶠ s in 𝓝 t,
      HasDerivAt (deriv w)
        (- Geodesic.chartChristoffelContraction (I := I) g q (deriv w s) (deriv w s)
            (w s)) s := by
    filter_upwards [hsrc_ev, hgeo_ev, hcontAt_ev] with s hsrcs hgeos hcs
    exact Geodesic.hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g q
      hcs hsrcs hgeos
  filter_upwards [hev_first, hev_second, hsrc_ev] with s hf hsd hsrcs
  refine ⟨?_, ?_⟩
  · have hpair : HasDerivAt (fun r => (w r, deriv w r))
        ((deriv w s,
          - Geodesic.chartChristoffelContraction (I := I) g q (deriv w s) (deriv w s)
              (w s))) s := hf.prodMk hsd
    have hrhs : Geodesic.chartPhaseVF (I := I) g q (w s, deriv w s) =
        (deriv w s,
          - Geodesic.chartChristoffelContraction (I := I) g q (deriv w s) (deriv w s)
              (w s)) := by
      simp only [Geodesic.chartPhaseVF_apply]
    rw [hrhs]; exact hpair
  · refine ⟨?_, Set.mem_univ _⟩
    have hp_ext_src : γ s ∈ (extChartAt I q).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrcs
    have hp_target : extChartAt I q (γ s) ∈ (extChartAt I q).target :=
      (extChartAt I q).map_source hp_ext_src
    have hws : w s = extChartAt I q (γ s) := by rw [hw_def, chartCurve_def]
    rw [hws]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) q hp_target

/-- **Chart-phase ODE uniqueness re-centred at a base time `t`.**  The
neighbourhood-of-`0` chart-coordinate ODE uniqueness
`Geodesic.chartPhaseVF_orbit_uniqueness` re-based at an arbitrary base time `t`
by the time-shift `s ↦ s + t`.  Two chart-phase ODE solutions agreeing at `t` and
staying in the chart-target interior product near `t` agree on a neighbourhood of
`t`. -/
theorem chartPhaseVF_orbit_uniqueness_at
    {g : SmoothRiemannianMetric I M} {q : M}
    {c₁ c₂ : ℝ → E × E} {z₀ : E × E} {t : ℝ}
    (hz₀ : z₀ ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E))
    (h1 : c₁ t = z₀) (h2 : c₂ t = z₀)
    (hd1 : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₁ (Geodesic.chartPhaseVF (I := I) g q (c₁ s)) s ∧
        c₁ s ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E))
    (hd2 : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₂ (Geodesic.chartPhaseVF (I := I) g q (c₂ s)) s ∧
        c₂ s ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E)) :
    c₁ =ᶠ[𝓝 t] c₂ := by
  classical
  set d₁ : ℝ → E × E := fun s => c₁ (s + t) with hd₁_def
  set d₂ : ℝ → E × E := fun s => c₂ (s + t) with hd₂_def
  have hshift : Filter.Tendsto (fun s : ℝ => s + t) (𝓝 0) (𝓝 t) := by
    have h := (continuous_add_const t).tendsto (0 : ℝ)
    simpa using h
  have he1 : d₁ 0 = z₀ := by simp [hd₁_def, h1]
  have he2 : d₂ 0 = z₀ := by simp [hd₂_def, h2]
  have hdd1 : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt d₁ (Geodesic.chartPhaseVF (I := I) g q (d₁ s)) s ∧
        d₁ s ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hshift.eventually hd1] with s hs
    obtain ⟨hder, hmem⟩ := hs
    refine ⟨?_, hmem⟩
    have hadd : HasDerivAt (fun r : ℝ => r + t) 1 s := by
      simpa using (hasDerivAt_id s).add_const t
    have hcomp := HasDerivAt.scomp s hder hadd
    simpa [hd₁_def, mul_one] using hcomp
  have hdd2 : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt d₂ (Geodesic.chartPhaseVF (I := I) g q (d₂ s)) s ∧
        d₂ s ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hshift.eventually hd2] with s hs
    obtain ⟨hder, hmem⟩ := hs
    refine ⟨?_, hmem⟩
    have hadd : HasDerivAt (fun r : ℝ => r + t) 1 s := by
      simpa using (hasDerivAt_id s).add_const t
    have hcomp := HasDerivAt.scomp s hder hadd
    simpa [hd₂_def, mul_one] using hcomp
  have hdeq : d₁ =ᶠ[𝓝 (0 : ℝ)] d₂ :=
    chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := q) hz₀ he1 he2 hdd1 hdd2
  have hshift2 : Filter.Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have h := (continuous_add_const (-t)).tendsto t
    simpa [sub_eq_add_neg] using h
  filter_upwards [hshift2.eventually hdeq] with s hs
  simp only [hd₁_def, hd₂_def] at hs
  simpa using hs

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Local continuity of the chart-`q`-phase curve of a moving-foot geodesic.**
Under the hypotheses of `chartPhase_eventually_of_geodesicOn`, the chart-`q`-phase
curve `c(s) = (chartCurve q γ s, deriv (chartCurve q γ) s)` is continuous at `t`.
This is the closedness input for the clopen agreement-set propagation. -/
private theorem chartPhase_continuousAt_of_geodesicOn
    (g : SmoothRiemannianMetric I M) (q : M) {γ : ℝ → M} {O : Set ℝ} {t : ℝ}
    (hO_open : IsOpen O) (htO : t ∈ O)
    (hγ_cont : ContinuousOn γ O)
    (hsrc : ∀ s ∈ O, γ s ∈ (chartAt H q).source)
    (hgeo : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γ s) :
    ContinuousAt
      (fun r => (chartCurve (I := I) q γ r, deriv (chartCurve (I := I) q γ) r)) t := by
  have hev := chartPhase_eventually_of_geodesicOn (I := I) g q hO_open htO hγ_cont hsrc hgeo
  exact (hev.self_of_nhds.1).continuousAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Local agreement of two moving-foot geodesics with matching chart-`q`
phase.**  Fix a chart basepoint `q`.  If `γ₁, γ₂` are continuous moving-foot
geodesics on an open neighbourhood `O` of `t`, both keeping their feet in
`(chartAt H q).source` on `O`, and their chart-`q`-phase curves agree at `t`,
then `γ₁ =ᶠ[𝓝 t] γ₂`. -/
private theorem geodesic_eventuallyEq_of_chartPhase_eq
    (g : SmoothRiemannianMetric I M) (q : M) {γ₁ γ₂ : ℝ → M} {O : Set ℝ} {t : ℝ}
    (hO_open : IsOpen O) (htO : t ∈ O)
    (hγ₁_cont : ContinuousOn γ₁ O) (hγ₂_cont : ContinuousOn γ₂ O)
    (hsrc₁ : ∀ s ∈ O, γ₁ s ∈ (chartAt H q).source)
    (hsrc₂ : ∀ s ∈ O, γ₂ s ∈ (chartAt H q).source)
    (hgeo₁ : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γ₁ s)
    (hgeo₂ : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γ₂ s)
    (hphase :
      (chartCurve (I := I) q γ₁ t, deriv (chartCurve (I := I) q γ₁) t)
        = (chartCurve (I := I) q γ₂ t, deriv (chartCurve (I := I) q γ₂) t)) :
    γ₁ =ᶠ[𝓝 t] γ₂ := by
  classical
  set c₁ : ℝ → E × E :=
    fun s => (chartCurve (I := I) q γ₁ s, deriv (chartCurve (I := I) q γ₁) s) with hc₁_def
  set c₂ : ℝ → E × E :=
    fun s => (chartCurve (I := I) q γ₂ s, deriv (chartCurve (I := I) q γ₂) s) with hc₂_def
  have hd1 := chartPhase_eventually_of_geodesicOn (I := I) g q hO_open htO hγ₁_cont hsrc₁ hgeo₁
  have hd2 := chartPhase_eventually_of_geodesicOn (I := I) g q hO_open htO hγ₂_cont hsrc₂ hgeo₂
  set z₀ : E × E := c₁ t with hz₀_def
  have hz₀_mem : z₀ ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) :=
    (hd1.self_of_nhds).2
  have h1 : c₁ t = z₀ := rfl
  have h2 : c₂ t = z₀ := by rw [hz₀_def]; exact hphase.symm
  have hceq : c₁ =ᶠ[𝓝 t] c₂ :=
    chartPhaseVF_orbit_uniqueness_at (I := I) (g := g) (q := q) hz₀_mem h1 h2 hd1 hd2
  have hsrc₁_ev : ∀ᶠ s in 𝓝 t, γ₁ s ∈ (chartAt H q).source := by
    filter_upwards [hO_open.mem_nhds htO] with s hs; exact hsrc₁ s hs
  have hsrc₂_ev : ∀ᶠ s in 𝓝 t, γ₂ s ∈ (chartAt H q).source := by
    filter_upwards [hO_open.mem_nhds htO] with s hs; exact hsrc₂ s hs
  filter_upwards [hceq, hsrc₁_ev, hsrc₂_ev] with s hs hs₁ hs₂
  have hfst : extChartAt I q (γ₁ s) = extChartAt I q (γ₂ s) := by
    have := congrArg Prod.fst hs
    simpa [hc₁_def, hc₂_def, chartCurve_def] using this
  have hγ₁_es : γ₁ s ∈ (extChartAt I q).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hs₁
  have hγ₂_es : γ₂ s ∈ (extChartAt I q).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hs₂
  exact (extChartAt I q).injOn hγ₁_es hγ₂_es hfst

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Chart-`q`-velocity at a foot point from `mfderiv`.**  If `γ` is
`MDifferentiableAt 𝓘(ℝ,ℝ) I` at `0`, has foot `γ 0 = q`, and launch velocity
`(mfderiv 𝓘(ℝ,ℝ) I γ 0 1 : E) = v`, then its chart-`q`-velocity at `0` is the
trivialization-`q` coordinate of `v`, a quantity depending only on `q` and `v`. -/
theorem chartCurve_deriv_zero_eq
    (q : M) {γ : ℝ → M} {v : E}
    (hγ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0)
    (hγ0 : γ 0 = q) (hv : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = v) :
    deriv (chartCurve (I := I) q γ) 0 =
      ((trivializationAt E (TangentSpace I) q).continuousLinearMapAt ℝ q) v := by
  classical
  have hsrc : γ 0 ∈ (chartAt H q).source := by rw [hγ0]; exact mem_chart_source H q
  have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    (I := I) (γ := γ) (t := 0) hγ_mdiff q hsrc
  have hcc : chartCurve (I := I) q γ = (extChartAt I q) ∘ γ := by
    funext s; rw [chartCurve_def]; rfl
  have hderiv_eq : deriv (chartCurve (I := I) q γ) 0
      = (fderiv ℝ ((extChartAt I q) ∘ γ) 0 : ℝ →L[ℝ] E) (1 : ℝ) := by
    rw [hcc]
    exact (fderiv_apply_one_eq_deriv (f := (extChartAt I q) ∘ γ) (x := (0 : ℝ))).symm
  rw [hderiv_eq]
  rw [hγ0] at hbridge
  rw [← hbridge]
  exact congrArg _ hv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Agreement of `maximalGeodesic` and `intrinsicGeodesic` on `[0, 1]`
(semantic-hypothesis form).**  Fix a chart basepoint `q`, and let `a < 0 ≤ 1 < b`
so that the closed interval `[0, 1]` lies inside the open interval `O = Ioo a b`.
Suppose, throughout `O`, both the home-chart maximal geodesic and the intrinsic
geodesic with initial data `(q, v)` satisfy the moving-foot geodesic equation and
keep their feet inside the home chart source `(chartAt H q).source`, and that the
home-chart maximal geodesic is continuous on `O`.  Then they agree at `t = 1`,
hence `expMapIntrinsic g hEnorm q v = expMap g q v`.

The argument is a clopen propagation along the preconnected interval `[0, 1]` of
the chart-`q`-phase agreement set; the open step is chart-`q`-coordinate ODE
uniqueness, the closed step continuity, and the base point `0 ∈ [0, 1]` is anchored
by the shared launch data `(q, v)`. -/
theorem expMapIntrinsic_eq_expMap_of_geodesicOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q : M) (v : TangentSpace I q) {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hcont_M : ContinuousOn (fun s => maximalGeodesic (I := I) g q v s) (Set.Ioo a b))
    (hgeo_M : ∀ t ∈ Set.Ioo a b,
      Geodesic.HasGeodesicEquationAt (I := I) g
        (fun s => maximalGeodesic (I := I) g q v s) t)
    (hvel_M : (mfderiv 𝓘(ℝ, ℝ) I (fun s => maximalGeodesic (I := I) g q v s) 0 (1 : ℝ)
        : E) = (v : E))
    (hsrc_M : ∀ t ∈ Set.Ioo a b,
      maximalGeodesic (I := I) g q v t ∈ (chartAt H q).source)
    (hsrc_I : ∀ t ∈ Set.Ioo a b,
      intrinsicGeodesic (I := I) g hEnorm q v t ∈ (chartAt H q).source) :
    expMapIntrinsic (I := I) g hEnorm q v = expMap (I := I) g q v := by
  classical
  set γM : ℝ → M := fun s => maximalGeodesic (I := I) g q v s with hγM_def
  set γI : ℝ → M := fun s => intrinsicGeodesic (I := I) g hEnorm q v s with hγI_def
  set O : Set ℝ := Set.Ioo a b with hO_def
  have hO_open : IsOpen O := isOpen_Ioo
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ O := by
    intro x hx; exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hγI_geoAll : ∀ s, Geodesic.HasGeodesicEquationAt (I := I) g γI s :=
    fun s => (intrinsicGeodesic_isGeodesic (I := I) g hEnorm q v) s
  have hγI_cont : Continuous γI := intrinsicGeodesic_continuous (I := I) g hEnorm q v
  have hγI_geo : ∀ t ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γI t :=
    fun t _ => hγI_geoAll t
  have hγI_contOn : ContinuousOn γI O := hγI_cont.continuousOn
  have hγM_geo : ∀ t ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γM t := hgeo_M
  have hγM_contOn : ContinuousOn γM O := hcont_M
  have hsrcM : ∀ t ∈ O, γM t ∈ (chartAt H q).source := hsrc_M
  have hsrcI : ∀ t ∈ O, γI t ∈ (chartAt H q).source := hsrc_I
  have hγM0 : γM 0 = q := by
    rw [hγM_def]; exact maximalGeodesic_zero (I := I) g q v
  have hγI0 : γI 0 = q := by
    rw [hγI_def]; exact intrinsicGeodesic_zero (I := I) g hEnorm q v
  set cM : ℝ → E × E :=
    fun s => (chartCurve (I := I) q γM s, deriv (chartCurve (I := I) q γM) s) with hcM_def
  set cI : ℝ → E × E :=
    fun s => (chartCurve (I := I) q γI s, deriv (chartCurve (I := I) q γI) s) with hcI_def
  have h0O : (0 : ℝ) ∈ O := hIcc_sub ⟨le_refl _, by norm_num⟩
  have hγM_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I γM 0 := by
    have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γM O :=
      HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g hO_open hγM_geo hγM_contOn
    exact (hC1.contMDiffAt (hO_open.mem_nhds h0O)).mdifferentiableAt (by norm_num)
  have hγI_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I γI 0 :=
    (((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm q v).contMDiffAt
      (Filter.univ_mem)).mdifferentiableAt (by norm_num))
  have hvM : (mfderiv 𝓘(ℝ, ℝ) I γM 0 (1 : ℝ) : E) = (v : E) := hvel_M
  have hvI : (mfderiv 𝓘(ℝ, ℝ) I γI 0 (1 : ℝ) : E) = (v : E) := by
    rw [hγI_def]; exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q v
  have hcM0 : cM 0 = cI 0 := by
    have hfst : chartCurve (I := I) q γM 0 = chartCurve (I := I) q γI 0 := by
      rw [chartCurve_def, chartCurve_def, hγM0, hγI0]
    have hsnd : deriv (chartCurve (I := I) q γM) 0 = deriv (chartCurve (I := I) q γI) 0 := by
      rw [chartCurve_deriv_zero_eq (I := I) q hγM_mdiff0 hγM0 hvM,
        chartCurve_deriv_zero_eq (I := I) q hγI_mdiff0 hγI0 hvI]
    change (chartCurve (I := I) q γM 0, deriv (chartCurve (I := I) q γM) 0)
      = (chartCurve (I := I) q γI 0, deriv (chartCurve (I := I) q γI) 0)
    rw [hfst, hsnd]
  set A : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ cM s = cI s} with hA_def
  have hcM_contOn : ContinuousOn cM O := by
    intro t ht
    exact (chartPhase_continuousAt_of_geodesicOn (I := I) g q hO_open ht hγM_contOn
      hsrcM hγM_geo).continuousWithinAt
  have hcI_contOn : ContinuousOn cI O := by
    intro t ht
    exact (chartPhase_continuousAt_of_geodesicOn (I := I) g q hO_open ht hγI_contOn
      hsrcI hγI_geo).continuousWithinAt
  have hA_closed : IsClosed (A : Set ℝ) := by
    have hcM_Icc : ContinuousOn cM (Set.Icc 0 1) := hcM_contOn.mono hIcc_sub
    have hcI_Icc : ContinuousOn cI (Set.Icc 0 1) := hcI_contOn.mono hIcc_sub
    have hpair : ContinuousOn (fun s => (cM s, cI s)) (Set.Icc (0 : ℝ) 1) :=
      hcM_Icc.prodMk hcI_Icc
    have hclosed_diag : IsClosed {p : (E × E) × (E × E) | p.1 = p.2} :=
      isClosed_diagonal
    have hpre := hpair.preimage_isClosed_of_isClosed isClosed_Icc hclosed_diag
    have hEq : A = Set.Icc (0 : ℝ) 1 ∩
        ((fun s => (cM s, cI s)) ⁻¹' {p : (E × E) × (E × E) | p.1 = p.2}) := by
      ext s
      simp only [hA_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [hEq]; exact hpre
  have hA_openIn : ∀ t ∈ A, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      U ∩ Set.Icc (0 : ℝ) 1 ⊆ A := by
    intro t ht
    obtain ⟨ht_Icc, ht_phase⟩ := ht
    have htO : t ∈ O := hIcc_sub ht_Icc
    have hdM := chartPhase_eventually_of_geodesicOn (I := I) g q hO_open htO hγM_contOn
      hsrcM hγM_geo
    have hdI := chartPhase_eventually_of_geodesicOn (I := I) g q hO_open htO hγI_contOn
      hsrcI hγI_geo
    set z₀ : E × E := cM t with hz₀_def
    have hz₀_mem : z₀ ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) :=
      (hdM.self_of_nhds).2
    have h1 : cM t = z₀ := rfl
    have h2 : cI t = z₀ := by rw [hz₀_def]; exact ht_phase.symm
    have hceq : cM =ᶠ[𝓝 t] cI :=
      chartPhaseVF_orbit_uniqueness_at (I := I) (g := g) (q := q) hz₀_mem h1 h2 hdM hdI
    rcases Filter.eventually_iff_exists_mem.mp hceq with ⟨U, hU_nhds, hU_eq⟩
    rcases mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem⟩
    refine ⟨V, hV_open, hV_mem, ?_⟩
    intro s hs
    refine ⟨hs.2, hU_eq s (hVU hs.1)⟩
  have h0A : (0 : ℝ) ∈ A := ⟨⟨le_refl _, by norm_num⟩, hcM0⟩
  have h1_mem : (1 : ℝ) ∈ A := by
    set S : Set ℝ := Set.Icc (0 : ℝ) 1 with hS_def
    have hS_conn : IsPreconnected S := (isPreconnected_Icc)
    have hA_sub_S : A ⊆ S := fun s hs => hs.1
    haveI : PreconnectedSpace (↥S) := isPreconnected_iff_preconnectedSpace.mp hS_conn
    set Asub : Set (↥S) := {x : ↥S | (x : ℝ) ∈ A} with hAsub_def
    have hAsub_clopen : IsClopen Asub := by
      constructor
      · exact hA_closed.preimage continuous_subtype_val
      · rw [isOpen_iff_mem_nhds]
        intro x hx
        obtain ⟨U, hU_open, hxU, hUsub⟩ := hA_openIn (x : ℝ) hx
        have hmem : (Subtype.val ⁻¹' U) ∈ nhds x :=
          (hU_open.preimage continuous_subtype_val).mem_nhds hxU
        refine Filter.mem_of_superset hmem ?_
        intro y hy
        have hyU : (y : ℝ) ∈ U := hy
        have hyS : (y : ℝ) ∈ S := y.2
        exact hUsub ⟨hyU, hyS⟩
    have hAsub_ne : Asub.Nonempty := by
      refine ⟨⟨0, ⟨le_refl _, by norm_num⟩⟩, ?_⟩
      exact h0A
    have hAsub_univ : Asub = Set.univ := hAsub_clopen.eq_univ hAsub_ne
    have h1S : (1 : ℝ) ∈ S := ⟨by norm_num, le_refl _⟩
    have : (⟨1, h1S⟩ : ↥S) ∈ Asub := by rw [hAsub_univ]; exact Set.mem_univ _
    exact this
  obtain ⟨_, h1_phase⟩ := h1_mem
  have h1O : (1 : ℝ) ∈ O := hIcc_sub ⟨by norm_num, le_refl _⟩
  have hfst1 : extChartAt I q (γM 1) = extChartAt I q (γI 1) := by
    have := congrArg Prod.fst h1_phase
    simpa [hcM_def, hcI_def, chartCurve_def] using this
  have hγM1_es : γM 1 ∈ (extChartAt I q).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrcM 1 h1O
  have hγI1_es : γI 1 ∈ (extChartAt I q).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrcI 1 h1O
  have hγ1 : γM 1 = γI 1 := (extChartAt I q).injOn hγM1_es hγI1_es hfst1
  have hgoal : γI 1 = γM 1 := hγ1.symm
  simpa [expMapIntrinsic, expMap, hγI_def, hγM_def] using hgoal

/-- **Home-chart maximal-geodesic data on an open interval, for small velocity.**
There is `ρ > 0` such that for every `v` with `‖v‖ < ρ` there are `a < 0 < 1 < b`
with: the maximal geodesic `maximalGeodesic g q v` is continuous on `Ioo a b`,
launches with velocity `v` at `0`, and keeps its foot inside `(chartAt H q).source`
throughout `Ioo a b`. -/
theorem exists_maximalGeodesic_data_of_small
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (q : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {v : TangentSpace I q}, ‖(v : E)‖ < ρ →
      ∃ a b : ℝ, a < 0 ∧ 1 < b ∧
        ContinuousOn (fun s => maximalGeodesic (I := I) g q v s) (Set.Ioo a b) ∧
        ((mfderiv 𝓘(ℝ, ℝ) I (fun s => maximalGeodesic (I := I) g q v s) 0 (1 : ℝ)
            : E) = (v : E)) ∧
        (∀ t ∈ Set.Ioo a b,
          maximalGeodesic (I := I) g q v t ∈ (chartAt H q).source) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    Exponential.exists_uniform_existence_interval (I := I) (g := g) (p := q)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv
  set w : E := (v : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  set vb : E := (1 / t') • w with hvb_def
  have hvb_resc : t' • vb = (v : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp
  refine ⟨-T / t', T / t', ?_, ?_, ?_, ?_, ?_⟩
  · rw [neg_div, hT_div]; norm_num
  · rw [hT_div]; norm_num
  · intro s hs
    have hF_int := Exponential.chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo
      (I := I) g q vb ht'_pos (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
    have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    have hproj_cont : ContinuousOn
        (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb r).proj)
        (Set.Ioo (-T / t') (T / t')) :=
      hπ_cont.comp_continuousOn hF_int.continuousOn
    have hEq : Set.EqOn (fun r => maximalGeodesic (I := I) g q v r)
        (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb r).proj)
        (Set.Ioo (-T / t') (T / t')) := by
      intro r hr
      have h := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
        (I := I) (g := g) (p := q) (v := vb) (T := T) (t' := t') ht'_pos
        (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := r) hr
      rw [show (t' • vb : TangentSpace I q) = v from hvb_resc] at h
      exact h.symm
    exact (hproj_cont.congr hEq) s hs
  · have hF_int := Exponential.chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo
      (I := I) g q vb ht'_pos (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
    have h0_mem : (0 : ℝ) ∈ Set.Ioo (-T / t') (T / t') := by
      rw [neg_div, hT_div]; norm_num
    have hF0 : Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb 0
        = (⟨q, v⟩ : TangentBundle I M) := by
      rw [Exponential.chartFlowOrbitLiftRescaled_zero (I := I) q vb t'
        (hΦ_init vb hvb_ball)]
      rw [show (t' • vb : TangentSpace I q) = v from hvb_resc]
    have hF_at : IsMIntegralCurveAt (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb)
        (Geodesic.geodesicVectorFieldChart (I := I) g q) 0 :=
      hF_int.isMIntegralCurveAt (isOpen_Ioo.mem_nhds h0_mem)
    have hF0_src : (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb 0).proj
        ∈ (chartAt H q).source := by
      rw [hF0]; exact mem_chart_source H q
    have hmfd := Geodesic.IsMIntegralCurveAt.mfderiv_proj_one (I := I) hF_at hF0_src
    have hEqnhds : (fun s => maximalGeodesic (I := I) g q v s)
        =ᶠ[𝓝 (0 : ℝ)] (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb r).proj) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0_mem) ?_
      intro r hr
      have h := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
        (I := I) (g := g) (p := q) (v := vb) (T := T) (t' := t') ht'_pos
        (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := r) hr
      rw [show (t' • vb : TangentSpace I q) = v from hvb_resc] at h
      exact h.symm
    have hmfd_eq : mfderiv 𝓘(ℝ, ℝ) I (fun s => maximalGeodesic (I := I) g q v s) 0
        = mfderiv 𝓘(ℝ, ℝ) I
          (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb r).proj) 0 :=
      hEqnhds.mfderiv_eq
    have hchain : mfderiv 𝓘(ℝ, ℝ) I (fun s => maximalGeodesic (I := I) g q v s) 0 (1 : ℝ)
        = (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb 0).snd := by
      rw [hmfd_eq]; exact hmfd
    rw [hchain, hF0]
  · intro t ht
    have hts_Icc : t' * t ∈ Set.Icc (-T) T := by
      rw [Set.mem_Ioo, neg_div, hT_div] at ht
      obtain ⟨ht0, ht1⟩ := ht
      refine ⟨?_, ?_⟩
      · nlinarith [ht'_pos.le, hT_pos.le]
      · nlinarith [ht'_lt_T.le, ht'_pos.le]
    have hΦ_target_tt := hΦ_target vb hvb_ball (t' * t) hts_Icc
    have hsrc' := Exponential.chartFlowOrbitLiftRescaled_proj_mem_chartAt_source
      (I := I) q vb t' t hΦ_target_tt
    have hEq := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
      (I := I) (g := g) (p := q) (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := t) ht
    rw [show (t' • vb : TangentSpace I q) = v from hvb_resc] at hEq
    rw [← hEq]; exact hsrc'

/-- **Coercivity of `g.inner q`.**  The positive-definite continuous bilinear form
`g.inner q` on a finite-dimensional space is bounded below by a multiple of the
squared Euclidean norm: there is `c > 0` with `c · ‖x‖² ≤ g_q(x, x)` for all `x : E`.
The unit sphere is compact (finite dimension), `g_q(x, x) > 0` there, and its minimum
is the constant `c`.  Stated with the Euclidean `E`-norm `‖x‖` (no fibre-norm
attribute removal), it converts a `g`-norm smallness `√(g_q(v,v)) < ρ` into the
Euclidean smallness consumed by the small-velocity home-chart data. -/
private lemma gq_coercive (g : SmoothRiemannianMetric I M) (q : M) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ^ 2 ≤ g.inner q x x := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_rclike (K := ℝ) (E := E)
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner q with hB_def
  set Q : E → ℝ := fun x => B x x with hQ
  have hQcont : Continuous Q := by
    have : Continuous (fun x : E => B x x) :=
      (B.continuous₂).comp (continuous_id.prodMk continuous_id)
    simpa [hQ] using this
  have hsphere : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hQpos : ∀ x ∈ Metric.sphere (0 : E) 1, (0 : ℝ) < Q x := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro h; rw [h] at hx
      simp only [mem_sphere_zero_iff_norm, norm_zero] at hx
      exact (zero_ne_one hx)
    exact g.pos q x hxne
  obtain ⟨c, hc_pos, hc_le⟩ :=
    hsphere.exists_forall_le' hQcont.continuousOn hQpos
  refine ⟨c, hc_pos, fun x => ?_⟩
  change c * ‖x‖ ^ 2 ≤ B x x
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0
    rw [ContinuousLinearMap.map_zero₂, norm_zero]
    simp
  · have hnx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set u : E := ‖x‖⁻¹ • x with hu_def
    have hu_sphere : u ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, hu_def, norm_smul]
      simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hnx_pos]
      exact inv_mul_cancel₀ (ne_of_gt hnx_pos)
    have hcu : c ≤ B u u := hc_le u hu_sphere
    have hx_eq : x = ‖x‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hnx_pos), one_smul]
    have hQscale : B x x = ‖x‖ ^ 2 * B u u := by
      nth_rewrite 1 [hx_eq]
      nth_rewrite 2 [hx_eq]
      rw [ContinuousLinearMap.map_smul₂, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hQscale]
    have hsq_nn : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    calc c * ‖x‖ ^ 2 = ‖x‖ ^ 2 * c := by ring
      _ ≤ ‖x‖ ^ 2 * B u u := mul_le_mul_of_nonneg_left hcu hsq_nn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Foot-in-source on `(-1, 2)` for small velocity (intrinsic geodesic).**
There is `ρ > 0` such that for every launch velocity `v` with `√(g_q(v,v)) < ρ`,
the intrinsic geodesic `t ↦ intrinsicGeodesic g hEnorm q v t` keeps its foot
inside the home chart source `(chartAt H q).source` for every `t ∈ Ioo (-1) 2`.

This discharges the cross-chart confinement hypothesis `hsrc_I` of
`expMapIntrinsic_eq_expMap_of_small` (so the latter becomes side-condition free on
small velocities).  The proof is the combined agree-and-confine clopen propagation
of the chart-`q` phase agreement set, anchored at the launch time `0`. -/
theorem intrinsicGeodesic_foot_in_source_of_small
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {v : TangentSpace I q},
      Real.sqrt (g.inner q (v : E) (v : E)) < ρ →
      ∀ t ∈ Set.Ioo (-1 : ℝ) 2,
        intrinsicGeodesic (I := I) g hEnorm q v t ∈ (chartAt H q).source := by
  classical
  obtain ⟨c, hc_pos, hcoerc⟩ := gq_coercive (I := I) g q
  obtain ⟨ρ₁, hρ₁_pos, hdata⟩ := exists_maximalGeodesic_data_of_small (I := I) g q
  obtain ⟨ρ₂, hρ₂_pos, hMdata⟩ :=
    DifferentialGeometry.Geometry.Riemannian.radial_maximalGeodesic_cont_and_foot_in_source_of_small
      (I := I) g q
  set R : ℝ := min (min ρ₁ ρ₂)
    (DifferentialGeometry.Geometry.Riemannian.expMapC2Radius (I := I) g q) with hR_def
  have hR_pos : 0 < R :=
    lt_min (lt_min hρ₁_pos hρ₂_pos)
      (DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos (I := I) g q)
  refine ⟨Real.sqrt c * R, mul_pos (Real.sqrt_pos.mpr hc_pos) hR_pos, ?_⟩
  intro v hv t ht
  set vE : E := (v : E) with hvE_def
  have hvE : ‖vE‖ < R := by
    have hsq : g.inner q vE vE < (Real.sqrt c * R) ^ 2 := by
      have := Real.lt_sq_of_sqrt_lt (x := g.inner q vE vE) hv
      simpa using this
    have hRsq : (Real.sqrt c * R) ^ 2 = c * R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc_pos.le]
    rw [hRsq] at hsq
    have hcoerc_v : c * ‖vE‖ ^ 2 ≤ g.inner q vE vE := hcoerc vE
    have hlt : c * ‖vE‖ ^ 2 < c * R ^ 2 := lt_of_le_of_lt hcoerc_v hsq
    have hsq_lt : ‖vE‖ ^ 2 < R ^ 2 := lt_of_mul_lt_mul_left hlt hc_pos.le
    nlinarith [norm_nonneg vE, hsq_lt, hR_pos]
  have hv₁ : ‖vE‖ < ρ₁ := lt_of_lt_of_le hvE (le_trans (min_le_left _ _) (min_le_left _ _))
  have hv₂' : ‖vE‖ < ρ₂ := lt_of_lt_of_le hvE (le_trans (min_le_left _ _) (min_le_right _ _))
  have hv₂ : ‖vE‖ <
      DifferentialGeometry.Geometry.Riemannian.expMapC2Radius (I := I) g q :=
    lt_of_lt_of_le hvE (min_le_right _ _)
  obtain ⟨_a₀, _b₀, _ha₀, _hb₀, _hcont_M, hvel_M, _hsrcM₀⟩ := hdata hv₁
  obtain ⟨hcont_M12, hsrcM12⟩ := hMdata hv₂'
  set O : Set ℝ := Set.Ioo (-1 : ℝ) 2 with hO_def
  have hO_open : IsOpen O := isOpen_Ioo
  have hO_conn : IsPreconnected O := isPreconnected_Ioo
  have ha : (-1 : ℝ) < 0 := by norm_num
  have hb : (1 : ℝ) < 2 := by norm_num
  have hO_sub_12 : O ⊆ Set.Ioo (-1 : ℝ) 2 := le_refl _
  set γM : ℝ → M := fun s => maximalGeodesic (I := I) g q v s with hγM_def
  set γI : ℝ → M := fun s => intrinsicGeodesic (I := I) g hEnorm q v s with hγI_def
  have hγI_cont : Continuous γI := intrinsicGeodesic_continuous (I := I) g hEnorm q v
  have hγI_contOn : ContinuousOn γI O := hγI_cont.continuousOn
  have hγM_contOn : ContinuousOn γM O := hcont_M12
  have hγI_geoAll : ∀ s, Geodesic.HasGeodesicEquationAt (I := I) g γI s :=
    fun s => (intrinsicGeodesic_isGeodesic (I := I) g hEnorm q v) s
  have hγI_geo : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γI s :=
    fun s _ => hγI_geoAll s
  have hγM_geo : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γM s := by
    intro s hs
    exact DifferentialGeometry.Geometry.Riemannian.radial_hasGeodesicEquationAt_of_norm_lt_radius
      (I := I) g q hv₂ s (hO_sub_12 hs)
  have hsrcM : ∀ s ∈ O, γM s ∈ (chartAt H q).source := hsrcM12
  have hγM0 : γM 0 = q := by rw [hγM_def]; exact maximalGeodesic_zero (I := I) g q v
  have hγI0 : γI 0 = q := by rw [hγI_def]; exact intrinsicGeodesic_zero (I := I) g hEnorm q v
  have h0O : (0 : ℝ) ∈ O := ⟨ha, by linarith⟩
  have hγM_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I γM 0 := by
    have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γM O :=
      HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g hO_open hγM_geo hγM_contOn
    exact (hC1.contMDiffAt (hO_open.mem_nhds h0O)).mdifferentiableAt (by norm_num)
  have hγI_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I γI 0 :=
    (((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm q v).contMDiffAt
      (Filter.univ_mem)).mdifferentiableAt (by norm_num))
  have hvM : (mfderiv 𝓘(ℝ, ℝ) I γM 0 (1 : ℝ) : E) = (v : E) := hvel_M
  have hvI : (mfderiv 𝓘(ℝ, ℝ) I γI 0 (1 : ℝ) : E) = (v : E) := by
    rw [hγI_def]; exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q v
  set cM : ℝ → E × E :=
    fun s => (chartCurve (I := I) q γM s, deriv (chartCurve (I := I) q γM) s) with hcM_def
  set cI : ℝ → E × E :=
    fun s => (chartCurve (I := I) q γI s, deriv (chartCurve (I := I) q γI) s) with hcI_def
  have hcM0 : cM 0 = cI 0 := by
    have hfst : chartCurve (I := I) q γM 0 = chartCurve (I := I) q γI 0 := by
      rw [chartCurve_def, chartCurve_def, hγM0, hγI0]
    have hsnd : deriv (chartCurve (I := I) q γM) 0 = deriv (chartCurve (I := I) q γI) 0 := by
      rw [chartCurve_deriv_zero_eq (I := I) q hγM_mdiff0 hγM0 hvM,
        chartCurve_deriv_zero_eq (I := I) q hγI_mdiff0 hγI0 hvI]
    change (chartCurve (I := I) q γM 0, deriv (chartCurve (I := I) q γM) 0)
      = (chartCurve (I := I) q γI 0, deriv (chartCurve (I := I) q γI) 0)
    rw [hfst, hsnd]
  set A : Set ℝ := {s | s ∈ O ∧ cM s = cI s ∧ γI s ∈ (chartAt H q).source} with hA_def
  have hcM_contOn : ContinuousOn cM O := fun t ht =>
    (chartPhase_continuousAt_of_geodesicOn (I := I) g q hO_open ht hγM_contOn
      hsrcM hγM_geo).continuousWithinAt
  have hA_openIn : ∀ s ∈ A, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ U ⊆ O ∧ U ⊆ A := by
    intro s hs
    obtain ⟨hsO, hsphase, hsI_src⟩ := hs
    have hsrcI_nhds : ∀ᶠ r in 𝓝 s, γI r ∈ (chartAt H q).source := by
      have hopen : IsOpen (γI ⁻¹' (chartAt H q).source) :=
        (chartAt H q).open_source.preimage hγI_cont
      exact hopen.mem_nhds hsI_src
    obtain ⟨O'', hO''_sub, hO''_open, hsO''⟩ :=
      mem_nhds_iff.mp (Filter.inter_mem (hsrcI_nhds) (hO_open.mem_nhds hsO))
    set O' : Set ℝ := O'' with hO'_def
    have hO'_open : IsOpen O' := hO''_open
    have hsO' : s ∈ O' := hsO''
    have hO'_sub_O : O' ⊆ O := fun r hr => (hO''_sub hr).2
    have hsrcI' : ∀ r ∈ O', γI r ∈ (chartAt H q).source := fun r hr => (hO''_sub hr).1
    have hγM_contOn' : ContinuousOn γM O' := hγM_contOn.mono hO'_sub_O
    have hγI_contOn' : ContinuousOn γI O' := hγI_cont.continuousOn
    have hsrcM' : ∀ r ∈ O', γM r ∈ (chartAt H q).source := fun r hr => hsrcM r (hO'_sub_O hr)
    have hγM_geo' : ∀ r ∈ O', Geodesic.HasGeodesicEquationAt (I := I) g γM r :=
      fun r hr => hγM_geo r (hO'_sub_O hr)
    have hγI_geo' : ∀ r ∈ O', Geodesic.HasGeodesicEquationAt (I := I) g γI r :=
      fun r hr => hγI_geo r (hO'_sub_O hr)
    have hphase_eq :
        (chartCurve (I := I) q γM s, deriv (chartCurve (I := I) q γM) s)
          = (chartCurve (I := I) q γI s, deriv (chartCurve (I := I) q γI) s) := hsphase
    have hev_eq : γM =ᶠ[𝓝 s] γI :=
      geodesic_eventuallyEq_of_chartPhase_eq (I := I) g q hO'_open hsO'
        hγM_contOn' hγI_contOn' hsrcM' hsrcI' hγM_geo' hγI_geo' hphase_eq
    have hcM_ev : ∀ᶠ r in 𝓝 s,
        HasDerivAt (fun u => (chartCurve (I := I) q γM u, deriv (chartCurve (I := I) q γM) u))
          (Geodesic.chartPhaseVF (I := I) g q
            (chartCurve (I := I) q γM r, deriv (chartCurve (I := I) q γM) r)) r ∧
        (chartCurve (I := I) q γM r, deriv (chartCurve (I := I) q γM) r)
          ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) :=
      chartPhase_eventually_of_geodesicOn (I := I) g q hO'_open hsO'
        hγM_contOn' hsrcM' hγM_geo'
    have hcI_ev : ∀ᶠ r in 𝓝 s,
        HasDerivAt (fun u => (chartCurve (I := I) q γI u, deriv (chartCurve (I := I) q γI) u))
          (Geodesic.chartPhaseVF (I := I) g q
            (chartCurve (I := I) q γI r, deriv (chartCurve (I := I) q γI) r)) r ∧
        (chartCurve (I := I) q γI r, deriv (chartCurve (I := I) q γI) r)
          ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) :=
      chartPhase_eventually_of_geodesicOn (I := I) g q hO'_open hsO'
        hγI_contOn' hsrcI' hγI_geo'
    set z₀ : E × E := cM s with hz₀_def
    have hz₀_mem : z₀ ∈ (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) :=
      (hcM_ev.self_of_nhds).2
    have h1z : cM s = z₀ := rfl
    have h2z : cI s = z₀ := by rw [hz₀_def, hcM_def, hcI_def]; exact hsphase.symm
    have hcphase_ev : cM =ᶠ[𝓝 s] cI :=
      chartPhaseVF_orbit_uniqueness_at (I := I) (g := g) (q := q) hz₀_mem h1z h2z
        hcM_ev hcI_ev
    have hW_mem : (O' ∩ {r | cM r = cI r ∧ γI r ∈ (chartAt H q).source}) ∈ 𝓝 s := by
      refine Filter.inter_mem (hO'_open.mem_nhds hsO') ?_
      filter_upwards [hcphase_ev, hsrcI_nhds] with r hr hr_src
      exact ⟨hr, hr_src⟩
    obtain ⟨W, hW_sub, hW_open, hsW⟩ := mem_nhds_iff.mp hW_mem
    refine ⟨W, hW_open, hsW, ?_, ?_⟩
    · intro r hr; exact hO'_sub_O (hW_sub hr).1
    · intro r hr
      obtain ⟨hrO', hrphase, hr_src⟩ := hW_sub hr
      exact ⟨hO'_sub_O hrO', hrphase, hr_src⟩
  haveI : PreconnectedSpace (↥O) := isPreconnected_iff_preconnectedSpace.mp hO_conn
  set Asub : Set (↥O) := {x : ↥O | (x : ℝ) ∈ A} with hAsub_def
  have hAsub_open : IsOpen Asub := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU_open, hxU, _hUO, hUA⟩ := hA_openIn (x : ℝ) hx
    have hmem : (Subtype.val ⁻¹' U) ∈ nhds x :=
      (hU_open.preimage continuous_subtype_val).mem_nhds hxU
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    exact hUA hy
  have hAeq_curve : ∀ s ∈ A, γM s = γI s := by
    intro s hs
    obtain ⟨_hsO, hsphase, hsI_src⟩ := hs
    have hfst : extChartAt I q (γM s) = extChartAt I q (γI s) := by
      have := congrArg Prod.fst hsphase
      simpa [hcM_def, hcI_def, chartCurve_def] using this
    have hγM_es : γM s ∈ (extChartAt I q).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrcM s _hsO
    have hγI_es : γI s ∈ (extChartAt I q).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsI_src
    exact (extChartAt I q).injOn hγM_es hγI_es hfst
  set P : Set (↥O) := {x : ↥O | γM (x : ℝ) = γI (x : ℝ)} with hP_def
  have hPclosed : IsClosed P := by
    have hγM_sub : Continuous (fun x : ↥O => γM (x : ℝ)) :=
      hγM_contOn.comp_continuous continuous_subtype_val (fun x => x.2)
    have hγI_sub : Continuous (fun x : ↥O => γI (x : ℝ)) :=
      hγI_cont.comp continuous_subtype_val
    exact isClosed_eq hγM_sub hγI_sub
  have hAsub_closed : IsClosed Asub := by
    rw [isClosed_iff_clusterPt]
    intro x hx
    have hxO : (x : ℝ) ∈ O := x.2
    have hAsub_sub_P : Asub ⊆ P := fun y hy => hAeq_curve (y : ℝ) hy
    have hxP : x ∈ P :=
      hPclosed.closure_subset (mem_closure_iff_clusterPt.mpr
        (hx.mono (Filter.principal_mono.mpr hAsub_sub_P)))
    have hγeq_x : γM (x : ℝ) = γI (x : ℝ) := hxP
    have hxsrc : γI (x : ℝ) ∈ (chartAt H q).source := by
      rw [← hγeq_x]; exact hsrcM (x : ℝ) hxO
    have hsrcI_nhds : ∀ᶠ r in 𝓝 (x : ℝ), γI r ∈ (chartAt H q).source := by
      have hopen : IsOpen (γI ⁻¹' (chartAt H q).source) :=
        (chartAt H q).open_source.preimage hγI_cont
      exact hopen.mem_nhds hxsrc
    obtain ⟨O'', hO''_sub, hO''_open, hxO''⟩ :=
      mem_nhds_iff.mp (Filter.inter_mem hsrcI_nhds (hO_open.mem_nhds hxO))
    have hO'_open : IsOpen O'' := hO''_open
    have hxO' : (x : ℝ) ∈ O'' := hxO''
    have hO'_sub_O : O'' ⊆ O := fun r hr => (hO''_sub hr).2
    have hsrcI' : ∀ r ∈ O'', γI r ∈ (chartAt H q).source := fun r hr => (hO''_sub hr).1
    have hcI_catx : ContinuousAt cI (x : ℝ) :=
      chartPhase_continuousAt_of_geodesicOn (I := I) g q hO'_open hxO'
        (hγI_cont.continuousOn) hsrcI' (fun r _ => hγI_geoAll r)
    have hcM_catx : ContinuousAt cM (x : ℝ) :=
      chartPhase_continuousAt_of_geodesicOn (I := I) g q hO_open hxO hγM_contOn
        hsrcM hγM_geo
    have hpair_catx : ContinuousAt (fun r => (cM r, cI r)) (x : ℝ) :=
      hcM_catx.prodMk hcI_catx
    have hphase_x : cM (x : ℝ) = cI (x : ℝ) := by
      by_contra hne
      have hdiag_open : IsOpen {p : (E × E) × (E × E) | p.1 ≠ p.2} :=
        isOpen_compl_iff.mpr isClosed_diagonal
      have hxmem : ((cM (x : ℝ), cI (x : ℝ))) ∈ {p : (E × E) × (E × E) | p.1 ≠ p.2} := hne
      have hnhds : (fun r => (cM r, cI r)) ⁻¹' {p : (E × E) × (E × E) | p.1 ≠ p.2}
          ∈ 𝓝 (x : ℝ) := hpair_catx.preimage_mem_nhds (hdiag_open.mem_nhds hxmem)
      have hnhds_sub : (Subtype.val ⁻¹'
          ((fun r => (cM r, cI r)) ⁻¹' {p : (E × E) × (E × E) | p.1 ≠ p.2})) ∈ 𝓝 x :=
        continuousAt_subtype_val.preimage_mem_nhds hnhds
      have hdisj : Disjoint (𝓝 x) (Filter.principal Asub) := by
        rw [Filter.disjoint_principal_right]
        refine Filter.mem_of_superset hnhds_sub ?_
        intro y hy
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
        intro hyAsub
        exact hy (hyAsub.2.1)
      exact (clusterPt_iff_not_disjoint.mp hx) hdisj
    exact ⟨hxO, hphase_x, hxsrc⟩
  have hAsub_clopen : IsClopen Asub := ⟨hAsub_closed, hAsub_open⟩
  have hAsub_ne : Asub.Nonempty := by
    refine ⟨⟨0, h0O⟩, ?_⟩
    exact ⟨h0O, hcM0, by rw [hγI0]; exact mem_chart_source H q⟩
  have hAsub_univ : Asub = Set.univ := hAsub_clopen.eq_univ hAsub_ne
  have htO : t ∈ O := ht
  have : (⟨t, htO⟩ : ↥O) ∈ Asub := by rw [hAsub_univ]; exact Set.mem_univ _
  exact (this.2).2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`expMapIntrinsic = expMap` for small velocity (cross-chart agreement bridge).**
For a small launch velocity `v` (`√(g_q(v,v)) < ρ` for an explicit `ρ > 0`) whose
intrinsic geodesic stays inside the home chart `(chartAt H q).source` throughout the
open interval `(-1, 2) ⊇ [0, 1]`, the intrinsic exponential map agrees with the
chart-fixed exponential map:
`expMapIntrinsic g hEnorm q v = expMap g q v`.

The smallness is stated in the `g`-norm `√(g_q(v,v))`; coercivity of `g_q` converts it
to the Euclidean smallness consumed by the small-velocity home-chart data and the
Gauss-lemma radial geodesic equation.  The home-chart side (continuity, launch
velocity, foot-in-source, moving-foot geodesic equation of `maximalGeodesic g q v` on
an open interval) is then in hand; the remaining input is the intrinsic geodesic's
home-chart confinement `hsrc_I`, the genuine cross-chart datum.  The equality is the
geodesic-uniqueness clopen propagation of `expMapIntrinsic_eq_expMap_of_geodesicOn`. -/
theorem expMapIntrinsic_eq_expMap_of_small
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {v : TangentSpace I q},
      Real.sqrt (g.inner q (v : E) (v : E)) < ρ →
      (∀ t ∈ Set.Ioo (-1 : ℝ) 2,
        intrinsicGeodesic (I := I) g hEnorm q v t ∈ (chartAt H q).source) →
      expMapIntrinsic (I := I) g hEnorm q v = expMap (I := I) g q v := by
  classical
  obtain ⟨c, hc_pos, hcoerc⟩ := gq_coercive (I := I) g q
  obtain ⟨ρ₁, hρ₁_pos, hdata⟩ := exists_maximalGeodesic_data_of_small (I := I) g q
  set R : ℝ := min ρ₁ (DifferentialGeometry.Geometry.Riemannian.expMapC2Radius (I := I) g q)
    with hR_def
  have hR_pos : 0 < R :=
    lt_min hρ₁_pos (DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos (I := I) g q)
  refine ⟨Real.sqrt c * R, mul_pos (Real.sqrt_pos.mpr hc_pos) hR_pos, ?_⟩
  intro v hv hsrc_I
  set vE : E := (v : E) with hvE_def
  have hvE : ‖vE‖ < R := by
    have hsq : g.inner q vE vE < (Real.sqrt c * R) ^ 2 := by
      have := Real.lt_sq_of_sqrt_lt (x := g.inner q vE vE) hv
      simpa using this
    have hRsq : (Real.sqrt c * R) ^ 2 = c * R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc_pos.le]
    rw [hRsq] at hsq
    have hcoerc_v : c * ‖vE‖ ^ 2 ≤ g.inner q vE vE := hcoerc vE
    have hlt : c * ‖vE‖ ^ 2 < c * R ^ 2 := lt_of_le_of_lt hcoerc_v hsq
    have hsq_lt : ‖vE‖ ^ 2 < R ^ 2 := lt_of_mul_lt_mul_left hlt hc_pos.le
    nlinarith [norm_nonneg vE, hsq_lt, hR_pos]
  have hv₁ : ‖vE‖ < ρ₁ := lt_of_lt_of_le hvE (min_le_left _ _)
  have hv₂ : ‖vE‖ <
      DifferentialGeometry.Geometry.Riemannian.expMapC2Radius (I := I) g q :=
    lt_of_lt_of_le hvE (min_le_right _ _)
  obtain ⟨a, b, ha, hb, hcont_M, hvel_M, hsrcM⟩ := hdata hv₁
  set a' : ℝ := max a (-1) with ha'_def
  set b' : ℝ := min b 2 with hb'_def
  have ha' : a' < 0 := by rw [ha'_def]; exact max_lt ha (by norm_num)
  have hb' : 1 < b' := by rw [hb'_def]; exact lt_min hb (by norm_num)
  have hIoo'_sub_ab : Set.Ioo a' b' ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hIoo'_sub_12 : Set.Ioo a' b' ⊆ Set.Ioo (-1 : ℝ) 2 := by
    intro x hx
    exact ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
  refine expMapIntrinsic_eq_expMap_of_geodesicOn (I := I) g hEnorm q v ha' hb'
    (hcont_M.mono hIoo'_sub_ab) ?_ hvel_M ?_ ?_
  · intro t ht
    exact DifferentialGeometry.Geometry.Riemannian.radial_hasGeodesicEquationAt_of_norm_lt_radius
      (I := I) g q hv₂ t (hIoo'_sub_12 ht)
  · intro t ht
    exact hsrcM t (hIoo'_sub_ab ht)
  · intro t ht
    exact hsrc_I t (hIoo'_sub_12 ht)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Affine time-rescaling of the moving-foot geodesic equation.**  If `γ`
satisfies the moving-foot geodesic equation at `c · t`, then the rescaled curve
`s ↦ γ (c · s)` satisfies it at `t`.  The new velocity is `c` times the old,
the new acceleration `c²` times the old, and the quadratic Christoffel scaling
makes the geodesic identity persist. -/
private theorem hasGeodesicEquationAt_comp_const_smul
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} (c t : ℝ)
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ (c * t)) :
    Geodesic.HasGeodesicEquationAt (I := I) g (fun s => γ (c * s)) t := by
  classical
  obtain ⟨v, a, hv, hev, ha, hid⟩ := hgeo
  set η : ℝ → M := fun s => γ (c * s) with hη_def
  have hηt : η t = γ (c * t) := rfl
  have hcl_eq : Geodesic.chartLocalCurve (I := I) η t
      = (Geodesic.chartLocalCurve (I := I) γ (c * t)) ∘ (fun s => c * s) := by
    funext s
    simp only [Geodesic.chartLocalCurve_def, Function.comp_apply, hη_def]
  set w : ℝ → E := Geodesic.chartLocalCurve (I := I) γ (c * t) with hw_def
  have haff : ∀ s : ℝ, HasDerivAt (fun r : ℝ => c * r) c s := fun s => by
    simpa using (hasDerivAt_id s).const_mul c
  have hv' : HasDerivAt (Geodesic.chartLocalCurve (I := I) η t) (c • v) t := by
    rw [hcl_eq]
    have hcomp : HasDerivAt (w ∘ (fun s => c * s)) (c • v) t := by
      have := (hv).scomp t (haff t)
      simpa [hw_def] using this
    exact hcomp
  have hev' : ∀ᶠ s in 𝓝 t,
      HasDerivAt (Geodesic.chartLocalCurve (I := I) η t)
        (deriv (Geodesic.chartLocalCurve (I := I) η t) s) s := by
    have hpb : Filter.Tendsto (fun s : ℝ => c * s) (𝓝 t) (𝓝 (c * t)) := by
      have := (haff t).continuousAt
      simpa [hη_def] using this.tendsto
    filter_upwards [hpb.eventually hev] with s hs
    have hcomp : HasDerivAt (w ∘ (fun r => c * r)) (c • deriv w (c * s)) s :=
      hs.scomp s (haff s)
    have hcls : HasDerivAt (Geodesic.chartLocalCurve (I := I) η t)
        (c • deriv w (c * s)) s := by rw [hcl_eq]; exact hcomp
    rwa [hcls.deriv]
  have hderiv_eq : (fun s => deriv (Geodesic.chartLocalCurve (I := I) η t) s)
      =ᶠ[𝓝 t] (fun s => c • deriv w (c * s)) := by
    have hpb : Filter.Tendsto (fun s : ℝ => c * s) (𝓝 t) (𝓝 (c * t)) := by
      have := (haff t).continuousAt
      simpa using this.tendsto
    filter_upwards [hpb.eventually hev] with s hs
    have hcomp : HasDerivAt (w ∘ (fun r => c * r)) (c • deriv w (c * s)) s :=
      hs.scomp s (haff s)
    have hcls : HasDerivAt (Geodesic.chartLocalCurve (I := I) η t)
        (c • deriv w (c * s)) s := by rw [hcl_eq]; exact hcomp
    exact hcls.deriv
  have ha' : HasDerivAt (fun s => deriv (Geodesic.chartLocalCurve (I := I) η t) s)
      (c • (c • a)) t := by
    have hinner : HasDerivAt (fun s => deriv w (c * s)) (c • a) t := by
      have := ha.scomp t (haff t)
      simpa [hw_def] using this
    have houter : HasDerivAt (fun s => c • deriv w (c * s)) (c • (c • a)) t :=
      hinner.const_smul c
    exact houter.congr_of_eventuallyEq hderiv_eq
  have hfoot : (fun s => γ (c * s)) t = γ (c * t) := rfl
  have hbase : extChartAt I (η t) (η t) = extChartAt I (γ (c * t)) (γ (c * t)) := by
    rw [hηt]
  refine ⟨c • v, c • (c • a), hv', hev', ha', ?_⟩
  have hΓ : Geodesic.chartChristoffelContraction (I := I) g (η t) (c • v) (c • v)
        (extChartAt I (η t) (η t))
      = (c * c) • Geodesic.chartChristoffelContraction (I := I) g (γ (c * t)) v v
        (extChartAt I (γ (c * t)) (γ (c * t))) := by
    rw [hηt, hbase]
    exact Geodesic.chartChristoffelContraction_smul_smul (I := I) g (γ (c * t)) c v _
  rw [hΓ]
  have hcc : c • (c • a) = (c * c) • a := by rw [smul_smul]
  rw [hcc, ← smul_add, hid, smul_zero]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Local agreement of two moving-foot geodesics from matching initial data at
`t₀`.**  If `γ₁, γ₂` are continuous moving-foot geodesics on all of `ℝ`, share the
foot `γ₁ t₀ = γ₂ t₀` and the chart-`(γ₁ t₀)` velocity
`deriv (chartCurve (γ₁ t₀) γ₁) t₀ = deriv (chartCurve (γ₁ t₀) γ₂) t₀`, then
`γ₁ =ᶠ[𝓝 t₀] γ₂`.  This is the open-propagation engine for the global
uniqueness theorem below; it is chart-`(γ₁ t₀)`-coordinate ODE uniqueness
specialised to the chart centred at the common foot. -/
private theorem geodesic_eventuallyEq_of_initial_local
    (g : SmoothRiemannianMetric I M) {γ₁ γ₂ : ℝ → M} {t₀ : ℝ}
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hgeo₁ : Geodesic.IsGeodesic (I := I) g γ₁)
    (hgeo₂ : Geodesic.IsGeodesic (I := I) g γ₂)
    (h0 : γ₁ t₀ = γ₂ t₀)
    (hvel : deriv (chartCurve (I := I) (γ₁ t₀) γ₁) t₀
        = deriv (chartCurve (I := I) (γ₁ t₀) γ₂) t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  classical
  set q : M := γ₁ t₀ with hq_def
  set O : Set ℝ := γ₁ ⁻¹' (chartAt H q).source ∩ γ₂ ⁻¹' (chartAt H q).source with hO_def
  have hO_open : IsOpen O :=
    ((chartAt H q).open_source.preimage hγ₁_cont).inter
      ((chartAt H q).open_source.preimage hγ₂_cont)
  have hq_src : q ∈ (chartAt H q).source := mem_chart_source H q
  have htO : t₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · change γ₁ t₀ ∈ (chartAt H q).source; exact hq_src
    · change γ₂ t₀ ∈ (chartAt H q).source; rw [← h0]; exact hq_src
  have hsrc₁ : ∀ s ∈ O, γ₁ s ∈ (chartAt H q).source := fun s hs => hs.1
  have hsrc₂ : ∀ s ∈ O, γ₂ s ∈ (chartAt H q).source := fun s hs => hs.2
  have hgeo₁' : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γ₁ s :=
    fun s _ => hgeo₁ s
  have hgeo₂' : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g γ₂ s :=
    fun s _ => hgeo₂ s
  have hphase :
      (chartCurve (I := I) q γ₁ t₀, deriv (chartCurve (I := I) q γ₁) t₀)
        = (chartCurve (I := I) q γ₂ t₀, deriv (chartCurve (I := I) q γ₂) t₀) := by
    have hfst : chartCurve (I := I) q γ₁ t₀ = chartCurve (I := I) q γ₂ t₀ := by
      rw [chartCurve_def, chartCurve_def, ← hq_def, h0]
    have hsnd : deriv (chartCurve (I := I) q γ₁) t₀ = deriv (chartCurve (I := I) q γ₂) t₀ := by
      rw [hq_def]; exact hvel
    rw [hfst, hsnd]
  exact geodesic_eventuallyEq_of_chartPhase_eq (I := I) g q hO_open htO
    hγ₁_cont.continuousOn hγ₂_cont.continuousOn hsrc₁ hsrc₂ hgeo₁' hgeo₂' hphase

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Global uniqueness of complete geodesics from initial data.**  Two
moving-foot geodesics on all of `ℝ`, both continuous, sharing the initial point
`Γ₁ 0 = Γ₂ 0` and the launch velocity
`(mfderiv 𝓘(ℝ,ℝ) I Γ₁ 0 1 : E) = (mfderiv 𝓘(ℝ,ℝ) I Γ₂ 0 1 : E)`, coincide on all
of `ℝ`.

The proof is a clopen propagation along the preconnected line of the
local-agreement set `S = {t | Γ₁ =ᶠ[𝓝 t] Γ₂}`: openness is immediate, closedness
is chart-`(Γ₁ t)`-coordinate ODE uniqueness at each cluster point, and the base
point `0` is anchored by the shared launch data. -/
theorem isGeodesic_eq_of_initial
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M) {Γ₁ Γ₂ : ℝ → M}
    (h₁ : Geodesic.IsGeodesic (I := I) g Γ₁) (h₂ : Geodesic.IsGeodesic (I := I) g Γ₂)
    (hc₁ : Continuous Γ₁) (hc₂ : Continuous Γ₂)
    (h0 : Γ₁ 0 = Γ₂ 0)
    (hv : (mfderiv 𝓘(ℝ, ℝ) I Γ₁ 0 (1 : ℝ) : E) = (mfderiv 𝓘(ℝ, ℝ) I Γ₂ 0 (1 : ℝ) : E)) :
    Γ₁ = Γ₂ := by
  classical
  have hC1₁ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 Γ₁ Set.univ :=
    HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g isOpen_univ
      (h₁.isGeodesicOn Set.univ) hc₁.continuousOn
  have hC1₂ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 Γ₂ Set.univ :=
    HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g isOpen_univ
      (h₂.isGeodesicOn Set.univ) hc₂.continuousOn
  have hmdiff₁ : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I Γ₁ t :=
    fun t => (hC1₁.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by norm_num)
  have hmdiff₂ : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I Γ₂ t :=
    fun t => (hC1₂.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by norm_num)
  set S : Set ℝ := {t | Γ₁ =ᶠ[𝓝 t] Γ₂} with hS_def
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    rcases Filter.eventually_iff_exists_mem.mp ht with ⟨U, hU_nhds, hU_eq⟩
    rcases mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, htV⟩
    refine Filter.mem_of_superset (hV_open.mem_nhds htV) ?_
    intro s hsV
    exact Filter.eventually_iff_exists_mem.mpr
      ⟨V, hV_open.mem_nhds hsV, fun r hrV => hU_eq r (hVU hrV)⟩
  have hfeet_closed : IsClosed {t : ℝ | Γ₁ t = Γ₂ t} :=
    isClosed_eq hc₁ hc₂
  have hS_sub_feet : S ⊆ {t : ℝ | Γ₁ t = Γ₂ t} := by
    intro t ht; exact ht.self_of_nhds
  have hS_closed : IsClosed S := by
    rw [← closure_subset_iff_isClosed]
    intro t ht
    have hfeet_t : Γ₁ t = Γ₂ t := by
      have : t ∈ closure {s : ℝ | Γ₁ s = Γ₂ s} :=
        closure_mono hS_sub_feet ht
      rwa [hfeet_closed.closure_eq] at this
    set q : M := Γ₁ t with hq_def
    set O : Set ℝ := Γ₁ ⁻¹' (chartAt H q).source ∩ Γ₂ ⁻¹' (chartAt H q).source with hO_def
    have hO_open : IsOpen O :=
      ((chartAt H q).open_source.preimage hc₁).inter
        ((chartAt H q).open_source.preimage hc₂)
    have hq_src : q ∈ (chartAt H q).source := mem_chart_source H q
    have htO : t ∈ O := by
      refine ⟨?_, ?_⟩
      · change Γ₁ t ∈ (chartAt H q).source; exact hq_src
      · change Γ₂ t ∈ (chartAt H q).source; rw [← hfeet_t]; exact hq_src
    have hsrc₁ : ∀ s ∈ O, Γ₁ s ∈ (chartAt H q).source := fun s hs => hs.1
    have hsrc₂ : ∀ s ∈ O, Γ₂ s ∈ (chartAt H q).source := fun s hs => hs.2
    have hgeo₁ : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g Γ₁ s :=
      fun s _ => h₁ s
    have hgeo₂ : ∀ s ∈ O, Geodesic.HasGeodesicEquationAt (I := I) g Γ₂ s :=
      fun s _ => h₂ s
    set c₁ : ℝ → E × E :=
      fun s => (chartCurve (I := I) q Γ₁ s, deriv (chartCurve (I := I) q Γ₁) s) with hc₁_def
    set c₂ : ℝ → E × E :=
      fun s => (chartCurve (I := I) q Γ₂ s, deriv (chartCurve (I := I) q Γ₂) s) with hc₂_def
    have hc₁_contOn : ContinuousOn c₁ O := fun s hs =>
      (chartPhase_continuousAt_of_geodesicOn (I := I) g q hO_open hs hc₁.continuousOn
        hsrc₁ hgeo₁).continuousWithinAt
    have hc₂_contOn : ContinuousOn c₂ O := fun s hs =>
      (chartPhase_continuousAt_of_geodesicOn (I := I) g q hO_open hs hc₂.continuousOn
        hsrc₂ hgeo₂).continuousWithinAt
    have hc_eqOn : Set.EqOn c₁ c₂ (S ∩ O) := by
      intro s hs
      have hloc : Γ₁ =ᶠ[𝓝 s] Γ₂ := hs.1
      have hcc : chartCurve (I := I) q Γ₁ =ᶠ[𝓝 s] chartCurve (I := I) q Γ₂ := by
        filter_upwards [hloc] with r hr
        rw [chartCurve_def, chartCurve_def, hr]
      have hfst : chartCurve (I := I) q Γ₁ s = chartCurve (I := I) q Γ₂ s := by
        rw [chartCurve_def, chartCurve_def, hloc.self_of_nhds]
      have hsnd : deriv (chartCurve (I := I) q Γ₁) s = deriv (chartCurve (I := I) q Γ₂) s :=
        Filter.EventuallyEq.deriv_eq hcc
      simp only [hc₁_def, hc₂_def, hfst, hsnd]
    have ht_closSO : t ∈ closure (S ∩ O) := by
      rw [mem_closure_iff_nhds]
      intro u hu
      have huO : u ∩ O ∈ 𝓝 t := Filter.inter_mem hu (hO_open.mem_nhds htO)
      rcases (mem_closure_iff_nhds.mp ht) (u ∩ O) huO with ⟨z, hz_uO, hz_S⟩
      exact ⟨z, hz_uO.1, hz_S, hz_uO.2⟩
    have hc_t : c₁ t = c₂ t := by
      set W : Set ℝ := (S ∩ O) ∪ {t} with hW_def
      have hW_sub_O : W ⊆ O := by
        rintro s (hs | hs)
        · exact hs.2
        · rw [Set.mem_singleton_iff.mp hs]; exact htO
      have hSO_sub_W : (S ∩ O) ⊆ W := Set.subset_union_left
      have hW_sub_clos : W ⊆ closure (S ∩ O) := by
        rintro s (hs | hs)
        · exact subset_closure hs
        · rw [Set.mem_singleton_iff.mp hs]; exact ht_closSO
      have heqW : Set.EqOn c₁ c₂ W :=
        hc_eqOn.of_subset_closure (hc₁_contOn.mono hW_sub_O) (hc₂_contOn.mono hW_sub_O)
          hSO_sub_W hW_sub_clos
      exact heqW (Set.mem_union_right _ rfl)
    have hvel_t : deriv (chartCurve (I := I) q Γ₁) t = deriv (chartCurve (I := I) q Γ₂) t := by
      have := congrArg Prod.snd hc_t
      simpa [hc₁_def, hc₂_def] using this
    have : Γ₁ =ᶠ[𝓝 t] Γ₂ :=
      geodesic_eventuallyEq_of_initial_local (I := I) g hc₁ hc₂ h₁ h₂ hfeet_t
        (by rw [hq_def] at hvel_t; exact hvel_t)
    exact this
  have h0S : (0 : ℝ) ∈ S := by
    set q : M := Γ₁ 0 with hq_def
    have hv₁ : deriv (chartCurve (I := I) q Γ₁) 0
        = ((trivializationAt E (TangentSpace I) q).continuousLinearMapAt ℝ q)
            (mfderiv 𝓘(ℝ, ℝ) I Γ₁ 0 (1 : ℝ) : E) :=
      chartCurve_deriv_zero_eq (I := I) q (hmdiff₁ 0) rfl rfl
    have hv₂ : deriv (chartCurve (I := I) q Γ₂) 0
        = ((trivializationAt E (TangentSpace I) q).continuousLinearMapAt ℝ q)
            (mfderiv 𝓘(ℝ, ℝ) I Γ₂ 0 (1 : ℝ) : E) :=
      chartCurve_deriv_zero_eq (I := I) q (hmdiff₂ 0) h0.symm rfl
    have hvel0 : deriv (chartCurve (I := I) q Γ₁) 0
        = deriv (chartCurve (I := I) q Γ₂) 0 := by
      rw [hv₁, hv₂, hv]
    exact geodesic_eventuallyEq_of_initial_local (I := I) g hc₁ hc₂ h₁ h₂ h0
      (by rw [hq_def] at hvel0; exact hvel0)
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hS_univ : S = Set.univ := hS_clopen.eq_univ ⟨0, h0S⟩
  funext t
  have htS : t ∈ S := by rw [hS_univ]; exact Set.mem_univ t
  exact htS.self_of_nhds

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Spray homogeneity of the intrinsic geodesic.**  For every scalar `t`,
`intrinsicGeodesic g hEnorm p (t • u) 1 = intrinsicGeodesic g hEnorm p u t`.
Equivalently `expMapIntrinsic p (t • u) = intrinsicGeodesic p u t`, so the radial
ray `s ↦ expMapIntrinsic p (s • u)` is the single smooth geodesic
`intrinsicGeodesic p u`. -/
theorem intrinsicGeodesic_smul
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u : TangentSpace I p) (t : ℝ) :
    intrinsicGeodesic (I := I) g hEnorm p (t • u) 1
      = intrinsicGeodesic (I := I) g hEnorm p u t := by
  classical
  set φ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u with hφ_def
  set Γrep : ℝ → M := fun s => φ (t * s) with hΓrep_def
  have hφ_geo : Geodesic.IsGeodesic (I := I) g φ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hφ_cont : Continuous φ := intrinsicGeodesic_continuous (I := I) g hEnorm p u
  have hφ0 : φ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p u
  have hφ_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I φ 0 :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p u).contMDiffAt
      (Filter.univ_mem)).mdifferentiableAt (by norm_num)
  have hφv : (mfderiv 𝓘(ℝ, ℝ) I φ 0 (1 : ℝ) : E) = (u : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p u
  have hΓrep_geo : Geodesic.IsGeodesic (I := I) g Γrep := by
    intro s
    exact hasGeodesicEquationAt_comp_const_smul (I := I) g t s (hφ_geo (t * s))
  have hΓrep_cont : Continuous Γrep := hφ_cont.comp (by fun_prop)
  have hΓrep0 : Γrep 0 = p := by rw [hΓrep_def]; simp only [mul_zero]; exact hφ0
  have hscale_mfderiv : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => t * s)
      (0 : ℝ) (t • ContinuousLinearMap.id ℝ ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    have hfd : HasFDerivAt (fun s : ℝ => t * s) (t • ContinuousLinearMap.id ℝ ℝ) (0 : ℝ) := by
      simpa [mul_comm] using
        ((hasFDerivAt_id (0 : ℝ)).const_mul t)
    simpa using hfd
  have hφ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I φ (t * (0 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I φ 0) := by
    rw [mul_zero]; exact hφ_mdiff0.hasMFDerivAt
  have hΓrep_mfderiv : mfderiv 𝓘(ℝ, ℝ) I Γrep 0
      = (mfderiv 𝓘(ℝ, ℝ) I φ 0).comp (t • ContinuousLinearMap.id ℝ ℝ) :=
    (hφ_at.comp 0 hscale_mfderiv).mfderiv
  have hΓrep_vel : (mfderiv 𝓘(ℝ, ℝ) I Γrep 0 (1 : ℝ) : E) = ((t • u : TangentSpace I p) : E) := by
    have h1 : mfderiv 𝓘(ℝ, ℝ) I Γrep 0 (1 : ℝ)
        = (mfderiv 𝓘(ℝ, ℝ) I φ 0) ((t • ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)) := by
      rw [hΓrep_mfderiv]; rfl
    have h2 : (t • ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) = t • (1 : ℝ) := by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    have happ : mfderiv 𝓘(ℝ, ℝ) I Γrep 0 (1 : ℝ)
        = t • (mfderiv 𝓘(ℝ, ℝ) I φ 0) (1 : ℝ) := by
      rw [h1, h2]
      exact ContinuousLinearMap.map_smul (mfderiv 𝓘(ℝ, ℝ) I φ 0) t (1 : ℝ)
    rw [happ]
    exact congrArg (t • ·) hφv
  have hψ_geo : Geodesic.IsGeodesic (I := I) g (intrinsicGeodesic (I := I) g hEnorm p (t • u)) :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p (t • u)
  have hψ_cont : Continuous (intrinsicGeodesic (I := I) g hEnorm p (t • u)) :=
    intrinsicGeodesic_continuous (I := I) g hEnorm p (t • u)
  have hψ0 : intrinsicGeodesic (I := I) g hEnorm p (t • u) 0 = p :=
    intrinsicGeodesic_zero (I := I) g hEnorm p (t • u)
  have hψv : (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p (t • u)) 0 (1 : ℝ) : E)
      = ((t • u : TangentSpace I p) : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p (t • u)
  have hfoot : Γrep 0 = intrinsicGeodesic (I := I) g hEnorm p (t • u) 0 := by
    rw [hΓrep0, hψ0]
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I Γrep 0 (1 : ℝ) : E)
      = (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p (t • u)) 0 (1 : ℝ) : E) := by
    rw [hΓrep_vel, hψv]
  have heq : Γrep = intrinsicGeodesic (I := I) g hEnorm p (t • u) :=
    isGeodesic_eq_of_initial (I := I) g hΓrep_geo hψ_geo hΓrep_cont hψ_cont hfoot hvel
  have h1 : Γrep 1 = intrinsicGeodesic (I := I) g hEnorm p (t • u) 1 := by rw [heq]
  rw [hΓrep_def] at h1
  simp only [mul_one, hφ_def] at h1
  exact h1.symm

end AgreementBridge

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
