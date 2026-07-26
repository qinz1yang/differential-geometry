import DifferentialGeometry.Geometry.Comparison.Volume.BishopIntrinsic
import DifferentialGeometry.Geometry.Comparison.Variation.MinimizingNoConj

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Intrinsic Bishop ratio — consumer adapters

Thin consumer-facing adapters on the whole-tail intrinsic Bishop ratio
`exists_intrRatio`.  Along the complete intrinsic geodesic
`γ = intrinsicGeodesic g hEnorm p u` (speed `ell = √(g.inner p u u)`) with the
transverse Jacobi frame `V`, under a lower Ricci bound `Ric ≥ -(n-1)q²` and
interior nonconjugacy:

* `intrCross_anti` — division-free (cross-multiplicative) Bishop ratio
  monotonicity, the form the relative Bishop--Gromov volume comparison consumes.
* `densUB_of_pole` — antitone ratio plus a near-pole cap gives a uniform
  pointwise upper density bound; and `intrDens_le_hyp`, its intrinsic instance
  `curveDensity ≤ N · hypDensity`.
* `intrNoConj_min` — the interior nonconjugacy hypothesis packaged from a
  minimizing intrinsic tail (`tail_no_conj`).

The model is scaled by the speed: comparisons are against `hypDensity (q * ell)`
and `hypMeanCurv (q * ell)`, the true form (see `IntrinsicRatio.md`).
-/

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open CovariantDerivativeAlong
open Exponential
open Geodesic
open Variation
open BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Division-free Bishop ratio monotonicity along the complete intrinsic
geodesic: for `s ≤ t` in the conjugate-free window,
`curveDensity t · hypDensity s ≤ curveDensity s · hypDensity t`.  The
cross-multiplicative form consumed by the relative Bishop--Gromov comparison. -/
theorem intrCross_anti
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      LinearIndependent Real v ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
      let ell := Real.sqrt (g.inner p u u)
      ∀ s t, s ∈ Set.Ioo (0 : Real) b → t ∈ Set.Ioo (0 : Real) b → s ≤ t →
        curveDensity (I := I) g γ V t *
            hypDensity (q * ell) (Module.finrank Real E - 1) s ≤
          curveDensity (I := I) g γ V s *
            hypDensity (q * ell) (Module.finrank Real E - 1) t := by
  obtain ⟨v, hv, hperp, hanti⟩ :=
    exists_intrRatio (I := I) g hEnorm p u q b hq hd hu hno hRic
  refine ⟨v, hv, hperp, ?_⟩
  intro γ V ell s t hs ht hst
  have hqell : 0 ≤ q * ell := mul_nonneg hq (Real.sqrt_nonneg _)
  have hps : 0 < hypDensity (q * ell) (Module.finrank Real E - 1) s :=
    hypDensity_pos hqell hs.1
  have hpt : 0 < hypDensity (q * ell) (Module.finrank Real E - 1) t :=
    hypDensity_pos hqell ht.1
  have hR : curveDensity (I := I) g γ V t /
        hypDensity (q * ell) (Module.finrank Real E - 1) t ≤
      curveDensity (I := I) g γ V s /
        hypDensity (q * ell) (Module.finrank Real E - 1) s :=
    hanti hs ht hst
  rw [div_le_div_iff₀ hpt hps] at hR
  exact hR

/-- Antitone density ratio plus a near-pole cap gives a uniform pointwise upper
density bound on the whole window.  Pure consequence of monotonicity: the ratio
sup is attained at the pole. -/
theorem densUB_of_pole
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : Real → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) {q' : Real} {d : ℕ} {b N : Real}
    (hq' : 0 ≤ q')
    (hanti : AntitoneOn
      (fun t => curveDensity (I := I) g γ V t / hypDensity q' d t)
      (Set.Ioo (0 : Real) b))
    (hcap : ∀ᶠ t in 𝓝[>] (0 : Real),
      curveDensity (I := I) g γ V t / hypDensity q' d t ≤ N) :
    ∀ t ∈ Set.Ioo (0 : Real) b,
      curveDensity (I := I) g γ V t ≤ N * hypDensity q' d t := by
  intro t ht
  have hev : ∀ᶠ s in 𝓝[>] (0 : Real),
      curveDensity (I := I) g γ V s / hypDensity q' d s ≤ N ∧
        s ∈ Set.Ioo (0 : Real) t := by
    filter_upwards [hcap, Ioo_mem_nhdsGT ht.1] with s hsN hsIoo
    exact ⟨hsN, hsIoo⟩
  obtain ⟨s, hsN, hs⟩ := hev.exists
  have hsb : s ∈ Set.Ioo (0 : Real) b := ⟨hs.1, hs.2.trans ht.2⟩
  have hRt : curveDensity (I := I) g γ V t / hypDensity q' d t ≤ N :=
    le_trans (hanti hsb ht hs.2.le) hsN
  have hpt : 0 < hypDensity q' d t := hypDensity_pos hq' ht.1
  rwa [div_le_iff₀ hpt] at hRt

/-- A nonzero tangent vector plus an orthogonal linearly independent transverse
family assembles into an `Option`-indexed basis of `E`, with `none ↦ u` and
`some i ↦ v i`.  (Weaker input than `exists_scaled_basis`: only `u ⊥ vᵢ` and
`LinearIndependent v`, not orthonormality.) -/
private theorem exists_perp_basis
    (g : SmoothRiemannianMetric I M) (p : M) (u : TangentSpace I p)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hv : LinearIndependent Real v)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hu : 0 < g.inner p u u) :
    ∃ B : Module.Basis (Option (Fin (Module.finrank Real E - 1))) Real E,
      B none = (u : E) ∧ ∀ i, B (some i) = (v i : E) := by
  classical
  have hu_ne : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  let φ : TangentSpace I p →ₗ[Real] Real := (g.inner p u).toLinearMap
  have hVker : Set.range v ⊆ LinearMap.ker φ := by
    rintro y ⟨i, rfl⟩
    change g.inner p u (v i) = 0
    exact hperp i
  have hZspan : u ∉ Submodule.span Real (Set.range v) := by
    intro hmem
    have hker : u ∈ LinearMap.ker φ := (Submodule.span_le.2 hVker) hmem
    have hzero : g.inner p u u = 0 := hker
    exact hu.ne' hzero
  have hWLI : LinearIndependent Real
      (fun o : Option (Fin (Module.finrank Real E - 1)) =>
        Option.casesOn' o u v) := hv.option hZspan
  have hdim : 0 < Module.finrank Real (TangentSpace I p) :=
    Module.finrank_pos_iff.mpr ⟨u, 0, hu_ne⟩
  have hcardW : Fintype.card (Option (Fin (Module.finrank Real E - 1))) =
      Module.finrank Real (TangentSpace I p) := by
    rw [Fintype.card_option, Fintype.card_fin]
    exact Nat.sub_add_cancel hdim
  let b : Module.Basis (Option (Fin (Module.finrank Real E - 1))) Real
      (TangentSpace I p) :=
    basisOfLinearIndependentOfCardEqFinrank hWLI hcardW
  have hb : ∀ o, b o = Option.casesOn' o u v :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hWLI hcardW)
  refine ⟨b, ?_, ?_⟩
  · exact hb none
  · intro i; exact hb (some i)

/-- The hyperbolic warping function dominates the radius. -/
private lemma hypSn_ge_id {q : Real} (hq : 0 ≤ q) {t : Real} (ht : 0 ≤ t) :
    t ≤ hypSn q t := by
  by_cases hq0 : q = 0
  · simp [hypSn, hq0]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [hypSn, if_neg hq0, le_div_iff₀ hqpos]
    calc t * q = q * t := mul_comm _ _
      _ ≤ Real.sinh (q * t) := Real.self_le_sinh_iff.mpr (mul_nonneg hq ht)

/-- The hyperbolic model density dominates the Euclidean radial density. -/
private lemma hypDens_ge_pow {q : Real} (hq : 0 ≤ q) {d : ℕ} {t : Real}
    (ht : 0 ≤ t) : t ^ d ≤ hypDensity q d t := by
  rw [hypDensity]
  exact pow_le_pow_left₀ ht (hypSn_ge_id hq ht) d

/-- Near-pole cap of the intrinsic transverse-Jacobi density ratio.

FRONTIER (missing API).  For any linearly independent transverse frame the ratio
`curveDensity / hypDensity` has a finite `t → 0⁺` limit (`= 1` for an
orthonormal-at-pole frame), hence is eventually bounded.  The comparison tree
currently exposes only the *lower* pole ratio (`radialRatio_auto`) and heavy
chart-scale Gronwall *upper* density bounds; the light near-pole upper cap is not
yet available.  Route to discharge (see `IntrinsicRatio.md`): `normalDensity_curve`
(chart↔curve density identity) + boundedness of `normalChartDensity` near `0`
(from `paramDensity_continuousOn_chart`) + `hypSn q t ≥ t`, transported to the
intrinsic picture by `intrJacobi_raw`. -/
private theorem intrPoleCap
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q : Real) (hq : 0 ≤ q)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hv : LinearIndependent Real v)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hu : 0 < g.inner p u u) :
    ∃ N : Real, 0 < N ∧ ∀ᶠ t in 𝓝[>] (0 : Real),
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        hypDensity (q * Real.sqrt (g.inner p u u))
          (Module.finrank Real E - 1) t ≤ N := by
  classical
  obtain ⟨B, hBnone, hBsome⟩ := exists_perp_basis (I := I) g p u v hv hperp hu
  let ue : E := (u : E)
  set ell : Real := Real.sqrt (g.inner p u u) with hell_def
  have hqell : 0 ≤ q * ell := mul_nonneg hq (Real.sqrt_nonneg _)
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hue_ne : ue ≠ 0 := hu_ne
  have hunorm : 0 < ‖ue‖ := norm_pos_iff.mpr hue_ne
  -- chart window `Ioo 0 b₀`
  set b₀ : Real := expMapC2Radius (I := I) g p / ‖ue‖ with hb₀_def
  have hb₀ : 0 < b₀ :=
    div_pos (expMapC2Radius_pos (I := I) g p) hunorm
  have hrad : ∀ r ∈ Set.Ioo (0 : Real) b₀,
      ‖r • ue‖ < expMapC2Radius (I := I) g p := by
    intro r hr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, ← lt_div_iff₀ hunorm]
    exact hr.2
  have hsrc : Set.MapsTo (fun r : Real => r • ue) (Set.Ioo (0 : Real) b₀)
      (expMapDiffeo (I := I) g p).source := by
    intro r hr
    show r • ue ∈ (expMapDiffeo (I := I) g p).source
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p (hrad r hr)
  have hBperp : ∀ i, g.inner p ue (B (some i)) = 0 := by
    intro i
    rw [hBsome i]
    exact hperp i
  obtain ⟨c, hc, hdensity⟩ :=
    normalDensity_curve (I := I) g p ue B hBnone hBperp hsrc hrad
  -- near-pole bound on the chart density
  have hcontAt : ContinuousAt (normalChartDensity (I := I) g p) 0 := by
    have hcont : ContinuousOn (normalChartDensity (I := I) g p)
        (expMapDiffeo (I := I) g p).source := by
      simpa only [normalChartDensity] using
        paramDensity_contOn (I := I) g (expMapDiffeo (I := I) g p)
    exact hcont.continuousAt ((expMapDiffeo (I := I) g p).open_source.mem_nhds
      (zero_mem_expMapDiffeo_source (I := I) g p))
  have hncd0 : 0 < normalChartDensity (I := I) g p 0 := by
    simpa only [normalChartDensity] using
      paramDensity_pos (I := I) g (expMapDiffeo (I := I) g p)
        (zero_mem_expMapDiffeo_source (I := I) g p)
  set M₀ : Real := normalChartDensity (I := I) g p 0 + 1 with hM₀_def
  have hM₀pos : 0 < M₀ := by rw [hM₀_def]; linarith [hncd0]
  have htend : Tendsto (fun r : Real => r • ue)
      (𝓝[>] (0 : Real)) (𝓝 (0 : E)) := by
    have hcont : Continuous fun r : Real => r • ue :=
      continuous_id.smul continuous_const
    have hzero : Tendsto (fun r : Real => r • ue)
        (𝓝 (0 : Real)) (𝓝 (0 : E)) := by
      simpa using (hcont.continuousAt (x := (0 : Real))).tendsto
    exact hzero.mono_left inf_le_left
  have hncd_t : ∀ᶠ t in 𝓝[>] (0 : Real),
      normalChartDensity (I := I) g p (t • ue) < M₀ := by
    have hbnd : ∀ᶠ w in 𝓝 (0 : E),
        normalChartDensity (I := I) g p w < M₀ :=
      hcontAt (Iio_mem_nhds (by rw [hM₀_def]; exact lt_add_one _))
    exact htend.eventually hbnd
  -- intrinsic density agrees with the radial one near the pole
  have hcurveEq : ∀ᶠ t in 𝓝[>] (0 : Real),
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t =
        curveDensity (I := I) g (radialCurve (I := I) g p ue)
          (fun i => radialJacobiField (I := I) g p ue (B (some i))) t := by
    have hcurve : ∀ᶠ t in 𝓝[>] (0 : Real),
        intrinsicGeodesic (I := I) g hEnorm p u t =
          radialCurve (I := I) g p ue t := by
      filter_upwards [intrJacobi_raw (I := I) g hEnorm p ue (0 : E)]
        with t ht using ht.1
    have hfields : ∀ᶠ t in 𝓝[>] (0 : Real), ∀ i,
        (intrinsicJacobi (I := I) g hEnorm p u (v i) t : E) =
          (radialJacobiField (I := I) g p ue (B (some i)) t : E) := by
      refine Filter.eventually_all.2 (fun i => ?_)
      filter_upwards [intrJacobi_raw (I := I) g hEnorm p ue (v i : E)]
        with t ht
      rw [hBsome i]
      exact ht.2
    filter_upwards [hcurve, hfields] with t hct hft
    have hgram :
        curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t =
          curveGram (I := I) g (radialCurve (I := I) g p ue)
            (fun i => radialJacobiField (I := I) g p ue (B (some i))) t := by
      ext i j
      simp only [curveGram, Matrix.of_apply]
      rw [hct, hft i, hft j]
    simp only [curveDensity, hgram]
  -- assemble the cap `N = M₀ / c`
  refine ⟨M₀ / c, div_pos hM₀pos hc, ?_⟩
  have hwin : Set.Ioo (0 : Real) b₀ ∈ 𝓝[>] (0 : Real) :=
    Ioo_mem_nhdsGT hb₀
  filter_upwards [hncd_t, hcurveEq, self_mem_nhdsWithin, hwin]
    with t hncdt hcurvet htpos htwin
  have ht0 : 0 < t := htpos
  set CDr : Real := curveDensity (I := I) g (radialCurve (I := I) g p ue)
    (fun i => radialJacobiField (I := I) g p ue (B (some i))) t with hCDr_def
  have hdens_t : t ^ (Module.finrank Real E - 1) *
      normalChartDensity (I := I) g p (t • ue) = c * CDr := by
    have := hdensity t htwin
    rwa [Fintype.card_fin] at this
  have hHDpos : 0 < hypDensity (q * ell) (Module.finrank Real E - 1) t :=
    hypDensity_pos hqell ht0
  have hHDge : t ^ (Module.finrank Real E - 1) ≤
      hypDensity (q * ell) (Module.finrank Real E - 1) t :=
    hypDens_ge_pow hqell ht0.le
  rw [hcurvet, div_le_div_iff₀ hHDpos hc]
  have hCDrc : CDr * c = t ^ (Module.finrank Real E - 1) *
      normalChartDensity (I := I) g p (t • ue) := by
    rw [mul_comm CDr c, ← hdens_t]
  rw [hCDrc]
  calc t ^ (Module.finrank Real E - 1) *
        normalChartDensity (I := I) g p (t • ue)
      ≤ t ^ (Module.finrank Real E - 1) * M₀ :=
        mul_le_mul_of_nonneg_left hncdt.le (pow_nonneg ht0.le _)
    _ = M₀ * t ^ (Module.finrank Real E - 1) := by ring
    _ ≤ M₀ * hypDensity (q * ell) (Module.finrank Real E - 1) t :=
        mul_le_mul_of_nonneg_left hHDge hM₀pos.le

/-- Pointwise upper density along the conjugate-free intrinsic geodesic:
`curveDensity g γ V t ≤ N · hypDensity (q·ℓ) d t` on the whole window, for a
positive pole normalization `N`.  Priority consumer for the segment-domain
polar-measure representation.  Reduces (via `densUB_of_pole`) to the near-pole
frontier `intrPoleCap`. -/
theorem intrDens_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      LinearIndependent Real v ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
      let ell := Real.sqrt (g.inner p u u)
      ∃ N : Real, 0 < N ∧ ∀ t ∈ Set.Ioo (0 : Real) b,
        curveDensity (I := I) g γ V t ≤
          N * hypDensity (q * ell) (Module.finrank Real E - 1) t := by
  obtain ⟨v, hv, hperp, hanti⟩ :=
    exists_intrRatio (I := I) g hEnorm p u q b hq hd hu hno hRic
  refine ⟨v, hv, hperp, ?_⟩
  intro γ V ell
  obtain ⟨N, hN, hcap⟩ := intrPoleCap (I := I) g hEnorm p u q hq v hv hperp hu
  exact ⟨N, hN,
    densUB_of_pole (I := I) g γ V (mul_nonneg hq (Real.sqrt_nonneg _)) hanti hcap⟩

/-- Interior nonconjugacy for the intrinsic Bishop adapters, packaged from a
minimizing intrinsic tail (`tail_no_conj`): along the shifted tail geodesic that
starts at `z.proj` with velocity `uTail`, every interior radial time is
nonconjugate.  Supplies the `hno` hypothesis of `intrCross_anti` /
`intrDens_le_hyp` with base point `z.proj`, direction `uTail` and window `b = 1`. -/
theorem intrNoConj_min
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {O x : M} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = (riemannianEDist I O x).toReal)
    (hr : 0 < (riemannianEDist I O x).toReal)
    {s₀ : Real} (hs₀ : s₀ ∈ Set.Ioo (0 : Real) 1) :
    let z := intrinsicVelocityLift (I := I) g hEnorm O v s₀
    let uTail : TangentSpace I z.proj := (1 - s₀) • z.snd
    ∀ t ∈ Set.Ioo (0 : Real) 1,
      ¬ IsConjVec (I := I) g hEnorm z.proj
        ((t • uTail : TangentSpace I z.proj) : E) := by
  intro z uTail t ht
  exact tail_no_conj (I := I) g hEnorm v hexp hlen hr hs₀ t
    (Set.Ioo_subset_Ioc_self ht)

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
