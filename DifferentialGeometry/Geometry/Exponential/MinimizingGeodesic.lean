import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Exponential.IntrinsicExpContinuity
import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option linter.unusedSectionVars false

/-!
# Hopf–Rinow minimising-geodesic existence via the ray/sphere argument

For a complete Riemannian manifold the intrinsic exponential map
`expMapIntrinsic g hEnorm p v = intrinsicGeodesic g hEnorm p v 1`
(`Exponential/IntrinsicExp.lean`) follows the *complete* moving-foot geodesic
through `p` with launch velocity `v`.  Unlike the chart-fixed `expMap`, this
object is genuinely defined and geodesic across charts (and continuous in `v`,
`expMapIntrinsic_continuous`).  This file works towards the velocity-identified
Hopf–Rinow surjectivity

`∀ p q, ∃ v, expMapIntrinsic g hEnorm p v = q ∧
    √(g_p(v, v)) = (riemannianEDist I p q).toReal`,

i.e. every `q` is reached by a radial geodesic whose `g`-speed equals the
Riemannian distance.  (There is no `riemannianDist` definition in the project;
the real-valued Riemannian distance is `(riemannianEDist I p q).toReal`, and the
velocity bound is the intrinsic `g`-norm `√(g_p(v, v))`, never the model-`E`
norm `‖v‖`.)

## The classical ray/sphere argument

Let `r := (riemannianEDist I p q).toReal`.  If `r = 0` then `q = p` and `v := 0`
works.  Otherwise pick `δ ∈ (0, expRadiusGp g p)` and form the **sphere**
`S_δ := { expMapIntrinsic g hEnorm p (δ • w) | √(g_p(w, w)) = 1 }`, the
continuous image of the compact `g`-unit sphere, hence compact.  Choose
`x₀ := expMapIntrinsic g hEnorm p (δ • u)` minimising `q ↦ riemannianEDist · q`
over `S_δ`.  The triangle inequality plus the Gauss-lemma radial local minimality
`normalBall_radial_length_le_riemannianEDist` give `riemannianEDist x₀ q = r - δ` (the
"ray jumps onto the sphere" step).  Tracking the unit-speed radial geodesic
`γ(t) := expMapIntrinsic g hEnorm p (t • u)` (defined for all `t` by
completeness) and the propagation set

`A := { t ∈ [0, r] | (riemannianEDist I (γ t) q).toReal = r - t }`,

one shows `A` is closed, `δ ∈ A`, and `sup A = r` (repeating the sphere argument
at `γ(t₀)` whenever `t₀ := sup A < r`).  At `t = r`, `riemannianEDist (γ r) q = 0`
forces `γ r = q`, so `v := r • u` realises the conclusion (`√(g_p(r•u, r•u)) =
r·√(g_p(u,u)) = r` by homogeneity and `√(g_p(u,u)) = 1`).

## What this file establishes unconditionally

* `gInner_smul_self` / `sqrt_gInner_smul_self` — the degree-two homogeneity of
  the `g`-quadratic form and its square root.
* `gUnitSphere_isCompact` — the `g`-unit sphere `{w | g_p(w, w) = 1}` in `T_p M`
  is compact (closed equalizer inside the compact closed `g`-ball, in the proper
  finite-dimensional tangent space).
* `intrinsicSphere_isCompact` — the image `S_δ` of the `g`-unit sphere under
  `w ↦ expMapIntrinsic g hEnorm p (δ • w)` is compact (continuous image of a
  compact set, via the proven `expMapIntrinsic_continuous`).
* `exists_min_riemannianEDist_on_intrinsicSphere` — the sphere-minimisation step
  (`IsCompact.exists_isMinOn` on the continuous `riemannianEDist · q`).
* `propagationSet_isClosed` — closedness of the propagation set `A`.
* `riemannianEDist_eq_zero_imp_eq` — point separation (the `r = 0` base case
  reduction `riemannianEDist I p q = 0 → p = q`).
* `riemannianEDist_ne_top` — finiteness of the Riemannian distance (so that
  `(riemannianEDist I p q).toReal` is informative).
* `radial_riemannianEDist_eq_of_small'` — the arbitrary-small-vector radial
  Riemannian distance (`riemannianEDist p (expMapIntrinsic p w) = ofReal
  √(g_p(w, w))`), generalising the `δ • u` form by unit-direction rescaling.
* `expMapIntrinsic_local_surjective` — the **local radial surjectivity** of
  `expMapIntrinsic` (the easy local case `normal ball = metric ball` within the
  injectivity radius): every point in the normal chart with `g`-small chart
  coordinate is reached by a radial geodesic whose `g`-speed equals the
  Riemannian distance, via the normal-chart round-trip plus the agreement bridge.

Inside the headline body, the nonemptiness `0 ∈ A`, the supremum attainment
`t₀ := sup A ∈ A` (`IsClosed.csSup_mem`), and the
`t₀ = r ⟹ γ r = q ⟹ v := r • u` conclusion are also all proved unconditionally.

## The closed propagation argument

The headline `hopf_rinow_expMapIntrinsic_surjective_minimizing` is established unconditionally.  The
strict-supremum step `t₀ < r → False` (the "no-corner" moving-foot extension of
`A` past `t₀`) is the reusable metric-sphere distance drop `sphere_jump` applied at
the moving foot `c := γ(t₀)`, combined with the broken-geodesic no-corner lemma
`broken_minimizer_velocity_match` and the autonomous time-translation continuation
`intrinsicGeodesic_continuation`.  `sphere_jump` reads the radial distance and the
sphere distance drop off the Gauss inclusion `metricBall_subset_normalBall` (the
path-crosses-the-metric-sphere intermediate-value identification) and the radial
distance identity; its sphere compactness routes through the chart-smooth `expMap`
on the agreement ball (so it does not consume the in-velocity joint continuity of
the intrinsic exponential).
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

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
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Degree-two homogeneity of the `g`-quadratic form.**
`g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v`. -/
lemma gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    (b : ℝ) (v : TangentSpace I p) :
    g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v := by
  rw [(g.inner p).map_smul b v, ContinuousLinearMap.smul_apply,
    (g.inner p v).map_smul b v]
  simp only [smul_eq_mul]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Homogeneity of the `g`-norm.** For `0 ≤ b`,
`√(g.inner p (b • v) (b • v)) = b * √(g.inner p v v)`. -/
lemma sqrt_gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    {b : ℝ} (hb : 0 ≤ b) (v : TangentSpace I p) :
    Real.sqrt (g.inner p (b • v) (b • v)) = b * Real.sqrt (g.inner p v v) := by
  rw [gInner_smul_self (I := I) g p b v, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq hb]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The `g`-quadratic form `g.inner p v v` is non-negative. -/
lemma gInner_self_nonneg (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : 0 ≤ g.inner p v v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · exact (g.pos p v hv).le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The map `v ↦ g.inner p v v` is continuous on `T_p M`. -/
lemma continuous_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => g.inner p v v) :=
  (g.inner p).continuous.clm_apply continuous_id

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The map `v ↦ √(g.inner p v v)` is continuous on `T_p M`. -/
lemma continuous_sqrt_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) :=
  Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g p)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The `g`-unit sphere is closed.** It is the equalizer of the continuous map
`v ↦ g.inner p v v` with the constant `1`. -/
lemma gUnitSphere_isClosed (g : SmoothRiemannianMetric I M) (p : M) :
    IsClosed {w : TangentSpace I p | g.inner p w w = 1} :=
  isClosed_eq (continuous_gInner_self (I := I) g p) continuous_const

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The `g`-unit sphere is bounded.** The von Neumann boundedness of the unit
`g`-ball `{w | g_p(w, w) < 1}` (`g.isVonNBounded`) gives a model-norm bound `r` on
it; rescaling `v ↦ 2⁻¹ • v` carries a `g`-unit vector into the unit `g`-ball
(`g_p(2⁻¹•v, 2⁻¹•v) = 1/4 < 1`), so `‖v‖ ≤ 2 r`. -/
lemma gUnitSphere_isBounded (g : SmoothRiemannianMetric I M) (p : M) :
    Bornology.IsBounded {w : TangentSpace I p | g.inner p w w = 1} := by
  obtain ⟨r, hr⟩ :=
    (NormedSpace.isVonNBounded_iff' ℝ (E := TangentSpace I p)).1 (g.isVonNBounded p)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2 * r, fun v hv => ?_⟩
  have hgvv : g.inner p v v = 1 := hv
  set w : TangentSpace I p := (2 : ℝ)⁻¹ • v with hw
  have hgw : g.inner p w w < 1 := by
    have hscale : g.inner p w w = (2 : ℝ)⁻¹ ^ 2 * g.inner p v v :=
      gInner_smul_self (I := I) g p _ v
    rw [hscale, hgvv]; norm_num
  have hwnorm : ‖w‖ ≤ r := hr w hgw
  have hv_eq : v = (2 : ℝ) • w := by rw [hw, smul_smul]; norm_num
  rw [hv_eq, norm_smul, Real.norm_eq_abs]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  exact mul_le_mul_of_nonneg_left hwnorm (by norm_num)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The `g`-unit sphere is compact.** Closed (`gUnitSphere_isClosed`) and
bounded (`gUnitSphere_isBounded`) in the proper finite-dimensional tangent
space. -/
lemma gUnitSphere_isCompact (g : SmoothRiemannianMetric I M) (p : M) :
    IsCompact {w : TangentSpace I p | g.inner p w w = 1} := by
  haveI : ProperSpace (TangentSpace I p) :=
    FiniteDimensional.proper_real (TangentSpace I p)
  exact Metric.isCompact_of_isClosed_isBounded
    (gUnitSphere_isClosed (I := I) g p) (gUnitSphere_isBounded (I := I) g p)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Compactness of the intrinsic sphere `S_δ`.** For any `δ`, the image of the
`g`-unit sphere under `w ↦ expMapIntrinsic g hEnorm p (δ • w)` is compact. -/
theorem intrinsicSphere_isCompact
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (δ : ℝ) :
    IsCompact
      ((fun w : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p (δ • w))
        '' {w : TangentSpace I p | g.inner p w w = 1}) := by
  have hexp : Continuous (fun v : TangentSpace I p =>
      expMapIntrinsic (I := I) g hEnorm p v) :=
    expMapIntrinsic_continuous (I := I) g hEnorm p
  have hscale : Continuous (fun w : TangentSpace I p => δ • w) :=
    continuous_const_smul δ
  have hcomp : Continuous
      (fun w : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p (δ • w)) :=
    hexp.comp hscale
  exact (gUnitSphere_isCompact (I := I) g p).image hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Continuity of `q' ↦ riemannianEDist I q' q` for the manifold topology.

The ambient `[PseudoEMetricSpace M]` need not have the manifold topology, so its
`edist`-continuity does not transfer; instead we use Mathlib's canonical
`PseudoEMetricSpace.ofRiemannianMetric I M`, whose `edist` is `riemannianEDist I`
definitionally and whose topology is the manifold topology by construction. -/
lemma continuous_riemannianEDist_to
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (q : M) :
    Continuous (fun q' : M => riemannianEDist I q' q) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_id.edist continuous_const)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Sphere-minimisation step.** On the (nonempty) compact intrinsic sphere
`S_δ` the continuous function `x ↦ riemannianEDist I x q` attains a minimum: there
is a `g`-unit vector `u` with `x₀ := expMapIntrinsic g hEnorm p (δ • u)`
minimising `riemannianEDist · q` over `S_δ`.

Existence of a `g`-unit vector uses the positive dimension of `E`; the minimum is
the extreme value theorem `IsCompact.exists_isMinOn` on the compact `S_δ`. -/
theorem exists_min_riemannianEDist_on_intrinsicSphere
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) (δ : ℝ) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      ∀ w : TangentSpace I p, g.inner p w w = 1 →
        riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (δ • u)) q ≤
          riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (δ • w)) q := by
  classical
  set f : TangentSpace I p → M :=
    fun w => expMapIntrinsic (I := I) g hEnorm p (δ • w) with hf_def
  set sph : Set (TangentSpace I p) := {w : TangentSpace I p | g.inner p w w = 1}
    with hsph_def
  have hsph_ne : sph.Nonempty := by
    have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
    obtain ⟨x, hx_ne⟩ : ∃ x : TangentSpace I p, x ≠ 0 :=
      ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
    have hc_pos : 0 < g.inner p x x := g.pos p x hx_ne
    have hc_ne : g.inner p x x ≠ 0 := ne_of_gt hc_pos
    set s : ℝ := Real.sqrt (g.inner p x x)⁻¹ with hs_def
    have hs_sq : s * s = (g.inner p x x)⁻¹ := by
      rw [hs_def]
      exact Real.mul_self_sqrt (inv_nonneg.mpr hc_pos.le)
    refine ⟨s • x, ?_⟩
    change g.inner p (s • x) (s • x) = 1
    rw [gInner_smul_self (I := I) g p s x]
    rw [show s ^ 2 = s * s by ring, hs_sq, inv_mul_cancel₀ hc_ne]
  have hcont : Continuous (fun x : M => riemannianEDist I x q) :=
    continuous_riemannianEDist_to (I := I) q
  have hfcont : Continuous f := by
    have hexp : Continuous (fun v : TangentSpace I p =>
        expMapIntrinsic (I := I) g hEnorm p v) :=
      expMapIntrinsic_continuous (I := I) g hEnorm p
    exact hexp.comp (continuous_const_smul δ)
  have hcompact : IsCompact sph := gUnitSphere_isCompact (I := I) g p
  have hcontOn : ContinuousOn (fun w : TangentSpace I p =>
      riemannianEDist I (f w) q) sph :=
    (hcont.comp hfcont).continuousOn
  obtain ⟨u, hu_mem, hu_min⟩ :=
    hcompact.exists_isMinOn hsph_ne hcontOn
  refine ⟨u, hu_mem, ?_⟩
  intro w hw
  exact hu_min (show w ∈ sph from hw)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The radial ray `t ↦ expMapIntrinsic g hEnorm p (t • u)` is continuous in
`t`.  By the spray-homogeneity identity `intrinsicGeodesic_smul`,
`expMapIntrinsic p (t • u) = intrinsicGeodesic p u t`, so the ray is the single
intrinsic geodesic `intrinsicGeodesic p u`, whose continuity in time is the
(per-launch-velocity) `intrinsicGeodesic_continuous` — this route avoids the
in-velocity joint continuity of the exponential map. -/
theorem radialRay_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u : TangentSpace I p) :
    Continuous (fun t : ℝ => expMapIntrinsic (I := I) g hEnorm p (t • u)) := by
  have heq : (fun t : ℝ => expMapIntrinsic (I := I) g hEnorm p (t • u))
      = intrinsicGeodesic (I := I) g hEnorm p u := by
    funext t
    rw [expMapIntrinsic_def, intrinsicGeodesic_smul (I := I) g hEnorm p u t]
  rw [heq]
  exact intrinsicGeodesic_continuous (I := I) g hEnorm p u

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Finiteness of the Riemannian distance** on a connected manifold: any two
points have `riemannianEDist I p q ≠ ⊤`.  The finite-distance locus from `p` is
clopen (open: a finite point has a neighbourhood of finite points by the local
bound `eventually_riemannianEDist_lt` and the triangle inequality; closed: the
infinite locus is open by the same bound) and contains `p`, so by connectedness it
is everything. -/
theorem riemannianEDist_ne_top
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (p q : M) : riemannianEDist I p q ≠ (⊤ : ℝ≥0∞) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  set S : Set M := {z : M | riemannianEDist I p z ≠ ⊤} with hS
  have hpS : p ∈ S := by
    simp only [hS, Set.mem_setOf_eq, riemannianEDist_self]; exact ENNReal.zero_ne_top
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hfin : riemannianEDist I p z₀ ≠ ⊤ := hz₀
    have hloc : ∀ᶠ z in nhds z₀, riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_setOf_eq]
    have htri : riemannianEDist I p z ≤
        riemannianEDist I p z₀ + riemannianEDist I z₀ z := riemannianEDist_triangle
    have hlt : riemannianEDist I p z < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hfin,
          lt_of_lt_of_le hz (by norm_num)⟩)
    exact hlt.ne
  have hScompl_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hinf : riemannianEDist I p z₀ = ⊤ := by
      simpa only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hz₀
    have hloc : ∀ᶠ z in nhds z₀, riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    by_contra hpz
    have hpz' : riemannianEDist I p z ≠ ⊤ := hpz
    have htri : riemannianEDist I p z₀ ≤
        riemannianEDist I p z + riemannianEDist I z z₀ := riemannianEDist_triangle
    have hzz0 : riemannianEDist I z z₀ < ⊤ := by
      rw [riemannianEDist_comm]; exact lt_of_lt_of_le hz (by norm_num)
    have hfin' : riemannianEDist I p z₀ < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hpz', hzz0⟩)
    exact hfin'.ne hinf
  have hSclopen : IsClopen S := ⟨⟨hScompl_open⟩, hSopen⟩
  have hSuniv : S = Set.univ := by
    rcases isClopen_iff.mp hSclopen with hempty | huniv
    · exact absurd (hempty ▸ hpS) (by simp)
    · exact huniv
  exact (hSuniv ▸ Set.mem_univ q : q ∈ S)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The real-valued radial distance-to-`q` along the ray,
`t ↦ (riemannianEDist I (γ t) q).toReal`, is continuous. -/
theorem radialDistToReal_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) (u : TangentSpace I p) :
    Continuous (fun t : ℝ =>
      (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal) := by
  have hray : Continuous (fun t : ℝ =>
      expMapIntrinsic (I := I) g hEnorm p (t • u)) :=
    radialRay_continuous (I := I) g hEnorm p u
  have hdist : Continuous (fun x : M => riemannianEDist I x q) :=
    continuous_riemannianEDist_to (I := I) q
  have hcomp : Continuous (fun t : ℝ =>
      riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q) :=
    hdist.comp hray
  refine ENNReal.continuousOn_toReal.comp_continuous hcomp (fun t => ?_)
  rw [Set.mem_setOf_eq]
  exact riemannianEDist_ne_top (I := I) _ q

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Closedness of the propagation set `A`.** For the ray `γ(t) :=
expMapIntrinsic g hEnorm p (t • u)`, target `q`, and radius `r`, the set

`A := { t ∈ [0, r] | (riemannianEDist I (γ t) q).toReal = r - t }`

is closed: it is the intersection of the closed `Icc 0 r` with the equalizer of
the two continuous real functions `t ↦ (riemannianEDist I (γ t) q).toReal`
(`radialDistToReal_continuous`) and `t ↦ r - t`. -/
theorem propagationSet_isClosed
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) (u : TangentSpace I p) (r : ℝ) :
    IsClosed
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) r ∧
        (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
          = r - t} := by
  have hdistCont : Continuous (fun t : ℝ =>
      (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal) :=
    radialDistToReal_continuous (I := I) g hEnorm p q u
  have hlinCont : Continuous (fun t : ℝ => r - t) :=
    continuous_const.sub continuous_id
  have heq : IsClosed
      {t : ℝ |
        (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
          = r - t} :=
    isClosed_eq hdistCont hlinCont
  have hsplit :
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) r ∧
        (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
          = r - t} =
      Set.Icc (0 : ℝ) r ∩
        {t : ℝ |
          (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
            = r - t} := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [hsplit]
  exact isClosed_Icc.inter heq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Point separation from a vanishing Riemannian distance.** On a finite-
dimensional `T2` Riemannian manifold, `riemannianEDist I a b = 0` forces `a = b`.

The manifold is locally compact (finite dimension) and Hausdorff, hence regular,
hence `T3`, so the canonical `EMetricSpace.ofRiemannianMetric` is an actual
(point-separating) emetric structure whose `edist` is `riemannianEDist I`
definitionally; `edist_eq_zero` then concludes. -/
theorem riemannianEDist_eq_zero_imp_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (a b : M) (h : riemannianEDist I a b = 0) : a = b := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  haveI : T3Space M := inferInstance
  letI em : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hedist : @edist M em.toEDist a b = 0 := h
  exact (@edist_eq_zero M em a b).mp hedist

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Constant squared `g`-speed of the intrinsic geodesic.** Along
`γ := intrinsicGeodesic g hEnorm p v`, the squared `g`-speed
`g.inner (γ t) (γ'(t)) (γ'(t))` equals the launch squared speed
`g.inner p v v` for every `t`.  This is `isGeodesicOn_speedSq_const` (the
intrinsic geodesic is `IsGeodesicOn univ` and `ContMDiffOn 𝓘(ℝ,ℝ) I 1` on
`univ`) evaluated at the launch time `0`, where `intrinsicGeodesic_mfderiv_zero`
identifies the velocity with `v`. -/
theorem intrinsicGeodesic_speedSq_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    g.inner (intrinsicGeodesic (I := I) g hEnorm p v t)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
      = g.inner p v v := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hgeo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ Set.univ :=
    intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v
  have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g (t₀ := t) (t₁ := 0)
    isOpen_univ (hgeo.isGeodesicOn Set.univ) hC1 (Set.subset_univ _)
  rw [hconst]
  have h0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hvelE : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
  refine (congrArg₂ (fun (x : M) (w : E) => g.inner x w w) h0 ?_)
  exact hvelE

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Velocity enorm bound along the intrinsic geodesic.** Along
`γ := intrinsicGeodesic g hEnorm p v`, the bundle enorm of the velocity is
bounded by the launch speed `√(g_p(v, v))` at every time, by constant
squared speed (`intrinsicGeodesic_speedSq_eq`) and the enorm-from-speed
conversion (`velocity_enorm_le_of_speedSq_le`). -/
theorem intrinsicGeodesic_velocity_enorm_le
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t (1 : ℝ)‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hspeedSq : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = c ^ 2 := by
    rw [intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v t, hc_def,
      Real.sq_sqrt (gInner_self_nonneg (I := I) g p v)]
  rw [hEnorm]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  calc Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))
      = Real.sqrt (c ^ 2) := by rw [hspeedSq]
    _ = c := Real.sqrt_sq hc_nn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Length-distance bound along the intrinsic geodesic.** For `s ≤ t`,
`riemannianEDist (γ s) (γ t) ≤ √(g_p(v, v)) · (t - s)`, where
`γ := intrinsicGeodesic g hEnorm p v`.  This bounds the moving-foot geodesic's
displacement by its (constant) launch speed times the elapsed parameter.  The
proof dominates `pathELength I γ s t` by the constant speed `√(g_p(v, v))` (via
`intrinsicGeodesic_velocity_enorm_le`) and chains with
`riemannianEDist_le_pathELength`. -/
theorem intrinsicGeodesic_riemannianEDist_le
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v) * (t - s)) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s t) :=
    (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono (Set.subset_univ _)
  have h_pathLen_le : pathELength I γ s t ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc s t, (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ _ => ?_)
      simpa [hγ_def, hc_def] using
        intrinsicGeodesic_velocity_enorm_le (I := I) g hEnorm p v τ
    have h_const :
        (∫⁻ _ in Set.Icc s t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) :=
      MeasureTheory.setLIntegral_const (Set.Icc s t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc s t) = ENNReal.ofReal (t - s) :=
      Real.volume_Icc
    have h_mul :
        ENNReal.ofReal c * ENNReal.ofReal (t - s) = ENNReal.ofReal (c * (t - s)) :=
      (ENNReal.ofReal_mul hc_nn).symm
    calc
      ∫⁻ τ in Set.Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - s) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - s)) := h_mul
  have h_dist_le : riemannianEDist I (γ s) (γ t) ≤ pathELength I γ s t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := s) (b := t)
      hγ_C1 rfl rfl hst
  exact h_dist_le.trans h_pathLen_le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The intrinsic geodesic with zero launch velocity is the constant `p`.**
In particular `expMapIntrinsic g hEnorm p 0 = p` (target value at `t = 1`).
Zero launch speed makes the length-distance bound
(`intrinsicGeodesic_riemannianEDist_le`) collapse:
`riemannianEDist (γ 0) (γ 1) ≤ 0`, so `γ 1 = γ 0 = p` by point separation
(`riemannianEDist_eq_zero_imp_eq`). -/
theorem expMapIntrinsic_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    expMapIntrinsic (I := I) g hEnorm p 0 = p := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)
    with hγ_def
  have h0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p 0
  have hspeed0 : Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) = 0 := by
    rw [show g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 by simp,
      Real.sqrt_zero]
  have hbound := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p
    (0 : TangentSpace I p) (s := 0) (t := 1) (by norm_num)
  rw [hspeed0, zero_mul, ENNReal.ofReal_zero] at hbound
  have hzero : riemannianEDist I (γ 0) (γ 1) = 0 := le_antisymm hbound (by simp)
  have heq : γ 0 = γ 1 :=
    riemannianEDist_eq_zero_imp_eq (I := I) (γ 0) (γ 1) hzero
  change γ 1 = p
  rw [← heq, h0]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Side-condition-free small-vector agreement.** There is an explicit `ρ > 0`
such that `expMapIntrinsic g hEnorm p v = expMap g p v` for every `v` with
`√(g_p(v,v)) < ρ`.  The cross-chart confinement hypothesis of
`expMapIntrinsic_eq_expMap_of_small` is supplied by
`intrinsicGeodesic_foot_in_source_of_small`; `ρ` is the minimum of the two radii. -/
theorem exists_expMapIntrinsic_eq_expMap_radius
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {v : TangentSpace I p},
      Real.sqrt (g.inner p (v : E) (v : E)) < ρ →
      expMapIntrinsic (I := I) g hEnorm p v = expMap (I := I) g p v := by
  obtain ⟨ρ₁, hρ₁_pos, hbridge⟩ :=
    expMapIntrinsic_eq_expMap_of_small (I := I) g hEnorm p
  obtain ⟨ρ₂, hρ₂_pos, hfoot⟩ :=
    intrinsicGeodesic_foot_in_source_of_small (I := I) g hEnorm p
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁_pos hρ₂_pos, ?_⟩
  intro v hv
  have hv₁ : Real.sqrt (g.inner p (v : E) (v : E)) < ρ₁ :=
    lt_of_lt_of_le hv (min_le_left _ _)
  have hv₂ : Real.sqrt (g.inner p (v : E) (v : E)) < ρ₂ :=
    lt_of_lt_of_le hv (min_le_right _ _)
  exact hbridge hv₁ (hfoot hv₂)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A named positive radius on which the realized normal-coordinate
exponential and the intrinsic exponential agree.  The radius also lies below
`expRadiusGp`, so its `g_p`-ball is contained in the source of
`NormalCoordinates.expMapDiffeo`. -/
noncomputable def expDiffeoRadius
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : ℝ :=
  min
    (Classical.choose
      (exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p))
    (expRadiusGp (I := I) g p)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The named intrinsic/realized exponential agreement radius is positive. -/
theorem expDiffeoRadius_pos
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    0 < expDiffeoRadius (I := I) g hEnorm p := by
  rw [expDiffeoRadius, lt_min_iff]
  exact ⟨(Classical.choose_spec
      (exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p)).1,
    expRadiusGp_pos (I := I) g p⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A vector inside `expDiffeoRadius` belongs to the source of the realized
exponential partial diffeomorphism. -/
theorem expDiffeo_mem_of_lt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {v : TangentSpace I p}
    (hv : Real.sqrt (g.inner p (v : E) (v : E)) <
      expDiffeoRadius (I := I) g hEnorm p) :
    (v : E) ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source := by
  have hvGp : Real.sqrt (g.inner p (v : E) (v : E)) <
      expRadiusGp (I := I) g p :=
    lt_of_lt_of_le hv (min_le_right _ _)
  have hvNorm :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p hvGp
  exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p hvNorm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Inside `expDiffeoRadius`, the realized normal-coordinate exponential is
the intrinsic exponential. -/
theorem expDiffeo_eq_intr
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {v : TangentSpace I p}
    (hv : Real.sqrt (g.inner p (v : E) (v : E)) <
      expDiffeoRadius (I := I) g hEnorm p) :
    NormalCoordinates.expMapDiffeo (I := I) g p (v : E) =
      expMapIntrinsic (I := I) g hEnorm p v := by
  have hvAgree : Real.sqrt (g.inner p (v : E) (v : E)) <
      Classical.choose
        (exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p) :=
    lt_of_lt_of_le hv (min_le_left _ _)
  have hvSrc := expDiffeo_mem_of_lt (I := I) g hEnorm p hv
  rw [NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hvSrc]
  exact ((Classical.choose_spec
    (exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p)).2 hvAgree).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Radial Riemannian distance equals the radius (small radii).** For a `g`-unit
vector `u` and `0 ≤ δ` with `δ` below the agreement and Gauss radii, the Riemannian
distance from `p` to the radial point `expMapIntrinsic g hEnorm p (δ • u)` is
exactly `δ` (as an `ℝ≥0∞`, `ENNReal.ofReal δ`).  The `≤` direction is the length
bound `intrinsicGeodesic_riemannianEDist_le`; the `≥` direction is the Gauss-lemma
radial lower bound `normalBall_radial_length_le_riemannianEDist` transported across the
bridge `exists_expMapIntrinsic_eq_expMap_radius`. -/
theorem radial_riemannianEDist_eq_of_small
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {u : TangentSpace I p}, g.inner p u u = 1 →
      ∀ {δ : ℝ}, 0 ≤ δ → δ < ρ →
        riemannianEDist I p (expMapIntrinsic (I := I) g hEnorm p (δ • u))
          = ENNReal.ofReal δ := by
  obtain ⟨ρ₀, hρ₀_pos, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  set ρ : ℝ := min ρ₀ (expRadiusGp (I := I) g p) with hρ_def
  have hρ_pos : 0 < ρ := lt_min hρ₀_pos (expRadiusGp_pos (I := I) g p)
  refine ⟨ρ, hρ_pos, ?_⟩
  intro u hu δ hδ_nn hδ
  set vδ : TangentSpace I p := δ • u with hvδ_def
  have hnorm_vδ : Real.sqrt (g.inner p (vδ : E) (vδ : E)) = δ := by
    rw [hvδ_def, sqrt_gInner_smul_self (I := I) g p hδ_nn u, hu, Real.sqrt_one, mul_one]
  have hvδ_lt_ρ₀ : Real.sqrt (g.inner p (vδ : E) (vδ : E)) < ρ₀ := by
    rw [hnorm_vδ]; exact lt_of_lt_of_le hδ (min_le_left _ _)
  have hvδ_lt_gp : Real.sqrt (g.inner p (vδ : E) (vδ : E)) < expRadiusGp (I := I) g p := by
    rw [hnorm_vδ]; exact lt_of_lt_of_le hδ (min_le_right _ _)
  have hagree_vδ : expMapIntrinsic (I := I) g hEnorm p vδ = expMap (I := I) g p vδ :=
    hagree hvδ_lt_ρ₀
  set vE : E := (vδ : E) with hvE_def
  have hvE_inner : g.inner p vE vE = g.inner p (vδ : E) (vδ : E) := rfl
  have hvE_lt_gp : Real.sqrt (g.inner p vE vE) < expRadiusGp (I := I) g p := by
    rw [hvE_inner]; exact hvδ_lt_gp
  have hvδ_normE : ‖vE‖ < expMapC2Radius (I := I) g p :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p hvE_lt_gp
  have hvδ_dom : (show TangentSpace I p from vE) ∈ expDomain (I := I) g p :=
    mem_expDomain_of_norm_lt_radius (I := I) g p hvδ_normE
  have hvδ_ball : vE ∈ (NormalCoordinates.normalChartAt (I := I) g p).target :=
    ball_subset_normalChartAt_target (I := I) g p hvδ_normE
  have hlower :
      ENNReal.ofReal (Real.sqrt (g.inner p vE vE)) ≤
        riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from vE)) :=
    normalBall_radial_length_le_riemannianEDist (I := I) g p hEnorm hvδ_dom hvδ_ball hvE_lt_gp
  have hupper :
      riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm p vδ 0)
          (intrinsicGeodesic (I := I) g hEnorm p vδ 1)
        ≤ ENNReal.ofReal (Real.sqrt (g.inner p vδ vδ) * (1 - 0)) :=
    intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p vδ (by norm_num)
  rw [hnorm_vδ] at hlower
  have hg0 : intrinsicGeodesic (I := I) g hEnorm p vδ 0 = p :=
    intrinsicGeodesic_zero (I := I) g hEnorm p vδ
  have hg1 : intrinsicGeodesic (I := I) g hEnorm p vδ 1 = expMapIntrinsic (I := I) g hEnorm p vδ :=
    rfl
  rw [hg0, hg1, hnorm_vδ, sub_zero, mul_one] at hupper
  have hlower' :
      ENNReal.ofReal δ ≤ riemannianEDist I p (expMapIntrinsic (I := I) g hEnorm p vδ) := by
    rw [hagree_vδ]; exact hlower
  exact le_antisymm hupper hlower'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Arbitrary-small-vector radial Riemannian distance.** There is an explicit
`ρ > 0` such that for every `w : T_p M` with `√(g_p(w, w)) < ρ`, the Riemannian
distance from `p` to the radial point `expMapIntrinsic g hEnorm p w` equals
`ofReal (√(g_p(w, w)))`.  This generalises `radial_riemannianEDist_eq_of_small`
(which is stated for the explicit radial form `δ • u`, `u` a `g`-unit vector) to
an arbitrary small launch vector by rescaling `w = √(g_p(w, w)) • (√(g_p(w, w))⁻¹
• w)` into unit-direction form; the degenerate `√(g_p(w, w)) = 0` case is
`w = 0`, where both sides are `0` (`expMapIntrinsic_zero`, `riemannianEDist_self`). -/
theorem radial_riemannianEDist_eq_of_small'
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {w : TangentSpace I p},
      Real.sqrt (g.inner p (w : E) (w : E)) < ρ →
        riemannianEDist I p (expMapIntrinsic (I := I) g hEnorm p w)
          = ENNReal.ofReal (Real.sqrt (g.inner p (w : E) (w : E))) := by
  obtain ⟨ρ, hρ_pos, hradial⟩ := radial_riemannianEDist_eq_of_small (I := I) g hEnorm p
  refine ⟨ρ, hρ_pos, ?_⟩
  intro w hw
  set s : ℝ := Real.sqrt (g.inner p (w : E) (w : E)) with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs_nn with hs0 | hspos
  · have hs_eq : s = 0 := hs0.symm
    have hww0 : g.inner p (w : E) (w : E) = 0 := by
      have hsq : Real.sqrt (g.inner p (w : E) (w : E)) = 0 := hs_eq
      nlinarith [Real.sq_sqrt (gInner_self_nonneg (I := I) g p w), hsq,
        gInner_self_nonneg (I := I) g p w]
    have hw0 : w = 0 := by
      by_contra hne
      exact absurd hww0 (ne_of_gt (g.pos p w hne))
    rw [hw0, expMapIntrinsic_zero (I := I) g hEnorm p, riemannianEDist_self, hs_eq,
      ENNReal.ofReal_zero]
  · set u : TangentSpace I p := s⁻¹ • w with hu_def
    have hu_unit : g.inner p u u = 1 := by
      rw [hu_def, gInner_smul_self (I := I) g p s⁻¹ w]
      rw [show (s⁻¹) ^ 2 = (s ^ 2)⁻¹ by rw [inv_pow]]
      rw [show g.inner p (w : E) (w : E) = s ^ 2 from
        (Real.sq_sqrt (gInner_self_nonneg (I := I) g p w)).symm]
      exact inv_mul_cancel₀ (by positivity)
    have hw_eq : w = s • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hspos), one_smul]
    rw [hw_eq, hradial hu_unit hs_nn hw]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Local radial surjectivity of `expMapIntrinsic` (within the injectivity
radius).** There is an explicit `ρ > 0` such that every point `q` in the normal
chart's source at `p` whose chart coordinate `ψ q := normalChartAt g p q` has
`g`-norm `√(g_p(ψ q, ψ q)) < ρ` is reached by a radial geodesic: there is a
launch vector `w` (namely the chart coordinate `ψ q`) with
`expMapIntrinsic g hEnorm p w = q` and `g`-speed `√(g_p(w, w))` equal to the
Riemannian distance `(riemannianEDist I p q).toReal`.

The witness is the normal-chart coordinate `w := ψ q`.  Then `expMap g p w =
ψ.symm (ψ q) = q` (normal-chart round-trip `normalChartAt_left_inv` together with
`normalChartAt_symm_apply`), so `expMapIntrinsic g hEnorm p w = q` by the
side-condition-free agreement bridge `exists_expMapIntrinsic_eq_expMap_radius`;
the `g`-speed identity is `radial_riemannianEDist_eq_of_small'` followed by
`ENNReal.toReal_ofReal`.  This is the easy local case of Hopf–Rinow surjectivity
(`normal ball = metric ball`), distinct from the global closed-ball route. -/
theorem expMapIntrinsic_local_surjective
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {q : M},
      q ∈ (NormalCoordinates.normalChartAt (I := I) g p).source →
      Real.sqrt (g.inner p
        ((NormalCoordinates.normalChartAt (I := I) g p q : E))
        ((NormalCoordinates.normalChartAt (I := I) g p q : E))) < ρ →
      ∃ w : TangentSpace I p, expMapIntrinsic (I := I) g hEnorm p w = q ∧
        Real.sqrt (g.inner p (w : E) (w : E)) = (riemannianEDist I p q).toReal := by
  obtain ⟨ρ₁, hρ₁_pos, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  obtain ⟨ρ₂, hρ₂_pos, hdist⟩ :=
    radial_riemannianEDist_eq_of_small' (I := I) g hEnorm p
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁_pos hρ₂_pos, ?_⟩
  intro q hq_src hsmall
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set w : E := ψ q with hw_def
  have hw_lt1 : Real.sqrt (g.inner p (w : E) (w : E)) < ρ₁ :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have hw_lt2 : Real.sqrt (g.inner p (w : E) (w : E)) < ρ₂ :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hw_target : w ∈ ψ.target := by
    rw [hw_def]; exact ψ.map_source hq_src
  have hexp_eq_q : expMap (I := I) g p (show TangentSpace I p from w) = q := by
    have hround : ψ.symm (ψ q) = q :=
      NormalCoordinates.normalChartAt_left_inv (I := I) g p hq_src
    have hsymm : ψ.symm w = expMap (I := I) g p (show TangentSpace I p from w) :=
      NormalCoordinates.normalChartAt_symm_apply (I := I) g p
        (show w ∈ ψ.symm.source from hw_target)
    rw [← hsymm, hw_def, hround]
  have hintr_eq_q :
      expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w) = q := by
    rw [hagree hw_lt1, hexp_eq_q]
  refine ⟨(show TangentSpace I p from w), hintr_eq_q, ?_⟩
  have hd : riemannianEDist I p
      (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from w))
      = ENNReal.ofReal (Real.sqrt (g.inner p (w : E) (w : E))) := hdist hw_lt2
  rw [hintr_eq_q] at hd
  rw [hd, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C^∞`-in-time regularity of the chart curve of a moving-foot geodesic.**
The chart-coordinate curve `u = φ_{γ t} ∘ γ` of a moving-foot geodesic `γ`,
geodesic on an open set `s ∋ t` and continuous on `s`, is `ContDiffAt ℝ ∞` at
`t`.  The chart pair `(u, u')` solves the `C^∞` first-order phase-space geodesic
ODE `(u, u')' = chartPhaseVF g (γ t) (u, u')` (the velocity clause
`hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt` and the acceleration
clause `hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity`), so the
ODE-smoothness bootstrap `ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt` (with the
`C^∞` field `chartPhaseVF_contDiffOn`) upgrades the `C¹` solution
(`chartCurve_contDiffAt_one_of_isGeodesicOn`) to `C^∞`. -/
theorem chartCurve_contDiffAt_top_of_isGeodesicOn
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn
      (I := I) g γ s)
    (hcont : ContinuousOn γ s) :
    ContDiffAt ℝ ∞
      (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
        (I := I) (γ t) γ) t := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set α : M := γ t with hα_def
  set u : ℝ → E := DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
    (I := I) α γ with hu_def
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hcontAt_t : ContinuousAt γ t := hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
    hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα_src)
  have hW_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∩ s ∈ 𝓝 t :=
    Filter.inter_mem hsrc_nhds (hs.mem_nhds ht)
  obtain ⟨W', hW'_sub, hW'_open, htW'⟩ := mem_nhds_iff.mp hW_nhds
  have hW'_src : ∀ r ∈ W', γ r ∈ (chartAt H α).source := fun r hr => (hW'_sub hr).1
  have hW'_geo : ∀ r ∈ W',
      DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicEquationAt
        (I := I) g γ r := fun r hr => hγ r (hW'_sub hr).2
  have hW'_contAt : ∀ r ∈ W', ContinuousAt γ r :=
    fun r hr => hcont.continuousAt (hs.mem_nhds (hW'_sub hr).2)
  set Z : ℝ → E × E := fun r => (u r, deriv u r) with hZ_def
  have hZ_ode : ∀ r ∈ W',
      HasDerivAt Z
        (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF
          (I := I) g α (Z r)) r := by
    intro r hr
    have hu_d : HasDerivAt u (deriv u r) r := by
      have hev :=
        DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt
          (I := I) g α (γ := γ) (t := r) (hW'_contAt r hr) (hW'_src r hr)
          (hW'_geo r hr)
      simpa [hu_def] using hev.self_of_nhds
    have hdu_d : HasDerivAt (deriv u)
        (- DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction
            (I := I) g α (deriv u r) (deriv u r) (u r)) r := by
      simpa [hu_def] using
        DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity
          (I := I) g α (γ := γ) (t := r) (hW'_contAt r hr) (hW'_src r hr)
          (hW'_geo r hr)
    have hprod : HasDerivAt Z
        (deriv u r,
          - DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction
              (I := I) g α (deriv u r) (deriv u r) (u r)) r :=
      hu_d.prodMk hdu_d
    simpa only [hZ_def,
      DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF_mk] using hprod
  have hu_int : ∀ r ∈ W', u r ∈ interior (extChartAt I α).target := by
    intro r hr
    have hur : u r = extChartAt I α (γ r) := by
      rw [hu_def,
        DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
    rw [hur]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α
      ((extChartAt I α).map_source (by rw [extChartAt_source]; exact hW'_src r hr))
  obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hW'_open t htW'
  set a : ℝ := t - ε / 2 with ha_def
  set b : ℝ := t + ε / 2 with hb_def
  have hIcc_sub : Set.Icc a b ⊆ W' := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    rcases hr with ⟨hr1, hr2⟩
    rw [abs_lt]
    refine ⟨by simp only [ha_def] at hr1; linarith, by simp only [hb_def] at hr2; linarith⟩
  have ht_mem_lo : a < t := by simp only [ha_def]; linarith
  have ht_mem_hi : t < b := by simp only [hb_def]; linarith
  have hZ_smooth : ContDiffOn ℝ ∞ Z (Set.Icc a b) := by
    refine ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun _ : ℝ =>
        DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF (I := I) g α)
      (u := interior (extChartAt I α).target ×ˢ (Set.univ : Set E))
      (n := (⊤ : ℕ∞)) ?_ ?_ ?_
    · have huncurry :
          Function.uncurry
            (fun _ : ℝ =>
              DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF (I := I) g α)
            = fun p : ℝ × (E × E) =>
                DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF
                  (I := I) g α p.2 := by
        funext p; rfl
      rw [huncurry]
      exact (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartPhaseVF_contDiffOn
        (I := I) g α).comp contDiffOn_snd (fun p hp => hp.2)
    · intro r hr
      exact (hZ_ode r (hIcc_sub hr)).hasDerivWithinAt
    · intro r hr
      exact ⟨hu_int r (hIcc_sub hr), Set.mem_univ _⟩
  have hZ_at : ContDiffAt ℝ ∞ Z t :=
    (hZ_smooth.contDiffWithinAt ⟨ht_mem_lo.le, ht_mem_hi.le⟩).contDiffAt
      (Icc_mem_nhds ht_mem_lo ht_mem_hi)
  have hu_at : ContDiffAt ℝ ∞ u t := by
    have hfst := hZ_at.fst
    simpa [hZ_def] using hfst
  rw [hu_def] at hu_at
  exact hu_at

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C^∞`-in-time regularity of a moving-foot geodesic (pointwise).**  An
intrinsic moving-foot geodesic `γ` on an open set `s`, continuous on `s`, is
`ContMDiffAt 𝓘(ℝ, ℝ) I ∞` at every `t ∈ s`.  Bootstraps the chart-curve `C^∞`
regularity `chartCurve_contDiffAt_top_of_isGeodesicOn` through the smooth chart
round-trip `(extChartAt I (γ t)).symm ∘ u = γ`. -/
theorem isGeodesicOn_contMDiffAt_top
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn
      (I := I) g γ s)
    (hcont : ContinuousOn γ s) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
    (I := I) α γ with hu_def
  have hu_cd : ContDiffAt ℝ ∞ u t :=
    chartCurve_contDiffAt_top_of_isGeodesicOn (I := I) g hs ht hγ hcont
  have hu_cmd : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ u t := hu_cd.contMDiffAt
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hα_ext_src : α ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα_src
  have hut_eq : u t = extChartAt I α α := by
    rw [hu_def,
      DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def, hα_def]
  have hut_target : u t ∈ (extChartAt I α).target := by
    rw [hut_eq]; exact (extChartAt I α).map_source hα_ext_src
  have htarget_nhds : (extChartAt I α).target ∈ 𝓝 (u t) := by
    have hut_int : u t ∈ interior (extChartAt I α).target := by
      rw [hut_eq]
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) α ((extChartAt I α).map_source hα_ext_src)
    exact mem_nhds_iff.mpr ⟨interior (extChartAt I α).target, interior_subset,
      isOpen_interior, hut_int⟩
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ∞
      (extChartAt I α).symm (extChartAt I α).target (u t) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) α hut_target
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (u t) :=
    hsymm_within.contMDiffAt htarget_nhds
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ ((extChartAt I α).symm ∘ u) t :=
    hsymm_at.comp t hu_cmd
  have hcontAt_t : ContinuousAt γ t := hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
    hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα_src)
  have heq : ((extChartAt I α).symm ∘ u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hsrc_nhds] with s' hs'
    have hs'_ext : γ s' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hs'
    change (extChartAt I α).symm (u s') = γ s'
    rw [hu_def,
      DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
    exact (extChartAt I α).left_inv hs'_ext
  exact hcomp.congr_of_eventuallyEq heq.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C^∞`-in-time regularity of a moving-foot geodesic (on an open set).** -/
theorem isGeodesicOn_contMDiffOn_top
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s)
    (hγ : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn
      (I := I) g γ s)
    (hcont : ContinuousOn γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ s := fun _t ht =>
  (isGeodesicOn_contMDiffAt_top (I := I) g hs ht hγ hcont).contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C^∞`-in-time regularity of a complete moving-foot geodesic.**  A complete
moving-foot geodesic `γ` (geodesic on all of `ℝ`), continuous everywhere, is
`ContMDiff 𝓘(ℝ, ℝ) I ∞`. -/
theorem isGeodesic_contMDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (hγ : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
  rw [← contMDiffOn_univ]
  exact isGeodesicOn_contMDiffOn_top (I := I) g isOpen_univ
    (hγ.isGeodesicOn Set.univ) hcont.continuousOn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The metric-sphere distance drop.**  See the section docstring.  The radial
step `δ` is required below an explicit positive `x`-dependent threshold `R`
(the minimum of the small-vector agreement radius, the unit-direction radial
radius, and the Gauss radius `expRadiusGp g x`) and below the distance `ρ`. -/
theorem sphere_jump
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x q : M) {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hxq : riemannianEDist I x q = ENNReal.ofReal ρ) :
    ∃ R : ℝ, 0 < R ∧ ∀ {δ : ℝ}, 0 < δ → δ < R → δ < ρ →
      ∃ (y : M) (w : TangentSpace I x), g.inner x w w = 1 ∧
        y = expMapIntrinsic (I := I) g hEnorm x (δ • w) ∧
        riemannianEDist I x y = ENNReal.ofReal δ ∧
        riemannianEDist I y q = ENNReal.ofReal (ρ - δ) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨ρ₀, hρ₀_pos, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm x
  obtain ⟨ρ₂, hρ₂_pos, hradial⟩ :=
    radial_riemannianEDist_eq_of_small (I := I) g hEnorm x
  refine ⟨min ρ₀ (min ρ₂ (expRadiusGp (I := I) g x)),
    lt_min hρ₀_pos (lt_min hρ₂_pos (expRadiusGp_pos (I := I) g x)), ?_⟩
  intro δ hδ_pos hδ_R hδ_lt_ρ
  have hδ_lt_ρ₀ : δ < ρ₀ := lt_of_lt_of_le hδ_R (min_le_left _ _)
  have hδ_lt_ρ₂ : δ < ρ₂ := lt_of_lt_of_le hδ_R (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_lt_R : δ < expRadiusGp (I := I) g x :=
    lt_of_lt_of_le hδ_R (le_trans (min_le_right _ _) (min_le_right _ _))
  set f : TangentSpace I x → M :=
    fun w => expMapIntrinsic (I := I) g hEnorm x (δ • w) with hf_def
  set sph : Set (TangentSpace I x) := {w : TangentSpace I x | g.inner x w w = 1}
    with hsph_def
  have hsph_ne : sph.Nonempty := by
    have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
    obtain ⟨a, ha_ne⟩ : ∃ a : TangentSpace I x, a ≠ 0 :=
      ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
    have hc_pos : 0 < g.inner x a a := g.pos x a ha_ne
    set s : ℝ := Real.sqrt (g.inner x a a)⁻¹ with hs_def
    have hs_sq : s * s = (g.inner x a a)⁻¹ :=
      Real.mul_self_sqrt (inv_nonneg.mpr hc_pos.le)
    refine ⟨s • a, ?_⟩
    change g.inner x (s • a) (s • a) = 1
    rw [gInner_smul_self (I := I) g x s a, show s ^ 2 = s * s by ring, hs_sq,
      inv_mul_cancel₀ (ne_of_gt hc_pos)]
  have hsph_compact : IsCompact sph := gUnitSphere_isCompact (I := I) g x
  set F : E → M := fun u : E => (expMap (I := I) g x (show TangentSpace I x from u) : M) with hF_def
  have hsphnorm : ∀ w ∈ sph,
      Real.sqrt (g.inner x ((δ • w : TangentSpace I x) : E)
        ((δ • w : TangentSpace I x) : E)) = δ := by
    intro w hw
    have hwu : g.inner x w w = 1 := hw
    rw [sqrt_gInner_smul_self (I := I) g x hδ_pos.le w, hwu, Real.sqrt_one, mul_one]
  have hf_agree : ∀ w ∈ sph, f w = F (δ • (w : E)) := by
    intro w hw
    have hlt : Real.sqrt (g.inner x ((δ • w : TangentSpace I x) : E)
        ((δ • w : TangentSpace I x) : E)) < ρ₀ := by rw [hsphnorm w hw]; exact hδ_lt_ρ₀
    rw [hf_def, hF_def]
    exact hagree hlt
  have hexp_contOn : ContinuousOn (fun w : TangentSpace I x => F (δ • (w : E))) sph := by
    intro w₀ hw₀
    have hball : Real.sqrt (g.inner x ((δ • w₀ : TangentSpace I x) : E)
        ((δ • w₀ : TangentSpace I x) : E)) < expRadiusGp (I := I) g x := by
      rw [hsphnorm w₀ hw₀]; exact hδ_lt_R
    have hEucl := norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g x hball
    have hcd : ContMDiffAt 𝓘(ℝ, E) I 2 F ((δ • (w₀ : E)) : E) :=
      expMap_contMDiffAt2_of_norm_lt_radius (I := I) g x hEucl
    have hcontAt_u : ContinuousAt F ((δ • (w₀ : E)) : E) := hcd.continuousAt
    have hscale : ContinuousAt (fun w : TangentSpace I x => ((δ • (w : E)) : E)) w₀ :=
      (continuous_const_smul δ).continuousAt
    exact (hcontAt_u.comp hscale).continuousWithinAt
  have hf_contOn : ContinuousOn f sph := hexp_contOn.congr hf_agree
  have hS_compact : IsCompact (f '' sph) := hsph_compact.image_of_continuousOn hf_contOn
  have hS_ne : (f '' sph).Nonempty := hsph_ne.image f
  have hcont : Continuous (fun z : M => riemannianEDist I z q) :=
    continuous_riemannianEDist_to (I := I) q
  obtain ⟨y₀, hy₀_mem, hy₀_min⟩ :=
    hS_compact.exists_isMinOn hS_ne hcont.continuousOn
  obtain ⟨w, hw_unit, hw_eq⟩ := hy₀_mem
  simp only [hf_def] at hw_eq
  have hdxy : riemannianEDist I x y₀ = ENNReal.ofReal δ := by
    have := hradial hw_unit hδ_pos.le hδ_lt_ρ₂
    rwa [hw_eq] at this
  refine ⟨y₀, w, hw_unit, hw_eq.symm, hdxy, ?_⟩
  have hρδ_nn : 0 ≤ ρ - δ := (sub_nonneg.mpr hδ_lt_ρ.le)
  have hδ_nn : 0 ≤ δ := hδ_pos.le
  have hge : ENNReal.ofReal (ρ - δ) ≤ riemannianEDist I y₀ q := by
    have htri : riemannianEDist I x q ≤ riemannianEDist I x y₀ + riemannianEDist I y₀ q :=
      riemannianEDist_triangle
    rw [hxq, hdxy] at htri
    have hsplit : ENNReal.ofReal ρ = ENNReal.ofReal δ + ENNReal.ofReal (ρ - δ) := by
      rw [← ENNReal.ofReal_add hδ_nn hρδ_nn]; congr 1; ring
    rw [hsplit] at htri
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp htri
  have hcont_from_x : Continuous (fun z : M => riemannianEDist I x z) := by
    have hc := continuous_riemannianEDist_to (I := I) (M := M) x
    have heq : (fun z : M => riemannianEDist I x z) = (fun z : M => riemannianEDist I z x) := by
      funext z; exact riemannianEDist_comm
    rw [heq]; exact hc
  have hcore : ∀ ε : ℝ, 0 < ε → riemannianEDist I y₀ q ≤ ENNReal.ofReal (ρ - δ + ε) := by
    intro ε hε
    have hlt : riemannianEDist I x q < ENNReal.ofReal (ρ + ε) := by
      rw [hxq]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρ_pos.le).mpr (by linarith)
    obtain ⟨P, hP0, hP1, hP_C1, hP_len⟩ := exists_lt_of_riemannianEDist_lt hlt
    set h : ℝ → ℝ := fun t => (riemannianEDist I x (P t)).toReal with hh_def
    have hP_contOn : ContinuousOn P (Set.Icc (0 : ℝ) 1) := hP_C1.continuousOn
    have hh_contOn : ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
      have hdistP : ContinuousOn (fun t : ℝ => riemannianEDist I x (P t)) (Set.Icc 0 1) :=
        hcont_from_x.comp_continuousOn hP_contOn
      refine ENNReal.continuousOn_toReal.comp' hdistP ?_
      intro t _
      exact riemannianEDist_ne_top (I := I) x (P t)
    have hh0 : h 0 = 0 := by
      simp only [hh_def, hP0, riemannianEDist_self, ENNReal.toReal_zero]
    have hh1 : h 1 = ρ := by
      simp only [hh_def, hP1, hxq, ENNReal.toReal_ofReal hρ_pos.le]
    have hδ_mem : δ ∈ Set.Icc (h 0) (h 1) := by
      rw [hh0, hh1]; exact ⟨hδ_nn, hδ_lt_ρ.le⟩
    obtain ⟨ts, hts_mem, hts_eq⟩ :=
      intermediate_value_Icc (zero_le_one) hh_contOn hδ_mem
    set z : M := P ts with hz_def
    have hz_fin : riemannianEDist I x z ≠ ⊤ := riemannianEDist_ne_top (I := I) x z
    have hdxz : riemannianEDist I x z = ENNReal.ofReal δ := by
      have : (riemannianEDist I x z).toReal = δ := hts_eq
      rw [← this, ENNReal.ofReal_toReal hz_fin]
    have hdxz_real : (riemannianEDist I x z).toReal = δ := hts_eq
    have hz_lt_R : (riemannianEDist I x z).toReal < expRadiusGp (I := I) g x := by
      rw [hdxz_real]; exact hδ_lt_R
    obtain ⟨vz, hvz_target, hvz_dom, hvz_norm, hz_eq⟩ :=
      metricBall_subset_normalBall (I := I) g x hEnorm hz_fin hz_lt_R
    rw [hdxz_real] at hvz_norm
    set wz : TangentSpace I x := (δ⁻¹ : ℝ) • (show TangentSpace I x from vz) with hwz_def
    have hgvz : g.inner x (show TangentSpace I x from vz) (show TangentSpace I x from vz) = δ ^ 2 := by
      have := Real.sq_sqrt (gInner_self_nonneg (I := I) g x (show TangentSpace I x from vz))
      rw [hvz_norm] at this; linarith [this]
    have hwz_unit : g.inner x wz wz = 1 := by
      rw [hwz_def, gInner_smul_self (I := I) g x δ⁻¹ (show TangentSpace I x from vz), hgvz,
        show (δ⁻¹) ^ 2 = (δ ^ 2)⁻¹ by rw [inv_pow]]
      exact inv_mul_cancel₀ (by positivity)
    have hδwz : (δ : ℝ) • wz = (show TangentSpace I x from vz) := by
      rw [hwz_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hδ_pos), one_smul]
    have hz_in_S : z ∈ f '' sph := by
      refine ⟨wz, hwz_unit, ?_⟩
      change expMapIntrinsic (I := I) g hEnorm x (δ • wz) = z
      have hgwz : Real.sqrt (g.inner x ((δ • wz : TangentSpace I x) : E)
          ((δ • wz : TangentSpace I x) : E)) < ρ₀ := by
        rw [show ((δ • wz : TangentSpace I x) : E) = (show TangentSpace I x from vz) from hδwz]
        rw [hvz_norm]; exact hδ_lt_ρ₀
      rw [hagree hgwz, hδwz, ← hz_eq]
    have hmin_z : riemannianEDist I y₀ q ≤ riemannianEDist I z q := hy₀_min hz_in_S
    have hts_le_one : ts ≤ 1 := hts_mem.2
    have hts_nn : 0 ≤ ts := hts_mem.1
    have hC1_left : ContMDiffOn 𝓘(ℝ, ℝ) I 1 P (Set.Icc 0 ts) :=
      hP_C1.mono (Set.Icc_subset_Icc le_rfl hts_le_one)
    have hC1_right : ContMDiffOn 𝓘(ℝ, ℝ) I 1 P (Set.Icc ts 1) :=
      hP_C1.mono (Set.Icc_subset_Icc hts_nn le_rfl)
    have hdxz_path : riemannianEDist I x z ≤ pathELength I P 0 ts :=
      riemannianEDist_le_pathELength (I := I) (γ := P) (a := 0) (b := ts) hC1_left hP0 rfl hts_nn
    have hdzq_path : riemannianEDist I z q ≤ pathELength I P ts 1 :=
      riemannianEDist_le_pathELength (I := I) (γ := P) (a := ts) (b := 1) hC1_right rfl hP1
        hts_le_one
    have hadd : pathELength I P 0 ts + pathELength I P ts 1 = pathELength I P 0 1 :=
      Manifold.pathELength_add hts_nn hts_le_one
    have hsum_lt : ENNReal.ofReal δ + riemannianEDist I z q < ENNReal.ofReal (ρ + ε) := by
      calc ENNReal.ofReal δ + riemannianEDist I z q
          = riemannianEDist I x z + riemannianEDist I z q := by rw [hdxz]
        _ ≤ pathELength I P 0 ts + pathELength I P ts 1 := add_le_add hdxz_path hdzq_path
        _ = pathELength I P 0 1 := hadd
        _ < ENNReal.ofReal (ρ + ε) := hP_len
    have hsplit2 : ENNReal.ofReal (ρ + ε) = ENNReal.ofReal δ + ENNReal.ofReal (ρ - δ + ε) := by
      rw [← ENNReal.ofReal_add hδ_nn (by linarith)]; congr 1; ring
    rw [hsplit2] at hsum_lt
    have hzq_lt : riemannianEDist I z q < ENNReal.ofReal (ρ - δ + ε) :=
      (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mp hsum_lt
    exact hmin_z.trans hzq_lt.le
  have hle : riemannianEDist I y₀ q ≤ ENNReal.ofReal (ρ - δ) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    have h1 : riemannianEDist I y₀ q ≤ ENNReal.ofReal (ρ - δ + (ε : ℝ)) :=
      hcore ε (by exact_mod_cast hε)
    refine h1.trans ?_
    rw [ENNReal.ofReal_add hρδ_nn (le_of_lt (by exact_mod_cast hε))]
    gcongr
    rw [ENNReal.ofReal_coe_nnreal]
  exact le_antisymm hle hge

open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

/-- **Smooth chart-localised variation field value.** For the smooth slice
`u ↦ φ.symm (y₀ + η u • c₀)` (with `φ := extChartAt I c`), built from a `C^∞`
cutoff `η` with `η 0 = 0`, `η'(0) = 1`, whose perturbed argument stays in the
chart target, the manifold velocity at `u = 0` is the inverse trivialisation of
`c₀` at the foot `φ.symm y₀`. The chart round-trip collapses `φ ∘ slice` to the
affine `u ↦ y₀ + η u • c₀`, whose Fréchet derivative is `c₀`; the bridge
`raw_mfderiv_eq_symmL_apply_fderiv` then identifies the manifold velocity. -/
private lemma chartSlice_mfderiv_value
    (c : M) (y₀ c₀ : E) (ηf : ℝ → ℝ)
    (hη_smooth : ContDiff ℝ ∞ ηf) (hη0 : ηf 0 = 0) (hη'0 : HasDerivAt ηf 1 0)
    (hmem : ∀ u : ℝ, y₀ + ηf u • c₀ ∈ (extChartAt I c).target)
    (hbase : (extChartAt I c).symm y₀ ∈ (chartAt H c).source) :
    ((mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => (extChartAt I c).symm (y₀ + ηf u • c₀)) 0 (1 : ℝ)) : E)
      = (trivializationAt E (TangentSpace I) c).symmL ℝ ((extChartAt I c).symm y₀) c₀ := by
  set ζ : ℝ → M := fun u : ℝ => (extChartAt I c).symm (y₀ + ηf u • c₀) with hζ
  have hsmooth_symm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I c).symm (extChartAt I c).target :=
    contMDiffOn_extChartAt_symm c
  have hηM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ηf := by
    rw [contMDiff_iff_contDiff]; exact hη_smooth
  have hcurveE : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun u : ℝ => y₀ + ηf u • c₀) :=
    contMDiff_const.add (hηM.smul contMDiff_const)
  have hζsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ ζ :=
    hsmooth_symm.comp_contMDiff hcurveE (fun u => hmem u)
  have hζ0 : ζ 0 ∈ (chartAt H c).source := by
    simp only [hζ, hη0, zero_smul, add_zero]; exact hbase
  have hbridge := MFDerivAlongCurve.raw_mfderiv_eq_symmL_apply_fderiv (I := I) (M := M)
    (γ := ζ) hζsmooth c hζ0
  rw [hbridge]
  have hζ0eq : ζ 0 = (extChartAt I c).symm y₀ := by simp only [hζ, hη0, zero_smul, add_zero]
  rw [hζ0eq]
  congr 1
  have hcomp_eq : (fun u : ℝ => extChartAt I c (ζ u)) =ᶠ[nhds 0] (fun u : ℝ => y₀ + ηf u • c₀) := by
    filter_upwards with u
    simp only [hζ]
    rw [PartialEquiv.right_inv _ (hmem u)]
  have hfd : fderiv ℝ ((extChartAt I c) ∘ ζ) 0 (1 : ℝ)
      = fderiv ℝ (fun u : ℝ => y₀ + ηf u • c₀) 0 (1 : ℝ) := by
    apply Filter.EventuallyEq.fderiv_eq at hcomp_eq
    rw [show ((extChartAt I c) ∘ ζ) = (fun u : ℝ => extChartAt I c (ζ u)) from rfl, hcomp_eq]
  rw [hfd]
  have h : HasDerivAt (fun u : ℝ => ηf u • c₀) c₀ 0 := by
    have := hη'0.smul_const c₀; simpa using this
  have hderiv : HasDerivAt (fun u : ℝ => y₀ + ηf u • c₀) c₀ 0 := by
    have hsum := (hasDerivAt_const (0 : ℝ) y₀).add h
    rw [zero_add] at hsum; exact hsum
  rw [fderiv_apply_one_eq_deriv]
  exact hderiv.deriv

/-- **Joint smoothness of the chart-localised variation.** A two-parameter map
`Hfun : ℝ → ℝ → M` that agrees with the chart formula
`φ.symm (φ (ξ t) + η s • (β t • w))` on an open `t`-set `W` (where `ξ t` is in the
chart source and the perturbed argument is in the chart target), and agrees with
the unperturbed `ξ t` off the bump's support (`tsupport β ⊆ W`), is jointly `C^∞`
on `ℝ × ℝ` (i.e. `IsSmoothVariation`). Proved by the open-cover smoothness
criterion: `W × ℝ` carries the chart formula, `(tsupport β)ᶜ × ℝ` carries `ξ`. -/
private lemma isSmoothVariation_of_chartGlue
    (c : M) (ξ : ℝ → M) (βf ηf : ℝ → ℝ) (w : E)
    (hξ : ContMDiff 𝓘(ℝ, ℝ) I ∞ ξ)
    (hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ βf) (hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ηf)
    (W : Set ℝ) (hWopen : IsOpen W) (hWsub : ∀ t ∈ W, ξ t ∈ (chartAt H c).source)
    (hsupp : tsupport βf ⊆ W)
    (hmem : ∀ p : ℝ × ℝ, p.2 ∈ W →
        extChartAt I c (ξ p.2) + ηf p.1 • (βf p.2 • w) ∈ (extChartAt I c).target)
    (Hfun : ℝ → ℝ → M)
    (hH_in : ∀ s t, t ∈ W → Hfun s t = (extChartAt I c).symm
        (extChartAt I c (ξ t) + ηf s • (βf t • w)))
    (hH_out : ∀ s t, t ∉ tsupport βf → Hfun s t = ξ t) :
    IsSmoothVariation (I := I) (fun s t => Hfun s t) := by
  suffices hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => Hfun p.1 p.2) by
    exact hsmooth.of_le (ENat.LEInfty.out (m := ((8 : ℕ) : WithTop ℕ∞)))
  apply contMDiff_of_locally_contMDiffOn
  intro p
  by_cases hp : p.2 ∈ W
  · refine ⟨{q : ℝ × ℝ | q.2 ∈ W}, hWopen.preimage continuous_snd, hp, ?_⟩
    have hsmooth_symm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I c).symm (extChartAt I c).target :=
      contMDiffOn_extChartAt_symm c
    have hcurve : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => extChartAt I c (ξ q.2) + ηf q.1 • (βf q.2 • w))
        {q : ℝ × ℝ | q.2 ∈ W} := by
      have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I c) (chartAt H c).source :=
        contMDiffOn_extChartAt
      have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
          (fun q : ℝ × ℝ => extChartAt I c (ξ q.2)) {q : ℝ × ℝ | q.2 ∈ W} := by
        apply hext.comp (hξ.comp contMDiff_snd).contMDiffOn
        intro q hq; exact hWsub q.2 hq
      apply hcomp.add
      apply ContMDiffOn.smul
      · exact (hη.comp contMDiff_fst).contMDiffOn
      · exact ((hβ.comp contMDiff_snd).contMDiffOn).smul contMDiffOn_const
    have hcompose : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        ((extChartAt I c).symm ∘
          (fun q : ℝ × ℝ => extChartAt I c (ξ q.2) + ηf q.1 • (βf q.2 • w)))
        {q : ℝ × ℝ | q.2 ∈ W} :=
      hsmooth_symm.comp hcurve (fun q hq => hmem q hq)
    apply hcompose.congr
    intro q hq; exact hH_in q.1 q.2 hq
  · refine ⟨{q : ℝ × ℝ | q.2 ∉ tsupport βf},
      (isClosed_tsupport βf).isOpen_compl.preimage continuous_snd,
      (fun hcontra => hp (hsupp hcontra)), ?_⟩
    have : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ (fun q : ℝ × ℝ => ξ q.2)
        {q : ℝ × ℝ | q.2 ∉ tsupport βf} := (hξ.comp contMDiff_snd).contMDiffOn
    apply this.congr
    intro q hq; exact hH_out q.1 q.2 hq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **First-variation data for one geodesic half.** For a `C^∞` unit-speed
geodesic `ξ` on `[0, len]` (`len > 0`), perturbed in a smooth chart at a fixed
point `c` along a model vector `w` with cutoff `ηf` (`ηf 0 = 0`, `ηf'(0) = 1`)
and bump `βf` supported inside the open set where `ξ` enters the chart source,
the chart-localised variation `Fξ s t := φ.symm (φ (ξ t) + ηf s • (βf t • w))`
(equal to `ξ t` off `tsupport βf`) is a smooth unit-speed variation of `ξ` whose
arc length on `[0, len]` has, at `s = 0`, derivative equal to the free-endpoint
boundary term
`⟨V len, ξ'(len)⟩ - ⟨V 0, ξ'(0)⟩` with `V t = symmL_{ξ t} (βf t • w)`
(the interior `∇_t ξ'` integral vanishes because `ξ` is a geodesic). It also
satisfies `Fξ 0 = ξ`, the arc length at `s = 0` is `len`, and the path length of
each slice dominates the Riemannian edistance between its endpoints. -/
private lemma broken_piece_firstVariation
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (c : M) (w : E) {ξ : ℝ → M} {len : ℝ} (hlen : 0 < len)
    (hξsmooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ ξ)
    (hξgeo : IsGeodesicOn (I := I) g ξ (Set.Icc 0 len))
    (hξunit : ∀ t ∈ Set.Icc (0 : ℝ) len,
      g.inner (ξ t) (mfderiv (𝓘(ℝ, ℝ)) I ξ t (1 : ℝ)) (mfderiv (𝓘(ℝ, ℝ)) I ξ t (1 : ℝ)) = 1)
    (ηf βf : ℝ → ℝ)
    (hη_smooth : ContDiff ℝ ∞ ηf) (hη0 : ηf 0 = 0) (hη'0 : HasDerivAt ηf 1 0)
    (hβ_smooth : ContDiff ℝ ∞ βf)
    (W : Set ℝ) (hWopen : IsOpen W) (hWsub : ∀ t ∈ W, ξ t ∈ (chartAt H c).source)
    (hsupp : tsupport βf ⊆ W)
    (hmem : ∀ s t, ξ t ∈ (chartAt H c).source →
        extChartAt I c (ξ t) + ηf s • (βf t • w) ∈ (extChartAt I c).target)
    (Fξ : ℝ → ℝ → M)
    (hF_def : ∀ s t, t ∈ W → Fξ s t = (extChartAt I c).symm
        (extChartAt I c (ξ t) + ηf s • (βf t • w)))
    (hF_out : ∀ s t, t ∉ tsupport βf → Fξ s t = ξ t) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => Fξ s t) 0 len)
        (g.inner (ξ len)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (ξ len) (βf len • w))
            (mfderiv (𝓘(ℝ, ℝ)) I ξ len (1 : ℝ))
          - g.inner (ξ 0)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (ξ 0) (βf 0 • w))
            (mfderiv (𝓘(ℝ, ℝ)) I ξ 0 (1 : ℝ))) 0
      ∧ arcLength (I := I) g (fun t : ℝ => ξ t) 0 len = len
      ∧ (∀ s : ℝ, riemannianEDist I (Fξ s 0) (Fξ s len)
          ≤ ENNReal.ofReal (arcLength (I := I) g (fun t : ℝ => Fξ s t) 0 len)) := by
  classical
  have hηM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ηf := by rw [contMDiff_iff_contDiff]; exact hη_smooth
  have hβM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ βf := by rw [contMDiff_iff_contDiff]; exact hβ_smooth
  have hsmooth : IsSmoothVariation (I := I) Fξ :=
    isSmoothVariation_of_chartGlue (I := I) c ξ βf ηf w hξsmooth hβM hηM W hWopen hWsub hsupp
      (fun p hp => hmem p.1 p.2 (hWsub p.2 hp)) Fξ hF_def hF_out
  have hF0 : ∀ t, Fξ 0 t = ξ t := by
    intro t
    by_cases ht : t ∈ tsupport βf
    · have hsrc : ξ t ∈ (extChartAt I c).source := by
        rw [extChartAt_source]; exact hWsub t (hsupp ht)
      rw [hF_def 0 t (hsupp ht), hη0, zero_smul, add_zero,
        PartialEquiv.left_inv _ hsrc]
    · exact hF_out 0 t ht
  have hV : ∀ t, ((mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => Fξ u t) 0 (1 : ℝ)) : E)
      = (trivializationAt E (TangentSpace I) c).symmL ℝ (ξ t) (βf t • w) := by
    intro t
    by_cases ht : t ∈ tsupport βf
    · have htW : t ∈ W := hsupp ht
      have hsrc : ξ t ∈ (chartAt H c).source := hWsub t htW
      have hsrc' : (extChartAt I c).symm (extChartAt I c (ξ t)) = ξ t := by
        apply PartialEquiv.left_inv; rw [extChartAt_source]; exact hsrc
      have heqfun : (fun u : ℝ => Fξ u t)
          = (fun u : ℝ => (extChartAt I c).symm (extChartAt I c (ξ t) + ηf u • (βf t • w))) := by
        funext u; exact hF_def u t htW
      rw [heqfun]
      have hbase : (extChartAt I c).symm (extChartAt I c (ξ t)) ∈ (chartAt H c).source := by
        rw [hsrc']; exact hsrc
      have hcsv := chartSlice_mfderiv_value (I := I) c (extChartAt I c (ξ t)) (βf t • w) ηf
        hη_smooth hη0 hη'0 (fun u => hmem u t hsrc) hbase
      rw [hsrc'] at hcsv
      exact hcsv
    · have hβ0 : βf t = 0 := image_eq_zero_of_notMem_tsupport ht
      have heqfun : (fun u : ℝ => Fξ u t) = (fun _ : ℝ => ξ t) := by
        funext u; exact hF_out u t ht
      rw [hβ0, zero_smul, map_zero, heqfun]
      rw [mfderiv_const]
      rfl
  have hFcentral : ∀ t, (fun u : ℝ => Fξ 0 u) t = ξ t := hF0
  have hUnit : ∀ t ∈ Set.Icc (0 : ℝ) len,
      g.inner (Fξ 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => Fξ 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => Fξ 0 u) t (1 : ℝ)) = 1 := by
    intro t ht
    have hslice_eq : (fun u : ℝ => Fξ 0 u) = ξ := funext hF0
    rw [hslice_eq, hF0 t]
    exact hξunit t ht
  have hfv := first_variation_of_arcLength_free_endpoints (I := I) g Fξ len hsmooth hlen hUnit
  have hslice_eq : (fun v : ℝ => Fξ 0 v) = ξ := funext hF0
  have hcov0 : ∀ t ∈ Set.Icc (0 : ℝ) len,
      covDerivAlong (I := I) g ξ
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I ξ v (1 : ℝ)) t = 0 := by
    intro t ht
    exact (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt (I := I) g ξ t hξsmooth).mpr
      (hξgeo.hasGeodesicEquationAt ht)
  have hintzero :
      (∫ t in (0 : ℝ)..len,
        g.inner (Fξ 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => Fξ u t) 0 (1 : ℝ))
          (covDerivAlong (I := I) g (fun v : ℝ => Fξ 0 v)
            (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => Fξ 0 w) v (1 : ℝ)) t)) = 0 := by
    rw [show (∫ t in (0 : ℝ)..len,
        g.inner (Fξ 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => Fξ u t) 0 (1 : ℝ))
          (covDerivAlong (I := I) g (fun v : ℝ => Fξ 0 v)
            (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => Fξ 0 w) v (1 : ℝ)) t))
        = ∫ _t in (0 : ℝ)..len, (0 : ℝ) from ?_, intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hlen.le] at ht
    simp only
    have hcov : covDerivAlong (I := I) g (fun v : ℝ => Fξ 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => Fξ 0 w) v (1 : ℝ)) t = 0 := by
      rw [hslice_eq]; exact hcov0 t ht
    rw [hcov, map_zero]
  have hbdry : HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => Fξ s t) 0 len)
        (g.inner (ξ len)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (ξ len) (βf len • w))
            (mfderiv (𝓘(ℝ, ℝ)) I ξ len (1 : ℝ))
          - g.inner (ξ 0)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (ξ 0) (βf 0 • w))
            (mfderiv (𝓘(ℝ, ℝ)) I ξ 0 (1 : ℝ))) 0 := by
    convert hfv using 1
    rw [hintzero, sub_zero, hF0 len, hF0 0, hslice_eq]
    congr 1
    · congr 2
      exact (hV len).symm
    · congr 2
      exact (hV 0).symm
  refine ⟨hbdry, ?_, ?_⟩
  · rw [arcLength]
    have hcongr : (∫ t in (0 : ℝ)..len,
        Real.sqrt (g.inner (ξ t)
          (mfderiv (𝓘(ℝ, ℝ)) I ξ t (1 : ℝ)) (mfderiv (𝓘(ℝ, ℝ)) I ξ t (1 : ℝ))))
        = ∫ _t in (0 : ℝ)..len, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hlen.le] at ht
      simp only
      rw [hξunit t ht, Real.sqrt_one]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  · intro s
    have hslice_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun t : ℝ => Fξ s t) := by
      have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
          (fun t : ℝ => (s, t)) := contMDiff_const.prodMk contMDiff_id
      exact (hsmooth : ContMDiff _ _ _ _).comp hincl
    have hvelTM : Continuous (fun t : ℝ => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (Fξ s t)
        (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => Fξ s t) t (1 : ℝ))) := by
      have := MFDerivAlongCurve.continuous_tangentMap_unitLift (I := I) (M := M)
        (γ := fun t : ℝ => Fξ s t)
        (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) hslice_smooth
      simpa only [tangentMap] using this
    have hspeed_cont : ContinuousOn (fun t : ℝ => Real.sqrt
        (g.inner (Fξ s t)
          (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => Fξ s t) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => Fξ s t) t (1 : ℝ)))) (Set.Icc 0 len) :=
      Real.continuous_sqrt.comp_continuousOn
        (continuousOn_g_inner_along_curve (I := I) g
          hvelTM.continuousOn hvelTM.continuousOn)
    set Fspeed : ℝ → ℝ := fun t : ℝ => Real.sqrt
      (g.inner (Fξ s t)
        (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => Fξ s t) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => Fξ s t) t (1 : ℝ))) with hFspeed_def
    have hFspeed_nn : ∀ t, 0 ≤ Fspeed t := fun t => Real.sqrt_nonneg _
    have hFspeed_int : MeasureTheory.IntegrableOn Fspeed (Set.Icc 0 len) MeasureTheory.volume :=
      hspeed_cont.integrableOn_compact isCompact_Icc
    have hpath_eq : pathELength I (fun t : ℝ => Fξ s t) 0 len
        = ENNReal.ofReal (arcLength (I := I) g (fun t : ℝ => Fξ s t) 0 len) := by
      have harc_eq : arcLength (I := I) g (fun t : ℝ => Fξ s t) 0 len
          = ∫ t in Set.Icc 0 len, Fspeed t := by
        rw [arcLength, intervalIntegral.integral_of_le hlen.le,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc, harc_eq,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFspeed_int
          (MeasureTheory.ae_of_all _ hFspeed_nn)]
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun t _ht => ?_)
      rw [hFspeed_def]
      exact hEnorm (Fξ s t) (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => Fξ s t) t (1 : ℝ))
    rw [← hpath_eq]
    have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t : ℝ => Fξ s t) (Set.Icc 0 len) :=
      (hslice_smooth.contMDiffOn).of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8))
    exact riemannianEDist_le_pathELength (I := I) (γ := fun t : ℝ => Fξ s t)
      (a := 0) (b := len) hC1 rfl rfl hlen.le

/-- **Localised bump + margin for one geodesic half.** Around a junction time `jt`
where the `C^∞` curve `ξ` is at `c`, builds a smooth, compactly supported bump
`βf` with `βf jt = 1`, `tsupport βf` inside the open set `W := ξ⁻¹(chart source)`
and avoiding the far time `fe`, together with a positive margin `r` such that any
chart-coordinate perturbation of `ξ` on `tsupport βf` of size `< r` stays inside
the chart target. This packages the geometric data feeding
`broken_piece_firstVariation`. -/
private lemma exists_broken_bump
    (c : M) {ξ : ℝ → M} {jt fe : ℝ} (hjtfe : jt ≠ fe) (hjtc : ξ jt = c)
    (hξsmooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ ξ) :
    ∃ (βf : ℝ → ℝ) (W : Set ℝ) (r : ℝ),
      0 < r ∧ IsOpen W ∧ (∀ t ∈ W, ξ t ∈ (chartAt H c).source) ∧ tsupport βf ⊆ W
      ∧ ContDiff ℝ ∞ βf ∧ βf jt = 1 ∧ βf fe = 0 ∧ (∀ t, βf t ∈ Set.Icc (0 : ℝ) 1)
      ∧ fe ∉ tsupport βf
      ∧ (∀ t ∈ tsupport βf, extChartAt I c (ξ t) ∈ (extChartAt I c).target)
      ∧ (∀ t ∈ tsupport βf, ∀ z : E,
          ‖z - extChartAt I c (ξ t)‖ < r → z ∈ (extChartAt I c).target) := by
  classical
  set U : Set M := (chartAt H c).source with hU
  have hUopen : IsOpen U := (chartAt H c).open_source
  have hjtU : ξ jt ∈ U := by rw [hjtc]; exact mem_chart_source H c
  set W₀ : Set ℝ := ξ ⁻¹' U with hW₀
  have hW₀open : IsOpen W₀ := hUopen.preimage hξsmooth.continuous
  have hjtW₀ : jt ∈ W₀ := hjtU
  set W : Set ℝ := W₀ ∩ {fe}ᶜ with hWdef
  have hWopen : IsOpen W := hW₀open.inter isOpen_compl_singleton
  have hjtW : jt ∈ W := ⟨hjtW₀, hjtfe⟩
  have hWnhds : W ∈ nhds jt := hWopen.mem_nhds hjtW
  obtain ⟨βf, hβtsupp, hβcompact, hβsmooth0, hβrange, hβjt⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (x := jt) hWnhds
  have hβsmooth : ContDiff ℝ ∞ βf := by
    have : ((⊤ : ℕ∞) : WithTop ℕ∞) = (∞ : WithTop ℕ∞) := rfl
    rwa [this] at hβsmooth0
  have hWsub : ∀ t ∈ W, ξ t ∈ (chartAt H c).source := fun t ht => ht.1
  have hβfe : βf fe = 0 := by
    by_contra hne
    have : fe ∈ tsupport βf := subset_tsupport _ (by simpa [Function.mem_support] using hne)
    have : fe ∈ W := hβtsupp this
    exact this.2 rfl
  have hβIcc : ∀ t, βf t ∈ Set.Icc (0 : ℝ) 1 := fun t => hβrange ⟨t, rfl⟩
  have hξimg_compact : IsCompact (ξ '' tsupport βf) := hβcompact.image hξsmooth.continuous
  have hξimg_sub : ξ '' tsupport βf ⊆ (extChartAt I c).source := by
    rintro x ⟨t, ht, rfl⟩; rw [extChartAt_source]; exact hWsub t (hβtsupp ht)
  have hcompact_img : IsCompact (extChartAt I c '' (ξ '' tsupport βf)) :=
    hξimg_compact.image_of_continuousOn ((continuousOn_extChartAt c).mono hξimg_sub)
  have hsub_target : extChartAt I c '' (ξ '' tsupport βf) ⊆ (extChartAt I c).target := by
    rintro y ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    apply (extChartAt I c).map_source
    rw [extChartAt_source]; exact hWsub t (hβtsupp ht)
  have htarget_open : IsOpen (extChartAt I c).target := isOpen_extChartAt_target c
  obtain ⟨r, hr_pos, hr_thick⟩ :=
    hcompact_img.exists_thickening_subset_open htarget_open hsub_target
  refine ⟨βf, W, r, hr_pos, hWopen, hWsub, hβtsupp, hβsmooth, hβjt, hβfe, hβIcc, ?_, ?_, ?_⟩
  · intro hc; exact (hβtsupp hc).2 rfl
  · intro t ht
    apply (extChartAt I c).map_source
    rw [extChartAt_source]; exact hWsub t (hβtsupp ht)
  · intro t ht z hz
    apply hr_thick
    rw [Metric.mem_thickening_iff]
    refine ⟨extChartAt I c (ξ t), ⟨ξ t, ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm]; exact hz

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **No corner at the junction of a length-minimising broken geodesic.**
For a unit-speed geodesic `γ` on `[0, ℓ₁]` and a unit-speed geodesic `σ` on
`[0, ℓ₂]` issuing from `γ ℓ₁ = σ 0`, whose concatenation realises the Riemannian
distance from `γ 0` to `σ ℓ₂` (length `ℓ₁ + ℓ₂`) and lies inside the normal ball
of the junction `c := γ ℓ₁`, the incoming velocity `γ'(ℓ₁)` equals the outgoing
velocity `σ'(0)`:
`mfderiv 𝓘(ℝ,ℝ) I γ ℓ₁ 1 = mfderiv 𝓘(ℝ,ℝ) I σ 0 1`.

This is the textbook "a minimising broken geodesic is unbroken" / no-corner
lemma, proved by the broken first variation of arc length.

The proof reduces, via positive definiteness of `g` (`g.pos`), to the vanishing of
the squared `g`-norm of the velocity jump `δ := σ'(0) - γ'(ℓ₁)` at the junction
`c`, which is the conclusion of the first-variation computation (smooth-chart
variation, free-endpoint formula on each geodesic half, and minimality of the
broken arc). -/
theorem broken_minimizer_velocity_match
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ σ : ℝ → M} {ℓ₁ ℓ₂ : ℝ} (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hγgeo : IsGeodesicOn (I := I) g γ (Set.Icc 0 ℓ₁))
    (hσgeo : IsGeodesicOn (I := I) g σ (Set.Icc 0 ℓ₂))
    (hγsmooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ)
    (hσsmooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ σ)
    (hγunit : ∀ t ∈ Set.Icc (0 : ℝ) ℓ₁,
      g.inner (γ t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (hσunit : ∀ t ∈ Set.Icc (0 : ℝ) ℓ₂,
      g.inner (σ t) (mfderiv (𝓘(ℝ, ℝ)) I σ t (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I σ t (1 : ℝ)) = 1)
    (hjunc : γ ℓ₁ = σ 0)
    (hmin : riemannianEDist I (γ 0) (σ ℓ₂) = ENNReal.ofReal (ℓ₁ + ℓ₂)) :
    mfderiv (𝓘(ℝ, ℝ)) I γ ℓ₁ (1 : ℝ) = mfderiv (𝓘(ℝ, ℝ)) I σ 0 (1 : ℝ) := by
  classical
  set c : M := γ ℓ₁ with hc_def
  set Tminus : E := (mfderiv (𝓘(ℝ, ℝ)) I γ ℓ₁ (1 : ℝ) : E) with hTminus_def
  set Tplus : E := (mfderiv (𝓘(ℝ, ℝ)) I σ 0 (1 : ℝ) : E) with hTplus_def
  set δ : E := Tplus - Tminus with hδ_def
  have hjump : g.inner c δ δ = 0 := by
    set w : E := (trivializationAt E (TangentSpace I) c).continuousLinearMapAt ℝ c δ with hw_def
    have hsymmLw : (trivializationAt E (TangentSpace I) c).symmL ℝ c w = δ :=
      (trivializationAt E (TangentSpace I) c).symmL_continuousLinearMapAt
        (FiberBundle.mem_baseSet_trivializationAt' c) δ
    have hσ0c : σ 0 = c := hjunc.symm
    obtain ⟨βγ, Wγ, rγ, hrγ, hWγopen, hWγsub, hβγsupp, hβγsmooth, hβγjt, hβγfe,
        hβγIcc, hβγfenot, hβγtarget, hβγmargin⟩ :=
      exists_broken_bump (I := I) c (ξ := γ) (jt := ℓ₁) (fe := 0)
        (ne_of_gt hℓ₁) hc_def.symm hγsmooth
    obtain ⟨βσ, Wσ, rσ, hrσ, hWσopen, hWσsub, hβσsupp, hβσsmooth, hβσjt, hβσfe,
        hβσIcc, hβσfenot, hβσtarget, hβσmargin⟩ :=
      exists_broken_bump (I := I) c (ξ := σ) (jt := 0) (fe := ℓ₂)
        (ne_of_lt hℓ₂) hσ0c hσsmooth
    set ρ : ℝ := min (rγ / (‖w‖ + 1)) (rσ / (‖w‖ + 1)) with hρ_def
    have hwpos : 0 < ‖w‖ + 1 := by positivity
    have hρ_pos : 0 < ρ := lt_min (div_pos hrγ hwpos) (div_pos hrσ hwpos)
    have hρrγ : ρ * ‖w‖ < rγ := by
      have h1 : ρ ≤ rγ / (‖w‖ + 1) := min_le_left _ _
      calc ρ * ‖w‖ ≤ (rγ / (‖w‖ + 1)) * ‖w‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < rγ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hwpos]
            nlinarith [norm_nonneg w, hrγ]
    have hρrσ : ρ * ‖w‖ < rσ := by
      have h1 : ρ ≤ rσ / (‖w‖ + 1) := min_le_right _ _
      calc ρ * ‖w‖ ≤ (rσ / (‖w‖ + 1)) * ‖w‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < rσ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hwpos]
            nlinarith [norm_nonneg w, hrσ]
    set ηf : ℝ → ℝ := fun s : ℝ => ρ * Real.sin (s / ρ) with hηf_def
    have hη_smooth : ContDiff ℝ ∞ ηf :=
      contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ρ))
    have hη0 : ηf 0 = 0 := by simp [hηf_def]
    have hη'0 : HasDerivAt ηf 1 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s / ρ) (1 / ρ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).div_const ρ
      have h2 : HasDerivAt Real.sin (Real.cos (0 / ρ)) (0 / ρ) := Real.hasDerivAt_sin _
      have h4 := ((h2.comp 0 h1).const_mul ρ)
      simp only [Real.cos_zero, zero_div] at h4
      convert h4 using 1
      field_simp
    have hηbd : ∀ s, |ηf s| ≤ ρ := by
      intro s
      rw [hηf_def, abs_mul, abs_of_pos hρ_pos]
      calc ρ * |Real.sin (s / ρ)| ≤ ρ * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hρ_pos.le
        _ = ρ := mul_one ρ
    have hpert_bd : ∀ (βf : ℝ → ℝ) (s t : ℝ), (∀ t, βf t ∈ Set.Icc (0 : ℝ) 1) →
        ‖ηf s • (βf t • w)‖ ≤ ρ * ‖w‖ := by
      intro βf s t hβIcc
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |ηf s| ≤ ρ := hηbd s
      have h2 : |βf t| ≤ 1 := by
        rw [abs_of_nonneg (hβIcc t).1]; exact (hβIcc t).2
      calc |ηf s| * (|βf t| * ‖w‖) ≤ ρ * (1 * ‖w‖) := by
            apply mul_le_mul h1 _ (by positivity) hρ_pos.le
            exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ρ * ‖w‖ := by ring
    have hmemγ : ∀ s t, γ t ∈ (chartAt H c).source →
        extChartAt I c (γ t) + ηf s • (βγ t • w) ∈ (extChartAt I c).target := by
      intro s t hsrc
      by_cases ht : t ∈ tsupport βγ
      · apply hβγmargin t ht
        rw [add_sub_cancel_left]
        calc ‖ηf s • (βγ t • w)‖ ≤ ρ * ‖w‖ := hpert_bd βγ s t hβγIcc
          _ < rγ := hρrγ
      · have hβ0 : βγ t = 0 := image_eq_zero_of_notMem_tsupport ht
        rw [hβ0, zero_smul, smul_zero, add_zero]
        apply (extChartAt I c).map_source
        rw [extChartAt_source]; exact hsrc
    have hmemσ : ∀ s t, σ t ∈ (chartAt H c).source →
        extChartAt I c (σ t) + ηf s • (βσ t • w) ∈ (extChartAt I c).target := by
      intro s t hsrc
      by_cases ht : t ∈ tsupport βσ
      · apply hβσmargin t ht
        rw [add_sub_cancel_left]
        calc ‖ηf s • (βσ t • w)‖ ≤ ρ * ‖w‖ := hpert_bd βσ s t hβσIcc
          _ < rσ := hρrσ
      · have hβ0 : βσ t = 0 := image_eq_zero_of_notMem_tsupport ht
        rw [hβ0, zero_smul, smul_zero, add_zero]
        apply (extChartAt I c).map_source
        rw [extChartAt_source]; exact hsrc
    set Fγ : ℝ → ℝ → M := fun s t =>
      if t ∈ Wγ then (extChartAt I c).symm (extChartAt I c (γ t) + ηf s • (βγ t • w)) else γ t
      with hFγ_def
    set Fσ : ℝ → ℝ → M := fun s t =>
      if t ∈ Wσ then (extChartAt I c).symm (extChartAt I c (σ t) + ηf s • (βσ t • w)) else σ t
      with hFσ_def
    have hFγ_in : ∀ s t, t ∈ Wγ → Fγ s t
        = (extChartAt I c).symm (extChartAt I c (γ t) + ηf s • (βγ t • w)) := by
      intro s t ht; simp only [hFγ_def]; exact if_pos ht
    have hFγ_out : ∀ s t, t ∉ tsupport βγ → Fγ s t = γ t := by
      intro s t ht
      have hβ0 : βγ t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp only [hFγ_def]
      by_cases htW : t ∈ Wγ
      · rw [if_pos htW, hβ0, zero_smul, smul_zero, add_zero]
        apply PartialEquiv.left_inv
        rw [extChartAt_source]; exact hWγsub t htW
      · rw [if_neg htW]
    have hFσ_in : ∀ s t, t ∈ Wσ → Fσ s t
        = (extChartAt I c).symm (extChartAt I c (σ t) + ηf s • (βσ t • w)) := by
      intro s t ht; simp only [hFσ_def]; exact if_pos ht
    have hFσ_out : ∀ s t, t ∉ tsupport βσ → Fσ s t = σ t := by
      intro s t ht
      have hβ0 : βσ t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp only [hFσ_def]
      by_cases htW : t ∈ Wσ
      · rw [if_pos htW, hβ0, zero_smul, smul_zero, add_zero]
        apply PartialEquiv.left_inv
        rw [extChartAt_source]; exact hWσsub t htW
      · rw [if_neg htW]
    obtain ⟨hbdryγ, harcγ, hedistγ⟩ :=
      broken_piece_firstVariation (I := I) g hEnorm c w hℓ₁ hγsmooth hγgeo hγunit
        ηf βγ hη_smooth hη0 hη'0 hβγsmooth Wγ hWγopen hWγsub hβγsupp
        (fun s t hsrc => hmemγ s t hsrc) Fγ hFγ_in hFγ_out
    obtain ⟨hbdryσ, harcσ, hedistσ⟩ :=
      broken_piece_firstVariation (I := I) g hEnorm c w hℓ₂ hσsmooth hσgeo hσunit
        ηf βσ hη_smooth hη0 hη'0 hβσsmooth Wσ hWσopen hWσsub hβσsupp
        (fun s t hsrc => hmemσ s t hsrc) Fσ hFσ_in hFσ_out
    have hsymm1 : (trivializationAt E (TangentSpace I) c).symmL ℝ c (βγ ℓ₁ • w) = δ := by
      rw [hβγjt, one_smul]; exact hsymmLw
    have hsymm0γ : (trivializationAt E (TangentSpace I) c).symmL ℝ (γ 0) (βγ 0 • w) = 0 := by
      rw [hβγfe, zero_smul, map_zero]
    have hsymm1σ : (trivializationAt E (TangentSpace I) c).symmL ℝ c (βσ 0 • w) = δ := by
      rw [hβσjt, one_smul]; exact hsymmLw
    have hsymm0σ : (trivializationAt E (TangentSpace I) c).symmL ℝ (σ ℓ₂) (βσ ℓ₂ • w) = 0 := by
      rw [hβσfe, zero_smul, map_zero]
    have hbdryγ' : HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => Fγ s t) 0 ℓ₁)
        (g.inner c δ Tminus) 0 := by
      have heq : g.inner (γ ℓ₁)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (γ ℓ₁) (βγ ℓ₁ • w))
            (mfderiv (𝓘(ℝ, ℝ)) I γ ℓ₁ (1 : ℝ))
          - g.inner (γ 0)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (γ 0) (βγ 0 • w))
            (mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ))
          = g.inner c δ Tminus := by
        rw [← hc_def, hsymm1, hsymm0γ, map_zero, ContinuousLinearMap.zero_apply, sub_zero]
      rw [← heq]; exact hbdryγ
    have hbdryσ' : HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => Fσ s t) 0 ℓ₂)
        (- g.inner c δ Tplus) 0 := by
      have heq : g.inner (σ ℓ₂)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (σ ℓ₂) (βσ ℓ₂ • w))
            (mfderiv (𝓘(ℝ, ℝ)) I σ ℓ₂ (1 : ℝ))
          - g.inner (σ 0)
            ((trivializationAt E (TangentSpace I) c).symmL ℝ (σ 0) (βσ 0 • w))
            (mfderiv (𝓘(ℝ, ℝ)) I σ 0 (1 : ℝ))
          = - g.inner c δ Tplus := by
        rw [hσ0c, hsymm1σ, hsymm0σ, map_zero, ContinuousLinearMap.zero_apply, zero_sub]
        rfl
      rw [← heq]; exact hbdryσ
    set Lfun : ℝ → ℝ := fun s : ℝ =>
      arcLength (I := I) g (fun t : ℝ => Fγ s t) 0 ℓ₁
        + arcLength (I := I) g (fun t : ℝ => Fσ s t) 0 ℓ₂ with hLfun_def
    have hLderiv0 : HasDerivAt Lfun (g.inner c δ Tminus + - g.inner c δ Tplus) 0 :=
      hbdryγ'.add hbdryσ'
    have hLval : g.inner c δ Tminus + - g.inner c δ Tplus = - g.inner c δ δ := by
      have hbil : g.inner c δ Tminus - g.inner c δ Tplus = g.inner c δ (Tminus - Tplus) :=
        (ContinuousLinearMap.map_sub (g.inner c δ) Tminus Tplus).symm
      have hsub : Tminus - Tplus = -δ := by rw [hδ_def]; abel
      rw [show g.inner c δ Tminus + - g.inner c δ Tplus
          = g.inner c δ Tminus - g.inner c δ Tplus from by ring, hbil, hsub]
      exact ContinuousLinearMap.map_neg _ _
    have hLderiv : HasDerivAt Lfun (- g.inner c δ δ) 0 := hLval ▸ hLderiv0
    have hFγ0 : ∀ t, Fγ 0 t = γ t := by
      intro t
      by_cases ht : t ∈ Wγ
      · rw [hFγ_in 0 t ht, hη0, zero_smul, add_zero]
        apply PartialEquiv.left_inv
        rw [extChartAt_source]; exact hWγsub t ht
      · exact hFγ_out 0 t (fun hc => ht (hβγsupp hc))
    have hFσ0 : ∀ t, Fσ 0 t = σ t := by
      intro t
      by_cases ht : t ∈ Wσ
      · rw [hFσ_in 0 t ht, hη0, zero_smul, add_zero]
        apply PartialEquiv.left_inv
        rw [extChartAt_source]; exact hWσsub t ht
      · exact hFσ_out 0 t (fun hc => ht (hβσsupp hc))
    have hL0 : Lfun 0 = ℓ₁ + ℓ₂ := by
      rw [hLfun_def]
      simp only
      rw [show (fun t : ℝ => Fγ 0 t) = γ from funext hFγ0,
        show (fun t : ℝ => Fσ 0 t) = σ from funext hFσ0]
      rw [harcγ, harcσ]
    have hFγfix : ∀ s, Fγ s 0 = γ 0 := fun s => hFγ_out s 0 hβγfenot
    have hFσfix : ∀ s, Fσ s ℓ₂ = σ ℓ₂ := fun s => hFσ_out s ℓ₂ hβσfenot
    have hjunction : ∀ s, Fγ s ℓ₁ = Fσ s 0 := by
      intro s
      have hℓ₁W : ℓ₁ ∈ Wγ := hβγsupp (subset_tsupport _ (by
        simp only [Function.mem_support, hβγjt]; exact one_ne_zero))
      have h0W : (0 : ℝ) ∈ Wσ := hβσsupp (subset_tsupport _ (by
        simp only [Function.mem_support, hβσjt]; exact one_ne_zero))
      rw [hFγ_in s ℓ₁ hℓ₁W, hFσ_in s 0 h0W, hβγjt, hβσjt, ← hc_def, hσ0c]
    have hLmin : ∀ s, ℓ₁ + ℓ₂ ≤ Lfun s := by
      intro s
      have htri : riemannianEDist I (γ 0) (σ ℓ₂)
          ≤ riemannianEDist I (γ 0) (Fγ s ℓ₁) + riemannianEDist I (Fγ s ℓ₁) (σ ℓ₂) :=
        riemannianEDist_triangle
      have hd1 : riemannianEDist I (γ 0) (Fγ s ℓ₁)
          ≤ ENNReal.ofReal (arcLength (I := I) g (fun t : ℝ => Fγ s t) 0 ℓ₁) := by
        have := hedistγ s
        rwa [hFγfix s] at this
      have hd2 : riemannianEDist I (Fγ s ℓ₁) (σ ℓ₂)
          ≤ ENNReal.ofReal (arcLength (I := I) g (fun t : ℝ => Fσ s t) 0 ℓ₂) := by
        have := hedistσ s
        rwa [← hjunction s, hFσfix s] at this
      have harc1_nn : 0 ≤ arcLength (I := I) g (fun t : ℝ => Fγ s t) 0 ℓ₁ := by
        rw [arcLength, intervalIntegral.integral_of_le hℓ₁.le]
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => Real.sqrt_nonneg _)
      have harc2_nn : 0 ≤ arcLength (I := I) g (fun t : ℝ => Fσ s t) 0 ℓ₂ := by
        rw [arcLength, intervalIntegral.integral_of_le hℓ₂.le]
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => Real.sqrt_nonneg _)
      have hchain : ENNReal.ofReal (ℓ₁ + ℓ₂) ≤ ENNReal.ofReal (Lfun s) := by
        rw [← hmin]
        refine htri.trans ?_
        rw [hLfun_def]
        simp only
        rw [ENNReal.ofReal_add harc1_nn harc2_nn]
        exact add_le_add hd1 hd2
      have hLs_nn : 0 ≤ Lfun s := by rw [hLfun_def]; simp only; exact add_nonneg harc1_nn harc2_nn
      exact (ENNReal.ofReal_le_ofReal_iff hLs_nn).mp hchain
    have hisMin : IsMinOn Lfun Set.univ 0 := by
      intro s _
      rw [hL0]; exact hLmin s
    have hLocalMin : IsLocalMin Lfun 0 :=
      hisMin.isLocalMin (Filter.univ_mem)
    have hLderiv_zero : - g.inner c δ δ = 0 := hLocalMin.hasDerivAt_eq_zero hLderiv
    linarith [hLderiv_zero]
  have hδ0 : δ = 0 := by
    by_contra hδ_ne
    exact absurd hjump (ne_of_gt (g.pos c δ hδ_ne))
  have hTeq : Tplus = Tminus := sub_eq_zero.mp hδ0
  change (mfderiv (𝓘(ℝ, ℝ)) I γ ℓ₁ (1 : ℝ) : E) = (mfderiv (𝓘(ℝ, ℝ)) I σ 0 (1 : ℝ) : E)
  rw [← hTminus_def, ← hTplus_def]; exact hTeq.symm

/-- **Additive time-translation of the moving-foot geodesic equation.**  If `η`
satisfies the geodesic equation at `t + T`, then the time-translated curve
`s ↦ η (s + T)` satisfies it at `t`. -/
private lemma hasGeodesicEquationAt_comp_add_const
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} (T t : ℝ)
    (h : DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicEquationAt
      (I := I) g η (t + T)) :
    DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicEquationAt
      (I := I) g (fun s => η (s + T)) t := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := h
  have hshift :
      DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve
        (I := I) (fun s => η (s + T)) t =
      fun s => DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve
        (I := I) η (t + T) (s + T) := by funext s; rfl
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]; exact hv.comp_add_const t T
  · rw [hshift]
    have hderiv : ∀ s,
        deriv (fun s => DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve
            (I := I) η (t + T) (s + T)) s =
          deriv (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve
            (I := I) η (t + T)) (s + T) := fun s =>
      deriv_comp_add_const
        (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve (I := I) η (t + T)) T s
    have hev' : ∀ᶠ s in nhds t, HasDerivAt
        (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve (I := I) η (t + T))
        (deriv (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve
          (I := I) η (t + T)) (s + T)) (s + T) :=
      ((continuous_id.add continuous_const).continuousAt).eventually hev
    filter_upwards [hev'] with s hs
    rw [hderiv s]; exact hs.comp_add_const s T
  · rw [hshift]
    have hd2 : (fun s => deriv
        (fun s => DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve
          (I := I) η (t + T) (s + T)) s) =
        fun s => deriv (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve
          (I := I) η (t + T)) (s + T) := by
      funext s
      exact deriv_comp_add_const
        (DifferentialGeometry.Geometry.Riemannian.Geodesic.chartLocalCurve (I := I) η (t + T)) T s
    rw [hd2]; exact ha.comp_add_const t T
  · exact hgeo

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Moving-foot continuation of the intrinsic geodesic.**  For the complete
intrinsic geodesic `γ := intrinsicGeodesic p u`, the time-translated continuation
`s ↦ γ (s + t₀)` is exactly the fresh intrinsic geodesic launched from the moving
foot `γ t₀` with velocity `γ'(t₀)`:
`intrinsicGeodesic p u (s + t₀) = intrinsicGeodesic (γ t₀) (γ'(t₀)) s` for all `s`,
where `γ'(t₀)` is the fibre vector `mfderiv 𝓘(ℝ,ℝ) I γ t₀ 1`.  Proved by global
uniqueness `isGeodesic_eq_of_initial`: the continuation is a complete geodesic
(autonomous time-translation `hasGeodesicEquationAt_comp_add_const`), continuous,
with matching foot and launch velocity. -/
theorem intrinsicGeodesic_continuation
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u : TangentSpace I p) (t₀ : ℝ) :
    (fun s => intrinsicGeodesic (I := I) g hEnorm p u (s + t₀))
      = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm p u t₀)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p u) t₀ (1 : ℝ)) := by
  classical
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u with hγ_def
  set c : M := γ t₀ with hc_def
  set w₂ : TangentSpace I c := mfderiv 𝓘(ℝ, ℝ) I γ t₀ (1 : ℝ) with hw₂_def
  set η : ℝ → M := fun s => γ (s + t₀) with hη_def
  have hγ_geo : Geodesic.IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p u
  have hη_geo : Geodesic.IsGeodesic (I := I) g η := by
    intro t
    have := hasGeodesicEquationAt_comp_add_const (I := I) g t₀ t (hγ_geo (t + t₀))
    exact this
  have hη_cont : Continuous η := hγ_cont.comp (by fun_prop)
  have hη0 : η 0 = c := by rw [hη_def]; simp only [zero_add]; rfl
  have hψ_geo : Geodesic.IsGeodesic (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm c w₂) :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm c w₂
  have hψ_cont : Continuous (intrinsicGeodesic (I := I) g hEnorm c w₂) :=
    intrinsicGeodesic_continuous (I := I) g hEnorm c w₂
  have hψ0 : intrinsicGeodesic (I := I) g hEnorm c w₂ 0 = c :=
    intrinsicGeodesic_zero (I := I) g hEnorm c w₂
  have hfoot : η 0 = intrinsicGeodesic (I := I) g hEnorm c w₂ 0 := by rw [hη0, hψ0]
  have hmdiff_γ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t₀ :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p u).contMDiffAt
      (Filter.univ_mem)).mdifferentiableAt (by norm_num)
  have hη_vel : (mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ) : E) = (w₂ : E) := by
    have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + t₀)
        (0 : ℝ) (ContinuousLinearMap.id ℝ ℝ) := by
      rw [hasMFDerivAt_iff_hasFDerivAt]
      simpa using (hasFDerivAt_id (0 : ℝ)).add_const t₀
    have hγ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I γ ((0 : ℝ) + t₀) (mfderiv 𝓘(ℝ, ℝ) I γ ((0 : ℝ) + t₀)) := by
      rw [zero_add]; exact hmdiff_γ.hasMFDerivAt
    have hη_mfderiv : mfderiv 𝓘(ℝ, ℝ) I η 0
        = (mfderiv 𝓘(ℝ, ℝ) I γ ((0 : ℝ) + t₀)).comp (ContinuousLinearMap.id ℝ ℝ) :=
      (hγ_at.comp 0 hshift).mfderiv
    have happ : mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) I γ t₀ (1 : ℝ) := by
      have h1 : mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ)
          = (mfderiv 𝓘(ℝ, ℝ) I γ ((0 : ℝ) + t₀)) ((ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)) := by
        rw [hη_mfderiv]; rfl
      rw [h1, ContinuousLinearMap.id_apply, zero_add]
    rw [happ]
  have hψ_vel : (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm c w₂) 0 (1 : ℝ) : E)
      = (w₂ : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm c w₂
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ) : E)
      = (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm c w₂) 0 (1 : ℝ) : E) := by
    rw [hη_vel, hψ_vel]
  exact isGeodesic_eq_of_initial (I := I) g hη_geo hψ_geo hη_cont hψ_cont hfoot hvel

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Hopf–Rinow surjectivity with a minimizing witness.** On a complete Riemannian
manifold, for every `p q : M` there is a tangent vector `v : T_p M` with
`expMapIntrinsic g hEnorm p v = q` and `g`-speed `√(g_p(v, v))` equal to the
Riemannian distance `(riemannianEDist I p q).toReal`; i.e. `q` is reached by a
minimizing intrinsic geodesic out of `p`.

The hypothesis `hEnorm` is the structural identity that the tangent-bundle extended
norm `‖·‖ₑ` is `√(g_p(·,·))`; the real Riemannian distance is taken as
`(riemannianEDist I p q).toReal` (the project has no separate `riemannianDist`).

The proof is the ray/sphere Hopf–Rinow argument.

* `r := (riemannianEDist I p q).toReal = 0`: then `q = p` (point separation
  `riemannianEDist_eq_zero_imp_eq`) and `v := 0` works (`expMapIntrinsic_zero`;
  the `g`-speed of `0` is `0 = r`).

* `r > 0`: a base sphere-jump `sphere_jump` at `p` produces a `g`-unit launch
  direction `u` along which the radial ray `γ(t) := expMapIntrinsic g hEnorm p (t • u)`
  heads toward `q`.  The propagation set `A := { t ∈ [0, r] |
  (riemannianEDist I (γ t) q).toReal = r - t }` is closed (`propagationSet_isClosed`),
  contains a positive `δ₀` (from the base sphere-jump), and is bounded above by `r`,
  so its supremum `t₀ := sSup A` is attained (`IsClosed.csSup_mem`): `t₀ ∈ A` with
  `0 < t₀ ≤ r`.  One shows `t₀ = r`; then `(riemannianEDist (γ r) q).toReal = 0`, so
  `riemannianEDist (γ r) q = 0` (finiteness `riemannianEDist_ne_top`) and `γ r = q`
  (point separation).  The witness `v := r • u` satisfies
  `expMapIntrinsic g hEnorm p v = γ r = q` and
  `√(g_p(r•u, r•u)) = r · √(g_p(u,u)) = r` (`sqrt_gInner_smul_self`, `g.inner p u u = 1`).

The strict-supremum step `t₀ < r → False` (the "no-corner" moving-foot extension)
runs as follows: a sphere-jump at the moving foot `c := γ(t₀)` produces a
sphere-minimiser `y₁ = expMapIntrinsic c (δ' • w₂)` with `d(c, y₁) = δ'`,
`d(y₁, q) = (r - t₀) - δ'`, and hence `d(p, y₁) = t₀ + δ'`.  The two unit-speed
geodesics `Γu := intrinsicGeodesic p u` (on `[0, t₀]`) and `σ := intrinsicGeodesic c w₂`
(on `[0, δ']`) meet the hypotheses of the broken-geodesic no-corner lemma
`broken_minimizer_velocity_match`, whose conclusion `mfderiv Γu t₀ 1 = mfderiv σ 0 1 = w₂`
identifies the forward radial direction at the foot with `w₂`.  The autonomous
time-translation continuation `intrinsicGeodesic_continuation` then forces
`Γu(t₀ + δ') = σ δ' = y₁`, so `t₀ + δ' ∈ A`, contradicting `δ' > 0` and `t₀ = sSup A`. -/
theorem hopf_rinow_expMapIntrinsic_surjective_minimizing
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) :
    ∃ v : TangentSpace I p, expMapIntrinsic (I := I) g hEnorm p v = q ∧
      Real.sqrt (g.inner p v v) = (riemannianEDist I p q).toReal := by
  classical
  set r : ℝ := (riemannianEDist I p q).toReal with hr_def
  rcases eq_or_ne (riemannianEDist I p q) 0 with hpq0 | hpq_pos
  · have hpq : p = q := riemannianEDist_eq_zero_imp_eq (I := I) p q hpq0
    refine ⟨0, ?_, ?_⟩
    · have hexp0 : expMapIntrinsic (I := I) g hEnorm p 0 = p :=
        expMapIntrinsic_zero (I := I) g hEnorm p
      rw [hexp0, hpq]
    · have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by simp
      rw [h0, Real.sqrt_zero, hr_def, hpq0, ENNReal.toReal_zero]
  · have hr_ne_top : riemannianEDist I p q ≠ ⊤ := riemannianEDist_ne_top (I := I) p q
    have hr_pos : 0 < r := by
      rw [hr_def]
      exact ENNReal.toReal_pos hpq_pos hr_ne_top
    have hpq_eq : riemannianEDist I p q = ENNReal.ofReal r := by
      rw [hr_def, ENNReal.ofReal_toReal hr_ne_top]
    obtain ⟨Rp, hRp_pos, hbase⟩ := sphere_jump (I := I) g hEnorm p q hr_pos hpq_eq
    set δ₀ : ℝ := min (Rp / 2) (r / 2) with hδ₀_def
    have hδ₀_pos : 0 < δ₀ := lt_min (by linarith) (by linarith)
    have hδ₀_Rp : δ₀ < Rp := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ₀_r : δ₀ < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨yb, u, hu_unit, hyb_eq, hyb_dxy, hyb_dyq⟩ := hbase hδ₀_pos hδ₀_Rp hδ₀_r
    set γ : ℝ → M := fun t => expMapIntrinsic (I := I) g hEnorm p (t • u) with hγ_def
    set A : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) r ∧
      (riemannianEDist I (γ t) q).toReal = r - t} with hA_def
    have hA_closed : IsClosed A := by
      rw [hA_def, hγ_def]
      exact propagationSet_isClosed (I := I) g hEnorm p q u r
    have hγ0 : γ 0 = p := by
      rw [hγ_def]; simp only [zero_smul]
      exact expMapIntrinsic_zero (I := I) g hEnorm p
    have h0A : (0 : ℝ) ∈ A := by
      rw [hA_def]
      refine ⟨⟨le_refl 0, hr_pos.le⟩, ?_⟩
      rw [hγ0, sub_zero, hr_def]
    have hγδ₀ : γ δ₀ = yb := by rw [hγ_def]; exact hyb_eq.symm
    have hδ₀A : δ₀ ∈ A := by
      rw [hA_def]
      refine ⟨⟨hδ₀_pos.le, hδ₀_r.le⟩, ?_⟩
      rw [hγδ₀, hyb_dyq, ENNReal.toReal_ofReal (by linarith)]
    have hA_ne : A.Nonempty := ⟨0, h0A⟩
    have hA_sub : A ⊆ Set.Icc (0 : ℝ) r := fun t ht => ht.1
    have hA_bdd : BddAbove A := ⟨r, fun t ht => (hA_sub ht).2⟩
    set t₀ : ℝ := sSup A with ht₀_def
    have ht₀_mem : t₀ ∈ A := hA_closed.csSup_mem hA_ne hA_bdd
    have ht₀_Icc : t₀ ∈ Set.Icc (0 : ℝ) r := hA_sub ht₀_mem
    have ht₀_nn : 0 ≤ t₀ := ht₀_Icc.1
    have ht₀_le : t₀ ≤ r := ht₀_Icc.2
    have ht₀_pos : 0 < t₀ := lt_of_lt_of_le hδ₀_pos (le_csSup hA_bdd hδ₀A)
    have ht₀_dist : (riemannianEDist I (γ t₀) q).toReal = r - t₀ := ht₀_mem.2
    set Γu : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u with hΓu_def
    have hγ_eq : γ = Γu := by
      funext t
      rw [hΓu_def]
      change expMapIntrinsic (I := I) g hEnorm p (t • u) = intrinsicGeodesic (I := I) g hEnorm p u t
      rw [expMapIntrinsic_def, intrinsicGeodesic_smul (I := I) g hEnorm p u t]
    have hΓu_geo : Geodesic.IsGeodesic (I := I) g Γu :=
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u
    have hΓu_cont : Continuous Γu := intrinsicGeodesic_continuous (I := I) g hEnorm p u
    have hΓu_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ Γu := isGeodesic_contMDiff (I := I) g hΓu_geo hΓu_cont
    have hΓu_unit : ∀ t : ℝ,
        g.inner (Γu t) (mfderiv 𝓘(ℝ, ℝ) I Γu t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I Γu t (1 : ℝ)) = 1 := by
      intro t
      have hsp := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
      rw [hu_unit] at hsp
      exact hsp
    have ht₀_eq_r : t₀ = r := by
      by_contra hne'
      have ht₀_lt : t₀ < r := lt_of_le_of_ne ht₀_le hne'
      set c : M := Γu t₀ with hc_def
      set ρc : ℝ := r - t₀ with hρc_def
      have hρc_pos : 0 < ρc := by rw [hρc_def]; linarith
      have hcq_fin : riemannianEDist I c q ≠ ⊤ := riemannianEDist_ne_top (I := I) c q
      have hcq_eq : riemannianEDist I c q = ENNReal.ofReal ρc := by
        rw [← ENNReal.ofReal_toReal hcq_fin]
        congr 1
        rw [hc_def, ← hγ_eq, hρc_def]; exact ht₀_dist
      have hpc_le : riemannianEDist I p c ≤ ENNReal.ofReal t₀ := by
        have hb := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p u
          (s := 0) (t := t₀) ht₀_nn
        rw [intrinsicGeodesic_zero (I := I) g hEnorm p u, hu_unit, Real.sqrt_one, one_mul,
          sub_zero] at hb
        rw [hc_def, hΓu_def]; exact hb
      have hpc_ge : ENNReal.ofReal t₀ ≤ riemannianEDist I p c := by
        have htri : riemannianEDist I p q ≤ riemannianEDist I p c + riemannianEDist I c q :=
          riemannianEDist_triangle
        rw [hpq_eq, hcq_eq] at htri
        have hsplit : ENNReal.ofReal r = ENNReal.ofReal t₀ + ENNReal.ofReal ρc := by
          rw [← ENNReal.ofReal_add ht₀_nn hρc_pos.le]; congr 1; rw [hρc_def]; ring
        rw [hsplit] at htri
        exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htri
      have hpc_eq : riemannianEDist I p c = ENNReal.ofReal t₀ := le_antisymm hpc_le hpc_ge
      obtain ⟨Rc, hRc_pos, hcjump⟩ := sphere_jump (I := I) g hEnorm c q hρc_pos hcq_eq
      set δ' : ℝ := min (Rc / 2) (ρc / 2) with hδ'_def
      have hδ'_pos : 0 < δ' := lt_min (by linarith) (by linarith)
      have hδ'_Rc : δ' < Rc := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hδ'_ρc : δ' < ρc := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      obtain ⟨y₁, w₂, hw₂_unit, hy₁_eq, hy₁_dcy, hy₁_dyq⟩ := hcjump hδ'_pos hδ'_Rc hδ'_ρc
      have hpy₁_le : riemannianEDist I p y₁ ≤ ENNReal.ofReal (t₀ + δ') := by
        have htri : riemannianEDist I p y₁ ≤ riemannianEDist I p c + riemannianEDist I c y₁ :=
          riemannianEDist_triangle
        rw [hpc_eq, hy₁_dcy, ← ENNReal.ofReal_add ht₀_nn hδ'_pos.le] at htri
        exact htri
      have hpy₁_ge : ENNReal.ofReal (t₀ + δ') ≤ riemannianEDist I p y₁ := by
        have htri : riemannianEDist I p q ≤ riemannianEDist I p y₁ + riemannianEDist I y₁ q :=
          riemannianEDist_triangle
        rw [hpq_eq, hy₁_dyq] at htri
        have hsplit : ENNReal.ofReal r
            = ENNReal.ofReal (t₀ + δ') + ENNReal.ofReal (ρc - δ') := by
          rw [← ENNReal.ofReal_add (by positivity) (by linarith)]
          congr 1; rw [hρc_def]; ring
        rw [hsplit] at htri
        exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htri
      have hpy₁_eq : riemannianEDist I p y₁ = ENNReal.ofReal (t₀ + δ') :=
        le_antisymm hpy₁_le hpy₁_ge
      set σ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm c w₂ with hσ_def
      have hσ_geo : Geodesic.IsGeodesic (I := I) g σ :=
        intrinsicGeodesic_isGeodesic (I := I) g hEnorm c w₂
      have hσ_cont : Continuous σ := intrinsicGeodesic_continuous (I := I) g hEnorm c w₂
      have hσ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ σ := isGeodesic_contMDiff (I := I) g hσ_geo hσ_cont
      have hσ0 : σ 0 = c := intrinsicGeodesic_zero (I := I) g hEnorm c w₂
      have hσ_unit : ∀ t : ℝ,
          g.inner (σ t) (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ)) = 1 := by
        intro t
        have hsp := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm c w₂ t
        rw [hw₂_unit] at hsp
        exact hsp
      have hy₁_σ : y₁ = σ δ' := by
        rw [hy₁_eq, hσ_def, expMapIntrinsic_def, intrinsicGeodesic_smul (I := I) g hEnorm c w₂ δ']
      have hjunc : Γu t₀ = σ 0 := by rw [hσ0, hc_def]
      have hΓu0 : Γu 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p u
      have hmin : riemannianEDist I (Γu 0) (σ δ') = ENNReal.ofReal (t₀ + δ') := by
        rw [hΓu0, ← hy₁_σ]; exact hpy₁_eq
      have hvmatch : mfderiv 𝓘(ℝ, ℝ) I Γu t₀ (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) :=
        broken_minimizer_velocity_match (I := I) g hEnorm ht₀_pos hδ'_pos
          (hΓu_geo.isGeodesicOn (Set.Icc 0 t₀)) (hσ_geo.isGeodesicOn (Set.Icc 0 δ'))
          hΓu_smooth hσ_smooth (fun t _ => hΓu_unit t) (fun t _ => hσ_unit t) hjunc hmin
      have hσ_vel : mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) = w₂ := by
        have : (mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) : E) = (w₂ : E) :=
          intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm c w₂
        exact this
      have hvel_w₂ : mfderiv 𝓘(ℝ, ℝ) I Γu t₀ (1 : ℝ) = w₂ := by rw [hvmatch, hσ_vel]
      have hcont' : (fun s => Γu (s + t₀)) = σ := by
        have hcont := intrinsicGeodesic_continuation (I := I) g hEnorm p u t₀
        rw [hvel_w₂] at hcont
        rw [hσ_def]; exact hcont
      have hΓu_t₀δ' : Γu (t₀ + δ') = y₁ := by
        have h1 : Γu (δ' + t₀) = σ δ' := congrFun hcont' δ'
        rw [add_comm] at h1
        rw [h1, ← hy₁_σ]
      have hmem_new : t₀ + δ' ∈ A := by
        rw [hA_def]
        refine ⟨⟨by linarith, by rw [hρc_def] at hδ'_ρc; linarith⟩, ?_⟩
        rw [show γ (t₀ + δ') = y₁ by rw [hγ_eq]; exact hΓu_t₀δ', hy₁_dyq,
          ENNReal.toReal_ofReal (by linarith)]
        rw [hρc_def]; ring
      have hle_sup : t₀ + δ' ≤ t₀ := le_csSup hA_bdd hmem_new
      linarith
    have hr_dist : (riemannianEDist I (γ r) q).toReal = 0 := by
      have hd := ht₀_dist; rw [ht₀_eq_r] at hd; rw [hd, sub_self]
    have hr_dist0 : riemannianEDist I (γ r) q = 0 := by
      have hne_top : riemannianEDist I (γ r) q ≠ ⊤ := riemannianEDist_ne_top (I := I) _ q
      exact ((ENNReal.toReal_eq_zero_iff _).mp hr_dist).resolve_right hne_top
    have hγr_eq_q : γ r = q := riemannianEDist_eq_zero_imp_eq (I := I) (γ r) q hr_dist0
    refine ⟨r • u, ?_, ?_⟩
    · rw [hγ_def] at hγr_eq_q; exact hγr_eq_q
    · rw [sqrt_gInner_smul_self (I := I) g p hr_pos.le u, hu_unit, Real.sqrt_one, mul_one]

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
