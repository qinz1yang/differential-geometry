import DifferentialGeometry.Geometry.Riemannian.GaussLemma
import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import DifferentialGeometry.Geometry.Riemannian.RiemannianDistContinuity
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.PathConnected

set_option linter.unusedSectionVars false

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

/-!
# Radial-geodesic surjectivity on rieDist-closed balls

For a smooth Riemannian metric `g` on a connected, sigma-compact,
boundaryless smooth manifold `M` that is metric-complete as a
`PseudoEMetricSpace` and satisfies `IsRiemannianManifold I M`, this
file packages the open-closed-nonempty connectedness route to radial
surjectivity. The base point `p : M` is fixed and the radius is `R : ℝ`.

The route avoids any Arzelà–Ascoli / pre-assumed Heine–Borel argument:
points within `riemannianEDist`-distance `R` are reached by *minimising
radial geodesics* `t ↦ expMap g p (t • v)` with `g`-velocity-norm
`√(g.inner p v v) ≤ R`.

## The radial-minimiser set

`radialMinSet g p` is the set of points `q : M` reached by some
`v : T_p M` whose minimising radial geodesic has `g`-length equal to
the Riemannian distance:

`radialMinSet g p = { q | ∃ v, expMap g p v = q ∧
    ENNReal.ofReal (√(g.inner p v v)) = riemannianEDist I p q }`.

The velocity bound is stated with the intrinsic `g`-norm
`Real.sqrt (g.inner p v v)`, *not* the model-`E` norm `‖v‖`: the
latter has no a-priori relation to the metric `g` and its appearance in
earlier drafts of this file was an instance of the tangent-bundle norm
diamond leaking into a public statement.

## Main statements

* `gBall_isPreconnected` — the `g`-norm closed ball
  `{v | √(g.inner p v v) ≤ R}` in `T_p M` is preconnected (it is
  star-shaped about `0`).

* `radial_image_T_preconnected` — the `expMap g p`-image of the
  `g`-norm closed ball is preconnected, by continuity of `expMap g p`
  (`bm_c_expMap_continuous_of_geodesic_complete`). **Fully proven.**

* `radial_image_is_open` — `radialMinSet g p` is open *relative to* the
  `riemannianEDist`-closed-ball subspace of radius `R` at `p` (the
  subspace-open hypothesis required by the clopen-in-connected step).

* `radial_image_is_closed` — `radialMinSet g p` is closed relative to
  the same closed ball.

* `radial_image_T_contains_rieDist_closedBall` — every `q : M` with
  `riemannianEDist I p q ≤ ENNReal.ofReal R` is reached by some `v` with
  `g`-velocity-norm `≤ R`.

* `expMap_surjective_on_riemannianEDist_closedBall` — combining the previous nodes via
  the preconnected-clopen argument, every `q` at distance `≤ R` is
  reached by a *minimising* radial geodesic of `g`-velocity-norm `≤ R`.

The genuinely-hard nodes (openness relative to the ball; the
containment; the minimising-curve conclusion) carry a single,
clearly-marked `sorry` each, naming the missing geometric content. The
preconnectedness nodes and the relative-closedness node are proven
outright.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace RadialSurjectivity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [PseudoEMetricSpace M] [T2Space (TangentBundle I M)]
variable (g : SmoothRiemannianMetric I M)
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]

/-- The closed `g`-ball of radius `R` in the tangent space `T_p M`:
the set of vectors `v` with `√(g.inner p v v) ≤ R`. -/
def gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    Set (TangentSpace I p) :=
  {v : TangentSpace I p | Real.sqrt (g.inner p v v) ≤ R}

/-- The `g`-quadratic form is homogeneous of degree two:
`g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v`. -/
lemma gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    (b : ℝ) (v : TangentSpace I p) :
    g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v := by
  rw [(g.inner p).map_smul b v, ContinuousLinearMap.smul_apply,
    (g.inner p v).map_smul b v]
  simp only [smul_eq_mul]
  ring

/-- The `g`-norm `√(g.inner p · ·)` is homogeneous: for `0 ≤ b`,
`√(g.inner p (b • v) (b • v)) = b * √(g.inner p v v)`. -/
lemma sqrt_gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    {b : ℝ} (hb : 0 ≤ b) (v : TangentSpace I p) :
    Real.sqrt (g.inner p (b • v) (b • v)) =
      b * Real.sqrt (g.inner p v v) := by
  rw [gInner_smul_self (I := I) g p b v, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq hb]

/-- The zero vector lies in every `g`-closed ball of non-negative radius;
more precisely, its `g`-norm is `0`. -/
lemma zero_mem_gBall (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : 0 ≤ R) : (0 : TangentSpace I p) ∈ gBall (I := I) g p R := by
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) ≤ R
  rw [h0, Real.sqrt_zero]
  exact hR

/-- **The closed `g`-ball is star-shaped about the origin.** Scaling a
ball element by `b ∈ [0, 1]` keeps it inside the ball, since the
`g`-norm scales by `b ≤ 1`. -/
lemma starConvex_gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    StarConvex ℝ (0 : TangentSpace I p) (gBall (I := I) g p R) := by
  intro y hy a b ha hb hab
  have hb_le_one : b ≤ 1 := by linarith
  have hy' : Real.sqrt (g.inner p y y) ≤ R := hy
  have hsqrt_nonneg : 0 ≤ Real.sqrt (g.inner p y y) := Real.sqrt_nonneg _
  change Real.sqrt (g.inner p (a • (0 : TangentSpace I p) + b • y)
      (a • (0 : TangentSpace I p) + b • y)) ≤ R
  rw [smul_zero, zero_add]
  rw [sqrt_gInner_smul_self (I := I) g p hb y]
  calc b * Real.sqrt (g.inner p y y)
      ≤ 1 * Real.sqrt (g.inner p y y) :=
        mul_le_mul_of_nonneg_right hb_le_one hsqrt_nonneg
    _ = Real.sqrt (g.inner p y y) := one_mul _
    _ ≤ R := hy'

/-- **The closed `g`-ball is preconnected.** It is star-shaped about the
origin (`starConvex_gBall`), hence path-connected, hence
preconnected. -/
theorem gBall_isPreconnected (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (gBall (I := I) g p R) :=
  ((starConvex_gBall (I := I) g p R).isPathConnected
    (zero_mem_gBall (I := I) g p hR)).isConnected.isPreconnected

/-- **The radial-minimiser set at `p`.** Points `q : M` reached by some
`v : T_p M` whose minimising radial geodesic has `g`-length equal to the
Riemannian distance `riemannianEDist I p q`. -/
def radialMinSet (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  {q : M | ∃ v : TangentSpace I p,
    expMap (I := I) g p v = q ∧
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q}

/-- The base point `p` belongs to its own radial-minimiser set, witnessed
by the zero vector (`expMap g p 0 = p`, and both the `g`-length and the
Riemannian distance are `0`). -/
theorem p_mem_radialMinSet (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ radialMinSet (I := I) g p := by
  refine ⟨(0 : TangentSpace I p), expMap_zero (I := I) g p, ?_⟩
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  rw [h0, Real.sqrt_zero, ENNReal.ofReal_zero, riemannianEDist_self]

/-- **Preconnectedness of the `expMap g p`-image of the closed `g`-ball.**
The closed `g`-ball `gBall g p R` is preconnected (`gBall_isPreconnected`);
its image under the continuous map `expMap g p`
(`bm_c_expMap_continuous_of_geodesic_complete`) is preconnected. -/
theorem radial_image_T_preconnected (g : SmoothRiemannianMetric I M)
    (p : M) {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected
      ((expMap (I := I) g p) '' (gBall (I := I) g p R)) := by
  have hcont : Continuous (expMap (I := I) g p) :=
    HopfRinow.bm_c_expMap_continuous_of_geodesic_complete (I := I) g p
  exact (gBall_isPreconnected (I := I) g p hR).image _ hcont.continuousOn

/-- **Radial-image openness (relative form).** The radial-minimiser set
`radialMinSet g p` is open *relative to* the `riemannianEDist`-closed-ball
of radius `R` at `p`: its preimage under the subtype inclusion of
`{q | riemannianEDist I p q ≤ ENNReal.ofReal R}` is open. At any witness
point `q = expMap g p v`, openness is propagated by composing the
minimising radial geodesic with a short radial geodesic in a normal-chart
ball at `q`; Gauss's lemma certifies that the composed curve still
realises `riemannianEDist`. -/
theorem radial_image_is_open (g : SmoothRiemannianMetric I M)
    (p : M) (R : ℝ) :
    IsOpen
      (Subtype.val ⁻¹' (radialMinSet (I := I) g p) :
        Set ↥{q : M | riemannianEDist I p q ≤ ENNReal.ofReal R}) := by
  sorry

/-- The `g`-quadratic form `g.inner p v v` is non-negative: it is `0` at the
zero vector and strictly positive elsewhere by positive-definiteness. -/
private lemma gInner_self_nonneg (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : 0 ≤ g.inner p v v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · exact (g.pos p v hv).le

/-- The map `v ↦ g.inner p v v` is continuous on `T_p M`: the metric value
`g.inner p` is a continuous bilinear map and we evaluate it on the diagonal. -/
private lemma continuous_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => g.inner p v v) :=
  (g.inner p).continuous.clm_apply continuous_id

/-- The map `v ↦ √(g.inner p v v)` is continuous on `T_p M`. -/
private lemma continuous_sqrt_gInner_self (g : SmoothRiemannianMetric I M)
    (p : M) :
    Continuous (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) :=
  Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g p)

/-- **The closed `g`-ball is closed.** It is the preimage of `Set.Iic R`
under the continuous map `v ↦ √(g.inner p v v)`. -/
private lemma isClosed_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsClosed (gBall (I := I) g p R) := by
  have hpre : gBall (I := I) g p R =
      (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) ⁻¹' Set.Iic R := by
    ext v; simp only [gBall, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
  rw [hpre]
  exact IsClosed.preimage (continuous_sqrt_gInner_self (I := I) g p) isClosed_Iic

/-- **The closed `g`-ball is bounded.** The von Neumann boundedness of the
unit `g`-ball (`g.isVonNBounded`) gives a model-norm bound on `{v | g v v < 1}`,
and a rescaling argument transports it to the radius-`R` `g`-ball. -/
private lemma isBounded_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : Bornology.IsBounded (gBall (I := I) g p R) := by
  rcases lt_or_ge R 0 with hR | hR
  · have hempty : gBall (I := I) g p R = ∅ := by
      ext v
      simp only [gBall, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hR (Real.sqrt_nonneg _)
    rw [hempty]; exact Bornology.isBounded_empty
  · obtain ⟨r, hr⟩ :=
      (NormedSpace.isVonNBounded_iff' ℝ (E := TangentSpace I p)).1 (g.isVonNBounded p)
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(R + 1) * r, fun v hv => ?_⟩
    have hsqrt : Real.sqrt (g.inner p v v) ≤ R := hv
    have hnonneg : 0 ≤ g.inner p v v := gInner_self_nonneg (I := I) g p v
    have hgvv : g.inner p v v ≤ R ^ 2 := by
      nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (g.inner p v v), hsqrt]
    have hRpos : (0 : ℝ) < R + 1 := by linarith
    set w : TangentSpace I p := (R + 1)⁻¹ • v with hw
    have hgw : g.inner p w w < 1 := by
      have hsmul : g.inner p w w = (R + 1)⁻¹ ^ 2 * g.inner p v v :=
        gInner_smul_self (I := I) g p _ v
      rw [hsmul]
      have hinv_sq_pos : (0 : ℝ) < (R + 1)⁻¹ ^ 2 :=
        pow_pos (inv_pos.mpr hRpos) 2
      have hge : 0 ≤ R / (R + 1) := div_nonneg hR hRpos.le
      have hlt : R / (R + 1) < 1 := by rw [div_lt_one hRpos]; linarith
      calc (R + 1)⁻¹ ^ 2 * g.inner p v v
          ≤ (R + 1)⁻¹ ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left hgvv hinv_sq_pos.le
        _ = (R / (R + 1)) ^ 2 := by
            rw [div_pow]; field_simp
        _ < 1 := by nlinarith [hlt, hge]
    have hwnorm : ‖w‖ ≤ r := hr w hgw
    have hv_eq : v = (R + 1) • w := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hRpos), one_smul]
    rw [hv_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    exact mul_le_mul_of_nonneg_left hwnorm hRpos.le

/-- **The closed `g`-ball is compact.** In the finite-dimensional (hence
proper) tangent space `T_p M`, a closed and bounded set is compact. -/
private lemma isCompact_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsCompact (gBall (I := I) g p R) := by
  haveI : ProperSpace (TangentSpace I p) := FiniteDimensional.proper_real (TangentSpace I p)
  exact Metric.isCompact_of_isClosed_isBounded
    (isClosed_gBall (I := I) g p R) (isBounded_gBall (I := I) g p R)

/-- Continuity of `q ↦ riemannianEDist I p q` for the manifold topology.

The ambient `[PseudoEMetricSpace M]` variable carries a topology that is
*not* assumed equal to the manifold topology, so continuity of `edist` for
that structure does not transfer. Instead we build, from the ambient
`RiemannianBundle` data (whose fibre inner product varies continuously by
`[IsContinuousRiemannianBundle E (TangentSpace I)]`), Mathlib's canonical
`PseudoEMetricSpace.ofRiemannianMetric I M`, whose `edist` is
`riemannianEDist I` definitionally and whose topology is definitionally the
manifold topology (it is constructed via `PseudoEMetricSpace.ofEDistOfTopology`,
which sets `toTopologicalSpace := t` to the ambient one). Continuity of
`edist` (`Continuous.edist`) for this structure is therefore continuity of
`riemannianEDist I` for the manifold topology. The fibre norm feeding
`riemannianEDist` is the one induced by the ambient `RiemannianBundle`, which
is exactly the one appearing in the goal. The required `[RegularSpace M]` is
discharged from finite-dimensional local compactness together with the
Hausdorff hypothesis. -/
private lemma continuous_riemannianEDist_ambient
    (p : M) : Continuous (fun q : M => riemannianEDist I p q) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_const.edist continuous_id)

/-- **Radial-image closedness (relative form).** The radial-minimiser set
`radialMinSet g p` is closed *relative to* the `riemannianEDist`-closed-ball
of radius `R` at `p`. The intersection `radialMinSet g p ∩ closedBall` is the
`expMap g p`-image of the compact locus `A`: the vectors in the compactifying
closed `g`-ball of radius `max R 0` that realise `riemannianEDist` and whose
endpoint lies in the closed ball. `A` is the intersection of the compact closed
`g`-ball with an equalizer of two continuous maps and a closed sublevel set,
hence compact; its image is compact and therefore closed in the Hausdorff
manifold, and pulling back along the closed-ball subtype inclusion yields the
relative closedness. The velocity bound is the intrinsic `g`-norm
`√(g.inner p v v)`, not the model-`E` norm. -/
theorem radial_image_is_closed (g : SmoothRiemannianMetric I M)
    (p : M) (R : ℝ) :
    IsClosed
      (Subtype.val ⁻¹' (radialMinSet (I := I) g p) :
        Set ↥{q : M | riemannianEDist I p q ≤ ENNReal.ofReal R}) := by
  have hexp : Continuous (expMap (I := I) g p) :=
    HopfRinow.bm_c_expMap_continuous_of_geodesic_complete (I := I) g p
  have hf : Continuous
      (fun v : TangentSpace I p =>
        ENNReal.ofReal (Real.sqrt (g.inner p v v))) :=
    ENNReal.continuous_ofReal.comp (continuous_sqrt_gInner_self (I := I) g p)
  have hh : Continuous
      (fun v : TangentSpace I p =>
        riemannianEDist I p (expMap (I := I) g p v)) :=
    (continuous_riemannianEDist_ambient (I := I) p).comp hexp
  set A : Set (TangentSpace I p) :=
    {v : TangentSpace I p |
      v ∈ gBall (I := I) g p (max R 0) ∧
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) =
        riemannianEDist I p (expMap (I := I) g p v) ∧
      riemannianEDist I p (expMap (I := I) g p v) ≤ ENNReal.ofReal R} with hA
  have hAclosed : IsClosed A := by
    have heq : IsClosed
        {v : TangentSpace I p |
          ENNReal.ofReal (Real.sqrt (g.inner p v v)) =
            riemannianEDist I p (expMap (I := I) g p v)} :=
      isClosed_eq hf hh
    have hlev : IsClosed
        {v : TangentSpace I p |
          riemannianEDist I p (expMap (I := I) g p v) ≤ ENNReal.ofReal R} :=
      IsClosed.preimage hh isClosed_Iic
    have hsplit : A =
        gBall (I := I) g p (max R 0) ∩
          ({v : TangentSpace I p |
              ENNReal.ofReal (Real.sqrt (g.inner p v v)) =
                riemannianEDist I p (expMap (I := I) g p v)} ∩
            {v : TangentSpace I p |
              riemannianEDist I p (expMap (I := I) g p v) ≤
                ENNReal.ofReal R}) := by
      ext v; simp only [hA, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hsplit]
    exact (isClosed_gBall (I := I) g p (max R 0)).inter (heq.inter hlev)
  have hAcompact : IsCompact A :=
    (isCompact_gBall (I := I) g p (max R 0)).of_isClosed_subset hAclosed
      (fun v hv => hv.1)
  have hImageClosed : IsClosed (expMap (I := I) g p '' A) :=
    (hAcompact.image hexp).isClosed
  have hpreimage_eq :
      (Subtype.val ⁻¹' (radialMinSet (I := I) g p) :
        Set ↥{q : M | riemannianEDist I p q ≤ ENNReal.ofReal R}) =
      Subtype.val ⁻¹' (expMap (I := I) g p '' A) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨v, hexpv, hlen⟩
      have hxball : riemannianEDist I p x.val ≤ ENNReal.ofReal R := x.2
      have hlen' : ENNReal.ofReal (Real.sqrt (g.inner p v v)) =
          riemannianEDist I p (expMap (I := I) g p v) := by
        rw [hexpv]; exact hlen
      have hconstr : riemannianEDist I p (expMap (I := I) g p v) ≤
          ENNReal.ofReal R := by rw [hexpv]; exact hxball
      have hle : ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
          ENNReal.ofReal R := by rw [hlen']; exact hconstr
      have hvmax : Real.sqrt (g.inner p v v) ≤ max R 0 := by
        rcases (ENNReal.ofReal_le_ofReal_iff' (p := Real.sqrt (g.inner p v v))
          (q := R)).1 hle with h | h
        · exact le_trans h (le_max_left R 0)
        · exact le_trans h (le_max_right R 0)
      exact ⟨v, ⟨hvmax, hlen', hconstr⟩, hexpv⟩
    · rintro ⟨v, ⟨_hvmax, hlen', _hconstr⟩, hexpv⟩
      have hrie : riemannianEDist I p x.val =
          ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
        rw [← hexpv, hlen']
      exact ⟨v, hexpv, by rw [hrie]⟩
  rw [hpreimage_eq]
  exact hImageClosed.preimage continuous_subtype_val

/-- **The rieDist-closed-ball is contained in the radial image.** For
every `q : M` with `riemannianEDist I p q ≤ ENNReal.ofReal R`, there is a
`v : T_p M` with `expMap g p v = q` and `g`-velocity-norm
`√(g.inner p v v) ≤ R`. The proof decomposes a `riemannianEDist`-quasi-
minimising path `p → q` of length `≤ R + ε` along a Lebesgue-cover of
`[0,1]` into short segments inside normal charts; Gauss's lemma identifies
each segment with a radial geodesic in normal coordinates, and uniqueness
on overlaps glues the radial pieces into a single radial geodesic with
`g`-velocity-norm `≤ R + ε`. Sending `ε → 0` and applying
`radial_image_is_closed` lands the velocity exactly inside the closed
`g`-ball of radius `R`. -/
theorem radial_image_T_contains_rieDist_closedBall
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    ∀ q : M, riemannianEDist I p q ≤ ENNReal.ofReal R →
      ∃ v : TangentSpace I p,
        expMap (I := I) g p v = q ∧
          Real.sqrt (g.inner p v v) ≤ R := by
  sorry

/-- **Surjectivity of `expMap g p` onto the `riemannianEDist`-closed ball.**
For every `q : M` with `riemannianEDist I p q ≤ ENNReal.ofReal R` there is a
`v : T_p M` with `expMap g p v = q`, intrinsic `g`-velocity-norm
`√(g.inner p v v) ≤ R`, and `ENNReal.ofReal (√(g.inner p v v)) =`
`riemannianEDist I p q`, i.e. the radial geodesic `t ↦ expMap g p (t • v)`
minimises and realises the Riemannian distance from `p` to `q`. This is the
Hopf–Rinow exponential-surjectivity / minimising-geodesic-existence statement
on the closed ball of radius `R`.

The argument runs the preconnected-clopen step inside the `expMap g p`-image
`T := expMap g p '' gBall g p R`. `T` is preconnected
(`radial_image_T_preconnected`); the minimising-radial subset
`radialMinSet g p ∩ T` is open in `T` (`radial_image_is_open`) and closed in
`T` (`radial_image_is_closed`), and contains `p` (via the zero vector,
`p_mem_radialMinSet`); hence `radialMinSet g p ∩ T = T`. The containment
`{q | riemannianEDist I p q ≤ ENNReal.ofReal R} ⊆ T` is supplied by
`radial_image_T_contains_rieDist_closedBall`. -/
theorem expMap_surjective_on_riemannianEDist_closedBall
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    ∀ q : M, riemannianEDist I p q ≤ ENNReal.ofReal R →
      ∃ v : TangentSpace I p,
        expMap (I := I) g p v = q ∧
          Real.sqrt (g.inner p v v) ≤ R ∧
          ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q := by
  sorry

end RadialSurjectivity
end Riemannian
end Geometry
end DifferentialGeometry

end
