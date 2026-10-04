import DifferentialGeometry.Geometry.Comparison.RayChord
import DifferentialGeometry.Geometry.Comparison.RayDensity
import DifferentialGeometry.Geometry.Metric.RadialConeQuotient
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import DifferentialGeometry.Topology.MetricSpace.PseudometricLimit
import DifferentialGeometry.Topology.MetricSpace.ProperRadialImage

/-!
# The ray cone of a space with nonnegative four-point comparison

Tier T3 ("RayCone") of the Tits-cone producer of chapter 13, part (i): the cone built from rays,
design `docs/geometrization/chapter13/design-tits-cone-20261004.md` §2 ("Cone") and §4, the metric
form of the blueprint's LFR57 (`docs/geometrization/blueprint/master207A.tex:29600–29926`).

Let `Y` satisfy `fourPointComparison 0 univ` and fix `q : Y`. A point of the carrier
`RayConeCarrier q` is a ray `γ` from `q` (a map `ℝ≥0 → Y` with `Isometry γ ∧ γ 0 = q`) together with
a radius `a : ℝ≥0`. The cone distance is the cosine law at infinity of tier T1
(`GC.MetricGeometry.tendsto_dist_mul_div_of_ray`):
`rayConeDist ((γ, a), (σ, b)) = √((a - b)² + a b ρ∞(γ, σ)²)`, `ρ∞ = rayChordLimit`.

* `rayConePseudoMetric`: `rayConeDist` is a pseudometric, obtained from the existing constructor
  `PseudoMetricSpace.ofPointwiseDistLimit` as the pointwise limit of the pullbacks
  `rayConeApprox q n` of the rescaled spaces `((n + 1)⁻¹ Y)` under `(γ, a) ↦ γ (a (n + 1))`.
* `RayCone hcomp q`: its separation quotient, a metric space (Mathlib's
  `SeparationQuotient.instMetricSpace`).
* `rayConeRadialData`: AC82 radial data on `RayCone hcomp q` at the apex, through the existing
  constructor `radialConeDataSeparationQuotient`, with `H_t (γ, a) = (γ, t a)` for `t ≠ 0` and
  `H_0` the apex representative itself (the constructor needs `H 0 x = p` on the nose).
* `rayConeDist_mk_mul_le`: the cone distance of the points at radii `c s`, `c u` never exceeds
  `c · d(γ s, σ u)` (T1's I4 in scaled form). Consequently two rays through the same point give the
  same cone point (`RayCone.mk_eq_mk_of_eq`).

* `rayConeProj hcomp c`: the radial projection `x ↦ [(γ_x, c |qx|)]` of the ray union
  `rayUnion q` (the union of the rays from `q`) onto the cone, `γ_x` a ray through `x`. It is
  `c`-Lipschitz, radial, and onto (`rayConeProj_mk_of_ray`).
* `properSpace_rayCone`: the cone is proper, as the radial image of the ray union, which is proper
  because it is closed (tier T2's I7 `isClosed_rayUnion`) — the existing
  `ProperSpace.of_surjective_dist_basepoint_eq`.

The Kleiner–Lott maps use tier T2's density (I5) and error budget and live in
`DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinity`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

variable {Y : Type u} [mY : MetricSpace Y]

/-- A point of the ray cone over `q`: a ray from `q` and a radius. A structure (not a product) so
that no product uniformity competes with the cone metric. -/
structure RayConeCarrier (q : Y) : Type u where
  /-- The ray, a map `ℝ≥0 → Y`. -/
  ray : ℝ≥0 → Y
  /-- The map is a ray from `q`. -/
  isRay : Isometry ray ∧ ray 0 = q
  /-- The radius. -/
  radius : ℝ≥0

/-- The cone distance: the limit chord `√((a - b)² + a b ρ∞²)` of tier T1 (LFR56 with
`2 - 2 cos θ∞ = ρ∞²`). -/
def rayConeDist (q : Y) (z w : RayConeCarrier q) : ℝ :=
  Real.sqrt (((z.radius : ℝ) - w.radius) ^ 2 +
    z.radius * w.radius * rayChordLimit z.ray w.ray ^ 2)

theorem rayConeDist_nonneg (q : Y) (z w : RayConeCarrier q) : 0 ≤ rayConeDist q z w :=
  Real.sqrt_nonneg _

theorem rayConeDist_sq (q : Y) (z w : RayConeCarrier q) :
    rayConeDist q z w ^ 2 = ((z.radius : ℝ) - w.radius) ^ 2 +
      z.radius * w.radius * rayChordLimit z.ray w.ray ^ 2 := by
  apply Real.sq_sqrt
  have h1 : (0 : ℝ) ≤ z.radius := NNReal.coe_nonneg _
  have h2 : (0 : ℝ) ≤ w.radius := NNReal.coe_nonneg _
  positivity

/-- The cone distance from a radius-zero point is the radius. -/
theorem rayConeDist_zero_left (q : Y) (z w : RayConeCarrier q) (hz : z.radius = 0) :
    rayConeDist q z w = w.radius := by
  rw [rayConeDist, hz, NNReal.coe_zero, zero_sub, zero_mul, zero_mul, add_zero, neg_sq,
    Real.sqrt_sq (NNReal.coe_nonneg _)]

/-- The cone distance to a radius-zero point is the radius. -/
theorem rayConeDist_zero_right (q : Y) (z w : RayConeCarrier q) (hw : w.radius = 0) :
    rayConeDist q z w = z.radius := by
  rw [rayConeDist, hw, NNReal.coe_zero, sub_zero, mul_zero, zero_mul, add_zero,
    Real.sqrt_sq (NNReal.coe_nonneg _)]

/-- The rescaled pullback pseudometrics: `(γ, a) ↦ γ (a (n + 1))` into `((n + 1)⁻¹ Y)`. -/
@[instance_reducible]
def rayConeApprox (q : Y) (n : ℕ) : PseudoMetricSpace (RayConeCarrier q) :=
  PseudoMetricSpace.induced (fun z : RayConeCarrier q => z.ray (z.radius * ((n : ℝ≥0) + 1)))
    (mY.rescale ((n : ℝ) + 1)⁻¹ (by positivity)).toPseudoMetricSpace

theorem rayConeApprox_dist (q : Y) (n : ℕ) (z w : RayConeCarrier q) :
    @dist _ (rayConeApprox q n).toDist z w =
      dist (z.ray (z.radius * ((n : ℝ≥0) + 1))) (w.ray (w.radius * ((n : ℝ≥0) + 1))) /
        ((n : ℝ) + 1) := by
  rw [div_eq_inv_mul]
  rfl

/-- I3 in the form `PseudoMetricSpace.ofPointwiseDistLimit` consumes. -/
theorem tendsto_rayConeApprox_dist (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y)
    (z w : RayConeCarrier q) :
    Tendsto (fun n : ℕ => @dist _ (rayConeApprox q n).toDist z w) atTop
      (𝓝 (rayConeDist q z w)) := by
  have h := tendsto_dist_mul_div_of_ray hcomp z.isRay w.isRay z.radius w.radius
  have hn : Tendsto (fun n : ℕ => (n : ℝ≥0) + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_self_add) tendsto_natCast_atTop_atTop
  have hfun : (fun n : ℕ => @dist _ (rayConeApprox q n).toDist z w) =
      (fun t : ℝ≥0 => dist (z.ray (z.radius * t)) (w.ray (w.radius * t)) / (t : ℝ)) ∘
        (fun n : ℕ => (n : ℝ≥0) + 1) := by
    funext n
    rw [rayConeApprox_dist, Function.comp_apply, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one]
  rw [hfun]
  exact h.comp hn

/-- The cone pseudometric on the carrier: the existing pointwise-limit constructor applied to the
rescaled pullbacks; its distance is `rayConeDist` by definition. -/
@[instance_reducible]
def rayConePseudoMetric (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) :
    PseudoMetricSpace (RayConeCarrier q) :=
  PseudoMetricSpace.ofPointwiseDistLimit (rayConeApprox q) (rayConeDist q)
    (tendsto_rayConeApprox_dist hcomp q)

/-- The ray cone: the separation quotient of the carrier under the cone pseudometric. -/
def RayCone (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) : Type u :=
  @SeparationQuotient (RayConeCarrier q) (rayConePseudoMetric hcomp q).toUniformSpace.toTopologicalSpace

instance instMetricSpaceRayCone (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) :
    MetricSpace (RayCone hcomp q) :=
  @SeparationQuotient.instMetricSpace _ (rayConePseudoMetric hcomp q)

/-- The class of a carrier point in the ray cone. -/
def RayCone.mk (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y} (z : RayConeCarrier q) :
    RayCone hcomp q :=
  @SeparationQuotient.mk _ (rayConePseudoMetric hcomp q).toUniformSpace.toTopologicalSpace z

theorem RayCone.dist_mk (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    (z w : RayConeCarrier q) :
    dist (RayCone.mk hcomp z) (RayCone.mk hcomp w) = rayConeDist q z w :=
  rfl

theorem RayCone.surjective_mk (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) :
    Function.Surjective (RayCone.mk hcomp (q := q)) :=
  @SeparationQuotient.surjective_mk _ (rayConePseudoMetric hcomp q).toUniformSpace.toTopologicalSpace

theorem RayCone.mk_eq_mk_iff (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    {z w : RayConeCarrier q} :
    RayCone.mk hcomp z = RayCone.mk hcomp w ↔ rayConeDist q z w = 0 := by
  rw [← RayCone.dist_mk hcomp z w]
  exact dist_eq_zero.symm

/-! ## Comparison with `Y` (T1's I4, scaled) -/

/-- The cone distance of the points at radii `c s` and `c u` is at most `c · d(γ s, σ u)`. -/
theorem rayConeDist_mk_mul_le (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q) (c s u : ℝ≥0) :
    rayConeDist q ⟨γ, hγ, c * s⟩ ⟨σ, hσ, c * u⟩ ≤ c * dist (γ s) (σ u) := by
  rw [rayConeDist, sqrt_rayChord_mul_left]
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg c)
  calc Real.sqrt (((s : ℝ) - u) ^ 2 + s * u * rayChordLimit γ σ ^ 2)
      ≤ Real.sqrt (dist (γ s) (σ u) ^ 2) :=
        Real.sqrt_le_sqrt (sub_sq_add_mul_rayChordLimit_sq_le_dist_sq hcomp hγ hσ s u)
    _ = dist (γ s) (σ u) := Real.sqrt_sq dist_nonneg

/-- Two rays through the same point at the same radius give the same cone point, at every
scale. -/
theorem RayCone.mk_eq_mk_of_eq (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q) (c s : ℝ≥0)
    (h : γ s = σ s) :
    RayCone.mk hcomp ⟨γ, hγ, c * s⟩ = RayCone.mk hcomp ⟨σ, hσ, c * s⟩ := by
  rw [RayCone.mk_eq_mk_iff]
  apply le_antisymm _ (rayConeDist_nonneg _ _ _)
  simpa only [h, dist_self, mul_zero] using rayConeDist_mk_mul_le hcomp hγ hσ c s s

/-! ## The apex and AC82 -/

/-- The apex of the ray cone, represented by any ray at radius `0`. -/
def rayConeApex (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y} {γ₀ : ℝ≥0 → Y}
    (hγ₀ : Isometry γ₀ ∧ γ₀ 0 = q) : RayCone hcomp q :=
  RayCone.mk hcomp ⟨γ₀, hγ₀, 0⟩

/-- The apex does not depend on the representing ray. -/
theorem rayConeApex_eq (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    {γ₀ σ : ℝ≥0 → Y} (hγ₀ : Isometry γ₀ ∧ γ₀ 0 = q) (hσ : Isometry σ ∧ σ 0 = q) :
    rayConeApex hcomp hγ₀ = rayConeApex hcomp hσ := by
  rw [rayConeApex, rayConeApex, RayCone.mk_eq_mk_iff, rayConeDist_zero_left q _ _ rfl]
  rfl

/-- The distance from the apex is the radius. -/
theorem dist_rayConeApex_mk (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    {γ₀ : ℝ≥0 → Y} (hγ₀ : Isometry γ₀ ∧ γ₀ 0 = q) (z : RayConeCarrier q) :
    dist (rayConeApex hcomp hγ₀) (RayCone.mk hcomp z) = z.radius := by
  rw [rayConeApex, RayCone.dist_mk, rayConeDist_zero_left q _ _ rfl]

/-- The radial maps on the carrier: `(γ, a) ↦ (γ, t a)` for `t ≠ 0`, and the apex
representative `(γ₀, 0)` for `t = 0`. -/
def rayConeRadialMap {q : Y} (z₀ : RayConeCarrier q) (t : ℝ≥0) (z : RayConeCarrier q) :
    RayConeCarrier q :=
  if t = 0 then ⟨z₀.ray, z₀.isRay, 0⟩ else ⟨z.ray, z.isRay, t * z.radius⟩

theorem rayConeRadialMap_sq (q : Y) (z₀ : RayConeCarrier q) (s t : ℝ≥0) (x y : RayConeCarrier q) :
    rayConeDist q (rayConeRadialMap z₀ s x) (rayConeRadialMap z₀ t y) ^ 2 =
      (s : ℝ) ^ 2 * rayConeDist q ⟨z₀.ray, z₀.isRay, 0⟩ x ^ 2 +
        (t : ℝ) ^ 2 * rayConeDist q ⟨z₀.ray, z₀.isRay, 0⟩ y ^ 2 -
        (s : ℝ) * (t : ℝ) * (rayConeDist q ⟨z₀.ray, z₀.isRay, 0⟩ x ^ 2 +
          rayConeDist q ⟨z₀.ray, z₀.isRay, 0⟩ y ^ 2 - rayConeDist q x y ^ 2) := by
  unfold rayConeRadialMap
  simp only [rayConeDist_sq]
  by_cases hs : s = 0 <;> by_cases ht : t = 0 <;>
    simp only [hs, ht, ite_true, ite_false, NNReal.coe_zero, NNReal.coe_mul] <;> ring

/-- AC82 radial data on the ray cone at its apex, through the existing constructor
`radialConeDataSeparationQuotient`. -/
def rayConeRadialData (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y} {γ₀ : ℝ≥0 → Y}
    (hγ₀ : Isometry γ₀ ∧ γ₀ 0 = q) : RadialConeData (rayConeApex hcomp hγ₀) :=
  @radialConeDataSeparationQuotient _ (rayConePseudoMetric hcomp q) ⟨γ₀, hγ₀, 0⟩
    (rayConeRadialMap ⟨γ₀, hγ₀, 0⟩)
    (fun z => by simp [rayConeRadialMap])
    (fun z => by simp [rayConeRadialMap])
    (fun s t x y => rayConeRadialMap_sq q ⟨γ₀, hγ₀, 0⟩ s t x y)

/-- The radial map of the ray cone on classes: `t · [(γ, a)] = [(γ, t a)]` for `t ≠ 0`. -/
theorem rayConeRadialData_map_mk (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    {γ₀ : ℝ≥0 → Y} (hγ₀ : Isometry γ₀ ∧ γ₀ 0 = q) {t : ℝ≥0} (ht : t ≠ 0)
    (z : RayConeCarrier q) :
    (rayConeRadialData hcomp hγ₀).map t (RayCone.mk hcomp z) =
      RayCone.mk hcomp ⟨z.ray, z.isRay, t * z.radius⟩ := by
  change RayCone.mk hcomp (rayConeRadialMap ⟨γ₀, hγ₀, 0⟩ t z) = _
  rw [rayConeRadialMap, ite_eq_right_iff.mpr (fun h => absurd h ht)]

/-! ## The radial projection of the ray union and properness -/

/-- The union of the rays from `q` (closed in a proper space: T2's `isClosed_rayUnion`). -/
def rayUnion (q : Y) : Set Y :=
  {x : Y | ∃ γ : ℝ≥0 → Y, (Isometry γ ∧ γ 0 = q) ∧ x ∈ range γ}

theorem mem_rayUnion {q : Y} {γ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (t : ℝ≥0) :
    γ t ∈ rayUnion q :=
  ⟨γ, hγ, t, rfl⟩

/-- A point of the ray union lies on some ray at its own radius. -/
theorem exists_ray_apply_dist_eq {q x : Y} (hx : x ∈ rayUnion q) :
    ∃ γ : ℝ≥0 → Y, (Isometry γ ∧ γ 0 = q) ∧ γ ⟨dist q x, dist_nonneg⟩ = x := by
  obtain ⟨γ, hγ, t, rfl⟩ := hx
  exact ⟨γ, hγ, congrArg γ (NNReal.eq (dist_of_ray hγ t))⟩

/-- A chosen ray through a point of the ray union. -/
def rayThrough {q : Y} (x : rayUnion q) : ℝ≥0 → Y :=
  (exists_ray_apply_dist_eq x.2).choose

theorem rayThrough_isRay {q : Y} (x : rayUnion q) :
    Isometry (rayThrough x) ∧ rayThrough x 0 = q :=
  (exists_ray_apply_dist_eq x.2).choose_spec.1

theorem rayThrough_apply {q : Y} (x : rayUnion q) :
    rayThrough x ⟨dist q x, dist_nonneg⟩ = x :=
  (exists_ray_apply_dist_eq x.2).choose_spec.2

/-- The radial projection at scale `c`: `x ↦ [(γ_x, c |qx|)]`. -/
def rayConeProj (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y} (c : ℝ≥0)
    (x : rayUnion q) : RayCone hcomp q :=
  RayCone.mk hcomp ⟨rayThrough x, rayThrough_isRay x, c * ⟨dist q x, dist_nonneg⟩⟩

/-- The projection is `c`-Lipschitz (T1's I4). -/
theorem dist_rayConeProj_le (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y} (c : ℝ≥0)
    (x y : rayUnion q) :
    dist (rayConeProj hcomp c x) (rayConeProj hcomp c y) ≤ c * dist x y := by
  have h := rayConeDist_mk_mul_le hcomp (rayThrough_isRay x) (rayThrough_isRay y) c
    ⟨dist q x, dist_nonneg⟩ ⟨dist q y, dist_nonneg⟩
  rw [rayThrough_apply, rayThrough_apply] at h
  exact h

/-- The projection in terms of the limit chord of the chosen rays. -/
theorem dist_rayConeProj_eq (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y} (c : ℝ≥0)
    (x y : rayUnion q) :
    dist (rayConeProj hcomp c x) (rayConeProj hcomp c y) =
      c * Real.sqrt ((dist q (x : Y) - dist q (y : Y)) ^ 2 +
        dist q (x : Y) * dist q (y : Y) * rayChordLimit (rayThrough x) (rayThrough y) ^ 2) := by
  rw [rayConeProj, rayConeProj, RayCone.dist_mk, rayConeDist]
  exact sqrt_rayChord_mul_left _ ⟨dist q x, dist_nonneg⟩ ⟨dist q y, dist_nonneg⟩ c

/-- The projection of a radius-zero cone point: distances to it are radii. -/
theorem dist_rayConeProj_mk_zero (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    (c : ℝ≥0) (x : rayUnion q) {σ : ℝ≥0 → Y} (hσ : Isometry σ ∧ σ 0 = q) :
    dist (rayConeProj hcomp c x) (RayCone.mk hcomp ⟨σ, hσ, 0⟩) = c * dist q (x : Y) := by
  rw [rayConeProj, RayCone.dist_mk, rayConeDist_zero_right q _ _ rfl]
  rfl

/-- The projection of a point on a ray `σ` at radius `s` is the class of `(σ, c s)`. -/
theorem rayConeProj_mk_of_ray (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    (c : ℝ≥0) {σ : ℝ≥0 → Y} (hσ : Isometry σ ∧ σ 0 = q) (s : ℝ≥0) :
    rayConeProj hcomp c ⟨σ s, mem_rayUnion hσ s⟩ = RayCone.mk hcomp ⟨σ, hσ, c * s⟩ := by
  have hs : (⟨dist q (σ s), dist_nonneg⟩ : ℝ≥0) = s := NNReal.eq (dist_of_ray hσ s)
  have happ := rayThrough_apply (q := q) ⟨σ s, mem_rayUnion hσ s⟩
  simp only [hs] at happ
  rw [rayConeProj]
  simp only [hs]
  exact RayCone.mk_eq_mk_of_eq hcomp _ hσ c s happ

/-- The ray cone is proper: it is the radial image of the ray union, which is proper because it
is closed (T2's I7). Without rays the cone is empty. -/
theorem properSpace_rayCone (hcomp : fourPointComparison 0 (univ : Set Y)) [ProperSpace Y]
    (q : Y) : ProperSpace (RayCone hcomp q) := by
  by_cases hray : ∃ γ : ℝ≥0 → Y, Isometry γ ∧ γ 0 = q
  · obtain ⟨γ₀, hγ₀⟩ := hray
    have : ProperSpace (rayUnion q) := ProperSpace.of_isClosed (isClosed_rayUnion q)
    let p : rayUnion q := ⟨γ₀ 0, mem_rayUnion hγ₀ 0⟩
    have hp : (p : Y) = q := hγ₀.2
    have hpmk : rayConeProj hcomp 1 p = RayCone.mk hcomp ⟨γ₀, hγ₀, 0⟩ := by
      rw [rayConeProj_mk_of_ray, mul_zero]
    refine ProperSpace.of_surjective_dist_basepoint_eq (rayConeProj hcomp 1)
      ((LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous) ?_ p fun x => ?_
    · simpa only [NNReal.coe_one, one_mul] using dist_rayConeProj_le hcomp 1 x y
    · intro z
      obtain ⟨⟨σ, hσ, b⟩, rfl⟩ := RayCone.surjective_mk hcomp q z
      refine ⟨⟨σ b, mem_rayUnion hσ b⟩, ?_⟩
      rw [rayConeProj_mk_of_ray, one_mul]
    · rw [hpmk, dist_rayConeProj_mk_zero, NNReal.coe_one, one_mul, Subtype.dist_eq, hp,
        dist_comm]
  · have : IsEmpty (RayCone hcomp q) := by
      refine ⟨fun z => ?_⟩
      obtain ⟨⟨σ, hσ, b⟩, -⟩ := RayCone.surjective_mk hcomp q z
      exact hray ⟨σ, hσ⟩
    infer_instance

end GC.MetricGeometry
