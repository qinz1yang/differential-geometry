import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Exponential.IntrinsicExpContinuity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval

set_option linter.unusedSectionVars false

/-!
# Geodesic convexity and the good-cover property

This file develops the *structural* side of geodesic (Whitehead) convexity:
the part that is purely topological once a minimising-geodesic selector is
available, together with the **radial confinement** core that is provable
directly from the intrinsic geodesic's constant-speed length bound.

A subset `S` of a manifold is **geodesically convex with respect to a joining
map** `join : M → M → ℝ → M` when, for every pair of points `a b ∈ S`, the
curve `t ↦ join a b t` stays inside `S` for `t ∈ [0,1]`, starts at `a`, ends at
`b`, and is continuous on `[0,1]`. The map `join` is meant to select *the*
minimising geodesic between two nearby points; on a Riemannian manifold this
selector exists and is continuous on a small enough region (the genuine
Whitehead content, the two-point side of which is supplied elsewhere).

## Topological facts (no further Riemannian input)

* `IsGeodesicallyConvexWith.joinedIn` — a geodesically convex set is internally
  path-connected: any two of its points are joined by a path inside it.
* `IsGeodesicallyConvexWith.inter` — the intersection of two sets that are
  geodesically convex **for the same joining map** is again geodesically convex
  for that map.

## The radial confinement core (genuine Riemannian content)

Let `γ_v(t) := intrinsicGeodesic g hEnorm p v t` be the complete moving-foot
geodesic through `p` with launch velocity `v`.  Its squared `g`-speed is constant
and equal to the launch value `g_p(v, v)` (`isGeodesicOn_speedSq_const` at the
launch time), so its velocity enorm is everywhere `≤ √(g_p(v, v))` and the path
length over `[0, t]` is `≤ √(g_p(v, v)) · t`.  Combined with
`riemannianEDist_le_pathELength` this gives the **radial length bound**

`riemannianEDist I p (γ_v t) ≤ ENNReal.ofReal (√(g_p(v, v)) · t)`  for `0 ≤ t`,

from which the **radial confinement** follows: the radial geodesic to a point at
`g_p`-radius `< ρ` stays inside the intrinsic-distance ball `smallNormalBall g p ρ`.
This is the star-shapedness of the small ball about its centre, established here as
`smallNormalBall_radial_confined`, and packaged as `joinedIn_centre_smallNormalBall`
(every ball point is joined to the centre by a path inside the ball).

## What remains for full two-point Whitehead convexity

The velocity-identified Hopf–Rinow theorem is now packaged below as the
two-point selector `minJoin`, with its endpoint, continuity, and minimizing
length facts.  The remaining analytic input is the positive Hessian comparison
`0 < ∇² (½ d(p, ·)²)` on the controlled ball.  Its along-`minJoin` consequence
must both confine the selected curve and give the strict convexity used by the
center-of-mass construction.  Existing second-variation nonnegativity alone
does not provide that uniform positive lower bound.
-/

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

/-- **Geodesic convexity with respect to a joining map.**

`IsGeodesicallyConvexWith join S` says that for any two points `a b ∈ S` the
curve `t ↦ join a b t` is a continuous curve on the unit interval, starts at
`a`, ends at `b`, and stays inside `S`.

The map `join` is an external datum (a minimising-geodesic selector). Phrasing
convexity relative to a *fixed* `join` is what makes convexity closed under
intersection: two sets convex for the *same* selector have a convex
intersection, because the single joining curve between two shared points is
forced to lie in both.

This is a genuine convexity predicate, not a restatement of any downstream
conclusion: it constrains the set `S` through the externally given geometric
datum `join`, exactly as ordinary convexity constrains a set through the
externally given affine segment map. -/
def IsGeodesicallyConvexWith {M : Type*} [TopologicalSpace M]
    (join : M → M → ℝ → M) (S : Set M) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    ContinuousOn (join a b) unitInterval ∧ join a b 0 = a ∧ join a b 1 = b ∧
      (∀ t ∈ unitInterval, join a b t ∈ S)

namespace IsGeodesicallyConvexWith

variable {M : Type*} [TopologicalSpace M] {join : M → M → ℝ → M} {S T : Set M}

/-- A geodesically convex set is internally path-connected: any two of its
points are joined by a path that never leaves the set. -/
theorem joinedIn (hS : IsGeodesicallyConvexWith join S) {a b : M}
    (ha : a ∈ S) (hb : b ∈ S) : JoinedIn S a b := by
  obtain ⟨hcont, h0, h1, hmem⟩ := hS a ha b hb
  refine JoinedIn.ofLine hcont h0 h1 ?_
  rintro x ⟨t, ht, rfl⟩
  exact hmem t ht

/-- The intersection of two sets that are geodesically convex **for the same
joining map** is geodesically convex for that map.

The joining curve `t ↦ join a b t` between two points `a b ∈ S ∩ T` is the
*same* curve whether viewed through `S`'s convexity or `T`'s convexity (the
selector `join` is shared); convexity of `S` keeps it in `S`, convexity of `T`
keeps it in `T`, hence it stays in `S ∩ T`. -/
theorem inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) :
    IsGeodesicallyConvexWith join (S ∩ T) := by
  rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩
  obtain ⟨hcontS, h0, h1, hmemS⟩ := hS a haS b hbS
  obtain ⟨_, _, _, hmemT⟩ := hT a haT b hbT
  exact ⟨hcontS, h0, h1, fun t ht => ⟨hmemS t ht, hmemT t ht⟩⟩

/-- **Good-cover step.** If `S` and `T` are geodesically convex for a common
joining map, then any two points common to both are joined by a path lying
inside the intersection `S ∩ T`. This is precisely the pairwise-intersection
condition required of a good cover. -/
theorem joinedIn_inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) {a b : M}
    (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T) :
    JoinedIn (S ∩ T) a b :=
  (hS.inter hT).joinedIn ⟨haS, haT⟩ ⟨hbS, hbT⟩

end IsGeodesicallyConvexWith

section IntrinsicBall

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **The small normal ball of radius `ρ` about `p`.** The open intrinsic
Riemannian-distance ball: the set of points within `riemannianEDist` strictly
less than `ρ` of the centre `p`.

On a complete manifold and for `ρ ≤ expRadiusGp g p` this set agrees with the
`expMapIntrinsic`-image of the open `g_p`-ball of radius `ρ` in `T_p M` (each
such point is reached by a unique minimising radial geodesic of `g`-length
`< ρ`).  The intrinsic distance phrasing is the diamond-free one: it avoids the
ambient fibre-norm and refers only to the Riemannian metric `g` through
`riemannianEDist`. -/
def smallNormalBall (p : M) (ρ : ℝ) : Set M :=
  {q : M | riemannianEDist I p q < ENNReal.ofReal ρ}

/-- Membership in the small normal ball unfolds to the defining
`riemannianEDist` strict inequality. -/
@[simp] lemma mem_smallNormalBall {p q : M} {ρ : ℝ} :
    q ∈ smallNormalBall (I := I) p ρ ↔ riemannianEDist I p q < ENNReal.ofReal ρ :=
  Iff.rfl

/-- The centre lies in every small normal ball of positive radius. -/
lemma centre_mem_smallNormalBall (p : M) {ρ : ℝ} (hρ : 0 < ρ) :
    p ∈ smallNormalBall (I := I) p ρ := by
  rw [mem_smallNormalBall, riemannianEDist_self]
  exact ENNReal.ofReal_pos.2 hρ

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [T2Space (TangentBundle I M)]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

/-- A chosen tangent vector whose intrinsic exponential reaches `b` from `a`
with length equal to the Riemannian distance. -/
noncomputable def minimizingVec
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : TangentSpace I a :=
  Classical.choose
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)

/-- The chosen minimizing vector exponentiates to its target. -/
theorem minimizingVec_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) :
    expMapIntrinsic (I := I) g hEnorm a (minimizingVec (I := I) g hEnorm a b) = b :=
  (Classical.choose_spec
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)).1

/-- The chosen minimizing vector has length equal to the Riemannian distance. -/
theorem minimizingVec_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) :
    Real.sqrt (g.inner a (minimizingVec (I := I) g hEnorm a b)
        (minimizingVec (I := I) g hEnorm a b)) =
      (riemannianEDist I a b).toReal :=
  (Classical.choose_spec
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)).2

/-- The chosen minimizing-geodesic join from `a` to `b`. -/
noncomputable def minJoin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) (t : ℝ) : M :=
  intrinsicGeodesic (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b) t

/-- The chosen minimizing join starts at its first endpoint. -/
@[simp] theorem minJoin_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : minJoin (I := I) g hEnorm a b 0 = a := by
  exact intrinsicGeodesic_zero (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b)

/-- The chosen minimizing join ends at its second endpoint. -/
@[simp] theorem minJoin_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : minJoin (I := I) g hEnorm a b 1 = b := by
  change intrinsicGeodesic (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b) 1 = b
  rw [← expMapIntrinsic_def, minimizingVec_exp]

/-- The chosen minimizing join is continuous in its time parameter. -/
theorem minJoin_cont
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : Continuous (minJoin (I := I) g hEnorm a b) :=
  intrinsicGeodesic_continuous (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b)

/-- Along the standard `[0, 1]` parametrization of the chosen minimizing join, the
displacement from the first endpoint is at most `t` times the endpoint
distance. -/
theorem minJoin_edist_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) {t : ℝ} (ht : 0 ≤ t) :
    riemannianEDist I a (minJoin (I := I) g hEnorm a b t) ≤
      ENNReal.ofReal ((riemannianEDist I a b).toReal * t) := by
  simpa only [minJoin, intrinsicGeodesic_zero, minimizingVec_len, sub_zero] using
    intrinsicGeodesic_riemannianEDist_le
      (I := I) g hEnorm a (minimizingVec (I := I) g hEnorm a b)
        (s := 0) (t := t) ht

/-- **Constant squared `g`-speed of the intrinsic geodesic.** Along
`γ := intrinsicGeodesic g hEnorm p v`, the squared `g`-speed
`g.inner (γ t) (γ'(t)) (γ'(t))` equals the launch squared speed `g.inner p v v`
for every `t`: the curve is `IsGeodesic` and `C¹` in time, so its squared speed
is constant (`isGeodesicOn_speedSq_const`); comparing with the launch time `0`,
where `intrinsicGeodesic_mfderiv_zero` identifies the velocity with `v`, gives
the value. -/
private lemma intrinsicGeodesic_speedSq_const
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
  exact congrArg₂ (fun (x : M) (w : E) => g.inner x w w) h0 hvelE

/-- **Velocity enorm bound along the intrinsic geodesic.** The bundle enorm of
the velocity is bounded by the launch speed `√(g_p(v, v))` at every time, by
constant squared speed (`intrinsicGeodesic_speedSq_const`) and the
enorm-from-speed conversion `hEnorm`. -/
private lemma intrinsicGeodesic_velocity_enorm_le'
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t (1 : ℝ)‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hnn : (0 : ℝ) ≤ g.inner p v v := by
    rcases eq_or_ne v 0 with h | h
    · subst h; simp
    · exact (g.pos p v h).le
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hspeedSq : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = c ^ 2 := by
    rw [intrinsicGeodesic_speedSq_const (I := I) g hEnorm p v t, hc_def,
      Real.sq_sqrt hnn]
  rw [hEnorm]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  calc Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))
      = Real.sqrt (c ^ 2) := by rw [hspeedSq]
    _ = c := Real.sqrt_sq hc_nn

/-- **Radial length-distance bound.** For `0 ≤ t`, the intrinsic-distance
displacement of the radial geodesic from its launch point `p` over `[0, t]` is
bounded by the launch speed times the elapsed parameter:
`riemannianEDist I p (γ_v t) ≤ ENNReal.ofReal (√(g_p(v, v)) · t)`.

The proof dominates `pathELength I γ_v 0 t` by the constant speed
`√(g_p(v, v))` (via `intrinsicGeodesic_velocity_enorm_le'`) and chains with
`riemannianEDist_le_pathELength`. -/
theorem intrinsicGeodesic_riemannianEDist_le_radius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {t : ℝ} (ht : 0 ≤ t) :
    riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v) * t) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 t) :=
    (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono (Set.subset_univ _)
  have h_pathLen_le : pathELength I γ 0 t ≤ ENNReal.ofReal (c * t) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc 0 t, (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ _ => ?_)
      simpa [hγ_def, hc_def] using
        intrinsicGeodesic_velocity_enorm_le' (I := I) g hEnorm p v τ
    have h_const :
        (∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc 0 t) :=
      MeasureTheory.setLIntegral_const (Set.Icc 0 t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc 0 t) = ENNReal.ofReal (t - 0) :=
      Real.volume_Icc
    calc
      ∫⁻ τ in Set.Icc 0 t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc 0 t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - 0) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - 0)) := (ENNReal.ofReal_mul hc_nn).symm
      _ = ENNReal.ofReal (c * t) := by ring_nf
  have h_dist_le : riemannianEDist I (γ 0) (γ t) ≤ pathELength I γ 0 t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := 0) (b := t)
      hγ_C1 rfl rfl ht
  calc riemannianEDist I p (γ t)
      = riemannianEDist I (γ 0) (γ t) := by rw [hγ0]
    _ ≤ pathELength I γ 0 t := h_dist_le
    _ ≤ ENNReal.ofReal (c * t) := h_pathLen_le

/-- **Radial confinement (star-shapedness about the centre).** If the radial
geodesic from `p` with launch velocity `v` reaches `g_p`-radius
`√(g_p(v, v)) < ρ`, then the whole radial geodesic
`t ↦ intrinsicGeodesic g hEnorm p v t` lies inside the small normal ball
`smallNormalBall p ρ` for every `t ∈ [0, 1]`.

This is the genuine geometric core of the centre-star part of Whitehead
convexity: the small intrinsic ball is star-shaped about its centre along
radial geodesics.  The proof is the radial length bound
`intrinsicGeodesic_riemannianEDist_le_radius` combined with the monotone scaling
`√(g_p(v, v)) · t ≤ √(g_p(v, v)) < ρ` for `t ∈ [0, 1]`. -/
theorem smallNormalBall_radial_confined
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {ρ : ℝ}
    (hv : Real.sqrt (g.inner p v v) < ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    intrinsicGeodesic (I := I) g hEnorm p v t ∈ smallNormalBall (I := I) p ρ := by
  obtain ⟨ht0, ht1⟩ := ht
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hbound := intrinsicGeodesic_riemannianEDist_le_radius (I := I) g hEnorm p v ht0
  rw [mem_smallNormalBall]
  refine lt_of_le_of_lt hbound ?_
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc_nn |>.2 hv)
  calc c * t ≤ c * 1 := by
        exact mul_le_mul_of_nonneg_left ht1 hc_nn
    _ = c := mul_one c

/-- **Every small-ball point reached by a radial geodesic is joined to the centre
inside the ball.** If `√(g_p(v, v)) < ρ`, then the centre `p` and the radial
endpoint `expMapIntrinsic g hEnorm p v` are joined by a path
(`t ↦ intrinsicGeodesic g hEnorm p v t`) lying entirely inside
`smallNormalBall p ρ`.

This is the centre-star path-connectivity of the small ball: the genuine
provable consequence of the radial confinement.  Continuity of the radial path
is `intrinsicGeodesic_continuous`; confinement is `smallNormalBall_radial_confined`. -/
theorem joinedIn_centre_smallNormalBall
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {ρ : ℝ}
    (hv : Real.sqrt (g.inner p v v) < ρ) :
    JoinedIn (smallNormalBall (I := I) p ρ) p
      (expMapIntrinsic (I := I) g hEnorm p v) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ1 : γ 1 = expMapIntrinsic (I := I) g hEnorm p v := rfl
  refine JoinedIn.ofLine hγ_cont.continuousOn hγ0 hγ1 ?_
  rintro x ⟨t, ht, rfl⟩
  exact smallNormalBall_radial_confined (I := I) g hEnorm p v hv ht

end IntrinsicBall

end Riemannian
end Geometry
end DifferentialGeometry

end
