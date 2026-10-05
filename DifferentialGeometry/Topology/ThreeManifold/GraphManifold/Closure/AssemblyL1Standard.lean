import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyBallHandleCycle
import DifferentialGeometry.Topology.Handle.SphereCapComplementIsotopy
import DifferentialGeometry.Topology.Manifold.SphereDirection

/-!
# Chapter-14 assembly, item L1, group G3: the standard local forms and the cycle normal form

Shared definitions of the three parts of G3 (lane ASM-L1; split agreed with main on 2026-10-04):
G3a (the model cycle in the 3-sphere), G3b (the normal form of an actual `BallHandleCycle`), G3c
(gluing). Both G3a and G3b produce a `CycleNormalForm`; G3c glues two of them.

**Standard local forms (scale `ε`).** Near an end disk everything is read in NECK coordinates
`(z, τ) ∈ ℝ² × ℝ` on `neckDomain ε = {‖z‖ < 1 + 2ε, |τ| < 2ε}`: the ball side is `{τ ≤ 0}`, the handle
side is `{0 ≤ τ, ‖z‖ ≤ 1}`, the end disk is `{τ = 0, ‖z‖ ≤ 1}`, and the rounded union is
`{neckRounding ε ≤ 0}` with `neckRounding ε (z, τ) = standardRimRounding ((‖z‖ - 1) / ε, τ / ε)`
(the rim chart `(θ, x, y) ↦ ((1 + ε x) θ, ε y)`, `neckRim`, puts the fixed rim rounding of
`AssemblyRimRounding.lean` in these coordinates).
* A handle `ClosedCell 2 × [0, 1]` enters the neck at its end `b` by `(z, t) ↦ (z, t)` (`b = false`)
  or `(z, t) ↦ (z, 1 - t)` (`b = true`): `handleEnd`.
* A ball `ClosedCell 3` enters the neck at its cap `b` by `capMap b`: radial coordinate `‖x‖ - 1` and
  the stereographic coordinate of the direction from the antipodal pole, on the open hemisphere of the
  pole (`neckCapRegion`); the cap `false` is around the south pole, the cap `true` is its mirror
  image under `x₃ ↦ -x₃` (`capMap true = capMap false ∘ reflectThree`), so the two caps carry opposite orientations, as the two ends of a handle do.
  The unit disk `{‖z‖ ≤ 1}` corresponds to the round cap `{3/5 ≤ ⟪θ, pole⟫}`.

**`CycleNormalForm I X len ε U`.** `len` balls `ClosedCell 3 → X`, `len` handles
`ClosedCell 2 × [0, 1] → X` (handle `k` from ball `k` to ball `k + 1 mod len`), and `2 len` necks
(partial diffeomorphisms `neckDomain ε → X`, pairwise disjoint targets), with: balls and handles
smooth injective of bijective differential; the balls and handles enter the necks in the standard
forms on fixed regions (`ball_cap`, `handle_end`); inside a neck the ball, the handle and the set
`U` are the standard sets (`neck_ball`, `neck_handle`, `neck_union`); a neck meets no other ball or
handle (`neck_pieces`); balls pairwise disjoint, handles pairwise disjoint, handles meet balls
exactly in their end disks (`handle_ball_inter`); `U` is the union of the balls, the handles and the
neck images of the standard rounded sets (`union_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

universe u v

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1Std : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1Std : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASML1Std : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance fact_finrank_three_ASML1Std :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- The unit circle in the plane `ℝ²`. -/
def planeOfCircle (θ : Circle) : EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr (θ : ℂ)

/-- The neck domain at scale `ε`. -/
def neckDomain (ε : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {q | ‖q.1‖ < 1 + 2 * ε ∧ |q.2| < 2 * ε}

/-- The standard rim chart in neck coordinates at scale `ε`. -/
def neckRim (ε : ℝ) (p : Circle × (ℝ × ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ :=
  ((1 + ε * p.2.1) • planeOfCircle p.1, ε * p.2.2)

/-- The standard rim rounding in neck coordinates at scale `ε`. -/
def neckRounding (ε : ℝ) (q : EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ :=
  standardRimRounding ((‖q.1‖ - 1) / ε, q.2 / ε)

/-- The neck coordinate of the handle parameter at the end `b`. -/
def endCoord (b : Bool) (t : ℝ) : ℝ := if b then 1 - t else t

/-- A handle enters the neck at its end `b`. -/
def handleEnd (b : Bool) (q : ClosedCell 2 × Icc (0 : ℝ) 1) : EuclideanSpace ℝ (Fin 2) × ℝ :=
  ((q.1 : EuclideanSpace ℝ (Fin 2)), endCoord b q.2)

/-- The south pole of the unit sphere of `ℝ³`. -/
def southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨-EuclideanSpace.single 2 1, by simp⟩

/-- The north pole of the unit sphere of `ℝ³`. -/
def northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single 2 1, by simp⟩

/-- The reflection `x₃ ↦ -x₃` of `ℝ³` (through the plane orthogonal to the north pole). -/
def reflectThree : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ℝ ∙ (EuclideanSpace.single 2 1 : EuclideanSpace ℝ (Fin 3)))ᗮ.reflection

/-- The standard cap chart of the south cap: stereographic coordinate (from the north pole) of the
direction and the radial coordinate `‖x‖ - 1`. -/
def southCapMap (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) × ℝ :=
  (DifferentialGeometry.Topology.Handle.stereoChart northPole
    (DifferentialGeometry.Topology.Manifold.sphereDirection southPole x), ‖x‖ - 1)

/-- The standard cap chart of the cap `b` (`false`: south; `true`: north, the mirror image). -/
def capMap (b : Bool) (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) × ℝ :=
  if b then southCapMap (reflectThree x) else southCapMap x

/-- The pole of the cap `b` (`false`: south; `true`: north). -/
def capPole (b : Bool) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  if b then northPole else southPole

/-- The region of the closed 3-cell read by the neck of the cap `b` at scale `ε`: the radial collar
`1 - 2ε < ‖x‖`, the open hemisphere of the pole (which keeps the stereographic coordinate away from
its singular point) and the stereographic disk of radius `1 + 2ε`. -/
def neckCapRegion (ε : ℝ) (b : Bool) : Set (ClosedCell 3) :=
  {x | 1 - 2 * ε < ‖(x : EuclideanSpace ℝ (Fin 3))‖ ∧
    0 < ⟪(x : EuclideanSpace ℝ (Fin 3)), ((capPole b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))⟫_ℝ ∧
    ‖(capMap b (x : EuclideanSpace ℝ (Fin 3))).1‖ < 1 + 2 * ε}

/-- **The cycle normal form** (see the module docstring): `len` balls, `len` handles and `2 len`
necks in a manifold `X` modelled on `ℝ³` (with or without boundary), in the standard local forms
at scale `ε`, whose union is `U`. -/
structure CycleNormalForm {H : Type u} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H)
    (X : Type v) [TopologicalSpace X] [ChartedSpace H X] (len : ℕ) (ε : ℝ) (U : Set X) where
  ε_pos : 0 < ε
  ε_le : ε ≤ 1 / 8
  neck : Fin len → Bool →
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) I (EuclideanSpace ℝ (Fin 2) × ℝ) X ∞
  neck_source : ∀ k b, (neck k b).source = neckDomain ε
  neck_disjoint : ∀ k b k' b', (k, b) ≠ (k', b') → Disjoint (neck k b).target (neck k' b').target
  ball : Fin len → ClosedCell 3 → X
  ball_smooth : ∀ k, ContMDiff (𝓡∂ 3) I ∞ (ball k)
  ball_mfderiv : ∀ k x, Bijective (mfderiv (𝓡∂ 3) I (ball k) x)
  ball_injective : ∀ k, Injective (ball k)
  handle : Fin len → ClosedCell 2 × Icc (0 : ℝ) 1 → X
  handle_smooth : ∀ k, ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) I ∞ (handle k)
  handle_mfderiv : ∀ k q, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) I (handle k) q)
  handle_injective : ∀ k, Injective (handle k)
  ball_cap : ∀ k b x, x ∈ neckCapRegion ε b →
    ball (rimBall len k b) x = neck k b (capMap b (x : EuclideanSpace ℝ (Fin 3)))
  handle_end : ∀ k b (q : ClosedCell 2 × Icc (0 : ℝ) 1), |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε →
    handle k q = neck k b (handleEnd b q)
  neck_ball : ∀ k b {q}, q ∈ neckDomain ε →
    (neck k b q ∈ range (ball (rimBall len k b)) ↔ q.2 ≤ 0)
  neck_handle : ∀ k b {q}, q ∈ neckDomain ε →
    (neck k b q ∈ range (handle k) ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1))
  neck_union : ∀ k b {q}, q ∈ neckDomain ε → (neck k b q ∈ U ↔ neckRounding ε q ≤ 0)
  neck_pieces : ∀ k b, (neck k b).target ∩ ((⋃ j, range (ball j)) ∪ ⋃ j, range (handle j)) ⊆
    range (ball (rimBall len k b)) ∪ range (handle k)
  ball_disjoint : Pairwise fun k k' => Disjoint (range (ball k)) (range (ball k'))
  handle_disjoint : Pairwise fun k k' => Disjoint (range (handle k)) (range (handle k'))
  handle_ball_inter : ∀ k j, range (handle k) ∩ range (ball j) =
    (if j = k then handle k '' {q | q.2 = iccEnd false} else ∅) ∪
      (if j = finRotate len k then handle k '' {q | q.2 = iccEnd true} else ∅)
  union_eq : U = ((⋃ k, range (ball k)) ∪ ⋃ k, range (handle k)) ∪
    ⋃ k, ⋃ b, neck k b '' {q | q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0}

end GC.GraphManifold.Assembly
