/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalMonodromy
import Mathlib.Data.ZMod.Basic

/-!
# An orientation obstruction for the first closed branch case

A closed branch of a normal singular disk whose complete preimage is a single circle double
covering it is spliced by `CylinderSplice`, whose period map is the coordinate swap
`(x, y) ↦ (y, x)`.  That map is a reflection of the cross-section, and this file proves that the
configuration it models is incompatible with an orientation preserving boundary monodromy.

The geometric picture is the cross-section circle of a tube around the branch.  The two sheets
of the disk meet it in four marked rays, each sheet contributing a pair of opposite rays.  In the
first case the monodromy exchanges the two sheets.  An orientation preserving self map of the
circle preserves the cyclic order of the four rays, so a monodromy that exchanges the two
opposite pairs is a quarter turn, and its square exchanges the two rays of each sheet.  A
preimage circle whose neighbourhood in the source surface is an annulus forces the square to fix
each ray instead, and the two conclusions contradict each other.

The file has three layers.

* `zmodFour_quarterTurn`, `zmodFour_quarterTurn_sq` and `zmodFour_quarterTurn_sq_ne_self` are the
  finite combinatorial core, for the four marked rays indexed cyclically by `ZMod 4`.
* `HasIncreasingCircleLift.apply_ne_of_interleaved` and
  `HasIncreasingCircleLift.apply_apply_eq_of_sheetExchange` are the same statement for a self map
  of `loopCircle` with an increasing periodic lift.  They are proved directly from the lift, so
  they carry the cyclic order argument without any separate cyclic order API.
* `IsSheetExchange`, `IsPLCirclePositive.apply_apply_eq_of_sheetExchange`,
  `not_isPLCirclePositive_of_closedBranchCase1` and `IsCylindricalDiagram.not_closedBranchCase1`
  transport the conclusion to a piecewise linear circle and to the boundary monodromy of a
  cylindrical diagram.
* `not_isPLCirclePositive_spliceSquareBoundary_swap` applies the exclusion to the splice model
  itself: the period map `Prod.swap` of `CylinderSplice` reverses the orientation of the boundary
  circle of the square cross-section.  The four marked rays there are `spliceEnds`, split into
  the two sheets by `crossingArcX_inter_spliceSquareBoundary` and
  `crossingArcY_inter_spliceSquareBoundary`.
* `not_isCylindricalDiagram_swap_of_isOrientable` is the corollary in the form the induction of
  Moise's Lemma 2 consumes, with the inputs it still needs named in its docstring.

`IsCylindricalDiagram.not_closedBranchCase1` is a statement about the complex `M` of the
cylindrical diagram itself, exactly as `IsCylindricalDiagram.boundary_isPLCirclePositive` is: the
hypothesis `IsCylindricalDiagram f D.space M.space` makes `M.space` the image of the whole
diagram, so `M` is a triangulation of the tube around the branch carrying the orientation induced
from an ambient manifold, and is not the ambient manifold.

These results are an exclusion available in addition to the general reflection model, not a
replacement for it.  `LemmaTwoStatement` carries no orientability hypothesis and none is added
here.
-/

open Set

namespace DifferentialGeometry.Topology

/-! ### The combinatorial core on four cyclically indexed rays -/

/-- Index the four marked rays of the cross-section circle cyclically by `ZMod 4`, so that the
two sheets are the pairs `{i, i + 2}` of opposite rays.  A rotation by `k` preserves the sheets
exactly when `k = 0` or `k = 2`, so a rotation that exchanges the two sheets is a quarter turn. -/
theorem zmodFour_quarterTurn {k : ZMod 4} (h0 : k ≠ 0) (h2 : k ≠ 2) : k = 1 ∨ k = 3 := by
  have h : ∀ m : ZMod 4, m ≠ 0 → m ≠ 2 → m = 1 ∨ m = 3 := by decide
  exact h k h0 h2

/-- The square of a quarter turn of the four marked rays is the half turn `i ↦ i + 2`, which
exchanges the two rays of each sheet. -/
theorem zmodFour_quarterTurn_sq {k : ZMod 4} (h0 : k ≠ 0) (h2 : k ≠ 2) (i : ZMod 4) :
    i + k + k = i + 2 := by
  have h : ∀ j m : ZMod 4, m ≠ 0 → m ≠ 2 → j + m + m = j + 2 := by decide
  exact h i k h0 h2

/-- The half turn of the four marked rays fixes no ray. -/
theorem zmodFour_add_two_ne_self (i : ZMod 4) : i + 2 ≠ i := by
  have h : ∀ j : ZMod 4, j + 2 ≠ j := by decide
  exact h i

/-- The square of a quarter turn of the four marked rays fixes no ray.  This is the finite form
of the obstruction: an annular neighbourhood of the preimage circle in the source surface would
force the square of the monodromy to fix each of the two rays of its own sheet. -/
theorem zmodFour_quarterTurn_sq_ne_self {k : ZMod 4} (h0 : k ≠ 0) (h2 : k ≠ 2) (i : ZMod 4) :
    i + k + k ≠ i := by
  rw [zmodFour_quarterTurn_sq h0 h2 i]
  exact zmodFour_add_two_ne_self i

/-! ### Orientation preserving self maps of the circle -/

/-- Shifting a real number by the period does not change its class in `loopCircle`. -/
theorem loopCircle_coe_add_one (x : ℝ) : ((x + 1 : ℝ) : loopCircle) = (x : loopCircle) :=
  (loopCircle_coe_eq_coe_iff _ _).mpr ⟨1, by push_cast; ring⟩

/-- Two real numbers lying in one period window have distinct classes in `loopCircle`. -/
theorem loopCircle_coe_ne_coe_of_lt_of_lt_add_one {x y : ℝ} (hxy : x < y) (hy : y < x + 1) :
    (y : loopCircle) ≠ (x : loopCircle) := by
  intro h
  obtain ⟨n, hn⟩ := (loopCircle_coe_eq_coe_iff y x).mp h
  have hpos : (0 : ℤ) < n := by exact_mod_cast (by linarith : (0 : ℝ) < (n : ℝ))
  have hlt : n < (1 : ℤ) := by exact_mod_cast (by linarith : (n : ℝ) < 1)
  omega

/-- Normalize an increasing periodic lift so that it takes a prescribed value at a prescribed
point.  Only the integer translate of the lift is adjusted, so the three defining properties are
preserved. -/
theorem HasIncreasingCircleLift.exists_lift_eq {ψ : loopCircle → loopCircle}
    (hψ : HasIncreasingCircleLift ψ) {a b : ℝ} (hab : ψ (a : loopCircle) = (b : loopCircle)) :
    ∃ F : ℝ → ℝ, StrictMono F ∧ (∀ t : ℝ, F (t + 1) = F t + 1) ∧
      (∀ t : ℝ, ((F t : ℝ) : loopCircle) = ψ ((t : ℝ) : loopCircle)) ∧ F a = b := by
  obtain ⟨F, hFm, hFp, hFl⟩ := hψ
  obtain ⟨m, hm⟩ := (loopCircle_coe_eq_coe_iff (F a) b).mp ((hFl a).trans hab)
  refine ⟨fun t => F t - (m : ℝ), fun x y hxy => sub_lt_sub_right (hFm hxy) (m : ℝ),
    fun t => ?_, fun t => ?_, ?_⟩
  · change F (t + 1) - (m : ℝ) = F t - (m : ℝ) + 1
    rw [hFp]
    ring
  · refine Eq.trans ?_ (hFl t)
    exact (loopCircle_coe_eq_coe_iff (F t - (m : ℝ)) (F t)).mpr ⟨-m, by push_cast; ring⟩
  · change F a - (m : ℝ) = b
    linarith

/-- The step that makes the cyclic order argument work.  If `α < β < γ < δ < α + 1` mark four
points of the circle in cyclic order and an orientation preserving self map sends `α` to `β` and
`γ` to `δ`, then it cannot send `β` back to `α`.  Equivalently, a monodromy that exchanges the
two opposite pairs `{α, γ}` and `{β, δ}` cannot do so by a reflection. -/
theorem HasIncreasingCircleLift.apply_ne_of_interleaved {ψ : loopCircle → loopCircle}
    (hψ : HasIncreasingCircleLift ψ) {α β γ δ : ℝ} (hαβ : α < β) (hβγ : β < γ) (hγδ : γ < δ)
    (hδα : δ < α + 1) (hab : ψ (α : loopCircle) = (β : loopCircle))
    (hcd : ψ (γ : loopCircle) = (δ : loopCircle)) :
    ψ (β : loopCircle) ≠ (α : loopCircle) := by
  intro hba
  obtain ⟨F, hFm, hFp, hFl, hFa⟩ := hψ.exists_lift_eq hab
  have hβ1 : β < α + 1 := by linarith
  have hγ1 : γ < α + 1 := by linarith
  have hlow : β < F β := by
    have h := hFm hαβ
    rwa [hFa] at h
  have hhigh : F β < β + 1 := by
    have h := hFm hβ1
    rwa [hFp, hFa] at h
  obtain ⟨n, hn⟩ := (loopCircle_coe_eq_coe_iff (F β) α).mp ((hFl β).trans hba)
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (by linarith : (0 : ℝ) < (n : ℝ))
  have hn2 : n < (2 : ℤ) := by exact_mod_cast (by linarith : (n : ℝ) < 2)
  have hn1 : n = 1 := by omega
  subst hn1
  push_cast at hn
  have hβF : F β = α + 1 := by linarith
  have hlow' : α + 1 < F γ := by
    have h := hFm hβγ
    rwa [hβF] at h
  have hhigh' : F γ < β + 1 := by
    have h := hFm hγ1
    rwa [hFp, hFa] at h
  obtain ⟨k, hk⟩ := (loopCircle_coe_eq_coe_iff (F γ) δ).mp ((hFl γ).trans hcd)
  have hk0 : (0 : ℤ) < k := by exact_mod_cast (by linarith : (0 : ℝ) < (k : ℝ))
  have hk1 : k < (1 : ℤ) := by exact_mod_cast (by linarith : (k : ℝ) < 1)
  omega

/-- The circle form of the combinatorial core.  Let `α < β < γ < δ < α + 1` mark four points of
the circle in cyclic order, the two sheets being the opposite pairs `{α, γ}` and `{β, δ}`.  If an
orientation preserving self map carries every marked point to a marked point of the other sheet,
injectively on each sheet, then its square carries `α` to `γ`: it exchanges the two points of
each sheet rather than fixing them. -/
theorem HasIncreasingCircleLift.apply_apply_eq_of_sheetExchange {ψ : loopCircle → loopCircle}
    (hψ : HasIncreasingCircleLift ψ) {α β γ δ : ℝ} (hαβ : α < β) (hβγ : β < γ) (hγδ : γ < δ)
    (hδα : δ < α + 1)
    (ha : ψ (α : loopCircle) = (β : loopCircle) ∨ ψ (α : loopCircle) = (δ : loopCircle))
    (hb : ψ (β : loopCircle) = (α : loopCircle) ∨ ψ (β : loopCircle) = (γ : loopCircle))
    (hc : ψ (γ : loopCircle) = (β : loopCircle) ∨ ψ (γ : loopCircle) = (δ : loopCircle))
    (hd : ψ (δ : loopCircle) = (α : loopCircle) ∨ ψ (δ : loopCircle) = (γ : loopCircle))
    (hac : ψ (α : loopCircle) ≠ ψ (γ : loopCircle))
    (hbd : ψ (β : loopCircle) ≠ ψ (δ : loopCircle)) :
    ψ (ψ (α : loopCircle)) = (γ : loopCircle) := by
  rcases ha with ha | ha
  · have hcδ : ψ (γ : loopCircle) = (δ : loopCircle) :=
      hc.resolve_left fun hc' => hac (ha.trans hc'.symm)
    have hbγ : ψ (β : loopCircle) = (γ : loopCircle) :=
      hb.resolve_left (hψ.apply_ne_of_interleaved hαβ hβγ hγδ hδα ha hcδ)
    rw [ha, hbγ]
  · have hcβ : ψ (γ : loopCircle) = (β : loopCircle) :=
      hc.resolve_right fun hc' => hac (ha.trans hc'.symm)
    rcases hb with hb | hb
    · have hdγ : ψ (δ : loopCircle) = (γ : loopCircle) :=
        hd.resolve_left fun hd' => hbd (hb.trans hd'.symm)
      rw [ha, hdγ]
    · exfalso
      have hdα : ψ (δ : loopCircle) = (α : loopCircle) :=
        hd.resolve_right fun hd' => hbd (hb.trans hd'.symm)
      have hdα' : ψ (δ : loopCircle) = ((α + 1 : ℝ) : loopCircle) := by
        rw [hdα, loopCircle_coe_add_one]
      exact hψ.apply_ne_of_interleaved hβγ hγδ hδα (by linarith) hb hdα' hcβ

namespace PiecewiseLinear

/-! ### The configuration on a piecewise linear cross-section circle -/

/-- The configuration of the first closed branch case on a cross-section circle.

Here `g` parametrizes the circle and `g α`, `g β`, `g γ`, `g δ` are the four rays in which the
branch meets it, listed in cyclic order, so the two sheets contribute the opposite pairs
`{g α, g γ}` and `{g β, g δ}`.  The monodromy `u` carries each ray to a ray of the other sheet,
and separates the two rays of each sheet. -/
structure IsSheetExchange {E : Type*} (u : E → E) (g : loopCircle → E) (α β γ δ : ℝ) : Prop where
  /-- The four marked rays are listed in cyclic order. -/
  lt_fst : α < β
  /-- The four marked rays are listed in cyclic order. -/
  lt_snd : β < γ
  /-- The four marked rays are listed in cyclic order. -/
  lt_thd : γ < δ
  /-- The four marked rays lie in one period window of the parametrization. -/
  lt_period : δ < α + 1
  /-- The first ray is carried to a ray of the other sheet. -/
  map_fst : u (g (α : loopCircle)) = g (β : loopCircle) ∨
    u (g (α : loopCircle)) = g (δ : loopCircle)
  /-- The second ray is carried to a ray of the other sheet. -/
  map_snd : u (g (β : loopCircle)) = g (α : loopCircle) ∨
    u (g (β : loopCircle)) = g (γ : loopCircle)
  /-- The third ray is carried to a ray of the other sheet. -/
  map_thd : u (g (γ : loopCircle)) = g (β : loopCircle) ∨
    u (g (γ : loopCircle)) = g (δ : loopCircle)
  /-- The fourth ray is carried to a ray of the other sheet. -/
  map_fth : u (g (δ : loopCircle)) = g (α : loopCircle) ∨
    u (g (δ : loopCircle)) = g (γ : loopCircle)
  /-- The monodromy separates the two rays of the first sheet. -/
  ne_fst : u (g (α : loopCircle)) ≠ u (g (γ : loopCircle))
  /-- The monodromy separates the two rays of the second sheet. -/
  ne_snd : u (g (β : loopCircle)) ≠ u (g (δ : loopCircle))

variable {E : Type*} [NormedAddCommGroup E]

/-- If the monodromy of a piecewise linear circle preserves its orientation and exchanges the two
sheets of the four marked rays, then its square carries the first ray to the opposite ray of the
same sheet. -/
theorem IsPLCirclePositive.apply_apply_eq_of_sheetExchange {S : Set E} {u : E → E}
    (hu : IsPLCirclePositive S u) (hmu : MapsTo u S S) {g : loopCircle → E} (hgc : Continuous g)
    (hgb : BijOn g univ S) {α β γ δ : ℝ} (hconf : IsSheetExchange u g α β γ δ) :
    u (u (g (α : loopCircle))) = g (γ : loopCircle) := by
  have hkey : ∀ {s t : ℝ}, u (g (s : loopCircle)) = g (t : loopCircle) →
      circleConj g u (s : loopCircle) = (t : loopCircle) := by
    intro s t h
    exact hgb.injOn (mem_univ _) (mem_univ _) ((circleConj_spec hgb hmu _).trans h)
  have hne : ∀ {s t : ℝ}, u (g (s : loopCircle)) ≠ u (g (t : loopCircle)) →
      circleConj g u (s : loopCircle) ≠ circleConj g u (t : loopCircle) := by
    intro s t h hst
    exact h (((circleConj_spec hgb hmu _).symm.trans (congrArg g hst)).trans
      (circleConj_spec hgb hmu _))
  have hmain := (hu.forall_param hmu hgc hgb).apply_apply_eq_of_sheetExchange hconf.lt_fst
    hconf.lt_snd hconf.lt_thd hconf.lt_period (hconf.map_fst.imp hkey hkey)
    (hconf.map_snd.imp hkey hkey) (hconf.map_thd.imp hkey hkey) (hconf.map_fth.imp hkey hkey)
    (hne hconf.ne_fst) (hne hconf.ne_snd)
  have h := congrArg g hmain
  rw [circleConj_spec hgb hmu, circleConj_spec hgb hmu] at h
  exact h

/-- The exclusion on a piecewise linear circle.  A monodromy that exchanges the two sheets of the
four marked rays and whose square fixes the first ray, as an annular neighbourhood of the
preimage circle in the source surface forces, cannot preserve the orientation of the circle. -/
theorem not_isPLCirclePositive_of_closedBranchCase1 {S : Set E} {u : E → E} (hmu : MapsTo u S S)
    {g : loopCircle → E} (hgc : Continuous g) (hgb : BijOn g univ S) {α β γ δ : ℝ}
    (hconf : IsSheetExchange u g α β γ δ)
    (hsq : u (u (g (α : loopCircle))) = g (α : loopCircle)) : ¬ IsPLCirclePositive S u := by
  intro hu
  have hmain := hu.apply_apply_eq_of_sheetExchange hmu hgc hgb hconf
  have hg : g (γ : loopCircle) = g (α : loopCircle) := by
    rw [← hmain]
    exact hsq
  have hcirc : (γ : loopCircle) = (α : loopCircle) :=
    hgb.injOn (mem_univ _) (mem_univ _) hg
  exact loopCircle_coe_ne_coe_of_lt_of_lt_add_one
    (hconf.lt_fst.trans hconf.lt_snd) (hconf.lt_thd.trans hconf.lt_period) hcirc

/-! ### The exclusion for a cylindrical diagram -/

open Classical in
/-- The first closed branch case is excluded by orientability.

The hypotheses are those of `IsCylindricalDiagram.boundary_isPLCirclePositive_of_bottom_eq_top`
together with the configuration of the first case on the boundary circle of the cross-section
disk: four marked rays in cyclic order whose two sheets the monodromy `u` exchanges, and an
annular neighbourhood of the preimage circle in the source surface, which makes the square of the
monodromy fix the first ray.

As in `IsCylindricalDiagram.boundary_isPLCirclePositive_of_bottom_eq_top`, the orientable complex
`M` is the target of the cylindrical diagram itself, that is a triangulation of the tube around
the branch carrying the orientation induced from an ambient manifold, and not the ambient
manifold. -/
theorem IsCylindricalDiagram.not_closedBranchCase1 {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E × ℝ → F} (D : Geometry.SimplicialComplex ℝ E)
    (M : Geometry.SimplicialComplex ℝ F) [Finite D.faces] [Finite M.faces]
    (hD : IsPLBall 2 D.space) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hor : IsOrientable 3 M) (hf : IsCylindricalDiagram f D.space M.space) {u : E → E}
    (hu : IsPLHomeomorphOn u D.space D.space) (hfu : ∀ x ∈ D.space, f (x, 0) = f (u x, 1))
    {g : loopCircle → E} (hgc : Continuous g)
    (hgb : BijOn g univ (boundaryComplex 2 D).space) {α β γ δ : ℝ}
    (hconf : IsSheetExchange u g α β γ δ)
    (hsq : u (u (g (α : loopCircle))) = g (α : loopCircle)) : False := by
  have hBsub := boundaryComplex_space_subset 2 D
  have hmu : MapsTo u (boundaryComplex 2 D).space (boundaryComplex 2 D).space := by
    intro x hx
    exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn D D
      hD.isCombinatorialManifoldWithBoundary hu (hBsub hx)).mpr hx
  exact not_isPLCirclePositive_of_closedBranchCase1 hmu hgc hgb hconf hsq
    (hf.boundary_isPLCirclePositive_of_bottom_eq_top D M hD hM hor hu hfu)

/-! ### The splice model reverses the orientation of its cross-section circle -/

/-- The upper arc of the boundary of the square model of the disk. -/
def upperSpliceBoundary : Set (ℝ × ℝ) := {p | p ∈ spliceSquareBoundary ∧ 0 ≤ p.2}

/-- The lower arc of the boundary of the square model of the disk. -/
def lowerSpliceBoundary : Set (ℝ × ℝ) := {p | p ∈ spliceSquareBoundary ∧ p.2 ≤ 0}

/-- Membership in the upper arc of the boundary of the square. -/
theorem mem_upperSpliceBoundary {p : ℝ × ℝ} :
    p ∈ upperSpliceBoundary ↔ p ∈ spliceSquareBoundary ∧ 0 ≤ p.2 := Iff.rfl

/-- Membership in the lower arc of the boundary of the square. -/
theorem mem_lowerSpliceBoundary {p : ℝ × ℝ} :
    p ∈ lowerSpliceBoundary ↔ p ∈ spliceSquareBoundary ∧ p.2 ≤ 0 := Iff.rfl

/-- The two arcs cover the boundary of the square. -/
theorem upperSpliceBoundary_union_lowerSpliceBoundary :
    upperSpliceBoundary ∪ lowerSpliceBoundary = spliceSquareBoundary := by
  ext p
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases le_total (0 : ℝ) p.2 with h2 | h2
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr ⟨h, h2⟩

/-- A point of the closed square with nonnegative second coordinate lying on one of the three
upper sides belongs to the upper arc. -/
theorem mk_mem_upperSpliceBoundary {x y : ℝ} (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y)
    (hy' : y ≤ 1) (h : x = -1 ∨ x = 1 ∨ y = 1) : (x, y) ∈ upperSpliceBoundary := by
  refine ⟨⟨mem_spliceSquare.mpr ⟨⟨hx, hx'⟩, ⟨by linarith, hy'⟩⟩, ?_⟩, hy⟩
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

/-- A point of the closed square with nonpositive second coordinate lying on one of the three
lower sides belongs to the lower arc. -/
theorem mk_mem_lowerSpliceBoundary {x y : ℝ} (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y)
    (hy' : y ≤ 0) (h : x = -1 ∨ x = 1 ∨ y = -1) : (x, y) ∈ lowerSpliceBoundary := by
  refine ⟨⟨mem_spliceSquare.mpr ⟨⟨hx, hx'⟩, ⟨hy, by linarith⟩⟩, ?_⟩, hy'⟩
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- The two arcs meet exactly in the two rays of the sheet `crossingArcY`. -/
theorem upperSpliceBoundary_inter_lowerSpliceBoundary :
    upperSpliceBoundary ∩ lowerSpliceBoundary =
      {((1 : ℝ), (0 : ℝ)), ((-1 : ℝ), (0 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨hb, h1⟩, -, h2⟩
    have hp2 : p.2 = 0 := le_antisymm h2 h1
    rcases hb.2 with h | h | h | h
    · exact Or.inr (Prod.ext_iff.mpr ⟨h, hp2⟩)
    · exact Or.inl (Prod.ext_iff.mpr ⟨h, hp2⟩)
    · exact absurd (h.symm.trans hp2) (by norm_num)
    · exact absurd (h.symm.trans hp2) (by norm_num)
  · rintro (rfl | rfl)
    · exact ⟨mk_mem_upperSpliceBoundary (by norm_num) le_rfl le_rfl (by norm_num)
        (Or.inr (Or.inl rfl)),
        mk_mem_lowerSpliceBoundary (by norm_num) le_rfl (by norm_num) le_rfl
          (Or.inr (Or.inl rfl))⟩
    · exact ⟨mk_mem_upperSpliceBoundary le_rfl (by norm_num) le_rfl (by norm_num) (Or.inl rfl),
        mk_mem_lowerSpliceBoundary le_rfl (by norm_num) (by norm_num) le_rfl (Or.inl rfl)⟩

/-- A parametrization of `upperSpliceBoundary` by `[0, 1]`, running from `(1, 0)` up the right
side of the square, across the top through `(0, 1)`, and down the left side to `(-1, 0)`. -/
noncomputable def upperSpliceArc (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 / 4 then (1, 4 * t) else if t ≤ 3 / 4 then (2 - 4 * t, 1) else (-1, 4 - 4 * t)

/-- A parametrization of `lowerSpliceBoundary` by `[0, 1]`, running from `(1, 0)` down the right
side of the square, across the bottom through `(0, -1)`, and up the left side to `(-1, 0)`. -/
noncomputable def lowerSpliceArc (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 / 4 then (1, -(4 * t)) else if t ≤ 3 / 4 then (2 - 4 * t, -1) else (-1, -(4 - 4 * t))

/-- The upper arc on the right side of the square. -/
theorem upperSpliceArc_of_le {t : ℝ} (ht : t ≤ 1 / 4) : upperSpliceArc t = (1, 4 * t) := if_pos ht

/-- The lower arc on the right side of the square. -/
theorem lowerSpliceArc_of_le {t : ℝ} (ht : t ≤ 1 / 4) :
    lowerSpliceArc t = (1, -(4 * t)) := if_pos ht

/-- The upper arc on the top side of the square. -/
theorem upperSpliceArc_of_mem {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 3 / 4) :
    upperSpliceArc t = (2 - 4 * t, 1) := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h, upperSpliceArc_of_le le_rfl]
    norm_num
  · unfold upperSpliceArc
    rw [if_neg (not_le.mpr h), if_pos h2]

/-- The lower arc on the bottom side of the square. -/
theorem lowerSpliceArc_of_mem {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 3 / 4) :
    lowerSpliceArc t = (2 - 4 * t, -1) := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h, lowerSpliceArc_of_le le_rfl]
    norm_num
  · unfold lowerSpliceArc
    rw [if_neg (not_le.mpr h), if_pos h2]

/-- The upper arc on the left side of the square. -/
theorem upperSpliceArc_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) : upperSpliceArc t = (-1, 4 - 4 * t) := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, upperSpliceArc_of_mem (by norm_num) le_rfl]
    norm_num
  · unfold upperSpliceArc
    rw [if_neg (not_le.mpr (by linarith : (1 : ℝ) / 4 < t)), if_neg (not_le.mpr h)]

/-- The lower arc on the left side of the square. -/
theorem lowerSpliceArc_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) :
    lowerSpliceArc t = (-1, -(4 - 4 * t)) := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, lowerSpliceArc_of_mem (by norm_num) le_rfl]
    norm_num
  · unfold lowerSpliceArc
    rw [if_neg (not_le.mpr (by linarith : (1 : ℝ) / 4 < t)), if_neg (not_le.mpr h)]

/-- The three closed sides traversed by the upper arc. -/
theorem upperSpliceArc_cases (t : ℝ) :
    (t ≤ 1 / 4 ∧ upperSpliceArc t = (1, 4 * t)) ∨
      (1 / 4 ≤ t ∧ t ≤ 3 / 4 ∧ upperSpliceArc t = (2 - 4 * t, 1)) ∨
        (3 / 4 ≤ t ∧ upperSpliceArc t = (-1, 4 - 4 * t)) := by
  rcases le_total t (1 / 4 : ℝ) with h | h
  · exact Or.inl ⟨h, upperSpliceArc_of_le h⟩
  · rcases le_total t (3 / 4 : ℝ) with h' | h'
    · exact Or.inr (Or.inl ⟨h, h', upperSpliceArc_of_mem h h'⟩)
    · exact Or.inr (Or.inr ⟨h', upperSpliceArc_of_ge h'⟩)

/-- The three closed sides traversed by the lower arc. -/
theorem lowerSpliceArc_cases (t : ℝ) :
    (t ≤ 1 / 4 ∧ lowerSpliceArc t = (1, -(4 * t))) ∨
      (1 / 4 ≤ t ∧ t ≤ 3 / 4 ∧ lowerSpliceArc t = (2 - 4 * t, -1)) ∨
        (3 / 4 ≤ t ∧ lowerSpliceArc t = (-1, -(4 - 4 * t))) := by
  rcases le_total t (1 / 4 : ℝ) with h | h
  · exact Or.inl ⟨h, lowerSpliceArc_of_le h⟩
  · rcases le_total t (3 / 4 : ℝ) with h' | h'
    · exact Or.inr (Or.inl ⟨h, h', lowerSpliceArc_of_mem h h'⟩)
    · exact Or.inr (Or.inr ⟨h', lowerSpliceArc_of_ge h'⟩)

/-- Both arcs start at the ray `(1, 0)`. -/
theorem upperSpliceArc_zero : upperSpliceArc 0 = (1, 0) := by
  rw [upperSpliceArc_of_le (by norm_num)]
  norm_num

/-- Both arcs start at the ray `(1, 0)`. -/
theorem lowerSpliceArc_zero : lowerSpliceArc 0 = (1, 0) := by
  rw [lowerSpliceArc_of_le (by norm_num)]
  norm_num

/-- Both arcs end at the ray `(-1, 0)`. -/
theorem upperSpliceArc_one : upperSpliceArc 1 = (-1, 0) := by
  rw [upperSpliceArc_of_ge (by norm_num)]
  norm_num

/-- Both arcs end at the ray `(-1, 0)`. -/
theorem lowerSpliceArc_one : lowerSpliceArc 1 = (-1, 0) := by
  rw [lowerSpliceArc_of_ge (by norm_num)]
  norm_num

/-- A map agreeing with an affine map on a closed interval is piecewise affine there. -/
theorem isPiecewiseAffineOn_Icc_of_eqOn {f : ℝ → ℝ × ℝ} {a b : ℝ} {A : ℝ →ᵃ[ℝ] ℝ × ℝ}
    (h : EqOn f A (Icc a b)) : IsPiecewiseAffineOn f (Icc a b) := by
  have h' := isPiecewiseAffineOn_of_forall_isHPolytope (fun _ : Unit => Icc a b)
    (fun _ => isHPolytope_Icc) (fun _ => ⟨A, h⟩)
  rwa [iUnion_const] at h'

/-- The upper arc is piecewise affine. -/
theorem isPiecewiseAffineOn_upperSpliceArc :
    IsPiecewiseAffineOn upperSpliceArc (Icc (0 : ℝ) 1) := by
  have e1 : EqOn upperSpliceArc (AffineMap.lineMap ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (4 : ℝ)))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    rw [upperSpliceArc_of_le ht.2, AffineMap.lineMap_apply_module]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have e2 : EqOn upperSpliceArc (AffineMap.lineMap ((2 : ℝ), (1 : ℝ)) ((-2 : ℝ), (1 : ℝ)))
      (Icc (1 / 4 : ℝ) (3 / 4)) := by
    intro t ht
    rw [upperSpliceArc_of_mem ht.1 ht.2, AffineMap.lineMap_apply_module]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have e3 : EqOn upperSpliceArc (AffineMap.lineMap ((-1 : ℝ), (4 : ℝ)) ((-1 : ℝ), (0 : ℝ)))
      (Icc (3 / 4 : ℝ) 1) := by
    intro t ht
    rw [upperSpliceArc_of_ge ht.1, AffineMap.lineMap_apply_module]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have h12 := (isPiecewiseAffineOn_Icc_of_eqOn e1).union_of_isClosed
    (isPiecewiseAffineOn_Icc_of_eqOn e2) isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 : ℝ) / 4 ≤ 3 / 4)] at h12
  have h123 := h12.union_of_isClosed (isPiecewiseAffineOn_Icc_of_eqOn e3)
    isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 : ℝ) / 4 ≤ 1)] at h123

/-- The lower arc is piecewise affine. -/
theorem isPiecewiseAffineOn_lowerSpliceArc :
    IsPiecewiseAffineOn lowerSpliceArc (Icc (0 : ℝ) 1) := by
  have e1 : EqOn lowerSpliceArc (AffineMap.lineMap ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (-4 : ℝ)))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    rw [lowerSpliceArc_of_le ht.2, AffineMap.lineMap_apply_module]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have e2 : EqOn lowerSpliceArc (AffineMap.lineMap ((2 : ℝ), (-1 : ℝ)) ((-2 : ℝ), (-1 : ℝ)))
      (Icc (1 / 4 : ℝ) (3 / 4)) := by
    intro t ht
    rw [lowerSpliceArc_of_mem ht.1 ht.2, AffineMap.lineMap_apply_module]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have e3 : EqOn lowerSpliceArc (AffineMap.lineMap ((-1 : ℝ), (-4 : ℝ)) ((-1 : ℝ), (0 : ℝ)))
      (Icc (3 / 4 : ℝ) 1) := by
    intro t ht
    rw [lowerSpliceArc_of_ge ht.1, AffineMap.lineMap_apply_module]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have h12 := (isPiecewiseAffineOn_Icc_of_eqOn e1).union_of_isClosed
    (isPiecewiseAffineOn_Icc_of_eqOn e2) isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 : ℝ) / 4 ≤ 3 / 4)] at h12
  have h123 := h12.union_of_isClosed (isPiecewiseAffineOn_Icc_of_eqOn e3)
    isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 : ℝ) / 4 ≤ 1)] at h123

/-- The upper arc is a bijection of `[0, 1]` onto the upper arc of the square boundary. -/
theorem bijOn_upperSpliceArc : BijOn upperSpliceArc (Icc (0 : ℝ) 1) upperSpliceBoundary := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases upperSpliceArc_cases t with ⟨h, e⟩ | ⟨h1, h2, e⟩ | ⟨h, e⟩
    · rw [e]
      exact mk_mem_upperSpliceBoundary (by norm_num) le_rfl (by linarith [ht.1]) (by linarith)
        (Or.inr (Or.inl rfl))
    · rw [e]
      exact mk_mem_upperSpliceBoundary (by linarith) (by linarith) (by norm_num) le_rfl
        (Or.inr (Or.inr rfl))
    · rw [e]
      exact mk_mem_upperSpliceBoundary le_rfl (by norm_num) (by linarith [ht.2]) (by linarith)
        (Or.inl rfl)
  · intro t _ s _ hts
    rcases upperSpliceArc_cases t with ⟨-, et⟩ | ⟨-, -, et⟩ | ⟨-, et⟩ <;>
      rcases upperSpliceArc_cases s with ⟨-, es⟩ | ⟨-, -, es⟩ | ⟨-, es⟩ <;>
      rw [et, es, Prod.mk.injEq] at hts <;> obtain ⟨u1, u2⟩ := hts <;> linarith
  · rintro p ⟨hb, h0⟩
    obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := mem_spliceSquare.mp hb.1
    rcases hb.2 with h | h | h | h
    · refine ⟨1 - p.2 / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [upperSpliceArc_of_ge (by linarith), Prod.ext_iff]
      refine ⟨h.symm, ?_⟩
      change 4 - 4 * (1 - p.2 / 4) = p.2
      ring
    · refine ⟨p.2 / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [upperSpliceArc_of_le (by linarith), Prod.ext_iff]
      refine ⟨h.symm, ?_⟩
      change 4 * (p.2 / 4) = p.2
      ring
    · exact absurd (h ▸ h0) (by norm_num)
    · refine ⟨(2 - p.1) / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [upperSpliceArc_of_mem (by linarith) (by linarith), Prod.ext_iff]
      refine ⟨?_, h.symm⟩
      change 2 - 4 * ((2 - p.1) / 4) = p.1
      ring

/-- The lower arc is a bijection of `[0, 1]` onto the lower arc of the square boundary. -/
theorem bijOn_lowerSpliceArc : BijOn lowerSpliceArc (Icc (0 : ℝ) 1) lowerSpliceBoundary := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases lowerSpliceArc_cases t with ⟨h, e⟩ | ⟨h1, h2, e⟩ | ⟨h, e⟩
    · rw [e]
      exact mk_mem_lowerSpliceBoundary (by norm_num) le_rfl (by linarith) (by linarith [ht.1])
        (Or.inr (Or.inl rfl))
    · rw [e]
      exact mk_mem_lowerSpliceBoundary (by linarith) (by linarith) le_rfl (by norm_num)
        (Or.inr (Or.inr rfl))
    · rw [e]
      exact mk_mem_lowerSpliceBoundary le_rfl (by norm_num) (by linarith) (by linarith [ht.2])
        (Or.inl rfl)
  · intro t _ s _ hts
    rcases lowerSpliceArc_cases t with ⟨-, et⟩ | ⟨-, -, et⟩ | ⟨-, et⟩ <;>
      rcases lowerSpliceArc_cases s with ⟨-, es⟩ | ⟨-, -, es⟩ | ⟨-, es⟩ <;>
      rw [et, es, Prod.mk.injEq] at hts <;> obtain ⟨u1, u2⟩ := hts <;> linarith
  · rintro p ⟨hb, h0⟩
    obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := mem_spliceSquare.mp hb.1
    rcases hb.2 with h | h | h | h
    · refine ⟨1 + p.2 / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [lowerSpliceArc_of_ge (by linarith), Prod.ext_iff]
      refine ⟨h.symm, ?_⟩
      change -(4 - 4 * (1 + p.2 / 4)) = p.2
      ring
    · refine ⟨-(p.2 / 4), ⟨by linarith, by linarith⟩, ?_⟩
      rw [lowerSpliceArc_of_le (by linarith), Prod.ext_iff]
      refine ⟨h.symm, ?_⟩
      change -(4 * -(p.2 / 4)) = p.2
      ring
    · refine ⟨(2 - p.1) / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [lowerSpliceArc_of_mem (by linarith) (by linarith), Prod.ext_iff]
      refine ⟨?_, h.symm⟩
      change 2 - 4 * ((2 - p.1) / 4) = p.1
      ring
    · exact absurd (h ▸ h0) (by norm_num)

/-- The upper arc is a piecewise linear homeomorphism onto the upper arc of the boundary. -/
theorem isPLHomeomorphOn_upperSpliceArc :
    IsPLHomeomorphOn upperSpliceArc (Icc (0 : ℝ) 1) upperSpliceBoundary :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    isPiecewiseAffineOn_upperSpliceArc bijOn_upperSpliceArc

/-- The lower arc is a piecewise linear homeomorphism onto the lower arc of the boundary. -/
theorem isPLHomeomorphOn_lowerSpliceArc :
    IsPLHomeomorphOn lowerSpliceArc (Icc (0 : ℝ) 1) lowerSpliceBoundary :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    isPiecewiseAffineOn_lowerSpliceArc bijOn_lowerSpliceArc

/-- The coordinate swap preserves the boundary of the square. -/
theorem mapsTo_swap_spliceSquareBoundary :
    MapsTo Prod.swap spliceSquareBoundary spliceSquareBoundary := by
  intro p hp
  refine ⟨swap_mem_spliceSquare hp.1, ?_⟩
  rcases hp.2 with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- The period map of the cylinder splice reverses the orientation of the boundary circle of the
square cross-section.

The four marked rays are `spliceEnds`.  The sheet `crossingArcY` contributes `(1, 0)` and
`(-1, 0)`, the sheet `crossingArcX` contributes `(0, 1)` and `(0, -1)`, and the coordinate swap
exchanges the two sheets while its square is the identity, which is the configuration of the
first closed branch case.  So that case cannot occur inside an orientable ambient manifold. -/
theorem not_isPLCirclePositive_spliceSquareBoundary_swap :
    ¬ IsPLCirclePositive spliceSquareBoundary Prod.swap := by
  obtain ⟨g, hgc, hgb, hA, h0, hhalf⟩ := exists_loopCircle_param_of_arc_decomposition
    isPLHomeomorphOn_upperSpliceArc isPLHomeomorphOn_lowerSpliceArc
    (lowerSpliceArc_zero.trans upperSpliceArc_zero.symm)
    (lowerSpliceArc_one.trans upperSpliceArc_one.symm)
    upperSpliceBoundary_union_lowerSpliceBoundary
    (by rw [upperSpliceArc_zero, upperSpliceArc_one]
        exact upperSpliceBoundary_inter_lowerSpliceBoundary)
  rw [upperSpliceArc_zero] at h0
  rw [upperSpliceArc_one] at hhalf
  have hup : ((0 : ℝ), (1 : ℝ)) ∈ upperSpliceBoundary :=
    ⟨⟨mem_spliceSquare.mpr (by norm_num), Or.inr (Or.inr (Or.inr rfl))⟩, by norm_num⟩
  have hdown : ((0 : ℝ), (-1 : ℝ)) ∈ spliceSquareBoundary :=
    ⟨mem_spliceSquare.mpr (by norm_num), Or.inr (Or.inr (Or.inl rfl))⟩
  obtain ⟨θ, ⟨b, hb, rfl⟩, hgb1⟩ := hA.symm.subset hup
  obtain ⟨η, -, hgd⟩ := hgb.surjOn hdown
  obtain ⟨d, hd, rfl⟩ := exists_lift_mem_Ico η
  have hbne0 : b ≠ 0 := by
    rintro rfl
    rw [h0, Prod.mk.injEq] at hgb1
    norm_num at hgb1
  have hbnehalf : b ≠ 1 / 2 := by
    rintro rfl
    rw [hhalf, Prod.mk.injEq] at hgb1
    norm_num at hgb1
  have hdhalf : 1 / 2 < d := by
    by_contra hcon
    have hmem : ((0 : ℝ), (-1 : ℝ)) ∈ upperSpliceBoundary := by
      rw [← hA]
      exact ⟨((d : ℝ) : loopCircle), ⟨d, ⟨hd.1, not_lt.mp hcon⟩, rfl⟩, hgd⟩
    exact absurd hmem.2 (by norm_num)
  have hconf : IsSheetExchange Prod.swap g 0 b (1 / 2) d := by
    refine ⟨lt_of_le_of_ne hb.1 (Ne.symm hbne0), lt_of_le_of_ne hb.2 hbnehalf, hdhalf,
      by linarith [hd.2], Or.inl ?_, Or.inl ?_, Or.inr ?_, Or.inr ?_, ?_, ?_⟩
    · rw [h0, hgb1]
      rfl
    · rw [h0, hgb1]
      rfl
    · rw [hhalf, hgd]
      rfl
    · rw [hhalf, hgd]
      rfl
    · rw [h0, hhalf]
      intro hcon
      rw [Prod.mk.injEq] at hcon
      norm_num at hcon
    · rw [hgb1, hgd]
      intro hcon
      rw [Prod.mk.injEq] at hcon
      norm_num at hcon
  exact not_isPLCirclePositive_of_closedBranchCase1 mapsTo_swap_spliceSquareBoundary hgc hgb
    hconf (by rw [Prod.swap_swap])

/-- The coordinate swap is a piecewise linear homeomorphism of the square model of the disk. -/
theorem isPLHomeomorphOn_swap_spliceSquare :
    IsPLHomeomorphOn Prod.swap spliceSquare spliceSquare :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_spliceSquare.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope
      ((LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.fst ℝ ℝ ℝ)).toAffineMap isHPolytope_spliceSquare)
    ⟨fun _ hp => swap_mem_spliceSquare hp, Prod.swap_injective.injOn,
      fun p hp => ⟨p.swap, swap_mem_spliceSquare hp, Prod.swap_swap p⟩⟩

/-- The splice model of the first closed branch case has no orientable target.

Concretely: there is no cylindrical diagram over a triangulated square model of the disk
cross-section whose bottom-to-top end map is the coordinate swap and whose target complex `M`
is an orientable combinatorial three manifold with boundary.  This is the statement that a
closed branch whose complete preimage is a single circle double covering it cannot occur over
an orientable target, in the form the induction of Moise's Lemma 2 consumes.

Three inputs of that induction are hypotheses here rather than conclusions, and none of them is
proved in this file.

* That the first case tube of an actual closed branch carries such a diagram with end map
  `Prod.swap`.  `CylinderSplice` states the matching fact only conditionally, in
  `spliceRel_iff_of_isCylindricalDiagram`, and constructs no diagram.
* That the tube complex `M` is orientable.  `M.space` is the image of the whole diagram, so `M`
  is a triangulation of the tube carrying the orientation induced from an orientable ambient
  three manifold; producing `M` with that orientation from the ambient one is a separate step.
* That the one circle branch of
  `branchPreimage_isPLSphere_or_exists_two_isPLSpheres_of_not_boundaryBranch` is the case
  modelled here, with the two sheets meeting the cross-section in the four rays `spliceEnds`. -/
theorem not_isCylindricalDiagram_swap_of_isOrientable {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : (ℝ × ℝ) × ℝ → F}
    (D : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : D.space = spliceSquare)
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f D.space M.space)
    (hfu : ∀ x ∈ D.space, f (x, 0) = f (Prod.swap x, 1)) : False := by
  have hDball : IsPLBall 2 D.space := by
    rw [hD]
    exact isPLBall_spliceSquare
  have hswap : IsPLHomeomorphOn Prod.swap D.space D.space := by
    rw [hD]
    exact isPLHomeomorphOn_swap_spliceSquare
  have hpos := hf.boundary_isPLCirclePositive_of_bottom_eq_top D M hDball hM hor hswap hfu
  rw [← frontier_space_eq_boundaryComplex_space_of_finrank (d := _) (n := 1)
      (by simp [Module.finrank_prod]) D hDball.isCombinatorialManifoldWithBoundary, hD,
    ← spliceSquareBoundary_eq_frontier] at hpos
  exact not_isPLCirclePositive_spliceSquareBoundary_swap hpos

end PiecewiseLinear

end DifferentialGeometry.Topology
