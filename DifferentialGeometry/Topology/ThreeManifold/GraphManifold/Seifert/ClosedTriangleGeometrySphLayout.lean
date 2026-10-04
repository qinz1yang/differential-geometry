import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphMoves
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGenericWalls

/-!
# The base layout of a spherical closed triangle fold (interface)

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §5, with
review 32 §5.4–5.5 and §6.1, §6.6). A `SphLayout K` for a spherical datum `K` (shape `σ`, fold
datum `D`, inner vertices `v₁`, `v₂`, outer vertex `0`) records the base pieces of the fold and
exactly the properties the lifts, the fold and the pair classification consume:
* three radii `ρⱼ ∈ (0, 1/2]`, `ρⱼ ≤ D.apexRadius`, and the vertex discs
  `discOneR K ρ₁ = {1 + v̄₁ z ≠ 0, ‖rotOne z‖ < ρ₁}` (CF's `apexDisc` with its denominator
  condition), `discTwoR K ρ₂` likewise, `discThreeR ρ₃ = {‖z‖ < ρ₃}`; on the inner discs
  `1 + v̄ⱼ z` lies in the slit plane and the screw charts have nonzero denominators; the discs
  (and the mirror disc of `v₁`) are pairwise disjoint and the disc of `v₁` lies in `Im z > 0`;
  the disc sectors `0 ≤ arg ≤ θⱼ` lie in the triangle and conversely triangle points of a disc lie
  in its closed sector;
* three open wall patches with `patchᵢ ⊆ V i`, the wall images of `f` (`Re f < -3/2` on patch 0,
  `> 3/2` on patch 1, `|Re f| < 3/2` and `|f|² < 25/4` on patch 2), stable under their reflection,
  reflecting into the open triangle when outside the triangle; the main set
  `sphMainSet = open triangle ∪ patches` avoids the three vertices, carries both gauges in the slit
  plane, meets its mirror only in patch 0 and never meets the mirror disc of `v₁`; on the main set
  points of a vertex disc lie in the good angular window `(-θⱼ/2, 3θⱼ/2)`;
* the real closing identity is supplied in the form a continuity argument proves: on patch 2 the
  gauge defect `ψ₁ z + ψ₁ (r₂ z) - ψ₂ z - ψ₂ (r₂ z)` is within `π` of `2 arg (1 + v₂ v₁)`
  (`patchTwo_window`); it vanishes on wall 2 (`psiS_sub_psiS_of_wall`) and is continuous, so the
  window is an open neighbourhood of the wall, and with `psiS_wallTwo_angle` (equality modulo
  `2π`) the identity is exact on the patch (`SphFold`);
* the cover `T \ {0} ⊆ sphMainSet ∪ discs`.
Intended choice (lane B3d2, `SF/ClosedTriangleGeometrySph{Discs,Patches,Cover}.lean`): radii
`min (apexRadius, 1/2, ρ₀)` with `ρ₀` from disjointness and the sector-in-triangle property; patches
as B3's flat patches (`V i`, wall margins `κ`, `Re f` ranges, angular wedges in the discs) cut
down by compactness margins and, for patch 2, by the window above; the mirror pole of the legs of
`(n, 2, 2)` (`r₀ v₁ = -1/v̄₁` when `v₁ = i`) is never in `sphMainSet` or in a disc (only in the
mirror disc of `v₁`, where the fold uses `S₃⁻¹`), so each gauge is used on its own branch only.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry GC.Geometry
open scoped Topology ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

def discOneR (K : SphDatum) (r : ℝ) : Set ℂ :=
  {z | 1 + conj K.σ.vertexOne * z ≠ 0 ∧ ‖K.σ.rotOne z‖ < r}

def discTwoR (K : SphDatum) (r : ℝ) : Set ℂ :=
  {z | 1 + conj K.σ.vertexTwo * z ≠ 0 ∧ ‖K.σ.rotTwo z‖ < r}

def discThreeR (r : ℝ) : Set ℂ := {z | ‖z‖ < r}

structure SphLayout (K : SphDatum) where
  radOne : ℝ
  radTwo : ℝ
  radThree : ℝ
  radOne_pos : 0 < radOne
  radTwo_pos : 0 < radTwo
  radThree_pos : 0 < radThree
  radOne_le_apex : radOne ≤ K.D.apexRadius 0
  radTwo_le_apex : radTwo ≤ K.D.apexRadius 1
  radThree_le_apex : radThree ≤ K.D.apexRadius 2
  radOne_le_half : radOne ≤ 1 / 2
  radTwo_le_half : radTwo ≤ 1 / 2
  radThree_le_half : radThree ≤ 1 / 2
  discOne_slit : ∀ z ∈ discOneR K radOne, 1 + conj K.σ.vertexOne * z ∈ slitPlane
  discTwo_slit : ∀ z ∈ discTwoR K radTwo, 1 + conj K.σ.vertexTwo * z ∈ slitPlane
  discOne_den : ∀ z ∈ discOneR K radOne, ∀ θ : ℝ,
    1 - conj K.σ.vertexOne * (exp (θ * I) * discV K.σ.vertexOne z) ≠ 0
  discTwo_den : ∀ z ∈ discTwoR K radTwo, ∀ θ : ℝ,
    1 - conj K.σ.vertexTwo * (exp (θ * I) * discV K.σ.vertexTwo z) ≠ 0
  discOne_im_pos : ∀ z ∈ discOneR K radOne, 0 < z.im
  disjoint_one_two : Disjoint (discOneR K radOne) (discTwoR K radTwo)
  disjoint_one_three : Disjoint (discOneR K radOne) (discThreeR radThree)
  disjoint_two_three : Disjoint (discTwoR K radTwo) (discThreeR radThree)
  disjoint_two_mirror : ∀ z ∈ discTwoR K radTwo, conj z ∉ discOneR K radOne
  disjoint_three_mirror : ∀ z ∈ discThreeR radThree, conj z ∉ discOneR K radOne
  discOne_sector : ∀ z ∈ discOneR K radOne, 0 ≤ arg (K.σ.rotOne z) →
    arg (K.σ.rotOne z) ≤ K.σ.θ₁ → z ∈ K.σ.triangle
  discTwo_sector : ∀ z ∈ discTwoR K radTwo, 0 ≤ arg (K.σ.rotTwo z) →
    arg (K.σ.rotTwo z) ≤ K.σ.θ₂ → z ∈ K.σ.triangle
  discThree_sector : ∀ z ∈ discThreeR radThree, 0 ≤ arg z → arg z ≤ K.σ.θ₃ → z ∈ K.σ.triangle
  triangle_sector_one : ∀ z ∈ K.σ.triangle, z ∈ discOneR K radOne → z ≠ K.σ.vertexOne →
    0 ≤ arg (K.σ.rotOne z) ∧ arg (K.σ.rotOne z) ≤ K.σ.θ₁
  triangle_sector_two : ∀ z ∈ K.σ.triangle, z ∈ discTwoR K radTwo → z ≠ K.σ.vertexTwo →
    0 ≤ arg (K.σ.rotTwo z) ∧ arg (K.σ.rotTwo z) ≤ K.σ.θ₂
  triangle_sector_three : ∀ z ∈ K.σ.triangle, z ∈ discThreeR radThree → z ≠ 0 →
    0 ≤ arg z ∧ arg z ≤ K.σ.θ₃
  patchZero : Set ℂ
  patchOne : Set ℂ
  patchTwo : Set ℂ
  isOpen_patchZero : IsOpen patchZero
  isOpen_patchOne : IsOpen patchOne
  isOpen_patchTwo : IsOpen patchTwo
  patchZero_spec : ∀ z ∈ patchZero, z ∈ K.D.V 0 ∧ (K.D.f z).re < -(3 / 2) ∧ conj z ∈ patchZero
  patchOne_spec : ∀ z ∈ patchOne,
    z ∈ K.D.V 1 ∧ 3 / 2 < (K.D.f z).re ∧ K.σ.refl 1 z ∈ patchOne
  patchTwo_spec : ∀ z ∈ patchTwo, z ∈ K.D.V 2 ∧ -(3 / 2) < (K.D.f z).re ∧
    (K.D.f z).re < 3 / 2 ∧ normSq (K.D.f z) < 25 / 4 ∧ K.σ.refl 2 z ∈ patchTwo
  patchZero_out : ∀ z ∈ patchZero, z ∉ K.σ.triangle → conj z ∈ K.σ.openTriangle
  patchOne_out : ∀ z ∈ patchOne, z ∉ K.σ.triangle → K.σ.refl 1 z ∈ K.σ.openTriangle
  patchTwo_out : ∀ z ∈ patchTwo, z ∉ K.σ.triangle → K.σ.refl 2 z ∈ K.σ.openTriangle
  main_ne : ∀ z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo,
    z ≠ 0 ∧ z ≠ K.σ.vertexOne ∧ z ≠ K.σ.vertexTwo
  main_slit : ∀ z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo,
    1 + conj K.σ.vertexOne * z ∈ slitPlane ∧ 1 + conj K.σ.vertexTwo * z ∈ slitPlane
  main_conj : ∀ z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo,
    conj z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo → z ∈ patchZero
  main_mirror : ∀ z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo,
    conj z ∉ discOneR K radOne
  main_window_one : ∀ z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo,
    z ∈ discOneR K radOne → -(K.σ.θ₁ / 2) < arg (K.σ.rotOne z) ∧
      arg (K.σ.rotOne z) < 3 * K.σ.θ₁ / 2
  main_window_two : ∀ z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo,
    z ∈ discTwoR K radTwo → -(K.σ.θ₂ / 2) < arg (K.σ.rotTwo z) ∧
      arg (K.σ.rotTwo z) < 3 * K.σ.θ₂ / 2
  main_window_three : ∀ z ∈ K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo,
    z ∈ discThreeR radThree → -(K.σ.θ₃ / 2) < arg z ∧ arg z < 3 * K.σ.θ₃ / 2
  rotTwo_vertexOne_real : exp (-(2 * (K.σ.θ₂ : ℂ) * I)) *
    conj (discV K.σ.vertexTwo K.σ.vertexOne) = discV K.σ.vertexTwo K.σ.vertexOne
  patchTwo_window : ∀ z ∈ patchTwo,
    |psiS K.σ.vertexOne z + psiS K.σ.vertexOne (K.σ.refl 2 z) - psiS K.σ.vertexTwo z -
      psiS K.σ.vertexTwo (K.σ.refl 2 z) - 2 * arg (1 + K.σ.vertexTwo * K.σ.vertexOne)| <
        Real.pi
  cover : K.σ.triangle \ {0} ⊆ (K.σ.openTriangle ∪ patchZero ∪ patchOne ∪ patchTwo) ∪
    discOneR K radOne ∪ discTwoR K radTwo ∪ discThreeR radThree

namespace SphLayout

variable {K : SphDatum} (L : SphLayout K)

def mainSet : Set ℂ := K.σ.openTriangle ∪ L.patchZero ∪ L.patchOne ∪ L.patchTwo

def discOne : Set ℂ := discOneR K L.radOne

def discTwo : Set ℂ := discTwoR K L.radTwo

def discThree : Set ℂ := discThreeR L.radThree

def discOneMirror : Set ℂ := {z | conj z ∈ L.discOne}

end SphLayout

end Sph

end ClosedTriangle

end GC.Seifert
