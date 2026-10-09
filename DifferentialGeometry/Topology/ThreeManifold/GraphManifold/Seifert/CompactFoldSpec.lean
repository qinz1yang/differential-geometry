import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGerms

/-!
# The compact triangle fold: shared specification for the three curvatures

Lane CF (design `docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §0–§2
and §7, with the errata of review 23). This file fixes the interface consumed by B3 and the
statements the per-curvature lanes deliver.

**Shapes.** A `CompactShape` is an ordered triple of cone orders `pᵢ ≥ 2` with a curvature
`curv : CompactCurvature` matching the angle sum (`hyperbolic`: `Σ 1/pᵢ < 1`, `flat`: `= 1`,
`spherical`: `> 1`). The chart is the ε-model with `ε = eps = 1, 0, -1`: the unit disc with the
Poincaré metric, the plane, the stereographic chart of the sphere; `plane = {ε‖z‖² < 1}`.
The disc coordinate at `v` is `disc v z = (z - v)/(1 - ε v̄ z)`, an isometry onto the model
sending `v` to `0` (a disc automorphism, a translation, a rotation of the sphere); its inverse is
`discInv v`. The flat chart is normalised to circumdiameter one (sides `sin θₖ`, as `EuclidShape`);
for `ε = ±1`, `‖disc v z‖ = t_ε(d(z, v)/2)` with `t₁ = tanh`, `t₋₁ = tan`.

**Triangle.** `v₃ = 0`, `v₂ = t₂₃ > 0`, `v₁ = t₁₃ e^{iθ₃}` with the side tangents `sideTan` from the
ε-law of cosines (`cosh ℓ`, `cos ℓ` equal to `sideCos`; `sin θₖ` for `ε = 0`). The side functions
are `w₀ = Im z`, `w₁ = Im(e^{iθ₃} z̄)` and the polynomial
`w₂ = Im(-e^{iθ₂}(z - v₂) conj(1 - ε v̄₂ z)) = Im rotTwo · |1 - ε v̄₂ z|²` (`wallSide_two_eq`);
`triangle = plane ∩ {wᵢ ≥ 0}`. Rotated disc coordinates `rotOne = -e^{-iθ₃} disc v₁`,
`rotTwo = -e^{iθ₂} disc v₂` put the sector of `vⱼ` on `[0, θⱼ]`.
Reflections: `refl 0 = conj`, `refl 1 = e^{2iθ₃} conj`, `refl 2 = discInv v₂ ∘ (e^{-2iθ₂} conj) ∘
disc v₂`, the last one defined on its chart domain `reflChart 2` (both denominators nonzero).
Apex discs are taken over chart domains: `apexDisc v r = {1 - ε v̄ z ≠ 0 ∧ ‖disc v z‖ < r}`.

**Target and fold data.** `basePlusSeven = {‖u‖ < 7/2, Im u ≥ 0}`; the outer cone `v₃` goes to the
outer hole through `compactOuterGerm p₃`. `CompactShape.FoldData` collects: an open `U ⊆ plane`
with `T \ {0} ⊆ U`, `0 ∉ U`; a smooth `f` on `U` with positive Jacobian off `v₁, v₂`; open wall
neighbourhoods `V i ⊆ U ∩ reflChart i`, stable under `refl i`, containing `wall i \ {0}`, with
`f ∘ refl i = conj ∘ f`; `BijOn f (T \ {0}) basePlusSeven`; explicit apex radii with the germs
`3/2 + rotOne^{p₁}/2` on `apexDisc v₁`, `-3/2 + rotTwo^{p₂}/2` on `apexDisc v₂` and
`compactOuterGerm p₃` on the punctured disc about `0`. The double domain
`doubleDomain = (T ∪ refl₀ T) \ {0}`, the mirror extension `doubleFold` and the pairings
`pairThree = refl₀ refl₁`, `pairOne = refl₁ refl₂`, `pairTwo = refl₂ refl₀` are defined here.
The common profile slope is `compactProfileSlope = 2/5`; with the circumdiameter normalisation
`|Tⱼ| < 1` on `T` in all three curvatures (`tanh`, `tan` of half a side defect `< π/4`, the flat
bound `CompactFoldEuclidBridges.canon_lt_of_mem`), so `R₁, R₂ ∈ (11/10, 19/10)`,
`R₃ ∈ (13/5, 17/5)` (review 23 §4.4 concerned the `ρ = 1` scaling only).

**Deliverables per curvature** (lanes CF-H for `hyperbolic`, CF-S for `spherical`, in new files
`SF/CompactFoldHyp*.lean`, `SF/CompactFoldSph*.lean`; CF does `flat` through `EuclidShape`,
`toEuclidShape` and the `*_flat` lemmas below):
* T1, shape: bounds on `θᵢ`; side tangents in `(0, 1)` (resp. `(0, 1]`) with the ε-law of cosines;
  `wallSide i` vanishes at the vertices of wall `i`; `triangle` compact, inside `plane`, containing
  the vertices; `refl i` involutive on `reflChart i`,
  `wallSide i ∘ refl i = -(positive)·wallSide i`,
  `refl i z = z` on `wallSide i = 0`, `‖disc v ·‖` invariant for the vertices `v` on wall `i`;
  `rotOne`, `rotTwo` map `T` near `vⱼ` into the sector `[0, θⱼ]`; canonical radii `rⱼ`,
  `Tⱼ = t_ε((dⱼ - rⱼ)/2)` with `|Tⱼ| < 1` on `T`, `Tᵢ + Tⱼ = 0` on wall `ij` and the bracket
  factorisation `Tᵢ + Tⱼ = wᵢⱼ² Qᵢⱼ` with `Qᵢⱼ > 0` off the vertices.
* T2, maps: moduli `3/2 + κT₁`, `3/2 + κT₂`, `3 - κT₃` (`κ = compactProfileSlope`) with the
  bounds above; bridges `M₀, M₁, M₂` by `twoCircle`, smooth on the domains, positive polar
  Jacobians, `M ∘ refl = conj ∘ M`; the corners at `v₁`, `v₂` (apex blends) and at `v₃` (outer
  germ blend, modulus decreasing), positive Jacobian off the apices, wall identities where the
  weights are constant, strict angle derivatives including the wall branches.
* T3, assembly: incircle core layout (lens arc and switch windows in the shrunk core, parameters
  proportional to the inradius, uniform over the family), open pieces with one formula each and
  their cover of `T \ ({0} ∪ core)`, injectivity (structural separation of the branch images,
  per-branch injectivity, global angle order of the corner at `v₃`), `exists_core_replacement` on a
  Euclidean annulus, `MapsTo`, `Im > 0` inside, surjectivity (open–closed and the intermediate
  value theorem on the walls), wall neighbourhoods, and finally
  `exists_foldData_hyperbolic (σ) (h : σ.curv = .hyperbolic) : Nonempty σ.FoldData`
  (resp. `exists_foldData_spherical`).
* Generic, curvature-free (CF): wall images `(-7/2, -3/2]`, `[3/2, 7/2)`, `[-3/2, 3/2]` and
  `Im f > 0` on the open triangle from the fields, the quotient bijection on `doubleDomain`, the
  seam exports for B3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

inductive CompactCurvature
  | hyperbolic
  | flat
  | spherical
  deriving DecidableEq

namespace CompactCurvature

def eps : CompactCurvature → ℝ
  | hyperbolic => 1
  | flat => 0
  | spherical => -1

end CompactCurvature

def compactProfileSlope : ℝ := 2 / 5

def basePlusSeven : Set ℂ := {u | ‖u‖ < 7 / 2 ∧ 0 ≤ u.im}

structure CompactShape where
  curv : CompactCurvature
  p₁ : ℕ
  p₂ : ℕ
  p₃ : ℕ
  two_le_p₁ : 2 ≤ p₁
  two_le_p₂ : 2 ≤ p₂
  two_le_p₃ : 2 ≤ p₃
  angle_cond : (curv = .hyperbolic ∧ (1 / p₁ + 1 / p₂ + 1 / p₃ : ℝ) < 1) ∨
    (curv = .flat ∧ (1 / p₁ + 1 / p₂ + 1 / p₃ : ℝ) = 1) ∨
    (curv = .spherical ∧ 1 < (1 / p₁ + 1 / p₂ + 1 / p₃ : ℝ))

namespace CompactShape

variable (σ : CompactShape)

def eps : ℝ := σ.curv.eps

def θ₁ : ℝ := Real.pi / σ.p₁

def θ₂ : ℝ := Real.pi / σ.p₂

def θ₃ : ℝ := Real.pi / σ.p₃

def sideCos (a b c : ℝ) : ℝ := (Real.cos c + Real.cos a * Real.cos b) / (Real.sin a * Real.sin b)

def sideTan (a b c : ℝ) : ℝ :=
  match σ.curv with
  | .hyperbolic => Real.sqrt ((sideCos a b c - 1) / (sideCos a b c + 1))
  | .flat => Real.sin c
  | .spherical => Real.sqrt ((1 - sideCos a b c) / (1 + sideCos a b c))

def vertexOne : ℂ := (σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂ : ℂ) * exp (σ.θ₃ * I)

def vertexTwo : ℂ := (σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁ : ℂ)

def plane : Set ℂ := {z | σ.eps * ‖z‖ ^ 2 < 1}

def disc (v z : ℂ) : ℂ := (z - v) / (1 - σ.eps * conj v * z)

def discInv (v w : ℂ) : ℂ := (w + v) / (1 + σ.eps * conj v * w)

def apexDisc (v : ℂ) (r : ℝ) : Set ℂ := {z | 1 - σ.eps * conj v * z ≠ 0 ∧ ‖σ.disc v z‖ < r}

def rotOne (z : ℂ) : ℂ := -(exp (-((σ.θ₃ : ℂ) * I)) * σ.disc σ.vertexOne z)

def rotTwo (z : ℂ) : ℂ := -(exp ((σ.θ₂ : ℂ) * I) * σ.disc σ.vertexTwo z)

def wallSide : Fin 3 → ℂ → ℝ
  | 0 => fun z => z.im
  | 1 => fun z => (exp ((σ.θ₃ : ℂ) * I) * conj z).im
  | 2 => fun z => (-(exp ((σ.θ₂ : ℂ) * I) * ((z - σ.vertexTwo) *
      conj (1 - σ.eps * conj σ.vertexTwo * z)))).im

def triangle : Set ℂ := {z | z ∈ σ.plane ∧ ∀ i, 0 ≤ σ.wallSide i z}

def foldWall (i : Fin 3) : Set ℂ := {z | z ∈ σ.triangle ∧ σ.wallSide i z = 0}

def reflTwoAux (z : ℂ) : ℂ := exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (σ.disc σ.vertexTwo z)

def refl : Fin 3 → ℂ → ℂ
  | 0 => fun z => conj z
  | 1 => fun z => exp (2 * (σ.θ₃ : ℂ) * I) * conj z
  | 2 => fun z => σ.discInv σ.vertexTwo (σ.reflTwoAux z)

def reflChart : Fin 3 → Set ℂ
  | 0 => univ
  | 1 => univ
  | 2 => {z | 1 - σ.eps * conj σ.vertexTwo * z ≠ 0 ∧
      1 + σ.eps * conj σ.vertexTwo * σ.reflTwoAux z ≠ 0}

def pairThree (z : ℂ) : ℂ := σ.refl 0 (σ.refl 1 z)

def pairOne (z : ℂ) : ℂ := σ.refl 1 (σ.refl 2 z)

def pairTwo (z : ℂ) : ℂ := σ.refl 2 (σ.refl 0 z)

def doubleDomain : Set ℂ := (σ.triangle ∪ σ.refl 0 '' σ.triangle) \ {0}

def doubleFold (f : ℂ → ℂ) (z : ℂ) : ℂ := if 0 ≤ z.im then f z else conj (f (conj z))

structure FoldData where
  U : Set ℂ
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  U_subset_plane : U ⊆ σ.plane
  zero_not_mem_U : (0 : ℂ) ∉ U
  triangle_diff_subset_U : σ.triangle \ {0} ⊆ U
  contDiffOn_f : ContDiffOn ℝ ∞ f U
  det_fderiv_pos : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ f z).det
  V : Fin 3 → Set ℂ
  isOpen_V : ∀ i, IsOpen (V i)
  V_subset_U : ∀ i, V i ⊆ U
  V_subset_reflChart : ∀ i, V i ⊆ σ.reflChart i
  foldWall_diff_subset_V : ∀ i, σ.foldWall i \ {0} ⊆ V i
  refl_mapsTo_V : ∀ i, MapsTo (σ.refl i) (V i) (V i)
  f_refl : ∀ i, ∀ z ∈ V i, f (σ.refl i z) = conj (f z)
  bijOn_f : BijOn f (σ.triangle \ {0}) basePlusSeven
  apexRadius : Fin 3 → ℝ
  apexRadius_pos : ∀ i, 0 < apexRadius i
  f_apexOne : ∀ z ∈ σ.apexDisc σ.vertexOne (apexRadius 0),
    z ∈ U ∧ f z = 3 / 2 + σ.rotOne z ^ σ.p₁ / 2
  f_apexTwo : ∀ z ∈ σ.apexDisc σ.vertexTwo (apexRadius 1),
    z ∈ U ∧ f z = -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2
  f_outer : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < apexRadius 2 → z ∈ U ∧ f z = compactOuterGerm σ.p₃ z

theorem wallSide_two_eq (z : ℂ) : σ.wallSide 2 z =
    (σ.rotTwo z).im * Complex.normSq (1 - σ.eps * conj σ.vertexTwo * z) := by
  change (-(exp ((σ.θ₂ : ℂ) * I) * ((z - σ.vertexTwo) *
    conj (1 - σ.eps * conj σ.vertexTwo * z)))).im = _
  set D := 1 - σ.eps * conj σ.vertexTwo * z with hD
  by_cases h0 : D = 0
  · simp [h0]
  · have e : -(exp ((σ.θ₂ : ℂ) * I) * ((z - σ.vertexTwo) * conj D)) =
        σ.rotTwo z * (Complex.normSq D : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, rotTwo, disc, ← hD]
      field_simp
    rw [e, Complex.mul_im, ofReal_re, ofReal_im, mul_zero, zero_add]

theorem sum_inv_of_flat (h : σ.curv = .flat) : (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃ : ℝ) = 1 := by
  rcases σ.angle_cond with ⟨h', -⟩ | ⟨-, hs⟩ | ⟨h', -⟩
  · rw [h] at h'
    exact absurd h' (by decide)
  · exact hs
  · rw [h] at h'
    exact absurd h' (by decide)

def toEuclidShape (h : σ.curv = .flat) : EuclidShape where
  p₁ := σ.p₁
  p₂ := σ.p₂
  p₃ := σ.p₃
  two_le_p₁ := σ.two_le_p₁
  two_le_p₂ := σ.two_le_p₂
  two_le_p₃ := σ.two_le_p₃
  sum_inv := σ.sum_inv_of_flat h

section Flat

variable {σ}
variable (h : σ.curv = .flat)
include h

theorem eps_flat : σ.eps = 0 := by
  unfold eps
  rw [h]
  rfl

theorem sideTan_flat (a b c : ℝ) : σ.sideTan a b c = Real.sin c := by
  unfold sideTan
  rw [h]

theorem θ₁_flat : σ.θ₁ = (σ.toEuclidShape h).θ₁ := rfl

theorem θ₂_flat : σ.θ₂ = (σ.toEuclidShape h).θ₂ := rfl

theorem θ₃_flat : σ.θ₃ = (σ.toEuclidShape h).θ₃ := rfl

theorem vertexOne_flat : σ.vertexOne = (σ.toEuclidShape h).vertexOne := by
  rw [vertexOne, sideTan_flat h]
  rfl

theorem vertexTwo_flat : σ.vertexTwo = (σ.toEuclidShape h).vertexTwo := by
  rw [vertexTwo, sideTan_flat h]
  rfl

theorem plane_flat : σ.plane = univ := by
  ext z
  simp [plane, eps_flat h]

theorem disc_flat (v z : ℂ) : σ.disc v z = z - v := by
  simp [disc, eps_flat h]

theorem discInv_flat (v w : ℂ) : σ.discInv v w = w + v := by
  simp [discInv, eps_flat h]

theorem apexDisc_flat (v : ℂ) (r : ℝ) : σ.apexDisc v r = {z | ‖z - v‖ < r} := by
  ext z
  simp [apexDisc, eps_flat h, disc_flat h]

theorem rotOne_flat (z : ℂ) : σ.rotOne z = (σ.toEuclidShape h).rotOne z := by
  rw [rotOne, disc_flat h, vertexOne_flat h]
  rfl

theorem rotTwo_flat (z : ℂ) : σ.rotTwo z = (σ.toEuclidShape h).rotTwo z := by
  rw [rotTwo, disc_flat h, vertexTwo_flat h]
  rfl

theorem wallSide_flat (i : Fin 3) (z : ℂ) :
    σ.wallSide i z = (σ.toEuclidShape h).wallSide i z := by
  fin_cases i
  · rfl
  · rfl
  · change (-(exp ((σ.θ₂ : ℂ) * I) * ((z - σ.vertexTwo) *
      conj (1 - σ.eps * conj σ.vertexTwo * z)))).im = ((σ.toEuclidShape h).rotTwo z).im
    rw [eps_flat h, vertexTwo_flat h]
    simp only [ofReal_zero, zero_mul, sub_zero, map_one, mul_one]
    rfl

theorem triangle_flat : σ.triangle = (σ.toEuclidShape h).triangle := by
  ext z
  simp only [triangle, plane_flat h, mem_univ, true_and, wallSide_flat h]
  rfl

theorem foldWall_flat (i : Fin 3) :
    σ.foldWall i = {z | z ∈ (σ.toEuclidShape h).triangle ∧
      (σ.toEuclidShape h).wallSide i z = 0} := by
  ext z
  simp only [foldWall, triangle_flat h, wallSide_flat h, mem_ofPred_eq]

theorem refl_flat (i : Fin 3) (z : ℂ) : σ.refl i z = (σ.toEuclidShape h).refl i z := by
  fin_cases i
  · rfl
  · rfl
  · change σ.discInv σ.vertexTwo (σ.reflTwoAux z) = (σ.toEuclidShape h).vertexTwo +
      exp (-(2 * ((σ.toEuclidShape h).θ₂ : ℂ) * I)) * conj (z - (σ.toEuclidShape h).vertexTwo)
    rw [discInv_flat h, reflTwoAux, disc_flat h, vertexTwo_flat h, add_comm]
    rfl

theorem reflChart_flat (i : Fin 3) : σ.reflChart i = univ := by
  fin_cases i
  · rfl
  · rfl
  · ext z
    simp [reflChart, eps_flat h]

end Flat

end CompactShape

def EuclidShape.toCompactShape (σ : EuclidShape) : CompactShape where
  curv := .flat
  p₁ := σ.p₁
  p₂ := σ.p₂
  p₃ := σ.p₃
  two_le_p₁ := σ.two_le_p₁
  two_le_p₂ := σ.two_le_p₂
  two_le_p₃ := σ.two_le_p₃
  angle_cond := Or.inr (Or.inl ⟨rfl, σ.sum_inv⟩)

theorem EuclidShape.toCompactShape_curv (σ : EuclidShape) : σ.toCompactShape.curv = .flat := rfl

end GC.Seifert
