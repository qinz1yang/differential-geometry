import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockProfile
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Exact boundary marker at every contributing plane (blueprint 207B, BCG05, B:9202–9288)

Row-local kernels:
* `dist_center_lt_of_support_meet` — (BCG05.a): a smoothing center whose closed `80 b r_y` support
  meets `B(x, 8 b r_x)` is within `.025 ρ(p)` of `x` once `r_y ≤ 5r_x/3`, `r_x ≤ (5/3)Σρ(p)` and
  `b Σ ≤ 1/10000` (the printed `b = ε_j⁻¹`, `Σ_j ≤ ε_j/10000`).
* `abs_sub_lt_of_marker_division` — marker division `|η - t| < 79r/(1-r)`.
* `abs_sub_lt_and_boundaryProfile_eq_one_of_block_near` — at a band point `32 ≤ t ≤ 78` any height whose
  physical block is within `r < 10⁻⁴` has `|η - t| < .01` and marker exactly one.
The marker-one spectral step is W4-GAF's `Submodule.starProjection_eq_of_weighted_normal_section_eq_zero`
with `V = ℝ ∙ e`, `c = e`; the stage induction is `starProjection_stages_eq_of_contributors`
(`BlockIsolation.lean`); the model-plane marker kernel is `hasFDerivAt_modelBlock_snd_zero`
(`ModelBlock.lean`).
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

open DifferentialGeometry.Analysis

/-- (BCG05.a): the contributing center is within `250 b Σ ρ(p) ≤ .025 ρ(p)` of the core point. -/
theorem dist_center_lt_of_support_meet {d ry rx b σ ρp : ℝ} (hb : 0 ≤ b) (hrx : 0 ≤ rx)
    (hd : d < 80 * b * ry + 8 * b * rx) (hry : ry ≤ 5 * rx / 3) (hrxσ : rx ≤ 5 / 3 * (σ * ρp))
    (hbσ : b * σ ≤ 1 / 10000) (hρ : 0 ≤ ρp) :
    d < 250 * (b * σ) * ρp ∧ d < ρp / 40 := by
  have h1 : 80 * b * ry ≤ 80 * b * (5 * rx / 3) := mul_le_mul_of_nonneg_left hry (by positivity)
  have h2 : b * rx ≤ b * (5 / 3 * (σ * ρp)) := mul_le_mul_of_nonneg_left hrxσ hb
  have hbr : 0 ≤ b * rx := mul_nonneg hb hrx
  have hσρ : b * (σ * ρp) = (b * σ) * ρp := by ring
  have h3 : (b * σ) * ρp ≤ 1 / 10000 * ρp := mul_le_mul_of_nonneg_right hbσ hρ
  have hfirst : d < 250 * (b * σ) * ρp := by nlinarith
  refine ⟨hfirst, ?_⟩
  nlinarith

/-- Marker division: if the actual block `(ηζ, ζ)` with `ζ ≤ 1` is within `r` of `(t, 1)` with
`0 ≤ t ≤ 78`, then `|η - t| < 79 r/(1 - r)`. -/
theorem abs_sub_lt_of_marker_division {η t ζ r : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 78) (hζ1 : ζ ≤ 1)
    (hζ : 1 - r < ζ) (hu : |η * ζ - t| < r) (hr : r < 1) :
    |η - t| < 79 * r / (1 - r) := by
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hu.le
  have hζpos : 0 < ζ := by linarith
  have hkey : (η - t) * ζ = (η * ζ - t) + t * (1 - ζ) := by ring
  have hprod : |η - t| * ζ < 79 * r := by
    have habs : |(η - t) * ζ| ≤ |η * ζ - t| + t * (1 - ζ) := by
      rw [hkey]
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (mul_nonneg ht0 (by linarith))]
    rw [abs_mul, abs_of_pos hζpos] at habs
    have : t * (1 - ζ) ≤ 78 * r := by
      have h1 : t * (1 - ζ) ≤ t * r := mul_le_mul_of_nonneg_left (by linarith) ht0
      have h2 : t * r ≤ 78 * r := mul_le_mul_of_nonneg_right ht hr0
      linarith
    linarith
  rw [lt_div_iff₀ (by linarith)]
  have hlow : |η - t| * (1 - r) ≤ |η - t| * ζ :=
    mul_le_mul_of_nonneg_left hζ.le (abs_nonneg _)
  linarith

/-- With `r < 10⁻⁴` the marker-division bound is below `.01`. -/
theorem abs_sub_lt_hundredth_of_marker_division {η t ζ r : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 78)
    (hζ1 : ζ ≤ 1) (hζ : 1 - r < ζ) (hu : |η * ζ - t| < r) (hr : r < 1 / 10000) :
    |η - t| < 1 / 100 := by
  have h := abs_sub_lt_of_marker_division ht0 ht hζ1 hζ hu (by linarith)
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hu.le
  have hden : 0 < 1 - r := by linarith
  have : 79 * r / (1 - r) ≤ 1 / 100 := by
    rw [div_le_iff₀ hden]
    linarith
  linarith

/-- BCG05's marker step on the actual block: at a band point `32 ≤ t ≤ 78`, any height `s` whose
physical block is within `r < 10⁻⁴` of the block at `t` satisfies `31 < s < 79` and has boundary
marker exactly one. -/
theorem abs_sub_lt_and_boundaryProfile_eq_one_of_block_near {s t r : ℝ}
    (ht : t ∈ Icc (32 : ℝ) 78) (hnear : ‖boundaryBlock s - boundaryBlock t‖ < r)
    (hr : r < 1 / 10000) :
    |s - t| < 1 / 100 ∧ boundaryProfile s = 1 := by
  have hpt : boundaryProfile t = 1 := boundaryProfile_eq_one ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfst : |(boundaryBlock s - boundaryBlock t).1| < r :=
    (norm_fst_le (boundaryBlock s - boundaryBlock t)).trans_lt hnear
  have hsnd : |(boundaryBlock s - boundaryBlock t).2| < r :=
    (norm_snd_le (boundaryBlock s - boundaryBlock t)).trans_lt hnear
  simp only [Prod.fst_sub, Prod.snd_sub, boundaryBlock_fst, boundaryBlock_snd, hpt,
    mul_one] at hfst hsnd
  have hζ1 := (boundaryProfile_mem_Icc s).2
  have hζ : 1 - r < boundaryProfile s := by linarith [(abs_lt.mp hsnd).1]
  have hclose := abs_sub_lt_hundredth_of_marker_division (by linarith [ht.1]) ht.2 hζ1 hζ hfst hr
  refine ⟨hclose, boundaryProfile_eq_one ⟨?_, ?_⟩⟩
  · linarith [(abs_lt.mp hclose).1, ht.1]
  · linarith [(abs_lt.mp hclose).2, ht.2]

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
