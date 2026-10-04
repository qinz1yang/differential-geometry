import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# LFR11, metric pieces: the Euclidean coordinate of an exact splitting from squared distances

Blueprint 207A, LFR11 (`thm:collapse-exact-splitting-regularity`, A:25566–25672), first step of the
proof: for a distance isometry `I : N ≃ᵢ ℝ^j × Y` (`ℓ²` product), `p ∈ N` with `I p = (u₀, y₀)`
and the two auxiliary points `a_± = I⁻¹(u₀ ± s v, y₀)`,
`⟪t(x) - u₀, v⟫ = (d(x, a₋)² - d(x, a₊)²) / (4 s)`, where `t = π_{ℝ^j} ∘ I`
(`inner_fst_sub_eq_sq_dist_sub`). This is the identity that makes `t` as regular as squared
distance functions; it holds for any inner-product first factor and any vector `v`, with no unit
normalisation. The other metric pieces of LFR11 are already in the tree: the slice
`{x | (I x).fst = u}` is isometric to `Y` (`IsometryEquiv.l2ProductSlice`), and every point `z`
with `d(x,z) + d(z,y) = d(x,y)` for `x, y` in one slice lies in that slice
(`WithLp.fst_eq_of_dist_add_eq`); `slice_mem_of_dist_add_eq` restates the latter on `N`.

The differentiable conclusions of LFR11 need finite-regularity Riemannian geometry (sheet
addendum, G11.1–G11.5) and are not proved here.
-/

set_option autoImplicit false

open WithLp

namespace GC.MetricGeometry

variable {N F Y : Type*} [MetricSpace N] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MetricSpace Y]

/-- **LFR11, coordinate from squared distances.** -/
theorem inner_fst_sub_eq_sq_dist_sub (I : N ≃ᵢ WithLp 2 (F × Y)) (x : N) (u₀ : F) (y₀ : Y)
    (v : F) {s : ℝ} (hs : s ≠ 0) :
    inner ℝ ((I x).fst - u₀) v =
      (dist x (I.symm (toLp 2 (u₀ - s • v, y₀))) ^ 2 -
        dist x (I.symm (toLp 2 (u₀ + s • v, y₀))) ^ 2) / (4 * s) := by
  rw [← I.dist_eq, ← I.dist_eq, I.apply_symm_apply, I.apply_symm_apply,
    prod_dist_sq_eq_add_sq, prod_dist_sq_eq_add_sq]
  simp only [toLp_fst, toLp_snd, dist_eq_norm]
  rw [eq_div_iff (by positivity : (4 : ℝ) * s ≠ 0),
    show (I x).fst - (u₀ - s • v) = ((I x).fst - u₀) + s • v by abel,
    show (I x).fst - (u₀ + s • v) = ((I x).fst - u₀) - s • v by abel]
  have h1 := norm_add_sq_real ((I x).fst - u₀) (s • v)
  have h2 := norm_sub_sq_real ((I x).fst - u₀) (s • v)
  rw [real_inner_smul_right] at h1 h2
  rw [h1, h2]
  ring

/-- **LFR11, slices are closed under metric segments**, stated on `N`: if `x, y` lie in the slice
`(I ·).fst = u` and `d(x,z) + d(z,y) = d(x,y)`, then `z` lies in the same slice. -/
theorem slice_mem_of_dist_add_eq {E : Type*} [MetricSpace E] (I : N ≃ᵢ WithLp 2 (E × Y))
    {u : E} {x y z : N} (hx : (I x).fst = u) (hy : (I y).fst = u)
    (hz : dist x z + dist z y = dist x y) : (I z).fst = u := by
  have hxe : I x = toLp 2 (u, (I x).snd) := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext hx rfl
  have hye : I y = toLp 2 (u, (I y).snd) := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext hy rfl
  apply WithLp.fst_eq_of_dist_add_eq u (I x).snd (I y).snd (I z)
  have hxy : dist x y = dist (I x).snd (I y).snd :=
    calc dist x y = dist (I x) (I y) := (I.dist_eq x y).symm
      _ = dist (toLp 2 (u, (I x).snd)) (toLp 2 (u, (I y).snd)) := by rw [← hxe, ← hye]
      _ = dist (I x).snd (I y).snd := (WithLp.isometry_prodMk_left (Y := Y) u).dist_eq (I x).snd (I y).snd
  rw [← hxe, ← hye, I.dist_eq, I.dist_eq, ← hxy, hz]

end GC.MetricGeometry
