import DifferentialGeometry.Geometry.Collapse.MetricRank.KLRelax
import DifferentialGeometry.Geometry.Collapse.MetricRank.ProductIsometries

/-!
# A product approximation is a `k`-splitting (S-X144c, group G10)

`HasEuclideanSplitting p k ε` asks for a Kleiner-Lott approximation at tolerance `ε` into
`ℝᵏ ×₂ Y` with the base point `p ↦ (0, q)`. The thin product approximations of the rank kernels
(`ApproxDistortion`, `ApproxRankWiring`) are into `A ×₂ Z` with `A = ℝ` (line) or `A = ℝ²`
(plane) and an arbitrary base point `p ↦ (a, z)`. Two steps connect them:

* `KleinerLottApprox.transportTo_SMR` : transport of a Kleiner-Lott approximation along an
  isometry of the target (map `e ∘ f`, base point `e q`, same tolerance);
* `exists_splitting_of_product_SMR` : for `e : A ≃ᵢ ℝᵏ` with `e a = 0`, an approximation
  `p ↦ (a, z)` into `A ×₂ Z` at tolerance `δ` is a `k`-splitting at every tolerance `β` with
  `2 δ ≤ β < 1` (translation to the origin inside `e`, the isometry `prodCongrLeft_SMR e`, then
  the relaxation `HasEuclideanSplitting.relax_SMR` of group G9; with `β = δ` no relaxation).

The case `A = ℝᵏ` itself (any `k`, `e v = v − a`) is `exists_splitting_of_thin_product_SMR`, the
plane (`k = 2`) is `exists_splitting_of_thin_product_plane_SMR`, and the line with the factor `ℝ`
instead of `ℝ¹` (`e x = !₂[x − a]`, `k = 1`) is `exists_splitting_of_thin_product_line_SMR`.

The smallness of the second factor `Z` (diameter `≤ D`, `δ + D ≤ 1/100`) is *not* needed for the
existence of the splitting (the factor `Y` of `HasEuclideanSplitting` is arbitrary); it is needed
only for the exclusion of higher ranks and is assumed by the rank theorems of `ThinOnlyRank`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v w

section Transport

variable {X : Type u} {Y : Type v} {Y' : Type w} [MetricSpace X] [MetricSpace Y]
  [MetricSpace Y'] {p : X} {q : Y} {δ : ℝ}

/-- **Transport along an isometry of the target.** `e ∘ f` is a Kleiner-Lott `δ`-approximation at
`p ↦ e q` (and hence at any `q'` with `e q = q'`). -/
def KleinerLottApprox.transportTo_SMR (f : KleinerLottApprox p q δ) (e : Y ≃ᵢ Y') {q' : Y'}
    (hq : e q = q') : KleinerLottApprox p q' δ where
  error_pos := f.error_pos
  error_lt_one := f.error_lt_one
  toFun x := e (f.toFun x)
  basepoint := by rw [f.basepoint, hq]
  distortion x hx x' hx' := by
    rw [e.dist_eq]
    exact f.distortion x hx x' hx'
  coverage y hy := by
    have hy' : dist (e.symm y) q < δ⁻¹ - δ := by
      have h : dist (e.symm y) (e.symm q') = dist y q' := e.symm.dist_eq y q'
      have hq' : e.symm q' = q := by rw [← hq, e.symm_apply_apply]
      rw [hq'] at h
      rw [h]
      exact hy
    have h := Metric.infDist_image e.isometry (x := e.symm y) (t := f.toFun '' Metric.ball p δ⁻¹)
    rw [e.apply_symm_apply, Set.image_image] at h
    rw [h]
    exact f.coverage (e.symm y) hy'

end Transport

section Splitting

variable {X : Type u} [MetricSpace X] {p : X} {δ β : ℝ}
  {A : Type*} [MetricSpace A] {Z : Type v} [MetricSpace Z] {a : A} {z : Z}

/-- **A product approximation `p ↦ (a, z)` into `A ×₂ Z` with `A ≃ᵢ ℝᵏ` is a `k`-splitting.** -/
theorem exists_splitting_of_product_SMR (k : ℕ) (e : A ≃ᵢ EuclideanSpace ℝ (Fin k)) (hea : e a = 0)
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hβ : 2 * δ ≤ β) (hβ1 : β < 1) :
    HasEuclideanSplitting.{u, v} p k β := by
  have h : HasEuclideanSplitting.{u, v} p k δ :=
    ⟨Z, inferInstance, z, ⟨f.transportTo_SMR (prodCongrLeft_SMR e)
      (by rw [prodCongrLeft_apply_SMR, hea])⟩⟩
  exact h.relax_SMR hβ hβ1

/-- **A product approximation into `ℝᵏ ×₂ Z` is a `k`-splitting.** The target is exactly the
product of `HasEuclideanSplitting`, at an arbitrary base point `(a, z)`; the approximation at
tolerance `δ` gives the `k`-splitting at every `β` with `2 δ ≤ β < 1` (translation by `−a`). -/
theorem exists_splitting_of_thin_product_SMR (k : ℕ) {a : EuclideanSpace ℝ (Fin k)}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hβ : 2 * δ ≤ β) (hβ1 : β < 1) :
    HasEuclideanSplitting.{u, v} p k β :=
  exists_splitting_of_product_SMR k (IsometryEquiv.subRight a) (by simp) f hβ hβ1

/-- **Thin line.** An approximation into `ℝ ×₂ Z` (at any base point `(a, z)`) at tolerance `δ` is
a one-splitting at every `β` with `2 δ ≤ β < 1`. -/
theorem exists_splitting_of_thin_product_line_SMR {a : ℝ}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hβ : 2 * δ ≤ β) (hβ1 : β < 1) :
    HasEuclideanSplitting.{u, v} p 1 β :=
  exists_splitting_of_product_SMR 1
    ((IsometryEquiv.subRight a).trans realEuclideanOneIso_SMR) (by simp [realEuclideanOneIso_SMR])
    f hβ hβ1

/-- **Thin plane.** An approximation into `ℝ² ×₂ Z` at tolerance `δ` is a two-splitting at every
`β` with `2 δ ≤ β < 1`. -/
theorem exists_splitting_of_thin_product_plane_SMR {a : EuclideanSpace ℝ (Fin 2)}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hβ : 2 * δ ≤ β) (hβ1 : β < 1) :
    HasEuclideanSplitting.{u, v} p 2 β :=
  exists_splitting_of_thin_product_SMR 2 f hβ hβ1

end Splitting

end GC.MetricGeometry
