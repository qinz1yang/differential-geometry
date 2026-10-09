import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspCollars
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryBandUpperDistance

/-!
The actual double cusp has two nearly cuspidal boundary components at every finite order.
Their ambient diameters follow from the original torus bound and the same metric scaling.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open GC.Seifert GC.GraphManifold GC.Endpoint Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem doubleCuspBoundary_distance (a : ℝ) (ha : 0 < a) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D)
    (K : ℕ) (i : Fin 2) {x y : annulusCircleCarrier.{u}.Carrier}
    (hx : x ∈ doubleCuspBoundary i) (hy : y ∈ doubleCuspBoundary i) :
    riemannianEDistOf (doubleCuspMetric a ha) x y ≤ ENNReal.ofReal (a * D) := by
  rw [← doubleCuspCollar_boundary_image] at hx hy
  rcases hx with ⟨t, rfl⟩
  rcases hy with ⟨t', rfl⟩
  have hp (v : Torus) : (v, halfZero) ∈ cuspDomain := by
    change (0 : ℝ) < 100
    norm_num
  have hu := (doubleCuspEmbedding.{u} a ha K i).riemannianEDistOf_le_flat (hp t) (hp t')
  have hscaled : riemannianEDistOf
      (scaleMetric (a ^ 2) (sq_pos_of_pos ha) standardCuspTorusMetric) t t' ≤
      ENNReal.ofReal (a * D) := by
    rw [edistOf_scale, Real.sqrt_sq ha.le, ENNReal.ofReal_mul ha.le]
    exact mul_le_mul' (le_refl (ENNReal.ofReal a)) (hbound t t')
  have hreal := ENNReal.toReal_mono (by simp) hscaled
  rw [ENNReal.toReal_ofReal (mul_nonneg ha.le hD)] at hreal
  change riemannianEDistOf (doubleCuspMetric a ha)
      (doubleCuspCollar i (t, halfZero)) (doubleCuspCollar i (t', halfZero)) ≤
    ENNReal.ofReal (Real.sqrt (1 + 0) * Real.sqrt ((0 - 0) ^ 2 +
      (riemannianEDistOf
        (scaleMetric (a ^ 2) (sq_pos_of_pos ha) standardCuspTorusMetric) t t').toReal ^ 2)) at hu
  simpa only [add_zero, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    Real.sqrt_one, one_mul, Real.sqrt_sq ENNReal.toReal_nonneg] using
    hu.trans (ENNReal.ofReal_le_ofReal (by simpa using hreal))

def doubleCuspNearlyCuspidalBoundary (a : ℝ) (ha : 0 < a) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D) (K : ℕ) :
    NearlyCuspidalBoundary annulusCircleCarrier.{u} (doubleCuspMetric a ha) K (a * D) where
  count := 2
  count_pos := by norm_num
  component := doubleCuspBoundary
  connected := doubleCuspBoundary_connected
  closed := doubleCuspBoundary_closed
  disjoint := doubleCuspBoundary_disjoint
  covers := doubleCuspBoundary_cover
  diameter i x hx y hy := doubleCuspBoundary_distance a ha D hD hbound K i hx hy
  collar i := (doubleCuspEmbedding a ha K i).weaken (mul_nonneg ha.le hD)

theorem doubleCuspNearlyCuspidalBoundary_count (a : ℝ) (ha : 0 < a) (D : ℝ)
    (hD : 0 ≤ D) (hbound : ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D) (K : ℕ) :
    (doubleCuspNearlyCuspidalBoundary.{u} a ha D hD hbound K).count = 2 := rfl

theorem doubleCuspNearlyCuspidalBoundary_component (a : ℝ) (ha : 0 < a) (D : ℝ)
    (hD : 0 ≤ D) (hbound : ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D)
    (K : ℕ) (i : Fin 2) :
    (doubleCuspNearlyCuspidalBoundary.{u} a ha D hD hbound K).component i =
      doubleCuspBoundary i := rfl

def doubleCuspNearlyCuspidalBoundaryAt (a : ℝ) (ha : 0 < a) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D)
    (K : ℕ) (w : ℝ) (hw : a * D ≤ w) :
    NearlyCuspidalBoundary annulusCircleCarrier.{u} (doubleCuspMetric a ha) K w :=
  (doubleCuspNearlyCuspidalBoundary a ha D hD hbound K).weaken hw

theorem doubleCuspNearlyCuspidalBoundaryAt_count (a : ℝ) (ha : 0 < a) (D : ℝ)
    (hD : 0 ≤ D) (hbound : ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D)
    (K : ℕ) (w : ℝ) (hw : a * D ≤ w) :
    (doubleCuspNearlyCuspidalBoundaryAt.{u} a ha D hD hbound K w hw).count = 2 := rfl

theorem doubleCuspNearlyCuspidalBoundaryAt_component (a : ℝ) (ha : 0 < a) (D : ℝ)
    (hD : 0 ≤ D) (hbound : ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D)
    (K : ℕ) (w : ℝ) (hw : a * D ≤ w) (i : Fin 2) :
    (doubleCuspNearlyCuspidalBoundaryAt.{u} a ha D hD hbound K w hw).component i =
      doubleCuspBoundary i := rfl

end DifferentialGeometry.Geometry.Collapse
