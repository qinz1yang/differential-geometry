import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  [SigmaCompactSpace W]

omit [SigmaCompactSpace W] in
theorem exists_finiteHorn_neck_precision_eq_of_le {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) {alpha : ℝ} (halpha : 0 < alpha) (hsmall : alpha < 1 / 11)
    (hle : H.neck_precision ≤ alpha) :
    ∃ H' : FiniteHorn g, H'.neck_precision = alpha ∧ H'.collar_depth = H.collar_depth := by
  have horder : Nat.ceil alpha⁻¹ ≤ Nat.ceil H.neck_precision⁻¹ :=
    Nat.ceil_le_ceil (inv_anti₀ H.neck_precision_pos hle)
  refine ⟨{ H with
    neck_precision := alpha
    neck_precision_pos := halpha
    neck_precision_small := hsmall
    cylindrical_tail := ?_ }, rfl, rfl⟩
  obtain ⟨i, hi⟩ := H.cylindrical_tail
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨cyl, F, p, hcenter, hcross, hsource, hQ, hcmp⟩ := hi x hx
  obtain ⟨cmp⟩ := hcmp
  exact ⟨cyl, F, p, hcenter, hcross, hsource, hQ, ⟨cmp.mono (subset_refl _) horder hle⟩⟩

omit [SigmaCompactSpace W] in
theorem exists_finiteHorn_neck_precision_eq_iff_le {g : SmoothRiemannianMetric I3 W} {alpha : ℝ}
    (halpha : 0 < alpha) (hsmall : alpha < 1 / 11) :
    (∃ H : FiniteHorn g, H.neck_precision = alpha) ↔
      ∃ H : FiniteHorn g, H.neck_precision ≤ alpha :=
  ⟨fun ⟨H, hH⟩ => ⟨H, hH.le⟩,
    fun ⟨H, hH⟩ => (exists_finiteHorn_neck_precision_eq_of_le H halpha hsmall hH).imp
      fun _ h => h.1⟩

omit [SigmaCompactSpace W] in
theorem exists_finiteHorn_collar_depth_eq_of_le {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) {collar : ℝ} (hcollar : 0 < collar) (hle : collar ≤ H.collar_depth) :
    ∃ H' : FiniteHorn g, H'.collar_depth = collar ∧ H'.neck_precision = H.neck_precision := by
  have hsource : (Set.univ : Set (Sphere 2)) ×ˢ Set.Icc (-collar) collar ⊆
      (Set.univ : Set (Sphere 2)) ×ˢ Set.Icc (-H.collar_depth) H.collar_depth := by
    rintro ⟨a, b⟩ ⟨-, hb⟩
    exact ⟨trivial, Set.Icc_subset_Icc (by linarith) hle hb⟩
  refine ⟨{ H with
    collar_depth := collar
    collar_depth_pos := hcollar
    cylindrical_tail := ?_ }, rfl, rfl⟩
  obtain ⟨i, hi⟩ := H.cylindrical_tail
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨cyl, F, p, hcenter, hcross, hsource', hQ, hcmp⟩ := hi x hx
  obtain ⟨cmp⟩ := hcmp
  exact ⟨cyl, F, p, hcenter, hcross, Set.Subset.trans hsource hsource', hQ,
    ⟨cmp.mono hsource le_rfl le_rfl⟩⟩

omit [SigmaCompactSpace W] in
theorem exists_finiteHorn_collar_depth_eq_iff_le {g : SmoothRiemannianMetric I3 W} {collar : ℝ}
    (hcollar : 0 < collar) :
    (∃ H : FiniteHorn g, H.collar_depth = collar) ↔
      ∃ H : FiniteHorn g, collar ≤ H.collar_depth :=
  ⟨fun ⟨H, hH⟩ => ⟨H, hH.symm.le⟩,
    fun ⟨H, hH⟩ => (exists_finiteHorn_collar_depth_eq_of_le H hcollar hH).imp fun _ h => h.1⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
