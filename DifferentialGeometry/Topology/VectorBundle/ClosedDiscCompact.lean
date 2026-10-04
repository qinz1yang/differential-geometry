import DifferentialGeometry.Topology.VectorBundle.Compactness
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact closed discs in a finite-dimensional Riemannian vector bundle

The base is compact and the actual fiber norm is continuous in vector-bundle charts. Closed
radius discs and spheres are compact. The fiber radius is proper, also after an actual
homeomorphism of the total space to another carrier.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology.VectorBundle

variable {B : Type*} [TopologicalSpace B] [CompactSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]

theorem isCompact_closedDiscBundle (R : ℝ) :
    IsCompact {z : TotalSpace F V | ‖z.2‖ ≤ R} := by
  have h := isCompact_univ.bundle_norm_le (F := F) (V := V) R
  simpa only [mem_univ, true_and] using h

theorem isCompact_sphereBundle (R : ℝ) :
    IsCompact {z : TotalSpace F V | ‖z.2‖ = R} := by
  have h := isCompact_univ.bundle_norm_eq (F := F) (V := V) R
  simpa only [mem_univ, true_and] using h

omit [CompactSpace B] [FiniteDimensional ℝ F] in
theorem continuous_fiberRadius : Continuous (fun z : TotalSpace F V => ‖z.2‖) := by
  have hi : Continuous (fun z : TotalSpace F V => inner ℝ z.2 z.2) :=
    continuous_id.inner_bundle continuous_id
  simpa only [← norm_eq_sqrt_real_inner] using hi.sqrt

theorem isProperMap_fiberRadius : IsProperMap (fun z : TotalSpace F V => ‖z.2‖) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_fiberRadius, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hsub : (fun z : TotalSpace F V => ‖z.2‖) ⁻¹' K ⊆ {z | ‖z.2‖ ≤ R} := by
    intro z hz
    have h := hR hz
    change ‖z.2‖ ≤ R
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_norm] using h
  exact (isCompact_closedDiscBundle R).of_isClosed_subset
    (hK.isClosed.preimage continuous_fiberRadius) hsub

theorem isProperMap_transportedFiberRadius {N : Type*} [TopologicalSpace N]
    (e : TotalSpace F V ≃ₜ N) : IsProperMap (fun y : N => ‖(e.symm y).2‖) :=
  isProperMap_fiberRadius.comp e.symm.isProperMap

theorem isCompact_transportedClosedDiscBundle {N : Type*} [TopologicalSpace N]
    (e : TotalSpace F V ≃ₜ N) (R : ℝ) :
    IsCompact (e '' {z : TotalSpace F V | ‖z.2‖ ≤ R}) :=
  (isCompact_closedDiscBundle R).image e.continuous

theorem circleLineBundle_closedDisc_compact_and_radius_proper :
    IsCompact {z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) | |z.2| ≤ 2} ∧
      IsProperMap (fun z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) => |z.2|) := by
  constructor
  · simpa only [Real.norm_eq_abs] using
      (isCompact_closedDiscBundle (B := Circle) (F := ℝ) (V := Bundle.Trivial Circle ℝ) 2)
  · simpa only [Real.norm_eq_abs] using
      (isProperMap_fiberRadius (B := Circle) (F := ℝ) (V := Bundle.Trivial Circle ℝ))

end DifferentialGeometry.Topology.VectorBundle
