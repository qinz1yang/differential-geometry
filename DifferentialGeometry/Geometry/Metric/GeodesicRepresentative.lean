import DifferentialGeometry.Topology.MetricSpace.SegmentExtension

set_option autoImplicit false

open Set Metric

namespace Metric

structure GeodesicRepresentative {X : Type*} [MetricSpace X] (p : X) where
  length : ℝ
  length_pos : 0 < length
  curve : Icc (0 : ℝ) length → X
  isometry : Isometry curve
  start : curve ⟨0, le_rfl, length_pos.le⟩ = p

namespace GeodesicRepresentative

variable {X : Type*} [MetricSpace X] {p : X}

noncomputable def path (σ : GeodesicRepresentative p) : ℝ → X :=
  IccExtend σ.length_pos.le σ.curve

theorem path_of_mem (σ : GeodesicRepresentative p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) σ.length) : σ.path t = σ.curve ⟨t, ht⟩ :=
  IccExtend_of_mem σ.length_pos.le σ.curve ht

theorem path_zero (σ : GeodesicRepresentative p) : σ.path 0 = p := by
  rw [σ.path_of_mem ⟨le_rfl, σ.length_pos.le⟩, σ.start]

theorem dist_path (σ : GeodesicRepresentative p) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) σ.length) (ht : t ∈ Icc (0 : ℝ) σ.length) :
    dist (σ.path s) (σ.path t) = |s - t| :=
  σ.isometry.dist_IccExtend σ.length_pos.le hs ht

theorem dist_base_path (σ : GeodesicRepresentative p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) σ.length) : dist p (σ.path t) = t := by
  simpa only [σ.path_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] using
    σ.dist_path ⟨le_rfl, σ.length_pos.le⟩ ht

def shorten (σ : GeodesicRepresentative p) {r : ℝ} (hr : 0 < r)
    (hle : r ≤ σ.length) : GeodesicRepresentative p where
  length := r
  length_pos := hr
  curve := fun t => σ.curve ⟨t, t.property.1, t.property.2.trans hle⟩
  isometry := by
    apply Isometry.of_dist_eq
    intro s t
    rw [σ.isometry.dist_eq]
    rfl
  start := σ.start

theorem shorten_path (σ : GeodesicRepresentative p) {r : ℝ} (hr : 0 < r)
    (hle : r ≤ σ.length) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) r) :
    (σ.shorten hr hle).path t = σ.path t := by
  rw [(σ.shorten hr hle).path_of_mem ht,
    σ.path_of_mem ⟨ht.1, ht.2.trans hle⟩]
  rfl

instance [Subsingleton X] : IsEmpty (GeodesicRepresentative p) := by
  refine ⟨fun σ => ?_⟩
  have h := σ.dist_base_path ⟨σ.length_pos.le, le_rfl⟩
  have hz : dist p (σ.path σ.length) = 0 := dist_eq_zero.mpr (Subsingleton.elim _ _)
  exact σ.length_pos.ne (hz.symm.trans h)

end GeodesicRepresentative

end Metric
