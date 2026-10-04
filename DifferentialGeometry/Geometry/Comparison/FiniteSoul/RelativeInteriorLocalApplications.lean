import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeInteriorLocal

/-!
# Consumers of the local S3-SLICE results (lane CMS3-SLICE, group G2)

* `maxSliceLocusOfOrder_local_package`: for a nonempty totally convex `C` of a complete finite-order
  metric (`2 ≤ r`), the relative interior is nonempty, a totally geodesic `C^r` slice of the relative
  dimension, and relatively open (`C ∩ O`);
* `top_slices_eq_near_finite`: two top-dimensional slices of `C` through a point agree near it;
* `exists_slice_succ_of_not_relOpen`: a slice of `C` that is not relatively open near one of its points
  forces a slice of one more dimension (the cone step read contrapositively).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The local package of S3-SLICE for a nonempty totally convex set. -/
theorem maxSliceLocusOfOrder_local_package
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCne : C.Nonempty) (hC : IsTotallyConvexFinite g C) :
    (maxSliceLocusOfOrder I (r : ℕ∞ω) C).Nonempty ∧
      IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C)
        (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      IsTotallyGeodesicFinite g (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      ∃ O : Set M, IsOpen O ∧ C ∩ O = maxSliceLocusOfOrder I (r : ℕ∞ω) C :=
  ⟨maxSliceLocusOfOrder_nonempty hCne,
    isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr hnorm hC,
    isTotallyGeodesicFinite_maxSliceLocusOfOrder g hr hnorm hC,
    exists_isOpen_inter_eq_maxSliceLocusOfOrder g hr hnorm hC⟩

/-- **Local uniqueness of top slices.** Two top-dimensional slices of the totally convex `C` through
`x` agree near `x`. -/
theorem top_slices_eq_near_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C N₁ N₂ : Set M} (hC : IsTotallyConvexFinite g C)
    (hN₁ : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C) N₁)
    (hN₂ : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C) N₂)
    (h₁ : N₁ ⊆ C) (h₂ : N₂ ⊆ C) {x : M} (hx₁ : x ∈ N₁) (hx₂ : x ∈ N₂) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ∩ N₁ = U ∩ N₂ := by
  obtain ⟨U₁, hU₁, hxU₁, hE₁⟩ := maxSlice_eq_near_finite g hr hnorm hC hN₁ h₁ hx₁
  obtain ⟨U₂, hU₂, hxU₂, hE₂⟩ := maxSlice_eq_near_finite g hr hnorm hC hN₂ h₂ hx₂
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hxU₁, hxU₂⟩, ?_⟩
  have e₁ : U₁ ∩ U₂ ∩ N₁ = U₁ ∩ U₂ ∩ C := by
    rw [inter_assoc, inter_comm U₂, ← inter_assoc, ← hE₁, inter_assoc, inter_comm C,
      ← inter_assoc]
  have e₂ : U₁ ∩ U₂ ∩ N₂ = U₁ ∩ U₂ ∩ C := by
    rw [inter_assoc, ← hE₂, ← inter_assoc]
  rw [e₁, e₂]

/-- **Cone step, contrapositive form.** If a `d`-slice `N ⊆ C` is not relatively open in `C` at
`p ∈ N`, then `C` contains a nonempty `(d + 1)`-slice. -/
theorem exists_slice_succ_of_not_relOpen
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C N : Set M} {d : ℕ} (hC : IsTotallyConvexFinite g C)
    (hN : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d N) (hNC : N ⊆ C) {p : M} (hpN : p ∈ N)
    (hnot : ∀ U : Set M, IsOpen U → p ∈ U → ¬ (C ∩ U ⊆ N)) :
    ∃ S : Set M, S.Nonempty ∧ S ⊆ C ∧ IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (d + 1) S := by
  refine exists_slice_succ_finite g hr hnorm hC hN hNC hpN ?_
  rw [_root_.mem_closure_iff]
  intro U hU hpU
  by_contra hempty
  apply hnot U hU hpU
  intro y hy
  by_contra hyN
  exact hempty ⟨y, hy.2, hy.1, hyN⟩

end DifferentialGeometry.Geometry.FiniteSoul
