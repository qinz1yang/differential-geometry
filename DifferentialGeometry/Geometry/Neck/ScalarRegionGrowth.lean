import DifferentialGeometry.Geometry.Neck.SpatialChart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

open Set
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M}

theorem SpatialNeck.scalar_le_on_union_region
    {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    {W V A : Set M} (hV : V ⊆ W ∪ A) (hp : p ∈ W)
    (hA : A ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    {B : ℝ} (hB : ∀ x ∈ W, metricScalarAt g x ≤ B) :
    ∀ x ∈ V, metricScalarAt g x ≤ (1 + 4323 * eps) * B := by
  have hBpos : 0 < B := nk.Q_pos.trans_le (hB p hp)
  have hBmul : B ≤ (1 + 4323 * eps) * B := by nlinarith [nk.eps_pos]
  intro x hx
  rcases hV hx with hxW | hxA
  · exact (hB x hxW).trans hBmul
  · exact (nk.scalar_bounds_on_image_window (hA hxA)).2.trans
      (mul_le_mul_of_nonneg_left (hB p hp) (by have := nk.eps_pos; positivity))

theorem SpatialNeck.scalar_le_on_union_slab
    {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (P : PartialDiffeomorph IC I3 Cylinder M ∞) {W V : Set M}
    (hV : V = W ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1)) (hp : p ∈ W)
    (hP : P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    {B : ℝ} (hB : ∀ x ∈ W, metricScalarAt g x ≤ B) :
    ∀ x ∈ V, metricScalarAt g x ≤ (1 + 4323 * eps) * B :=
  nk.scalar_le_on_union_region hV.subset hp hP hB

theorem scalar_le_mul_prod_of_neck_region_growth
    (W A : ℕ → Set M) (eps : ℕ → ℝ) (p : ℕ → M)
    (nk : ∀ n, SpatialNeck g (eps n) (p n))
    (hnext : ∀ n, W (n + 1) ⊆ W n ∪ A n)
    (hcenter : ∀ n, p n ∈ W n)
    (hcontrolled : ∀ n, A n ⊆ (nk n).map '' (univ ×ˢ Ioo (-(eps n)⁻¹) (eps n)⁻¹))
    {B : ℝ} (hinitial : ∀ x ∈ W 0, metricScalarAt g x ≤ B) :
    ∀ n, ∀ x ∈ W n,
      metricScalarAt g x ≤ (∏ j ∈ Finset.range n, (1 + 4323 * eps j)) * B := by
  intro n
  induction n with
  | zero => simpa only [Finset.range_zero, Finset.prod_empty, one_mul] using hinitial
  | succ n ih =>
    have hstep := (nk n).scalar_le_on_union_region (hnext n) (hcenter n) (hcontrolled n) ih
    simpa only [Finset.prod_range_succ, mul_assoc, mul_left_comm, mul_comm] using hstep

theorem scalar_le_mul_pow_of_neck_region_growth
    (W A : ℕ → Set M) {eps : ℝ} (p : ℕ → M)
    (nk : ∀ n, SpatialNeck g eps (p n))
    (hnext : ∀ n, W (n + 1) ⊆ W n ∪ A n)
    (hcenter : ∀ n, p n ∈ W n)
    (hcontrolled : ∀ n, A n ⊆ (nk n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    {B : ℝ} (hinitial : ∀ x ∈ W 0, metricScalarAt g x ≤ B) :
    ∀ n, ∀ x ∈ W n,
      metricScalarAt g x ≤ (1 + 4323 * eps) ^ n * B := by
  simpa only [Finset.prod_const, Finset.card_range] using
    scalar_le_mul_prod_of_neck_region_growth W A (fun _ => eps) p nk
      hnext hcenter hcontrolled hinitial

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
