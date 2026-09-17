import DifferentialGeometry.Topology.Manifold.Sard
import DifferentialGeometry.Topology.Manifold.LocalExtrema
import Mathlib.Geometry.Manifold.BumpFunction

noncomputable section

open Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] in
private theorem exists_compact_support_nonneg_ge_one
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x) ∧ ∀ x ∈ K, 1 ≤ f x := by
  classical
  have hb (x : K) : ∃ b : SmoothBumpFunction I (x : M), tsupport b ⊆ U := by
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.mp
      (hU.mem_nhds (hKU x.property))
    exact ⟨b, hb⟩
  choose b hb using hb
  let V (x : K) := interior {y : M | b x y = 1}
  have hcover : K ⊆ ⋃ x : K, V x := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact mem_interior_iff_mem_nhds.mpr (b ⟨x, hx⟩).eventuallyEq_one
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V (fun _ => isOpen_interior) hcover
  let f : M → ℝ := fun y => ∑ x ∈ s, b x y
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := contMDiff_finsetSum fun x _ => (b x).contMDiff
  have hfs : tsupport f ⊆ ⋃ x ∈ s, tsupport (b x : M → ℝ) := by
    apply closure_minimal _ (isClosed_biUnion_finset fun _ _ => isClosed_tsupport _)
    intro y hy
    by_contra hnot
    have hzero (x : K) (hx : x ∈ s) : b x y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hnot (mem_iUnion₂.mpr ⟨x, hx, h⟩))
    exact hy (Finset.sum_eq_zero hzero)
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · exact (s.isCompact_biUnion fun x _ => (b x).hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport f) hfs
  · exact hfs.trans (iUnion₂_subset fun x _ => hb x)
  · intro y
    exact Finset.sum_nonneg fun x _ => (b x).nonneg
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hs hy)
    have hone : b x y = 1 :=
      (interior_subset : interior {z : M | b x z = 1} ⊆ {z : M | b x z = 1}) hyx
    rw [← hone]
    exact Finset.single_le_sum (fun x _ => (b x).nonneg) hx

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem interior_superlevel_eq
    {f : M → ℝ} (hf : Continuous f) {r : ℝ}
    (hreg : ∀ x, f x = r → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    interior {x | r ≤ f x} = {x | r < f x} := by
  apply Subset.antisymm
  · intro x hx
    have hle : r ≤ f x :=
      (interior_subset : interior {y : M | r ≤ f y} ⊆ {y : M | r ≤ f y}) hx
    apply lt_of_le_of_ne hle
    intro heq
    have hmin : IsLocalMin f x := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
      exact heq ▸ hy
    apply hreg x heq.symm
    ext v
    exact congrArg (fun A : E →L[ℝ] ℝ => A v)
      (hmin.mvfderiv_eq_zero (I := I) BoundarylessManifold.isInteriorPoint)
  · exact interior_maximal (fun x (hx : r < f x) => hx.le)
      (isOpen_lt continuous_const hf)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem closure_strict_superlevel_eq
    {f : M → ℝ} (hf : Continuous f) {r : ℝ}
    (hreg : ∀ x, f x = r → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    closure {x | r < f x} = {x | r ≤ f x} := by
  apply Subset.antisymm
  · exact closure_minimal (fun x (hx : r < f x) => hx.le)
      (isClosed_le continuous_const hf)
  · intro x hx
    by_contra hnot
    have hle : f x ≤ r := le_of_not_gt (fun h => hnot (subset_closure h))
    have heq : f x = r := hle.antisymm hx
    have hmax : IsLocalMax f x := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnot] with y hy
      rw [heq]
      exact le_of_not_gt (fun h => hy (subset_closure h))
    apply hreg x heq
    ext v
    exact congrArg (fun A : E →L[ℝ] ℝ => A v)
      (hmax.mvfderiv_eq_zero (I := I) BoundarylessManifold.isInteriorPoint)

theorem exists_compact_regular_superlevel_between
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (f : M → ℝ) (r : ℝ),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x ∈ K, 1 ≤ f x) ∧ r ∈ Ioo (0 : ℝ) 1 ∧
      IsCompact {x | r ≤ f x} ∧ K ⊆ interior {x | r ≤ f x} ∧
      {x | r ≤ f x} ⊆ U ∧
      interior {x | r ≤ f x} = {x | r < f x} ∧
      closure {x | r < f x} = {x | r ≤ f x} ∧
      frontier {x | r ≤ f x} = {x | f x = r} ∧
      ∀ x, f x = r → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
  obtain ⟨f, hf, hc, hs, hn, hKf⟩ := exists_compact_support_nonneg_ge_one (I := I) hK hU hKU
  obtain ⟨r, hr, hreg⟩ := hf.exists_regular_value_of_hasCompactSupport hc
    (by norm_num : (0 : ℝ) < 1)
  have hsupport : {x | r ≤ f x} ⊆ tsupport f := by
    intro x hx
    exact subset_tsupport f (hr.1.trans_le hx).ne'
  have hinter := interior_superlevel_eq hf.continuous hreg
  have hclosed : IsClosed {x | r ≤ f x} := isClosed_le continuous_const hf.continuous
  refine ⟨f, r, hf, hc, hs, hn, hKf, hr, hc.of_isClosed_subset hclosed hsupport,
    ?_, hsupport.trans hs, hinter, closure_strict_superlevel_eq hf.continuous hreg, ?_, hreg⟩
  · rw [hinter]
    exact fun x hx => hr.2.trans_le (hKf x hx)
  · rw [frontier, hclosed.closure_eq, hinter]
    ext x
    change (r ≤ f x ∧ ¬ r < f x) ↔ f x = r
    exact ⟨fun h => (le_of_not_gt h.2).antisymm h.1,
      fun h => ⟨h.ge, not_lt_of_ge h.le⟩⟩

end DifferentialGeometry.Topology.Manifold
