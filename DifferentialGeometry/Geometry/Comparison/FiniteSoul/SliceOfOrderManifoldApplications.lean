import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderManifold

/-!
# Consumers of the order-`k` subtype structure (lane CMS3-SLICE, group G1)

* `wsub_input_ofOrder`: the input instances of W-SUB's kernel for a compact `C^k` slice `S` of a
  Hausdorff carrier — a `C^n` manifold structure (`n ≤ k`) on the subtype modelled on `Fin d → ℝ`,
  compact and Hausdorff, with `C^n` inclusion;
* `injective_mfderiv_val_ofOrder`: the inclusion is an immersion (`k ≠ 0`);
* `finrank_sliceTangent_singleton`: the tangent space of a point is zero.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : WithTop ℕ∞} {S : Set M} {d : ℕ}

/-- **Input of the W-SUB kernel.** A compact `C^k` slice of a Hausdorff carrier is, through the slice
charts, a compact Hausdorff `C^n` manifold (`n ≤ k`) modelled on `Fin d → ℝ` with `C^n` inclusion. -/
theorem wsub_input_ofOrder [T2Space M] (hS : IsEmbeddedSliceOfOrder I k d S) (hSc : IsCompact S)
    {n : WithTop ℕ∞} (hn : n ≤ k) :
    let _ := embeddedSliceChartedSpaceOfOrder hS
    IsManifold 𝓘(ℝ, Fin d → ℝ) n S ∧ CompactSpace S ∧ T2Space S ∧
      ContMDiff 𝓘(ℝ, Fin d → ℝ) I n (Subtype.val : S → M) := by
  let _ := embeddedSliceChartedSpaceOfOrder hS
  have : IsManifold 𝓘(ℝ, Fin d → ℝ) k S := embeddedSliceOfOrder_isManifold hS
  exact ⟨IsManifold.of_le hn, isCompact_iff_compactSpace.mp hSc, inferInstance,
    (contMDiff_val_ofOrder hS).of_le hn⟩

/-- **The inclusion of a `C^k` slice is an immersion** (`k ≠ 0`). -/
theorem injective_mfderiv_val_ofOrder (hk : k ≠ 0) (hS : IsEmbeddedSliceOfOrder I k d S) (p : S) :
    let _ := embeddedSliceChartedSpaceOfOrder hS
    Injective (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p) := by
  let _ := embeddedSliceChartedSpaceOfOrder hS
  change Injective (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p)
  set D := mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p with hD
  have hrange : LinearMap.range D.toLinearMap = sliceTangent I S p.1 :=
    range_mfderiv_val_ofOrder hk hS p
  have hfr : Module.finrank ℝ (LinearMap.range D.toLinearMap) = d := by
    rw [hrange]
    exact finrank_sliceTangent_ofOrder hk hS p.2
  have hsum := LinearMap.finrank_range_add_finrank_ker D.toLinearMap
  have hdom : Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin d → ℝ) p) = d := by
    change Module.finrank ℝ (Fin d → ℝ) = d
    simp
  rw [hfr, hdom] at hsum
  have hker : LinearMap.ker D.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.1 (by omega)
  exact LinearMap.ker_eq_bot.1 hker

omit [FiniteDimensional ℝ E] in
/-- The tangent space of a point (a `0`-slice of every order `k ≤ ∞`) is zero. -/
theorem finrank_sliceTangent_singleton [I.Boundaryless] [IsManifold I ∞ M] (x : M) :
    Module.finrank ℝ (sliceTangent I ({x} : Set M) x) = 0 :=
  finrank_sliceTangent_ofOrder (k := ((1 : ℕ∞) : WithTop ℕ∞)) one_ne_zero
    (IsEmbeddedSliceOfOrder.singleton x) rfl

end DifferentialGeometry.Geometry.FiniteSoul
