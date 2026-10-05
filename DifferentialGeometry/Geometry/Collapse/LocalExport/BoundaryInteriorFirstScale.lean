import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCut
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleInterior

/-!
# LC88 / BCP04, packet P1 tail: first volume scales of the interior completion (lane BDRY-1, G6)

Review 45 §1.4: the first-volume scale transfers to the completion only through a first-hit witness.
* `firstPositiveCrossing_congr_of_witness_BDRY1` (real analysis): two profiles agreeing on `(0, r₀]`,
  with `r₀ > 0` a crossing of the first, have the same first positive crossing;
* `firstVolumeScale_cut_eq_BDRY1`: for `ĝ = g°` on `{D ≥ a}`, `0 < w < ω₃` and `r_q(w) + a ≤ D(q)`,
  the first volume scale of `ĝ` at `q` equals the ORIGINAL one of `W` (witness = the attained original
  first-hit radius, BSA03 at interior centres; ball volumes up to it agree by
  `completion_cut_local_data_BDRY1`).
The scale `ρ` itself is never recomputed on the completion (it is `ρ ∘ ι`, review 45 §1.4).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold Bundle
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

/-- **First-hit transfer.** If two profiles agree on `(0, r₀]` and `r₀ > 0` is a crossing of the
first (`V₁ r₀ ≤ F r₀`), the first positive crossings coincide. -/
theorem firstPositiveCrossing_congr_of_witness_BDRY1 {V₁ V₂ F : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hagree : ∀ r, 0 < r → r ≤ r₀ → V₁ r = V₂ r) (hwit : V₁ r₀ ≤ F r₀) :
    Real.firstPositiveCrossing V₁ F = Real.firstPositiveCrossing V₂ F := by
  have key : ∀ V : ℝ → ℝ, (∀ r, 0 < r → r ≤ r₀ → V r = V₁ r) →
      Real.firstPositiveCrossing V F =
        sInf ({r : ℝ | 0 < r ∧ V₁ r ≤ F r} ∩ Iic r₀) := by
    intro V hV
    have hS : {r : ℝ | 0 < r ∧ V r ≤ F r} ∩ Iic r₀ = {r : ℝ | 0 < r ∧ V₁ r ≤ F r} ∩ Iic r₀ := by
      ext r
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Iic]
      constructor
      · rintro ⟨⟨hr, hv⟩, hle⟩
        exact ⟨⟨hr, (hV r hr hle) ▸ hv⟩, hle⟩
      · rintro ⟨⟨hr, hv⟩, hle⟩
        exact ⟨⟨hr, (hV r hr hle).symm ▸ hv⟩, hle⟩
    have hmem : r₀ ∈ {r : ℝ | 0 < r ∧ V r ≤ F r} ∩ Iic r₀ :=
      ⟨⟨hr₀, (hV r₀ hr₀ le_rfl).symm ▸ hwit⟩, mem_Iic.mpr le_rfl⟩
    have hbdd : BddBelow {r : ℝ | 0 < r ∧ V r ≤ F r} := ⟨0, fun r hr => hr.1.le⟩
    rw [← hS]
    unfold Real.firstPositiveCrossing
    refine le_antisymm (csInf_le_csInf hbdd ⟨r₀, hmem⟩ inter_subset_left) ?_
    refine le_csInf ⟨r₀, hmem.1⟩ fun x hx => ?_
    rcases le_or_gt x r₀ with hxr | hxr
    · exact csInf_le ⟨0, fun r hr => hr.1.1.le⟩ ⟨hx, hxr⟩
    · exact (csInf_le ⟨0, fun r hr => hr.1.1.le⟩ hmem).trans hxr.le
  rw [key V₁ (fun _ _ _ => rfl), key V₂ (fun r hr hle => (hagree r hr hle).symm)]

variable (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- **First volume scales of the completion (first-hit witness).** For `ĝ = g°` on `{D ≥ a}`
(`a ≥ 0`), `0 < w < ω₃` and `r_q(w) + a ≤ D(q)` (the original first-hit radius of `W` stays in the
protected region), the first volume scale of `ĝ` at `q` is the original one. -/
theorem firstVolumeScale_cut_eq_BDRY1 {a : ℝ} (ha : 0 ≤ a)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal a ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (q : W.pieceInterior ⊤) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    (hq : ENNReal.ofReal (firstVolumeScale g q.val w + a) ≤ distanceToBoundary W g q) :
    firstVolumeScale ĝ q w = firstVolumeScale g q.val w := by
  have hint : q.val ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1 W]
    exact q.property
  obtain ⟨hpos, hhit, -⟩ := firstVolumeScale_spec_of_distanceToBoundary_pos W g q.val
    (distanceToBoundary_pos_of_mem_interior W g hint) hw hwc
  have hvol := (completion_cut_local_data_BDRY1 W g ĝ ha heq (ρ := 1) one_pos).2.2
  unfold firstVolumeScale
  refine (firstPositiveCrossing_congr_of_witness_BDRY1 hpos (fun r hr hle => ?_)
    (le_of_eq hhit)).symm
  have h := (hvol q hr.le ((ENNReal.ofReal_le_ofReal (by
    rw [mul_one]; linarith)).trans hq)).1
  rw [mul_one] at h
  rw [h]

end DifferentialGeometry.Geometry.Collapse
