import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoresDiagonal_O21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyCoresPost_S37

set_option autoImplicit false

/-! CH12-O21 G3 — `exists_bufferedCores_O21`: both scalar branches.
Negative branch (`EventuallyNegativeScalar_S13 F`): `exists_bufferedCores_of_cover_O21` on the
H4/HPI06/HPI07 family `hfam`.  Non-negative branch: `bufferedPersistentCores_count_zero_of_slice_empty_S37`
(count 0; `base` from `hHG03`, vacuous). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **H5, sheet S5 verbatim**, both branches.  `hslice` / `hevent`: S37 G2 shapes (S37 / S38 + S50);
`hfam`: the frozen O21 family input (cover form) under the negative branch. -/
theorem exists_bufferedCores_O21 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hslice : ¬ EventuallyNegativeScalar_S13 F →
      ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
        ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
          curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
          ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → False)
    (hevent : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      t ∈ F.observation.eventTimes →
      ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p =
          ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p r →
        False)
    (hfam : EventuallyNegativeScalar_S13 F → ∃ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
      (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
      (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
      (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x)) ∧
      (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) ∧
      (∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ t, T ≤ t → ∀ (ht0 : 0 < t) (w' : ℝ),
        w ≤ w' → w' ≤ w0 →
          ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p =
              ENNReal.ofReal r →
            ENNReal.ofReal (w' * r ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p r →
            ∃ (i : Fin count) (hi : start i ≤ t),
              p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹)) :
    ∃ B : BufferedPersistentCores F K,
      Nonempty (∀ i : Fin B.count, HyperbolicTruncation (B.model i)) := by
  by_cases hneg : EventuallyNegativeScalar_S13 F
  · exact exists_bufferedCores_of_cover_O21 F K hHG03 (hfam hneg)
  · obtain ⟨B, -⟩ := bufferedPersistentCores_count_zero_of_slice_empty_S37 F K (hslice hneg) hevent
    exact ⟨B, ⟨fun i => Classical.choice (hHG03 _)⟩⟩

end GC.LongTime.Ch12
