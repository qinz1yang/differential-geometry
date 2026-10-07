import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverRegularAssembly_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyThickCores_S37

set_option autoImplicit false

/-! CH12-O33 G3 (R5) — `hfam_O33`: the frozen `hfam` input of `exists_bufferedCores_v2_O21`
(cover form) from the R3 family (`[FROZEN] CH12-O33` G1 conclusion), the regular-time cover
`cover_regular_O27` and the event-time cover R4e (`[FROZEN] CH12-O33` G2 statement).
Truncations `Tr` are chosen from `hHG03`; a time `t > 0` is either an event time (R4e) or the time
of a regular slice (`regularSlice_exists_of_not_eventTime_S37`), and `w0` is the minimum. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **R5 packaging.**  `hR3` = `[FROZEN] CH12-O33` G1 conclusion (under the negative branch),
`hR4e` = `[FROZEN] CH12-O33` G2 statement (`cover_event_O33`).  Output: the `hfam` binder of
`exists_bufferedCores_v2_O21`, verbatim. -/
theorem hfam_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hR3 : EventuallyNegativeScalar_S13 F → ∃ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
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
      (∀ w : ℝ, 0 < w → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
        ¬ ∀ (i : Fin count) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : start i ≤ (S.slices j).time,
          S.point j ∉ sliceCast_CX4 (S.slices j) ''
            (map i _ hj '' riemannianBallOf (model i).metric (model i).basepoint R)))
    (hR4e : ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
      (_Tr : ∀ i, HyperbolicTruncation (model i)) (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
      (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
      (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
      (∀ i, 0 < start i) → (∀ i t, start i ≤ t → 0 < α i t) →
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) →
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) →
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) →
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) →
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) →
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x)) →
      (∀ w : ℝ, 0 < w → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
        ¬ ∀ (i : Fin count) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : start i ≤ (S.slices j).time,
          S.point j ∉ sliceCast_CX4 (S.slices j) ''
            (map i _ hj '' riemannianBallOf (model i).metric (model i).basepoint R)) →
      ∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht0 : 0 < t), T ≤ t →
        t ∈ F.observation.eventTimes → ∀ w' : ℝ, w ≤ w' → w' ≤ w0 →
          ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p =
              ENNReal.ofReal r →
            ENNReal.ofReal (w' * r ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p r →
            ∃ (i : Fin count) (hi : start i ≤ t),
              p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹) :
    EventuallyNegativeScalar_S13 F → ∃ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
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
              p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹) := by
  intro hneg
  obtain ⟨count, model, start, α, Ω, map, hstart, hpos, hanti, hdecay, hsmooth, hemb, hball, hck,
    hpatch, hdisj, hDone⟩ := hR3 hneg
  let Tr : ∀ i, HyperbolicTruncation (model i) := fun i => Classical.choice (hHG03 (model i))
  obtain ⟨w1, hw1, hreg⟩ := cover_regular_O27 F K count model Tr start α Ω map hstart hpos hdecay
    hsmooth hemb hball hck hDone
  obtain ⟨w2, hw2, hev⟩ := hR4e count model Tr start α Ω map hstart hpos hdecay hsmooth hemb hball
    hck hpatch hDone
  refine ⟨count, model, start, α, Ω, map, hstart, hpos, hanti, hdecay, hsmooth, hemb, hball, hck,
    hpatch, hdisj, min w1 w2, lt_min hw1 hw2, fun w hw => ?_⟩
  obtain ⟨T1, hT1⟩ := hreg w hw
  obtain ⟨T2, hT2⟩ := hev w hw
  refine ⟨max T1 T2, fun t hT ht0 w' hww' hw'0 p r hr hcr hth => ?_⟩
  by_cases hevt : t ∈ F.observation.eventTimes
  · exact hT2 t ht0 ((le_max_right _ _).trans hT) hevt w' hww' (hw'0.trans (min_le_right _ _))
      p r hr hcr hth
  · obtain ⟨s, rfl⟩ := regularSlice_exists_of_not_eventTime_S37 F.observation t ht0 hevt
    exact hT1 s ((le_max_left _ _).trans hT) w' hww' (hw'0.trans (min_le_left _ _)) p r hr hcr hth

end GC.LongTime.Ch12
