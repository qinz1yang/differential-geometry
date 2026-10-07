import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HEvtLate_O75
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HoldAssembly_O66
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HNewLimWired_O73
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HEndWired_S143
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HPRrev_O76

set_option autoImplicit false

/-!
# CH12-O75 G3a: `[FROZEN v5] CH12-O75 hEndSfam` producer, `hRRlate_of_hRRF_O75`

`hEndSfam_v5_O75`: the hone_S129-form hEndSfam binder with the OLD-GOOD and late old
right-regularisation premises (v5), produced from the top-level leaves `hHG03`, `hHG06`, `hthickWF`
and the compactness supply `hcptF` (= `hextract hneg` in the terminal): `hEnd_O54` + `hanchor_O60`
with `hold := hold_O66 … (hPRrev_O76 hHG03 hHG06) hgo` and
`hNewLim := hNewLim_of_parts_O73 … (hEvtLate_O75 … hRR)`.  `hRRlate_of_hRRF_O75`: the family
`hRRlate` from the single-model binder `hRRF` (`[FROZEN] CH12-O75 hRRF`, producer lane O82).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace GC.LongTime.Ch12

/-- `[FROZEN] CH12-O75 hRRF` (binder text) and its family use: `hRRlate` of a family from the
single-model `hRRF` and the per-model Single 8-tuple (hdrift `hb` shape). -/
theorem hRRlate_of_hRRF_O75 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hRRF : ∀ (H₀ : FiniteVolumeHyperbolicModel.{u}) (s₀ : ℝ) (_hs₀ : 0 < s₀) (K : ℕ) (α : ℝ → ℝ)
      (Ω : TopologicalSpace.Opens (ℝ × H₀.Carrier))
      (m₀ : ∀ t : ℝ, s₀ ≤ t → H₀.Carrier → (postStage F.observation t).Carrier),
      ((∀ t, s₀ ≤ t → 0 < α t) ∧ AntitoneOn α (Ici s₀) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : s₀ ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (m₀ t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : s₀ ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => m₀ t ht x)) ∧
      (∀ t, s₀ ≤ t →
        riemannianBallOf H₀.metric H₀.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : s₀ ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf H₀.metric H₀.basepoint (2 * (α t)⁻¹),
          ckErr_S45 H₀ (postMetric F.observation t) t⁻¹ (m₀ t ht) k p < α t) ∧
      (∀ t (_ht : s₀ ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
        Nonempty (PersistentModelPatch F H₀ s₀ α (sourceSlice_CX5 Ω) m₀ t x))) →
      ∀ ρ : ℝ, ∃ T : ℝ, ∀ (t : ℝ) (hi : s₀ ≤ t), T ≤ t → ∃ δ : ℝ, 0 < δ ∧
        ∀ (s : ℝ) (hs : s₀ ≤ s), t ≤ s → s < t + δ →
        postStage F.observation t = postStage F.observation s →
        ∀ (x : (postStage F.observation t).Carrier) (y : (postStage F.observation s).Carrier),
          HEq x y →
          y ∈ m₀ s hs '' riemannianBallOf H₀.metric H₀.basepoint ρ →
          x ∈ m₀ t hi '' riemannianBallOf H₀.metric H₀.basepoint (ρ + 1))
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (K : ℕ) (α : Fin old → ℝ → ℝ) (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (Hold i).Carrier))
    (hpos : ∀ i, 0 < sold i)
    (hb : ∀ i, ((∀ t, sold i ≤ t → 0 < α i t) ∧ AntitoneOn (α i) (Ici (sold i)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ t (ht : sold i ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ t (ht : sold i ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 (Ω i) t => mold i t ht x)) ∧
      (∀ t, sold i ≤ t →
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ t (ht : sold i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t ht) k p < α i t) ∧
      (∀ t (_ht : sold i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (Hold i) (sold i) (α i) (sourceSlice_CX5 (Ω i)) (mold i) t x)))) :
    (∀ (i : Fin old) (ρ : ℝ), ∃ T : ℝ, ∀ (t : ℝ) (hi : sold i ≤ t), T ≤ t → ∃ δ : ℝ, 0 < δ ∧
          ∀ (s : ℝ) (hs : sold i ≤ s), t ≤ s → s < t + δ →
          postStage F.observation t = postStage F.observation s →
          ∀ (x : (postStage F.observation t).Carrier) (y : (postStage F.observation s).Carrier),
            HEq x y →
            y ∈ mold i s hs '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ →
            x ∈ mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (ρ + 1)) :=
  fun i ρ => hRRF (Hold i) (sold i) (hpos i) K (α i) (Ω i) (mold i) (hb i) ρ

/-- `[FROZEN v5] CH12-O75 hEndSfam` producer (hone_S129 form, a := 1): v5 = hone_S129's hEndSfam
binder with `OLDGOOD → hRRlate →` right after `hcan`. -/
theorem hEndSfam_v5_O75 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hHG06 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
          (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
            ckErr_O19 H H'.metric 1 f k p < ξ / 3) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η)
    (hthickWF : ∀ wstar : ℝ, 0 < wstar → ∀ H : FiniteVolumeHyperbolicModel.{u},
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (4 * R''), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r)
    (hcptF : ∀ wstar : ℝ, 0 < wstar → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S wstar →
      ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ M : FiniteVolumeHyperbolicModel.{u},
        PointedSmoothConverges_S13 (S.subsequence σ hσ) M) :
    ∀ wstar : ℝ, 0 < wstar → ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (_Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
      (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
      (C : MetricConvergenceData Φ)
      (_hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k),
      (∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
      (∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0)) ∧
      (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
        ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t)) →
      (∀ (i : Fin old) (ρ : ℝ), ∃ T : ℝ, ∀ (t : ℝ) (hi : sold i ≤ t), T ≤ t → ∃ δ : ℝ, 0 < δ ∧
          ∀ (s : ℝ) (hs : sold i ≤ s), t ≤ s → s < t + δ →
          postStage F.observation t = postStage F.observation s →
          ∀ (x : (postStage F.observation t).Carrier) (y : (postStage F.observation s).Carrier),
            HEq x y →
            y ∈ mold i s hs '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ →
            x ∈ mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (ρ + 1)) →
      IsWThickSequence_S13 S wstar → (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) → (∀ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar → PointedSmoothConverges_S13 S' H' →
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
        S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
        ∀ Tr' : HyperbolicTruncation H', ∃ Tr : HyperbolicTruncation H, Tr.count ≤ Tr'.count) →
      ∃ β : ℝ → ℝ, (∀ t, 0 < β t) ∧ Filter.Tendsto β Filter.atTop (nhds 0) ∧
      (∃ I : ℕ, ∀ i : ℕ, I ≤ i →
        ∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sliceApprox_O32 S H Φ i) U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => sliceApprox_O32 S H Φ i x) ∧
          ∀ k : ℕ, k ≤ ⌈(β (S.slices i).time)⁻¹⌉₊ →
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹),
            ckErr_S45 H (postMetric F.observation (S.slices i).time) (S.slices i).time⁻¹
              (sliceApprox_O32 S H Φ i) k p < β (S.slices i).time) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ (ε' R' : ℝ) (k' : ℕ), 0 < ε' ∧ 0 < R' ∧
        ε' ≤ ε ∧ R ≤ R' ∧ k ≤ k' ∧ ∃ Te : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Te ≤ t → t₂ = 2 * t →
        ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < β t) →
        ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
          (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'), f t h0 p = g₁ p) →
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
        ∃ (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(β t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < β t₂) ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E ∧
          (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E (μ, p)) ∧
            Function.Bijective (fun p => E (μ, p))) ∧
          (∀ p, E (0, p) = p) ∧
          (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * R) → E (μ, p) = p) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
            let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
            H.metric.inner (E (μ, p)) v v ≤ ε ^ 2) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ i : ℕ, i ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
            ckErr_S45 H H.metric 1 (fun x => E (μ, x)) i p ≤ ε) ∧
          (∀ (h1 : t₂ ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), f t₂ h1 (E (1, p)) = g₂ p) ∧
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r) := by
  intro wstar hw old Hold sold mold Rold H S Φ C hcan hgo hRR hW hESC hMIN
  exact hEnd_O54 F H wstar 1 S Φ C hcan hHG06 hps01_O62 (hHG03 H).some (hthickWF wstar hw H)
    (hanchor_O60 F H wstar old Hold sold mold hHG03 hHG06 hMIN
      (hold_O66 F H old Hold sold mold hHG06 (hPRrev_O76 hHG03 hHG06) hgo)
      (hNewLim_of_parts_O73 F H wstar old Hold sold mold hw (hcptF wstar) (hthickWF wstar hw H)
        (hEvtLate_O75 F H wstar old Hold sold mold hRR)))

end GC.LongTime.Ch12
