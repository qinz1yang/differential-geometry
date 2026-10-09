import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NewLimReg_O68

set_option autoImplicit false

/-! # CH12-O68 G3: `hNewLim_O68 : <hNewLim binder of hanchor_O60, verbatim>`

Event times: a `RegularSlice` needs `time ∉ eventTimes`, so the regular-time producer
`newLimReg_O68` is lifted to all times through the binder `hEvt` (event-time transfer:
regular version ⇒ full `hNewLim`).  `hNewLim_of_parts_O68` is the wired form. -/

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

/-- `[FROZEN] CH12-O68` G3. -/
theorem hNewLim_O68 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (hEvt : (∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
        (∀ m, ∃ s : RegularSlice F.observation, s.time = t m) →
        ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
        (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
        (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
          q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
          IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
          (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
            S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
              (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
          ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
            (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
            (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
              ∃ U : TopologicalSpace.Opens H'.Carrier,
                riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
                ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
                IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
                ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                  ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
            ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
              riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
              ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
                ckErr_O19 H H'.metric 1 f k p < ξ / 3) →
      ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
        ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
        (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
        (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
          q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
          IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
          (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
            S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
              (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
          ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
            (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
            (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
              ∃ U : TopologicalSpace.Opens H'.Carrier,
                riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
                ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
                IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
                ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                  ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
            ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
              riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
              ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
                ckErr_O19 H H'.metric 1 f k p < ξ / 3)
    (hreg : ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
        (∀ m, ∃ s : RegularSlice F.observation, s.time = t m) →
        ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
        (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
        (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
          q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
          IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
          (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
            S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
              (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
          ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
            (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
            (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
              ∃ U : TopologicalSpace.Opens H'.Carrier,
                riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
                ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
                IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
                ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                  ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
            ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
              riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
              ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
                ckErr_O19 H H'.metric 1 f k p < ξ / 3) :
    ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
      ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
      ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
      (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
      (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
        q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
          S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
        ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
          (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
          (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
            ∃ U : TopologicalSpace.Opens H'.Carrier,
              riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
              ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
          ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
            riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
            ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
              ckErr_O19 H H'.metric 1 f k p < ξ / 3 :=
  hEvt hreg

/-- Wired G3: `hNewLim` from `hcpt`, `hthickW`, `hComp` (G2) and the event-time transfer `hEvt`. -/
theorem hNewLim_of_parts_O68 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (hw : 0 < wstar)
    (hcpt : 0 < wstar → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S wstar →
      ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ M : FiniteVolumeHyperbolicModel.{u},
        PointedSmoothConverges_S13 (S.subsequence σ hσ) M)
    (hthickW :
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
    (hComp :
    ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
      ∃ (δ r : ℝ) (m' : ℕ), 0 < δ ∧ 0 < r ∧
      ∀ (H H' : FiniteVolumeHyperbolicModel.{u}) (t : ℝ)
        (q : H.Carrier → (postStage F.observation t).Carrier)
        (ψ : H'.Carrier → (postStage F.observation t).Carrier) (R'' : ℝ)
        (U' : TopologicalSpace.Opens H'.Carrier), R ≤ R'' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ q k'' p < ε) →
        riemannianBallOf H'.metric H'.basepoint r ⊆ U' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ U' →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => ψ x) →
        (∀ k'' : ℕ, k'' ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
          ckErr_S45 H' (postMetric F.observation t) t⁻¹ ψ k'' p < δ) →
        ψ H'.basepoint = q H.basepoint →
        ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
          ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
            ckErr_O19 H H'.metric 1 f k p < ξ / 3)
    (hEvt : (∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
        (∀ m, ∃ s : RegularSlice F.observation, s.time = t m) →
        ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
        (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
        (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
          q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
          IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
          (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
            S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
              (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
          ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
            (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
            (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
              ∃ U : TopologicalSpace.Opens H'.Carrier,
                riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
                ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
                IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
                ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                  ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
            ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
              riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
              ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
                ckErr_O19 H H'.metric 1 f k p < ξ / 3) →
      ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
        ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
        (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
          ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
        (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
          q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
          IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
          (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
            S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
              (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
          ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
            (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
            (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
              ∃ U : TopologicalSpace.Opens H'.Carrier,
                riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
                ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
                IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
                ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                  ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
            ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
              riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
              ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
                ckErr_O19 H H'.metric 1 f k p < ξ / 3) :
    ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
      ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
      ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
      (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
      (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
        q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
          S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
        ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
          (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
          (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
            ∃ U : TopologicalSpace.Opens H'.Carrier,
              riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
              ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
          ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
            riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
            ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
              ckErr_O19 H H'.metric 1 f k p < ξ / 3 :=
  hNewLim_O68 F H wstar old Hold sold mold hEvt
    (newLimReg_O68 F H wstar old Hold sold mold hw hcpt hthickW hComp)

end GC.LongTime.Ch12
