import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HNewLim_O68
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HComp_O73

set_option autoImplicit false

/-! # CH12-O73 G2: `newLimReg_O73`, `hNewLim_of_parts_O73` (`[FROZEN v2] CH12-O73`)

`newLimReg_O68` / `hNewLim_of_parts_O68` with the `hComp` binder discharged by `hComp_O73 F H`
(`hComp` is used only at the fixed `H`).  Proof of `newLimReg_O73` = that of `newLimReg_O68`
with `hComp ξ n' hξ` ↦ `hComp_O73 F H ξ n' hξ`; `hNewLim_of_parts_O73` = `hNewLim_O68` applied to
`hEvt` and `newLimReg_O73`. -/

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

/-- G2: `newLimReg_O68` with `hComp` discharged (`hComp_O73 F H`). -/
theorem newLimReg_O73 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r) :
    ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
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
              ckErr_O19 H H'.metric 1 f k p < ξ / 3 := by
  intro ξ n' hξ
  obtain ⟨ε₀, R₀, k₀, hε₀, hR₀, hcore⟩ :=
    newLimCore_O68 F H wstar old Hold sold mold hw hcpt hthickW
  obtain ⟨εc, Rc, kc, hεc, _hRc, δ, r, m', hδ, hr, hcomp⟩ := hComp_O73 F H ξ n' hξ
  refine ⟨min ε₀ εc, max R₀ Rc, max k₀ kc, lt_min hε₀ hεc,
    lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro t ht hreg q hgood hesc
  obtain ⟨σ, hσ, H', S', hthS, hconvS, hescS, ψ, hψbp, hψ⟩ := hcore t ht hreg q (fun m => by
    obtain ⟨R'', hR'', hsm, _, hck⟩ := hgood m
    exact ⟨R'', le_trans (le_max_left _ _) hR'', hsm, fun k'' hk p hp =>
      lt_of_lt_of_le (hck k'' (le_trans hk (le_max_left _ _)) p hp) (min_le_left _ _)⟩) hesc
  obtain ⟨I, hI⟩ := hψ δ r m' hδ hr
  obtain ⟨U', hU', hψs, hψe, hψck⟩ := hI I le_rfl
  obtain ⟨R'', hR'', hsm, hinj, hck⟩ := hgood (σ I)
  obtain ⟨U, f, hU, hfs, hfe, hfck⟩ := hcomp H' (t (σ I)) (q (σ I)) (ψ I) R'' U'
    (le_trans (le_max_right _ _) hR'') hsm hinj
    (fun k'' hk p hp => lt_of_lt_of_le (hck k'' (le_trans hk (le_max_right _ _)) p hp)
      (min_le_right _ _)) hU' hψs hψe hψck (hψbp I)
  exact ⟨σ, hσ, H', S', hthS, hconvS, hescS, ψ, hψbp, hψ, U, f, hU, hfs, hfe, hfck⟩

/-- G2: `hNewLim_of_parts_O68` with `hComp` discharged; wired `hNewLim` from `hcpt`, `hthickW`, `hEvt`. -/
theorem hNewLim_of_parts_O73 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (newLimReg_O73 F H wstar old Hold sold mold hw hcpt hthickW)

end GC.LongTime.Ch12
