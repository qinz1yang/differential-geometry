import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HNewLimWired_O73

set_option autoImplicit false

/-! # CH12-O75 G3c: the new-limit chain with the O74/O80 window binder hthickW-prime (thickWB body, window `1 + 1`)

`newLimCoreB_O75` = `newLimCore_O68` (text) with `hthickW` ↦ the thickWB body (extra `InjOn` premise, window
`B(1 + 1)`; only `y = basepoint` is used) and an `InjOn` conjunct in the admissibility premise;
`newLimRegB_O75` / `hNewLim_of_partsB_O75` = `newLimReg_O73` / `hNewLim_of_parts_O73` (text) on top of it.
So the slack hEndSfam producer needs only the O80 binder hthickW'F (no old-shape `hthickW`). -/

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

theorem newLimCoreB_O75 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (1 + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r) :
    ∃ (ε₀ R₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ 0 < R₀ ∧
      ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
      (∀ m, ∃ s : RegularSlice F.observation, s.time = t m) →
      ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
      (∀ m, ∃ R'' : ℝ, R₀ ≤ R'' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        ∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε₀) →
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
                ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) := by
  obtain ⟨εT, RT, TT, kT, hεT, hTT, hthick⟩ := hthickW
  refine ⟨εT, max RT 1, kT, hεT, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro t ht hreg
  choose s hs using hreg
  obtain rfl : t = fun m => (s m).time := funext fun m => (hs m).symm
  intro q hgood hesc
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop TT)
  let S : LatePointSequence_S13 F :=
    { slices := fun j => s (j + M₀)
      times_tendsto := ht.comp (Filter.tendsto_add_atTop_nat M₀)
      point := fun j => sliceCast_CX4 (s (j + M₀)) (q (j + M₀) H.basepoint) }
  have hthickS : IsWThickSequence_S13 S wstar := by
    intro j
    obtain ⟨R'', hR'', hsm, hinj, hck⟩ := hgood (j + M₀)
    have hbp : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (1 + 1) := by
      change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal (1 + 1)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    obtain ⟨r, hr, hcr, hv⟩ := hthick _ (hM₀ (j + M₀) (Nat.le_add_left M₀ j)) (q (j + M₀)) R''
      (le_trans (le_max_left _ _) hR'') hsm hinj (fun k'' hk p hp => hck k'' hk p hp) H.basepoint hbp
    have T := thickTransport_O68 (postStage_eq_sliceStage_CX4 (s (j + M₀)))
      (postMetric F.observation (s (j + M₀)).time) (s (j + M₀)).metric
      (postMetric_regularSlice F.observation (s (j + M₀))) (s (j + M₀)).time⁻¹
      (inv_pos.mpr (s (j + M₀)).positive)
      (inv_pos.mpr (lt_of_lt_of_le hTT (hM₀ (j + M₀) (Nat.le_add_left M₀ j))))
      (q (j + M₀) H.basepoint) r
    refine ⟨r, hr, T.1.trans hcr, ?_⟩
    rw [show ballVolume (S.slices j).normalizedMetric (S.point j) r = _ from T.2]
    exact hv
  obtain ⟨σ', hσ', H', hconv⟩ := hcpt hw S hthickS
  obtain ⟨Φ, C, hcan⟩ := hconv
  refine ⟨fun m => σ' m + M₀, fun a b hab => Nat.add_lt_add_right (hσ' hab) M₀, H',
    S.subsequence σ' hσ', fun j => hthickS (σ' j), ⟨Φ, C, hcan⟩, ?_,
    fun m => sliceApprox_O32 (S.subsequence σ' hσ') H' Φ m, ?_,
    hconvS_O32 F H' (S.subsequence σ' hσ') Φ C hcan⟩
  · intro i R
    obtain ⟨M, hM⟩ := hesc i R
    refine ⟨M, fun j hj hij => ?_⟩
    rintro ⟨x, ⟨z, hz, rfl⟩, hx⟩
    have hle : M ≤ σ' j + M₀ := le_trans hj (le_trans (hσ'.id_le j) (Nat.le_add_right _ _))
    refine hM (σ' j + M₀) hle hij ⟨z, hz, ?_⟩
    exact eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq hx).trans (cast_heq _ _)))
  · intro m
    exact eq_of_heq ((cast_heq _ _).trans ((heq_of_eq (Φ.basepoint_map m)).trans (cast_heq _ _)))

/-- O75: `newLimReg_O73` with the `thickWB` window binder (hthickW-prime, O74/O80 text, needs `InjOn`); `newLimReg_O68` with `hComp` discharged (`hComp_O73 F H`). -/
theorem newLimRegB_O75 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (1 + 1), ∃ r : ℝ, 0 < r ∧
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
    newLimCoreB_O75 F H wstar old Hold sold mold hw hcpt hthickW
  obtain ⟨εc, Rc, kc, hεc, _hRc, δ, r, m', hδ, hr, hcomp⟩ := hComp_O73 F H ξ n' hξ
  refine ⟨min ε₀ εc, max R₀ Rc, max k₀ kc, lt_min hε₀ hεc,
    lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro t ht hreg q hgood hesc
  obtain ⟨σ, hσ, H', S', hthS, hconvS, hescS, ψ, hψbp, hψ⟩ := hcore t ht hreg q (fun m => by
    obtain ⟨R'', hR'', hsm, hinj, hck⟩ := hgood m
    exact ⟨R'', le_trans (le_max_left _ _) hR'', hsm, hinj, fun k'' hk p hp =>
      lt_of_lt_of_le (hck k'' (le_trans hk (le_max_left _ _)) p hp) (min_le_left _ _)⟩) hesc
  obtain ⟨I, hI⟩ := hψ δ r m' hδ hr
  obtain ⟨U', hU', hψs, hψe, hψck⟩ := hI I le_rfl
  obtain ⟨R'', hR'', hsm, hinj, hck⟩ := hgood (σ I)
  obtain ⟨U, f, hU, hfs, hfe, hfck⟩ := hcomp H' (t (σ I)) (q (σ I)) (ψ I) R'' U'
    (le_trans (le_max_right _ _) hR'') hsm hinj
    (fun k'' hk p hp => lt_of_lt_of_le (hck k'' (le_trans hk (le_max_right _ _)) p hp)
      (min_le_right _ _)) hU' hψs hψe hψck (hψbp I)
  exact ⟨σ, hσ, H', S', hthS, hconvS, hescS, ψ, hψbp, hψ, U, f, hU, hfs, hfe, hfck⟩

/-- O75: `hNewLim_of_parts_O73` with the `thickWB` window binder; `hNewLim_of_parts_O68` with `hComp` discharged; wired `hNewLim` from `hcpt`, `hthickW`, `hEvt`. -/
theorem hNewLim_of_partsB_O75 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (1 + 1), ∃ r : ℝ, 0 < r ∧
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
    (newLimRegB_O75 F H wstar old Hold sold mold hw hcpt hthickW)

end GC.LongTime.Ch12
