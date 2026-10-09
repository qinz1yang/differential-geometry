import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.AnchorCore_O60

set_option autoImplicit false

/-! # CH12-O60 G2: `hanchor_O60 : anchor_shape_O46` (old core = B', new patch = min-count limit)

`[FROZEN] CH12-O60` (scratch/FrozenO60.lean).  Case split at the radius `(α i t₂)⁻¹/2 → ∞`:
* old core (`q bp ∈ mold i t₂ '' B((α i t₂)⁻¹/2)`): `old_case_levels_O60` (B': old GOOD maps +
  old-core rigidity + `core_anchor_O60`);
* new patch (contradiction): a bad sequence `(t m, q m)` outside the old cores escapes every old
  core (radii `→ ∞`); `hNewLim` gives a limit `H'` with an ESC w-thick regular-slice sequence `S'`
  and convergence maps `ψ m`; `hMIN` gives `count H ≤ count H'`; S1 v3 (`hHG06`) gives `H ≅ H'`;
  `ψ I ∘ e` (`good_transport_O60`) is an anchor of `q (σ I)` — contradiction.
`anchor_of_levels_O60` assembles `βw`. -/

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

/-- G2: `hanchor_O60 : anchor_shape_O46` (body verbatim). -/
theorem hanchor_O60 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
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
    (hMIN : ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
      IsWThickSequence_S13 S' wstar → PointedSmoothConverges_S13 S' H' →
      (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
        S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
      ∀ Tr' : HyperbolicTruncation H', ∃ Tr : HyperbolicTruncation H, Tr.count ≤ Tr'.count)
    (hold : ∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
      (∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0)) ∧
      (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
        ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t) ∧
      ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧ ∃ T : ℝ,
        ∀ (i : Fin old) (t : ℝ) (hi : sold i ≤ t), T ≤ t →
        ∀ (q : H.Carrier → (postStage F.observation t).Carrier) (R'' : ℝ), R ≤ R'' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ q k'' p < ε) →
        ∀ z ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint ((α i t)⁻¹ / 2),
          mold i t hi z = q H.basepoint →
        ∃ e : H.Carrier ≃ (Hold i).Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
          ∀ p, localPullInner (Hold i).metric e p = H.metric.inner p)
    (hNewLim : ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
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
  ∃ βw : ℝ → ℝ, (∀ t, 0 < βw t) ∧ Filter.Tendsto βw Filter.atTop (nhds 0) ∧
    ∃ (ε₁ R₁ : ℝ) (k₁ : ℕ), 0 < ε₁ ∧ 0 < R₁ ∧ ∃ T₁ : ℝ, ∀ t₂ : ℝ, T₁ ≤ t₂ →
      ∀ (q : H.Carrier → (postStage F.observation t₂).Carrier) (R'' : ℝ), R₁ ≤ R'' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      (∀ k'' : ℕ, k'' ≤ k₁ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ q k'' p < ε₁) →
      ∃ (φ : H.Carrier → (postStage F.observation t₂).Carrier)
        (U' : TopologicalSpace.Opens H.Carrier) (y₀ : H.Carrier),
        riemannianBallOf H.metric y₀ (4 * (βw t₂)⁻¹) ⊆ U' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) ∧
        (∀ k : ℕ, k ≤ ⌈(βw t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric y₀ (4 * (βw t₂)⁻¹),
          ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ φ k p < βw t₂) ∧
        φ y₀ = q H.basepoint := by
  obtain ⟨α, hαpos, hα0, hgood, hrig⟩ := hold
  obtain ⟨εO, RO, kO, hεO, hRO, hOld⟩ :=
    old_case_levels_O60 F H old Hold sold mold α hαpos hα0 hgood hrig
  obtain ⟨ξ, hξ, n, -, -, hG⟩ := hHG06 H H.basepoint 1 one_pos
  obtain ⟨εN, RN, kN, hεN, -, hNew⟩ := hNewLim ξ n hξ
  refine anchor_of_levels_O60 F H (min εO εN) (max RO RN) (max kO kN) (lt_min hεO hεN)
    (lt_of_lt_of_le hRO (le_max_left _ _)) (fun n₀ => ?_)
  obtain ⟨TO, hTO1, hTO⟩ := hOld n₀
  by_contra hfail
  -- a bad admissible map at every late time
  have hbad : ∀ m : ℕ, ∃ t₂ : ℝ, max TO (m : ℝ) ≤ t₂ ∧
      ∃ (q : H.Carrier → (postStage F.observation t₂).Carrier) (R'' : ℝ), max RO RN ≤ R'' ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
      Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
      (∀ k'' : ℕ, k'' ≤ max kO kN → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ q k'' p < min εO εN) ∧
      ¬ ∃ (φ : H.Carrier → (postStage F.observation t₂).Carrier)
        (U' : TopologicalSpace.Opens H.Carrier) (y₀ : H.Carrier),
        riemannianBallOf H.metric y₀ (4 * (1 / ((n₀ : ℝ) + 1))⁻¹) ⊆ U' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) ∧
        (∀ k : ℕ, k ≤ ⌈(1 / ((n₀ : ℝ) + 1))⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric y₀ (4 * (1 / ((n₀ : ℝ) + 1))⁻¹),
          ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ φ k p < 1 / ((n₀ : ℝ) + 1)) ∧
        φ y₀ = q H.basepoint := by
    intro m
    by_contra hm
    apply hfail
    refine ⟨max TO (m : ℝ), fun t₂ ht₂ q R'' hR hq hinj herr => ?_⟩
    by_contra hq'
    exact hm ⟨t₂, ht₂, q, R'', hR, hq, hinj, herr, hq'⟩
  choose t ht q R hR hq hinj herr hno using hbad
  -- bad maps are not in an old core (old-core case = `old_case_levels_O60`)
  have hnotold : ∀ m (i : Fin old) (hi : sold i ≤ t m), q m H.basepoint ∉
      mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ((α i (t m))⁻¹ / 2) := by
    rintro m i hi ⟨z, hz, hzq⟩
    exact hno m (hTO (t m) ((le_max_left _ _).trans (ht m)) (q m) (R m)
      ((le_max_left _ _).trans (hR m)) (hq m) (hinj m)
      (fun k'' hk p hp => (herr m k'' (hk.trans (le_max_left _ _)) p hp).trans_le
        (min_le_left _ _)) i hi z hz hzq)
  have htend : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun m => (le_max_right _ _).trans (ht m)) tendsto_natCast_atTop_atTop
  -- hence they escape every old core (radii `(α i (t m))⁻¹ / 2 → ∞`)
  have hesc : ∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
      q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ := by
    intro i ρ
    have hlim : Tendsto (fun m => α i (t m)) atTop (𝓝 0) := (hα0 i).comp htend
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
      (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * (|ρ| + 1)) by positivity)))
    refine ⟨M, fun m hm hi hmem => hnotold m i hi ?_⟩
    obtain ⟨z, hz, hzq⟩ := hmem
    refine ⟨z, riemannianBallOf_mono _ _ ?_ hz, hzq⟩
    have h2 : 2 * (|ρ| + 1) < (α i (t m))⁻¹ := by
      have := inv_strictAnti₀ (hαpos i (t m)) (hM m hm)
      rwa [one_div, inv_inv] at this
    have := le_abs_self ρ
    linarith
  -- new patch: the limit, min count, S1 v3 rigidity
  obtain ⟨σ, -, H', S', hW', hconv', hESC', ψ, hψbp, hψconv, U, f, hball, hfs, hfemb, hferr⟩ :=
    hNew t htend q (fun m => ⟨R m, (le_max_right _ _).trans (hR m), hq m, hinj m,
      fun k'' hk p hp => (herr m k'' (hk.trans (le_max_right _ _)) p hp).trans_le
        (min_le_right _ _)⟩) hesc
  obtain ⟨Tr, hTr⟩ := hMIN H' S' hW' hconv' hESC' (hHG03 H').some
  obtain ⟨e, he, he', hiso, -⟩ := hG H' Tr (hHG03 H').some hTr U f hball hfs hfemb hferr
  have hβ : (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) := by positivity
  obtain ⟨I, hI⟩ := hψconv (1 / ((n₀ : ℝ) + 1)) (4 * (1 / ((n₀ : ℝ) + 1))⁻¹)
    ⌈(1 / ((n₀ : ℝ) + 1))⁻¹⌉₊ hβ (by positivity)
  obtain ⟨Uψ, hUψ, hψs, hψemb, hψerr⟩ := hI I le_rfl
  have htpos : 0 < t (σ I) :=
    lt_of_lt_of_le one_pos (hTO1.trans ((le_max_left _ _).trans (ht (σ I))))
  obtain ⟨U', hU', hφs, hφemb, hφerr⟩ := good_transport_O60 H H' e he he' hiso
    (postMetric F.observation (t (σ I))) (t (σ I))⁻¹ (inv_pos.2 htpos) (ψ I) Uψ H'.basepoint
    (4 * (1 / ((n₀ : ℝ) + 1))⁻¹) (1 / ((n₀ : ℝ) + 1)) ⌈(1 / ((n₀ : ℝ) + 1))⁻¹⌉₊
    hUψ hψs hψemb hψerr
  exact hno (σ I) ⟨fun x => ψ I (e x), U', e.symm H'.basepoint, hU', hφs, hφemb, hφerr,
    by simp [hψbp I]⟩

end GC.LongTime.Ch12
