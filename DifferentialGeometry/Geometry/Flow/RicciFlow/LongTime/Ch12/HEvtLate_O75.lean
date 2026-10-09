import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HEvt_O75

set_option autoImplicit false

/-!
# CH12-O75 G3a: `hEvt` from the LATE old right-regularisation `hRRlate` ([FROZEN v5] CH12-O75)

`hEvtLate_O75` (= `hEvt_O75` with `hRR` only at late times `t ≥ T i ρ`, the true form): the regular-slice version of the new-limit statement implies the version at arbitrary
times.  Each late time `t m` is replaced by a regular slice `s_m ∈ [t m, t m + δ_m)` with the same
post stage (`hRegRight_O75`); `δ_m` is below the forward C^k transfer step (admissibility at
`s_m`, `ckTransfer_O75`), the backward steps for all orders/accuracies `≤ m` (diagonal convergence
back at `t (σ m)`), and the `hRR` steps for all old models and integer radii `≤ m` (escape at
`s_m`).  Maps are moved between the equal stages by `cast`.
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

/-- `[FROZEN v5] CH12-O75`: the O68 `hEvt` (regular version ⇒ full) from `hRRlate` only. -/
theorem hEvtLate_O75 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (hRR :
        (∀ (i : Fin old) (ρ : ℝ), ∃ T : ℝ, ∀ (t : ℝ) (hi : sold i ≤ t), T ≤ t → ∃ δ : ℝ, 0 < δ ∧
          ∀ (s : ℝ) (hs : sold i ≤ s), t ≤ s → s < t + δ →
          postStage F.observation t = postStage F.observation s →
          ∀ (x : (postStage F.observation t).Carrier) (y : (postStage F.observation s).Carrier),
            HEq x y →
            y ∈ mold i s hs '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ →
            x ∈ mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (ρ + 1)))
    :
  (∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
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
                ckErr_O19 H H'.metric 1 f k p < ξ / 3
    := by
  classical
  intro hreg ξ n' hξ
  obtain ⟨εr, R, k, hεr, hR, hT⟩ := hreg ξ n' hξ
  obtain ⟨δF, hδF, hTF⟩ := ckTransfer_O75 F.observation k (εr / 2) (half_pos hεr)
  have hB : ∀ p N : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → ∃ τ : ℝ, 0 < τ ∧
      ∀ s : ℝ, t ≤ s → s < t + τ →
      ∀ (H₁ : FiniteVolumeHyperbolicModel.{u}) (U : TopologicalSpace.Opens H₁.Carrier)
        (q : H₁.Carrier → (postStage F.observation t).Carrier)
        (q' : H₁.Carrier → (postStage F.observation s).Carrier),
        HEq q q' → ContMDiffOn (𝓡 3) (𝓡 3) ∞ q U → Set.InjOn q U →
        ((∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ (postMetric F.observation t) t⁻¹ q j x ≤ δ) →
          ∀ j : ℕ, j ≤ p → ∀ x ∈ U,
            ckErr_S45 H₁ (postMetric F.observation s) s⁻¹ q' j x ≤ 1 / ((N : ℝ) + 1)) ∧
        ((∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ (postMetric F.observation s) s⁻¹ q' j x ≤ δ) →
          ∀ j : ℕ, j ≤ p → ∀ x ∈ U,
            ckErr_S45 H₁ (postMetric F.observation t) t⁻¹ q j x ≤ 1 / ((N : ℝ) + 1)) :=
    fun p N => ckTransfer_O75 F.observation p (1 / ((N : ℝ) + 1)) (by positivity)
  choose δB hδB hTB using hB
  refine ⟨δF, R, k, hδF, hR, ?_⟩
  intro t ht q hadm hesc
  -- drop the finitely many non-positive times
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (ht.eventually_gt_atTop 0)
  set u : ℕ → ℝ := fun m => t (m + M₀) with hudef
  have hu : ∀ m, 0 < u m := fun m => hM₀ (m + M₀) (Nat.le_add_left _ _)
  have hutend : Tendsto u atTop atTop := ht.comp (tendsto_add_atTop_nat M₀)
  -- step sizes
  have hF' : ∀ m, ∃ τ : ℝ, 0 < τ ∧ ∀ s : ℝ, u m ≤ s → s < u m + τ →
      ∀ (H₁ : FiniteVolumeHyperbolicModel.{u}) (U : TopologicalSpace.Opens H₁.Carrier)
        (q : H₁.Carrier → (postStage F.observation (u m)).Carrier)
        (q' : H₁.Carrier → (postStage F.observation s).Carrier),
        HEq q q' → ContMDiffOn (𝓡 3) (𝓡 3) ∞ q U → Set.InjOn q U →
        ((∀ j : ℕ, j ≤ k → ∀ x ∈ U,
            ckErr_S45 H₁ (postMetric F.observation (u m)) (u m)⁻¹ q j x ≤ δF) →
          ∀ j : ℕ, j ≤ k → ∀ x ∈ U, ckErr_S45 H₁ (postMetric F.observation s) s⁻¹ q' j x ≤ εr / 2) ∧
        ((∀ j : ℕ, j ≤ k → ∀ x ∈ U, ckErr_S45 H₁ (postMetric F.observation s) s⁻¹ q' j x ≤ δF) →
          ∀ j : ℕ, j ≤ k → ∀ x ∈ U,
            ckErr_S45 H₁ (postMetric F.observation (u m)) (u m)⁻¹ q j x ≤ εr / 2) :=
    fun m => hTF (u m) (hu m)
  choose τF hτF0 hτF using hF'
  choose τB hτB0 hτB using fun (m p N : ℕ) => hTB p N (u m) (hu m)
  choose TR hTR using fun (i : Fin old) (j : ℕ) => hRR i (j : ℝ)
  have hRR' : ∀ (m : ℕ) (i : Fin old) (j : ℕ), ∃ δ : ℝ, 0 < δ ∧ ∀ hi : sold i ≤ u m,
      TR i j ≤ u m → ∀ (s : ℝ) (hs : sold i ≤ s), u m ≤ s → s < u m + δ →
      postStage F.observation (u m) = postStage F.observation s →
      ∀ (x : (postStage F.observation (u m)).Carrier) (y : (postStage F.observation s).Carrier),
        HEq x y →
        y ∈ mold i s hs '' riemannianBallOf (Hold i).metric (Hold i).basepoint (j : ℝ) →
        x ∈ mold i (u m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ((j : ℝ) + 1) := by
    intro m i j
    by_cases hi : sold i ≤ u m
    · by_cases hT : TR i j ≤ u m
      · obtain ⟨δ, hδ, h⟩ := hTR i j (u m) hi hT
        exact ⟨δ, hδ, fun _ _ => h⟩
      · exact ⟨1, one_pos, fun _ h => absurd h hT⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose δR hδR0 hδR using hRR'
  have hev : ∀ m, ∃ δ : ℝ, 0 < δ ∧ δ < τF m ∧
      (∀ p ∈ Finset.range (m + 1), ∀ N ∈ Finset.range (m + 1), δ < τB m p N) ∧
      ∀ i, ∀ j ∈ Finset.range (m + 1), δ < δR m i j := by
    intro m
    have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < τF m := nhdsWithin_le_nhds (gt_mem_nhds (hτF0 m))
    have h2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ p ∈ Finset.range (m + 1), ∀ N ∈ Finset.range (m + 1),
        x < τB m p N :=
      (Filter.eventually_all_finset _).2 fun p _ => (Filter.eventually_all_finset _).2
        fun N _ => nhdsWithin_le_nhds (gt_mem_nhds (hτB0 m p N))
    have h3 : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ i, ∀ j ∈ Finset.range (m + 1), x < δR m i j :=
      eventually_all.2 fun i => (Filter.eventually_all_finset _).2
        fun j _ => nhdsWithin_le_nhds (gt_mem_nhds (hδR0 m i j))
    obtain ⟨x, hx0, hx1, hx2, hx3⟩ := (eventually_mem_nhdsWithin.and (h1.and (h2.and h3))).exists
    exact ⟨x, hx0, hx1, hx2, hx3⟩
  choose δm hδm0 hδm1 hδm2 hδm3 using hev
  -- regular slices just to the right
  choose sl hsl1 hsl2 hsl3 using fun m => hRegRight_O75 F.observation (u m) (hu m) (δm m) (hδm0 m)
  set t' : ℕ → ℝ := fun m => (sl m).time with ht'def
  let q' : (m : ℕ) → H.Carrier → (postStage F.observation (t' m)).Carrier := fun m x =>
    cast (congrArg OrientedThreeStage.Carrier (hsl3 m)) (q (m + M₀) x)
  have hqq' : ∀ m, HEq (q (m + M₀)) (q' m) := fun m => heq_cast_comp_O75 (hsl3 m) (q (m + M₀))
  have ht'tend : Tendsto t' atTop atTop := tendsto_atTop_mono (fun m => hsl1 m) hutend
  -- admissibility at the regular times
  have hadm' : ∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q' m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
      Set.InjOn (q' m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
      ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation (t' m)) (t' m)⁻¹ (q' m) k'' p < εr := by
    intro m
    obtain ⟨R'', hR'', hsm, hinj, hck⟩ := hadm (m + M₀)
    let UQ : TopologicalSpace.Opens H.Carrier :=
      ⟨riemannianBallOf H.metric H.basepoint (4 * R''), isOpen_riemannianBallOf _ _ _⟩
    have htr := (hτF m (t' m) (hsl1 m) ((hsl2 m).trans (by linarith [hδm1 m])) H UQ
      (q (m + M₀)) (q' m) (hqq' m) hsm hinj).1
      (fun j hj x hx => (hck j hj x hx).le)
    exact ⟨R'', hR'', contMDiffOn_heq_O75 (hsl3 m) (hqq' m) _ hsm,
      injOn_heq_O75 (hsl3 m) (hqq' m) _ hinj,
      fun j hj x hx => (htr j hj x hx).trans_lt (half_lt_self hεr)⟩
  -- escape at the regular times
  have hesc' : ∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t' m,
      q' m H.basepoint ∉ mold i (t' m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ := by
    intro i ρ
    set j : ℕ := ⌈ρ⌉₊ with hj
    obtain ⟨M₁, hM₁⟩ := hesc i ((j : ℝ) + 1)
    obtain ⟨M₂, hM₂⟩ := eventually_atTop.1
      ((hutend.eventually_ge_atTop (sold i)).and (hutend.eventually_ge_atTop (TR i j)))
    refine ⟨max (max M₁ j) M₂, fun m hm hi hmem => ?_⟩
    have hm1 : M₁ ≤ m + M₀ := ((le_max_left _ _).trans ((le_max_left _ _).trans hm)).trans
      (Nat.le_add_right _ _)
    have hjm : j ≤ m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
    have hiu : sold i ≤ u m := (hM₂ m ((le_max_right _ _).trans hm)).1
    have hTu : TR i j ≤ u m := (hM₂ m ((le_max_right _ _).trans hm)).2
    have hmem' : q' m H.basepoint ∈
        mold i (t' m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (j : ℝ) :=
      Set.image_mono (riemannianBallOf_mono _ _ (Nat.le_ceil ρ)) hmem
    have hx := hδR m i j hiu hTu (t' m) hi (hsl1 m)
      ((hsl2 m).trans (by linarith [hδm3 m i j (Finset.mem_range.2 (Nat.lt_succ_of_le hjm))]))
      (hsl3 m) (q (m + M₀) H.basepoint) (q' m H.basepoint) (cast_heq _ _).symm hmem'
    exact hM₁ (m + M₀) hm1 hiu hx
  obtain ⟨σ', hσ', H', S', hW', hconv', hESC', ψ', hψbp, hψconv, hfpart⟩ :=
    hT t' ht'tend (fun m => ⟨sl m, rfl⟩) q' hadm' hesc'
  refine ⟨fun m => σ' m + M₀, fun a b hab => Nat.add_lt_add_right (hσ' hab) _, H', S', hW', hconv',
    hESC', fun m x => cast (congrArg OrientedThreeStage.Carrier (hsl3 (σ' m)).symm) (ψ' m x),
    fun m => ?_, ?_, hfpart⟩
  · change cast _ (ψ' m H'.basepoint) = q (σ' m + M₀) H.basepoint
    rw [hψbp m]
    simp only [q', cast_cast, cast_eq]
  · intro δ r m' hδ hr
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    obtain ⟨I', hI'⟩ := hψconv (δB m' N) r m' (hδB m' N) hr
    refine ⟨max I' (max m' N), fun m hm => ?_⟩
    obtain ⟨U, hU, hsm, hemb, hck⟩ := hI' m ((le_max_left _ _).trans hm)
    have hσm : max m' N ≤ σ' m := ((le_max_right _ _).trans hm).trans (hσ'.id_le m)
    have hψψ : HEq (fun x => cast (congrArg OrientedThreeStage.Carrier (hsl3 (σ' m)).symm)
        (ψ' m x)) (ψ' m) := (heq_cast_comp_O75 (hsl3 (σ' m)).symm (ψ' m)).symm
    let UB : TopologicalSpace.Opens H'.Carrier :=
      ⟨riemannianBallOf H'.metric H'.basepoint r, isOpen_riemannianBallOf _ _ _⟩
    have hinjU : Set.InjOn (ψ' m) U := fun a ha b hb hab =>
      congrArg Subtype.val (hemb.isEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    have hsm' := contMDiffOn_heq_O75 (hsl3 (σ' m)).symm (heq_cast_comp_O75 (hsl3 (σ' m)).symm (ψ' m)) _ hsm
    have hinj' := injOn_heq_O75 (hsl3 (σ' m)).symm (heq_cast_comp_O75 (hsl3 (σ' m)).symm (ψ' m)) _ hinjU
    have htr := (hτB (σ' m) m' N (t' (σ' m)) (hsl1 (σ' m))
      ((hsl2 (σ' m)).trans (by
        linarith [hδm2 (σ' m) m'
          (Finset.mem_range.2 (Nat.lt_succ_of_le ((le_max_left _ _).trans hσm))) N
          (Finset.mem_range.2 (Nat.lt_succ_of_le ((le_max_right _ _).trans hσm)))]))
      H' UB _ (ψ' m) hψψ (hsm'.mono hU) (hinj'.mono hU)).2
      (fun j hj x hx => (hck j hj x hx).le)
    refine ⟨U, hU, hsm', isSmoothEmbedding_heq_O75 (hsl3 (σ' m)).symm
      (heq_cast_comp_O75 (hsl3 (σ' m)).symm (ψ' m)) U hemb, fun j hj x hx => (htr j hj x hx).trans_lt hN⟩

end GC.LongTime.Ch12
