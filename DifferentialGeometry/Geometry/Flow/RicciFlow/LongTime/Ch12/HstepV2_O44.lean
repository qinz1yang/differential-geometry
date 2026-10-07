import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.FixedRadiusDisj_O44
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.R3Assembly_O41
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Embed_S86

set_option autoImplicit false

/-! # CH12-O44 G2/G3: slow radius diagonal and the DISJ step `hstep_O44` ([FROZEN] CH12-O44).

* `exists_slow_radius_O44` (G2): a left-continuous step radius `L t = ℓ0 + κ t` (κ t = last level whose
  time `τ k` is `< t`), open tube `U = ⋃ k, Ioi (τ k) ×ˢ B(ℓ0 + k)`, `L ≤ 1/(2a)`, `L → ∞`, and every
  fixed-radius "eventually" property `D R t` holds at `R = L t` for late `t`.
* `patch_mono_alpha_O44`: a `PersistentModelPatch` for `α` is one for any `α' ≥ α ≥ 0` (only `speed`).
* `hstep_O44` (G3): the hstep binder of [FROZEN v2] CH12-O44 (INV2) from hHG03 and HLOW;
  αn := 2 / L, Ωn := ΩH ⊓ U, β := αH, Ω' := ΩH; DISJ from `disjoint_fixed_radius_O44`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

theorem exists_slow_radius_O44 (H : FiniteVolumeHyperbolicModel.{u}) {sH : ℝ} (hsH : 0 < sH)
    (a : ℝ → ℝ) (hpos : ∀ t, sH ≤ t → 0 < a t) (hanti : AntitoneOn a (Ici sH))
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → a t < ε)
    (D : ℝ → ℝ → Prop) (hD : ∀ R : ℝ, ∃ T : ℝ, ∀ t, T ≤ t → D R t) :
    ∃ (L : ℝ → ℝ) (U : Set (ℝ × H.Carrier)), IsOpen U ∧
      (∀ t, sH ≤ t → ∀ x, (t, x) ∈ U ↔ x ∈ riemannianBallOf H.metric H.basepoint (L t)) ∧
      (∀ t, 0 < L t) ∧ MonotoneOn L (Ici sH) ∧
      (∀ M : ℝ, ∃ T : ℝ, ∀ t, T ≤ t → sH ≤ t → M < L t) ∧
      (∀ t, sH ≤ t → L t ≤ (2 * a t)⁻¹) ∧
      ∃ Td : ℝ, ∀ t, Td ≤ t → sH ≤ t → D (L t) t := by
  classical
  have ha0 := hpos sH le_rfl
  have hℓ0 : 0 < (2 * a sH)⁻¹ := inv_pos.mpr (by positivity)
  let Lk : ℕ → ℝ := fun k => (2 * a sH)⁻¹ + k
  have hLk : ∀ k, 0 < Lk k := fun k => by positivity
  have hLkm : Monotone Lk := fun j k hjk => by
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    simp only [Lk]; linarith
  choose T1 hT1 using fun k : ℕ => hD (Lk k)
  choose T2 hT2 using fun k : ℕ => hdec (2 * Lk k)⁻¹ (inv_pos.mpr (by positivity))
  let S : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, (|T1 (j + 1)| + |T2 (j + 1)|)
  have hSm : Monotone S := fun j k hjk => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hjk) (fun _ _ _ => by positivity)
  have hS0 : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg fun _ _ => by positivity
  have hST : ∀ j, |T1 (j + 1)| + |T2 (j + 1)| ≤ S (j + 1) := fun j =>
    Finset.single_le_sum (f := fun j => |T1 (j + 1)| + |T2 (j + 1)|) (fun _ _ => by positivity)
      (Finset.self_mem_range_succ j)
  let τ : ℕ → ℝ := fun k => sH - 1 + k + S k
  have hτge : ∀ k, sH - 1 + k ≤ τ k := fun k => by simp only [τ]; linarith [hS0 k]
  have hT1τ : ∀ j, T1 (j + 1) ≤ τ (j + 1) := fun j => by
    simp only [τ]; push_cast
    linarith [le_abs_self (T1 (j + 1)), abs_nonneg (T2 (j + 1)), hST j]
  have hT2τ : ∀ j, T2 (j + 1) ≤ τ (j + 1) := fun j => by
    simp only [τ]; push_cast
    linarith [le_abs_self (T2 (j + 1)), abs_nonneg (T1 (j + 1)), hST j]
  let N : ℝ → ℕ := fun t => ⌈t - sH + 1⌉₊
  have hN : ∀ k t, τ k < t → k ≤ N t := fun k t h => by
    have h1 : (k : ℝ) ≤ ⌈t - sH + 1⌉₊ := by linarith [hτge k, Nat.le_ceil (t - sH + 1)]
    exact_mod_cast h1
  let κ : ℝ → ℕ := fun t => Nat.findGreatest (fun k => τ k < t) (N t)
  have hτ0 : ∀ t, sH ≤ t → τ 0 < t := fun t ht => by simp [τ, S]; linarith
  have hspec : ∀ t, sH ≤ t → τ (κ t) < t := fun t ht =>
    Nat.findGreatest_spec (P := fun k => τ k < t) (Nat.zero_le _) (hτ0 t ht)
  have hle : ∀ k t, τ k < t → k ≤ κ t := fun k t h => Nat.le_findGreatest (hN k t h) h
  refine ⟨fun t => Lk (κ t), ⋃ k, Ioi (τ k) ×ˢ riemannianBallOf H.metric H.basepoint (Lk k),
    isOpen_iUnion fun k => isOpen_Ioi.prod (isOpen_riemannianBallOf_S61 H _), ?_,
    fun t => hLk _, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    simp only [mem_iUnion, mem_prod, mem_Ioi]
    constructor
    · rintro ⟨k, hk, hx⟩
      exact riemannianBallOf_mono _ _ (hLkm (hle k t hk)) hx
    · intro hx; exact ⟨κ t, hspec t ht, hx⟩
  · intro s hs t ht hst
    exact hLkm (hle _ t ((hspec s hs).trans_le hst))
  · intro M
    refine ⟨τ ⌈M⌉₊ + 1, fun t hT ht => ?_⟩
    have hk := hle ⌈M⌉₊ t (by linarith)
    have h1 : (⌈M⌉₊ : ℝ) ≤ κ t := by exact_mod_cast hk
    simp only [Lk]; linarith [Nat.le_ceil M]
  · intro t ht
    have hat := hpos t ht
    change Lk (κ t) ≤ (2 * a t)⁻¹
    rcases Nat.eq_zero_or_pos (κ t) with h0 | hpos'
    · rw [h0]; simp only [Lk, Nat.cast_zero, add_zero]
      exact inv_anti₀ (by positivity) (by linarith [hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht])
    · obtain ⟨j, hj⟩ : ∃ j, κ t = j + 1 := ⟨κ t - 1, by omega⟩
      have hτj : τ (j + 1) < t := by rw [← hj]; exact hspec t ht
      have h2 := hT2 (j + 1) t (by linarith [hT2τ j])
      rw [hj, le_inv_comm₀ (hLk _) (by positivity)]
      rw [mul_inv] at h2
      linarith
  · refine ⟨τ 1 + 1, fun t hT ht => ?_⟩
    have h1 : 1 ≤ κ t := hle 1 t (by linarith)
    obtain ⟨j, hj⟩ : ∃ j, κ t = j + 1 := ⟨κ t - 1, by omega⟩
    have hτj : τ (j + 1) < t := by rw [← hj]; exact hspec t ht
    simp only
    rw [hj]
    exact hT1 (j + 1) t (by linarith [hT1τ j])

theorem patch_mono_alpha_O44 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {H : FiniteVolumeHyperbolicModel.{u}} {T : ℝ} (hT : 0 < T)
    {α α' : ℝ → ℝ} (hαα : ∀ t, T ≤ t → 0 ≤ α t ∧ α t ≤ α' t)
    {domain : ℝ → TopologicalSpace.Opens H.Carrier}
    {f : (t : ℝ) → T ≤ t → H.Carrier → (postStage F.observation t).Carrier} {t₀ : ℝ} {x₀ : H.Carrier}
    (hp : Nonempty (PersistentModelPatch F H T α domain f t₀ x₀)) :
    Nonempty (PersistentModelPatch F H T α' domain f t₀ x₀) := by
  obtain ⟨p⟩ := hp
  exact ⟨{ p with
    speed := by
      intro t ht hTt x hx
      have h1 := p.speed t ht hTt x hx
      obtain ⟨h0, hle⟩ := hαα t hTt
      have h3 : 0 < (t : ℝ) := hT.trans_le hTt
      dsimp only at h1 ⊢
      refine lt_of_lt_of_le h1 ?_
      gcongr }⟩

theorem hstep_O44 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (HLOW : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (sH : ℝ) (hsH : 0 < sH) (αH : ℝ → ℝ)
      (ΩH : TopologicalSpace.Opens (ℝ × H.Carrier))
      (mapH : (t : ℝ) → sH ≤ t → H.Carrier → (postStage F.observation t).Carrier),
      (∀ t, sH ≤ t → 0 < αH t) → (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αH t < ε) →
      (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 ΩH t)) →
      (∀ t (ht : sH ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 ΩH t => mapH t ht x)) →
      (∀ t, sH ≤ t → riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹) ⊆ sourceSlice_CX5 ΩH t) →
      (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αH t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹),
          ckErr_O21 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αH t) →
      ∀ R : ℝ, ∃ w : ℝ, 0 < w ∧ ∃ T : ℝ, ∀ t (ht : sH ≤ t), T ≤ t →
        ∀ y ∈ riemannianBallOf H.metric H.basepoint R, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hsH.trans_le ht))
            (postMetric F.observation t)) (mapH t ht y) = ENNReal.ofReal r ∧
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (hsH.trans_le ht)) (postMetric F.observation t)) (mapH t ht y) r)
    :
    ∀ wstar : ℝ, 0 < wstar →
      ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
        (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
        (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
        (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
        (      (∀ i, 0 < start i) ∧
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
          (sourceSlice_CX5 (Ω i)) (map i) t x))) →
        (∀ i, (∃ (β : ℝ → ℝ) (Ω' : TopologicalSpace.Opens (ℝ × (model i).Carrier)),
      (∀ t, start i ≤ t → 0 < β t) ∧ (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧
      (∀ t (ht : start i ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 Ω' t)) ∧
      (∀ t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 Ω' t => map i t ht x)) ∧
      (∀ t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint (2 * (β t)⁻¹) ⊆
        sourceSlice_CX5 Ω' t) ∧
      (∀ t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(β t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (β t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < β t) ∧
      (∀ t, start i ≤ t → (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier) ⊆
        riemannianBallOf (model i).metric (model i).basepoint (2 * β t)⁻¹))) →
              (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) →
        ∃ R0 : Fin count → ℝ, ∀ (H : FiniteVolumeHyperbolicModel.{u}) (sH : ℝ) (hsH : 0 < sH)
          (αH : ℝ → ℝ) (ΩH : TopologicalSpace.Opens (ℝ × H.Carrier))
          (mapH : (t : ℝ) → sH ≤ t → H.Carrier → (postStage F.observation t).Carrier),
          (        (∀ t, sH ≤ t → 0 < αH t) ∧ AntitoneOn αH (Ici sH) ∧
        (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αH t < ε) ∧
        (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 ΩH t)) ∧
        (∀ t (ht : sH ≤ t),
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 ΩH t => mapH t ht x)) ∧
        (∀ t, sH ≤ t →
          riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹) ⊆ sourceSlice_CX5 ΩH t) ∧
        (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αH t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αH t) ∧
        (∀ Ω' : TopologicalSpace.Opens (ℝ × H.Carrier), Ω' ≤ ΩH →
          ∀ t (_ht : sH ≤ t), ∀ x ∈ sourceSlice_CX5 Ω' t,
            Nonempty (PersistentModelPatch F H sH αH (sourceSlice_CX5 Ω') mapH t x)) ∧
        (∀ t (ht : sH ≤ t), ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hsH.trans_le ht))
            (postMetric F.observation t)) (mapH t ht y) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (hsH.trans_le ht)) (postMetric F.observation t)) (mapH t ht y) r)) →
          (∀ i : Fin count, ∃ T : ℝ, ∀ t (hn : sH ≤ t) (hi : start i ≤ t), T ≤ t →
            mapH t hn H.basepoint ∉
              map i t hi '' riemannianBallOf (model i).metric (model i).basepoint (R0 i)) →
          ∃ (αn : ℝ → ℝ) (Ωn : TopologicalSpace.Opens (ℝ × H.Carrier)),
            (∀ t, sH ≤ t → 0 < αn t) ∧ AntitoneOn αn (Ici sH) ∧
            (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αn t < ε) ∧
            (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 Ωn t)) ∧
            (∀ t (ht : sH ≤ t),
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ωn t => mapH t ht x)) ∧
            (∀ t, sH ≤ t → riemannianBallOf H.metric H.basepoint (2 * (αn t)⁻¹) ⊆ sourceSlice_CX5 Ωn t) ∧
            (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αn t)⁻¹⌉₊ →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αn t)⁻¹),
                ckErr_O21 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αn t) ∧
            (∀ t (_ht : sH ≤ t), ∀ x ∈ sourceSlice_CX5 Ωn t,
              Nonempty (PersistentModelPatch F H sH αn (sourceSlice_CX5 Ωn) mapH t x)) ∧
            (∃ (β : ℝ → ℝ) (Ω' : TopologicalSpace.Opens (ℝ × (H).Carrier)),
      (∀ t, sH ≤ t → 0 < β t) ∧ (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧
      (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 Ω' t)) ∧
      (∀ t (ht : sH ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 Ω' t => mapH t ht x)) ∧
      (∀ t, sH ≤ t → riemannianBallOf (H).metric (H).basepoint (2 * (β t)⁻¹) ⊆
        sourceSlice_CX5 Ω' t) ∧
      (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(β t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (H).metric (H).basepoint (2 * (β t)⁻¹),
          ckErr_O21 (H) (postMetric F.observation t) t⁻¹ (mapH t ht) k p < β t) ∧
      (∀ t, sH ≤ t → (sourceSlice_CX5 Ωn t : Set (H).Carrier) ⊆
        riemannianBallOf (H).metric (H).basepoint (2 * β t)⁻¹)) ∧
            ∃ Td : ℝ, ∀ t (i : Fin count) (hi : start i ≤ t) (hn : sH ≤ t), Td ≤ t →
              Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
                (mapH t hn '' (sourceSlice_CX5 Ωn t : Set H.Carrier)) := by
  intro wstar hw count model start α Ω map h9 hinv2 _hdisj
  obtain ⟨R0, hR0⟩ := disjoint_fixed_radius_O44 F K hHG03 wstar hw model start Ω map h9.1 hinv2
  refine ⟨R0, ?_⟩
  intro H sH hsH αH ΩH mapH hH cesc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hH
  have c7' : ∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αH t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹),
        ckErr_O21 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αH t := c7
  have hlow := HLOW H sH hsH αH ΩH mapH c1 c3 c4 c5 c6 c7'
  obtain ⟨L, U, hU, hUt, hLpos, hLmono, hLinf, hLa, Td, hTd⟩ := exists_slow_radius_O44 H hsH αH c1 c2 c3
    (fun R t => ∀ (i : Fin count) (hi : start i ≤ t) (hn : sH ≤ t),
      Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
        (mapH t hn '' riemannianBallOf H.metric H.basepoint R))
    (fun R => by
      obtain ⟨T, hT⟩ := hR0 H sH hsH αH ΩH mapH c1 c3 c4 c6 c9 cesc R (hlow R)
      exact ⟨T, fun t ht i hi hn => hT t i hi hn ht⟩)
  let Ωn : TopologicalSpace.Opens (ℝ × H.Carrier) := ΩH ⊓ ⟨U, hU⟩
  have hsub : ∀ t, (sourceSlice_CX5 Ωn t : Set H.Carrier) ⊆ sourceSlice_CX5 ΩH t :=
    fun t x hx => hx.1
  have hLle2 : ∀ t, sH ≤ t → L t ≤ 2 * (αH t)⁻¹ := fun t ht => by
    have h := hLa t ht
    rw [mul_inv] at h
    nlinarith [inv_pos.mpr (c1 t ht)]
  have hsl : ∀ t, sH ≤ t →
      (sourceSlice_CX5 Ωn t : Set H.Carrier) = riemannianBallOf H.metric H.basepoint (L t) := by
    intro t ht
    ext x
    constructor
    · intro hx; exact (hUt t ht x).mp hx.2
    · intro hx
      exact ⟨c6 t ht (riemannianBallOf_mono _ _ (hLle2 t ht) hx), (hUt t ht x).mpr hx⟩
  have hαn : ∀ t, 2 * (2 / L t)⁻¹ = L t := fun t => by
    have := (hLpos t).ne'; field_simp
  have hαle : ∀ t, sH ≤ t → αH t ≤ 2 / L t := fun t ht => by
    have h1 := c1 t ht
    have h2 := hLpos t
    rw [le_div_iff₀ h2]
    have h3 := mul_le_mul_of_nonneg_left (hLa t ht) (by positivity : (0 : ℝ) ≤ 2 * αH t)
    rw [mul_inv_cancel₀ (by positivity)] at h3
    nlinarith
  refine ⟨fun t => 2 / L t, Ωn, fun t _ => div_pos two_pos (hLpos t), ?_, ?_,
    fun t ht => (c4 t ht).mono (hsub t),
    fun t ht => isSmoothEmbedding_restrict_open_S86 (mapH t ht) (sourceSlice_CX5 ΩH t)
      (sourceSlice_CX5 Ωn t) (hsub t) (c5 t ht), ?_, ?_, ?_,
    ⟨αH, ΩH, c1, c3, c4, c5, c6, c7', fun t ht => by
      rw [hsl t ht]; exact riemannianBallOf_mono _ _ (hLa t ht)⟩, Td, ?_⟩
  · intro s hs t ht hst
    have h1 := hLpos s
    have h2 := hLmono hs ht hst
    change 2 / L t ≤ 2 / L s
    gcongr
  · intro ε hε
    obtain ⟨T, hT⟩ := hLinf (2 / ε)
    refine ⟨max T sH, fun t ht => ?_⟩
    have h1 := hT t ((le_max_left _ _).trans ht) ((le_max_right _ _).trans ht)
    have h2 := hLpos t
    rw [div_lt_iff₀ hε] at h1
    rw [div_lt_iff₀ h2]
    linarith
  · intro t ht
    rw [hαn t, hsl t ht]
  · intro t ht k hk p hp
    rw [hαn t] at hp
    have hceil : ⌈(2 / L t)⁻¹⌉₊ ≤ ⌈(αH t)⁻¹⌉₊ :=
      Nat.ceil_mono (inv_anti₀ (c1 t ht) (hαle t ht))
    exact (c7' t ht k (hk.trans (max_le_max le_rfl hceil)) p
      (riemannianBallOf_mono _ _ (hLle2 t ht) hp)).trans_le (hαle t ht)
  · intro t ht x hx
    exact patch_mono_alpha_O44 hsH (fun s hs => ⟨(c1 s hs).le, hαle s hs⟩) (c8 Ωn inf_le_left t ht x hx)
  · intro t i hi hn hT
    exact (hTd t hT hn i hi hn).mono_right (image_mono (hsl t hn).le)

end GC.LongTime.Ch12
