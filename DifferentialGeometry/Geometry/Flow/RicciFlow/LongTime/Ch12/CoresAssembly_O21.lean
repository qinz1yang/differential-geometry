import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchMono_O15
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingDomain_CX5

set_option autoImplicit false

/-! CH12-O21 G1 — H5 assembly (blueprint HPI06–HPI08 bookkeeping).

From a finite family of persistent models (HPI05 output, domains already shrunk so that the
late slice images are disjoint) and a coverage statement (HPI06 + HPI07 + diagonal accuracy),
build `BufferedPersistentCores F K` with a common start (a finite bound) and a common accuracy
`β + Σ αᵢ`; every patch is moved by `persistentModelPatch_mono_O15`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- C^k pullback error `|∇^k (c • f^*g' - h)|_h` at `p` (the `metric_error` expression; lead
ruling D4: ℝ-valued helper, same body as the sheet's `ckErr_O15s`). -/
def ckErr_O21 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (k : ℕ)
    (p : H.Carrier) : ℝ :=
  tensor0SFiberNorm H.metric p (2 + k)
    (iteratedMetricCovariantDerivative H.metric 2
      (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner g' f q - H.metric.inner q)).uncurryLeft) k p)

/-- A compact subset of a finite-volume hyperbolic model lies in a Riemannian ball
(same proof as `CuspP1.exists_ball_of_isCompact_CPA2`, restated to keep the import closure small). -/
theorem exists_ball_of_isCompact_O21 {H : FiniteVolumeHyperbolicModel.{u}} {S : Set H.Carrier}
    (hS : IsCompact S) : ∃ R : ℝ, 0 < R ∧ S ⊆ riemannianBallOf H.metric H.basepoint R := by
  let B : ℕ → Set H.Carrier := fun n => riemannianBallOf H.metric H.basepoint (n : ℝ)
  have hcover : S ⊆ ⋃ n, B n := by
    intro x _
    have hfin : riemannianEDistOf H.metric H.basepoint x ≠ ⊤ :=
      riemannianEDistOf_ne_top H.metric H.basepoint x
    obtain ⟨n, hn⟩ := exists_nat_gt (riemannianEDistOf H.metric H.basepoint x).toReal
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change riemannianEDistOf H.metric H.basepoint x < ENNReal.ofReal (n : ℝ)
    have hq : (0 : ℝ) < n := lt_of_le_of_lt ENNReal.toReal_nonneg hn
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hq).mpr hn
  have hmono : Monotone B := fun m n h =>
    riemannianBallOf_mono _ _ (Nat.cast_le.mpr h)
  obtain ⟨n, hn⟩ := hS.elim_directed_cover B
    (fun n => isOpen_riemannianBallOf H.metric H.basepoint (n : ℝ)) hcover hmono.directed_le
  exact ⟨(n : ℝ) + 1, by positivity, hn.trans (riemannianBallOf_mono _ _ (by linarith))⟩

/-- A finite sum of terms each `< e / (2 (n + 1))` is `≤ e / 2`. -/
theorem sum_le_half_O21 {n : ℕ} (f : Fin n → ℝ) {e : ℝ} (he : 0 < e)
    (hf : ∀ i, f i ≤ e / (2 * ((n : ℝ) + 1))) : ∑ i, f i ≤ e / 2 := by
  calc ∑ i, f i ≤ ∑ _i : Fin n, e / (2 * ((n : ℝ) + 1)) := Finset.sum_le_sum fun i _ => hf i
    _ = (n : ℝ) * (e / (2 * ((n : ℝ) + 1))) := by simp
    _ ≤ e / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- One term of a finite family is bounded by the sum of absolute values. -/
theorem le_sum_abs_O21 {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : f i ≤ ∑ j, |f j| :=
  (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i))

/-- **H5 assembly** (sheet S5 conclusion, verbatim).  `hfam` = HPI05 (finite disjoint family of
persistent models, S4 per-model fields) + HPI06/HPI07 coverage with a diagonal accuracy `β`
(shape frozen in `[FROZEN] CH12-O21`). -/
theorem exists_bufferedCores_of_family_O21 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hfam : ∃ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
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
      (∃ w0 : ℝ, 0 < w0 ∧ ∃ (β : ℝ → ℝ) (Tc : ℝ), (∀ t, Tc ≤ t → 0 < β t) ∧
        AntitoneOn β (Ici Tc) ∧ (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧
        ∀ t (ht0 : 0 < t), Tc ≤ t → ∀ w' : ℝ, β t ≤ w' → w' ≤ w0 →
          ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p =
              ENNReal.ofReal r →
            ENNReal.ofReal (w' * r ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p r →
            ∃ (i : Fin count) (hi : start i ≤ t),
              p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹)) :
    ∃ B : BufferedPersistentCores F K,
      Nonempty (∀ i : Fin B.count, HyperbolicTruncation (B.model i)) := by
  obtain ⟨count, model, start, α, Ω, map, hs0, hα0, hαanti, hαdec, hsmooth, hemb, hball, herr,
    hpatch, ⟨Td, hdisj⟩, ⟨w0, hw0, β, Tc, hβ0, hβanti, hβdec, hcov⟩⟩ := hfam
  have hc : (0 : ℝ) < 2 * ((count : ℝ) + 1) := by positivity
  choose Tw hTw using fun i => hαdec i (w0 / (2 * ((count : ℝ) + 1))) (div_pos hw0 hc)
  obtain ⟨Tb, hTb⟩ := hβdec (w0 / 2) (by positivity)
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℝ, s = 1 + |Td| + |Tc| + |Tb| + (∑ j, |start j|) + ∑ j, |Tw j| :=
    ⟨_, rfl⟩
  have habs : 0 ≤ |Td| ∧ 0 ≤ |Tc| ∧ 0 ≤ |Tb| ∧ 0 ≤ ∑ j, |start j| ∧ 0 ≤ ∑ j, |Tw j| :=
    ⟨abs_nonneg _, abs_nonneg _, abs_nonneg _, Finset.sum_nonneg fun j _ => abs_nonneg _,
      Finset.sum_nonneg fun j _ => abs_nonneg _⟩
  have hs0pos : 0 < s₀ := by rw [hs₀]; linarith [habs.1, habs.2.1, habs.2.2.1, habs.2.2.2.1]
  have hstart : ∀ i, start i ≤ s₀ := fun i => by
    rw [hs₀]; linarith [le_sum_abs_O21 start i, habs.1, habs.2.1, habs.2.2.1, habs.2.2.2.2]
  have hTwle : ∀ i, Tw i ≤ s₀ := fun i => by
    rw [hs₀]; linarith [le_sum_abs_O21 Tw i, habs.1, habs.2.1, habs.2.2.1, habs.2.2.2.1]
  have hTd : Td ≤ s₀ := by
    rw [hs₀]; linarith [le_abs_self Td, habs.2.1, habs.2.2.1, habs.2.2.2.1, habs.2.2.2.2]
  have hTc : Tc ≤ s₀ := by
    rw [hs₀]; linarith [le_abs_self Tc, habs.1, habs.2.2.1, habs.2.2.2.1, habs.2.2.2.2]
  have hTble : Tb ≤ s₀ := by
    rw [hs₀]; linarith [le_abs_self Tb, habs.1, habs.2.1, habs.2.2.2.1, habs.2.2.2.2]
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, ∀ t, A t = β t + ∑ i, α i t := ⟨_, fun _ => rfl⟩
  have hαpos : ∀ i t, s₀ ≤ t → 0 < α i t := fun i t ht => hα0 i t ((hstart i).trans ht)
  have hβpos : ∀ t, s₀ ≤ t → 0 < β t := fun t ht => hβ0 t (hTc.trans ht)
  have hαle : ∀ i t, s₀ ≤ t → α i t ≤ A t := fun i t ht => by
    rw [hA]
    have := Finset.single_le_sum (f := fun j => α j t) (fun j _ => (hαpos j t ht).le)
      (Finset.mem_univ i)
    linarith [hβpos t ht]
  have hβle : ∀ t, s₀ ≤ t → β t ≤ A t := fun t ht => by
    rw [hA]; linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (hαpos j t ht).le]
  have hApos : ∀ t, s₀ ≤ t → 0 < A t := fun t ht => (hβpos t ht).trans_le (hβle t ht)
  have hAw0 : ∀ t, s₀ ≤ t → A t ≤ w0 := fun t ht => by
    rw [hA]
    have h1 := sum_le_half_O21 (fun i => α i t) hw0 fun i => (hTw i t ((hTwle i).trans ht)).le
    linarith [hTb t (hTble.trans ht)]
  have hinv : ∀ i t, s₀ ≤ t → (A t)⁻¹ ≤ (α i t)⁻¹ := fun i t ht =>
    inv_anti₀ (hαpos i t ht) (hαle i t ht)
  have hball' : ∀ i t (ht : s₀ ≤ t) (c : ℝ), c ≤ 2 →
      riemannianBallOf (model i).metric (model i).basepoint (c * (A t)⁻¹) ⊆
        sourceSlice_CX5 (Ω i) t := fun i t ht c hc2 => by
    refine (riemannianBallOf_mono _ _ ?_).trans (hball i t ((hstart i).trans ht))
    have h1 := hinv i t ht
    have h2 : 0 < (A t)⁻¹ := inv_pos.mpr (hApos t ht)
    nlinarith
  have hballα : ∀ i t (ht : s₀ ≤ t) (c : ℝ), c ≤ 2 →
      riemannianBallOf (model i).metric (model i).basepoint (c * (A t)⁻¹) ⊆
        riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹) :=
    fun i t ht c hc2 => riemannianBallOf_mono _ _ (by
      have h1 := hinv i t ht
      have h2 : 0 < (A t)⁻¹ := inv_pos.mpr (hApos t ht)
      nlinarith)
  have hk : ∀ i t (_ : s₀ ≤ t) (k : ℕ), k ≤ max K ⌈(A t)⁻¹⌉₊ → k ≤ max K ⌈(α i t)⁻¹⌉₊ :=
    fun i t ht k hk => hk.trans (max_le_max le_rfl (Nat.ceil_mono (hinv i t ht)))
  have hanti : AntitoneOn A (Ici s₀) := fun a ha b hb hab => by
    rw [hA, hA]
    have hβab := hβanti (mem_Ici.mpr (hTc.trans ha)) (mem_Ici.mpr (hTc.trans hb)) hab
    have hsum : ∑ i, α i b ≤ ∑ i, α i a := Finset.sum_le_sum fun i _ =>
      hαanti i (mem_Ici.mpr ((hstart i).trans ha)) (mem_Ici.mpr ((hstart i).trans hb)) hab
    linarith
  have hdecay : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → A t < ε := fun ε hε => by
    choose Te hTe using fun i => hαdec i (ε / (2 * ((count : ℝ) + 1))) (div_pos hε hc)
    obtain ⟨Tβ, hTβ⟩ := hβdec (ε / 2) (by positivity)
    refine ⟨|Tβ| + ∑ j, |Te j|, fun t ht => ?_⟩
    have hs : 0 ≤ ∑ j, |Te j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    rw [hA]
    have h1 := sum_le_half_O21 (fun i => α i t) hε fun i =>
      (hTe i t (by linarith [le_sum_abs_O21 Te i, abs_nonneg Tβ])).le
    linarith [hTβ t (by linarith [le_abs_self Tβ])]
  refine ⟨{
    count := count
    model := model
    start := s₀
    start_pos := hs0pos
    accuracy := A
    accuracy_pos := hApos
    accuracy_antitone := hanti
    accuracy_decay := hdecay
    domain := fun i t => sourceSlice_CX5 (Ω i) t
    map := fun i t ht => map i t ((hstart i).trans ht)
    smooth := fun i t ht => hsmooth i t _
    embedding := fun i t ht => hemb i t _
    advertised_ball := fun i t ht => by
      simpa only [one_mul] using hball' i t ht 1 (by norm_num)
    exhausts := fun i S hS => by
      obtain ⟨R, hR, hSR⟩ := exists_ball_of_isCompact_O21 hS
      obtain ⟨T1, hT1⟩ := hαdec i R⁻¹ (inv_pos.mpr hR)
      refine ⟨max s₀ T1, fun t ht => hSR.trans ?_⟩
      have hts : s₀ ≤ t := (le_max_left _ _).trans ht
      refine (riemannianBallOf_mono _ _ ?_).trans (hball i t ((hstart i).trans hts))
      have h1 : R < (α i t)⁻¹ :=
        (lt_inv_comm₀ (hαpos i t hts) hR).mp (hT1 t ((le_max_right _ _).trans ht))
      linarith
    disjoint := fun t ht i j hij => hdisj t i j _ _ (hTd.trans ht) hij
    metric_error := fun i t ht => by
      intro h error k hk' p hp
      exact (herr i t ((hstart i).trans ht) k (hk i t ht k hk') p
        (hballα i t ht 1 (by norm_num) (by simpa only [one_mul] using hp))).trans_le
        (hαle i t ht)
    thick_covered := fun t ht p r hr hcr hvol => by
      obtain ⟨i, hi, hp⟩ := hcov t (hs0pos.trans_le ht) (hTc.trans ht) (A t) (hβle t ht)
        (hAw0 t ht) p r hr hcr hvol
      exact ⟨i, hp⟩
    static_patches := fun i t ht x hx =>
      persistentModelPatch_mono_O15 (hpatch i t ((hstart i).trans ht) x hx) (hstart i)
        (fun t' ht' => (hαpos i t' ht').le) (fun t' ht' => hαle i t' ht') (fun _ _ => le_rfl)
    buffer_domain := fun i t ht => hball' i t ht 2 le_rfl
    buffer_error := fun i t ht => by
      intro h error k hk' p hp
      exact (herr i t ((hstart i).trans ht) k (hk i t ht k hk') p
        (hballα i t ht 2 le_rfl hp)).trans_le (hαle i t ht) }, ⟨?_⟩⟩
  exact fun i => Classical.choice (hHG03 _)

end GC.LongTime.Ch12
