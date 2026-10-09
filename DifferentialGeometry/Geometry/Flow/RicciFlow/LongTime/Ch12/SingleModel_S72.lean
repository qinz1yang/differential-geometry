import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SmoothedEmbedding_S72
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.AlphaCkErrS71_S72
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchWiring_S61
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchWiringTail_S118

set_option autoImplicit false

/-! # CH12-S72 G1b: `singleModel_S72` (A09-1c, sheet S4)

Statement = `[FROZEN v2] CH12-S72` G1 (sheet S4 with `ckErr_S45` / `sourceSlice_CX5`, S8 v5 data as binders;
`hcomp` binder removed: `hcomp_S71` is used inside `exists_alpha_ckErr_S72`).  Proof: `α₀` and `Ω₀` from S61, shrink to `Ω''` (slice inside `B(ρ_j)`), a second
diagonal `β` giving `B(2 β⁻¹) ⊆ slice Ω'' t` (the `τ`-condition, chosen after `Ω₀`), `α' = max α₀ β`
from a start where `η_j < 1`; patches by `patch_mono_S72`, embedding by `smoothedMap_embedding_S72`. -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem singleModel_S72 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (K : ℕ) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ) {T : ℝ} (hT : 0 < T)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ)
    (hη : ∀ j, 0 ≤ η j) (hηt : Tendsto η atTop (𝓝 0)) (hρm : Monotone ρ)
    (hρ : Tendsto ρ atTop atTop) (hρpos : ∀ j, 0 < ρ j) (hν : Tendsto ν atTop atTop)
    (hE : ∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j))
    (hEb : ∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
      Function.Bijective (fun p => E j (μ, p)))
    (hE0 : ∀ j p, E j (0, p) = p)
    (hsupp : ∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (hispeed : ∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
      let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ (timeVector_CX5 μ);
      H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2)
    (hEclose : ∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j)
    (hend : ∀ j (h1 : dyadicTime_CX5 T (j + 1) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)))
      (h2 : dyadicTime_CX5 T (j + 1) ∈ Icc (dyadicTime_CX5 T (j + 1)) (dyadicTime_CX5 T (j + 1 + 1))),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j), f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p)
    (hacc : ∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j)
    (J₀ : ℕ)
    (hlift0 : ∀ j, J₀ ≤ j → ∀ (s : ℝ), s ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
        (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
        (_ : b ≤ (F.tower.history n).horizon)
        (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
          first ≤ (F.tower.history n).toHistory.activeStage r ∧
            (F.tower.history n).toHistory.activeStage r ≤ last)
        (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
          (hrs : (r : ℝ) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
            ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
            (f j r hrs p))
    (hthick : ∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))) (μ : ℝ),
      ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (dyadicTime_pos_CX5 hT j) ht.1))
          (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
        ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
          (inv_pos.mpr (lt_of_lt_of_le (dyadicTime_pos_CX5 hT j) ht.1)) (postMetric F.observation t))
          (f j t ht (E j (μ, y))) r) :
    ∃ (start : ℝ) (hstart : 0 < start) (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × H.Carrier))
      (map : (t : ℝ) → start ≤ t → H.Carrier → (postStage F.observation t).Carrier),
      (∀ t, start ≤ t → 0 < α t) ∧ AntitoneOn α (Ici start) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : start ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => map t ht x)) ∧
      (∀ t, start ≤ t →
        riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ (map t ht) k p < α t) ∧
      (∀ Ω' : TopologicalSpace.Opens (ℝ × H.Carrier), Ω' ≤ Ω →
        ∀ t (_ht : start ≤ t), ∀ x ∈ sourceSlice_CX5 Ω' t,
          Nonempty (PersistentModelPatch F H start α (sourceSlice_CX5 Ω') map t x)) ∧
      (∀ t (ht : start ≤ t), ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
          (postMetric F.observation t)) (map t ht y) = ENNReal.ofReal r ∧
        ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
          (inv_pos.mpr (hstart.trans_le ht)) (postMetric F.observation t)) (map t ht y) r) := by
  classical
  obtain ⟨θ, B, hBpos, hθ, -, hθrange, hθ0, hθ1, hθderiv⟩ := exists_smoothingTheta_CX5
  have hacc2 : ∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j :=
    fun j t ht => ⟨(hacc j t ht).1, (hacc j t ht).2.2⟩
  obtain ⟨start₀, α₀, hTs₀, hpos₀, hanti₀, hdec₀, hbud₀, hck₀⟩ :=
    exists_alpha_ckErr_S72 F H hT K B f E η ρ ν hηt hρ hν hEb hsupp hEclose hacc2
  obtain ⟨Ω₀, hΩ₀, hpatch₀⟩ := persistentModelPatch_of_windows_tail_S118 F H hT hTs₀ α₀ θ B hBpos.le hθ
    hθrange hθ0 hθ1 hθderiv f E η ρ ν hη hηt hρ hE (fun j μ => (hEb j μ).2) hE0 hsupp hispeed hend
    hacc2 hbud₀ J₀ hlift0
  obtain ⟨Ω'', hΩ''le, hΩ'', hsl⟩ := exists_slice_in_ball_S61 H hT ρ hρm hρ Ω₀ hΩ₀
  choose τ hτ using hΩ''
  obtain ⟨startβ, β, hTsβ, hposβ, hantiβ, hdecβ, hkeyβ⟩ := exists_diagonal_alpha_S61 hT
    (fun m j => τ (2 * m) < dyadicTime_CX5 T j)
    (fun m => eventually_atTop.1 ((dyadicTime_tendsto_CX5 hT).eventually_gt_atTop (τ (2 * m))))
  obtain ⟨J1, hJ1⟩ : ∃ J : ℕ, ∀ j, J ≤ j → η j < 1 :=
    eventually_atTop.1 (hηt.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  set start := max (max start₀ startβ) (dyadicTime_CX5 T J1) with hstart_def
  have hs0 : start₀ ≤ start := (le_max_left _ _).trans (le_max_left _ _)
  have hsβ : startβ ≤ start := (le_max_right _ _).trans (le_max_left _ _)
  have hsJ : dyadicTime_CX5 T J1 ≤ start := le_max_right _ _
  have hTs : T ≤ start := hTs₀.trans hs0
  have hstart : 0 < start := hT.trans_le hTs
  have hmain : ∀ t (ht : start ≤ t),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (smoothedPhysicalMap_CX5 H T hT θ f E t (hTs.trans ht))
        (sourceSlice_CX5 Ω'' t) ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 Ω'' t => smoothedPhysicalMap_CX5 H T hT θ f E t (hTs.trans ht) x) := by
    intro t ht
    have hTt : T ≤ t := hTs.trans ht
    have hmem := dyadicIndex_mem_CX5 hT hTt
    have hw : t ∈ Icc (dyadicTime_CX5 T (dyadicIndex_CX5 T t))
        (dyadicTime_CX5 T (dyadicIndex_CX5 T t + 1)) := ⟨hmem.1, hmem.2.le⟩
    have hj1 : η (dyadicIndex_CX5 T t) < 1 :=
      hJ1 _ (le_dyadicIndex_CX5 hT J1 (hsJ.trans ht))
    exact smoothedMap_embedding_v2_S72 H (postMetric F.observation t) t⁻¹
      (f (dyadicIndex_CX5 T t) t hw)
      (fun p => E (dyadicIndex_CX5 T t) (θ (t / dyadicTime_CX5 T (dyadicIndex_CX5 T t)), p))
      (ρ (dyadicIndex_CX5 T t)) (hρpos _).le (hEb _ _).1 (hEb _ _).2 (hsupp _ _)
      (fun p hp => lt_of_le_of_lt
        (hEclose _ _ (hθrange _) 0 (Nat.zero_le _) p hp) hj1)
      (hacc _ t hw).1 (hacc _ t hw).2.1
      (fun p hp => lt_trans ((hacc _ t hw).2.2 0 (Nat.zero_le _) p hp) hj1)
      (sourceSlice_CX5 Ω'' t) (hsl t hTt)
  have hαle : ∀ t, α₀ t ≤ max (α₀ t) (β t) := fun t => le_max_left _ _
  refine ⟨start, hstart, fun t => max (α₀ t) (β t), Ω'',
    fun t ht => smoothedPhysicalMap_CX5 H T hT θ f E t (hTs.trans ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _; exact lt_max_of_lt_left (hpos₀ t)
  · intro s hs t ht hst
    exact max_le_max (hanti₀ (hs0.trans hs) (hs0.trans ht) hst) (hantiβ (hsβ.trans hs) (hsβ.trans ht) hst)
  · intro ε hε
    obtain ⟨T1, h1⟩ := hdec₀ ε hε
    obtain ⟨T2, h2⟩ := hdecβ ε hε
    exact ⟨max T1 T2, fun t ht => max_lt (h1 t ((le_max_left _ _).trans ht))
      (h2 t ((le_max_right _ _).trans ht))⟩
  · exact fun t ht => (hmain t ht).1
  · exact fun t ht => (hmain t ht).2
  · intro t ht p hp
    obtain ⟨m, hm1, hβm, hP⟩ := hkeyβ t (hsβ.trans ht)
    have hTt : T ≤ t := hTs.trans ht
    have hτt : τ (2 * m) < t :=
      hP.trans_le (dyadicIndex_mem_CX5 hT hTt).1
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hinv : (β t)⁻¹ = (m : ℝ) := by rw [hβm]; simp
    have hle : (max (α₀ t) (β t))⁻¹ ≤ (β t)⁻¹ := inv_anti₀ (hposβ t) (le_max_right _ _)
    refine hτ (2 * m) t hτt ?_
    refine riemannianBallOf_mono _ _ ?_ hp
    push_cast
    linarith
  · intro t ht k hk p hp
    have hTt : T ≤ t := hTs.trans ht
    have hmem := dyadicIndex_mem_CX5 hT hTt
    have hw : t ∈ Icc (dyadicTime_CX5 T (dyadicIndex_CX5 T t))
        (dyadicTime_CX5 T (dyadicIndex_CX5 T t + 1)) := ⟨hmem.1, hmem.2.le⟩
    have hle : (max (α₀ t) (β t))⁻¹ ≤ (α₀ t)⁻¹ := inv_anti₀ (hpos₀ t) (hαle t)
    have hk' : k ≤ max K ⌈(α₀ t)⁻¹⌉₊ := hk.trans (max_le_max le_rfl (Nat.ceil_mono hle))
    have hp' : p ∈ riemannianBallOf H.metric H.basepoint (2 * (α₀ t)⁻¹) :=
      riemannianBallOf_mono _ _ (by linarith) hp
    exact lt_of_lt_of_le
      (hck₀ t (hs0.trans ht) _ (hθrange _) hw k hk' p hp') (hαle t)
  · intro Ω' hle t ht x hx
    obtain ⟨Pt⟩ := hpatch₀ Ω' (hle.trans hΩ''le) t (hs0.trans ht) x hx
    exact patch_mono_S72 hs0 (fun t ht => (hpos₀ t).le) (fun t _ => hαle t) Pt
  · intro t ht y hy
    have hTt : T ≤ t := hTs.trans ht
    have hmem := dyadicIndex_mem_CX5 hT hTt
    exact hthick (dyadicIndex_CX5 T t) t ⟨hmem.1, hmem.2.le⟩
      (θ (t / dyadicTime_CX5 T (dyadicIndex_CX5 T t))) y hy
end GC.LongTime.Ch12
