import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DiagonalAlpha_S61
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Comp_S71

set_option autoImplicit false

/-! # CH12-S72 G1a': S61's G2b/G2c with `hcomp` substituted by `hcomp_S71` (no inline binder)

`smoothed_ckErr_threshold_S72` / `exists_alpha_ckErr_S72` = `smoothed_ckErr_threshold_S61` /
`exists_alpha_ckErr_S61` (same proofs) with the `hcomp` binder removed: `hcomp_S71 H k hε` is applied
at `f := f j t ht`, `E := E j (μ, ·)`, `R := 2m`; the two extra binders of `hcomp_S71` are fed by
`(hEb j μ).2.injective.injOn` and `(hacc j t ht).1.mono` (image of `B(2m)` stays in `B(4ρ_j)`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem isotopy_image_ball_S72 (H : FiniteVolumeHyperbolicModel.{u}) (E : ℕ → ℝ × H.Carrier → H.Carrier)
    (ρ : ℕ → ℝ) (hEb : ∀ j μ, Function.Bijective (fun p => E j (μ, p)))
    (hsupp : ∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (j : ℕ) (μ : ℝ) {R r : ℝ} (hρr : 4 * ρ j ≤ r) (hRr : R ≤ r) :
    (fun x => E j (μ, x)) '' riemannianBallOf H.metric H.basepoint R ⊆
      riemannianBallOf H.metric H.basepoint r := by
  rintro q ⟨x, hx, rfl⟩
  exact isotopy_mem_ball_S49 H (E j) (fun μ => (hEb j μ).1) (hsupp j) μ hρr
    (riemannianBallOf_mono _ _ hRr hx)

theorem smoothed_ckErr_threshold_S72 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (K : ℕ)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ)
    (hηt : Tendsto η atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop) (hν : Tendsto ν atTop atTop)
    (hEb : ∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
      Function.Bijective (fun p => E j (μ, p)))
    (hsupp : ∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (hEclose : ∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j)
    (hacc : ∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ μ ∈ Icc (0 : ℝ) 1,
      ∀ t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ k : ℕ, k ≤ max K m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * m),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (fun x => f j t ht (E j (μ, x))) k p <
          1 / (m : ℝ) := by
  have hmpos : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hQ : ∀ k : ℕ, ∀ᶠ j in atTop, ∀ μ ∈ Icc (0 : ℝ) 1,
      ∀ t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * m),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (fun x => f j t ht (E j (μ, x))) k p <
          1 / (m : ℝ) := by
    intro k
    obtain ⟨δ, hδ, hδc⟩ := hcomp_S71 H k hmpos
    filter_upwards [hηt.eventually (eventually_le_nhds hδ),
      hν.eventually (eventually_ge_atTop k),
      hρ.eventually (eventually_ge_atTop (2 * (m : ℝ)))] with j hηδ hνj hρj μ hμ t ht p hp
    have hball : ∀ q ∈ riemannianBallOf H.metric H.basepoint (2 * m),
        q ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) := fun q hq =>
      riemannianBallOf_mono _ _ (by linarith) hq
    have hρ0 : (0 : ℝ) ≤ ρ j := by
      have : (0 : ℝ) ≤ 2 * m := by positivity
      linarith
    have himg : ∀ q ∈ (fun x => E j (μ, x)) '' riemannianBallOf H.metric H.basepoint (2 * m),
        q ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) :=
      fun q hq => isotopy_image_ball_S72 H E ρ (fun j μ => (hEb j μ).2) hsupp j μ
        (by linarith) (by linarith) hq
    have hinjE : Set.InjOn (fun x => E j (μ, x)) (riemannianBallOf H.metric H.basepoint (2 * m)) :=
      (hEb j μ).2.1.injOn
    have hfs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht)
        ((fun x => E j (μ, x)) '' riemannianBallOf H.metric H.basepoint (2 * m)) :=
      (hacc j t ht).1.mono himg
    exact hδc (postMetric F.observation t) t⁻¹ (f j t ht) (fun x => E j (μ, x)) (2 * m) (hEb j μ).1
      hinjE hfs
      (fun i hi q hq => (hEclose j μ hμ i (hi.trans hνj) q (hball q hq)).trans hηδ)
      (fun i hi q hq => ((hacc j t ht).2 i (hi.trans hνj) q (himg q hq)).le.trans hηδ) p hp
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    ((Filter.eventually_all_finset (Finset.range (max K m + 1))).2 (fun k _ => hQ k))
  exact ⟨J, fun j hj μ hμ t ht k hk p hp =>
    hJ j hj k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) μ hμ t ht p hp⟩


theorem exists_alpha_ckErr_S72 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T) (K : ℕ) (B : ℝ)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ)
    (hηt : Tendsto η atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop) (hν : Tendsto ν atTop atTop)
    (hEb : ∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
      Function.Bijective (fun p => E j (μ, p)))
    (hsupp : ∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (hEclose : ∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j)
    (hacc : ∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j)
    :
    ∃ (start : ℝ) (α : ℝ → ℝ), T ≤ start ∧ (∀ t, 0 < α t) ∧ AntitoneOn α (Ici start) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T' : ℝ, ∀ t, T' ≤ t → α t < ε) ∧
      (∀ t, start ≤ t → 4 * B * η (dyadicIndex_CX5 T t) < α t) ∧
      ∀ t, start ≤ t → ∀ μ ∈ Icc (0 : ℝ) 1,
        ∀ ht : t ∈ Icc (dyadicTime_CX5 T (dyadicIndex_CX5 T t))
          (dyadicTime_CX5 T (dyadicIndex_CX5 T t + 1)),
        ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹
              (fun x => f (dyadicIndex_CX5 T t) t ht (E (dyadicIndex_CX5 T t) (μ, x))) k p < α t := by
  classical
  have hth := smoothed_ckErr_threshold_S72 F H K f E η ρ ν hηt hρ hν hEb hsupp hEclose hacc
  obtain ⟨start, α, hstart, hpos, hanti, hdec, hkey⟩ := exists_diagonal_alpha_S61 hT
    (fun m j => 1 ≤ m → (4 * B * η j < 1 / (m : ℝ) ∧
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ∀ k : ℕ, k ≤ max K m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * m),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ (fun x => f j t ht (E j (μ, x))) k p <
            1 / (m : ℝ)))
    (fun m => by
      by_cases hm : 1 ≤ m
      · obtain ⟨J, hJ⟩ := hth m hm
        have hmpos : (0 : ℝ) < 1 / (m : ℝ) := by
          have : (0 : ℝ) < m := by exact_mod_cast hm
          positivity
        obtain ⟨J2, hJ2⟩ := eventually_atTop.1
          ((hηt.const_mul (4 * B)).eventually (eventually_lt_nhds (a := (4 * B) * 0) (b := 1 / (m : ℝ))
            (by simpa using hmpos)))
        exact ⟨max J J2, fun j hj _ => ⟨hJ2 j ((le_max_right _ _).trans hj),
          hJ j ((le_max_left _ _).trans hj)⟩⟩
      · exact ⟨0, fun j _ h => absurd h hm⟩)
  refine ⟨start, α, hstart, hpos, hanti, hdec, ?_, ?_⟩
  · intro t ht
    obtain ⟨m, hm, hαm, hP⟩ := hkey t ht
    rw [hαm]; exact (hP hm).1
  · intro t ht μ hμ hw k hk p hp
    obtain ⟨m, hm, hαm, hP⟩ := hkey t ht
    have hinv : (α t)⁻¹ = (m : ℝ) := by rw [hαm]; simp
    have hceil : ⌈(α t)⁻¹⌉₊ = m := by rw [hinv]; exact Nat.ceil_natCast m
    rw [hceil] at hk
    rw [hinv] at hp
    rw [hαm]
    exact (hP hm).2 μ hμ t hw k hk p hp

end GC.LongTime.Ch12
