import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45

set_option autoImplicit false

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

/-! CH12-O24 G1b: S8 v5 (`[FROZEN v5] CH12-O24`).  `hpi03_discrete_from_v5_O24` is the
"from a given start" form needed by the escape start of `hone` (O21 NEWESC): it exposes the
precision function `β` and a threshold `Tth`, and for every `T ≥ Tth` and every `Good` map `g₀` at
time `2 ^ 0 * T` builds the S8 v5 family with `f 0 (2 ^ 0 * T) = g₀` on `B(4ρ_0)`.
`hpi03_discrete_v5_O24` is S8 v5 itself (start at a "frequent" time).  S8 v5 = S8 v4 with
`ckErr_S45` throughout, the isotopy clause `ckErr_S45 H H.metric 1 (E j (μ, ·)) k p ≤ η j`, and
the survivor lifts `hlift0` of S55. -/

theorem hpi03_discrete_from_v5_O24 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (hstep : ∃ β : ℝ → ℝ, (∀ t, 0 < β t) ∧
      (∀ T' : ℝ, ∃ t : ℝ, T' ≤ t ∧ 0 < t ∧
        ∃ g₀ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₀ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₀ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₀ k p < β t)) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ Tth : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Tth ≤ t → t₂ = 2 * t →
        ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < β t) →
        ∃ (f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier)
          (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(β t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < β t₂) ∧
          (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R), f t h0 p = g₁ p) ∧
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
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            (∀ k' : ℕ, k' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k' p < ε) ∧
          ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
            (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : a ≤ s) (_ : s < b)
            (_ : b ≤ (F.tower.history n).horizon)
            (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
              first ≤ (F.tower.history n).toHistory.activeStage r ∧
                (F.tower.history n).toHistory.activeStage r ≤ last)
            (φ : H.Carrier →
              (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
              (hrs : (r : ℝ) ∈ Icc t t₂),
              ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
                HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                  ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                  (φ p)) (f r hrs p)) ∧
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r)) :
    ∃ (β : ℝ → ℝ) (Tth : ℝ), (∀ t, 0 < β t) ∧
      (∀ T' : ℝ, ∃ t : ℝ, T' ≤ t ∧ 0 < t ∧
        ∃ g₀ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₀ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₀ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₀ k p < β t)) ∧
      ∀ (T : ℝ) (_ : 0 < T), Tth ≤ T →
      ∀ g₀ : H.Carrier → (postStage F.observation (2 ^ 0 * T)).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β (2 ^ 0 * T))⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₀ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₀ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β (2 ^ 0 * T))⁻¹⌉₊ →
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β (2 ^ 0 * T))⁻¹),
            ckErr_S45 H (postMetric F.observation (2 ^ 0 * T)) (2 ^ 0 * T)⁻¹ g₀ k p < β (2 ^ 0 * T)) →
      ∃ (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
          H.Carrier → (postStage F.observation t).Carrier)
        (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ),
        ((∀ j, 0 ≤ η j) ∧ Filter.Tendsto η Filter.atTop (nhds 0) ∧ Monotone ρ ∧
        Filter.Tendsto ρ Filter.atTop Filter.atTop ∧ (∀ j, 0 < ρ j) ∧
        Monotone ν ∧ Filter.Tendsto ν Filter.atTop Filter.atTop ∧
        (∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j)) ∧
        (∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
          Function.Bijective (fun p => E j (μ, p))) ∧
        (∀ j p, E j (0, p) = p) ∧
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
          let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
          H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j) ∧
        (∀ j (h1 : 2 ^ (j + 1) * T ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
            (h2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j),
            f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j) ∧
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ 2 ^ j * T) (_ : a ≤ s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (φ : H.Carrier →
            (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
            (hrs : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
              HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                (φ p)) (f j r hrs p)) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (μ : ℝ),
          ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) ∧
        ∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), f 0 _ h0 p = g₀ p := by
  classical
  obtain ⟨β, hβpos, hinit, hreq⟩ := hstep
  let Good : (t : ℝ) → (H.Carrier → (postStage F.observation t).Carrier) → ℝ → Prop :=
    fun t g₁ b => ∃ U : TopologicalSpace.Opens H.Carrier,
      riemannianBallOf H.metric H.basepoint (2 * b⁻¹) ⊆ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
      ∀ k : ℕ, k ≤ ⌈b⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * b⁻¹),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < b
  choose Th hTh using fun n : ℕ =>
    hreq (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) n (by positivity) (by positivity)
  choose fS ES gS hS using hTh
  refine ⟨β, Th 0, hβpos, hinit, fun T hTpos hThT g₀ hg₀ => ?_⟩
  have htj : ∀ j : ℕ, 0 < 2 ^ j * T := fun j => by positivity
  have hTle : ∀ j : ℕ, T ≤ 2 ^ j * T := fun j =>
    le_mul_of_one_le_left hTpos.le (one_le_pow₀ one_le_two)
  have hpow : ∀ i j : ℕ, i ≤ j → 2 ^ i * T ≤ 2 ^ j * T := fun i j hij =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hij) hTpos.le
  have hdouble : ∀ j : ℕ, 2 ^ (j + 1) * T = 2 * (2 ^ j * T) := fun j => by ring
  let ν : ℕ → ℕ := fun j => Nat.findGreatest (fun n => Th n ≤ 2 ^ j * T) j
  have h0 : ∀ j : ℕ, Th 0 ≤ 2 ^ j * T := fun j => hThT.trans (hTle j)
  have hthr : ∀ j : ℕ, Th (ν j) ≤ 2 ^ j * T := fun j =>
    Nat.findGreatest_spec (P := fun n => Th n ≤ 2 ^ j * T) (Nat.zero_le j) (h0 j)
  have hνmono : Monotone ν := by
    intro i j hij
    exact Nat.le_findGreatest ((Nat.findGreatest_le i).trans hij) ((hthr i).trans (hpow i j hij))
  have htend : Filter.Tendsto (fun j : ℕ => 2 ^ j * T) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const hTpos
  have hν : Filter.Tendsto ν Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop_of_monotone hνmono fun N => ?_
    obtain ⟨j, hj1, hj2⟩ :=
      ((htend.eventually (Filter.eventually_ge_atTop (Th N))).and
        (Filter.eventually_ge_atTop N)).exists
    exact ⟨j, Nat.le_findGreatest hj2 hj1⟩
  obtain ⟨st, hst0, hst⟩ : ∃ st : (j : ℕ) →
      {g₁ : H.Carrier → (postStage F.observation (2 ^ j * T)).Carrier //
        Good (2 ^ j * T) g₁ (β (2 ^ j * T))},
      (st 0).1 = g₀ ∧ ∀ j, (st (j + 1)).1 =
        gS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2 :=
    ⟨fun j => Nat.rec (motive := fun j =>
        {g₁ : H.Carrier → (postStage F.observation (2 ^ j * T)).Carrier //
          Good (2 ^ j * T) g₁ (β (2 ^ j * T))})
      ⟨g₀, hg₀⟩
      (fun j s => ⟨gS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) s.1 s.2,
        (hS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) s.1 s.2).1⟩) j,
      rfl, fun _ => rfl⟩
  have hSj := fun j : ℕ =>
    hS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2
  have hρmono : Monotone (fun j => (ν j : ℝ) + 1) := fun i j hij => by
    dsimp only
    linarith [(Nat.cast_le (α := ℝ)).2 (hνmono hij)]
  refine ⟨fun j => fS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2,
    fun j => ES (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2,
    fun j => 1 / ((ν j : ℝ) + 1), fun j => (ν j : ℝ) + 1, ν,
    ⟨fun j => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat.comp hν, hρmono,
    Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hν),
    fun j => by positivity, hνmono, hν, fun j => (hSj j).2.2.1, fun j => (hSj j).2.2.2.1,
    fun j => (hSj j).2.2.2.2.1, fun j => (hSj j).2.2.2.2.2.1, fun j => (hSj j).2.2.2.2.2.2.1,
    fun j => (hSj j).2.2.2.2.2.2.2.1, ?_,
    fun j t ht => ⟨((hSj j).2.2.2.2.2.2.2.2.2.1 t ht).1, ((hSj j).2.2.2.2.2.2.2.2.2.1 t ht).2.1, ((hSj j).2.2.2.2.2.2.2.2.2.1 t ht).2.2.1⟩,
    fun j s hs => ((hSj j).2.2.2.2.2.2.2.2.2.1 s hs).2.2.2,
    fun j t ht μ y hy => (hSj j).2.2.2.2.2.2.2.2.2.2 t ht μ y hy⟩, ?_⟩
  · intro j h1 h2 p hp
    have hle : (ν j : ℝ) ≤ ν (j + 1) := Nat.cast_le.2 (hνmono (Nat.le_succ j))
    have hnn : (0 : ℝ) ≤ ν j := Nat.cast_nonneg _
    have hsub : riemannianBallOf H.metric H.basepoint (2 * ((ν j : ℝ) + 1)) ⊆
        riemannianBallOf H.metric H.basepoint (4 * ((ν (j + 1) : ℝ) + 1)) :=
      riemannianBallOf_mono _ _ (by linarith)
    have e1 := (hSj j).2.2.2.2.2.2.2.2.1 h1 p hp
    have e2 := (hSj (j + 1)).2.1 h2 p (hsub hp)
    refine e1.trans ?_
    rw [← hst j]
    exact e2.symm
  · intro h0 p hp
    exact ((hSj 0).2.1 h0 p hp).trans (congrFun hst0 p)

theorem hpi03_discrete_v5_O24 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (hstep : ∃ β : ℝ → ℝ, (∀ t, 0 < β t) ∧
      (∀ T' : ℝ, ∃ t : ℝ, T' ≤ t ∧ 0 < t ∧
        ∃ g₀ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₀ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₀ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₀ k p < β t)) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ Tth : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Tth ≤ t → t₂ = 2 * t →
        ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < β t) →
        ∃ (f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier)
          (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(β t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < β t₂) ∧
          (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R), f t h0 p = g₁ p) ∧
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
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            (∀ k' : ℕ, k' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k' p < ε) ∧
          ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
            (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : a ≤ s) (_ : s < b)
            (_ : b ≤ (F.tower.history n).horizon)
            (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
              first ≤ (F.tower.history n).toHistory.activeStage r ∧
                (F.tower.history n).toHistory.activeStage r ≤ last)
            (φ : H.Carrier →
              (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
              (hrs : (r : ℝ) ∈ Icc t t₂),
              ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
                HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                  ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                  (φ p)) (f r hrs p)) ∧
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r)) :
    ∃ (T : ℝ) (_ : 0 < T)
      (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
          H.Carrier → (postStage F.observation t).Carrier)
        (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ),
    (∀ j, 0 ≤ η j) ∧ Filter.Tendsto η Filter.atTop (nhds 0) ∧ Monotone ρ ∧
        Filter.Tendsto ρ Filter.atTop Filter.atTop ∧ (∀ j, 0 < ρ j) ∧
        Monotone ν ∧ Filter.Tendsto ν Filter.atTop Filter.atTop ∧
        (∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j)) ∧
        (∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
          Function.Bijective (fun p => E j (μ, p))) ∧
        (∀ j p, E j (0, p) = p) ∧
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
          let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
          H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j) ∧
        (∀ j (h1 : 2 ^ (j + 1) * T ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
            (h2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j),
            f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j) ∧
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ 2 ^ j * T) (_ : a ≤ s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (φ : H.Carrier →
            (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
            (hrs : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
              HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                (φ p)) (f j r hrs p)) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (μ : ℝ),
          ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r) := by
  obtain ⟨β, Tth, -, hinit, hfrom⟩ := hpi03_discrete_from_v5_O24 F H wstar a hstep
  obtain ⟨T, hT, hTpos, g₀, hg₀⟩ := hinit Tth
  have hbase : ∃ g₁ : H.Carrier → (postStage F.observation (2 ^ 0 * T)).Carrier,
      (∃ U : TopologicalSpace.Opens H.Carrier,
        riemannianBallOf H.metric H.basepoint (2 * (β (2 ^ 0 * T))⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
        ∀ k : ℕ, k ≤ ⌈(β (2 ^ 0 * T))⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β (2 ^ 0 * T))⁻¹),
          ckErr_S45 H (postMetric F.observation (2 ^ 0 * T)) (2 ^ 0 * T)⁻¹ g₁ k p < β (2 ^ 0 * T)) := by
    rw [pow_zero, one_mul]
    exact ⟨g₀, hg₀⟩
  obtain ⟨g₁, hg₁⟩ := hbase
  obtain ⟨f, E, η, ρ, ν, h, -⟩ := hfrom T hTpos hT g₁ hg₁
  exact ⟨T, hTpos, f, E, η, ρ, ν, h⟩

end GC.LongTime.Ch12
