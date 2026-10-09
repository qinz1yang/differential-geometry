import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores

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

/-! CH12-O20 G1: the dyadic assembly of HPI03 (blueprint HPI03, sheet-H3H5 S8 v2).

From a one-step contract `hstep` (frozen in `[FROZEN v2] CH12-O20`; it packages
hLTF04 + β_w + S7 + S1 + CX3 for one dyadic window, see the HANDOVER) we build the
discrete H3 data `f_j, E_j, η_j, ρ_j, ν_j` consumed by CX5.  The request list
`n ↦ (ε, R, k) = (1/(n+1), n+1, n)` is fixed before the base time `T`; at window `j`
we use the strongest request `ν j = Nat.findGreatest (Th · ≤ 2^j T) j` whose
threshold has been passed.  The maps are produced by recursion along the dyadic
times, the state being a map at time `2^j T` satisfying the inline `Good` invariant. -/

theorem hpi03_discrete_of_step_O20 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (hstep : ∃ β : ℝ → ℝ, (∀ t, 0 < β t) ∧
      (∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
        ∃ g₀ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₀ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₀ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            tensor0SFiberNorm H.metric p (2 + k)
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (t⁻¹ • localPullInner (postMetric F.observation t) g₀ q - H.metric.inner q)).uncurryLeft) k p) < β t)) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ Tth : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Tth ≤ t → t₂ = 2 * t →
        ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            tensor0SFiberNorm H.metric p (2 + k)
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (t⁻¹ • localPullInner (postMetric F.observation t) g₁ q - H.metric.inner q)).uncurryLeft) k p) < β t) →
        ∃ (f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier)
          (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(β t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹),
              tensor0SFiberNorm H.metric p (2 + k)
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (t₂⁻¹ • localPullInner (postMetric F.observation t₂) g₂ q - H.metric.inner q)).uncurryLeft) k p) < β t₂) ∧
          (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R), f t h0 p = g₁ p) ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E ∧
          (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E (μ, p)) ∧
            Function.Bijective (fun p => E (μ, p))) ∧
          (∀ p, E (0, p) = p) ∧
          (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (R) → E (μ, p) = p) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
            let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
            H.metric.inner (E (μ, p)) v v ≤ ε ^ 2) ∧
          (∀ (h1 : t₂ ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), f t₂ h1 (E (1, p)) = g₂ p) ∧
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
            ∀ k' : ℕ, k' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
              tensor0SFiberNorm H.metric p (2 + k')
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (s⁻¹ • localPullInner (postMetric F.observation s) (f s hs) q - H.metric.inner q)).uncurryLeft) k' p) < ε) ∧
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
      (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (ρ j) → E j (μ, p) = p) ∧
      (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
        let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
        H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2) ∧
      (∀ j (h1 : 2 ^ (j + 1) * T ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
          (h2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T)),
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j),
          f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p) ∧
      (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          tensor0SFiberNorm H.metric p (2 + k)
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (t⁻¹ • localPullInner (postMetric F.observation t) (f j t ht) q - H.metric.inner q)).uncurryLeft) k p) < η j) ∧
      (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (μ : ℝ),
        ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
          (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
        ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
          (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
          (f j t ht (E j (μ, y))) r) := by
  classical
  obtain ⟨β, -, ⟨T₀, hT₀, hinit⟩, hreq⟩ := hstep
  let Good : (t : ℝ) → (H.Carrier → (postStage F.observation t).Carrier) → ℝ → Prop :=
    fun t g₁ b => ∃ U : TopologicalSpace.Opens H.Carrier,
      riemannianBallOf H.metric H.basepoint (2 * b⁻¹) ⊆ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
      ∀ k : ℕ, k ≤ ⌈b⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * b⁻¹),
        tensor0SFiberNorm H.metric p (2 + k)
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (t⁻¹ • localPullInner (postMetric F.observation t) g₁ q - H.metric.inner q)).uncurryLeft) k p) < b
  choose g0 hg0 using hinit
  choose Th hTh using fun n : ℕ =>
    hreq (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) n (by positivity) (by positivity)
  choose fS ES gS hS using hTh
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = max T₀ (Th 0) := ⟨_, rfl⟩
  have hTpos : 0 < T := hTdef ▸ lt_of_lt_of_le hT₀ (le_max_left _ _)
  have htj : ∀ j : ℕ, 0 < 2 ^ j * T := fun j => by positivity
  have hTle : ∀ j : ℕ, T ≤ 2 ^ j * T := fun j =>
    le_mul_of_one_le_left hTpos.le (one_le_pow₀ one_le_two)
  have hpow : ∀ i j : ℕ, i ≤ j → 2 ^ i * T ≤ 2 ^ j * T := fun i j hij =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hij) hTpos.le
  have hdouble : ∀ j : ℕ, 2 ^ (j + 1) * T = 2 * (2 ^ j * T) := fun j => by ring
  let ν : ℕ → ℕ := fun j => Nat.findGreatest (fun n => Th n ≤ 2 ^ j * T) j
  have h0 : ∀ j : ℕ, Th 0 ≤ 2 ^ j * T := fun j =>
    (hTdef ▸ le_max_right T₀ (Th 0) : Th 0 ≤ T).trans (hTle j)
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
  have h00 : T₀ ≤ 2 ^ 0 * T := by
    rw [pow_zero, one_mul, hTdef]; exact le_max_left _ _
  obtain ⟨st, hst⟩ : ∃ st : (j : ℕ) →
      {g₁ : H.Carrier → (postStage F.observation (2 ^ j * T)).Carrier //
        Good (2 ^ j * T) g₁ (β (2 ^ j * T))},
      ∀ j, (st (j + 1)).1 =
        gS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2 :=
    ⟨fun j => Nat.rec (motive := fun j =>
        {g₁ : H.Carrier → (postStage F.observation (2 ^ j * T)).Carrier //
          Good (2 ^ j * T) g₁ (β (2 ^ j * T))})
      ⟨g0 (2 ^ 0 * T) h00, hg0 (2 ^ 0 * T) h00⟩
      (fun j s => ⟨gS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) s.1 s.2,
        (hS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) s.1 s.2).1⟩) j,
      fun _ => rfl⟩
  have hSj := fun j : ℕ =>
    hS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2
  have hρmono : Monotone (fun j => (ν j : ℝ) + 1) := fun i j hij => by
    dsimp only
    linarith [(Nat.cast_le (α := ℝ)).2 (hνmono hij)]
  refine ⟨T, hTpos,
    fun j => fS (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2,
    fun j => ES (ν j) (2 ^ j * T) (2 ^ (j + 1) * T) (htj j) (hthr j) (hdouble j) (st j).1 (st j).2,
    fun j => 1 / ((ν j : ℝ) + 1), fun j => (ν j : ℝ) + 1, ν,
    fun j => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat.comp hν, hρmono,
    Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hν),
    fun j => by positivity, hνmono, hν, fun j => (hSj j).2.2.1, fun j => (hSj j).2.2.2.1,
    fun j => (hSj j).2.2.2.2.1, fun j => (hSj j).2.2.2.2.2.1, fun j => (hSj j).2.2.2.2.2.2.1,
    ?_, fun j => (hSj j).2.2.2.2.2.2.2.2.1, fun j t ht μ y hy => (hSj j).2.2.2.2.2.2.2.2.2 t ht μ y hy⟩
  intro j h1 h2 p hp
  have hle : (ν j : ℝ) ≤ ν (j + 1) := Nat.cast_le.2 (hνmono (Nat.le_succ j))
  have hnn : (0 : ℝ) ≤ ν j := Nat.cast_nonneg _
  have hsub : riemannianBallOf H.metric H.basepoint (2 * ((ν j : ℝ) + 1)) ⊆
      riemannianBallOf H.metric H.basepoint (4 * ((ν (j + 1) : ℝ) + 1)) :=
    riemannianBallOf_mono _ _ (by linarith)
  have e1 := (hSj j).2.2.2.2.2.2.2.1 h1 p hp
  have e2 := (hSj (j + 1)).2.1 h2 p (hsub hp)
  refine e1.trans ?_
  rw [← hst j]
  exact e2.symm

end GC.LongTime.Ch12
