import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HDrift_S90
import DifferentialGeometry.Geometry.Metric.Comparison.Inverse

set_option autoImplicit false

/-! # CH12-S128 G1a: `nearIso_S128` — both-way h-distance comparison for the old chart `mold s` at ONE time

For the `hold` block (`K α Ω`, `mold` smooth embedding on `sourceSlice Ω s`, `B(2/α s)` inside, `ckErr < α s` there):
there is `T1` such that for every `s ≥ T1`
* (low) `y` `A`-close (`A < L √(1-α_s)`) to `mold s q`, `q ∈ B(R-L)` ⇒ `y = mold s q'` with `q' ∈ B(R)` and
  `d_h(q,q') ≤ (1-α_s)^{-1/2} d_s(mold s q, y)`   (cover `member_of_drift_S90` + `edistOf_symm_le_…`);
* (up) `q ∈ B(R-L)`, `d_h(q,q') < L` ⇒ `d_s(mold s q, mold s q') ≤ √(1+α_s) d_h(q,q')`   (`edistOf_map_le_…`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem nearIso_S128 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Hold : FiniteVolumeHyperbolicModel.{u}) (K : ℕ) (start : ℝ) (hstart : 0 < start)
    (mold : (t : ℝ) → start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier)
    (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier))
    (hαpos : ∀ t, start ≤ t → 0 < α t)
    (hαlim : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)
    (hsm : ∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold t ht) (sourceSlice_CX5 Ω t))
    (hemb : ∀ t (ht : start ≤ t),
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold t ht x))
    (hball : ∀ t, start ≤ t →
      riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hck : ∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹),
        ckErr_S45 Hold (postMetric F.observation t) t⁻¹ (mold t ht) k p < α t)
    (R L : ℝ) (hL : 0 < L) :
    ∃ T1 : ℝ, ∀ s (hs : start ≤ s), T1 ≤ s →
      α s < 1 / 2 ∧
      (∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (R - L), ∀ {A : ℝ}, A < L / 2 →
        ∀ y : (postStage F.observation s).Carrier,
        riemannianEDistOf (scaleMetric s⁻¹ (inv_pos.mpr (hstart.trans_le hs)) (postMetric F.observation s))
          (mold s hs q) y < ENNReal.ofReal A →
        ∃ q' ∈ riemannianBallOf Hold.metric Hold.basepoint R, mold s hs q' = y ∧
          riemannianEDistOf Hold.metric q q' ≤ ENNReal.ofReal (1 / Real.sqrt (1 - α s)) *
            riemannianEDistOf (scaleMetric s⁻¹ (inv_pos.mpr (hstart.trans_le hs)) (postMetric F.observation s))
              (mold s hs q) y) ∧
      (∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (R - L), ∀ q' : Hold.Carrier,
        riemannianEDistOf Hold.metric q q' < ENNReal.ofReal L →
        riemannianEDistOf (scaleMetric s⁻¹ (inv_pos.mpr (hstart.trans_le hs)) (postMetric F.observation s))
          (mold s hs q) (mold s hs q') ≤
          ENNReal.ofReal (Real.sqrt (1 + α s)) * riemannianEDistOf Hold.metric q q') := by
  obtain ⟨T1, hT1⟩ := hαlim (min (1 / 2) (1 / (|R| + 1))) (lt_min (by norm_num) (by positivity))
  refine ⟨max T1 start, fun s hs hsT => ?_⟩
  have hs1 : T1 ≤ s := (le_max_left _ _).trans hsT
  have hαr := hT1 s hs1
  have hα0 := hαpos s hs
  have hαhalf : α s < 1 / 2 := lt_of_lt_of_le hαr (min_le_left _ _)
  have hαR : α s < 1 / (|R| + 1) := lt_of_lt_of_le hαr (min_le_right _ _)
  have hRlt : R < 2 * (α s)⁻¹ := by
    have h1 : |R| + 1 < (α s)⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hα0]
      simpa [one_div] using hαR
    have := le_abs_self R
    have hpos : 0 < (α s)⁻¹ := inv_pos.mpr hα0
    linarith
  have hspos : 0 < s := hstart.trans_le hs
  refine ⟨hαhalf, ?_⟩
  let U : TopologicalSpace.Opens Hold.Carrier :=
    ⟨riemannianBallOf Hold.metric Hold.basepoint (2 * (α s)⁻¹), isOpen_riemannianBallOf_S61 Hold _⟩
  have hUs : (U : Set Hold.Carrier) ⊆ sourceSlice_CX5 Ω s := hball s hs
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold s hs) (U : Set Hold.Carrier) := (hsm s hs).mono hUs
  have hinj : Set.InjOn (mold s hs) (U : Set Hold.Carrier) := by
    intro a ha b hb hab
    have := (hemb s hs).isEmbedding.injective (a₁ := ⟨a, hUs ha⟩) (a₂ := ⟨b, hUs hb⟩) hab
    exact congrArg Subtype.val this
  have hlow : ∀ p ∈ (U : Set Hold.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 - α s) * Hold.metric.inner p w w ≤
        (scaleMetric s⁻¹ (inv_pos.mpr hspos) (postMetric F.observation s)).inner (mold s hs p)
          (mfderiv (𝓡 3) (𝓡 3) (mold s hs) p w) (mfderiv (𝓡 3) (𝓡 3) (mold s hs) p w) := by
    intro p hp w
    have h0 := hck s hs 0 (Nat.zero_le _) p hp
    have := pullback_inner_ge_of_ckErr_S90 Hold (postMetric F.observation s) s⁻¹ (mold s hs) p h0 w
    simpa using this
  have hup : ∀ p ∈ (U : Set Hold.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (scaleMetric s⁻¹ (inv_pos.mpr hspos) (postMetric F.observation s)).inner (mold s hs p)
          (mfderiv (𝓡 3) (𝓡 3) (mold s hs) p w) (mfderiv (𝓡 3) (𝓡 3) (mold s hs) p w) ≤
        (1 + α s) * Hold.metric.inner p w w := by
    intro p hp w
    have h0 := hck s hs 0 (Nat.zero_le _) p hp
    have := pullback_inner_le_of_ckErr_S49 Hold (postMetric F.observation s) s⁻¹ (mold s hs) p h0 w
    simpa using this
  have hpos1 : 0 < 1 - α s := by linarith
  have hsq : 1 / 2 < Real.sqrt (1 - α s) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hsqpos : 0 < Real.sqrt (1 - α s) := by linarith
  obtain ⟨Φ, hΦs, hΦ⟩ := exists_partialDiffeomorph_of_lower_S90 Hold _ (mold s hs) U hf hinj
    (δ := α s) (by linarith) hlow
  have hcpt : ∀ (x : Hold.Carrier) (ρ : ℝ), IsCompact (riemannianClosedBallOf Hold.metric x ρ) :=
    fun x ρ => isCompact_riemannianClosedBallOf Hold.complete x ρ
  have hRU : riemannianClosedBallOf Hold.metric Hold.basepoint R ⊆ (U : Set Hold.Carrier) := by
    intro x hx
    exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by
      have : 0 < (α s)⁻¹ := inv_pos.mpr hα0
      linarith)).mpr hRlt)
  have hmemC : ∀ (x : Hold.Carrier) (ρ : ℝ), x ∈ riemannianBallOf Hold.metric Hold.basepoint ρ →
      x ∈ riemannianClosedBallOf Hold.metric Hold.basepoint ρ := by
    intro x ρ hx
    simp only [riemannianClosedBallOf, riemannianBallOf, Set.mem_ofPred_eq] at hx ⊢
    exact hx.le
  have hRLof : ∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (R - L), 0 < R - L := fun q hq =>
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt (by simp) hq)
  have hsub : ∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (R - L),
      riemannianClosedBallOf Hold.metric q L ⊆ (U : Set Hold.Carrier) := fun q hq =>
    (riemannianClosedBallOf_subset_of_add_radius_le Hold.metric (r := R - L) (ρ := L)
      (hRLof q hq).le hL.le (by linarith) (hmemC q (R - L) hq)).trans hRU
  refine ⟨?_, ?_⟩
  · intro q hq A hA y hy
    have hAL : A < L * Real.sqrt (1 - α s) := by nlinarith
    obtain ⟨q', hq', hq'y⟩ := member_of_drift_S90 Hold _ (mold s hs) U hf hinj (δ := α s)
      (by linarith) hlow hL hRU hAL ⟨q, hq, hy⟩
    refine ⟨q', hq', hq'y, ?_⟩
    have hA0 : 0 < A := by
      by_contra hA0
      rw [ENNReal.ofReal_of_nonpos (not_lt.mp hA0)] at hy
      exact absurd hy (by simp)
    have hLpos : 0 < 1 / Real.sqrt (1 - α s) := by positivity
    have hsq2 : (1 / Real.sqrt (1 - α s)) ^ 2 = 1 / (1 - α s) := by
      rw [div_pow, one_pow, Real.sq_sqrt hpos1.le]
    have hdiv : L / (1 / Real.sqrt (1 - α s)) = L * Real.sqrt (1 - α s) := by
      field_simp
    have key := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_symm_le_of_metric_lower_on_compact_ball
      Hold.metric _ Φ q (R := L) (L := 1 / Real.sqrt (1 - α s)) (r := A) hL hLpos hA0
      (by rw [hdiv]; nlinarith) (hcpt q L)
      (fun x hx => by rw [hΦs]; exact hsub q hq hx)
      (fun x hx v => by
        have h1 := hlow x (hsub q hq hx) v
        rw [hΦ, hsq2, div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos1]
        linarith)
      y (by rw [hΦ]; exact hy)
    have hsymm : Φ.symm y = q' := by
      rw [← hq'y, ← hΦ]
      exact Φ.left_inv' (hΦs ▸ hRU (hmemC q' R hq'))
    rw [hsymm, hΦ] at key
    exact key
  · intro q hq q' hd
    have hLpos : 0 < Real.sqrt (1 + α s) := Real.sqrt_pos.mpr (by linarith)
    have hsq2 : Real.sqrt (1 + α s) ^ 2 = 1 + α s := Real.sq_sqrt (by linarith)
    have key := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      Hold.metric _ Φ q q' hL hLpos (fun x hx => by rw [hΦs]; exact hsub q hq hx)
      (fun x hx v => by
        have h1 := hup x (hsub q hq hx) v
        rw [hΦ, hsq2]
        exact h1) hd
    rw [hΦ] at key
    exact key

end GC.LongTime.Ch12
