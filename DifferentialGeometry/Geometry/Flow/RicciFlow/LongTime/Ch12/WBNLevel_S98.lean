import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WBNLevelAux_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RefJetsU_S81
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HCollar_S92

set_option autoImplicit false

/-!
# CH12-S98 / G2c: `wbN_S98` — the N-level W-B assembly (R3 + S81 hRef + S82 core + S92 collar)
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology ENNReal
universe u
namespace GC.LongTime.Ch12

theorem wbN_S98 (H : FiniteVolumeHyperbolicModel.{u}) {R ε : ℝ} (k : ℕ) (hR : 0 < R) (hε : 0 < ε)
    {KShi : ℝ} (hKShi : 0 ≤ KShi) :
    ∃ δ' η₀ : ℝ, 0 < δ' ∧ 0 < η₀ ∧
      ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N]
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (t : ℝ), 0 < t →
        ∀ (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (ballU_S98 H R))
          (hinj : ∀ y ∈ ballU_S98 H R, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)),
        (∃ (D : RealTimeInterval) (S' : SolutionOn (I := 𝓡 3) (M := ballU_S98 H R) D),
          IsSolutionOn S' ∧ Icc t (2 * t) ⊆ D.regular ∧
          (∀ (x₀ : ballU_S98 H R) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × ballU_S98 H R => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S'.base.metric p.1) x₀ p.2 i j)
              (Icc t (2 * t) ×ˢ
                (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          (∀ r ∈ Icc t (2 * t),
            S'.base.metric r = pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)) →
        (∀ s ≤ k + 1, ∀ r ∈ Icc t (2 * t), ∀ x : ballU_S98 H R,
          normSq0S (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) x (2 + s)
            (ricCovTower (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)
              (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) s x) * r ^ (2 + s) ≤
            KShi ^ 2) →
        (∀ j ≤ k + 2, ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g t) t⁻¹ f j p < δ') →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g r) r⁻¹ f 0 p < η₀) →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ∀ V : TangentSpace (𝓡 3) (f p),
            |2 * r * ricciTensor (g r) (f p) V V + (g r).inner (f p) V V| ≤
              η₀ * (g r).inner (f p) V V) →
        ∀ j ≤ k, ∀ s ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H (g s) s⁻¹ f j p < ε := by
  classical
  let U : Opens H.Carrier := ballU_S98 H R
  have hU : ∀ y : H.Carrier, y ∈ riemannianBallOf H.metric H.basepoint (2 * R) → y ∈ U := fun y hy => hy
  let ℓ : ℝ := R / (((k + 1 : ℕ) : ℝ) + 1)
  have hℓ : 0 < ℓ := by positivity
  let Kc : Set U := {x | riemannianEDistOf H.metric H.basepoint (x : H.Carrier) ≤
    ENNReal.ofReal (2 * R - ℓ)}
  have hℓR : ℓ ≤ R := by
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (k + 1); linarith
    exact div_le_self hR.le this
  have hKc : IsCompact Kc := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert isCompact_closedBall_S98 H (2 * R - ℓ) using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      refine ⟨⟨y, ?_⟩, hy, rfl⟩
      exact lt_of_le_of_lt hy (ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.2 (by linarith))
  obtain ⟨B0, hB00, hB⟩ := hReferenceJets_S81 H U k (fun _ => Kc) hKc Set.univ isOpen_univ
    (Set.subset_univ _) (Λ := 2) (KShi := KShi) (by norm_num) hKShi (fun _ => 1)
    (fun _ => zero_le_one)
  let B : ℝ := max B0 1
  have hB1 : 1 ≤ B := le_max_right _ _
  let ε' : ℝ := wbEta_S82 k ℓ B ε
  have hε' : 0 < ε' := wbEta_pos_S82 k hℓ hε
  refine ⟨min 1 (ε / 2), min (1 / 2) (ε' / 6), lt_min one_pos (half_pos hε),
    lt_min (by norm_num) (by positivity), ?_⟩
  intro N _ _ _ _ _ g f t ht hF hinj hLF hShi h0 hC0 hdef
  obtain ⟨D, S', hS, hreg, hgram, hmet⟩ := hLF
  have hη1 : min (1 / 2 : ℝ) (ε' / 6) ≤ 1 / 2 := min_le_left _ _
  have hη2 : min (1 / 2 : ℝ) (ε' / 6) ≤ ε' / 6 := min_le_right _ _
  have hη0 : 0 < min (1 / 2 : ℝ) (ε' / 6) := lt_min (by norm_num) (by positivity)
  set η₀ := min (1 / 2 : ℝ) (ε' / 6) with hη₀
  -- two-sided metric bound on `↥U`
  have hbd : ∀ r ∈ Icc t (2 * t), ∀ x : U, ∀ v : TangentSpace (𝓡 3) x,
      (1 / 2) * (r * H.metric.inner x v v) ≤ (pullbackRestrict_S57 H (g r) f U hF hinj).inner x v v ∧
      (pullbackRestrict_S57 H (g r) f U hF hinj).inner x v v ≤
        (1 + η₀) * (r * H.metric.inner x v v) := by
    intro r hr x v
    have hr0 : 0 < r := ht.trans_le hr.1
    have h1 := abs_pullback_sub_le_S98 H (g r) r⁻¹ f x (hC0 r hr x x.2) v
    rw [(ricci_pullbackRestrict_S98 H (g r) f U hF hinj x v).2]
    have hv0 : 0 ≤ H.metric.inner x v v := metric_inner_self_nonneg _ _ _
    obtain ⟨hlo, hhi⟩ := abs_le.1 h1
    set P := (g r).inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v)
    have e : P = r * (r⁻¹ * P) := by field_simp
    constructor
    · rw [e]
      have : (1 / 2) * H.metric.inner x v v ≤ r⁻¹ * P := by nlinarith [mul_nonneg hv0 (sub_nonneg.2 hη1)]
      nlinarith [mul_le_mul_of_nonneg_left this hr0.le]
    · rw [e]
      have : r⁻¹ * P ≤ (1 + η₀) * H.metric.inner x v v := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hr0.le]
  have hmet' : ∀ r ∈ Icc t (2 * t), S'.base.metric r = pullbackRestrict_S57 H (g r) f U hF hinj := hmet
  have hr0' : ∀ r ∈ Icc t (2 * t), 0 < r := fun r hr => ht.trans_le hr.1
  have hequiv : ∀ r ∈ Icc t (2 * t), ∀ x ∈ (Set.univ : Set U), ∀ v : TangentSpace (𝓡 3) x,
      (2 : ℝ)⁻¹ * (r * (H.metric.restrictOpen U).inner x v v) ≤
          (pullbackRestrict_S57 H (g r) f U hF hinj).inner x v v ∧
        (pullbackRestrict_S57 H (g r) f U hF hinj).inner x v v ≤
          2 * (r * (H.metric.restrictOpen U).inner x v v) := by
    intro r hr x _ v
    obtain ⟨a, b⟩ := hbd r hr x v
    have hv0 : 0 ≤ H.metric.inner x v v := metric_inner_self_nonneg _ _ _
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    have hrv : 0 ≤ r * H.metric.inner x v v := mul_nonneg (hr0' r hr).le hv0
    constructor <;> nlinarith
  have hinit : ∀ q, 1 ≤ q → q ≤ k + 1 → ∀ x ∈ (Set.univ : Set U),
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (q + 2)
        (metricCovDeriv (pullbackRestrict_S57 H (g t) f U hF hinj) (H.metric.restrictOpen U) q x)) ≤
        (fun _ => (1 : ℝ)) q * t := by
    intro q hq1 hqk x _
    have hlt : ckErr_S45 H (g t) t⁻¹ f q x < 1 :=
      lt_of_lt_of_le (h0 q (by omega) x x.2) (min_le_left _ _)
    rw [ckErr_S45_eq_metricDerivNorm_S57 H (g t) t⁻¹ (inv_pos.2 ht) f U hF hinj q x,
      pullbackRestrict_scale_S57 H (g t) t⁻¹ (inv_pos.2 ht) f U hF hinj] at hlt
    obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
    have e : metricDerivNorm (a + 1)
        (scaleMetric t⁻¹ (inv_pos.2 ht) (pullbackRestrict_S57 H (g t) f U hF hinj))
        (H.metric.restrictOpen U) (H.metric.restrictOpen U) x =
        metricCovDerivNorm (a + 1)
          (scaleMetric t⁻¹ (inv_pos.2 ht) (pullbackRestrict_S57 H (g t) f U hF hinj))
          (H.metric.restrictOpen U) x := by
      simp [metricDerivNorm, metricDiffCovDerivAt, metricCovDerivNorm, covDeriv_self_succ]
    rw [e, metricCovDerivNorm_scaleMetric_left] at hlt
    have h2 : Real.sqrt (normSq0S (H.metric.restrictOpen U) x (a + 1 + 2)
        (metricCovDeriv (pullbackRestrict_S57 H (g t) f U hF hinj) (H.metric.restrictOpen U)
          (a + 1) x)) < t := by
      set s0 := Real.sqrt (normSq0S (H.metric.restrictOpen U) x (a + 1 + 2)
        (metricCovDeriv (pullbackRestrict_S57 H (g t) f U hF hinj) (H.metric.restrictOpen U)
          (a + 1) x)) with hs0
      calc s0 = t * (t⁻¹ * s0) := by field_simp
        _ < t * 1 := mul_lt_mul_of_pos_left hlt ht
        _ = t := mul_one t
    simpa using h2.le
  have hdef0 : ∀ r ∈ Ioo t (2 * t), ∀ x ∈ ballLevel_S82 H U R (k + 1) (0 + 1),
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (0 + 2)
        (defectJet_S57 S' (H.metric.restrictOpen U) 0 r x)) ≤ wbEta_S82 k ℓ B ε * r := by
    intro r hr x _
    have hrI : r ∈ Icc t (2 * t) := Ioo_subset_Icc_self hr
    have hr0 := hr0' r hrI
    have hq : ∀ w : TangentSpace (𝓡 3) x,
        |(S'.base.metric r).inner x w w + 2 * r * ricciTensor (S'.base.metric r) x w w| ≤
          (η₀ * (1 + η₀) * r) * (H.metric.restrictOpen U).inner x w w := by
      intro w
      rw [hmet' r hrI]
      obtain ⟨hR1, hI1⟩ := ricci_pullbackRestrict_S98 H (g r) f U hF hinj x w
      rw [hR1, hI1, add_comm]
      have hd := hdef r hrI x x.2 (mfderiv (𝓡 3) (𝓡 3) f x w)
      have hb := (hbd r hrI x w).2
      rw [hI1] at hb
      rw [SmoothRiemannianMetric.restrictOpen_inner]
      refine hd.trans ?_
      have : η₀ * (g r).inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x w) (mfderiv (𝓡 3) (𝓡 3) f x w) ≤
          η₀ * ((1 + η₀) * (r * H.metric.inner x w w)) := mul_le_mul_of_nonneg_left hb hη0.le
      nlinarith
    have := sqrt_normSq0S_defect0_le_S98 S' (H.metric.restrictOpen U) r x
      (by positivity) hq
    refine this.trans ?_
    nlinarith [mul_pos hη0 hr0]
  have hRef : ∀ j ≤ k + 1, ∀ r ∈ Ioo t (2 * t), ∀ x ∈ ballLevel_S82 H U R (k + 1) (0 + 1),
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (j + 2)
        (defectJet_S57 S' (H.metric.restrictOpen U) j r x)) ≤ B * r := by
    intro j hj r hr x hx
    have hxK : x ∈ (fun _ : ℕ => Kc) 0 := by
      change riemannianEDistOf H.metric H.basepoint (x : H.Carrier) ≤ ENNReal.ofReal (2 * R - ℓ)
      have hx' : riemannianEDistOf H.metric H.basepoint (x : H.Carrier) <
          ENNReal.ofReal (2 * R - ((0 + 1 : ℕ) : ℝ) * (R / (((k + 1 : ℕ) : ℝ) + 1))) := hx
      have e : (2 * R - ((0 + 1 : ℕ) : ℝ) * (R / (((k + 1 : ℕ) : ℝ) + 1))) = 2 * R - ℓ := by
        simp [ℓ]
      rw [e] at hx'
      exact hx'.le
    have := hB g f hF hinj t (2 * t) ht le_rfl hequiv (fun s hs r hr x _ => hShi s hs r hr x) hinit
      D S' hS hreg hmet' j hj r hr x hxK
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (hr0' r (Ioo_subset_Icc_self hr)).le)
  have hgeo := fun (j : ℕ) (hj : j < k) => hgeo_S92 H U hR hU (k + 1) (j + 1) (by omega)
  intro j hj s hs p hp
  have hpU : p ∈ (U : Set H.Carrier) := riemannianBallOf_mono H.metric H.basepoint (by linarith) hp
  exact wbCore_S82 H g f U hF hinj k (fun j => ballLevel_S82 H U R (k + 1) (j + 1))
    (fun j => ballLevel_succ_subset_S82 H U hR (k + 1) (j + 1)) hℓ hB1 hε ht S' hS hreg hgram hmet'
    hRef hgeo hdef0
    (fun i hi y hy => lt_of_lt_of_le (h0 i (by omega) y (ballLevel_zero_subset_S82 H U R (k + 1)
      (ballLevel_succ_subset_S82_trans H U hR (k + 1) hy))) (min_le_right _ _))
    j hj s hs ⟨p, hpU⟩ (ball_subset_ballLevel_S82 H U hR (k + 1) (x := ⟨p, hpU⟩) hp)

end GC.LongTime.Ch12
