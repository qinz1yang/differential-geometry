import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepCoreDisp_O74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepReparam_O74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HConvS_O32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SmoothedEmbedding_S72

set_option autoImplicit false

/-! # CH12-O74 G2a: `hstepW_O74 : P2 v4` and `hEnd_O74` with the bounded window binder `hthickW'`

Generated from `StepWrap_O54.lean` by `scratch/o74/gen_wrap.py` (`[FROZEN] CH12-O74`).  Edits:
* binder `hthickW` (`thickW_shape_O40`, `∀ y ∈ B(4R'')`; unsatisfiable for cusped `H`, S143 F1) ↦
  `hthickW'` (`thickWB_shape_O74`: extra premise `InjOn q`, window `∀ y ∈ B(a + 1)`);
* the isotopy of P2 is `E (smoothTransition μ, ·)` with `E` from `step_core_disp_O74` at speed
  `c * min ε 1` (`speed_reparam_O74`); since `smoothTransition μ ∈ [0,1]` and `E` moves points by
  `≤ 1` there, `E' (μ, B(a)) ⊆ B(a + 1)` for every `μ : ℝ`, and `step_thick_O74` gives P2's last
  conjunct.  P2 v4 / hEnd-S conclusions are verbatim. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Bundle
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

section CX3
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- P2 v4 (= P2 v2 text, verbatim) from the anchor, comparison (S1 v3 binders) and the bounded
window binder `hthickW'` (`[FROZEN] CH12-O74`): isotopy `E (smoothTransition μ, ·)` of
`step_core_disp_O74` at speed `c * min ε 1` (`speed_reparam_O74`), thickness `step_thick_O74`. -/
theorem hstepW_O74 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
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
    (hHPS01 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
      (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover →
      ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
      ∃ R θ δ : ℝ, 0 < R ∧ 0 < θ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
        O ⊆ riemannianBallOf H.metric o R ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (e : H.Carrier ≃ H'.Carrier),
          ContMDiff (𝓡 3) (𝓡 3) ∞ e → ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm →
          (∀ p, localPullInner H'.metric e p = H.metric.inner p) →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric o (2 * R) ⊆ U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
            ckErr_O19 H H'.metric 1 f j p < δ) →
          (∀ p ∈ riemannianBallOf H.metric o R,
            riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal θ) →
          (∀ p ∈ O, riemannianEDistOf H.metric p (e.symm (f p)) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (f p)) ∧
          e '' O ⊆ f '' (U : Set H.Carrier) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn f U (e p)) O ∧
          (∀ p ∈ O, riemannianEDistOf H.metric p (Function.invFunOn f U (e p)) <
            ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p)))
    (Tr : HyperbolicTruncation H)
    (hthickW' :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (a + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r)
    (hanchor :
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
        φ y₀ = q H.basepoint) :
  ∃ βw : ℝ → ℝ, (∀ t, 0 < βw t) ∧ Filter.Tendsto βw Filter.atTop (nhds 0) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ (ε' R' : ℝ) (k' : ℕ), 0 < ε' ∧ 0 < R' ∧
        ε' ≤ ε ∧ R ≤ R' ∧ k ≤ k' ∧ ∃ Te : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Te ≤ t → t₂ = 2 * t →
        ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
        ∃ (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (βw t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(βw t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (βw t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < βw t₂) ∧
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
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r) := by
  obtain ⟨βw, hβw, hβw0, ε₁, R₁, k₁, hε₁, hR₁, T₁, hanc⟩ := hanchor
  obtain ⟨εt, Rt, Tt, kt, hεt, hTt, hthick⟩ := step_thick_O74 F H wstar a hthickW'
  obtain ⟨c, hc0, hc1, hrep⟩ := speed_reparam_O74 H
  refine ⟨βw, hβw, hβw0, fun ε R k hε hR => ?_⟩
  obtain ⟨R₂, δ, ρ, m, hR₂, hδ, hρ, hcore⟩ :=
    step_core_disp_O74 hHG06 hHPS01 H Tr (ε := c * min ε 1) (mul_pos hc0 (lt_min hε one_pos)) hR k
  have hL : 0 < max (max (m : ℝ) (2 * R₂ + 2)) ρ + 1 := by positivity
  have hc : 0 < min δ (1 / (max (max (m : ℝ) (2 * R₂ + 2)) ρ + 1)) := lt_min hδ (by positivity)
  obtain ⟨Tβ, hTβ⟩ := Filter.eventually_atTop.1 (hβw0.eventually (gt_mem_nhds hc))
  obtain ⟨ε', hε'0, hε'ε, hε'δ, hε'1, hε't, hε'one⟩ :
      ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ δ ∧ ε' ≤ ε₁ ∧ ε' ≤ εt ∧ ε' ≤ 1 :=
    ⟨min (min ε δ) (min (min ε₁ εt) 1), lt_min (lt_min hε hδ) (lt_min (lt_min hε₁ hεt) one_pos),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨R', hRR', hR₂R', hR₁R', hRtR', -⟩ :
      ∃ R' : ℝ, R ≤ R' ∧ 2 * R₂ + 2 ≤ R' ∧ R₁ ≤ R' ∧ Rt ≤ R' ∧ a ≤ 4 * R' := by
    refine ⟨max (max R (2 * R₂ + 2)) (max (max R₁ Rt) (a / 4)),
      (le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
    have := (le_max_right (max R₁ Rt) (a / 4)).trans (le_max_right (max R (2 * R₂ + 2)) _)
    linarith
  obtain ⟨k', hkk', hmk', hk₁k', hktk'⟩ : ∃ k' : ℕ, k ≤ k' ∧ m ≤ k' ∧ k₁ ≤ k' ∧ kt ≤ k' :=
    ⟨max (max k m) (max k₁ kt), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  refine ⟨ε', R', k', hε'0, by linarith, hε'ε, hRR', hkk', max (max Tt (T₁ / 2)) (Tβ / 2), ?_⟩
  intro t t₂ ht hTe ht₂ f hf
  have hTt' : Tt ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans hTe)
  have hT₁' : T₁ ≤ t₂ := by
    have := (le_max_right Tt (T₁ / 2)).trans ((le_max_left _ (Tβ / 2)).trans hTe); linarith
  have hTβ' : Tβ ≤ t₂ := by
    have := (le_max_right (max Tt (T₁ / 2)) (Tβ / 2)).trans hTe; linarith
  have hβc := hTβ t₂ hTβ'
  have hβ0 : 0 < βw t₂ := hβw t₂
  have hβδ : βw t₂ ≤ δ := (lt_of_lt_of_le hβc (min_le_left _ _)).le
  have hLβ : max (max (m : ℝ) (2 * R₂ + 2)) ρ + 1 < (βw t₂)⁻¹ := by
    have h1 : βw t₂ < 1 / (max (max (m : ℝ) (2 * R₂ + 2)) ρ + 1) :=
      lt_of_lt_of_le hβc (min_le_right _ _)
    rw [one_div] at h1
    exact (lt_inv_comm₀ hL hβ0).2 h1
  have hmβ : (m : ℝ) ≤ (βw t₂)⁻¹ := by
    have := (le_max_left (m : ℝ) (2 * R₂ + 2)).trans (le_max_left _ ρ); linarith
  have h2Rβ : 2 * R₂ + 2 ≤ (βw t₂)⁻¹ := by
    have := (le_max_right (m : ℝ) (2 * R₂ + 2)).trans (le_max_left _ ρ); linarith
  have hρβ : ρ ≤ (βw t₂)⁻¹ := by
    have := le_max_right (max (m : ℝ) (2 * R₂ + 2)) ρ; linarith
  have hmceil : m ≤ ⌈(βw t₂)⁻¹⌉₊ := by exact_mod_cast hmβ.trans (Nat.le_ceil _)
  have ht₂0 : 0 < t₂ := by linarith
  have hpos : 0 < t₂⁻¹ := inv_pos.2 ht₂0
  have h1 : t₂ ∈ Icc t t₂ := ⟨by linarith, le_rfl⟩
  obtain ⟨hqs, hqi, hqe⟩ := hf t₂ h1
  obtain ⟨φ, U', y₀, hU'b, hφs, hφe, hφg, hφy⟩ := hanc t₂ hT₁' (f t₂ h1) R' hR₁R' hqs hqi
    (fun k'' hk p hp => (hqe k'' (hk.trans hk₁k') p hp).trans_le hε'1)
  have hR'0 : 0 ≤ R' := by linarith
  obtain ⟨hqsU, hqemb⟩ := smoothedMap_embedding_S72 H (postMetric F.observation t₂) t₂⁻¹
    (f t₂ h1) id R' hR'0 contMDiff_id Function.bijective_id (fun p _ => rfl)
    (fun p _ => by
      rw [ckErr_eq_zero_of_eq_id_O40 H id ⊤ (fun x _ => rfl) 0 p (by simp)]; exact one_pos)
    hqs hqi (fun p hp => (hqe 0 (Nat.zero_le _) p hp).trans_le hε'one)
    ⟨riemannianBallOf H.metric H.basepoint R', isOpen_riemannianBallOf_S61 H R'⟩ subset_rfl
  obtain ⟨E, e, he, he', hiso, hey, hEs, hsl, hE0, hsupp, hspeed, hck, hend, hdisp⟩ :=
    hcore (scaleMetric t₂⁻¹ hpos (postMetric F.observation t₂))
      ⟨riemannianBallOf H.metric H.basepoint R', isOpen_riemannianBallOf_S61 H R'⟩ U' (f t₂ h1) φ y₀
      (riemannianBallOf_mono _ _ hR₂R')
      ((riemannianBallOf_mono _ _ (by linarith)).trans hU'b)
      hqsU hqemb hφs hφe hφy.symm
      (fun j hj p hp => by
        rw [← ckErr_eq_scale_O19]
        exact (hqe j (hj.trans hmk') p (riemannianBallOf_mono _ _ (by linarith) hp)).trans_le hε'δ)
      (fun j hj p hp => by
        rw [← ckErr_eq_scale_O19]
        exact (hφg j (hj.trans hmceil) p (riemannianBallOf_mono _ _ (by linarith) hp)).trans_le hβδ)
  have hβi : 0 < (βw t₂)⁻¹ := inv_pos.2 hβ0
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := step_good_O54 H (postMetric F.observation t₂) t₂⁻¹ hpos e he
    he' hiso φ U' y₀ hβ0 hρ.le (by linarith) hey hU'b hφs hφe hφg
  have hmin0 : 0 ≤ min ε 1 := le_min hε.le zero_le_one
  have hcm : c * min ε 1 ≤ min ε 1 := mul_le_of_le_one_left hmin0 hc1
  have hσI : ∀ μ : ℝ, Real.smoothTransition μ ∈ Icc (0 : ℝ) 1 :=
    fun μ => ⟨Real.smoothTransition.nonneg μ, Real.smoothTransition.le_one μ⟩
  obtain ⟨hEs', hspeed'⟩ := hrep E (min ε 1) hmin0 hEs hspeed
  refine ⟨fun q => E (Real.smoothTransition q.1, q.2), fun x => φ (e x), ⟨U, hU1, hU2, hU3, hU4⟩,
    hEs', fun μ => hsl (Real.smoothTransition μ), fun p => ?_,
    fun μ p hp => hsupp (Real.smoothTransition μ) p hp,
    fun μ hμ p => le_trans (hspeed' μ hμ p) (pow_le_pow_left₀ hmin0 (min_le_left _ _) 2),
    fun μ _ i hi p _ => (hck (Real.smoothTransition μ) (hσI μ) i hi p).trans
      (hcm.trans (min_le_left _ _)),
    fun _ p hp => ?_, ?_⟩
  · change E (Real.smoothTransition 0, p) = p
    rw [Real.smoothTransition.zero]
    exact hE0 p
  · change f t₂ _ (E (Real.smoothTransition 1, p)) = φ (e p)
    rw [Real.smoothTransition.one]
    exact hend p hp
  · exact hthick t t₂ ht hTt' R' ε' k' hRtR' hε't hktk' f hf E
      (fun μ hμ p => (hdisp μ hμ p).trans
        (ENNReal.ofReal_le_ofReal (hcm.trans (min_le_right _ _))))

/-- `hEnd_O74`: hEnd-S for `(S, Φ)` = `hEnd_S_of_parts_O32 … (hconvS_O32 …) hstepW_O74` (binder `hthickW'`). -/
theorem hEnd_O74 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (S : LatePointSequence_S13 F)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
    (C : MetricConvergenceData Φ)
    (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
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
    (hHPS01 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
      (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover →
      ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
      ∃ R θ δ : ℝ, 0 < R ∧ 0 < θ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
        O ⊆ riemannianBallOf H.metric o R ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (e : H.Carrier ≃ H'.Carrier),
          ContMDiff (𝓡 3) (𝓡 3) ∞ e → ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm →
          (∀ p, localPullInner H'.metric e p = H.metric.inner p) →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric o (2 * R) ⊆ U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
            ckErr_O19 H H'.metric 1 f j p < δ) →
          (∀ p ∈ riemannianBallOf H.metric o R,
            riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal θ) →
          (∀ p ∈ O, riemannianEDistOf H.metric p (e.symm (f p)) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (f p)) ∧
          e '' O ⊆ f '' (U : Set H.Carrier) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn f U (e p)) O ∧
          (∀ p ∈ O, riemannianEDistOf H.metric p (Function.invFunOn f U (e p)) <
            ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p)))
    (Tr : HyperbolicTruncation H)
    (hthickW' :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (a + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r)
    (hanchor :
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
        φ y₀ = q H.basepoint) :
    ∃ β : ℝ → ℝ, (∀ t, 0 < β t) ∧ Filter.Tendsto β Filter.atTop (nhds 0) ∧
      (∃ I : ℕ, ∀ i : ℕ, I ≤ i →
        ∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sliceApprox_O32 S H Φ i) U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => sliceApprox_O32 S H Φ i x) ∧
          ∀ k : ℕ, k ≤ ⌈(β (S.slices i).time)⁻¹⌉₊ →
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹),
            ckErr_S45 H (postMetric F.observation (S.slices i).time) (S.slices i).time⁻¹
              (sliceApprox_O32 S H Φ i) k p < β (S.slices i).time) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ (ε' R' : ℝ) (k' : ℕ), 0 < ε' ∧ 0 < R' ∧
        ε' ≤ ε ∧ R ≤ R' ∧ k ≤ k' ∧ ∃ Te : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Te ≤ t → t₂ = 2 * t →
        ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < β t) →
        ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
          (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'), f t h0 p = g₁ p) →
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
        ∃ (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(β t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < β t₂) ∧
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
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r) :=
  hEnd_S_of_parts_O32 F H wstar a S Φ (hconvS_O32 F H S Φ C hcan)
    (hstepW_O74 F H wstar a hHG06 hHPS01 Tr hthickW' hanchor)

end CX3

end GC.LongTime.Ch12
