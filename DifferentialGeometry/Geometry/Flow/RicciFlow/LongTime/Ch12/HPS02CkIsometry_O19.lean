import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrDef_O19

/-!
# CH12-O19 G2: `hps02_Ck_isometry_O19` (H3, S1 v2)

From the frozen team rigidity shape `hHG06` (sheet S0) and the two-model HPS01 shape `hHPS01`
(frozen in `[FROZEN] CH12-O19`; staged binder until HPS01 is proved), the C^k-isometry statement
S1 v2 whose output is the `Φ` input of `transfer_isotopy_of_Ck_close_CX3`, in both directions
(`e.symm ∘ f` and `invFunOn f U ∘ e`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem closedBall_subset_ball_O19 (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
    {r r' : ℝ} (h : r < r') (hr' : 0 < r') :
    riemannianClosedBallOf H.metric o r ⊆ riemannianBallOf H.metric o r' := by
  intro y hy
  exact lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff hr').2 h)

theorem ball_subset_closedBall_O19 (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
    {r r' : ℝ} (h : r ≤ r') :
    riemannianBallOf H.metric o r ⊆ riemannianClosedBallOf H.metric o r' := by
  intro y hy
  exact hy.le.trans (ENNReal.ofReal_le_ofReal h)

/-- **HPS02 (S1 v2).**  `hHG06` = sheet S0 verbatim; `hHPS01` = the two-model HPS01 shape of
`[FROZEN] CH12-O19`.  Conclusion = O15's `[FROZEN v2]` S1v2 verbatim (with `ckErr_O19`). -/
theorem hps02_Ck_isometry_O19
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
          (∀ p ∈ O, Manifold.riemannianEDist (𝓡 3) p (e.symm (f p)) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (f p)) ∧
          e '' O ⊆ f '' (U : Set H.Carrier) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn f U (e p)) O ∧
          (∀ p ∈ O, Manifold.riemannianEDist (𝓡 3) p (Function.invFunOn f U (e p)) <
            ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p))) :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (A : CkAtlas_S15 (𝓡 3) H.Carrier)
      (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover → ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
      ∃ δ₀ R : ℝ, 0 < δ₀ ∧ 0 < R ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
        O ⊆ riemannianBallOf H.metric o R ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
          (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric o (2 * R) ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
            ckErr_O19 H H'.metric 1 f j p < δ₀) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => e.symm (f p)) O ∧
            (∀ p ∈ O, Manifold.riemannianEDist (𝓡 3) p (e.symm (f p)) < ENNReal.ofReal ρ) ∧
            CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (f p)) ∧
            e '' O ⊆ f '' (U : Set H.Carrier) ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn f U (e p)) O ∧
            (∀ p ∈ O, Manifold.riemannianEDist (𝓡 3) p (Function.invFunOn f U (e p)) <
              ENNReal.ofReal ρ) ∧
            CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p)) := by
  intro H o A D2 hD2 hD2A k ρ ε hρ hε
  obtain ⟨R, θ, δ, hR, hθ, hδ, m, O, hO, hD2O, hOR, hP⟩ :=
    hHPS01 H o A D2 hD2 hD2A k ρ ε hρ hε
  set η : ℝ := min θ R⁻¹ with hη_def
  have hη : 0 < η := lt_min hθ (inv_pos.2 hR)
  obtain ⟨ξ, hξ, n, -, -, hG⟩ := hHG06 H o η hη
  have hξinv : 0 < ξ⁻¹ := inv_pos.2 hξ
  have hR1 : 0 < max R ξ⁻¹ := lt_max_of_lt_left hR
  refine ⟨min δ (ξ / 3), max R ξ⁻¹, lt_min hδ (by positivity), hR1, max m (n + 1), O, hO, hD2O,
    hOR.trans (riemannianBallOf_mono H.metric o (le_max_left _ _)), ?_⟩
  intro H' Tr Tr' hcount U f hU hf hemb herr
  have hcb : riemannianClosedBallOf H.metric o ξ⁻¹ ⊆
      riemannianBallOf H.metric o (2 * max R ξ⁻¹) :=
    closedBall_subset_ball_O19 H o (by have := le_max_right R ξ⁻¹; linarith) (by positivity)
  obtain ⟨e, he, he', hiso, hclose⟩ := hG H' Tr Tr' hcount U f (hcb.trans hU) hf hemb
    (fun j hj p hp => (herr j (hj.trans (le_max_right _ _)) p (hcb hp)).trans_le
      (min_le_right _ _))
  have hball2 : riemannianBallOf H.metric o (2 * R) ⊆
      riemannianBallOf H.metric o (2 * max R ξ⁻¹) :=
    riemannianBallOf_mono H.metric o (by have := le_max_left R ξ⁻¹; linarith)
  have hRη : R ≤ η⁻¹ := (le_inv_comm₀ hR hη).2 (min_le_right _ _)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP H' e he he' hiso U f (hball2.trans hU) hf hemb
    (fun j hj p hp => (herr j (hj.trans (le_max_left _ _)) p (hball2 hp)).trans_le
      (min_le_left _ _))
    (fun p hp => (hclose p (ball_subset_closedBall_O19 H o hRη hp)).trans_le
      (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have hOU : O ⊆ (U : Set H.Carrier) :=
    hOR.trans ((riemannianBallOf_mono H.metric o (by linarith)).trans (hball2.trans hU))
  exact ⟨e, he, he', hiso, he'.comp_contMDiffOn (hf.mono hOU), h1, h2, h3, h4, h5, h6⟩

end GC.LongTime.Ch12
