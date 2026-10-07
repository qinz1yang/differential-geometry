import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickPreimage_O76
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Final_S86
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Comparison_O46
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LocalFlowPkg_S110
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.IdGerm_O40
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrNaturality_O19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HPS02CkIsometry_O19

set_option autoImplicit false

/-! # CH12-O76 G2: `hPRrev_O76 : <[FROZEN] CH12-O66 hPRrev>` (reverse pair rigidity)

If every truncation of `H'` has fewer cusps than every truncation of `H`, a near-isometric embedding
`f` of a large ball `B_H(bp, R)` into `H'` gives an isometry `H ≅ H'`.
* `basepoint_preimage_O76` (G1): `f p₀ = bp'` for some `p₀ ∈ B_H(bp, 16 (D + 1))`, `D` uniform;
* `hpi02_inverse_comparison_S86` at the source `(H', id, ⊤)` and the rebased target
  `{H with basepoint := p₀}` (constants depend on `H'` only): `g := invFunOn f U` is a near-isometry
  on `B_H'(bp', ξ⁻¹ + 1)`; `isSmoothEmbedding_invFunOn_comp_O46`;
* `hHG06` at `(H', bp', 1)` (`count H' ≤ count H`): `e : H' ≃ H` isometric; answer `e.symm`
  (`inner_mfderiv_symm_O19`).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-- **G2 (hPRrev producer).** -/
theorem hPRrev_O76
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
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
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η) :
    ∀ (H H' : FiniteVolumeHyperbolicModel.{u}),
      (∀ (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation H'), Tr'.count < Tr.count) →
      ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric H.basepoint R ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
            ckErr_O19 H H'.metric 1 f j p < ε) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            ∀ p, localPullInner H'.metric e p = H.metric.inner p := by
  intro H H' hcnt
  classical
  obtain ⟨Tr⟩ := hHG03 H
  obtain ⟨Tr'⟩ := hHG03 H'
  obtain ⟨D, hD0, hpre⟩ := basepoint_preimage_O76 H H' Tr'
  obtain ⟨ξ, hξ, n, -, -, hHG⟩ := hHG06 H' H'.basepoint 1 one_pos
  set R₀ : ℝ := ξ⁻¹ + 1 with hR₀
  have hξi : 0 < ξ⁻¹ := inv_pos.mpr hξ
  have hR₀pos : 0 < R₀ := by linarith
  have hξR₀ : ξ⁻¹ < R₀ := by linarith
  obtain ⟨δ, hδ, m, hS⟩ :=
    hpi02_inverse_comparison_S86 H' R₀ (ξ / 3) (n + 1) hR₀pos (by positivity)
  refine ⟨min (1 / 8) δ, 16 * (D + 1) + (8 * R₀ + 8), m, lt_min (by norm_num) hδ,
    by positivity, ?_⟩
  intro U f hRU hf hemb hck
  obtain ⟨p₀, hp₀, hfp₀⟩ := hpre (16 * (D + 1) + (8 * R₀ + 8)) U f (by linarith) hRU hf hemb
    (fun p hp => (hck 0 (Nat.zero_le _) p hp).trans_le (min_le_left _ _))
  have : Nonempty H.Carrier := ⟨p₀⟩
  let Hp : FiniteVolumeHyperbolicModel.{u} := { H with basepoint := p₀ }
  have hp₀ball : riemannianBallOf H.metric p₀ (8 * R₀ + 8) ⊆
      riemannianBallOf H.metric H.basepoint (16 * (D + 1) + (8 * R₀ + 8)) := by
    intro p hp
    change riemannianEDistOf H.metric H.basepoint p <
      ENNReal.ofReal (16 * (D + 1) + (8 * R₀ + 8))
    calc riemannianEDistOf H.metric H.basepoint p
        ≤ riemannianEDistOf H.metric H.basepoint p₀ + riemannianEDistOf H.metric p₀ p :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (16 * (D + 1)) + ENNReal.ofReal (8 * R₀ + 8) :=
          ENNReal.add_lt_add hp₀ hp
      _ = ENNReal.ofReal (16 * (D + 1) + (8 * R₀ + 8)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hidemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (fun x : (⊤ : Opens H'.Carrier) => (id x : H'.Carrier)) :=
    isSmoothEmbedding_phi_S110 H' id ⊤ contMDiffOn_id
      (fun y _ => by rw [mfderiv_id]; exact fun a b h => h) (injOn_id _)
  obtain ⟨hmem, hsm', hck'⟩ := hS Hp H'.metric ⊤ U id f (fun x _ => by simp)
    (hp₀ball.trans hRU) contMDiffOn_id hidemb hf hemb hfp₀.symm
    (fun j _ p _ => by
      rw [show ckErr_O19 H' H'.metric 1 id j p = 0 from
        ckErr_eq_zero_of_eq_id_O40 H' id ⊤ (fun _ _ => rfl) j p (by simp)]
      exact hδ)
    (fun j hj p hp => (hck j hj p (hp₀ball hp)).trans_le (min_le_right _ _))
  let V : Opens H'.Carrier :=
    ⟨riemannianBallOf H'.metric H'.basepoint R₀, isOpen_riemannianBallOf _ _ _⟩
  have hemb₁ := isSmoothEmbedding_invFunOn_comp_O46 id f ⊤ V U le_top hidemb hemb hmem hsm'
  obtain ⟨e, he, he', hiso, -⟩ := hHG H Tr' Tr (hcnt Tr Tr').le V _
    (closedBall_subset_ball_O19 H' H'.basepoint hξR₀ hR₀pos) hsm' hemb₁
    (fun j hj p hp => hck' j hj p (closedBall_subset_ball_O19 H' H'.basepoint hξR₀ hR₀pos hp))
  refine ⟨e.symm, he', he, fun y => ?_⟩
  ext a b
  rw [localPullInner_apply]
  exact inner_mfderiv_symm_O19 H' H e he he' hiso y a b

end GC.LongTime.Ch12
