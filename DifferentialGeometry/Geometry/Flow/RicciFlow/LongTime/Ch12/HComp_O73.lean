import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAnchor_O60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Final_S86
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Comparison_O46
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LocalFlowPkg_S110
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompImmersion_S60

set_option autoImplicit false

/-! # CH12-O73 G1: `hComp_O73 : <[FROZEN v2] CH12-O73 hComp>`

The composite near-isometry `f := (ψ|U')⁻¹ ∘ q : H → H'` of the `hComp` binder of
`newLimReg_O68` (H fixed, `[FROZEN v2] CH12-O73`).  Route (as in `holdRig_O66`):
`0 < t` from the order-0 error of `q` at the basepoint (`ckErr0_immersion_S60`); `q` is a smooth
embedding of `B(4R'')` (`isSmoothEmbedding_phi_S110`); S7 v3 `hpi02_inverse_comparison_S86` at
`R := ξ⁻¹ + 1`, `ε := min (ξ/3) 1`, `j₀ := n' + 1` for the target metric `t⁻¹ g(t)`
(`ckErr_eq_scale_O19`); `f` is a smooth embedding on `B(ξ⁻¹+1)` by
`isSmoothEmbedding_invFunOn_comp_O46`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace GC.LongTime.Ch12

/-- G1 (`[FROZEN v2] CH12-O73` hComp). -/
theorem hComp_O73 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) :
    ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
      ∃ (δ r : ℝ) (m' : ℕ), 0 < δ ∧ 0 < r ∧
      ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (t : ℝ)
        (q : H.Carrier → (postStage F.observation t).Carrier)
        (ψ : H'.Carrier → (postStage F.observation t).Carrier) (R'' : ℝ)
        (U' : TopologicalSpace.Opens H'.Carrier), R ≤ R'' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ q k'' p < ε) →
        riemannianBallOf H'.metric H'.basepoint r ⊆ U' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ U' →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => ψ x) →
        (∀ k'' : ℕ, k'' ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
          ckErr_S45 H' (postMetric F.observation t) t⁻¹ ψ k'' p < δ) →
        ψ H'.basepoint = q H.basepoint →
        ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
          ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
            ckErr_O19 H H'.metric 1 f k p < ξ / 3 := by
  intro ξ n' hξ
  have hξi : 0 < ξ⁻¹ := inv_pos.mpr hξ
  have hR₁ : (0 : ℝ) < ξ⁻¹ + 1 := by linarith
  have hε₁ : (0 : ℝ) < min (ξ / 3) 1 := lt_min (by positivity) one_pos
  obtain ⟨δ, hδ, m, hS⟩ :=
    hpi02_inverse_comparison_S86 H (ξ⁻¹ + 1) (min (ξ / 3) 1) (n' + 1) hR₁ hε₁
  refine ⟨min δ 1, ξ⁻¹ + 1, m, lt_min hδ one_pos, hR₁, δ, 8 * (ξ⁻¹ + 1) + 8, m, hδ,
    by linarith, ?_⟩
  intro H' t q ψ R'' U' hRR hqsm hqinj hqck hball hψsm hψemb hψck hbase
  have hbp : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (4 * R'') := by
    change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal (4 * R'')
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hc : 0 < t⁻¹ := (ckErr0_immersion_S60 H _ _ q H.basepoint
    ((hqck 0 (Nat.zero_le _) _ hbp).trans_le (min_le_right _ _))).1
  have : Nonempty H'.Carrier := ⟨H'.basepoint⟩
  let gN := scaleMetric t⁻¹ hc (postMetric F.observation t)
  let UQ : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint (4 * R''), isOpen_riemannianBallOf _ _ _⟩
  have hqemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : UQ => q x) :=
    isSmoothEmbedding_phi_S110 H q UQ hqsm (fun y hy => (ckErr0_immersion_S60 H _ _ q y
      ((hqck 0 (Nat.zero_le _) y hy).trans_le (min_le_right _ _))).2) hqinj
  have hsubQ : riemannianBallOf H.metric H.basepoint (2 * (ξ⁻¹ + 1) + 2) ⊆
      riemannianBallOf H.metric H.basepoint (4 * R'') :=
    riemannianBallOf_mono _ _ (by linarith)
  obtain ⟨hmem, hsm', hck'⟩ := hS H' gN UQ U' q ψ hsubQ hball hqsm hqemb hψsm hψemb hbase.symm
    (fun j hj p hp => by
      rw [← ckErr_eq_scale_O19 H _ t⁻¹ hc]
      exact (hqck j hj p (hsubQ hp)).trans_le (min_le_left _ _))
    (fun j hj p hp => by
      rw [← ckErr_eq_scale_O19 H' _ t⁻¹ hc]
      exact hψck j hj p hp)
  let V : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint (ξ⁻¹ + 1), isOpen_riemannianBallOf _ _ _⟩
  have hVU : V ≤ UQ := riemannianBallOf_mono _ _ (by linarith)
  have hcb : riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ V :=
    closedBall_subset_ball_O19 H H.basepoint (by linarith) hR₁
  refine ⟨V, fun p => Function.invFunOn ψ U' (q p), hcb, hsm',
    isSmoothEmbedding_invFunOn_comp_O46 q ψ UQ V U' hVU hqemb hψemb hmem hsm', ?_⟩
  intro k hk p hp
  exact (hck' k hk p (hcb hp)).trans_le (min_le_left _ _)

end GC.LongTime.Ch12
