import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAnchor_O60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Final_S86
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Comparison_O46
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LocalFlowPkg_S110

set_option autoImplicit false

/-! # CH12-O66 G2: hold.rig (old-core pair rigidity), `[FROZEN] CH12-O66`

`holdRig_O66`: if an admissible `q : H → M_t` (late `t`) sends the basepoint into the old core
`mold i t '' B((α i t)⁻¹/2)` then `H ≅ Hold i`.  The composite `(mold i t)⁻¹ ∘ q` is controlled by
`hpi02_inverse_comparison_S86` (constants depend on `H` only, uniform in the rebased target
`(Hold i, z)`); rigidity: `hHG06` at `(H, bp)` if some truncations satisfy `count H ≤ count Hold i`,
otherwise the frozen binder `hPRrev` (pair rigidity towards a model with fewer cusps). -/
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

/-- G2 (hold.rig): old-core pair rigidity.  Composite `(mold i t)⁻¹ ∘ q` via
`hpi02_inverse_comparison_S86` (constants uniform in the target model and point); then `hHG06` at
`(H, bp)` when some truncation counts satisfy `count H ≤ count Hold i`, else `hPRrev`. -/
theorem holdRig_O66 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u})
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
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
    (hPRrev : ∀ (H H' : FiniteVolumeHyperbolicModel.{u}),
      (∀ (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation H'), Tr'.count < Tr.count) →
      ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric H.basepoint R ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
            ckErr_O19 H H'.metric 1 f j p < ε) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧ ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    (α : Fin old → ℝ → ℝ) (hαpos : ∀ i t, 0 < α i t)
    (hα0 : ∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0))
    (hgood : (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
        ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t))
    :
  ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧ ∃ T : ℝ,
        ∀ (i : Fin old) (t : ℝ) (hi : sold i ≤ t), T ≤ t →
        ∀ (q : H.Carrier → (postStage F.observation t).Carrier) (R'' : ℝ), R ≤ R'' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ q k'' p < ε) →
        ∀ z ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint ((α i t)⁻¹ / 2),
          mold i t hi z = q H.basepoint →
        ∃ e : H.Carrier ≃ (Hold i).Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
          ∀ p, localPullInner (Hold i).metric e p = H.metric.inner p
    := by
  classical
  -- per-model constants of `hPRrev` (only used when every count of `Hold i` is `< count H`)
  have hPi : ∀ i : Fin old, ∃ (εi Ri : ℝ) (ki : ℕ), 0 < εi ∧ 0 < Ri ∧
      ((∀ (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation (Hold i)),
        Tr'.count < Tr.count) →
      ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → (Hold i).Carrier),
        riemannianBallOf H.metric H.basepoint Ri ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ ki → ∀ p ∈ riemannianBallOf H.metric H.basepoint Ri,
          ckErr_O19 H (Hold i).metric 1 f j p < εi) →
        ∃ e : H.Carrier ≃ (Hold i).Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
          ∀ p, localPullInner (Hold i).metric e p = H.metric.inner p) := by
    intro i
    by_cases hc : ∀ (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation (Hold i)),
        Tr'.count < Tr.count
    · obtain ⟨ε, R, k, hε, hR, h⟩ := hPRrev H (Hold i) hc
      exact ⟨ε, R, k, hε, hR, fun _ => h⟩
    · exact ⟨1, 1, 0, one_pos, one_pos, fun h => absurd h hc⟩
  choose εi Ri ki hεi hRi hPR using hPi
  -- HG06 at `(H, bp, η = 1)`
  obtain ⟨ξ, hξ, n, -, -, hHG⟩ := hHG06 H H.basepoint 1 one_pos
  -- uniform constants
  obtain ⟨R₀, hR₀i, hξR₀, hR₀pos⟩ : ∃ R₀ : ℝ, (∀ i, Ri i ≤ R₀) ∧ ξ⁻¹ < R₀ ∧ 0 < R₀ :=
    ((eventually_all.2 fun i => eventually_ge_atTop (Ri i)).and
      ((eventually_gt_atTop ξ⁻¹).and (eventually_gt_atTop (0 : ℝ)))).exists
  obtain ⟨j₀, hj₀i, hnj₀⟩ : ∃ j₀ : ℕ, (∀ i, ki i ≤ j₀) ∧ n + 1 ≤ j₀ :=
    ((eventually_all.2 fun i => eventually_ge_atTop (ki i)).and
      (eventually_ge_atTop (n + 1))).exists
  obtain ⟨ε₀, hε₀pos, hε₀ξ, hε₀i⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < ξ / 3 ∧ ∀ i, ε₀ < εi i := by
    have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < ξ / 3 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by positivity : (0 : ℝ) < ξ / 3))
    have h2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ i, x < εi i :=
      eventually_all.2 fun i => nhdsWithin_le_nhds (gt_mem_nhds (hεi i))
    exact (eventually_mem_nhdsWithin.and (h1.and h2)).exists
  obtain ⟨δ, hδ, m, hS⟩ := hpi02_inverse_comparison_S86 H R₀ ε₀ j₀ hR₀pos hε₀pos
  -- late times: `α i t` small for every old model
  have hev : ∀ i, ∀ᶠ t in atTop, 0 < t ∧ α i t < δ ∧
      ((m : ℝ) + 1 ≤ (α i t)⁻¹ ∧ 16 * R₀ + 16 ≤ 3 * (α i t)⁻¹) := by
    intro i
    have hinv : Tendsto (fun t => (α i t)⁻¹) atTop atTop :=
      tendsto_inv_nhdsGT_zero.comp
        (tendsto_nhdsWithin_iff.2 ⟨hα0 i, Eventually.of_forall (hαpos i)⟩)
    refine (eventually_gt_atTop 0).and (((hα0 i).eventually (gt_mem_nhds hδ)).and ?_)
    filter_upwards [hinv.eventually_ge_atTop ((m : ℝ) + 1),
      hinv.eventually_ge_atTop ((16 * R₀ + 16) / 3)] with t h1 h2
    exact ⟨h1, by linarith⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 (eventually_all.2 hev)
  refine ⟨min δ 1, R₀ + 1, m, lt_min hδ one_pos, by linarith, T, ?_⟩
  intro i t hi hTt q R'' hRR hqsm hqinj hqck z hz hzq
  obtain ⟨htpos, hαδ, hαm, hαR⟩ := hT t hTt i
  have hc : 0 < t⁻¹ := inv_pos.mpr htpos
  have hαp := hαpos i t
  have : Nonempty (Hold i).Carrier := ⟨z⟩
  let gN := scaleMetric t⁻¹ hc (postMetric F.observation t)
  let UQ : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint (4 * R''), isOpen_riemannianBallOf _ _ _⟩
  have hqemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : UQ => q x) :=
    isSmoothEmbedding_phi_S110 H q UQ hqsm (fun y hy => (ckErr0_immersion_S60 H _ _ q y
      ((hqck 0 (Nat.zero_le _) y hy).trans_le (min_le_right _ _))).2) hqinj
  obtain ⟨U', hU'ball, hmsm, hmemb, hmck⟩ := hgood i t hi
  let Hz : FiniteVolumeHyperbolicModel.{u} := { Hold i with basepoint := z }
  have hzball : riemannianBallOf (Hold i).metric z (8 * R₀ + 8) ⊆
      riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) := by
    intro p hp
    change riemannianEDistOf (Hold i).metric (Hold i).basepoint p < ENNReal.ofReal (2 * (α i t)⁻¹)
    calc riemannianEDistOf (Hold i).metric (Hold i).basepoint p
        ≤ riemannianEDistOf (Hold i).metric (Hold i).basepoint z +
            riemannianEDistOf (Hold i).metric z p := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal ((α i t)⁻¹ / 2) + ENNReal.ofReal (8 * R₀ + 8) :=
          ENNReal.add_lt_add hz hp
      _ = ENNReal.ofReal ((α i t)⁻¹ / 2 + (8 * R₀ + 8)) :=
          (ENNReal.ofReal_add (by positivity) (by linarith)).symm
      _ ≤ ENNReal.ofReal (2 * (α i t)⁻¹) := ENNReal.ofReal_le_ofReal (by linarith)
  have hmle : m ≤ ⌈(α i t)⁻¹⌉₊ :=
    Nat.cast_le.1 ((by linarith : (m : ℝ) ≤ (α i t)⁻¹).trans (Nat.le_ceil _))
  have hsubQ : riemannianBallOf H.metric H.basepoint (2 * R₀ + 2) ⊆
      riemannianBallOf H.metric H.basepoint (4 * R'') :=
    riemannianBallOf_mono _ _ (by linarith)
  obtain ⟨hmem, hsm', hck'⟩ := hS Hz gN UQ U' q (mold i t hi) hsubQ (hzball.trans hU'ball)
    hqsm hqemb hmsm hmemb hzq.symm
    (fun j hj p hp => by
      rw [← ckErr_eq_scale_O19 H _ t⁻¹ hc]
      exact (hqck j hj p (hsubQ hp)).trans_le (min_le_left _ _))
    (fun j hj p hp => by
      rw [← ckErr_eq_scale_O19 Hz _ t⁻¹ hc]
      exact (hmck j (hj.trans hmle) p (hzball hp)).trans hαδ)
  let V : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint R₀, isOpen_riemannianBallOf _ _ _⟩
  have hVU : V ≤ UQ := riemannianBallOf_mono _ _ (by linarith)
  have hemb₁ := isSmoothEmbedding_invFunOn_comp_O46 q (mold i t hi) UQ V U' hVU hqemb hmemb
    hmem hsm'
  by_cases hcnt : ∀ (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation (Hold i)),
      Tr'.count < Tr.count
  · exact hPR i hcnt V _ (riemannianBallOf_mono _ _ (hR₀i i)) hsm' hemb₁
      (fun j hj p hp => (hck' j (hj.trans (hj₀i i)) p
        (riemannianBallOf_mono _ _ (hR₀i i) hp)).trans (hε₀i i))
  · simp only [not_forall, not_lt] at hcnt
    obtain ⟨Tr, Tr', hTr⟩ := hcnt
    obtain ⟨e, he, he', hiso, -⟩ := hHG (Hold i) Tr Tr' hTr V _
      (closedBall_subset_ball_O19 H H.basepoint hξR₀ hR₀pos) hsm' hemb₁
      (fun j hj p hp => (hck' j (hj.trans hnj₀) p
        (closedBall_subset_ball_O19 H H.basepoint hξR₀ hR₀pos hp)).trans hε₀ξ)
    exact ⟨e, he, he', hiso⟩

end GC.LongTime.Ch12
