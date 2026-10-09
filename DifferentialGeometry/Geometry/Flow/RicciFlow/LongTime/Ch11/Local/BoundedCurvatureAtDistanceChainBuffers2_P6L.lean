import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceChainBuffers_P6L

/-!
# L6-B：`BoundedCurvatureAtDistanceChainBuffers:149` 的局部化（`_P6L`）

局部化合同 §2 (G)：原 `RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball`
（`ST/BoundedCurvatureAtDistanceChainBuffers.lean:149`）的 `hgradient`（carrier 全局）只经 CB:18 在
链点 `p k`（`k < N`）的小球上求值（原 l.218）。链点不在基点的固定球内被证明（d(x, p k) < k·r₀），
故**在使用点补成员关系**：新增 `U` 与 `hchainU : ∀ k < N, B_T(p k, 4·r₀) ⊆ U`
（`r₀ = localPropagationRadius Cgrad / (2√(2Mb))`），调 CB:18 的 static `_P6L` 版。
调用方（TSL:170 层）须由收敛几何给出 `hchainU`（见 state-O-CH11-P6C HANDOVER"关键设计问题"）。
证明体照抄。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6L`**：原 `RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball`（CB:149）。
改动：`hgradient` 限于 `U`；加链点成员前提 `hchainU : ∀ k < N, B_T(p k, 4·r₀) ⊆ U`。结论逐字。 -/
theorem RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball_P6L
    (H : RetainedCoreHistory.{u}) {T : ℝ}
    (A : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    {Kc lam θ D : ℝ} {Ctime Cgrad : ℝ≥0} {Phi : ℝ → ℝ}
    (htrace : ∀ (N : ℕ) (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ)
      (M τ : ℝ), p 0 = x.val → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k),
        A.flow.scalar T z ≤ M) →
      Kc * A.flow.scalar T x.val ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ T →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * τ) *
          (lam / Real.sqrt (A.flow.scalar T x.val) + ∑ k ∈ Finset.range (N + 1), δ k) < D →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ T - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z))
    {q : ℝ} (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (hgradient : ∀ y ∈ U, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          Cgrad * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    {N : ℕ} (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (hp0 : p 0 = x.val)
    {Mb C2 M θ₂ : ℝ} (hMb : 0 < Mb) (hqMb : q ≤ Mb)
    (hpR : ∀ k < N, A.flow.scalar T (p k) ≤ Mb)
    (hchainU : ∀ k < N, riemannianBallOf (A.flow.base.metric T) (p k)
      (2 * (2 * (localPropagationRadius Cgrad / Real.sqrt (2 * Mb)))) ⊆ U)
    (hchain : ∀ k < N, p (k + 1) ∈ riemannianBallOf (A.flow.base.metric T) (p k)
      (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * Mb))))
    (hRN : 0 < A.flow.scalar T (p N))
    (hlast : ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p N)
      (Real.sqrt (A.flow.scalar T (p N)))⁻¹, A.flow.scalar T z ≤ C2 * A.flow.scalar T (p N))
    (hM6 : 6 * Mb ≤ M) (hMC : C2 * A.flow.scalar T (p N) ≤ M)
    (hMK : Kc * A.flow.scalar T x.val ≤ M) (hM1 : 1 ≤ M) (hθ₂ : 0 ≤ θ₂)
    (hτT : θ₂ / A.flow.scalar T (p N) ≤ T)
    (hCτ : (Ctime : ℝ) * M * (θ₂ / A.flow.scalar T (p N)) ≤ 1 / 2)
    (h4 : 4 * M * (θ₂ / A.flow.scalar T (p N)) ≤ θ)
    (hD : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) *
        (θ₂ / A.flow.scalar T (p N))) *
        (lam / Real.sqrt (A.flow.scalar T x.val) +
          (N * (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * Mb))) +
            (Real.sqrt (A.flow.scalar T (p N)))⁻¹)) < D) :
    ∃ first : Fin (H.eventCount + 1), H.time first ≤ T - θ₂ / A.flow.scalar T (p N) ∧
      ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p N) (Real.sqrt (A.flow.scalar T (p N)))⁻¹,
        Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
          (Fin.le_last first) z) := by
  classical
  set r₀ := localPropagationRadius Cgrad / (2 * Real.sqrt (2 * Mb)) with hr₀def
  have hr₀ : 0 < r₀ := div_pos (localPropagationRadius_pos Cgrad.coe_nonneg) (by positivity)
  have hsN : 0 < (Real.sqrt (A.flow.scalar T (p N)))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hRN)
  let δ : ℕ → ℝ := fun k => if k < N then r₀ else (Real.sqrt (A.flow.scalar T (p N)))⁻¹
  have hδ : ∀ k ≤ N, 0 < δ k := fun k _ => by
    dsimp only [δ]
    split_ifs
    · exact hr₀
    · exact hsN
  have hδlt : ∀ k < N, δ k = r₀ := fun k hk => ite_eq_left hk
  have hδN : δ N = (Real.sqrt (A.flow.scalar T (p N)))⁻¹ := ite_eq_right (lt_irrefl N)
  have hsum : ∑ k ∈ Finset.range (N + 1), δ k = N * r₀ + (Real.sqrt (A.flow.scalar T (p N)))⁻¹ := by
    rw [Finset.sum_range_succ, hδN, Finset.sum_congr rfl (fun k hk => hδlt k
      (Finset.mem_range.mp hk)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hτ0 : 0 ≤ θ₂ / A.flow.scalar T (p N) := div_nonneg hθ₂ hRN.le
  have htr := htrace N p δ M (θ₂ / A.flow.scalar T (p N)) hp0 hδ
    (fun k hk => by rw [hδlt k hk]; exact hchain k hk)
    (fun k hk z hz => by
      rcases lt_or_eq_of_le hk with hlt | heq
      · rw [hδlt k hlt] at hz
        exact (A.scalar_le_six_mul_on_ball_of_gradient_bound_static_P6L Cgrad hMb hqMb U hgradient
          (p k) (hchainU k hlt) (hpR k hlt) z hz).trans hM6
      · subst heq
        rw [hδN] at hz
        exact (hlast z hz).trans hMC)
    hMK hM1 hτ0 hτT hCτ h4 (by rw [hsum]; exact hD)
  obtain ⟨first, hfirst, hS⟩ := ObservedHistory.exists_uniform_backwardPointTrace_of_forall
    H.toHistory {z | z ∈ riemannianBallOf (A.flow.base.metric T) (p N)
      (Real.sqrt (A.flow.scalar T (p N)))⁻¹}
    (c := T - θ₂ / A.flow.scalar T (p N)) (by linarith) (fun z hz => by
      refine htr N le_rfl z ?_
      rw [hδN]
      exact hz)
  exact ⟨first, hfirst, fun z hz => hS z hz⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Set

/-- consumer：原 CB:149（全局 `hgradient`）由 `_P6L` 版（`U = univ`）推出。 -/
example : type_of% @RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball.{0}
    := by
  intro H T A x Kc lam θ D Ctime Cgrad Phi htrace q hgradient N p hp0 Mb C2 M θ₂ hMb hqMb hpR
    hchain hRN hlast hM6 hMC hMK hM1 hθ₂ hτT hCτ h4 hD
  exact H.exists_trace_first_of_chain_trace_on_witness_ball_P6L A x htrace univ
    (fun y _ => hgradient y) p hp0 hMb hqMb hpR (fun _ _ => subset_univ _) hchain hRN hlast hM6 hMC
    hMK hM1 hθ₂ hτT hCτ h4 hD

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
