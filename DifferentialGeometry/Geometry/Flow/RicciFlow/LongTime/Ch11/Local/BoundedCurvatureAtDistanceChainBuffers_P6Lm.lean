import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceChainBuffers3_P6L

/-!
# L6-B `_P6Lm`：CB:149 / CB:320 的链球成员前提版（供 TP:97_P6L 的 `htrace`）

O-CH11-P6A3 请求（[V]：`htrace` 由 SL:73_P6L 供给，其证明在链球点的 backward trace 点上用 footprint
`hslabs`）⇒ `htrace` 加链球成员前提
`(∀ k ≤ N, ∀ z ∈ B_T(p k, δ k), z ∈ U) →`（插在 `(∀ k ≤ N, 0 < δ k) →` 之后）。`U` 移到 `htrace` 前。
* CB:149_P6Lm：调 `htrace` 处补成员——`k < N` 由 `hchainU`（`r₀ ≤ 4·r₀`），`k = N` 由新增
  `hlastU : B_T(p N, (√R(p N))⁻¹) ⊆ U`。
* CB:320_P6Lm：`htrace`、`hlastU` 透传。
已交 `_P6L` 文件不改；私有算术引理（CB3_P6L l.29–105）复制为 `_P6Lm`。其余证明体照抄；结论逐字。
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

/-- `_P6Lm` 私有副本：原 private `two_mul_lt_of_mul_sub_one_lt`（ChainBuffers），逐字。 -/
private theorem two_mul_lt_of_mul_sub_one_lt_P6Lm {Q L R : ℝ} (hQ : 0 < Q) (hL : 3 ≤ L)
    (h : Q * (L - 1) < R) : 2 * Q < R := by
  have : 2 * Q ≤ Q * (L - 1) := by nlinarith
  linarith

/-- `_P6Lm` 私有副本：原 private `max_le_secondLevel_mul`（ChainBuffers），逐字。 -/
private theorem max_le_secondLevel_mul_P6Lm {K C2 Kc L Q Rn K₃ : ℝ} (hK₃6 : 6 * (K + 1) ≤ K₃)
    (hK₃C : 2 * C2 ≤ K₃) (hK₃K : Kc ≤ K₃) (hK₃1 : 1 ≤ K₃) (hK : 1 ≤ K) (hQ : 1 ≤ Q)
    (hL : 3 ≤ L) (hRn : Rn < Q * (L + 1)) (hC2 : 1 ≤ C2) :
    max (max (6 * ((K + 1) * L * Q)) (C2 * Rn)) (max (Kc * Q) 1) ≤ K₃ * L * Q := by
  have hLQ : 1 ≤ L * Q := one_le_mul_of_one_le_of_one_le (by linarith) hQ
  have hLQ0 : 0 ≤ L * Q := by linarith
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · calc 6 * ((K + 1) * L * Q) = 6 * (K + 1) * (L * Q) := by ring
      _ ≤ K₃ * (L * Q) := mul_le_mul_of_nonneg_right hK₃6 hLQ0
      _ = K₃ * L * Q := by ring
  · have h1 : C2 * Rn ≤ C2 * (Q * (L + 1)) := mul_le_mul_of_nonneg_left hRn.le (by linarith)
    have h2 : Q * (L + 1) ≤ 4 / 3 * (L * Q) := by
      have : 0 ≤ Q * (L / 3 - 1) := mul_nonneg (by linarith) (by linarith)
      linarith
    have h3 : C2 * (Q * (L + 1)) ≤ C2 * (4 / 3 * (L * Q)) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : 2 * C2 * (L * Q) ≤ K₃ * (L * Q) := mul_le_mul_of_nonneg_right hK₃C hLQ0
    have h5 : C2 * (4 / 3 * (L * Q)) ≤ 2 * C2 * (L * Q) := by
      have : 0 ≤ C2 * (L * Q) := mul_nonneg (by linarith) hLQ0
      linarith
    calc C2 * Rn ≤ K₃ * (L * Q) := h1.trans (h3.trans (h5.trans h4))
      _ = K₃ * L * Q := by ring
  · have h1 : Kc * Q ≤ K₃ * Q := mul_le_mul_of_nonneg_right hK₃K (by linarith)
    have h2 : K₃ * Q ≤ K₃ * (L * Q) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    calc Kc * Q ≤ K₃ * (L * Q) := h1.trans h2
      _ = K₃ * L * Q := by ring
  · calc (1 : ℝ) ≤ L * Q := hLQ
      _ ≤ K₃ * (L * Q) := le_mul_of_one_le_left hLQ0 hK₃1
      _ = K₃ * L * Q := by ring

/-- `_P6Lm` 私有副本：原 private `mul_div_le_three_halves`（ChainBuffers），逐字。 -/
private theorem mul_div_le_three_halves_P6Lm {M θ₂ Rn K₃ L Q : ℝ} (hM : M ≤ K₃ * L * Q)
    (hθ : 0 ≤ θ₂) (hRn : Q * (L - 1) < Rn) (hL : 3 ≤ L) (hQ : 0 < Q) (hK : 0 ≤ K₃) :
    M * (θ₂ / Rn) ≤ 3 / 2 * K₃ * θ₂ := by
  have hRnpos : 0 < Rn := lt_of_le_of_lt (mul_nonneg hQ.le (by linarith)) hRn
  rw [mul_div_assoc', div_le_iff₀ hRnpos]
  have h1 : M * θ₂ ≤ K₃ * L * Q * θ₂ := mul_le_mul_of_nonneg_right hM hθ
  have h2 : L * Q ≤ 3 / 2 * Rn := by
    have : L * Q ≤ 3 / 2 * (Q * (L - 1)) := by nlinarith
    linarith
  have h3 : K₃ * θ₂ * (L * Q) ≤ K₃ * θ₂ * (3 / 2 * Rn) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hK hθ)
  calc M * θ₂ ≤ K₃ * L * Q * θ₂ := h1
    _ = K₃ * θ₂ * (L * Q) := by ring
    _ ≤ K₃ * θ₂ * (3 / 2 * Rn) := h3
    _ = 3 / 2 * K₃ * θ₂ * Rn := by ring

/-- `_P6Lm` 私有副本：原 private `ctime_mul_le_half`（ChainBuffers），逐字。 -/
private theorem ctime_mul_le_half_P6Lm {C M τ K₃ θ₂ : ℝ} (hC : 0 ≤ C) (hτ : M * τ ≤ 3 / 2 * K₃ * θ₂)
    (hθ₂ : θ₂ ≤ 1 / (3 * (C + 1) * K₃)) (hK : 1 ≤ K₃) (hθ0 : 0 ≤ θ₂) :
    C * M * τ ≤ 1 / 2 := by
  have hpos : 0 < 3 * (C + 1) * K₃ := by positivity
  rw [le_div_iff₀ hpos] at hθ₂
  have h1 : C * M * τ ≤ C * (3 / 2 * K₃ * θ₂) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hτ hC
  have h2 : C * (3 / 2 * K₃ * θ₂) ≤ 1 / 2 := by
    have : 0 ≤ K₃ * θ₂ := by nlinarith
    nlinarith
  linarith

/-- `_P6Lm` 私有副本：原 private `four_mul_le_of_depth`（ChainBuffers），逐字。 -/
private theorem four_mul_le_of_depth_P6Lm {M τ K₃ θ₂ θ : ℝ} (hτ : M * τ ≤ 3 / 2 * K₃ * θ₂)
    (hθ₂ : θ₂ ≤ θ / (6 * K₃)) (hK : 1 ≤ K₃) : 4 * M * τ ≤ θ := by
  have hpos : 0 < 6 * K₃ := by linarith
  rw [le_div_iff₀ hpos] at hθ₂
  have : 4 * M * τ = 4 * (M * τ) := by ring
  rw [this]
  linarith

/-- **`_P6Lm`**：原 `RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball`（CB:149）。
改动：同 `_P6L`（`hgradient` 限于 `U`、`hchainU`）+ `htrace` 链球成员前提 + `hlastU`。结论逐字。 -/
theorem RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball_P6Lm
    (H : RetainedCoreHistory.{u}) {T : ℝ}
    (A : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    {Kc lam θ D : ℝ} {Ctime Cgrad : ℝ≥0} {Phi : ℝ → ℝ}
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (htrace : ∀ (N : ℕ) (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ)
      (M τ : ℝ), p 0 = x.val → (∀ k ≤ N, 0 < δ k) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k), z ∈ U) →
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
    {q : ℝ}
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
    (hlastU : riemannianBallOf (A.flow.base.metric T) (p N)
      (Real.sqrt (A.flow.scalar T (p N)))⁻¹ ⊆ U)
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
  have hr4 : r₀ ≤ 2 * (2 * (localPropagationRadius Cgrad / Real.sqrt (2 * Mb))) := by
    have ha : 0 < localPropagationRadius Cgrad / Real.sqrt (2 * Mb) :=
      div_pos (localPropagationRadius_pos Cgrad.coe_nonneg) (Real.sqrt_pos.mpr (by positivity))
    have hr : r₀ = localPropagationRadius Cgrad / Real.sqrt (2 * Mb) / 2 := by
      rw [hr₀def]
      ring
    rw [hr]
    linarith
  have htr := htrace N p δ M (θ₂ / A.flow.scalar T (p N)) hp0 hδ
    (fun k hk z hz => by
      rcases lt_or_eq_of_le hk with hlt | heq
      · rw [hδlt k hlt] at hz
        exact hchainU k hlt (riemannianBallOf_mono _ _ hr4 hz)
      · subst heq
        rw [hδN] at hz
        exact hlastU hz)
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

/-- **`_P6Lm`**：原 `RetainedCoreHistory.exists_trace_first_on_witness_ball_of_ray_chain`（CB:320）。
改动：同 `_P6L` + `htrace` 链球成员前提 + `hlastU`（透传 CB:149_P6Lm）。结论逐字。 -/
theorem RetainedCoreHistory.exists_trace_first_on_witness_ball_of_ray_chain_P6Lm
    (H : RetainedCoreHistory.{u}) {T : ℝ}
    (A : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (hQ : 1 ≤ A.flow.scalar T x.val) {Kc lam θ D : ℝ} {Ctime Cgrad : ℝ≥0} {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) (hlam : 0 ≤ lam) (hθ : 0 < θ)
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (htrace : ∀ (N : ℕ) (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ)
      (M τ : ℝ), p 0 = x.val → (∀ k ≤ N, 0 < δ k) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k), z ∈ U) →
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
    {q : ℝ} (hqQ : q ≤ A.flow.scalar T x.val)
    (hgradient : ∀ y ∈ U, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          Cgrad * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    {eps C1 C2 : ℝ}
    (hW : ∀ y ∈ U, q < A.flow.scalar T y →
      ∃ W : SpatialCanonicalWitness (A.flow.base.metric T) eps C1 C2 y, W.capTubeHasNeckChart eps)
    {K L : ℝ} (hK : 1 ≤ K) (hL : 3 ≤ L) {N : ℕ}
    (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (hp0 : p 0 = x.val)
    (hpR : ∀ k < N, A.flow.scalar T (p k) ≤ (K + 1) * L * A.flow.scalar T x.val)
    (hchainU : ∀ k < N, riemannianBallOf (A.flow.base.metric T) (p k)
      (2 * (2 * (localPropagationRadius Cgrad /
        Real.sqrt (2 * ((K + 1) * L * A.flow.scalar T x.val))))) ⊆ U)
    (hendU : p N ∈ U)
    (hlastU : riemannianBallOf (A.flow.base.metric T) (p N)
      (Real.sqrt (A.flow.scalar T (p N)))⁻¹ ⊆ U)
    (hdist : ∀ k < N, riemannianEDistOf (A.flow.base.metric T) (p k) (p (k + 1)) <
      ENNReal.ofReal (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L))) /
        Real.sqrt (A.flow.scalar T x.val)))
    (hyl : A.flow.scalar T x.val * (L - 1) < A.flow.scalar T (p N))
    (hyu : A.flow.scalar T (p N) < A.flow.scalar T x.val * (L + 1))
    (hT : secondLevelTraceDepth K C2 Kc θ Ctime ≤ A.flow.scalar T x.val * T)
    (hD : 2 * StandardCap.transitionEnd +
      Real.sqrt (8 * (secondLevelTraceConstant K C2 Kc * L)) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) *
        (3 / 2 * secondLevelTraceConstant K C2 Kc * secondLevelTraceDepth K C2 Kc θ Ctime)) *
      (lam + (N * (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L)))) + 1)) <
        D) :
    ∃ first : Fin (H.eventCount + 1),
      H.time first ≤ T - secondLevelTraceDepth K C2 Kc θ Ctime / A.flow.scalar T (p N) ∧
      ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p N) (Real.sqrt (A.flow.scalar T (p N)))⁻¹,
        Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
          (Fin.le_last first) z) := by
  set Q := A.flow.scalar T x.val with hQdef
  set Rn := A.flow.scalar T (p N) with hRndef
  set K₃ := secondLevelTraceConstant K C2 Kc with hK₃def
  set θ₂ := secondLevelTraceDepth K C2 Kc θ Ctime with hθ₂def
  have hK₃1 : 1 ≤ K₃ := one_le_secondLevelTraceConstant K C2 Kc
  have hK₃6 : 6 * (K + 1) ≤ K₃ := (le_max_left _ _).trans (le_max_left _ _)
  have hK₃C : 2 * C2 ≤ K₃ := (le_max_right _ _).trans (le_max_left _ _)
  have hK₃K : Kc ≤ K₃ := (le_max_left _ _).trans (le_max_right _ _)
  have hθ₂0 : 0 < θ₂ := secondLevelTraceDepth_pos Ctime hθ
  have hθ₂a : θ₂ ≤ θ / (6 * K₃) := min_le_left _ _
  have hθ₂b : θ₂ ≤ 1 / (3 * ((Ctime : ℝ) + 1) * K₃) := min_le_right _ _
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hRnQ : 2 * Q < Rn := two_mul_lt_of_mul_sub_one_lt_P6Lm hQpos hL hyl
  have hRnpos : 0 < Rn := by linarith
  have hqRn : q < Rn := by linarith
  obtain ⟨Wy, -⟩ := hW (p N) hendU hqRn
  have hC2 : 1 ≤ C2 := Wy.one_le_comparison_constant
  have hlast : ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p N) (Real.sqrt Rn)⁻¹,
      A.flow.scalar T z ≤ C2 * Rn := fun z hz =>
    (Wy.scalar_bounds z (Wy.ball_inside (riemannianBallOf_mono _ _ Wy.radius_lower hz))).2
  set Mb := (K + 1) * L * Q with hMbdef
  have hMb : 0 < Mb := by positivity
  set M := max (max (6 * Mb) (C2 * Rn)) (max (Kc * Q) 1) with hMdef
  have hM6 : 6 * Mb ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMC : C2 * Rn ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMK : Kc * Q ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM1 : 1 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hMup : M ≤ K₃ * L * Q :=
    max_le_secondLevel_mul_P6Lm hK₃6 hK₃C hK₃K hK₃1 hK hQ hL hyu hC2
  have hτ : M * (θ₂ / Rn) ≤ 3 / 2 * K₃ * θ₂ :=
    mul_div_le_three_halves_P6Lm hMup hθ₂0.le hyl hL hQpos (by linarith)
  have hKφ : 0 ≤ 8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) := by
    have := hPhi.pos 0
    have := hPhi.pos 1
    positivity
  have hr₀ : localPropagationRadius Cgrad / (2 * Real.sqrt (2 * Mb)) =
      localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L))) / Real.sqrt Q := by
    rw [hMbdef, show 2 * ((K + 1) * L * Q) = 2 * ((K + 1) * L) * Q by ring,
      Real.sqrt_mul (by positivity)]
    field_simp
  refine RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball_P6Lm H A x U htrace
    hgradient p hp0 hMb (hqQ.trans ?_) hpR hchainU (fun k hk => ?_) hRnpos hlast hlastU hM6 hMC hMK
    hM1 hθ₂0.le ?_ (ctime_mul_le_half_P6Lm Ctime.coe_nonneg hτ hθ₂b hK₃1 hθ₂0.le)
    (four_mul_le_of_depth_P6Lm hτ hθ₂a hK₃1) ?_
  · calc Q = 1 * 1 * Q := by ring
      _ ≤ (K + 1) * L * Q := by
        apply mul_le_mul_of_nonneg_right _ hQpos.le
        exact mul_le_mul (by linarith) (by linarith) zero_le_one (by linarith)
  · change riemannianEDistOf _ _ _ < _
    rw [hr₀]
    exact hdist k hk
  · have hT0 : 0 ≤ T := (H.toHistory.time_nonneg _).trans A.lt.le
    rw [div_le_iff₀ hRnpos]
    have : Q * T ≤ Rn * T := mul_le_mul_of_nonneg_right (by linarith) hT0
    linarith
  · refine lt_of_le_of_lt ?_ hD
    have hsqM : Real.sqrt (8 * M) ≤ Real.sqrt (8 * (K₃ * L)) * Real.sqrt Q := by
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      calc 8 * M ≤ 8 * (K₃ * L * Q) := by linarith
        _ = 8 * (K₃ * L) * Q := by ring
    have hexp : Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * (θ₂ / Rn)) ≤
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) * (3 / 2 * K₃ * θ₂)) := by
      apply Real.exp_le_exp.mpr
      have h9 : 9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * (θ₂ / Rn) =
          9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) * (M * (θ₂ / Rn)) := by ring
      rw [h9]
      exact mul_le_mul_of_nonneg_left hτ (by positivity)
    have hinvRn : (Real.sqrt Rn)⁻¹ ≤ 1 / Real.sqrt Q := by
      rw [one_div]
      exact inv_anti₀ hsQ (Real.sqrt_le_sqrt (by linarith))
    have hlp := localPropagationRadius_pos Cgrad.coe_nonneg
    have hsum : lam / Real.sqrt Q + (N * (localPropagationRadius Cgrad /
        (2 * Real.sqrt (2 * ((K + 1) * L))) / Real.sqrt Q) + (Real.sqrt Rn)⁻¹) ≤
        (lam + (N * (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L)))) + 1)) /
          Real.sqrt Q := by
      rw [add_div, add_div, mul_div_assoc]
      linarith
    rw [hr₀]
    have hpos1 : 0 ≤ lam / Real.sqrt Q + (N * (localPropagationRadius Cgrad /
        (2 * Real.sqrt (2 * ((K + 1) * L))) / Real.sqrt Q) + (Real.sqrt Rn)⁻¹) :=
      add_nonneg (div_nonneg hlam hsQ.le) (add_nonneg (mul_nonneg (Nat.cast_nonneg N)
        (div_nonneg (div_nonneg hlp.le (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
          hsQ.le)) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    have hexp0 := Real.exp_pos (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * (θ₂ / Rn))
    have hprod := mul_le_mul (mul_le_mul hsqM hexp hexp0.le
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hsum hpos1
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le)
    have heq : Real.sqrt (8 * (K₃ * L)) * Real.sqrt Q *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) * (3 / 2 * K₃ * θ₂)) *
        ((lam + (N * (localPropagationRadius Cgrad /
          (2 * Real.sqrt (2 * ((K + 1) * L)))) + 1)) / Real.sqrt Q) =
        Real.sqrt (8 * (K₃ * L)) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) * (3 / 2 * K₃ * θ₂)) *
        (lam + (N * (localPropagationRadius Cgrad /
          (2 * Real.sqrt (2 * ((K + 1) * L)))) + 1)) := by
      field_simp
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Set

/-- consumer：原 CB:149 由 `_P6Lm` 版（`U = univ`）推出。 -/
example : type_of% @RetainedCoreHistory.exists_trace_first_of_chain_trace_on_witness_ball.{0}
    := by
  intro H T A x Kc lam θ D Ctime Cgrad Phi htrace q hgradient N p hp0 Mb C2 M θ₂ hMb hqMb hpR
    hchain hRN hlast hM6 hMC hMK hM1 hθ₂ hτT hCτ h4 hD
  exact H.exists_trace_first_of_chain_trace_on_witness_ball_P6Lm A x univ
    (fun N p δ M τ h0 hδ _ => htrace N p δ M τ h0 hδ) (fun y _ => hgradient y) p hp0 hMb hqMb
    hpR (fun _ _ => subset_univ _) hchain hRN hlast (subset_univ _) hM6 hMC hMK hM1 hθ₂ hτT hCτ
    h4 hD

/-- consumer：原 CB:320 由 `_P6Lm` 版（`U = univ`）推出。 -/
example : type_of% @RetainedCoreHistory.exists_trace_first_on_witness_ball_of_ray_chain.{0}
    := by
  intro H T A x hQ Kc lam θ D Ctime Cgrad Phi hPhi hlam hθ htrace q hqQ hgradient eps C1 C2 hW
    K L hK hL N p hp0 hpR hdist hyl hyu hT hD
  exact H.exists_trace_first_on_witness_ball_of_ray_chain_P6Lm A x hQ hPhi hlam hθ univ
    (fun N p δ M τ h0 hδ _ => htrace N p δ M τ h0 hδ) hqQ (fun y _ => hgradient y)
    (fun y _ => hW y) hK hL p hp0 hpR (fun _ _ => subset_univ _) (mem_univ _) (subset_univ _)
    hdist hyl hyu hT hD

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
