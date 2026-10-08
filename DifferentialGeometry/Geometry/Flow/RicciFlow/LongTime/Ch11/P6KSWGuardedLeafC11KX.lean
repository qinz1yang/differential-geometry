import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedC11KX

/-!
# KSW-EXIT G2：叶证书 L1（rebase chain）与 L2（chain traces）（O-CH11-KSWEXIT，后缀 `_C11KX`）

G1 壳 `shortSLT_guarded_of_leaves_C11KX` 的三个叶 binder 里，L1 / L2 在本文件 **PROVED**。做法 =
"在调用点把 `U` 与窗口缩到 guard 内的局部柱，再调树内旧叶"——旧叶只在缩小后的数据上被调用，
新定理（guarded 形）严格更强，不是把新假设传给旧定理：
* `guardKX_of_ceiling_C11KX`（ceiling ⇒ guard）：`R(t, z) ≤ M`、`q ≤ M`、`t − τ ≤ v ≤ t`、`Ct·M·τ ≤ 1/2`
  ⇒ `GuardKX_C11KX`。这是五要素 3 的算术核：局部传播所需邻域落在 guard 内。
* **L2** `guardedChainTracesLeaf_C11KX`：P6N chain traces 只在链球（`R(t) ≤ M`，`qcan ≤ M`）上、深度 `τ`
  （`Ctime·M·τ ≤ 1/2`）用数据 ⇒ 取 `U′ := U ∩ {R(t, ·) ≤ M}`、窗口起点 `a′ := t − τ`（`a ≤ t − τ` 已给）
  调旧叶 `chain_traces_of_not_capWindowPoint_of_incomingSlab_late_P6N`；`hslabs` / `hderG` 的 guard 由
  `guardKX_of_ceiling_C11KX` 付（event slab 上 `v < time j⁺ ≤ time last < t`）。
* **L1** `guardedRebaseLeaf_C11KX`：P6WB rebase chain 的 `hgradient` 只在 `t → T⁻` 求值（任意 `c < T`
  可用）⇒ carrier compact + `scalarCont` ⇒ `R(T, ·) ≤ Mb`；取 `Mc := |Mb| + |q| + 1`、
  `τ := 1/(2(Ct + 1)Mc)`、`c′ := max c (T − τ)` 调旧叶 `exists_rebase_chain_window_P6WB`；guard 由
  `guardKX_of_ceiling_C11KX` 付。
* consumer：`shortSLT_guarded_of_TP_C11KX`（PROVISIONAL[L3]）= G1 壳 ∘ (L1, L2)。
剩余 binder：L3 `GuardedTPLeaf_C11KX`（TP 复合叶，G3 拆 TL2 / TC / TTC / Cone）。
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

/-- **ceiling ⇒ guard（`_C11KX`）**：`R(t, z) ≤ M`、`q ≤ M`、`t − τ ≤ v ≤ t`、`Ct·M·τ ≤ 1/2` ⇒
`GuardKX_C11KX Rt q Ct t v z`。 -/
theorem guardKX_of_ceiling_C11KX {M : Type*} {Rt : M → ℝ} {q Ct t v Mc τ : ℝ} {z : M}
    (hCt : 0 ≤ Ct) (hz : Rt z ≤ Mc) (hq : q ≤ Mc) (hvt : v ≤ t) (hv : t - τ ≤ v)
    (hb : Ct * Mc * τ ≤ 1 / 2) : GuardKX_C11KX Rt q Ct t v z := by
  unfold GuardKX_C11KX
  have hm : max (Rt z) q ≤ Mc := max_le hz hq
  have hd0 : 0 ≤ t - v := sub_nonneg.mpr hvt
  have hdτ : t - v ≤ τ := by linarith
  rcases le_or_gt 0 (max (Rt z) q) with h0 | h0
  · have h1 : max (Rt z) q * (t - v) ≤ Mc * τ := mul_le_mul hm hdτ hd0 (h0.trans hm)
    nlinarith [mul_le_mul_of_nonneg_left h1 hCt]
  · have h1 : max (Rt z) q * (t - v) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0.le hd0
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hCt h1]

/-- **叶 L2 证书（`_C11KX`，PROVED）**：guarded chain traces ⇐ 旧叶 P6N 在 `U′ = U ∩ {R(t) ≤ M}`、
窗口 `[t − τ, t]` 上调用。 -/
theorem guardedChainTracesLeaf_C11KX : GuardedChainTracesLeaf_C11KX.{u} := by
  intro H hend s G hG t ht hts p T₀ records hcan hscale hacc Ctime qcan Dcap Dstar θ phi hphi a
    hTa hpinch hpinchG U hslabs hderG hDstar hDmodel y hnot Nc pc δc hpc0 hδc hchainc hchainUc
    Mc lamc hMc hlamc N pp δ M τ h0 hδ hUpp hch hb hMcM hq hM1 hτ0 hτt haτ hC h4 hD
  let U' : Set (H.stage (Fin.last H.eventCount)).Carrier :=
    {z | z ∈ U ∧ (G.closedPrefix t ht hts).flow.scalar t z ≤ M}
  have hgd : ∀ z ∈ U', ∀ v, v ≤ t → t - τ ≤ v →
      GuardKX_C11KX (G.flow.scalar t) qcan Ctime t v z :=
    fun z hz v hvt hv => guardKX_of_ceiling_C11KX Ctime.coe_nonneg hz.2 hq hvt hv hC
  have hvt : ∀ (j : Fin H.eventCount) (v : ℝ),
      v ∈ Ioo (H.time j.castSucc) (H.time j.succ) → v ≤ t :=
    fun j v hv => (hv.2.le.trans (H.time_strictMono.monotone (Fin.le_last _))).trans ht.le
  have hsub : Ici (t - τ) ⊆ Ici a := Ici_subset_Ici.mpr haτ
  exact RetainedCoreHistory.chain_traces_of_not_capWindowPoint_of_incomingSlab_late_P6N
    H hend G hG ht hts records hcan hscale hacc hphi (t - τ) (hTa.trans haτ)
    (fun j => RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinch j)
      (inter_subset_inter_right _ hsub))
    (RetainedCoreHistory.phiAlmostNonnegative_mono_P6N hpinchG (inter_subset_inter_right _ hsub))
    U'
    (fun j first hf z hz B v hv hav hqv =>
      hslabs j first hf z hz.1 B v hv (haτ.trans hav) hqv (hgd z hz v (hvt j v hv) hav))
    (fun z hz v hv hav hqv => hderG z hz.1 v hv (haτ.trans hav) hqv (hgd z hz v hv.2.le hav))
    hDstar hDmodel y hnot pc δc hpc0 hδc hchainc
    (fun k hk z hz => ⟨hchainUc k hk z hz, (hMc k hk z hz).trans hMcM⟩) hMc hlamc
    N pp δ M τ h0 hδ (fun k hk z hz => ⟨hUpp k hk z hz, hb k hk z hz⟩) hch hb hMcM hq hM1
    hτ0 hτt le_rfl hC h4 hD

/-- **叶 L1 证书（`_C11KX`，PROVED）**：guarded rebase chain ⇐ 旧叶 P6WB，窗口起点
`c′ := max c (T − τ)`（`τ := 1/(2(Ct + 1)Mc)`，`Mc := |Mb| + |q| + 1`，`Mb` = compact carrier 上
`R(T, ·)` 的上界）。 -/
theorem guardedRebaseLeaf_C11KX : GuardedRebaseLeaf_C11KX.{u} := by
  intro P a T A Cgrad Ct q hq U c hc hgradient y z r hyz hz hU
  have hTmem : T ∈ (RealTimeInterval.closed a T A.lt.le).carrier := by
    change T ∈ Icc a T
    exact ⟨A.lt.le, le_rfl⟩
  have h1 : Continuous (fun x : P.Carrier => ((T, x) : ℝ × P.Carrier)) :=
    continuous_const.prodMk continuous_id
  have h2 := A.equation.scalarCont.comp_continuous h1 (fun x => ⟨hTmem, mem_univ x⟩)
  obtain ⟨Mb, hMb⟩ := isCompact_univ.bddAbove_image h2.continuousOn
  have hMb' : ∀ x, A.flow.scalar T x ≤ Mb := fun x => hMb ⟨x, mem_univ x, rfl⟩
  have hMc : 0 < |Mb| + |q| + 1 := by positivity
  have hden : 0 < 2 * ((Ct : ℝ) + 1) * (|Mb| + |q| + 1) := by positivity
  obtain ⟨τ, hτ, hb⟩ : ∃ τ : ℝ, 0 < τ ∧ (Ct : ℝ) * (|Mb| + |q| + 1) * τ ≤ 1 / 2 := by
    refine ⟨1 / (2 * ((Ct : ℝ) + 1) * (|Mb| + |q| + 1)), by positivity, ?_⟩
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith [Ct.coe_nonneg]
  refine A.exists_rebase_chain_window_P6WB Cgrad hq U (max c (T - τ))
    (max_lt hc (by linarith)) ?_ y z hyz hz hU
  intro y' hy' t' ht' hct' hq' v
  have hR : A.flow.scalar T y' ≤ |Mb| + |q| + 1 := by
    have := le_abs_self Mb
    linarith [hMb' y', abs_nonneg q]
  have hqM : q ≤ |Mb| + |q| + 1 := by
    have := le_abs_self q
    linarith [abs_nonneg Mb]
  exact hgradient y' hy' t' ht' ((le_max_left _ _).trans hct') hq'
    (guardKX_of_ceiling_C11KX Ct.coe_nonneg hR hqM ht'.2.le ((le_max_right _ _).trans hct') hb) v

/-- **consumer（G2，PROVISIONAL[L3]）**：G1 壳的 L1 / L2 由本文件证书付清，只剩 TP 复合叶 L3。 -/
theorem shortSLT_guarded_of_TP_C11KX (hL3 : GuardedTPLeaf_C11KX.{u}) {θ : ℝ} (hθ : 0 < θ) :
    ShortSLTGuarded_C11KX.{u} θ :=
  shortSLT_guarded_of_leaves_C11KX guardedRebaseLeaf_C11KX guardedChainTracesLeaf_C11KX hL3 hθ

/-- consumer：L3 ⇒ K-SW（`0 < θ₀ ≤ 1/2`），只剩 L3。 -/
example (hL3 : GuardedTPLeaf_C11KX.{u}) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2) :
    KSW_C11KS.{u} θ₀ :=
  ksw_of_shortSLT_C11KS hθ₀ hθ₀2
    (ShortSLTGuarded_C11KX.toShortSLT (shortSLT_guarded_of_TP_C11KX hL3 hθ₀))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
