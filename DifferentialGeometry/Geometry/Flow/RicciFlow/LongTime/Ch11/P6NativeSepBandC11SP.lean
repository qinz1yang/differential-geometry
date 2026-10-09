import DifferentialGeometry.Geometry.Metric.ChartDistance.FirstExit
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeSepScaleC11SP

/-!
# O-CH11-NATIVE-SEP G3：`hSEP` chart-reach 的 neck band 出口长度 M2（后缀 `_C11SP`，无 binder）

* `mem_band_of_riemannianEDistOf_lt_C11SP`（一般形）：光滑嵌入 `c : neckBuffer δ → M`、高度
  `Z = chartHeight_NK c`；若在 band `{p ∈ range c | |Z p| ≤ L}`（`L ≤ δ⁻¹`）上 `(dZ v)² ≤ K²·g(v,v)`，则从
  `c w₀`（`|w₀.1.2| ≤ h₀ < L`）出发 `g`-距离 `< (L − h₀)/K` 的点都在 `range c` 里且 `|Z| < L`。
  证明照 `ChartDistance/FirstExit` 的 `mem_chart_ball_of_riemannianEDistOf_lt`：近最短曲线
  （`exists_lt_of_riemannianEDist_lt`）+ 首次出口（`exists_first_exit_frontier_of_not_mem_interior`；band 闭性
  由 `closure_height_set_chart_NK2`）+ `edist_comp_le_riemannianCurveELength_of_bound_on_path`。
* `GeometricCutoffRecord.mem_backwardNeck_range_of_dist_lt_C11SP`（record 形）：`e₂` 的 backward neck
  `G₂.backward α` 在 stage `e₁.succ`（度量 `(H.event e₁).outputMetric`，`T(e₁⁺)`）的 chart：`K = √2/r_α`
  （`band_cyl_NK` 的 `(dz)² ≤ 2ĝ`，`ĝ = r⁻²·c^*g`），`L = δ⁻¹`。
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Set MeasureTheory Manifold DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Band

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **M2 一般形（PROVED）**：neck band 首次出口长度。 -/
theorem mem_band_of_riemannianEDistOf_lt_C11SP (g : SmoothRiemannianMetric ThreeModel M)
    {δ : ℝ} {c : neckBuffer δ → M} (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c)
    {L : ℝ} (hL : L ≤ δ⁻¹) {K : ℝ≥0} (hK : 0 < K)
    (hdz : ∀ p ∈ Set.range c, |chartHeight_NK c p| ≤ L → ∀ v : TangentSpace ThreeModel p,
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) p v) ^ 2 ≤
        (K : ℝ) ^ 2 * g.inner p v v)
    (w₀ : neckBuffer δ) {h₀ : ℝ} (hh₀ : |w₀.1.2| ≤ h₀) (hh₀L : h₀ < L)
    {q : M} (hq : riemannianEDistOf g (c w₀) q < ENNReal.ofReal (L - h₀) / K) :
    q ∈ Set.range c ∧ |chartHeight_NK c q| < L := by
  let : RiemannianBundle (TangentSpace ThreeModel : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hq
  have hC0 : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hshort : (K : ℝ≥0∞) * riemannianCurveELength g γ 0 1 < ENNReal.ofReal (L - h₀) := by
    rw [riemannianCurveELength_eq_pathELength]
    have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hC0) (Or.inl ENNReal.coe_ne_top)).mp hlen
    simpa only [mul_comm] using h
  have hinj := hc.isEmbedding.injective
  have hopen : IsOpen (Set.range c) := isOpen_range_chart_of_embedding_NK hc
  have hZ : ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (chartHeight_NK c) (Set.range c) :=
    contMDiffOn_chartHeight_NK hc
  set Z := chartHeight_NK c with hZdef
  let U : Set M := Set.range c ∩ Z ⁻¹' {z : ℝ | |z| < L}
  let Kset : Set M := {p : M | p ∈ Set.range c ∧ Z p ∈ Icc (-L) L}
  have hUo : IsOpen U :=
    hZ.continuousOn.isOpen_inter_preimage hopen (isOpen_lt continuous_abs continuous_const)
  have hKcl : closure Kset ⊆ Set.range c :=
    closure_height_set_chart_NK2 hc (fun z hz => (abs_le.mpr hz).trans hL)
  have hKclosed : IsClosed Kset := by
    refine closure_subset_iff_isClosed.mp ?_
    intro p hp
    have hpc := hKcl hp
    have hcont : ContinuousAt Z p := hZ.continuousOn.continuousAt (hopen.mem_nhds hpc)
    have himg := mem_closure_image hcont hp
    have hsub : Z '' Kset ⊆ Icc (-L) L := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    exact ⟨hpc, closure_minimal hsub isClosed_Icc himg⟩
  have hUK : U ⊆ Kset := fun p hp => ⟨hp.1, abs_le.mp (le_of_lt hp.2)⟩
  have hZ0 : |Z (γ 0)| ≤ h₀ := by
    rw [hγ0, hZdef, chartHeight_chart_NK hinj]
    exact hh₀
  have h0 : γ 0 ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [hγ0]
      exact ⟨w₀, rfl⟩
    · change |Z (γ 0)| < L
      linarith
  suffices h1 : γ 1 ∈ U by
    rw [hγ1] at h1
    exact ⟨h1.1, h1.2⟩
  by_contra h1U
  obtain ⟨t, ht, hbefore, hfront⟩ :=
    DifferentialGeometry.exists_first_exit_frontier_of_not_mem_interior zero_lt_one
      hγ.continuousOn (hUo.interior_eq ▸ h0) (by simpa only [hUo.interior_eq] using h1U)
  have hbeforeU : ∀ s ∈ Ico (0 : ℝ) t, γ s ∈ U := by
    simpa only [hUo.interior_eq] using hbefore
  have htK : γ t ∈ Kset := closure_minimal hUK hKclosed (frontier_subset_closure hfront)
  have htNot : γ t ∉ U := by
    simpa only [hUo.interior_eq] using hfront.2
  have hZt : L ≤ |Z (γ t)| := le_of_not_gt (fun hlt => htNot ⟨htK.1, hlt⟩)
  have hmaps : MapsTo γ (Icc 0 t) (Set.range c) := by
    intro s hs
    by_cases hst : s = t
    · rw [hst]
      exact htK.1
    · exact (hbeforeU s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩).1
  have hbound : ∀ s ∈ Ioo (0 : ℝ) t, ∀ v : TangentSpace ThreeModel (γ s),
      ‖(mfderiv ThreeModel 𝓘(ℝ, ℝ) Z (γ s) v : ℝ)‖ ≤ (K : ℝ) * Real.sqrt (g.inner (γ s) v v) := by
    intro s hs v
    have hsU := hbeforeU s ⟨hs.1.le, hs.2⟩
    have hsq := hdz (γ s) hsU.1 (le_of_lt hsU.2) v
    have hg : 0 ≤ g.inner (γ s) v v := metric_inner_self_nonneg g _ v
    change ‖(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z (γ s) v)‖ ≤ _
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z (γ s) v) ^ 2)
        ≤ Real.sqrt ((K : ℝ) ^ 2 * g.inner (γ s) v v) := Real.sqrt_le_sqrt hsq
      _ = (K : ℝ) * Real.sqrt (g.inner (γ s) v v) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (NNReal.coe_nonneg K)]
  have hdisp := DifferentialGeometry.Geometry.edist_comp_le_riemannianCurveELength_of_bound_on_path
    g hopen (hZ.of_le (by norm_num)) ht.1.le (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hmaps hbound
  have hge : ENNReal.ofReal (L - h₀) ≤ edist (Z (γ 0)) (Z (γ t)) := by
    rw [edist_dist, Real.dist_eq]
    apply ENNReal.ofReal_le_ofReal
    have := abs_sub_abs_le_abs_sub (Z (γ t)) (Z (γ 0))
    rw [abs_sub_comm] at this
    linarith
  have hlen' : riemannianCurveELength g γ 0 t ≤ riemannianCurveELength g γ 0 1 :=
    lintegral_mono' (Measure.restrict_mono_set volume (Icc_subset_Icc le_rfl ht.2))
      (fun _ => le_rfl)
  exact (not_lt_of_ge ((hge.trans hdisp).trans (mul_le_mul_right hlen' _))) hshort

end Band

namespace GeometricCutoffRecord

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **M2 record 形（PROVED）**：`e₂` 的 backward neck（record neck `α`，nominal radius `r`）在 stage
`e₁.succ`（`T(e₁⁺)`，度量 `(H.event e₁).outputMetric`）的 chart：从 chart 点 `w₀`（`|w₀.1.2| ≤ h₀ < δ⁻¹`）
出发 output 距离 `< (δ⁻¹ − h₀)·r/√2` 的点都在该 chart 的像里（`0 < T(e₂⁺) − T(e₁⁺) ≤ r²/2`，
`δ ≤ 1/40000`）。 -/
theorem mem_backwardNeck_range_of_dist_lt_C11SP {H : ObservedHistory.{u}}
    {parameters : CutoffParameters} {e₁ e₂ : Fin H.eventCount}
    (G₂ : GeometricCutoffRecord H e₂ parameters) (α : (H.event e₂).transition.trace.tubes.Index)
    (hδ : G₂.delta α ≤ 1 / 40000) (hji : e₁.val < e₂.val) (hlt : H.time e₁.succ < H.time e₂.succ)
    (hhalf : H.time e₂.succ - H.time e₁.succ ≤ (G₂.nominalRadius ⟨α⟩) ^ 2 / 2)
    (hn : H.time e₂.succ - (G₂.nominalRadius ⟨α⟩) ^ 2 <
      H.time (⟨e₁.val + 1, by omega⟩ : Fin H.eventCount).succ)
    (w₀ : neckBuffer (G₂.delta α)) {h₀ : ℝ} (hh₀ : |w₀.1.2| ≤ h₀) (hh₀L : h₀ < (G₂.delta α)⁻¹)
    {q : (H.stage e₁.succ).Carrier}
    (hq : riemannianEDistOf (H.event e₁).outputMetric
        ((G₂.backward α).stageChart ⟨e₁.val + 1, by omega⟩
          (by change e₁.val + 1 ≤ e₂.val; omega) hn w₀) q <
      ENNReal.ofReal (((G₂.delta α)⁻¹ - h₀) * G₂.nominalRadius ⟨α⟩ / Real.sqrt 2)) :
    q ∈ Set.range ((G₂.backward α).stageChart ⟨e₁.val + 1, by omega⟩
      (by change e₁.val + 1 ≤ e₂.val; omega) hn) := by
  set r := G₂.nominalRadius ⟨α⟩ with hrdef
  have hr : 0 < r := G₂.nominal_pos ⟨α⟩
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  set B := G₂.backward α with hBdef
  let nx : Fin H.eventCount := ⟨e₁.val + 1, by omega⟩
  have hnx : nx.val ≤ e₂.val := by
    change e₁.val + 1 ≤ e₂.val
    omega
  set v : ℝ := (H.time e₁.succ - H.time e₂.succ) / r ^ 2 with hvdef
  have hv0 : v < 0 := div_neg_of_neg_of_pos (by linarith) hr2
  have hvhalf : -1 / 2 ≤ v := by
    rw [hvdef, le_div_iff₀ hr2]
    linarith
  have hsv : H.time e₂.succ + r ^ 2 * v = H.time e₁.succ := by
    have : r ^ 2 * v = H.time e₁.succ - H.time e₂.succ := by
      rw [hvdef, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hr2.ne'
    linarith
  have hstart : H.time nx.castSucc ≤ H.time e₂.succ + r ^ 2 * v := by
    rw [hsv]
    exact le_rfl
  have hend : H.time e₂.succ + r ^ 2 * v < H.time nx.succ := by
    rw [hsv]
    exact H.time_strictMono (Fin.castSucc_lt_succ (i := nx))
  have hslab := B.metric_on_slab nx hnx hn v ⟨by linarith, hv0⟩ hstart hend
  have hgs : (H.event nx).incoming.flow.base.metric (H.time e₁.succ) =
      (H.event e₁).outputMetric := by
    change (H.event nx).incoming.flow.base.metric (H.time nx.castSucc) = _
    rw [H.event_initial nx, H.event_output e₁]
    rfl
  let gm := scaleMetric (r ^ 2)⁻¹ (inv_pos.mpr hr2) (H.event e₁).outputMetric
  have hband := chart_band_estimates_wide_NK2 (B.stageChart_smooth nx hnx hn) gm (B.metric v)
    (a := 3 / 5) (C := 2) (T := Icc (-(G₂.delta α)⁻¹) (G₂.delta α)⁻¹) (by
      intro z V W
      change _ = (scaleMetric _ _ _).inner _ _ _
      rw [scaleMetric_inner, hslab z V W, hsv, hgs])
    (fun z hz => (B.band_cyl_NK (G₂.two_le_order_NK α) hδ v ⟨hvhalf, hv0.le⟩ z hz).1)
    (fun z hz => (B.band_cyl_NK (G₂.two_le_order_NK α) hδ v ⟨hvhalf, hv0.le⟩ z hz).2)
  let K : ℝ≥0 := ⟨Real.sqrt 2 / r, by positivity⟩
  have hK : 0 < K := by
    change (0 : ℝ) < Real.sqrt 2 / r
    positivity
  have hKsq : (K : ℝ) ^ 2 = 2 * (r ^ 2)⁻¹ := by
    change (Real.sqrt 2 / r) ^ 2 = _
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
  have hdz : ∀ p ∈ Set.range (B.stageChart nx hnx hn),
      |chartHeight_NK (B.stageChart nx hnx hn) p| ≤ (G₂.delta α)⁻¹ →
      ∀ w : TangentSpace ThreeModel p,
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK (B.stageChart nx hnx hn)) p w) ^ 2 ≤
        (K : ℝ) ^ 2 * (H.event e₁).outputMetric.inner p w w := by
    intro p hp hZp w
    have h := hband.2 p hp (abs_le.mp hZp) w
    rw [hKsq]
    change _ ≤ 2 * ((r ^ 2)⁻¹ * (H.event e₁).outputMetric.inner p w w) at h
    linarith
  have hthr : ENNReal.ofReal (((G₂.delta α)⁻¹ - h₀) * r / Real.sqrt 2) =
      ENNReal.ofReal ((G₂.delta α)⁻¹ - h₀) / K := by
    have hKr : ((K : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt 2 / r) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      rfl
    rw [hKr, ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  rw [hthr] at hq
  exact (mem_band_of_riemannianEDistOf_lt_C11SP (H.event e₁).outputMetric
    (B.stageChart_smooth nx hnx hn) le_rfl hK hdz w₀ hh₀ hh₀L hq).1

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
