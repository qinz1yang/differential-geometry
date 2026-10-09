import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResE4ThMJ

/-!
# MJ G3 观察：θ₀ 尾合取亦可由引擎数据供给（DT 行，后缀 `_MJ`）

θ₀ 尾合取（`hsepρ`）要求：`K` 帧时刻 `≥ Tn − 1/2` 的事件，粗 records（`rescale_P6M`）满足
`(n+1)·max (n+1) (ρ̃(Tn)²)⁻¹ ≤ scale`。这些事件的 Ho 帧时刻 `≥ c·(Tn − 1/2) ≥ c·aSeed`，故落在 T0K 供给的
Ho cutoff `c·aSeed` 之内，由 `birthN_aSeed_T0K`（`Nf := n+1`）直接给出（`θ₀ := 1`，析取前提不用）。
`drvResE4_DT_Th_of_engine_MJ`（PROVED 相对 `hrcs`、`hanti`、`hδq` 与阈值 `recentThrN_HNS (n+1)` /
`lateLambdaThr_P6HA ≤ T₀`）：`DrvResE4_DT_Th_MJ` 本身可由引擎数据证出。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory (DepthExtendable)

/-- **θ₀ 尾核由引擎数据证出（DT 行，`_MJ`，PROVED）**。 -/
theorem drvResE4_DT_Th_of_engine_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    DrvResE4_DT_Th_MJ F q records ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  refine ⟨1, one_pos, ?_⟩
  intro j hjt htj B hB
  refine Filter.Eventually.of_forall ?_
  intro n i hi b _ _
  have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
    have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
    rw [this]; field_simp [(hc k).ne']
  have hTno0 : ∀ k, 0 ≤ (Tno k : ℝ) := fun k => (Tno k).2.1
  have h2c : ∀ k, 2 * c k < (Tno k : ℝ) := fun k => h2r k
  have hρK : ∀ k, ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹ =
      c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [hTno k]; exact RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q (Tn k : ℝ)
  have hcn := hc n
  have hR' : R n ≤ c n * (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := by
    rw [← hρK n]; exact hRρ n
  have habs : ((n : ℝ) + 1) / c n ≤ (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := by
    rw [div_le_iff₀ hcn, mul_comm]
    exact (hRr n).trans hR'
  have hhi : max 1 (c n * (aSeed n : ℝ) / c n) ≤
      ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ := by
    rw [t0K_eq_aSeed_T0K hcn (h1 n)]
    have := hclock n
    linarith
  have key := (F.tower.history (ind n)).hscaleK_rescale_P6X3 (hc n)
    (fun i' _ => records (ind n) i') (T₀ := c n * (aSeed n : ℝ))
    (A := (n : ℝ) + 1) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹)
    (fun i' hi' b' => by
      rw [max_eq_right habs]
      have hb := birthN_aSeed_T0K records hrcs hanti hδq ind (fun m : ℕ => (m : ℝ) + 1)
        (T₀ := T₀) (c := c) (aS := fun k => (aSeed k : ℝ)) (Tn := fun k => (Tn k : ℝ))
        (Tno := fun k => (Tno k : ℝ)) hTr hΛ hlate hc hTno hTno0 h2c hclock n i' hi' b'
      simpa only [max_self] using hb) i hhi b
  rw [hρK n]
  exact key


/-- **θ₀ 尾核由引擎数据证出（DT × Cg 行，`_MJ`，PROVED）**：证明与 DT 行逐字（前提段只差 `hsel` / `hgood` 常数，
本合取都不用）。 -/
theorem drvResE4_DT_Cg_Th_of_engine_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    DrvResE4_DT_Cg_Th_MJ F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  refine ⟨1, one_pos, ?_⟩
  intro j hjt htj B hB
  refine Filter.Eventually.of_forall ?_
  intro n i hi b _ _
  have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
    have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
    rw [this]; field_simp [(hc k).ne']
  have hTno0 : ∀ k, 0 ≤ (Tno k : ℝ) := fun k => (Tno k).2.1
  have h2c : ∀ k, 2 * c k < (Tno k : ℝ) := fun k => h2r k
  have hρK : ∀ k, ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹ =
      c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [hTno k]; exact RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q (Tn k : ℝ)
  have hcn := hc n
  have hR' : R n ≤ c n * (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := by
    rw [← hρK n]; exact hRρ n
  have habs : ((n : ℝ) + 1) / c n ≤ (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := by
    rw [div_le_iff₀ hcn, mul_comm]
    exact (hRr n).trans hR'
  have hhi : max 1 (c n * (aSeed n : ℝ) / c n) ≤
      ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ := by
    rw [t0K_eq_aSeed_T0K hcn (h1 n)]
    have := hclock n
    linarith
  have key := (F.tower.history (ind n)).hscaleK_rescale_P6X3 (hc n)
    (fun i' _ => records (ind n) i') (T₀ := c n * (aSeed n : ℝ))
    (A := (n : ℝ) + 1) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹)
    (fun i' hi' b' => by
      rw [max_eq_right habs]
      have hb := birthN_aSeed_T0K records hrcs hanti hδq ind (fun m : ℕ => (m : ℝ) + 1)
        (T₀ := T₀) (c := c) (aS := fun k => (aSeed k : ℝ)) (Tn := fun k => (Tn k : ℝ))
        (Tno := fun k => (Tno k : ℝ)) hTr hΛ hlate hc hTno hTno0 h2c hclock n i' hi' b'
      simpa only [max_self] using hb) i hhi b
  rw [hρK n]
  exact key

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
