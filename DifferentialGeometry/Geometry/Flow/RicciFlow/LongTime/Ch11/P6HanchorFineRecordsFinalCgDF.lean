import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HanchorHPNFrameFinalCgDF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HanchorFineRecordsFinalG9S

/-!
# final 版 hPN 帧 `hanchor0`，K 帧 records 内付：Cg 参数化（DRVFINAL，`_DF`）

G9SHIFT `hanchor0_hPN_frame_final_RU` 的孪生：底座换
`hanchor0_hPN_frame_final_G9S_Cg_DF`，hgood `4` → `Cg`。证明同。**无新 binder**。
生成器 `build-logs/scratch/DRVFINAL/gen/g6.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **final 版 hPN 帧 `hanchor0`，K 帧 records 内部化（`_G9S`，PROVISIONAL[`hsupA`、`hder`、`hsepρ`（粗
records 改述）、`records / hfine`（SCRS⁺ 投影）、`hpinchK0`、`hpinchF`]）**：RECUP `hanchor0_hPN_frame_RU` 的
final 换帧（反证 + 子列取第 `l` 档细 records；final 帧只用 events 的 records，`htl htK hpinchF` 随子列复合）。 -/
theorem hanchor0_hPN_frame_final_RU_Cg_DF {Cg : ℝ} (hCg : 2 ≤ Cg)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hεcone : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (T₀o : ℕ → ℝ)
    (hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    {A : ℝ} (hA : 1 < A) (ind : ℕ → ℕ) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ (2 : ℕ) < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ (2 : ℕ)
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (pow_pos (hr k) 2)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k =>
      (Ho k).rescaleTime_P6X (pow_pos (hr k) 2) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (pow_pos (hr k) 2) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀o k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
      Tendsto L atTop atTop →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
        ∀ z : ((Kh k).stageAt v).Carrier,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
              ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k))
                  ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (L k / Real.sqrt (R k)) →
          Cg * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
          (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (pow_pos (hr k) 2)).neckRadius (Tn k) ^ (2 : ℕ))⁻¹) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
    ∀ (_hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi)
      (htl : ∀ k, (K k).time (Fin.last (K k).eventCount) < (σ k : ℝ))
      (htK : ∀ k, (σ k : ℝ) < (K k).horizon)
      (_hpinchF : ∀ k, Perelman.PhiAlmostNonnegative
        (((K k).finalSlab ((htl k).trans (htK k))).restrictIncoming le_rfl
          ((htl k).trans (htK k)) le_rfl).flow
        (Ico ((K k).time (Fin.last (K k).eventCount)) (K k).horizon ∩
          Ici ((Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi)
      (_hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
          (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K
              n).eventCount) →
          ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
            (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * ((((records (ind n) i).rescale_P6M (c n)
              (pow_pos (hr n) 2)).static b).neck.scale)⁻¹) →
          ((n : ℝ) + 1) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (pow_pos (hr n) 2)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
            (((records (ind n) i).rescale_P6M (c n) (pow_pos (hr n) 2)).static b).neck.scale),
      ∀ A' : ℝ, 0 < A' → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A' / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n := by
  intro Ho Tno pTo r hr hNT htime hsmallo hvolo c K Kh Tn pT aSeed haT hclock ha1 hsmallK hT₀o
    seedTrace σ y R hsT has L hRdef hRpos hRle hL hgood hwin hwinF hceil hyball hgate
    hpinchK0 htl htK hpinchF hsepρ A' hA'
  have hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
  -- 第 `l` 档细窗口：`(D, ζ, m) = (l + 1, 1/(l + 1), l + 2)`
  choose T₀f hT₀f using fun l : ℕ =>
    hfine ((l : ℝ) + 1) (1 / ((l : ℝ) + 1)) (l + 2) (by positivity)
  choose pf hradf haccf hordf recf hcanf hscf using hT₀f
  -- K 帧晚窗落在第 `l` 档阈值之后（`k ≥ ⌈2 T₀(l)⌉`）
  have hlate : ∀ (l k : ℕ), ⌈2 * T₀f l⌉₊ ≤ k → ∀ i : Fin (K k).eventCount,
      (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K k).time i.succ →
      T₀f l ≤ (F.tower.history (ind k)).time i.succ := by
    intro l k hk i hi
    have hk' : 2 * T₀f l ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have hTn : c k * (Tn k : ℝ) = (Tno k : ℝ) := (Ho k).mul_rescaleTime_P6X (hc k) (Tno k)
    have htk : (K k).time i.succ = (F.tower.history (ind k)).time i.succ / c k := rfl
    rw [htk, le_div_iff₀ (hc k)] at hi
    have h4 : ((Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) * c k = (Tno k : ℝ) - c k / 2 := by
      rw [← hTn]
      ring
    have h1 := hNT k
    have h2 := htime k
    have h3 : c k = r k ^ (2 : ℕ) := rfl
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [h4] at hi
    linarith
  by_contra hneg
  have hfreq : ∀ Q : ℝ, 2 ≤ Q → ∃ᶠ n in atTop,
      ¬ ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A' / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n :=
    fun Q hQ => Filter.not_eventually.mp fun h => hneg ⟨Q, hQ, h⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_frequently (P := fun l k =>
      ⌈2 * T₀f l⌉₊ ≤ k ∧
      ¬ ∀ z ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)
          (A' / Real.sqrt (R k)),
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) z ≤
          ((l : ℝ) + 2) * R k) fun l =>
    ((hfreq ((l : ℝ) + 2) (by have := (Nat.cast_nonneg l : (0 : ℝ) ≤ l); linarith)).and_eventually
      (eventually_ge_atTop ⌈2 * T₀f l⌉₊)).mono fun k hk => ⟨hk.2, hk.1⟩
  have hφle : ∀ l, l ≤ φ l := hφ.id_le
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφ1 : ∀ l : ℕ, (l : ℝ) + 1 ≤ (φ l : ℝ) + 1 := fun l => by
    have := (Nat.cast_le (α := ℝ)).mpr (hφle l)
    linarith
  -- 细 / 粗 neck scale（重标度后）相等
  have hsc : ∀ (l : ℕ) (i : Fin (K (φ l)).eventCount)
      (h' : T₀f l ≤ (F.tower.history (ind (φ l))).time i.succ)
      (b : ((K (φ l)).toHistory.event i).RetainedBoundaryIndex),
      (((recf l (ind (φ l)) i h').rescale_P6M (c (φ l)) (hc (φ l))).static b).neck.scale =
        (((records (ind (φ l)) i).rescale_P6M (c (φ l)) (hc (φ l))).static b).neck.scale := by
    intro l i h' b
    have e1 := ((recf l (ind (φ l)) i h').static b).rescale_P6M_scale (c (φ l)) (hc (φ l))
    have e2 := ((records (ind (φ l)) i).static b).rescale_P6M_scale (c (φ l)) (hc (φ l))
    rw [hscf l (ind (φ l)) i h' b] at e1
    exact e1.trans e2.symm
  have hG := hanchor0_hPN_frame_final_G9S_Cg_DF hCg hεcone hC2 hanti hder
    (fun l => T₀o (φ l)) hsupA hphi hθ₀
    records hA (fun l => ind (φ l)) (fun l => Tno (φ l)) (fun l => pTo (φ l)) (fun l => r (φ l))
    (fun l => hr (φ l)) (fun l => (hφ1 l).trans (hNT (φ l))) (fun l => htime (φ l))
    (fun l => hsmallo (φ l)) (fun l => hvolo (φ l)) (fun l => aSeed (φ l)) (fun l => haT (φ l))
    (fun l => hclock (φ l)) (fun l => ha1 (φ l)) (fun l => hsmallK (φ l))
    (fun l => hT₀o (φ l)) (fun l => seedTrace (φ l)) (fun l => σ (φ l)) (fun l => y (φ l))
    (fun l => R (φ l)) (fun l => hsT (φ l)) (fun l => has (φ l)) (fun l => L (φ l))
    (fun l => hRdef (φ l)) (fun l => hRpos (φ l)) (fun l => (hφ1 l).trans (hRle (φ l)))
    (hL.comp hφt) (fun l => hgood (φ l)) (fun T hT => hφt.eventually (hwin T hT))
    (fun T hT => hφt.eventually (hwinF T hT)) (fun l => hceil (φ l)) (fun l => hyball (φ l))
    (hφt.eventually hgate)
    (fun l => (pf l (ind (φ l))).rescale_P6N (c (φ l)) (hc (φ l)))
    (fun l i hi => (recf l (ind (φ l)) i (hlate l (φ l) (hφP l).1 i hi)).rescale_P6M (c (φ l))
      (hc (φ l)))
    (fun l i hi b => ((recf l (ind (φ l)) i (hlate l (φ l) (hφP l).1 i hi)).static
      b).hasCanonicalWindow_rescale_P6M (hcanf l (ind (φ l)) i _ b) _ _)
    (Filter.Eventually.of_forall fun l => haccf l (ind (φ l)))
    (Filter.Eventually.of_forall fun l => hradf l (ind (φ l)))
    (Filter.Eventually.of_forall fun l => hordf l (ind (φ l)))
    (fun l i => hpinchK0 (φ l) i) (fun l => htl (φ l)) (fun l => htK (φ l))
    (fun l => hpinchF (φ l))
    (fun B hB => (hφt.eventually (hsepρ B hB)).mono fun l hl i hi b hle hcond => by
      have e := hsc l i (hlate l (φ l) (hφP l).1 i hi) b
      have hcond' := hcond.imp_right fun h => h.trans_eq (congrArg (fun s => θ₀ * s⁻¹) e)
      have h := hl i hi b hle hcond'
      have h0 : (0 : ℝ) ≤ (l : ℝ) + 1 := by positivity
      exact (le_trans (mul_le_mul (hφ1 l) (max_le_max (hφ1 l) le_rfl)
        (h0.trans (le_max_left _ _)) (h0.trans (hφ1 l))) h).trans_eq e.symm)
  obtain ⟨Q₀, -, hev⟩ := hG A' hA'
  obtain ⟨l, hl1, hl2⟩ := (hev.and (eventually_ge_atTop ⌈Q₀⌉₊)).exists
  apply (hφP l).2
  intro z hz
  refine (hl1 z hz).trans ?_
  have h2 : ((⌈Q₀⌉₊ : ℕ) : ℝ) ≤ (l : ℝ) + 2 := by exact_mod_cast (show ⌈Q₀⌉₊ ≤ l + 2 by omega)
  exact mul_le_mul_of_nonneg_right ((Nat.le_ceil Q₀).trans h2) (hRpos (φ l)).le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
