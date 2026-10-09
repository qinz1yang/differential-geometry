import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EndpointSemicontinuity
import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.CompleteMinimizerGM

/-!
# 单时钟加权极小的可达性（O-CH11-KAPPA2 G1，K3 空间逃逸子句，后缀 `_C11Q2`）

树内 `physicalWeightedCost_minima_on_half_clock_of_cutoff_records`
（`PhysicalWeightedStageAttainmentPortC11P:283`）要切片时刻 `T − w²` 落在**同一 stage 的开时段**
（`hclock`，单 slab），所以在 event 时刻的切片（新 stage 的出生时刻）不适用。这里对**固定时钟 `v`**
重证可达性：只用
* `q ↦ regularizedCost(q)` 下半连续（`lowerSemicontinuous_regularizedCost`，无 `hclock`）；
* 固定切片度量下 `q ↦ d(O, q)` 连续（`continuous_riemannianEDistOf_GM`）；
* `φ = SingularBarrier.value` 在截断边界爆破 + 近期标量地板 `Bsharp` 给的正下界
  `2vL + 2rv ≥ 2v(r − (2Bsharp/3)v³) > 0`；
* stage carrier 紧。
证明骨架逐段取自上面树内定理的 private 引理（把 `Icc a b × carrier` 换成 `carrier`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- 正系数仿射映射保持下半连续（`PhysicalWeightedSemicontinuityPortC11P` 里同名 private 引理的
公开副本，证明逐字）。 -/
theorem lowerSemicontinuous_positive_affine_map_C11Q2
    {X : Type*} [TopologicalSpace X]
    (f : X → WithTop ℝ) (hf : LowerSemicontinuous f)
    (c d : X → ℝ) (hc : Continuous c) (hd : Continuous d) (hcpos : ∀ x, 0 < c x) :
    LowerSemicontinuous (fun x => WithTop.map (fun y : ℝ => c x * y + d x) (f x)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro bound
  cases bound using WithTop.recTopCoe with
  | top => simpa only [Iic_top, preimage_univ] using isClosed_univ
  | coe bound =>
    have hepi : IsClosed {z : X × WithTop ℝ | f z.1 ≤ z.2} :=
      lowerSemicontinuous_iff_isClosed_epigraph.mp hf
    have hbound : Continuous (fun x => (bound - d x) / c x) :=
      (continuous_const.sub hd).div hc (fun x => (hcpos x).ne')
    convert hepi.preimage (continuous_id.prodMk (WithTop.continuous_coe.comp hbound)) using 1
    ext x
    change WithTop.map (fun y : ℝ => c x * y + d x) (f x) ≤ (bound : WithTop ℝ) ↔
      f x ≤ (((bound - d x) / c x : ℝ) : WithTop ℝ)
    cases f x using WithTop.recTopCoe with
    | top => simp only [WithTop.map_top, WithTop.not_top_le_coe]
    | coe y =>
      simp only [WithTop.map_coe, WithTop.coe_le_coe]
      rw [le_div_iff₀ (hcpos x)]
      constructor <;> intro h <;> nlinarith only [h]

/-- **单时钟可达性**：固定时钟 `v > 0`，加权 cutoff 函数
`q ↦ physicalWeightedCost … v x O q` 的下确界被某点达到（含 event 时刻切片；`B` 为作用量截断地板，
`Bsharp` 为真实的近期标量地板，`(2Bsharp/3)v³ < r`）。 -/
theorem physicalWeightedCost_exists_min_at_clock_C11Q2
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B Bsharp r A v : ℝ) (hr : 0 < r) (hv : 0 < v)
    (hroom : (2 * Bsharp / 3) * v ^ 3 < r)
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ y : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (hsharp : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ y : (H.stage j.val).Carrier,
        -Bsharp ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (x : (H.stage last).Carrier) (O : (H.stage first).Carrier) :
    ∃ q : (H.stage first).Carrier,
      sInf (Set.range (H.physicalWeightedCost first last hle T B r A v x O)) =
        H.physicalWeightedCost first last hle T B r A v x O q := by
  classical
  let X := (H.stage first).Carrier
  let cost : X → WithTop ℝ := fun z => H.regularizedCost first last hle T B 0 v x z
  let dist : X → ENNReal := fun z => riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O z
  let shift : ℝ := A * (1 - 2 * v ^ 2 / r ^ 2)
  let arg : X → ℝ := fun z => (dist z).toReal / r - shift
  let phi := DifferentialGeometry.Analysis.SingularBarrier.value
  let W : X → WithTop ℝ := fun z => H.physicalWeightedCost first last hle T B r A v x O z
  let κ : ℝ := r - (2 * Bsharp / 3) * v ^ 3
  have hκ : 0 < κ := sub_pos.mpr hroom
  have hρ : 0 < 2 * v * κ := by positivity
  have hdist : Continuous dist :=
    DifferentialGeometry.Geometry.continuous_riemannianEDistOf_GM _ O
  have hupper' : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hupper
  have hcost : LowerSemicontinuous cost :=
    H.lowerSemicontinuous_regularizedCost first last hle T B 0 v hupper' hscalar x
  have hcostfloor (z : X) : ((-(2 * Bsharp / 3) * v ^ 3 : ℝ) : WithTop ℝ) ≤ cost z := by
    dsimp only [cost]
    rw [H.regularizedCost_congr_scalar_lower_bound first last hle T B Bsharp 0 v
      hscalar hsharp x z]
    simpa only [zero_pow (by decide : 3 ≠ 0), sub_zero] using
      H.regularizedCost_ge first last hle T Bsharp 0 v x z
  have hshifted (z : X) (L : ℝ) (hL : cost z = (L : WithTop ℝ)) :
      2 * v * κ ≤ 2 * v * L + 2 * r * v := by
    have hl := hcostfloor z
    rw [hL] at hl
    have hl' := WithTop.coe_le_coe.mp hl
    have hLr : κ ≤ L + r := by dsimp only [κ]; linarith
    nlinarith
  have hargInside (z : X) (hz : dist z < ENNReal.ofReal (r * (shift + 1 / 10))) :
      arg z < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hz
    dsimp only [arg]
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    nlinarith
  have hWformula (z : X) (hz : dist z < ENNReal.ofReal (r * (shift + 1 / 10))) :
      W z = WithTop.map (fun L : ℝ => phi (arg z) * (2 * v * L + 2 * r * v)) (cost z) := by
    simp only [W, physicalWeightedCost, cost, phi, arg, dist, shift, ite_eq_left hz]
  have hnonneg (z : X) : (0 : WithTop ℝ) ≤ W z := by
    by_cases hz : dist z < ENNReal.ofReal (r * (shift + 1 / 10))
    · rw [hWformula z hz]
      cases hL : cost z using WithTop.recTopCoe with
      | top => simp only [WithTop.map_top]; exact le_top
      | coe L =>
        have hZ := hshifted z L hL
        have hp := DifferentialGeometry.Analysis.SingularBarrier.pos (hargInside z hz)
        simp only [WithTop.map_coe]
        exact WithTop.coe_le_coe.mpr (mul_nonneg hp.le (hρ.le.trans hZ))
    · simp only [W, physicalWeightedCost, dist, shift, ite_eq_right hz]
      exact le_top
  have hcompact (bound : ℝ) : IsCompact {z : X | W z ≤ (bound : WithTop ℝ)} := by
    obtain ⟨θ, hθ, hphiθ⟩ : ∃ θ : ℝ, θ < 1 / 10 ∧ bound / (2 * v * κ) < phi θ := by
      have he := (DifferentialGeometry.Analysis.SingularBarrier.tendsto_at_pole.eventually
        (eventually_gt_atTop (bound / (2 * v * κ)))).and self_mem_nhdsWithin
      obtain ⟨θ, hp, hθ⟩ := he.exists
      exact ⟨θ, hθ, hp⟩
    let Rθ : ℝ := r * (shift + θ)
    let K : Set X := {z | 0 ≤ Rθ ∧ dist z ≤ ENNReal.ofReal Rθ}
    have hKclosed : IsClosed K :=
      isClosed_const.inter (isClosed_le hdist continuous_const)
    have hKcompact : IsCompact K := hKclosed.isCompact
    have hcapture (z : X) (hz : W z ≤ (bound : WithTop ℝ)) : z ∈ K := by
      have hinside : dist z < ENNReal.ofReal (r * (shift + 1 / 10)) := by
        by_contra hnot
        have htop : W z = ⊤ := by
          simp only [W, physicalWeightedCost, dist, shift, ite_eq_right hnot]
        exact WithTop.not_top_le_coe bound (htop ▸ hz)
      have harg := hargInside z hinside
      have hfinite : cost z ≠ ⊤ := by
        intro htop
        rw [hWformula z hinside, htop, WithTop.map_top] at hz
        exact WithTop.not_top_le_coe bound hz
      obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hfinite
      have hreal : phi (arg z) * (2 * v * L + 2 * r * v) ≤ bound := by
        rw [hWformula z hinside, ← hL, WithTop.map_coe] at hz
        exact WithTop.coe_le_coe.mp hz
      have hZ := hshifted z L hL.symm
      have hargθ : arg z < θ := by
        by_contra hnot
        have hp := DifferentialGeometry.Analysis.SingularBarrier.monotoneOn hθ harg
          (le_of_not_gt hnot)
        have hp0 := DifferentialGeometry.Analysis.SingularBarrier.pos harg
        have hlow := mul_le_mul_of_nonneg_left hZ hp0.le
        have hmul := mul_le_mul_of_nonneg_right hp hρ.le
        have hstrict := (div_lt_iff₀ hρ).mp hphiθ
        nlinarith
      have hrealDist : (dist z).toReal < Rθ := by
        have hh := (div_lt_iff₀ hr).mp ((sub_lt_iff_lt_add).mp hargθ)
        dsimp only [arg, Rθ] at hh ⊢
        nlinarith
      have hRpos : 0 < Rθ := (ENNReal.toReal_nonneg).trans_lt hrealDist
      exact ⟨hRpos.le, (ENNReal.lt_ofReal_iff_toReal_lt
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinside.le)).mpr hrealDist |>.le⟩
    have hKarg (z : K) : arg z.val ≤ θ := by
      have hd := ENNReal.toReal_le_of_le_ofReal z.property.1 z.property.2
      dsimp only [arg]
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hr).mpr
      dsimp only [Rθ] at hd
      nlinarith
    have hKinside (z : K) : dist z.val < ENNReal.ofReal (r * (shift + 1 / 10)) := by
      have hRlt : Rθ < r * (shift + 1 / 10) := by
        dsimp only [Rθ]
        nlinarith
      have hRpos : 0 < r * (shift + 1 / 10) := z.property.1.trans_lt hRlt
      exact z.property.2.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hRlt)
    have hKdist : Continuous (fun z : K => (dist z.val).toReal) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      have hcomp : ContinuousAt (fun z : K => dist z.val) z :=
        hdist.continuousAt.comp continuous_subtype_val.continuousAt
      exact (ENNReal.continuousAt_toReal
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top z.property.2)).comp
        (f := fun z : K => dist z.val) (x := z) hcomp
    have hKphi : Continuous (fun z : K => phi (arg z.val)) :=
      DifferentialGeometry.Analysis.SingularBarrier.contDiffOn.continuousOn.comp_continuous
        ((hKdist.div_const r).sub continuous_const)
        (fun z => (hKarg z).trans_lt hθ)
    have hKlsc : LowerSemicontinuous (fun z : K => W z.val) := by
      have hh := lowerSemicontinuous_positive_affine_map_C11Q2
        (fun z : K => cost z.val) (hcost.comp continuous_subtype_val)
        (fun z : K => phi (arg z.val) * (2 * v))
        (fun z : K => phi (arg z.val) * (2 * r * v))
        (hKphi.mul continuous_const)
        (hKphi.mul continuous_const)
        (fun z => mul_pos (DifferentialGeometry.Analysis.SingularBarrier.pos
          ((hKarg z).trans_lt hθ)) (mul_pos (by norm_num) hv))
      convert hh using 1
      funext z
      rw [hWformula z.val (hKinside z)]
      congr 1
      funext L
      ring
    have hclosed : IsClosed {z : K | W z.val ≤ (bound : WithTop ℝ)} :=
      lowerSemicontinuous_iff_isClosed_preimage.mp hKlsc _
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
    have himg := hclosed.isCompact.image continuous_subtype_val
    convert himg using 1
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, hcapture z hz⟩, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  have hWlsc : LowerSemicontinuous W := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro bound
    cases bound using WithTop.recTopCoe with
    | top => simpa only [Iic_top, preimage_univ] using isClosed_univ
    | coe bound => exact (hcompact bound).isClosed
  have hbdd : BddBelow (range W) := ⟨0, by rintro _ ⟨y, rfl⟩; exact hnonneg y⟩
  obtain ⟨y, _, hy⟩ := LowerSemicontinuousOn.exists_isMinOn
    ⟨O, mem_univ O⟩ isCompact_univ (hWlsc.lowerSemicontinuousOn univ)
  refine ⟨y, le_antisymm (csInf_le hbdd (mem_range_self y)) ?_⟩
  apply le_csInf ⟨_, mem_range_self O⟩
  rintro _ ⟨z, rfl⟩
  exact hy (mem_univ z)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
