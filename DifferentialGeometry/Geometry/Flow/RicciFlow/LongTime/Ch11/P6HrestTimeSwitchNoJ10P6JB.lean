import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestNoJ10P6JB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6JointNoJ10P6JB

/-!
# 切换 example（续）：HP3 孪生喂 time jointD 孪生的 hrestP 槽（O-CH11-J10GEN2B G3b，`_P6JB`）

HP3 consumer (i)（`P6HrestJointPrefixTopP6HP3.lean:974`）的无 J10 孪生：`hrestP_of_jointPrefix_P6HP3` →
`hrestP_of_jointPrefix_noJ10_P6JB hkerJ hkerF hkerF8`，`canonicalLateCore_of_jointD_P6CK` → time 版孪生
`canonicalLateTimeCore_of_jointD_noJ10_P6JB hkerJ0`。`_hcomp` 的 binder = 换完后 time jointD 的全部输入：
`hgapJ`（= `hgapJ_noJ10_P6JK`，G1 producer 可付，见 G3）、`hgapJ8 hgapJF hgapJF8`（无 J10 文本，G1 producer 可付）、
`hcapWL hcenE hfootE htransE hlocH hcan₁ hdomF`（HP3 原槽）+ 四个 no-J10 kernel 前提。无 J10 / `Q < R` 前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6CoarseC_eq_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6
  p6FineEta_le_C11GT6)

/-- **G3b consumer / 切换 example**：见文件头。 -/
example
    (hkerJ0 : ObservedHistory.NotKKernelNoJ10_P6JB.{u})
    (hkerJ : ObservedHistory.NotKKernelDecNoJ10_P6JB.{u})
    (hkerF : ObservedHistory.FinalKernelNoJ10_P6JB.{u})
    (hkerF8 : ObservedHistory.FinalKernelDecNoJ10_P6JB.{u}) :
    True := by
  obtain ⟨_c₀, -, _Cb, _Rn, _ζ, _δ₀, _m₀, -, -, -, -, -, epsH, -, hHP⟩ :=
    (ObservedHistory.hrestP_of_jointPrefix_noJ10_P6JB.{u} hkerJ hkerF hkerF8)
  obtain ⟨_c₀', -, _Cb', _Rn', _ζ', _δ₀', _m₀', -, -, -, -, -, epsJ, -, hJD⟩ :=
    (ObservedHistory.canonicalLateTimeCore_of_jointD_noJ10_P6JB.{u} hkerJ0)
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsH → ε ≤ epsJ →
      ε ≤ Classical.choose ObservedHistory.ancientWitness_decoupled_P6P.{u} →
      ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
      True := by
    intro ε hε hsmall hεH hεJ hεA hεX hεN hεcone
    obtain ⟨CH, -, hHP'⟩ := hHP ε hε hsmall hεH hεA hεX hεN hεcone
    obtain ⟨CJ, -, hJD'⟩ := hJD ε hε hsmall hεJ hεX hεN hεcone
    have _hcomp := fun {P : OrientedThreeStage.{u}} {g : P.Metric}
        {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} hanti hcan hder
        (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) hT₀m hQm hgapJ hgapJ8 hgapJF hgapJF8 hcapWL hcenE
        hfootE htransE hlocH hcan₁ hdomF =>
      hJD' (C1 := max CH CJ) (C2 := max CH CJ) (Ctime := (max CH CJ).toNNReal)
        (le_max_right _ _) (le_max_right _ _) (Real.toNNReal_le_toNNReal (le_max_right _ _))
        (F := F) (q := q) hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm hgapJ
        (hHP' (C1 := max CH CJ) (C2 := max CH CJ) (Ctime := (max CH CJ).toNNReal)
          (le_max_left _ _) (le_max_left _ _) (Real.toNNReal_le_toNNReal (le_max_left _ _))
          (F := F) (q := q) (C1f := 1) (C2f := 1) (m := 1) (kk := 0) Ctime₀ T₀ Qt hanti hT₀m hQm
          hgapJ8 hgapJF hgapJF8 hcapWL hcenE hfootE htransE hlocH hcan₁ hdomF)
    trivial
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
