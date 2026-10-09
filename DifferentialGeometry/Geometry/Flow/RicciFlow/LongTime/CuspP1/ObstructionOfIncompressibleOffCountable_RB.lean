import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ObstructionOfIncompressible_RB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaBarrierIF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaFlowAT
import DifferentialGeometry.Analysis.ODE.AreaUpperBarrierOffCountableDV
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A09OfEnhancedC11M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A13OfEnhancedC11M

/-!
# S-A11-ROUTEB G4′（Route W 的 obstruction plumbing，off-countable 版）

G3′（`ObstructionOfIncompressible_RB`）把 (b)/(c)/(d) 建在 `ContinuousOn A` 的 HG14 变体上；
Route W 实际产出的是 S-A10-DERIV 的 off-countable 版
`not_nonnegative_of_C1_majorants_off_countable_pi_shift_DV`：`A ≥ 0`、乘法 left-lsc（处处）、
`E` 上乘法 right-usc、`Ici T \ E` 上 C¹ barrier，`E` 可数，不需要 `ContinuousOn A`。

* (b′) `injective_of_morrey_obstruction_offCountable_RB`：通用版，`¬Injective → ∃ T c A E, …`
  （形状逐字照 DERIV 的定理）⇒ `Injective`。
* (c′) `hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_offCountable_RB`：对 `L j C`。
* (d′) `…_of_morrey_chain_top_offCountable_RB`：Route W 的最终形状。`A` 具体化为
  `morreyAreaS F.observation M₀.exterior.region T (M₀.transported …)`（`morreyAreaS_nonneg` 给 `hn`），
  假设 = HT-L（处处）/ HT-R（只在 `E` 上）/ `E` 外 C¹ barrier / `E.Countable`，逐字照 O-IFACE G2 的
  `false_of_morreyAreaS_transport_IF`；`M₀` 由 `exists_primitive_meridian_top_CPA3` 产出；不再需要
  `ContinuousOn`，也不再自己展开 HG14。
* consumer：`hasLateSequenceTests_of_thick_thin_and_morrey_chain_offCountable_RB`，
  `hasLateSequenceTests_of_thick_thin_and_obstruction` 证明体的拷贝，只把 obstruction 一行换成 (d′)。

不引入新结构 / 新 Prop；只 import 已交付的 sorry-free 模块，可登记。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.Topology GC.LongTime Set
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

/-- (b′) off-countable 版：Morrey 面积的 off-countable barrier 数据排除非单射。 -/
theorem injective_of_morrey_obstruction_offCountable_RB {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : C(X, Y)) (x : X)
    (harea : ¬ Function.Injective (FundamentalGroup.map φ x) →
      ∃ (T c : ℝ) (A : ℝ → ℝ) (E : Set ℝ), E.Countable ∧ 0 ≤ T ∧ 0 < c ∧
        (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ s ∈ Ici T, t - δ < s → s < t → A t ≤ Real.exp ε * A s) ∧
        (∀ t ∈ Ici T ∩ E, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ s, t < s → s < t + δ → A s ≤ Real.exp ε * A t) ∧
        (∀ t ∈ Ici T \ E, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen U ∧ t ∈ U ∧
          HasDerivAt B d t ∧ B t = A t ∧ (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
          d < 3 * A t / (4 * (t + c)) - Real.pi)) :
    Function.Injective (FundamentalGroup.map φ x) := by
  by_contra h
  obtain ⟨T, c, A, E, hE, hT, hc, hn, hleft, hright, hbar⟩ := harea h
  exact not_nonnegative_of_C1_majorants_off_countable_pi_shift_DV A T c E hE (by linarith) hn
    hleft hright hbar

/-- (c′) 对 `L j C`：每个非单射的 `(s, x)` 都有 off-countable Morrey 面积数据，则
`hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)`。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_offCountable_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (hmorrey : ∀ (s : Fin (L.decomposition j C).boundary.count) (x : GC.Endpoint.Torus),
      ¬ Function.Injective (FundamentalGroup.map
        ((L.decomposition j C).reconstructionAtlas.torusInPrime
          (L.decomposition j C).reconstruction s) x) →
      ∃ (T c : ℝ) (A : ℝ → ℝ) (E : Set ℝ), E.Countable ∧ 0 ≤ T ∧ 0 < c ∧
        (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ s ∈ Ici T, t - δ < s → s < t → A t ≤ Real.exp ε * A s) ∧
        (∀ t ∈ Ici T ∩ E, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ s, t < s → s < t + δ → A s ≤ Real.exp ε * A t) ∧
        (∀ t ∈ Ici T \ E, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen U ∧ t ∈ U ∧
          HasDerivAt B d t ∧ B t = A t ∧ (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
          d < 3 * A t / (4 * (t + c)) - Real.pi)) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_injective_RB F (L.decomposition j C)
    fun s x => injective_of_morrey_obstruction_offCountable_RB _ x (hmorrey s x)

/-- (d′) Route W 的最终形状：`A = morreyAreaS`，假设 = HT-L / HT-R / `E` 外 C¹ barrier /
`E` 可数。非单射 ⇒ Top meridian `M₀`（`exists_primitive_meridian_top_CPA3`）⇒
`false_of_morreyAreaS_transport_IF`。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_top_offCountable_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hmorrey : ∀ M₀ : PrescribedCuspMeridianTop_CPQ L.cores,
      ∃ (T c : ℝ) (hT : M₀.exterior.start ≤ T) (E : Set ℝ),
        let A : ℝ → ℝ := morreyAreaS F.observation M₀.exterior.region T
          (fun t ht => M₀.transported t (hT.trans ht))
        0 < c ∧ E.Countable ∧
        (∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ (s : ℝ) (hs : T ≤ s), t₀ - δ < s → s < t₀ →
            ∃ (v : C(closedDisk, (postStage F.observation s).Carrier))
              (Kc : Set (postStage F.observation s).Carrier)
              (φ : (postStage F.observation s).Carrier → (postStage F.observation t₀).Carrier),
              DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
              DiskWeakJordanTrace (M₀.transported s (hT.trans hs)) v ∧
              range v ⊆ M₀.exterior.region s ∧
              riemannianDiskArea (postMetric F.observation s) v ≤ A s ∧ range v ⊆ Kc ∧
              IsOpen Kc ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ Kc ∧
              MapsTo φ (Kc ∩ M₀.exterior.region s) (M₀.exterior.region t₀) ∧
              (∀ θ, φ (M₀.transported s (hT.trans hs) θ) = M₀.transported t₀ (hT.trans ht₀) θ) ∧
              ∀ p ∈ Kc, ∀ w : TangentSpace (𝓡 3) p,
                (postMetric F.observation t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                    (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
                  Real.exp ε * (postMetric F.observation s).inner p w w) ∧
        (∀ t₀ ∈ E, ∀ (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ (s : ℝ) (hs : T ≤ s), t₀ < s → s < t₀ + δ →
            ∃ (v : C(closedDisk, (postStage F.observation t₀).Carrier))
              (Kc : Set (postStage F.observation t₀).Carrier)
              (φ : (postStage F.observation t₀).Carrier → (postStage F.observation s).Carrier),
              DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
              DiskWeakJordanTrace (M₀.transported t₀ (hT.trans ht₀)) v ∧
              range v ⊆ M₀.exterior.region t₀ ∧
              riemannianDiskArea (postMetric F.observation t₀) v ≤ A t₀ ∧ range v ⊆ Kc ∧
              IsOpen Kc ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ Kc ∧
              MapsTo φ (Kc ∩ M₀.exterior.region t₀) (M₀.exterior.region s) ∧
              (∀ θ, φ (M₀.transported t₀ (hT.trans ht₀) θ) = M₀.transported s (hT.trans hs) θ) ∧
              ∀ p ∈ Kc, ∀ w : TangentSpace (𝓡 3) p,
                (postMetric F.observation s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                    (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
                  Real.exp ε * (postMetric F.observation t₀).inner p w w) ∧
        (∀ t ∈ Ici T \ E, ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t ∈ V ∧
          HasDerivAt B d t ∧ B t = A t ∧ (∀ s ∈ V ∩ Ici T, A s ≤ B s) ∧
          d < 3 * A t / (4 * (t + c)) - Real.pi)) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_injective_RB F (L.decomposition j C) fun s x => by
    by_contra hcomp
    obtain ⟨M₀⟩ := exists_primitive_meridian_top_CPA3 K hK δ hadm hdec L j hj C s x hcomp
    obtain ⟨T, c, hT, E, hc, hE, hL', hR, hbar⟩ := hmorrey M₀
    have hT0 : 0 ≤ T := (L.cores.start_pos.le.trans M₀.exterior.after_cores).trans hT
    exact false_of_morreyAreaS_transport_IF F.observation M₀.exterior.region T
      (fun t ht => M₀.transported t (hT.trans ht)) c (by linarith) E hE hL' hR hbar

/-- consumer：`hasLateSequenceTests_of_thick_thin_and_obstruction` 的证明体，只把 obstruction 一行换成
(d′)（Route W 最终 re-point 的目标定理形状）。 -/
theorem hasLateSequenceTests_of_thick_thin_and_morrey_chain_offCountable_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hmorrey : ∀ {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices),
      ∀ M₀ : PrescribedCuspMeridianTop_CPQ L.cores,
      ∃ (T c : ℝ) (hT : M₀.exterior.start ≤ T) (E : Set ℝ),
        let A : ℝ → ℝ := morreyAreaS F.observation M₀.exterior.region T
          (fun t ht => M₀.transported t (hT.trans ht))
        0 < c ∧ E.Countable ∧
        (∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ (s : ℝ) (hs : T ≤ s), t₀ - δ < s → s < t₀ →
            ∃ (v : C(closedDisk, (postStage F.observation s).Carrier))
              (Kc : Set (postStage F.observation s).Carrier)
              (φ : (postStage F.observation s).Carrier → (postStage F.observation t₀).Carrier),
              DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
              DiskWeakJordanTrace (M₀.transported s (hT.trans hs)) v ∧
              range v ⊆ M₀.exterior.region s ∧
              riemannianDiskArea (postMetric F.observation s) v ≤ A s ∧ range v ⊆ Kc ∧
              IsOpen Kc ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ Kc ∧
              MapsTo φ (Kc ∩ M₀.exterior.region s) (M₀.exterior.region t₀) ∧
              (∀ θ, φ (M₀.transported s (hT.trans hs) θ) = M₀.transported t₀ (hT.trans ht₀) θ) ∧
              ∀ p ∈ Kc, ∀ w : TangentSpace (𝓡 3) p,
                (postMetric F.observation t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                    (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
                  Real.exp ε * (postMetric F.observation s).inner p w w) ∧
        (∀ t₀ ∈ E, ∀ (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ (s : ℝ) (hs : T ≤ s), t₀ < s → s < t₀ + δ →
            ∃ (v : C(closedDisk, (postStage F.observation t₀).Carrier))
              (Kc : Set (postStage F.observation t₀).Carrier)
              (φ : (postStage F.observation t₀).Carrier → (postStage F.observation s).Carrier),
              DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
              DiskWeakJordanTrace (M₀.transported t₀ (hT.trans ht₀)) v ∧
              range v ⊆ M₀.exterior.region t₀ ∧
              riemannianDiskArea (postMetric F.observation t₀) v ≤ A t₀ ∧ range v ⊆ Kc ∧
              IsOpen Kc ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ Kc ∧
              MapsTo φ (Kc ∩ M₀.exterior.region t₀) (M₀.exterior.region s) ∧
              (∀ θ, φ (M₀.transported t₀ (hT.trans ht₀) θ) = M₀.transported s (hT.trans hs) θ) ∧
              ∀ p ∈ Kc, ∀ w : TangentSpace (𝓡 3) p,
                (postMetric F.observation s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                    (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
                  Real.exp ε * (postMetric F.observation t₀).inner p w w) ∧
        (∀ t ∈ Ici T \ E, ∃ (V : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen V ∧ t ∈ V ∧
          HasDerivAt B d t ∧ B t = A t ∧ (∀ s ∈ V ∩ Ici T, A s ≤ B s) ∧
          d < 3 * A t / (4 * (t + c)) - Real.pi)) :
    hasLateSequenceTests F K := by
  have hadm : hasAnalyticAdmissibility F δ := Ch11.hasAnalyticAdmissibility_of_full_C11F henh
  intro slices htimes hnonempty
  obtain ⟨L⟩ := Ch11.exists_late_cut_family_of_enhanced_C11M F K hK δ henh hdec slices htimes
    hnonempty
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds
    (Ch11.late_derivative_tests_of_flow_of_enhanced_C11M F K hK δ henh hdec slices htimes
      hnonempty L)
  refine ⟨A, hA, ?_⟩
  intro w hw hc
  obtain ⟨N, hn⟩ := htests w hw hc
  refine ⟨max N L.first, ?_⟩
  intro j hj C
  exact ⟨L.decomposition j C, hn j ((le_max_left _ _).trans hj) C,
    hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_top_offCountable_RB K hK δ hadm hdec L j
      ((le_max_right _ _).trans hj) C (hmorrey L)⟩

end GC.LongTime.CuspP1
