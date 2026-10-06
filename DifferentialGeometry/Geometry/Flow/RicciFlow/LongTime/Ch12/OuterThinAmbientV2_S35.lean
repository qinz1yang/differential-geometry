import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinStatic_S35
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinCase1_S35
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationBallInputs_S29
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferRadius_S35

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **(G2a)** Outer thinness, final shape.  The single inline hypothesis `hTrans` is the frozen
transfer from the buffer: for late `t` and `y ∈ B(x_i, n)`, with `ḡ = ḡ_t`, `x = φ_i(y)`:
(low) `sec ḡ ≥ -1/c₀²` on `B_ḡ(x, c₀)`; (up) some plane at `x` has `sec ḡ < -1/8`;
(vol) `vol B_ḡ(x, r) ≤ 2 · vol B_H(y, 4)` for `r² ≤ 8`. -/
theorem outerThin_ambient_v2_S35 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (hTrans : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t →
      ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        (∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) c₀,
          SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) ∧
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)) ∧
        ∀ r : ℝ, 0 < r → r ^ 2 ≤ 8 →
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) r ≤
          ENNReal.ofReal 2 * ballVolume (B.model i).metric y 4) :
    ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ t (ht : B.start ≤ t), T ≤ t →
      ∀ trunc : (i : Fin B.count) → HyperbolicTruncation (B.model i),
        (∀ i, riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
            ((B.accuracy t)⁻¹ / 2) ⊆ Set.range (trunc i).inclusion) →
        ∀ x : (postStage F.observation t).Carrier,
          x ∉ ⋃ i : Fin B.count, B.map i t ht '' Set.range (trunc i).inclusion →
          volumeCollapsedAtCurvatureScale
            (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
              (postMetric F.observation t)) w x := by
  intro w hw
  obtain ⟨c₀, hc₀, T₁, hT₁⟩ := hTrans
  obtain ⟨Tc, hTc⟩ := volumeCollapsed_of_not_covered_S35 B hw
  choose n₀ hn₀pos hn₀ using fun i : Fin B.count =>
    outer_thin_static_S35 (base i) (B.model i).basepoint (ρ := 4) (by norm_num)
  set N : ℝ := max (max (∑ i, n₀ i) 1) (8 / (w * c₀ ^ 3)) with hN
  have hNn : ∀ i, n₀ i ≤ N := fun i =>
    ((Finset.single_le_sum (f := n₀) (fun j _ => (hn₀pos j).le) (Finset.mem_univ i)).trans
      (le_max_left _ _)).trans (le_max_left _ _)
  have hN1 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
  have hNw : 8 / (w * c₀ ^ 3) ≤ N := le_max_right _ _
  obtain ⟨T₀, -, hT₀⟩ := accuracy_inv_large_S29 B N
  refine ⟨max (max Tc T₁) T₀, fun t ht hTt trunc hcl x hx => ?_⟩
  have hTc' : Tc ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans hTt)
  have hT₁' : T₁ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans hTt)
  have hT₀' : T₀ ≤ t := (le_max_right _ _).trans hTt
  have hn : N ≤ (B.accuracy t)⁻¹ := hT₀ t hT₀'
  by_cases hcov : x ∈ ⋃ i : Fin B.count, B.map i t ht ''
      riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹
  · obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hcov |>.imp fun i h => by simpa using h
    have hyn : y ∉ Set.range (trunc i).inclusion := fun hr => hx (Set.mem_iUnion.mpr
      ⟨i, ⟨y, hr, rfl⟩⟩)
    have hyc : y ∉ riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
        ((B.accuracy t)⁻¹ / 2) := fun h => hyn (hcl i h)
    have hthin := hn₀ i _ ((hNn i).trans hn) y hyc
    intro r hr hcr
    obtain ⟨hlow, hup, hvolr⟩ := hT₁ t ht hT₁' i y hy
    obtain ⟨hr1, hr8⟩ := curvatureRadius_bounds_S35 _ _ hc₀ hlow hup hr hcr
    have hvol := hvolr r hr hr8
    have hnpos : 0 < (B.accuracy t)⁻¹ := lt_of_lt_of_le hN1 hn
    have hwc : 0 < w * c₀ ^ 3 := by positivity
    have h8 : 8 / (B.accuracy t)⁻¹ ≤ w * c₀ ^ 3 := by
      rw [div_le_iff₀ hnpos]
      rw [div_le_iff₀ hwc] at hNw
      nlinarith [mul_le_mul_of_nonneg_right hn hwc.le]
    calc _ ≤ ENNReal.ofReal 2 * ballVolume (B.model i).metric y 4 := hvol
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (4 / (B.accuracy t)⁻¹) := by gcongr
      _ = ENNReal.ofReal (8 / (B.accuracy t)⁻¹) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (w * r ^ 3) := by
          apply ENNReal.ofReal_le_ofReal
          have : c₀ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hc₀.le hr1 3
          nlinarith [mul_le_mul_of_nonneg_left this hw.le]
  · exact hTc t ht hTc' x hcov

end GC.LongTime.Ch12
