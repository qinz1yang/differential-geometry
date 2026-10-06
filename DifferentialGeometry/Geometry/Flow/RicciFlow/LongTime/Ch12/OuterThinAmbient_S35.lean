import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinStatic_S35
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinCase1_S35
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationBallInputs_S29

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **(G1d)** Outer thinness in the ambient normalized metric.  Inline hypothesis `hTrans` is the
frozen G2 transfer: for late `t`, at every point `φ_i(y)` with `y ∈ B(x_i, n)` the curvature radius
`r` of the normalized metric satisfies `1 ≤ r` and
`vol B_ḡ(φ y, r) ≤ 2 · vol B_H(y, 3)`. -/
theorem outerThin_ambient_S35 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (hTrans : ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
      ∀ r : ℝ, 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) (B.map i t ht y) = ENNReal.ofReal r →
        1 ≤ r ∧ ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) (B.map i t ht y) r ≤
          ENNReal.ofReal 2 * ballVolume (B.model i).metric y 3) :
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
  obtain ⟨T₁, hT₁⟩ := hTrans
  obtain ⟨Tc, hTc⟩ := volumeCollapsed_of_not_covered_S35 B hw
  choose n₀ hn₀pos hn₀ using fun i : Fin B.count =>
    outer_thin_static_S35 (base i) (B.model i).basepoint (ρ := 3) (by norm_num)
  set N : ℝ := max (max (∑ i, n₀ i) 1) (8 / w) with hN
  have hNn : ∀ i, n₀ i ≤ N := fun i =>
    ((Finset.single_le_sum (f := n₀) (fun j _ => (hn₀pos j).le) (Finset.mem_univ i)).trans
      (le_max_left _ _)).trans (le_max_left _ _)
  have hN1 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
  have hNw : 8 / w ≤ N := le_max_right _ _
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
    obtain ⟨hr1, hvol⟩ := hT₁ t ht hT₁' i y hy r hr hcr
    have hnpos : 0 < (B.accuracy t)⁻¹ := lt_of_lt_of_le hN1 hn
    have h8 : 8 / (B.accuracy t)⁻¹ ≤ w := by
      rw [div_le_iff₀ hnpos]
      rw [div_le_iff₀ hw] at hNw
      nlinarith [mul_le_mul_of_nonneg_right hn hw.le]
    calc _ ≤ ENNReal.ofReal 2 * ballVolume (B.model i).metric y 3 := hvol
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (4 / (B.accuracy t)⁻¹) := by gcongr
      _ = ENNReal.ofReal (8 / (B.accuracy t)⁻¹) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (w * r ^ 3) := by
          apply ENNReal.ofReal_le_ofReal
          have : 1 ≤ r ^ 3 := one_le_pow₀ hr1
          nlinarith
  · exact hTc t ht hTc' x hcov

end GC.LongTime.Ch12
