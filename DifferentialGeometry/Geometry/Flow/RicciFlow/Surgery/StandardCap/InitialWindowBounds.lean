import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Metric.CompactSourceEllipticity
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Topology.Manifold.OpenSubtypeModel

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ReferenceCurvatureBounds

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
namespace CanonicalStaticInsertionWitness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
  (w : CanonicalStaticInsertionWitness d A hA D m ε)

theorem window_metricCovDerivNorm_le {j : ℕ} (hj : j ≤ m)
    {x : standardCapWindow D} (hx : ‖x.val‖ < D) :
    metricCovDerivNorm j w.windowMetric
      (standardCapMetric.restrictOpen (standardCapWindow D)) x ≤
      (if j = 0 then Real.sqrt 3 else 0) + ε := by
  let gRef := standardCapMetric.restrictOpen (standardCapWindow D)
  have he := w.properties.window_close
  change metricDerivENormSupOn
    {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at he
  simp only [distance_zero] at he
  have herr : metricDerivNorm j w.windowMetric gRef gRef x ≤ ε := by
    dsimp only [gRef]
    rw [standardCapMetric_eq_metric]
    exact (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ he hj hx).le
  have hb := covNorm_le_add j w.windowMetric gRef gRef x
  have hself : metricCovDerivNorm j gRef gRef x = if j = 0 then Real.sqrt 3 else 0 := by
    cases j with
    | zero => simp only [metricCovDerivNorm_self_zero,
        show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], Nat.cast_ofNat, ite_true]
    | succ j => simp only [covNorm_self_succ, Nat.succ_ne_zero, ite_false]
  exact hb.trans (add_le_add (le_of_eq hself) herr)

end CanonicalStaticInsertionWitness

theorem exists_uniform_window_coordinate_derivative_bounds
    (D R : ℝ) (hD : 0 < D) (hRD : R < D) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ε : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → r ≤ m →
        ∀ x : standardCapWindow D, ‖x.val‖ ≤ R →
          ∀ i j : Fin (Module.finrank ℝ ThreeSpace),
          ‖iteratedFDeriv ℝ r
            (chartGramOnE w.windowMetric (⟨0, by
              change ‖(0 : ThreeSpace)‖ < D + 1
              simp only [norm_zero]
              linarith⟩ : standardCapWindow D) i j) x.val‖ ≤ B := by
  let gRef := standardCapMetric.restrictOpen (standardCapWindow D)
  let p : standardCapWindow D := ⟨0, by
    change ‖(0 : ThreeSpace)‖ < D + 1
    simp only [norm_zero]
    linarith⟩
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ R}
  have hK : IsCompact K := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ R} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) R
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change ‖x‖ < D + 1
      change ‖x‖ ≤ R at hx
      linarith)
  have hKchart : K ⊆ (chartAt ThreeSpace p).source := by
    rw [← extChartAt_source (I := ThreeModel), extChartAt_opens_source]
    exact subset_univ _
  obtain ⟨C, hC, hdiff⟩ := chartJet_sub_le gRef p hK hKchart r
  have hself : ∀ q : ℕ, ∀ x : standardCapWindow D,
      metricCovDerivNorm q gRef gRef x ≤ Real.sqrt 3 := by
    intro q x
    cases q with
    | zero => simp only [metricCovDerivNorm_self_zero, show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], Nat.cast_ofNat, le_refl]
    | succ q => rw [covNorm_self_succ]; positivity
  obtain ⟨Cref, hCref, href⟩ := chartGram_iter_le gRef (fun _ : Unit => gRef) p hK hKchart r
    (fun q _ => ⟨Real.sqrt 3, fun _ x _ => hself q x⟩)
  refine ⟨C * ((r + 1 : ℕ) : ℝ) + Cref, by positivity, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ε w heps hrm x hx i j
  have hxK : x ∈ K := hx
  have hxD : ‖x.val‖ < D := hx.trans_lt hRD
  have herr : ∀ q ≤ r, metricDerivNorm q w.windowMetric gRef gRef x ≤ 1 := by
    intro q hqr
    have he := w.properties.window_close
    change metricDerivENormSupOn
      {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
      w.windowMetric (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at he
    simp only [distance_zero] at he
    have hh := metricDerivNorm_lt_of_sup_lt _ _ _ _ _ he (hqr.trans hrm) hxD
    rw [show gRef = metric.restrictOpen (standardCapWindow D) from
      congrArg (fun g => g.restrictOpen (standardCapWindow D)) standardCapMetric_eq_metric]
    exact hh.le.trans (by linarith)
  have hsum : ∑ q ∈ Finset.range (r + 1), metricDerivNorm q w.windowMetric gRef gRef x ≤
      ((r + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ _q ∈ Finset.range (r + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun q hq => herr q (Nat.le_of_lt_succ (Finset.mem_range.mp hq)))
      _ = _ := by simp
  have hd := (hdiff w.windowMetric gRef x hxK i j).trans
    (mul_le_mul_of_nonneg_left hsum hC)
  have hb := norm_le_norm_sub_add
    (iteratedFDeriv ℝ r (chartGramOnE w.windowMetric p i j) (extChartAt ThreeModel p x))
    (iteratedFDeriv ℝ r (chartGramOnE gRef p i j) (extChartAt ThreeModel p x))
  exact hb.trans (add_le_add hd (href () x hxK i j))

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

private theorem exists_metric_inner_lower_bound_on_closedBall (R : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ThreeSpace, ‖x‖ ≤ R → ∀ v : ThreeSpace,
      c * ‖v‖ ^ 2 ≤ metric.inner x v v := by
  obtain ⟨c, C, hc, _, hb⟩ := Geometry.exists_compact_source_metric_ellipticity
    (f := id) (U := univ) metric isOpen_univ contMDiff_id.contMDiffOn
    (isCompact_closedBall (0 : ThreeSpace) R) (subset_univ _)
    (by intro x hx; simpa using Function.injective_id)
  refine ⟨c, hc, fun x hx v => ?_⟩
  have hid : mfderiv ThreeModel ThreeModel (@id ThreeSpace) x v = v := by
    rw [mfderiv_id]
    rfl
  simpa only [hid, id_eq] using (hb x (by simpa using hx) v).1

theorem exists_uniform_window_ellipticity (R : ℝ) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → R < D → ∀ x : standardCapWindow D, ‖x.val‖ ≤ R →
        ∀ v : TangentSpace ThreeModel x,
          Λ⁻¹ * ‖v‖ ^ 2 ≤ metricScalarAt g x₀ *
            w.data.outMetric.inner (w.window x)
              (mfderiv ThreeModel ThreeModel w.window x v)
              (mfderiv ThreeModel ThreeModel w.window x v) ∧
          metricScalarAt g x₀ * w.data.outMetric.inner (w.window x)
              (mfderiv ThreeModel ThreeModel w.window x v)
              (mfderiv ThreeModel ThreeModel w.window x v) ≤ Λ * ‖v‖ ^ 2 := by
  obtain ⟨c, hc, hbound⟩ := exists_metric_inner_lower_bound_on_closedBall R
  let Λ := max 2 (2 / c)
  have hΛ : 1 ≤ Λ := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  have hinv : Λ⁻¹ ≤ c / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hΛpos]
    have h := (div_le_iff₀ hc).mp (le_max_right 2 (2 / c))
    nlinarith
  refine ⟨Λ, hΛ, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ε w heps hRD x hx v
  rw [← w.window_inner x v v]
  have he := w.properties.window_close
  change metricDerivENormSupOn
    {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at he
  simp only [distance_zero] at he
  have hb₀ := inner_bounds_of_metricDerivENormSupOn_lt
    (metric.restrictOpen (standardCapWindow D)) w.windowMetric he (hx.trans_lt hRD) v
  rw [SmoothRiemannianMetric.restrictOpen_inner] at hb₀
  have hnn := metric_inner_self_nonneg metric x.val v
  have hb : (1 / 2 : ℝ) * metric.inner x.val v v ≤ w.windowMetric.inner x v v ∧
      w.windowMetric.inner x v v ≤ (3 / 2 : ℝ) * metric.inner x.val v v := by
    constructor <;> nlinarith [hb₀.1, hb₀.2]
  have hlo := hbound x.val hx v
  have hup := metric_inner_le x.val v
  have hn := sq_nonneg ‖v‖
  constructor
  · calc
      Λ⁻¹ * ‖v‖ ^ 2 ≤ (c / 2) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hinv hn
      _ = (1 / 2 : ℝ) * (c * ‖v‖ ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * metric.inner x.val v v :=
        mul_le_mul_of_nonneg_left hlo (by norm_num)
      _ ≤ w.windowMetric.inner x v v := hb.1
  · calc
      w.windowMetric.inner x v v ≤ (3 / 2 : ℝ) * metric.inner x.val v v := hb.2
      _ ≤ (3 / 2 : ℝ) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left hup (by norm_num)
      _ ≤ Λ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right
        ((by norm_num : (3 / 2 : ℝ) ≤ 2).trans (le_max_left _ _)) hn


open DifferentialGeometry.Tensor0SBundle in
theorem exists_uniform_window_curvature_derivative_bounds (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → j + 2 ≤ m → ∀ x : standardCapWindow D, ‖x.val‖ < D →
        Real.sqrt (normSq0S w.windowMetric x (4 + j)
          (iterCov w.windowMetric 4 (metricRm04 w.windowMetric) j x)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets_on_opens
      j (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ε w heps hj x hx
  have he := w.properties.window_close
  change metricDerivENormSupOn
    {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at he
  simp only [distance_zero] at he
  have hjet (q : ℕ) (hq : q ≤ j + 2) :
      metricDerivNorm q w.windowMetric (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) x ≤ 1 / 2 :=
    (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ he (hq.trans hj) hx).le.trans heps
  apply hbound (standardCapWindow D) w.windowMetric x _ hjet
  intro v
  have h := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le
    (metric.restrictOpen (standardCapWindow D)) w.windowMetric x (hjet 0 (by omega)) v).1
  norm_num at h ⊢
  exact h

end DifferentialGeometry.PDE.RicciFlow.StandardCap
