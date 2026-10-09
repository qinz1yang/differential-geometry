import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.DerivativeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SliverForwardComparison
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private theorem exists_forall_Ico_of_eventually {Q : ℝ → P.Carrier → Prop} {t₀ : ℝ}
    (hts : t₀ < s) (hQ : ∀ y, ∀ᶠ z in 𝓝[Ici t₀ ×ˢ univ] (t₀, y), Q z.1 z.2) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧ ∀ t ∈ Ico t₀ (t₀ + η), ∀ y, Q t y := by
  have hQ' : ∀ y ∈ (univ : Set P.Carrier),
      ∀ᶠ z : ℝ × P.Carrier in 𝓝 (t₀, y), t₀ ≤ z.1 → Q z.1 z.2 := by
    intro y _
    filter_upwards [eventually_nhdsWithin_iff.mp (hQ y)] with z hz hz₁
    exact hz ⟨hz₁, mem_univ _⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun t x => t₀ ≤ t → Q t x) hQ')
  refine ⟨min (ε / 2) ((s - t₀) / 2), lt_min (half_pos hε) (by linarith),
    by linarith [min_le_right (ε / 2) ((s - t₀) / 2)], fun t ht y => ?_⟩
  have hdist : dist t t₀ < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2, min_le_left (ε / 2) ((s - t₀) / 2)]
  exact hball hdist y (mem_univ y) ht.1

theorem derivWithin_Ici_scalar_eq_Iic {t : ℝ} (ht : t ∈ Ioo a s) (x : P.Carrier) :
    derivWithin (fun v => G.flow.scalar v x) (Ici t) t =
      derivWithin (fun v => G.flow.scalar v x) (Iic t) t := by
  have hd := (G.equation.scalarTime
    (show t ∈ (RealTimeInterval.closedOpen a s G.lt).carrier from ⟨ht.1.le, ht.2⟩)
    Subset.rfl x).differentiableAt
    ((RealTimeInterval.closedOpen a s G.lt).regular_mem_nhds ht)
  rw [hd.derivWithin (uniqueDiffWithinAt_Ici t), hd.derivWithin (uniqueDiffWithinAt_Iic t)]

private theorem scalar_continuousWithinAt_Ici {t₀ : ℝ} (ht₀ : t₀ ∈ Ico a s) (y : P.Carrier) :
    ContinuousWithinAt (fun z : ℝ × P.Carrier => G.flow.scalar z.1 z.2) (Ici t₀ ×ˢ univ)
      (t₀, y) := by
  refine (G.equation.scalarCont (t₀, y) ⟨ht₀, mem_univ y⟩).mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.mpr ⟨Iio s ×ˢ univ, isOpen_Iio.prod isOpen_univ,
    ⟨ht₀.2, mem_univ y⟩, fun z hz => ⟨⟨ht₀.1.trans hz.2.1, hz.1.1⟩, mem_univ _⟩⟩

private theorem derivWithin_Ici_continuousAt {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s) (y : P.Carrier) :
    ContinuousAt (fun z : ℝ × P.Carrier =>
      derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1) (t₀, y) := by
  have hc := (G.flow.scalar_time_derivWithin_Iic_continuousOn G.equation).continuousAt
    (((RealTimeInterval.closedOpen a s G.lt).regular_isOpen.prod isOpen_univ).mem_nhds
      (show (t₀, y) ∈ (RealTimeInterval.closedOpen a s G.lt).regular ×ˢ univ from
        ⟨ht₀, mem_univ y⟩))
  refine hc.congr ?_
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
    (show (t₀, y) ∈ Ioo a s ×ˢ (univ : Set P.Carrier) from ⟨ht₀, mem_univ y⟩)] with z hz
  exact (G.derivWithin_Ici_scalar_eq_Iic hz.1 z.2).symm

theorem exists_derivativeBoundBefore_extend_of_slice {C : ℝ≥0} {q t₀ : ℝ} (hC : 0 < C)
    (hq : 0 < q) (ht₀ : t₀ ∈ Ico a s)
    (hreg : t₀ = a → ∀ y : P.Carrier, ContinuousWithinAt (fun z : ℝ × P.Carrier =>
      derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1) (Ici a ×ˢ univ) (a, y))
    (hstart : t₀ = a → ∀ y : P.Carrier, q < G.flow.scalar a y →
      |derivWithin (fun v => G.flow.scalar v y) (Ici a) a| ≤ C * G.flow.scalar a y ^ 2)
    (h : G.DerivativeBoundBefore C q t₀) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧ G.DerivativeBoundBefore (2 * C) (2 * q) (t₀ + η) := by
  have hC' : (0 : ℝ) < C := hC
  have hD : ∀ y : P.Carrier, ContinuousWithinAt (fun z : ℝ × P.Carrier =>
      derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1) (Ici t₀ ×ˢ univ) (t₀, y) := by
    intro y
    rcases ht₀.1.eq_or_lt with hat₀ | hat₀
    · subst hat₀
      exact hreg rfl y
    · exact (G.derivWithin_Ici_continuousAt ⟨hat₀, ht₀.2⟩ y).continuousWithinAt
  have hslice : ∀ y : P.Carrier, q < G.flow.scalar t₀ y →
      |derivWithin (fun v => G.flow.scalar v y) (Ici t₀) t₀| ≤ C * G.flow.scalar t₀ y ^ 2 := by
    intro y hy
    rcases ht₀.1.eq_or_lt with hat₀ | hat₀
    · subst hat₀
      exact hstart rfl y hy
    · rw [G.derivWithin_Ici_scalar_eq_Iic ⟨hat₀, ht₀.2⟩ y]
      exact G.abs_derivWithin_scalar_le_of_forall_Ioo ⟨hat₀, ht₀.2⟩ y
        (fun t ht hqt => h y t ht hqt) hy
  obtain ⟨η, hη, hηs, hgood⟩ := exists_forall_Ico_of_eventually (P := P)
    (Q := fun t x => 2 * q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Ici t) t| ≤ 2 * C * G.flow.scalar t x ^ 2)
    ht₀.2 (fun y => by
      have hR := G.scalar_continuousWithinAt_Ici ht₀ y
      rcases lt_or_ge q (G.flow.scalar t₀ y) with hy | hy
      · have hF : ContinuousWithinAt (fun z : ℝ × P.Carrier =>
            |derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1| -
              2 * C * G.flow.scalar z.1 z.2 ^ 2) (Ici t₀ ×ˢ univ) (t₀, y) :=
          (hD y).abs.sub (continuousWithinAt_const.mul (hR.pow 2))
        have hneg : |derivWithin (fun v => G.flow.scalar v y) (Ici t₀) t₀| -
            2 * C * G.flow.scalar t₀ y ^ 2 < 0 := by
          have hpos : 0 < G.flow.scalar t₀ y ^ 2 := pow_pos (hq.trans hy) 2
          nlinarith [hslice y hy]
        filter_upwards [hF.eventually (gt_mem_nhds hneg)] with z hz _
        linarith
      · filter_upwards [hR.eventually (gt_mem_nhds (show G.flow.scalar t₀ y < 2 * q by
          linarith))] with z hz hz'
        exact absurd hz' (not_lt.mpr hz.le))
  refine ⟨η, hη, hηs, fun y t ht hR => ?_⟩
  push_cast
  have hts : t < s := ht.2.trans hηs
  rcases lt_or_ge t t₀ with htt | htt
  · have hb := h y t ⟨ht.1, htt⟩ (by linarith)
    have hsq : 0 ≤ G.flow.scalar t y ^ 2 := sq_nonneg _
    nlinarith
  · rw [← G.derivWithin_Ici_scalar_eq_Iic ⟨ht.1, hts⟩ y]
    exact hgood t ⟨htt, ht.2⟩ y hR

theorem exists_derivativeBoundBefore_extend {C : ℝ≥0} {q t₀ : ℝ} (hC : 0 < C) (hq : 0 < q)
    (ht₀ : t₀ ∈ Ioo a s) (h : G.DerivativeBoundBefore C q t₀) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧ G.DerivativeBoundBefore (2 * C) (2 * q) (t₀ + η) :=
  G.exists_derivativeBoundBefore_extend_of_slice hC hq ⟨ht₀.1.le, ht₀.2⟩
    (fun h' => absurd h' ht₀.1.ne') (fun h' => absurd h' ht₀.1.ne') h

theorem scalarDifferential_eq_inner_gradientFun (t : ℝ) (x : P.Carrier)
    (v : TangentSpace ThreeModel x) :
    Perelman.CanonicalNeighborhood.scalarDifferential G.flow t x v =
      (G.flow.base.metric t).inner x
        (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) v := by
  rw [inner_gradientFun]
  rfl

theorem inner_gradientFun_scalar_le_sq_of_abs_scalarDifferential_le {t K : ℝ} (x : P.Carrier)
    (hK : 0 ≤ K)
    (h : ∀ v : TangentSpace ThreeModel x,
      |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t x v| ≤
        K * Real.sqrt ((G.flow.base.metric t).inner x v v)) :
    (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
      (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) ≤ K ^ 2 := by
  set w := gradientFun (G.flow.base.metric t) (G.flow.scalar t) x
  have hw := h w
  rw [G.scalarDifferential_eq_inner_gradientFun] at hw
  have hn := metric_inner_self_nonneg (G.flow.base.metric t) x w
  rw [abs_of_nonneg hn] at hw
  have hs := Real.sq_sqrt hn
  have hr := Real.sqrt_nonneg ((G.flow.base.metric t).inner x w w)
  have hle : Real.sqrt ((G.flow.base.metric t).inner x w w) ≤ K := by
    by_contra hlt
    nlinarith
  nlinarith

theorem abs_scalarDifferential_le_of_inner_gradientFun_le_sq {t K : ℝ} (x : P.Carrier)
    (hK : 0 ≤ K)
    (h : (G.flow.base.metric t).inner x
      (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
      (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) ≤ K ^ 2)
    (v : TangentSpace ThreeModel x) :
    |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t x v| ≤
      K * Real.sqrt ((G.flow.base.metric t).inner x v v) := by
  rw [G.scalarDifferential_eq_inner_gradientFun]
  refine (DifferentialGeometry.SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic
    _ x _ v).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  calc Real.sqrt _ ≤ Real.sqrt (K ^ 2) := Real.sqrt_le_sqrt h
    _ = K := Real.sqrt_sq hK

private theorem gradient_normSq_continuousAt {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s) (y : P.Carrier) :
    ContinuousAt (fun z : ℝ × P.Carrier => (G.flow.base.metric z.1).inner z.2
      (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)
      (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)) (t₀, y) :=
  (G.flow.scalar_gradient_norm_sq_contMDiffOn G.equation).continuousOn.continuousAt
    (((RealTimeInterval.closedOpen a s G.lt).regular_isOpen.prod isOpen_univ).mem_nhds
      (show (t₀, y) ∈ (RealTimeInterval.closedOpen a s G.lt).regular ×ˢ univ from
        ⟨ht₀, mem_univ y⟩))

theorem exists_gradientBoundBefore_extend_of_slice {C : ℝ≥0} {q t₀ : ℝ} (hC : 0 < C)
    (hq : 0 < q) (ht₀ : t₀ ∈ Ico a s)
    (hreg : t₀ = a → ∀ y : P.Carrier, ContinuousWithinAt (fun z : ℝ × P.Carrier =>
      (G.flow.base.metric z.1).inner z.2
        (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)
        (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)) (Ici a ×ˢ univ) (a, y))
    (hstart : t₀ = a → ∀ y : P.Carrier, q < G.flow.scalar a y →
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow a y v| ≤
          C * G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) *
            Real.sqrt ((G.flow.base.metric a).inner y v v))
    (h : G.GradientBoundBefore C q t₀) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧ G.GradientBoundBefore (2 * C) (2 * q) (t₀ + η) := by
  have hC' : (0 : ℝ) < C := hC
  have hD : ∀ y : P.Carrier, ContinuousWithinAt (fun z : ℝ × P.Carrier =>
      (G.flow.base.metric z.1).inner z.2
        (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)
        (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2))
      (Ici t₀ ×ˢ univ) (t₀, y) := by
    intro y
    rcases ht₀.1.eq_or_lt with hat₀ | hat₀
    · subst hat₀
      exact hreg rfl y
    · exact (G.gradient_normSq_continuousAt ⟨hat₀, ht₀.2⟩ y).continuousWithinAt
  obtain ⟨η, hη, hηs, hgood⟩ := exists_forall_Ico_of_eventually (P := P)
    (Q := fun t x => 2 * q < G.flow.scalar t x →
      (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
        (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) ≤
        (2 * C * G.flow.scalar t x * Real.sqrt (G.flow.scalar t x)) ^ 2)
    ht₀.2 (fun y => by
      have hR := G.scalar_continuousWithinAt_Ici ht₀ y
      rcases lt_or_ge q (G.flow.scalar t₀ y) with hy | hy
      · have hF : ContinuousWithinAt (fun z : ℝ × P.Carrier =>
            (G.flow.base.metric z.1).inner z.2
              (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)
              (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2) -
            (2 * C * G.flow.scalar z.1 z.2 * Real.sqrt (G.flow.scalar z.1 z.2)) ^ 2)
            (Ici t₀ ×ˢ univ) (t₀, y) :=
          (hD y).sub (((continuousWithinAt_const.mul hR).mul hR.sqrt).pow 2)
        have hRpos : 0 < G.flow.scalar t₀ y := hq.trans hy
        have hK : 0 < (C : ℝ) * G.flow.scalar t₀ y * Real.sqrt (G.flow.scalar t₀ y) := by
          have := Real.sqrt_pos.mpr hRpos
          positivity
        have hsl := G.inner_gradientFun_scalar_le_sq_of_abs_scalarDifferential_le y hK.le
          (G.abs_scalarDifferential_le_at_slice ht₀
            (fun t ht x hx v => h x t ht hx v) hstart y hy)
        have hneg : (G.flow.base.metric t₀).inner y
            (gradientFun (G.flow.base.metric t₀) (G.flow.scalar t₀) y)
            (gradientFun (G.flow.base.metric t₀) (G.flow.scalar t₀) y) -
            (2 * C * G.flow.scalar t₀ y * Real.sqrt (G.flow.scalar t₀ y)) ^ 2 < 0 := by
          nlinarith
        filter_upwards [hF.eventually (gt_mem_nhds hneg)] with z hz _
        linarith
      · filter_upwards [hR.eventually (gt_mem_nhds (show G.flow.scalar t₀ y < 2 * q by
          linarith))] with z hz hz'
        exact absurd hz' (not_lt.mpr hz.le))
  refine ⟨η, hη, hηs, fun y t ht hR v => ?_⟩
  push_cast
  have hRpos : 0 < G.flow.scalar t y := by linarith
  have hsq := Real.sqrt_nonneg (G.flow.scalar t y)
  have hsv := Real.sqrt_nonneg ((G.flow.base.metric t).inner y v v)
  rcases lt_or_ge t t₀ with htt | htt
  · have hb := h y t ⟨ht.1, htt⟩ (by linarith) v
    have hm : 0 ≤ (C : ℝ) * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
        Real.sqrt ((G.flow.base.metric t).inner y v v) := by positivity
    linarith
  · exact G.abs_scalarDifferential_le_of_inner_gradientFun_le_sq y (by positivity)
      (hgood t ⟨htt, ht.2⟩ y hR) v

theorem exists_gradientBoundBefore_extend {C : ℝ≥0} {q t₀ : ℝ} (hC : 0 < C) (hq : 0 < q)
    (ht₀ : t₀ ∈ Ioo a s) (h : G.GradientBoundBefore C q t₀) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧ G.GradientBoundBefore (2 * C) (2 * q) (t₀ + η) :=
  G.exists_gradientBoundBefore_extend_of_slice hC hq ⟨ht₀.1.le, ht₀.2⟩
    (fun h' => absurd h' ht₀.1.ne') (fun h' => absurd h' ht₀.1.ne') h

theorem exists_derivative_gradientBoundBefore_extend {Ctime Cgrad : ℝ≥0} {q t₀ : ℝ}
    (hCt : 0 < Ctime) (hCg : 0 < Cgrad) (hq : 0 < q) (ht₀ : t₀ ∈ Ioo a s)
    (hder : G.DerivativeBoundBefore Ctime q t₀) (hgrad : G.GradientBoundBefore Cgrad q t₀) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧ ∀ t, t < t₀ + η →
      G.DerivativeBoundBefore (2 * Ctime) (2 * q) t ∧
        G.GradientBoundBefore (2 * Cgrad) (2 * q) t := by
  obtain ⟨η₁, hη₁, hs₁, h₁⟩ := G.exists_derivativeBoundBefore_extend hCt hq ht₀ hder
  obtain ⟨η₂, hη₂, -, h₂⟩ := G.exists_gradientBoundBefore_extend hCg hq ht₀ hgrad
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, by linarith [min_le_left η₁ η₂], fun t ht => ⟨?_, ?_⟩⟩
  · exact G.derivativeBoundBefore_mono (by linarith [min_le_left η₁ η₂]) h₁
  · exact G.gradientBoundBefore_mono (by linarith [min_le_right η₁ η₂]) h₂

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
