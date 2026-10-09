import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.DerivativeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingCurvatureLifespan

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private theorem curvature_heat_subsolution_on {D : RealTimeInterval}
    (hcar : D.carrier ⊆ Ico a s) (hreg : D.regular ⊆ Ioo a s) :
    IsHeatPotSubsolutionOn D (flowG G.flow)
      (fun t x => rmTowerCost 3 0 * Real.sqrt (nablaKRm04NormSqIntrinsic G.flow 0 t x))
      (nablaKRm04NormSqIntrinsic G.flow 0) := by
  have hregsub : D.regular ×ˢ (univ : Set P.Carrier) ⊆
      (RealTimeInterval.closedOpen a s G.lt).regular ×ˢ univ :=
    prod_mono hreg subset_rfl
  refine
    { jointSmooth := (towerNorm_joint G.equation 0).mono hregsub
      jointCont := ?_
      sliceSmooth := fun t _ => nablaKNorm_smooth G.flow t 0
      timeDiff := ?_
      equation_le := ?_ }
  · have h := P.tensorFamily_normSq_continuousOn G.equation.smoothMetric.metricTensor_cont
      G.equation.rm04Cont
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero,
      SolutionOn.family_metric] using h.mono (prod_mono hcar subset_rfl)
  · intro t ht x
    have ht' := hreg ht
    obtain ⟨t1, hat1, ht1t⟩ := exists_between ht'.1
    have h := isHeatPotSubsolutionOn_nablaKRm04NormSqIntrinsic_of_solution
      (I := ThreeModel) G.equation hat1 (ht1t.trans ht'.2)
    exact h.timeDiff t ⟨ht1t, ht'.2⟩ x
  · intro t ht x
    have ht' := hreg ht
    obtain ⟨t1, hat1, ht1t⟩ := exists_between ht'.1
    have h := isHeatPotSubsolutionOn_nablaKRm04NormSqIntrinsic_of_solution
      (I := ThreeModel) G.equation hat1 (ht1t.trans ht'.2)
    simpa using h.equation_le t ⟨ht1t, ht'.2⟩ x

private theorem riemannNorm_sq_eq (t : ℝ) (x : P.Carrier) :
    G.riemannNorm t x ^ 2 = nablaKRm04NormSqIntrinsic G.flow 0 t x := by
  simpa only [riemannNorm, nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
    Nat.add_zero] using Real.sq_sqrt
    (normSq0S_nonneg (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x))

theorem riemannNorm_le_two_mul_of_forall_riemannNorm_le {K t₀ t : ℝ} (hK : 0 < K)
    (ht₀ : a ≤ t₀) (ht₀t : t₀ ≤ t) (hts : t < s) (hη : 2592 * K * (t - t₀) ≤ 1)
    (h : ∀ x : P.Carrier, G.riemannNorm t₀ x ≤ K) (x : P.Carrier) :
    G.riemannNorm t x ≤ 2 * K := by
  have hT0 : 0 ≤ t - t₀ := sub_nonneg.mpr ht₀t
  have hcost : rmTowerCost 3 0 = 2592 := by
    rw [rmTowerCost_zero]
    norm_num
  have hc : 0 < rmTowerCost 3 0 := by rw [hcost]; norm_num
  have hspan : t - t₀ ≤ curvatureDoublingSpan (rmTowerCost 3 0) K := by
    rw [curvatureDoublingSpan, hcost, le_div_iff₀ (by positivity)]
    linarith
  have hsub := curvature_heat_subsolution_on G
    (D := RealTimeInterval.closed t₀ (t₀ + (t - t₀)) (le_add_of_nonneg_right hT0))
    (fun r hr => ⟨ht₀.trans hr.1, by
      have := hr.2; simp only [add_sub_cancel] at this; exact this.trans_lt hts⟩)
    (fun r hr => ⟨ht₀.trans_lt hr.1, by
      have := hr.2; simp only [add_sub_cancel] at this; exact this.trans hts⟩)
  have hQ : ∀ y : P.Carrier, nablaKRm04NormSqIntrinsic G.flow 0 t₀ y ≤ K ^ 2 := by
    intro y
    rw [← riemannNorm_sq_eq]
    have hn : 0 ≤ G.riemannNorm t₀ y := Real.sqrt_nonneg _
    nlinarith [h y]
  have hd := curvature_norm_sq_doubling G.flow hc hK hT0 hspan hsub hQ t
    ⟨ht₀t, by linarith⟩ x
  rw [← riemannNorm_sq_eq] at hd
  have hn : 0 ≤ G.riemannNorm t x := Real.sqrt_nonneg _
  nlinarith

theorem scalar_time_derivWithin_continuousAt {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s) (y : P.Carrier) :
    ContinuousAt (fun t => derivWithin (fun v => G.flow.scalar v y) (Iic t) t) t₀ := by
  have hc := (G.flow.scalar_time_derivWithin_Iic_continuousOn G.equation).continuousAt
    (((RealTimeInterval.closedOpen a s G.lt).regular_isOpen.prod isOpen_univ).mem_nhds
      (show (t₀, y) ∈ (RealTimeInterval.closedOpen a s G.lt).regular ×ˢ univ from
        ⟨ht₀, mem_univ y⟩))
  exact ContinuousAt.comp (f := fun t : ℝ => (t, y)) hc (by fun_prop)

theorem scalar_continuousAt_time {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s) (y : P.Carrier) :
    ContinuousAt (fun t => G.flow.scalar t y) t₀ := by
  have hc := (scalar_joint G.flow G.equation).continuousOn.continuousAt
    (((RealTimeInterval.closedOpen a s G.lt).regular_isOpen.prod isOpen_univ).mem_nhds
      (show (t₀, y) ∈ (RealTimeInterval.closedOpen a s G.lt).regular ×ˢ univ from
        ⟨ht₀, mem_univ y⟩))
  exact ContinuousAt.comp (f := fun t : ℝ => (t, y)) hc (by fun_prop)

theorem scalarDifferential_continuousAt_time {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s) (y : P.Carrier)
    (v : TangentSpace ThreeModel y) :
    ContinuousAt (fun t => Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v) t₀ := by
  have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry fun (t : ℝ) (p : P.Carrier) => G.flow.scalar t p) (t₀, y) :=
    (scalar_joint G.flow G.equation).contMDiffAt
      (((RealTimeInterval.closedOpen a s G.lt).regular_isOpen.prod isOpen_univ).mem_nhds
        (show (t₀, y) ∈ (RealTimeInterval.closedOpen a s G.lt).regular ×ˢ univ from
          ⟨ht₀, mem_univ y⟩))
  have h := ContMDiffAt.mfderiv_apply (J := 𝓘(ℝ, ℝ)) (J' := 𝓘(ℝ, ℝ)) (I := ThreeModel)
    (I' := 𝓘(ℝ, ℝ)) (f := fun (t : ℝ) (p : P.Carrier) => G.flow.scalar t p)
    (g := fun _ : ℝ => y) (g₁ := id) (g₂ := fun _ : ℝ => (v : EuclideanSpace ℝ (Fin 3)))
    (x₀ := t₀) (m := 0) hf contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
  refine (h.continuousAt).congr (Eventually.of_forall fun t => ?_)
  simp only [id]
  erw [inTangentCoordinates_eq (I := ThreeModel) (I' := 𝓘(ℝ, ℝ)) _ _ _
    (mem_chart_source _ y) (by rw [chartAt_self_eq]; exact mem_univ _)]
  have htarget : (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange (achart ℝ (G.flow.scalar t y))
      (achart ℝ (G.flow.scalar t₀ y)) (G.flow.scalar t y) = (1 : ℝ →L[ℝ] ℝ) := by
    simp
  rw [htarget]
  change (mfderiv ThreeModel 𝓘(ℝ, ℝ) (fun p => G.flow.scalar t p) y)
    ((tangentBundleCore ThreeModel P.Carrier).coordChange (achart _ y) (achart _ y) y v) = _
  rw [(tangentBundleCore ThreeModel P.Carrier).coordChange_self (achart _ y) y
    (mem_achart_source _ y) v]
  rfl

theorem metric_inner_continuousAt_time {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s) (y : P.Carrier)
    (v : TangentSpace ThreeModel y) :
    ContinuousAt (fun t => (G.flow.base.metric t).inner y v v) t₀ := by
  obtain ⟨t₁, hat₁, ht₁⟩ := exists_between ht₀.1
  obtain ⟨t₂, ht₂, ht₂s⟩ := exists_between ht₀.2
  have hd := metricPDE_Icc G.flow G.equation (a := t₁) (b := t₂)
    (fun r hr => ⟨hat₁.le.trans hr.1, hr.2.trans_lt ht₂s⟩)
    (fun r hr => ⟨hat₁.trans hr.1, hr.2.trans ht₂s⟩) t₀ ⟨ht₁.le, ht₂.le⟩ y v v
  exact hd.continuousWithinAt.continuousAt (Icc_mem_nhds ht₁ ht₂)

theorem abs_derivWithin_scalar_le_of_forall_Ioo {C q t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s)
    (y : P.Carrier)
    (h : ∀ t ∈ Ioo a t₀, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    (hy : q < G.flow.scalar t₀ y) :
    |derivWithin (fun v => G.flow.scalar v y) (Iic t₀) t₀| ≤ C * G.flow.scalar t₀ y ^ 2 := by
  have hR := G.scalar_continuousAt_time ht₀ y
  have hf : ContinuousAt (fun t => |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| -
      C * G.flow.scalar t y ^ 2) t₀ :=
    (G.scalar_time_derivWithin_continuousAt ht₀ y).abs.sub (continuousAt_const.mul (hR.pow 2))
  have hev : ∀ᶠ t in 𝓝[<] t₀, |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| -
      C * G.flow.scalar t y ^ 2 ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT ht₀.1,
      nhdsWithin_le_nhds (hR.eventually (lt_mem_nhds hy))] with t ht hq
    linarith [h t ht hq]
  have hle := le_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds) hev
  linarith

theorem abs_scalarDifferential_le_of_forall_Ioo {C q t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a s)
    (y : P.Carrier)
    (h : ∀ t ∈ Ioo a t₀, q < G.flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
      |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
        C * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
          Real.sqrt ((G.flow.base.metric t).inner y v v))
    (hy : q < G.flow.scalar t₀ y) (v : TangentSpace ThreeModel y) :
    |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t₀ y v| ≤
      C * G.flow.scalar t₀ y * Real.sqrt (G.flow.scalar t₀ y) *
        Real.sqrt ((G.flow.base.metric t₀).inner y v v) := by
  have hR := G.scalar_continuousAt_time ht₀ y
  have hf : ContinuousAt (fun t =>
      |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| -
        C * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
          Real.sqrt ((G.flow.base.metric t).inner y v v)) t₀ :=
    (G.scalarDifferential_continuousAt_time ht₀ y v).abs.sub
      (((continuousAt_const.mul hR).mul hR.sqrt).mul
        (G.metric_inner_continuousAt_time ht₀ y v).sqrt)
  have hev : ∀ᶠ t in 𝓝[<] t₀,
      |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| -
        C * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
          Real.sqrt ((G.flow.base.metric t).inner y v v) ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT ht₀.1,
      nhdsWithin_le_nhds (hR.eventually (lt_mem_nhds hy))] with t ht hq
    linarith [h t ht hq v]
  have hle := le_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds) hev
  linarith

theorem abs_scalarDifferential_le_at_slice {C q t₀ : ℝ} (ht₀ : t₀ ∈ Ico a s)
    (hbefore : ∀ t ∈ Ioo a t₀, ∀ y : P.Carrier, q < G.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
          C * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
            Real.sqrt ((G.flow.base.metric t).inner y v v))
    (hstart : t₀ = a → ∀ y : P.Carrier, q < G.flow.scalar a y →
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow a y v| ≤
          C * G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) *
            Real.sqrt ((G.flow.base.metric a).inner y v v))
    (y : P.Carrier) (hy : q < G.flow.scalar t₀ y) (v : TangentSpace ThreeModel y) :
    |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t₀ y v| ≤
      C * G.flow.scalar t₀ y * Real.sqrt (G.flow.scalar t₀ y) *
        Real.sqrt ((G.flow.base.metric t₀).inner y v v) := by
  rcases ht₀.1.eq_or_lt with hat₀ | hat₀
  · subst hat₀
    exact hstart rfl y hy v
  · exact G.abs_scalarDifferential_le_of_forall_Ioo ⟨hat₀, ht₀.2⟩ y
      (fun t ht hq => hbefore t ht y hq) hy v

theorem normSq_rm_le_of_forall_riemannNorm_le {K t₀ t : ℝ} (hK : 0 < K)
    (ht₀ : a ≤ t₀) (ht₀t : t₀ ≤ t) (hts : t < s) (hη : 2592 * K * (t - t₀) ≤ 1)
    (h : ∀ x : P.Carrier, G.riemannNorm t₀ x ≤ K) (x : P.Carrier) :
    normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x) ≤ (2 * K) ^ 2 := by
  have hd := G.riemannNorm_le_two_mul_of_forall_riemannNorm_le hK ht₀ ht₀t hts hη h x
  have hsq := Real.sq_sqrt (normSq0S_nonneg (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x))
  have hn : 0 ≤ G.riemannNorm t x := Real.sqrt_nonneg _
  rw [riemannNorm] at hd hn
  nlinarith

theorem metric_inner_le_exp_one_mul_of_forall_riemannNorm_le {K t₀ t t₁ t₂ : ℝ} (hK : 0 < K)
    (ht₀ : a ≤ t₀) (hts : t < s) (hη : 2592 * K * (t - t₀) ≤ 1)
    (h : ∀ x : P.Carrier, G.riemannNorm t₀ x ≤ K) (h₁ : t₁ ∈ Icc t₀ t) (h₂ : t₂ ∈ Icc t₀ t)
    (x : P.Carrier) (v : TangentSpace ThreeModel x) :
    (G.flow.base.metric t₁).inner x v v ≤ Real.exp 1 * (G.flow.base.metric t₂).inner x v v := by
  have hcmp := (metric_inner_exp_bounds_of_curvature_bound G.flow G.equation (a := t₀) (b := t)
    (C := (2 * K) ^ 2) (fun r hr => ⟨ht₀.trans hr.1, hr.2.trans_lt hts⟩)
    (fun r hr => ⟨ht₀.trans_lt hr.1, hr.2.trans hts⟩) x
    (fun r hr => G.normSq_rm_le_of_forall_riemannNorm_le hK ht₀ hr.1 (hr.2.trans_lt hts)
      (by nlinarith [hr.2]) h x) h₁ h₂ v).2
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  have hsqrt : Real.sqrt ((2 * K) ^ 2) = 2 * K := Real.sqrt_sq (by positivity)
  rw [hdim, hsqrt] at hcmp
  have habs : |t₁ - t₂| ≤ t - t₀ := abs_sub_le_iff.mpr ⟨by linarith [h₁.2, h₂.1],
    by linarith [h₂.2, h₁.1]⟩
  have hexp : 2 * (3 : ℝ) ^ 2 * (2 * K) * |t₁ - t₂| ≤ 1 := by nlinarith
  exact hcmp.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
    (metric_inner_self_nonneg (G.flow.base.metric t₂) x v))

theorem riemannianBallOf_subset_of_forall_riemannNorm_le {K t₀ t t₁ t₂ : ℝ} (hK : 0 < K)
    (ht₀ : a ≤ t₀) (hts : t < s) (hη : 2592 * K * (t - t₀) ≤ 1)
    (h : ∀ x : P.Carrier, G.riemannNorm t₀ x ≤ K) (h₁ : t₁ ∈ Icc t₀ t) (h₂ : t₂ ∈ Icc t₀ t)
    (p : P.Carrier) (r : ℝ) :
    riemannianBallOf (G.flow.base.metric t₁) p r ⊆
      riemannianBallOf (G.flow.base.metric t₂) p (Real.sqrt (Real.exp 1) * r) :=
  DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul _ _ p (Real.exp_pos 1)
    (fun q _ v => G.metric_inner_le_exp_one_mul_of_forall_riemannNorm_le hK ht₀ hts hη h
      h₂ h₁ q v)

theorem scalar_le_of_forall_riemannNorm_le {K t₀ t : ℝ} (hK : 0 < K)
    (ht₀ : a ≤ t₀) (ht₀t : t₀ ≤ t) (hts : t < s) (hη : 2592 * K * (t - t₀) ≤ 1)
    (h : ∀ x : P.Carrier, G.riemannNorm t₀ x ≤ K) (x : P.Carrier) :
    G.flow.scalar t x ≤ 18 * K := by
  have hd := G.riemannNorm_le_two_mul_of_forall_riemannNorm_le hK ht₀ ht₀t hts hη h x
  have hs := scalar_abs_le_rm (I := ThreeModel) (G.flow.base.metric t) x
  have hdim : (Module.finrank ℝ (TangentSpace ThreeModel x) : ℝ) = 3 := by
    change (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3
    simp
  rw [hdim] at hs
  have hR : G.flow.scalar t x ≤ 3 ^ 2 * G.riemannNorm t x := (le_abs_self _).trans hs
  linarith

theorem exists_sliver_forward_comparison {K ζ t₀ : ℝ} (hK : 0 < K) (hζ : 0 < ζ)
    (ht₀ : t₀ ∈ Ico a s) (h : ∀ x : P.Carrier, G.riemannNorm t₀ x ≤ K) :
    ∃ η : ℝ, 0 < η ∧ η ≤ min 1 ζ / (2592 * K) ∧ t₀ + η < s ∧
      ∀ t ∈ Icc t₀ (t₀ + η),
        (∀ x : P.Carrier, G.riemannNorm t x ≤ 2 * K) ∧
        (∀ x : P.Carrier, G.flow.scalar t x ≤ 18 * K ∧ G.flow.scalar t x * η ≤ ζ) ∧
        (∀ (x : P.Carrier) (v : TangentSpace ThreeModel x),
          (G.flow.base.metric t).inner x v v ≤
              Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
            (G.flow.base.metric t₀).inner x v v ≤
              Real.exp 1 * (G.flow.base.metric t).inner x v v) ∧
        ∀ (p : P.Carrier) (r : ℝ),
          riemannianBallOf (G.flow.base.metric t₀) p r ⊆
              riemannianBallOf (G.flow.base.metric t) p (Real.sqrt (Real.exp 1) * r) ∧
            riemannianBallOf (G.flow.base.metric t) p r ⊆
              riemannianBallOf (G.flow.base.metric t₀) p (Real.sqrt (Real.exp 1) * r) := by
  have hm : 0 < min 1 ζ := lt_min one_pos hζ
  have hm1 : min 1 ζ ≤ 1 := min_le_left _ _
  have hmζ : min 1 ζ ≤ ζ := min_le_right _ _
  have hK' : 0 < 2592 * K := by positivity
  have hs : 0 < s - t₀ := sub_pos.mpr ht₀.2
  refine ⟨min (min 1 ζ / (2592 * K)) ((s - t₀) / 2), lt_min (div_pos hm hK') (by linarith),
    min_le_left _ _, by linarith [min_le_right (min 1 ζ / (2592 * K)) ((s - t₀) / 2)], ?_⟩
  set η := min (min 1 ζ / (2592 * K)) ((s - t₀) / 2)
  have hη₁ : η ≤ min 1 ζ / (2592 * K) := min_le_left _ _
  have hη₂ : η ≤ (s - t₀) / 2 := min_le_right _ _
  have hη0 : 0 ≤ η := le_min (div_pos hm hK').le (by linarith)
  have hKη : 2592 * K * η ≤ min 1 ζ := by
    rw [le_div_iff₀ hK'] at hη₁
    linarith
  intro t ht
  have hts : t < s := by linarith [ht.2]
  have hη : 2592 * K * (t - t₀) ≤ 1 := by nlinarith [ht.2]
  have hmem₀ : t₀ ∈ Icc t₀ t := ⟨le_rfl, ht.1⟩
  have hmem : t ∈ Icc t₀ t := ⟨ht.1, le_rfl⟩
  refine ⟨G.riemannNorm_le_two_mul_of_forall_riemannNorm_le hK ht₀.1 ht.1 hts hη h,
    fun x => ?_, fun x v => ⟨?_, ?_⟩, fun p r => ⟨?_, ?_⟩⟩
  · have hR := G.scalar_le_of_forall_riemannNorm_le hK ht₀.1 ht.1 hts hη h x
    refine ⟨hR, ?_⟩
    calc G.flow.scalar t x * η ≤ 18 * K * η := mul_le_mul_of_nonneg_right hR hη0
      _ ≤ ζ := by nlinarith
  · exact G.metric_inner_le_exp_one_mul_of_forall_riemannNorm_le hK ht₀.1 hts hη h hmem hmem₀
      x v
  · exact G.metric_inner_le_exp_one_mul_of_forall_riemannNorm_le hK ht₀.1 hts hη h hmem₀ hmem
      x v
  · exact G.riemannianBallOf_subset_of_forall_riemannNorm_le hK ht₀.1 hts hη h hmem₀ hmem p r
  · exact G.riemannianBallOf_subset_of_forall_riemannNorm_le hK ht₀.1 hts hη h hmem hmem₀ p r

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
