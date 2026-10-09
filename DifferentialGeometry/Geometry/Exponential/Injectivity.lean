import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Analysis.Calculus.Inverse.MovingImplicit
import DifferentialGeometry.Analysis.FunctionalAnalysis.BilinearCoercivity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Exponential.Inverse.Radius

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Operator (gradientFun inner_gradientFun)
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def shortBigons
    (F : E × E → E) (ell : E × E → Real) (a L : Real) :
    Set (E × E × E) :=
  {z |
    ‖z.1‖ ≤ a ∧
    ‖F (z.1, z.2.1)‖ ≤ a ∧
    F (z.1, z.2.1) = F (z.1, z.2.2) ∧
    ell (z.1, z.2.1) ≤ L ∧
    ell (z.1, z.2.2) ≤ L ∧
    z.2.1 ≠ z.2.2}

private theorem pinned_inj_nhds
    (F : E × E → E) (hF : ContDiff Real ∞ F)
    {x u : E}
    (hinj : Function.Injective (Analysis.partialFDeriv₂ F x u)) :
    ∃ U ∈ 𝓝 (x, u),
      Set.InjOn
        (fun z : E × E =>
          (F z, z.1))
        U := by
  classical
  have hsurj :
      Function.Surjective (Analysis.partialFDeriv₂ F x u) :=
    LinearMap.surjective_of_injective hinj
  let A : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective
      (Analysis.partialFDeriv₂ F x u)
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj)
  have hpartialInv :
      (Analysis.partialFDeriv₂ F x u).IsInvertible := by
    refine ⟨A, ?_⟩
    rfl
  let H : E × E → E × E := Analysis.pinnedRootMap F
  have hH : ContDiff Real ∞ H := by
    dsimp only [H, Analysis.pinnedRootMap]
    exact hF.prodMk contDiff_fst
  have hHInv :
      (fderiv Real H (x, u)).IsInvertible := by
    simpa only [H] using
      Analysis.pinnedFDeriv_inv
        ((hF.differentiable (by simp)).differentiableAt) hpartialInv
  rcases hHInv with ⟨B, hB⟩
  have hHD :
      HasFDerivAt H (B : (E × E) →L[Real] (E × E)) (x, u) := by
    rw [hB]
    exact ((hH.differentiable (by simp)).differentiableAt).hasFDerivAt
  let e := hH.contDiffAt.toOpenPartialHomeomorph H hHD (by simp)
  have hmem : (x, u) ∈ e.source := by
    exact hH.contDiffAt.mem_toOpenPartialHomeomorph_source hHD (by simp)
  refine ⟨e.source, e.open_source.mem_nhds hmem, ?_⟩
  have hinj := e.injOn
  change Set.InjOn H e.source at hinj
  dsimp only [H, Analysis.pinnedRootMap] at hinj
  exact hinj

private theorem shortBigons_compact
    (F : E × E → E) (ell : E × E → Real) (a L B : Real)
    (hF : Continuous F) (hell : Continuous ell)
    (hdiag :
      ∀ x u : E, ‖x‖ ≤ a → ell (x, u) ≤ L →
        ∃ U ∈ 𝓝 (x, u),
          Set.InjOn (fun z : E × E => (F z, z.1)) U)
    (hbound :
      ∀ z ∈ shortBigons F ell a L,
        ‖z.2.1‖ ≤ B ∧ ‖z.2.2‖ ≤ B) :
    IsCompact (shortBigons F ell a L) := by
  let pu : E × E × E → E × E := fun z => (z.1, z.2.1)
  let pv : E × E × E → E × E := fun z => (z.1, z.2.2)
  let Raw : Set (E × E × E) :=
    {z |
      ‖z.1‖ ≤ a ∧
      ‖F (pu z)‖ ≤ a ∧
      F (pu z) = F (pv z) ∧
      ell (pu z) ≤ L ∧
      ell (pv z) ≤ L}
  have hpu : Continuous pu :=
    continuous_fst.prodMk continuous_snd.fst
  have hpv : Continuous pv :=
    continuous_fst.prodMk continuous_snd.snd
  have hRawClosed : IsClosed Raw := by
    have hxClosed : IsClosed {z : E × E × E | ‖z.1‖ ≤ a} :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    have hyClosed : IsClosed {z : E × E × E | ‖F (pu z)‖ ≤ a} :=
      isClosed_le (continuous_norm.comp (hF.comp hpu)) continuous_const
    have heqClosed : IsClosed {z : E × E × E | F (pu z) = F (pv z)} :=
      isClosed_eq (hF.comp hpu) (hF.comp hpv)
    have huClosed : IsClosed {z : E × E × E | ell (pu z) ≤ L} :=
      isClosed_le (hell.comp hpu) continuous_const
    have hvClosed : IsClosed {z : E × E × E | ell (pv z) ≤ L} :=
      isClosed_le (hell.comp hpv) continuous_const
    rw [show Raw =
        {z : E × E × E | ‖z.1‖ ≤ a} ∩
          ({z : E × E × E | ‖F (pu z)‖ ≤ a} ∩
            ({z : E × E × E | F (pu z) = F (pv z)} ∩
              ({z : E × E × E | ell (pu z) ≤ L} ∩
                {z : E × E × E | ell (pv z) ≤ L}))) by
      ext z
      simp only [Raw, Set.mem_ofPred_eq, Set.mem_inter_iff]]
    exact hxClosed.inter
      (hyClosed.inter (heqClosed.inter (huClosed.inter hvClosed)))
  have hBadRaw :
      shortBigons F ell a L =
        Raw ∩ {z : E × E × E | z.2.1 ≠ z.2.2} := by
    ext z
    simp only [shortBigons, Raw, pu, pv, Set.mem_ofPred_eq,
      Set.mem_inter_iff]
    tauto
  have hBadClosed : IsClosed (shortBigons F ell a L) := by
    rw [hBadRaw, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    change z ∉ Raw ∩ {w : E × E × E | w.2.1 ≠ w.2.2} at hz
    by_cases hzRaw : z ∈ Raw
    · have huv : z.2.1 = z.2.2 := by
        by_contra hne
        exact hz ⟨hzRaw, hne⟩
      obtain ⟨U, hU, hUinj⟩ :=
        hdiag z.1 z.2.1 hzRaw.1 hzRaw.2.2.2.1
      have hUu : U ∈ 𝓝 (pu z) := by
        simpa only [pu] using hU
      have hUv : U ∈ 𝓝 (pv z) := by
        simpa only [pu, pv, huv] using hU
      have hV :
          {w : E × E × E | pu w ∈ U ∧ pv w ∈ U} ∈ 𝓝 z :=
        Filter.inter_mem (hpu.continuousAt hUu) (hpv.continuousAt hUv)
      refine Filter.mem_of_superset hV ?_
      intro w hw
      change w ∉ Raw ∩ {r : E × E × E | r.2.1 ≠ r.2.2}
      intro hwBad
      have hpairs : pu w = pv w := by
        apply hUinj hw.1 hw.2
        apply Prod.ext
        · exact hwBad.1.2.2.1
        · rfl
      exact hwBad.2 (congrArg Prod.snd hpairs)
    · have hRawCompl : Rawᶜ ∈ 𝓝 z :=
        hRawClosed.isOpen_compl.mem_nhds hzRaw
      refine Filter.mem_of_superset hRawCompl ?_
      intro w hw
      change w ∉ Raw ∩ {r : E × E × E | r.2.1 ≠ r.2.2}
      exact fun h => hw h.1
  let Box : Set (E × E × E) :=
    Metric.closedBall (0 : E) a ×ˢ
      (Metric.closedBall (0 : E) B ×ˢ Metric.closedBall (0 : E) B)
  have hBox : IsCompact Box :=
    (isCompact_closedBall (0 : E) a).prod
      ((isCompact_closedBall (0 : E) B).prod
        (isCompact_closedBall (0 : E) B))
  apply hBox.of_isClosed_subset hBadClosed
  intro z hz
  have hb := hbound z hz
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb.2

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem periodic_core_bound
    {γu γv : Real → E} {a c d T : Real}
    (hTdef : T = 1 + d) (hcPos : 0 < c) (hcd : c * d = 1)
    (hjoin : ∀ s : Real, γu (s + 1) = γv (1 - c * s))
    (hperiod : ∀ s : Real, γu (s + T) = γu s)
    (hcoreU : ∀ t ∈ Set.Icc (0 : Real) 1, ‖γu t‖ ≤ a)
    (hcoreV : ∀ t ∈ Set.Icc (0 : Real) 1, ‖γv t‖ ≤ a) :
    ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γu t‖ ≤ a := by
  have honeCore :
      ∀ t ∈ Set.Icc (0 : Real) T, ‖γu t‖ ≤ a := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · exact hcoreU t ⟨ht.1, ht1⟩
    · have hs0 : 0 ≤ t - 1 := sub_nonneg.mpr (le_of_not_ge ht1)
      have hsd : t - 1 ≤ d := by
        have ht' : t ≤ 1 + d := by
          simpa only [hTdef] using ht.2
        exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using ht')
      have hcs : 0 ≤ c * (t - 1) :=
        mul_nonneg hcPos.le hs0
      have hcs1 : c * (t - 1) ≤ 1 := by
        calc
          c * (t - 1) ≤ c * d :=
            mul_le_mul_of_nonneg_left hsd hcPos.le
          _ = 1 := hcd
      have hj := hjoin (t - 1)
      have htime : (t - 1) + 1 = t := by ring
      rw [htime] at hj
      rw [hj]
      exact hcoreV (1 - c * (t - 1))
        ⟨sub_nonneg.mpr hcs1, sub_le_self 1 hcs⟩
  intro t ht
  by_cases htT : t ≤ T
  · exact honeCore t ⟨ht.1.le, htT⟩
  · have hred : t - T ∈ Set.Icc (0 : Real) T := by
      constructor
      · exact sub_nonneg.mpr (le_of_not_ge htT)
      · apply sub_le_iff_le_add.mpr
        simpa only [two_mul] using ht.2.le
    have hp := hperiod (t - T)
    have heq : (t - T) + T = t := by ring
    rw [heq] at hp
    rw [hp]
    exact honeCore (t - T) hred

variable [NeZero (Module.finrank ℝ E)]

private theorem exists_nonzero_minimizing_bigon_of_loop
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    (∀ x y q : E, ‖x‖ ≤ a → ‖y‖ ≤ a →
      Real.sqrt (gExt.inner x q q) ≤ L →
      intrinsicGeodesic gExt hExt x q 1 = y →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x q t‖ ≤ a) →
    let F : E × E → E := fun z =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
    let ell : E × E → Real := fun z =>
      Real.sqrt (gExt.inner z.1 z.2 z.2)
    let total : E × E × E → Real := fun z =>
      ell (z.1, z.2.1) + ell (z.1, z.2.2)
    ∀ (z₀ : E × E × E),
      IsMinOn total (shortBigons F ell a L) z₀ →
      total z₀ < 2 * L →
      ∀ (x₀ q₀ : E), ‖x₀‖ ≤ a →
        ell (x₀, q₀) ≤ L → q₀ ≠ 0 →
        F (x₀, q₀) = x₀ → total z₀ = ell (x₀, q₀) →
        ∃ z₁ : E × E × E,
          z₁ ∈ shortBigons F ell a L ∧
          IsMinOn total (shortBigons F ell a L) z₁ ∧
          z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
          ell (z₁.1, z₁.2.1) < L ∧
          ell (z₁.1, z₁.2.2) < L := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  intro hcore
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  intro z₀ hmin htotalLt x₀ q₀ hx₀ hqL hqne hloop htot
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ q₀
  let m : E := γ (1 / 2)
  let w : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ (1 / 2) (1 : Real)
  have hγ0 : γ 0 = x₀ :=
    intrinsicGeodesic_zero
      (I := 𝓘(Real, E)) gExt hExt x₀ q₀
  have hγ1 : γ 1 = x₀ := by
    dsimp only [γ]
    with_unfolding_all
      change expMapIntrinsic (I := 𝓘(Real, E))
        gExt hExt x₀ q₀ = x₀
      exact hloop
  have hm : ‖m‖ ≤ a := by
    exact hcore x₀ x₀ q₀ hx₀ hx₀ hqL hγ1 (1 / 2) (by constructor <;> norm_num)
  have hcont :
      (fun s : Real => γ (s + 1 / 2)) =
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w := by
    simpa only [γ, m, w] using
      intrinsicGeodesic_continuation
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ (1 / 2)
  have hplus : F (m, (1 / 2 : Real) • w) = x₀ := by
    change
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
        m ((1 / 2 : Real) • w) 1 = x₀
    have hscale :
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
            m ((1 / 2 : Real) • w) 1 =
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w (1 / 2) :=
      intrinsicGeodesic_smul
        (I := 𝓘(Real, E)) gExt hExt m w (1 / 2)
    rw [hscale]
    rw [← congrFun hcont (1 / 2)]
    norm_num
    exact hγ1
  have hminus : F (m, (-1 / 2 : Real) • w) = x₀ := by
    change
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
        m ((-1 / 2 : Real) • w) 1 = x₀
    have hscale :
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
            m ((-1 / 2 : Real) • w) 1 =
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w (-1 / 2) :=
      intrinsicGeodesic_smul
        (I := 𝓘(Real, E)) gExt hExt m w (-1 / 2)
    rw [hscale]
    rw [← congrFun hcont (-1 / 2)]
    norm_num
    exact hγ0
  have hspeed :
      gExt.inner m w w = gExt.inner x₀ q₀ q₀ := by
    with_unfolding_all
      exact intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ (1 / 2)
  have hellPlus :
      ell (m, (1 / 2 : Real) • w) =
        (1 / 2 : Real) * ell (x₀, q₀) := by
    simp only [ell]
    have hscale :
        Real.sqrt
            (gExt.inner m ((1 / 2 : Real) • w)
              ((1 / 2 : Real) • w)) =
          (1 / 2 : Real) * Real.sqrt (gExt.inner m w w) :=
      sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt m (by norm_num) w
    rw [hscale, hspeed]
  have hellMinus :
      ell (m, (-1 / 2 : Real) • w) =
        (1 / 2 : Real) * ell (x₀, q₀) := by
    simp only [ell]
    rw [show (-1 / 2 : Real) • w =
        (1 / 2 : Real) • (-w) by module]
    have hscale :
        Real.sqrt
            (gExt.inner m ((1 / 2 : Real) • (-w))
              ((1 / 2 : Real) • (-w))) =
          (1 / 2 : Real) * Real.sqrt (gExt.inner m (-w) (-w)) :=
      sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt m (by norm_num) (-w)
    have hneg : gExt.inner m (-w) (-w) = gExt.inner m w w := by
      have h :=
        gInner_smul_self
          (I := 𝓘(Real, E)) gExt m (-1 : Real) w
      rw [show (-w : E) = (-1 : Real) • w by
        exact (neg_one_smul Real w).symm]
      calc
        _ = (-1 : Real) ^ 2 * gExt.inner m w w := h
        _ = gExt.inner m w w := by norm_num
    rw [hscale, hneg, hspeed]
  have hwne : w ≠ 0 := by
    have hvelne := intrinsicGeo_velocity_ne
      (I := 𝓘(Real, E)) gExt hExt x₀ q₀ hqne (1 / 2)
    intro hw
    apply hvelne
    with_unfolding_all
      exact hw
  have hplusNe : (1 / 2 : Real) • w ≠ 0 :=
    smul_ne_zero (by norm_num) hwne
  have hminusNe : (-1 / 2 : Real) • w ≠ 0 :=
    smul_ne_zero (by norm_num) hwne
  let z₁ : E × E × E :=
    (m, ((1 / 2 : Real) • w, (-1 / 2 : Real) • w))
  have hz₁ : z₁ ∈ shortBigons F ell a L := by
    change
      ‖m‖ ≤ a ∧
      ‖F (m, (1 / 2 : Real) • w)‖ ≤ a ∧
      F (m, (1 / 2 : Real) • w) = F (m, (-1 / 2 : Real) • w) ∧
      ell (m, (1 / 2 : Real) • w) ≤ L ∧
      ell (m, (-1 / 2 : Real) • w) ≤ L ∧
      (1 / 2 : Real) • w ≠ (-1 / 2 : Real) • w
    refine ⟨hm, ?_, hplus.trans hminus.symm, ?_, ?_, ?_⟩
    · rw [hplus]
      exact hx₀
    · rw [hellPlus]
      have hqnonneg : 0 ≤ ell (x₀, q₀) := Real.sqrt_nonneg _
      exact (mul_le_of_le_one_left hqnonneg (by norm_num)).trans hqL
    · rw [hellMinus]
      have hqnonneg : 0 ≤ ell (x₀, q₀) := Real.sqrt_nonneg _
      exact (mul_le_of_le_one_left hqnonneg (by norm_num)).trans hqL
    · intro heq
      let q : E := (1 / 2 : Real) • w
      have hqneg : q = -q := by
        calc
          q = (-1 / 2 : Real) • w := heq
          _ = -q := by simp only [q]; module
      have htwo : (2 : Real) • q = 0 := by
        rw [two_smul]
        nth_rewrite 1 [hqneg]
        exact neg_add_cancel q
      have hq0 : q = 0 :=
        (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      exact hplusNe (by simpa only [q] using hq0)
  have htotal₁ : total z₁ = total z₀ := by
    calc
      total z₁ =
          ell (m, (1 / 2 : Real) • w) +
            ell (m, (-1 / 2 : Real) • w) := by
              rfl
      _ = ell (x₀, q₀) := by
        rw [hellPlus, hellMinus]
        ring
      _ = total z₀ := htot.symm
  have hmin₁ : IsMinOn total (shortBigons F ell a L) z₁ := by
    apply isMinOn_iff.mpr
    intro z hz
    rw [htotal₁]
    exact (isMinOn_iff.mp hmin) z hz
  have hqLt : ell (x₀, q₀) < 2 * L := by
    have hqLtRaw := htotalLt
    rw [htot] at hqLtRaw
    simpa only [ell] using hqLtRaw
  have hplusLt : ell (m, (1 / 2 : Real) • w) < L := by
    rw [hellPlus]
    calc
      (1 / 2 : Real) * ell (x₀, q₀) < (1 / 2 : Real) * (2 * L) :=
        mul_lt_mul_of_pos_left hqLt (by norm_num)
      _ = L := by ring
  have hminusLt : ell (m, (-1 / 2 : Real) • w) < L := by
    rw [hellMinus]
    calc
      (1 / 2 : Real) * ell (x₀, q₀) < (1 / 2 : Real) * (2 * L) :=
        mul_lt_mul_of_pos_left hqLt (by norm_num)
      _ = L := by ring
  exact
    ⟨z₁, hz₁, hmin₁,
      by simpa only [z₁] using hplusNe,
      by simpa only [z₁] using hminusNe,
      by simpa only [z₁] using hplusLt,
      by simpa only [z₁] using hminusLt⟩

private theorem branch_radius_reverse_derivative
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    ∀ (x u v : E) (Br : ExponentialInverseBranch gExt hExt x),
      v ∈ Br.hom.source → v ≠ 0 →
      expMapIntrinsic gExt hExt x u = expMapIntrinsic gExt hExt x v →
      HasDerivAt
        (fun s : ℝ => branchRadius gExt Br (intrinsicGeodesic gExt hExt x u (1 - s)))
        (gExt.inner (intrinsicGeodesic gExt hExt x u 1)
          ((Real.sqrt (gExt.inner x v v))⁻¹ •
            mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (intrinsicGeodesic gExt hExt x v) 1 (1 : ℝ))
          (-mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (intrinsicGeodesic gExt hExt x u) 1 (1 : ℝ))) 0 := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  intro x₀ u₀ v₀ Br hvSource hzv huvEnd
  let y₀ : E := expMapIntrinsic gExt hExt x₀ u₀
  let lv : ℝ := Real.sqrt (gExt.inner x₀ v₀ v₀)
  let γu : ℝ → E := intrinsicGeodesic gExt hExt x₀ u₀
  let U : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γu 1 (1 : ℝ)
  let V : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
    (intrinsicGeodesic gExt hExt x₀ v₀) 1 (1 : ℝ)
  have hγu1 : γu 1 = y₀ := rfl
  have hyvExp : y₀ = expMapIntrinsic gExt hExt x₀ v₀ := huvEnd
  have hvPos : 0 < gExt.inner x₀ v₀ v₀ :=
    gExt.pos x₀ v₀ hzv
  have hbrDiff :
      MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
        (branchRadius (I := 𝓘(Real, E)) gExt Br) y₀ := by
    rw [hyvExp]
    exact branchRadius_diff
      (I := 𝓘(Real, E)) Br hvSource hvPos
  let η : Real → E := fun s => γu (1 - s)
  have hη0 : η 0 = y₀ := by
    simpa only [η, sub_zero] using hγu1
  have hηInf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ η := by
    convert
      (intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x₀ u₀).comp
          (contMDiff_const.sub contMDiff_id) using 1
    all_goals rfl
  have hηDiff :
      MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) η 0 :=
    hηInf.contMDiffAt.mdifferentiableAt (by simp)
  have hηVelocity :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E) η 0 (1 : Real) = -U := by
    have h :=
      curveVelocity_comp_affine
        (I := 𝓘(Real, E)) γu (-1) 1 0
          ((intrinsicGeodesic_contMDiff
            (I := 𝓘(Real, E)) gExt hExt x₀ u₀).contMDiffAt
              |>.mdifferentiableAt (by simp))
    have hfun :
        η = fun s : Real => γu ((-1 : Real) * s + 1) := by
      funext s
      dsimp only [η]
      congr 1
      ring
    rw [hfun]
    have harg : (-1 : Real) * 0 + 1 = 1 := by norm_num
    rw [harg] at h
    with_unfolding_all
      change Variation.curveVelocity (I := 𝓘(Real, E))
        (fun s : Real => γu ((-1 : Real) * s + 1)) 0 =
          -Variation.curveVelocity (I := 𝓘(Real, E)) γu 1
    rw [neg_one_smul (R := Real)] at h
    with_unfolding_all
      exact h
  have hgrad :
      gradientFun (I := 𝓘(Real, E)) gExt
          (branchRadius (I := 𝓘(Real, E)) gExt Br) y₀ =
        lv⁻¹ • V := by
    rw [hyvExp]
    convert grad_branchRadius
      (I := 𝓘(Real, E)) Br hvSource hvPos using 1
    all_goals rfl
  have hbrDeriv :
      HasDerivAt
        (fun s : Real =>
          branchRadius (I := 𝓘(Real, E)) gExt Br (η s))
        (gExt.inner y₀ (lv⁻¹ • V) (-U)) 0 := by
    have hbrDiffη :
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (branchRadius (I := 𝓘(Real, E)) gExt Br) (η 0) := by
      rw [hη0]
      exact hbrDiff
    have hηVelocityOne :
        mfderiv 𝓘(Real, Real) 𝓘(Real, E) η 0
            (DifferentialGeometry.Analysis.Calculus.realTangentOne 0) =
          -U := by
      with_unfolding_all exact hηVelocity
    have hraw :=
      DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
        𝓘(Real, E)
        (branchRadius (I := 𝓘(Real, E)) gExt Br) η 0
        hbrDiffη hηDiff
    refine hraw.congr_deriv ?_
    change mvfderiv 𝓘(Real, E) (branchRadius gExt Br) (η 0)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) η 0
        (DifferentialGeometry.Analysis.Calculus.realTangentOne 0)) = _
    rw [hηVelocityOne]
    calc
      _ = gExt.inner (η 0) (gradientFun gExt (branchRadius gExt Br) (η 0)) (-U) :=
        (inner_gradientFun (I := 𝓘(Real, E)) gExt (branchRadius gExt Br) (η 0) (-U)).symm
      _ = gExt.inner y₀ (lv⁻¹ • V) (-U) := by
        exact (congrArg (fun y : E =>
          gExt.inner y (gradientFun gExt (branchRadius gExt Br) y) (-U)) hη0).trans
            (congrArg (fun w => gExt.inner y₀ w (-U)) hgrad)
  exact hbrDeriv

private theorem eventual_competing_bigon
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    let F : E × E → E := fun z =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
    let ell : E × E → Real := fun z =>
      Real.sqrt (gExt.inner z.1 z.2 z.2)
    ∀ (z : E × E × E) (hz : z ∈ shortBigons F ell a L)
      (hzv : z.2.2 ≠ 0)
      (hzvLt : ell (z.1, z.2.2) < L),
      (∀ t ∈ Icc (0 : ℝ) 1,
        ‖intrinsicGeodesic gExt hExt z.1 z.2.1 t‖ ≤ a) →
      ∀ (Br : ExponentialInverseBranch gExt hExt z.1),
        z.2.2 ∈ Br.hom.source →
        ∀ᶠ s in 𝓝[>] (0 : ℝ),
          (z.1, (1 - s) • z.2.1,
            Br.inv (intrinsicGeodesic gExt hExt z.1 z.2.1 (1 - s))) ∈ shortBigons F ell a L := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  intro z hz hzv hzvLt hcore Br hvSource
  let x₀ : E := z.1
  let u₀ : E := z.2.1
  let v₀ : E := z.2.2
  let y₀ : E := F (x₀, u₀)
  let lu : Real := ell (x₀, u₀)
  let lv : Real := ell (x₀, v₀)
  let γu : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ u₀
  have hx₀ : ‖x₀‖ ≤ a := hz.1
  have huvEnd : F (x₀, u₀) = F (x₀, v₀) := hz.2.2.1
  have huLe : lu ≤ L := hz.2.2.2.1
  have huv : u₀ ≠ v₀ := hz.2.2.2.2.2
  have hγu1 : γu 1 = y₀ := by
    rfl
  have hyvExp :
      y₀ =
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x₀ v₀ := by
    simpa only [y₀, F] using huvEnd
  have hyDom : y₀ ∈ Br.dom := by
    have hyHom : y₀ = Br.hom v₀ :=
      hyvExp.trans (Br.hom_eq hvSource)
    rw [hyHom]
    exact Br.hom.map_source hvSource
  have hInvY : Br.inv y₀ = v₀ := by
    rw [hyvExp]
    exact Br.left_inv hvSource
  have hbrY :
      branchRadius (I := 𝓘(Real, E)) gExt Br y₀ = lv := by
    rw [hyvExp]
    simpa only [lv, ell] using
      branchRadius_exp (I := 𝓘(Real, E)) Br hvSource
  have hvPos : 0 < gExt.inner x₀ v₀ v₀ := gExt.pos x₀ v₀ hzv
  have hbrDiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (branchRadius gExt Br) y₀ := by
    rw [hyvExp]
    exact branchRadius_diff Br hvSource hvPos
  let η : ℝ → E := fun s => γu (1 - s)
  have hη0 : η 0 = y₀ := by simpa only [η, sub_zero] using hγu1
  have hηInf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η := by
    convert (intrinsicGeodesic_contMDiff gExt hExt x₀ u₀).comp
      (contMDiff_const.sub contMDiff_id) using 1 <;> rfl
  have hηCont : ContinuousAt η 0 := hηInf.continuous.continuousAt
  have hdomEv : ∀ᶠ s in 𝓝 (0 : Real), η s ∈ Br.dom := by
    have hyTarget : y₀ ∈ Br.hom.target := by
      with_unfolding_all exact hyDom
    exact hηCont
      (Br.hom.open_target.mem_nhds (by simpa only [hη0] using hyTarget))
  have hbrCont :
      ContinuousAt
        (fun s : Real =>
          branchRadius (I := 𝓘(Real, E)) gExt Br (η s)) 0 :=
    (by
      have hbrDiffη :
          MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
            (branchRadius (I := 𝓘(Real, E)) gExt Br) (η 0) := by
        rw [hη0]
        exact hbrDiff
      exact hbrDiffη.continuousAt.comp hηCont)
  have hbrLtEv :
      ∀ᶠ s in 𝓝 (0 : Real),
        branchRadius (I := 𝓘(Real, E)) gExt Br (η s) < L := by
    exact hbrCont
      (Iio_mem_nhds (by simpa only [hη0, hbrY] using hzvLt))
  have hInvDiff :
      ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞ Br.inv y₀ :=
    Br.inv_contMDiffOn.contMDiffAt (Br.hom.open_target.mem_nhds hyDom)
  have hleftCont :
      ContinuousAt (fun s : Real => (1 - s) • u₀) 0 :=
    (continuousAt_const.sub continuousAt_id).smul continuousAt_const
  have hrightCont :
      ContinuousAt (fun s : Real => Br.inv (η s)) 0 :=
    (by
      have hInvDiffη :
          ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞ Br.inv (η 0) := by
        rw [hη0]
        exact hInvDiff
      exact hInvDiffη.continuousAt.comp hηCont)
  have hneEv :
      ∀ᶠ s in 𝓝 (0 : Real),
        (1 - s) • u₀ ≠ Br.inv (η s) := by
    apply (hleftCont.ne_iff_eventually_ne hrightCont).1
    simpa only [sub_zero, one_smul, hη0, hInvY] using huv
  have hbadEv :
      ∀ᶠ s in 𝓝[>] (0 : Real),
        (x₀, (1 - s) • u₀, Br.inv (η s)) ∈
          shortBigons F ell a L := by
    filter_upwards [
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hdomEv,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hbrLtEv,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hneEv,
      self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (show (0 : Real) < 1 by norm_num))]
        with s hsDom hsBr hsNe hsPos hsOne
    change 0 < s at hsPos
    have hsIcc : 1 - s ∈ Set.Icc (0 : Real) 1 := by
      exact ⟨sub_nonneg.mpr hsOne.le, sub_le_self 1 hsPos.le⟩
    have hηCore : ‖η s‖ ≤ a := by
      exact hcore (1 - s) hsIcc
    have hfirst : F (x₀, (1 - s) • u₀) = η s := by
      change
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
          x₀ ((1 - s) • u₀) 1 = γu (1 - s)
      exact intrinsicGeodesic_smul
        (I := 𝓘(Real, E)) gExt hExt x₀ u₀ (1 - s)
    have hsecond : F (x₀, Br.inv (η s)) = η s := by
      exact Br.right_inv hsDom
    have hellFirst :
        ell (x₀, (1 - s) • u₀) = (1 - s) * lu := by
      exact sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt x₀
          (sub_nonneg.mpr hsOne.le) u₀
    have hfirstLe : ell (x₀, (1 - s) • u₀) ≤ L := by
      rw [hellFirst]
      have hluNonneg : 0 ≤ lu := Real.sqrt_nonneg _
      have hscaleLe : (1 - s) * lu ≤ lu := by
        have hsle : 1 - s ≤ 1 := sub_le_self 1 hsPos.le
        exact mul_le_of_le_one_left hluNonneg hsle
      exact hscaleLe.trans huLe
    have hsecondLt : ell (x₀, Br.inv (η s)) < L := by
      with_unfolding_all exact hsBr
    change
      ‖x₀‖ ≤ a ∧
      ‖F (x₀, (1 - s) • u₀)‖ ≤ a ∧
      F (x₀, (1 - s) • u₀) = F (x₀, Br.inv (η s)) ∧
      ell (x₀, (1 - s) • u₀) ≤ L ∧
      ell (x₀, Br.inv (η s)) ≤ L ∧
      (1 - s) • u₀ ≠ Br.inv (η s)
    exact
      ⟨hx₀, by simpa only [hfirst] using hηCore,
        hfirst.trans hsecond.symm, hfirstLe, hsecondLt.le, hsNe⟩
  exact hbadEv

private theorem first_variation_nonneg
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    let F : E × E → E := fun z =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
    let ell : E × E → Real := fun z =>
      Real.sqrt (gExt.inner z.1 z.2 z.2)
    let total : E × E × E → Real := fun z =>
      ell (z.1, z.2.1) + ell (z.1, z.2.2)
    ∀ z : E × E × E, z ∈ shortBigons F ell a L →
      IsMinOn total (shortBigons F ell a L) z →
      z.2.2 ≠ 0 → ell (z.1, z.2.2) < L →
      (∀ t ∈ Icc (0 : ℝ) 1,
        ‖intrinsicGeodesic gExt hExt z.1 z.2.1 t‖ ≤ a) →
      (¬ IsConjVec gExt hExt z.1 z.2.2) →
      0 ≤ -ell (z.1, z.2.1) +
        gExt.inner (intrinsicGeodesic gExt hExt z.1 z.2.1 1)
          ((ell (z.1, z.2.2))⁻¹ •
            mfderiv 𝓘(Real, Real) 𝓘(Real, E)
              (intrinsicGeodesic gExt hExt z.1 z.2.2) 1 (1 : Real))
          (-mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic gExt hExt z.1 z.2.1) 1 (1 : Real)) := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  intro z hz hzmin hzv hzvLt hcore hvNot
  let x₀ : E := z.1
  let u₀ : E := z.2.1
  let v₀ : E := z.2.2
  let y₀ : E := F (x₀, u₀)
  let lu : Real := ell (x₀, u₀)
  let lv : Real := ell (x₀, v₀)
  let γu : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ u₀
  let U : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γu 1 (1 : Real)
  let V : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E)
      (intrinsicGeodesic gExt hExt x₀ v₀) 1 (1 : Real)
  have huvEnd : F (x₀, u₀) = F (x₀, v₀) := hz.2.2.1
  have hγu1 : γu 1 = y₀ := by
    rfl
  have hyvExp :
      y₀ =
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x₀ v₀ := by
    simpa only [y₀, F] using huvEnd
  have hbranch : ∃ B : ExponentialInverseBranch gExt hExt x₀, v₀ ∈ B.hom.source := by
    with_unfolding_all
      exact branch_of_not_conj
        (I := 𝓘(Real, E)) gExt hExt (p := x₀) (u := v₀) hvNot
  obtain ⟨Br, hvSource⟩ := hbranch
  have hbrY :
      branchRadius (I := 𝓘(Real, E)) gExt Br y₀ = lv := by
    rw [hyvExp]
    simpa only [lv, ell] using
      branchRadius_exp (I := 𝓘(Real, E)) Br hvSource
  let η : ℝ → E := fun s => γu (1 - s)
  have hη0 : η 0 = y₀ := by simpa only [η, sub_zero] using hγu1
  have hbrDeriv : HasDerivAt (fun s : ℝ => branchRadius gExt Br (η s))
      (gExt.inner y₀ (lv⁻¹ • V) (-U)) 0 :=
    branch_radius_reverse_derivative gExt hcomplete x₀ u₀ v₀ Br hvSource hzv huvEnd
  have hbadEv : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (x₀, (1 - s) • u₀, Br.inv (η s)) ∈ shortBigons F ell a L :=
    eventual_competing_bigon gExt hcomplete z hz hzv hzvLt hcore Br hvSource
  let φ : Real → Real :=
    (fun s => (1 - s) * lu) +
      fun s => branchRadius (I := 𝓘(Real, E)) gExt Br (η s)
  have hφ0 : φ 0 = total z := by
    dsimp only [φ, total, x₀, u₀, v₀, lu, lv]
    change (1 - 0) * ell (z.1, z.2.1) +
        branchRadius (I := 𝓘(Real, E)) gExt Br (η 0) =
      ell (z.1, z.2.1) + ell (z.1, z.2.2)
    rw [hη0, hbrY]
    ring
  have hminEv : ∀ᶠ s in 𝓝[>] (0 : Real), φ 0 ≤ φ s := by
    filter_upwards [
      hbadEv,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (show (0 : Real) < 1 by norm_num))]
        with s hsBad hsOne
    let zs : E × E × E :=
      (x₀, (1 - s) • u₀, Br.inv (η s))
    have hzsMin := (isMinOn_iff.mp hzmin) zs hsBad
    have hellFirst :
        ell (x₀, (1 - s) • u₀) = (1 - s) * lu := by
      exact sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt x₀
          (sub_nonneg.mpr hsOne.le) u₀
    calc
      φ 0 = total z := hφ0
      _ ≤ total zs := hzsMin
      _ = φ s := by
        dsimp only [total, zs, φ]
        rw [hellFirst]
        rfl
  have hlin :=
    (((hasDerivAt_const (x := (0 : Real)) (c := (1 : Real))).sub
      (hasDerivAt_id (x := (0 : Real)))).mul_const lu).congr_deriv
        (show (0 - 1) * lu = -lu by ring)
  have hφDeriv := hlin.add hbrDeriv
  have hslope :
      ∀ᶠ s in 𝓝[>] (0 : Real),
        0 ≤ s⁻¹ • (φ (0 + s) - φ 0) := by
    filter_upwards [hminEv, self_mem_nhdsWithin] with s hsMin hsPos
    simpa only [zero_add, smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr hsPos.le) (sub_nonneg.mpr hsMin)
  have hderNonneg :
      0 ≤ -lu + gExt.inner y₀ (lv⁻¹ • V) (-U) :=
    ge_of_tendsto hφDeriv.tendsto_slope_zero_right hslope
  exact hderNonneg

private theorem terminal_velocity_eq_neg_of_minimal_bigon
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    let F : E × E → E := fun z =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
    let ell : E × E → Real := fun z =>
      Real.sqrt (gExt.inner z.1 z.2 z.2)
    let total : E × E × E → Real := fun z =>
      ell (z.1, z.2.1) + ell (z.1, z.2.2)
    ∀ z : E × E × E, z ∈ shortBigons F ell a L →
      IsMinOn total (shortBigons F ell a L) z →
      z.2.1 ≠ 0 → z.2.2 ≠ 0 → ell (z.1, z.2.2) < L →
      (∀ t ∈ Icc (0 : ℝ) 1,
        ‖intrinsicGeodesic gExt hExt z.1 z.2.1 t‖ ≤ a) →
      (¬ IsConjVec gExt hExt z.1 z.2.2) →
      (ell (z.1, z.2.1))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.1) 1 (1 : Real) =
        -((ell (z.1, z.2.2))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.2) 1
              (1 : Real)) := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  intro z hz hzmin hzu hzv hzvLt hcore hvNot
  let x₀ : E := z.1
  let u₀ : E := z.2.1
  let v₀ : E := z.2.2
  let y₀ : E := F (x₀, u₀)
  let lu : Real := ell (x₀, u₀)
  let lv : Real := ell (x₀, v₀)
  let γu : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ u₀
  let γv : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ v₀
  let U : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γu 1 (1 : Real)
  let V : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γv 1 (1 : Real)
  have huvEnd : F (x₀, u₀) = F (x₀, v₀) := hz.2.2.1
  have hluPos : 0 < lu := by
    exact Real.sqrt_pos.2 (gExt.pos x₀ u₀ hzu)
  have hlvPos : 0 < lv := by
    exact Real.sqrt_pos.2 (gExt.pos x₀ v₀ hzv)
  have hγu1 : γu 1 = y₀ := by
    rfl
  have hyvExp :
      y₀ =
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x₀ v₀ := by
    simpa only [y₀, F] using huvEnd
  have hγv1 : γv 1 = y₀ := by
    dsimp only [γv]
    with_unfolding_all
      change expMapIntrinsic (I := 𝓘(Real, E))
        gExt hExt x₀ v₀ = y₀
      exact hyvExp.symm
  have hderNonneg :=
    first_variation_nonneg gExt hcomplete z hz hzmin hzv hzvLt hcore hvNot
  change 0 ≤ -lu + gExt.inner y₀ (lv⁻¹ • V) (-U) at hderNonneg
  have hUSpeed : gExt.inner y₀ U U = gExt.inner x₀ u₀ u₀ := by
    have hspeed := intrinsicGeodesic_speedSq_eq
      (I := 𝓘(Real, E)) gExt hExt x₀ u₀ 1
    change gExt.inner (γu 1) U U = gExt.inner x₀ u₀ u₀ at hspeed
    rw [hγu1] at hspeed
    exact hspeed
  have hVSpeed : gExt.inner y₀ V V = gExt.inner x₀ v₀ v₀ := by
    have hspeed :=
      intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x₀ v₀ 1
    change gExt.inner (γv 1) V V = gExt.inner x₀ v₀ v₀ at hspeed
    rw [hγv1] at hspeed
    exact hspeed
  have hluSq : lu ^ 2 = gExt.inner x₀ u₀ u₀ := by
    exact Real.sq_sqrt (gInner_self_nonneg
      (I := 𝓘(Real, E)) gExt x₀ u₀)
  have hlvSq : lv ^ 2 = gExt.inner x₀ v₀ v₀ := by
    exact Real.sq_sqrt (gInner_self_nonneg
      (I := 𝓘(Real, E)) gExt x₀ v₀)
  have hUunit :
      gExt.inner y₀ (lu⁻¹ • U) (lu⁻¹ • U) = 1 := by
    calc
      gExt.inner y₀ (lu⁻¹ • U) (lu⁻¹ • U) =
          lu⁻¹ ^ 2 * gExt.inner y₀ U U :=
        gInner_smul_self
          (I := 𝓘(Real, E)) gExt y₀ lu⁻¹ U
      _ = 1 := by
        rw [hUSpeed, ← hluSq, inv_pow]
        exact inv_mul_cancel₀ (pow_ne_zero 2 hluPos.ne')
  have hVunit :
      gExt.inner y₀ (lv⁻¹ • V) (lv⁻¹ • V) = 1 := by
    calc
      gExt.inner y₀ (lv⁻¹ • V) (lv⁻¹ • V) =
          lv⁻¹ ^ 2 * gExt.inner y₀ V V :=
        gInner_smul_self
          (I := 𝓘(Real, E)) gExt y₀ lv⁻¹ V
      _ = 1 := by
        rw [hVSpeed, ← hlvSq, inv_pow]
        exact inv_mul_cancel₀ (pow_ne_zero 2 hlvPos.ne')
  have hpair :
      gExt.inner y₀ (lv⁻¹ • V) (-U) =
        -(lv⁻¹ * gExt.inner y₀ U V) := by
    have hsmul :
        gExt.inner y₀ (lv⁻¹ • V) (-U) =
          lv⁻¹ * gExt.inner y₀ V (-U) := by
      have h :=
        congrArg (fun A : E →L[Real] Real => A (-U))
          ((gExt.inner y₀).map_smul lv⁻¹ V)
      with_unfolding_all
        change gExt.inner y₀ (lv⁻¹ • V) (-U) =
          lv⁻¹ * gExt.inner y₀ V (-U) at h
        exact h
    have hneg :
        gExt.inner y₀ V (-U) = -gExt.inner y₀ V U :=
      (gExt.inner y₀ V).map_neg U
    rw [hsmul, hneg, gExt.symm y₀ V U]
    ring
  have hscaled : lv⁻¹ * gExt.inner y₀ U V ≤ -lu := by
    rw [hpair] at hderNonneg
    linarith only [hderNonneg]
  have hcrossForm :
      gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) =
        lu⁻¹ * (lv⁻¹ * gExt.inner y₀ U V) := by
    have hout :
        gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) =
          lu⁻¹ * gExt.inner y₀ U (lv⁻¹ • V) := by
      have h :=
        congrArg (fun A : E →L[Real] Real => A (lv⁻¹ • V))
          ((gExt.inner y₀).map_smul lu⁻¹ U)
      with_unfolding_all
        change gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) =
          lu⁻¹ * gExt.inner y₀ U (lv⁻¹ • V) at h
        exact h
    have hin :
        gExt.inner y₀ U (lv⁻¹ • V) =
          lv⁻¹ * gExt.inner y₀ U V := by
      have h := (gExt.inner y₀ U).map_smul lv⁻¹ V
      with_unfolding_all
        exact h
    rw [hout, hin]
  have hcrossUpper :
      gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) ≤ -1 := by
    calc
      gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) =
          lu⁻¹ * (lv⁻¹ * gExt.inner y₀ U V) := hcrossForm
      _ ≤ lu⁻¹ * (-lu) :=
        mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hluPos.le)
      _ = -1 := by
        rw [mul_neg, inv_mul_cancel₀ hluPos.ne']
  let uN : TangentSpace 𝓘(Real, E) y₀ := lu⁻¹ • U
  let vN : TangentSpace 𝓘(Real, E) y₀ := lv⁻¹ • V
  have huNorm : ‖uN‖ = 1 := by
    have hi : inner Real uN uN = 1 := hUunit
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg uN]
  have hvNorm : ‖vN‖ = 1 := by
    have hi : inner Real vN vN = 1 := hVunit
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg vN]
  have hcross : inner Real uN vN = -1 := by
    have hcs := real_inner_le_norm (-uN) vN
    rw [inner_neg_left, norm_neg, huNorm, hvNorm, one_mul] at hcs
    have hle : inner Real uN vN ≤ -1 := hcrossUpper
    linarith
  have hunitOpp : uN = -vN :=
    (inner_eq_neg_one_iff_of_norm_eq_one huNorm hvNorm).mp hcross
  have hunitOpp' := congrArg
    (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) (γu 1)).symm hunitOpp
  with_unfolding_all
    change
      (ell (z.1, z.2.1))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.1) 1 (1 : Real) =
        -((ell (z.1, z.2.2))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.2) 1
              (1 : Real)) at hunitOpp'
    exact hunitOpp'

private theorem exists_period_of_minimal_bigon
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    (∀ x y q : E, ‖x‖ ≤ a → ‖y‖ ≤ a →
      Real.sqrt (gExt.inner x q q) ≤ L →
      intrinsicGeodesic gExt hExt x q 1 = y →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x q t‖ ≤ a) →
    (∀ x q : E, ‖x‖ ≤ a → Real.sqrt (gExt.inner x q q) < L →
      ¬ IsConjVec gExt hExt x q) →
    let F : E × E → E := fun z =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
    let ell : E × E → Real := fun z =>
      Real.sqrt (gExt.inner z.1 z.2 z.2)
    let total : E × E × E → Real := fun z =>
      ell (z.1, z.2.1) + ell (z.1, z.2.2)
    ∀ z₁ : E × E × E,
      z₁ ∈ shortBigons F ell a L →
      IsMinOn total (shortBigons F ell a L) z₁ →
      z₁.2.1 ≠ 0 → z₁.2.2 ≠ 0 →
      (ell (z₁.1, z₁.2.1) < L ∨ ell (z₁.1, z₁.2.2) < L) →
      ∃ T : ℝ, 0 < T ∧
        (∀ s : ℝ,
          intrinsicGeodesic gExt hExt z₁.1 z₁.2.1 (s + T) =
            intrinsicGeodesic gExt hExt z₁.1 z₁.2.1 s) ∧
        ∀ t ∈ Ioo (0 : ℝ) (2 * T),
          ‖intrinsicGeodesic gExt hExt z₁.1 z₁.2.1 t‖ ≤ a := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  intro hcore hnot
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  intro z₁ hz₁ hmin₁ hu₁ hv₁ hslack₁
  have terminal_opposite
      (z : E × E × E) (hz : z ∈ shortBigons F ell a L)
      (hzmin : IsMinOn total (shortBigons F ell a L) z)
      (hzu : z.2.1 ≠ 0) (hzv : z.2.2 ≠ 0)
      (hzvLt : ell (z.1, z.2.2) < L) :
      (ell (z.1, z.2.1))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic gExt hExt z.1 z.2.1) 1 (1 : Real) =
        -((ell (z.1, z.2.2))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic gExt hExt z.1 z.2.2) 1 (1 : Real)) := by
    exact terminal_velocity_eq_neg_of_minimal_bigon
      gExt hcomplete z hz hzmin hzu hzv hzvLt
      (hcore z.1 (F (z.1, z.2.1)) z.2.1 hz.1 hz.2.1 hz.2.2.2.1 rfl)
      (hnot z.1 z.2.2 hz.1 hzvLt)
  have corner_opposite
      (z : E × E × E) (hz : z ∈ shortBigons F ell a L)
      (hzmin : IsMinOn total (shortBigons F ell a L) z)
      (hzu : z.2.1 ≠ 0) (hzv : z.2.2 ≠ 0)
      (hzslack :
        ell (z.1, z.2.1) < L ∨ ell (z.1, z.2.2) < L) :
      (ell (z.1, z.2.1))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.1) 1 (1 : Real) =
        -((ell (z.1, z.2.2))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.2) 1
              (1 : Real)) := by
    rcases hzslack with huLt | hvLt
    · let zs : E × E × E := (z.1, z.2.2, z.2.1)
      have hzs : zs ∈ shortBigons F ell a L := by
        dsimp only [zs]
        exact
          ⟨hz.1, by rw [← hz.2.2.1]; exact hz.2.1,
            hz.2.2.1.symm, hz.2.2.2.2.1, hz.2.2.2.1,
            hz.2.2.2.2.2.symm⟩
      have htotal : total zs = total z := by
        dsimp only [total, zs]
        rw [add_comm]
      have hzsmin : IsMinOn total (shortBigons F ell a L) zs := by
        apply isMinOn_iff.mpr
        intro w hw
        rw [htotal]
        exact (isMinOn_iff.mp hzmin) w hw
      have hs :=
        terminal_opposite zs hzs hzsmin hzv hzu
          (by simpa only [zs] using huLt)
      dsimp only [zs] at hs
      have hneg := congrArg Neg.neg hs
      exact (neg_neg _).symm.trans hneg.symm
    · exact terminal_opposite z hz hzmin hzu hzv hvLt
  have hterm :=
    corner_opposite z₁ hz₁ hmin₁ hu₁ hv₁ hslack₁
  let x₁ : E := z₁.1
  let u₁ : E := z₁.2.1
  let v₁ : E := z₁.2.2
  let γu : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₁ u₁
  let γv : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₁ v₁
  let y₁ : E := γu 1
  let U : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γu 1 (1 : Real)
  let V : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γv 1 (1 : Real)
  let lu : Real := ell (x₁, u₁)
  let lv : Real := ell (x₁, v₁)
  have hx₁ : ‖x₁‖ ≤ a := hz₁.1
  have hγu1 : γu 1 = y₁ := rfl
  have hγv1 : γv 1 = y₁ := by
    with_unfolding_all exact hz₁.2.2.1.symm
  have hy₁ : ‖y₁‖ ≤ a := by
    with_unfolding_all exact hz₁.2.1
  have hluPos : 0 < lu := by
    exact Real.sqrt_pos.2 (gExt.pos x₁ u₁ hu₁)
  have hlvPos : 0 < lv := by
    exact Real.sqrt_pos.2 (gExt.pos x₁ v₁ hv₁)
  have hterm' : lu⁻¹ • U = -(lv⁻¹ • V) := by
    have htermModel := congrArg
      (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) y₁) hterm
    with_unfolding_all
      change lu⁻¹ • U = -(lv⁻¹ • V) at htermModel
      exact htermModel
  have hUne : U ≠ 0 := by
    exact intrinsicGeo_velocity_ne
      (I := 𝓘(Real, E)) gExt hExt x₁ u₁ hu₁ 1
  have hVne : V ≠ 0 := by
    exact intrinsicGeo_velocity_ne
      (I := 𝓘(Real, E)) gExt hExt x₁ v₁ hv₁ 1
  have hUVne : U ≠ V := by
    intro hUV
    have hzero : (lu⁻¹ + lv⁻¹) • U = 0 := by
      rw [hUV] at hterm'
      rw [add_smul, hUV]
      rw [hterm']
      exact neg_add_cancel _
    have hcoef :
        lu⁻¹ + lv⁻¹ ≠ 0 :=
      (add_pos (inv_pos.mpr hluPos) (inv_pos.mpr hlvPos)).ne'
    exact hUne ((smul_eq_zero.mp hzero).resolve_left hcoef)
  have hUSpeed :
      gExt.inner y₁ U U = gExt.inner x₁ u₁ u₁ := by
    have hs := intrinsicGeodesic_speedSq_eq
      (I := 𝓘(Real, E)) gExt hExt x₁ u₁ 1
    change gExt.inner (γu 1) U U = gExt.inner x₁ u₁ u₁ at hs
    rw [hγu1] at hs
    exact hs
  have hVSpeed :
      gExt.inner y₁ V V = gExt.inner x₁ v₁ v₁ := by
    have hs :=
      intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x₁ v₁ 1
    change gExt.inner (γv 1) V V = gExt.inner x₁ v₁ v₁ at hs
    rw [hγv1] at hs
    exact hs
  have hlenU : ell (y₁, -U) = lu := by
    have hneg :
        gExt.inner y₁ (-U) (-U) = gExt.inner y₁ U U := by
      have h := gInner_smul_self
        (I := 𝓘(Real, E)) gExt y₁ (-1 : Real) U
      rw [neg_one_smul (R := Real)] at h
      norm_num only [neg_one_sq, one_mul] at h
      with_unfolding_all exact h
    dsimp only [ell, lu]
    rw [hneg, hUSpeed]
  have hlenV : ell (y₁, -V) = lv := by
    have hneg :
        gExt.inner y₁ (-V) (-V) = gExt.inner y₁ V V := by
      have h := gInner_smul_self
        (I := 𝓘(Real, E)) gExt y₁ (-1 : Real) V
      have hnegV := neg_one_smul (R := Real)
        (show TangentSpace 𝓘(Real, E) y₁ from V)
      rw [hnegV] at h
      norm_num only [neg_one_sq, one_mul] at h
      with_unfolding_all exact h
    dsimp only [ell, lv]
    rw [hneg, hVSpeed]
  have hrevU :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-U) =
        fun t => γu (1 - t) := by
    have hr := intrinsicGeo_reverse
      (I := 𝓘(Real, E)) gExt hExt x₁ u₁
    change
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt (γu 1) (-U) =
        fun t => γu (1 - t) at hr
    rw [hγu1] at hr
    exact hr
  have hrevV :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-V) =
        fun t => γv (1 - t) := by
    have hr :=
      intrinsicGeo_reverse
        (I := 𝓘(Real, E)) gExt hExt x₁ v₁
    change
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt (γv 1) (-V) =
        fun t => γv (1 - t) at hr
    rw [hγv1] at hr
    exact hr
  have hrevUend :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-U) 1 = x₁ := by
    rw [hrevU]
    norm_num only [sub_self]
    exact intrinsicGeodesic_zero
      (I := 𝓘(Real, E)) gExt hExt x₁ u₁
  have hrevVend :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-V) 1 = x₁ := by
    rw [hrevV]
    norm_num only [sub_self]
    exact intrinsicGeodesic_zero
      (I := 𝓘(Real, E)) gExt hExt x₁ v₁
  let zr : E × E × E := (y₁, -U, -V)
  have hzr : zr ∈ shortBigons F ell a L := by
    have hFU : F (y₁, -U) = x₁ := by
      dsimp only [F]
      with_unfolding_all exact hrevUend
    have hFV : F (y₁, -V) = x₁ := by
      dsimp only [F]
      with_unfolding_all exact hrevVend
    dsimp only [zr]
    exact
      ⟨hy₁, by rw [hFU]; exact hx₁, hFU.trans hFV.symm,
        by rw [hlenU]; exact hz₁.2.2.2.1,
        by rw [hlenV]; exact hz₁.2.2.2.2.1,
        fun h => hUVne (neg_injective h)⟩
  have htotalr : total zr = total z₁ := by
    dsimp only [total, zr]
    rw [hlenU, hlenV]
  have hminr : IsMinOn total (shortBigons F ell a L) zr := by
    apply isMinOn_iff.mpr
    intro w hw
    rw [htotalr]
    exact (isMinOn_iff.mp hmin₁) w hw
  have hslackr :
      ell (zr.1, zr.2.1) < L ∨ ell (zr.1, zr.2.2) < L := by
    dsimp only [zr]
    simpa only [hlenU, hlenV] using hslack₁
  have hrevCorner :=
    corner_opposite zr hzr hminr
      (neg_ne_zero.mpr hUne) (neg_ne_zero.mpr hVne) hslackr
  dsimp only [zr] at hrevCorner
  have hrevVelocityU :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (-U)) 1 (1 : Real) =
        -u₁ := by
    have hv := intrinsicGeo_rev_velocity
      (I := 𝓘(Real, E)) gExt hExt x₁ u₁
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E))
        (intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-U) 1)).injective
    with_unfolding_all exact hv
  have hrevVelocityV :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (-V)) 1 (1 : Real) =
        -v₁ := by
    have hv :=
      intrinsicGeo_rev_velocity
        (I := 𝓘(Real, E)) gExt hExt x₁ v₁
    change
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt (γv 1) (-V)) 1 (1 : Real) =
        -v₁ at hv
    rw [hγv1] at hv
    exact hv
  rw [hlenU, hlenV, hrevVelocityU, hrevVelocityV] at hrevCorner
  have hinit : lu⁻¹ • u₁ = -(lv⁻¹ • v₁) := by
    have hleft :
        lu⁻¹ • (-u₁) = -(lu⁻¹ • u₁) :=
      smul_neg lu⁻¹ u₁
    have hright :
        -(lv⁻¹ • (-v₁)) = lv⁻¹ • v₁ := by
      calc
        -(lv⁻¹ • (-v₁)) = -(-(lv⁻¹ • v₁)) :=
          congrArg Neg.neg (smul_neg lv⁻¹ v₁)
        _ = lv⁻¹ • v₁ := neg_neg _
    have hneg :
        -(lu⁻¹ • u₁) = lv⁻¹ • v₁ :=
      hleft.symm.trans (hrevCorner.trans hright)
    have hn := congrArg Neg.neg hneg
    exact (neg_neg _).symm.trans hn
  let c : Real := lu / lv
  let d : Real := lv / lu
  let T : Real := 1 + d
  have hcPos : 0 < c := div_pos hluPos hlvPos
  have hdPos : 0 < d := div_pos hlvPos hluPos
  have hcd : c * d = 1 := by
    dsimp only [c, d]
    field_simp [hluPos.ne', hlvPos.ne']
  have hTPos : 0 < T := by
    dsimp only [T]
    exact add_pos zero_lt_one hdPos
  have unnormalize (a₀ b₀ : Real) (ha₀ : a₀ ≠ 0)
      (A B : E) (h : a₀⁻¹ • A = -(b₀⁻¹ • B)) :
      A = (a₀ / b₀) • (-B) := by
    calc
      A = a₀ • (a₀⁻¹ • A) := by
        rw [smul_smul, mul_inv_cancel₀ ha₀, one_smul]
      _ = a₀ • (-(b₀⁻¹ • B)) := congrArg (fun q : E => a₀ • q) h
      _ = -(a₀ • (b₀⁻¹ • B)) := smul_neg a₀ _
      _ = -((a₀ * b₀⁻¹) • B) := by rw [smul_smul]
      _ = (a₀ / b₀) • (-B) := by
        rw [div_eq_mul_inv, smul_neg]
  have hUscale : U = c • (-V) := by
    exact unnormalize lu lv hluPos.ne' U V hterm'
  have huscale : u₁ = c • (-v₁) := by
    exact unnormalize lu lv hluPos.ne' u₁ v₁ hinit
  have hjoin (s : Real) :
      γu (s + 1) = γv (1 - c * s) := by
    have hcont :=
      congrFun
        (intrinsicGeodesic_continuation
          (I := 𝓘(Real, E)) gExt hExt x₁ u₁ 1) s
    change
      γu (s + 1) =
        intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt (γu 1) U s at hcont
    rw [hγu1] at hcont
    calc
      γu (s + 1) =
          intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ U s := hcont
      _ = intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (c • (-V)) s := by
          rw [hUscale]
      _ = intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (-V) (c * s) :=
          intrinsicGeo_smul_apply
            (I := 𝓘(Real, E)) gExt hExt y₁ (-V) c s
      _ = γv (1 - c * s) := congrFun hrevV (c * s)
  have hbase (s : Real) : γu s = γv (-(c * s)) := by
    calc
      γu s =
          intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x₁ (c • (-v₁)) s := by
        change
          intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt x₁ u₁ s =
            intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt x₁ (c • (-v₁)) s
        rw [huscale]
      _ = intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x₁ (-v₁) (c * s) :=
          intrinsicGeo_smul_apply
            (I := 𝓘(Real, E)) gExt hExt x₁ (-v₁) c s
      _ = γv (-(c * s)) := by
        have hs :=
          intrinsicGeo_smul_apply
            (I := 𝓘(Real, E)) gExt hExt x₁ v₁ (-1) (c * s)
        have hnegV := neg_one_smul (R := Real)
          (show TangentSpace 𝓘(Real, E) x₁ from v₁)
        rw [hnegV] at hs
        norm_num only [neg_one_mul] at hs
        dsimp only [γv]
        with_unfolding_all exact hs
  have hperiod (s : Real) : γu (s + T) = γu s := by
    calc
      γu (s + T) = γu ((s + d) + 1) := by
        congr 1
        dsimp only [T]
        ring
      _ = γv (1 - c * (s + d)) := hjoin (s + d)
      _ = γv (-(c * s)) := by
        congr 1
        rw [mul_add, hcd]
        ring
      _ = γu s := (hbase s).symm
  have hcoreU : ∀ t ∈ Icc (0 : ℝ) 1, ‖γu t‖ ≤ a :=
    hcore x₁ y₁ u₁ hx₁ hy₁ hz₁.2.2.2.1 hγu1
  have hcoreV : ∀ t ∈ Icc (0 : ℝ) 1, ‖γv t‖ ≤ a :=
    hcore x₁ y₁ v₁ hx₁ hy₁ hz₁.2.2.2.2.1 hγv1
  refine ⟨T, hTPos, hperiod, ?_⟩
  exact periodic_core_bound (E := E) (γu := γu) (γv := γv)
    (a := a) (c := c) (d := d) (T := T) rfl hcPos hcd
    hjoin hperiod hcoreU hcoreV

private theorem short_geodesic_bigons_compact
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    (∀ x q : E, ‖x‖ ≤ a → Real.sqrt (gExt.inner x q q) ≤ L →
      ¬ IsConjVec gExt hExt x q) →
    0 < L →
    let F : E × E → E := fun z =>
      expMapIntrinsic gExt hExt z.1 z.2
    let ell : E × E → ℝ := fun z => Real.sqrt (gExt.inner z.1 z.2 z.2)
    IsCompact (shortBigons F ell a L) ∧ Continuous ell := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  intro hshortNotConj hLpos
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  have hlift :
      ContMDiff
        (𝓘(Real, E).prod 𝓘(Real, E))
        𝓘(Real, E).tangent ∞
        (fun z : E × E =>
          (⟨z.1, z.2⟩ : TangentBundle 𝓘(Real, E) E)) := by
    have h :=
      contMDiff_tangentBundleModelSpaceHomeomorph_symm
        (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at h
    rw [← chartedSpaceSelf_prod] at h
    convert h using 1
    all_goals rfl
  have hFmd :
      ContMDiff
        (𝓘(Real, E).prod 𝓘(Real, E))
        𝓘(Real, E) ∞ F := by
    convert
      (intrinsicExp_smooth (I := 𝓘(Real, E)) gExt hExt).comp hlift
        using 1
    all_goals rfl
  have hFcd : ContDiff Real ∞ F := by
    rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hFmd
  have hFcont : Continuous F := hFcd.continuous
  have hellCont : Continuous ell := by
    have hquad :=
      (metricQuad_cont (I := 𝓘(Real, E)) gExt).comp hlift.continuous
    convert Real.continuous_sqrt.comp hquad using 1
    all_goals rfl
  have hdiag :
      ∀ x₀ u₀ : E, ‖x₀‖ ≤ a → ell (x₀, u₀) ≤ L →
        ∃ U ∈ 𝓝 (x₀, u₀),
          Set.InjOn (fun z : E × E => (F z, z.1)) U := by
    intro x₀ u₀ hx₀ hu₀
    have hnot :
        ¬ IsConjVec
          (I := 𝓘(Real, E)) gExt hExt x₀ u₀ := by
      exact hshortNotConj x₀ u₀ hx₀ hu₀
    let f : E → E := fun w =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x₀
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) x₀).symm w)
    have hfiber : (fun y : E => F (x₀, y)) = f := by
      funext y
      dsimp only [F, f]
      rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
    have hpairDiff : DifferentiableAt Real (fun y : E => (x₀, y)) u₀ :=
      (differentiableAt_const x₀).prodMk differentiableAt_id
    have hfiberDiff : DifferentiableAt Real (fun y : E => F (x₀, y)) u₀ :=
      ((hFcd.differentiable (by simp)).differentiableAt).comp u₀ hpairDiff
    have hpartial :
        Analysis.partialFDeriv₂ F x₀ u₀ =
          fderiv Real f u₀ := by
      have hp := Analysis.partialFDeriv₂_eq
        ((hFcd.differentiable (by simp)).differentiableAt)
        hfiberDiff.hasFDerivAt
      rw [hfiber] at hp
      exact hp
    have hinj :
        Function.Injective (Analysis.partialFDeriv₂ F x₀ u₀) := by
      rw [hpartial]
      have hnot' : Function.Injective fun w : E =>
          mfderiv 𝓘(Real, E) 𝓘(Real, E) f u₀
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) u₀).symm w) := by
        simpa only [IsConjVec, f, not_not] using hnot
      have hnotV : Function.Injective fun w : E =>
          mvfderiv 𝓘(Real, E) f u₀
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) u₀).symm w) := by
        intro v w hvw
        apply hnot'
        apply (NormedSpace.fromTangentSpace (f u₀)).injective
        with_unfolding_all exact hvw
      intro v w hvw
      apply hnotV
      simpa only [mvfderiv_model_apply_eq_fderiv,
        (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) u₀).apply_symm_apply] using hvw
    exact pinned_inj_nhds F hFcd hinj
  let A : E → E →L[ℝ] E →L[ℝ] ℝ := fun x => gExt.inner x
  have hdiagCont (w : E) : Continuous (fun x : E => A x w w) := by
    convert (metricQuad_cont (I := 𝓘(ℝ, E)) gExt).comp
      (hlift.continuous.comp (continuous_id.prodMk continuous_const)) using 1
    all_goals rfl
  have hA : Continuous A := by
    apply continuous_clm_apply.mpr
    intro w
    apply continuous_clm_apply.mpr
    intro z
    have hpolar (x : E) :
        A x w z = (A x (w + z) (w + z) - A x w w - A x z z) / 2 := by
      have hsymm : A x z w = A x w z := gExt.symm x z w
      simp only [map_add, add_apply, hsymm]
      ring
    simp_rw [hpolar]
    exact (((hdiagCont (w + z)).sub (hdiagCont w)).sub (hdiagCont z)).div_const 2
  obtain ⟨c, hc, hlower⟩ := exists_pos_mul_norm_sq_le_bilinear_of_isCompact
    (isCompact_closedBall (0 : E) a) A hA.continuousOn
    (fun x _ w hw => gExt.pos x w hw)
  let B : Real := Real.sqrt (L ^ 2 / c)
  have hlaunchBound :
      ∀ x₀ : E, ‖x₀‖ ≤ a → ∀ w : E,
        ell (x₀, w) ≤ L → ‖w‖ ≤ B := by
    intro x₀ hx₀ w hw
    have hxBall : x₀ ∈ Metric.closedBall (0 : E) a := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx₀
    have hl := hlower x₀ hxBall w
    change c * ‖w‖ ^ 2 ≤ gExt.inner x₀ w w at hl
    have hinner : 0 ≤ gExt.inner x₀ w w :=
      gInner_self_nonneg (I := 𝓘(Real, E)) gExt x₀ w
    have hellSq : gExt.inner x₀ w w ≤ L ^ 2 := by
      have hsqrtSq :
          Real.sqrt (gExt.inner x₀ w w) ^ 2 =
            gExt.inner x₀ w w :=
        Real.sq_sqrt hinner
      rw [← hsqrtSq]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hLpos.le).2
        (by simpa only [ell] using hw)
    have hwSq : ‖w‖ ^ 2 ≤ L ^ 2 / c :=
      (le_div_iff₀ hc).2 (by
        simpa only [mul_comm] using hl.trans hellSq)
    have hquot : 0 ≤ L ^ 2 / c :=
      div_nonneg (sq_nonneg L) hc.le
    have hBSq : B ^ 2 = L ^ 2 / c := by
      simpa only [B] using Real.sq_sqrt hquot
    exact
      (sq_le_sq₀ (norm_nonneg w) (Real.sqrt_nonneg _)).1
        (by simpa only [B, hBSq] using hwSq)
  have hbadCompact : IsCompact (shortBigons F ell a L) := by
    apply shortBigons_compact F ell a L B hFcont hellCont hdiag
    intro z hz
    exact ⟨
      hlaunchBound z.1 hz.1 z.2.1 hz.2.2.2.1,
      hlaunchBound z.1 hz.1 z.2.2 hz.2.2.2.2.1⟩
  exact ⟨hbadCompact, hellCont⟩

private theorem exists_nonzero_minimal_bigon
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    (∀ x y q : E, ‖x‖ ≤ a → ‖y‖ ≤ a →
      Real.sqrt (gExt.inner x q q) ≤ L →
      intrinsicGeodesic gExt hExt x q 1 = y →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x q t‖ ≤ a) →
    let F : E × E → E := fun z => expMapIntrinsic gExt hExt z.1 z.2
    let ell : E × E → ℝ := fun z => Real.sqrt (gExt.inner z.1 z.2 z.2)
    let total : E × E × E → ℝ := fun z => ell (z.1, z.2.1) + ell (z.1, z.2.2)
    ∀ z₀ : E × E × E, z₀ ∈ shortBigons F ell a L →
      IsMinOn total (shortBigons F ell a L) z₀ → total z₀ < 2 * L →
      ∃ z₁ : E × E × E,
        z₁ ∈ shortBigons F ell a L ∧
        IsMinOn total (shortBigons F ell a L) z₁ ∧
        z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
        (ell (z₁.1, z₁.2.1) < L ∨ ell (z₁.1, z₁.2.2) < L) := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  intro hcore
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  let total : E × E × E → ℝ := fun z => ell (z.1, z.2.1) + ell (z.1, z.2.2)
  intro z₀ hz₀ hmin htotalLt
  change z₀ ∈ shortBigons F ell a L at hz₀
  change IsMinOn total (shortBigons F ell a L) z₀ at hmin
  change total z₀ < 2 * L at htotalLt
  have hslack :
      ell (z₀.1, z₀.2.1) < L ∨
        ell (z₀.1, z₀.2.2) < L := by
    by_contra h
    push Not at h
    dsimp only [total] at htotalLt
    have htwo : 2 * L ≤ ell (z₀.1, z₀.2.1) + ell (z₀.1, z₀.2.2) := by
      calc
        2 * L = L + L := by ring
        _ ≤ ell (z₀.1, z₀.2.1) + ell (z₀.1, z₀.2.2) :=
          add_le_add h.1 h.2
    exact (not_lt_of_ge htwo) htotalLt
  have midpoint_min
      (x₀ q₀ : E) (hx₀ : ‖x₀‖ ≤ a)
      (hqL : ell (x₀, q₀) ≤ L) (hqne : q₀ ≠ 0)
      (hloop : F (x₀, q₀) = x₀)
      (htot : total z₀ = ell (x₀, q₀)) :
      ∃ z₁ : E × E × E,
        z₁ ∈ shortBigons F ell a L ∧
        IsMinOn total (shortBigons F ell a L) z₁ ∧
        z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
        ell (z₁.1, z₁.2.1) < L ∧
        ell (z₁.1, z₁.2.2) < L :=
    exists_nonzero_minimizing_bigon_of_loop
      gExt hcomplete hcore z₀ hmin htotalLt x₀ q₀ hx₀ hqL hqne hloop htot
  have hnormalize :
      ∃ z₁ : E × E × E,
        z₁ ∈ shortBigons F ell a L ∧
        IsMinOn total (shortBigons F ell a L) z₁ ∧
        z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
        (ell (z₁.1, z₁.2.1) < L ∨
          ell (z₁.1, z₁.2.2) < L) := by
    by_cases hu₀ : z₀.2.1 = 0
    · have hv₀ : z₀.2.2 ≠ 0 := by
        intro hv₀
        exact hz₀.2.2.2.2.2 (hu₀.trans hv₀.symm)
      have hFzero : F (z₀.1, 0) = z₀.1 := by
        dsimp only [F]
        with_unfolding_all
          exact expMapIntrinsic_zero
            (I := 𝓘(Real, E)) gExt hExt z₀.1
      have hloop : F (z₀.1, z₀.2.2) = z₀.1 := by
        rw [← hz₀.2.2.1, hu₀, hFzero]
      have htot :
          total z₀ = ell (z₀.1, z₀.2.2) := by
        have hell0 : ell (z₀.1, 0) = 0 := by
          have hzero :
              Real.sqrt (gExt.inner z₀.1
                ((tangentSpaceModelContinuousLinearEquiv
                  (I := 𝓘(Real, E)) z₀.1).symm (0 : E))
                ((tangentSpaceModelContinuousLinearEquiv
                  (I := 𝓘(Real, E)) z₀.1).symm (0 : E))) = 0 := by
            rw [map_zero, map_zero, Real.sqrt_zero]
          with_unfolding_all exact hzero
        dsimp only [total]
        rw [hu₀, hell0, zero_add]
      obtain ⟨z₁, hz₁, hmin₁, hu₁, hv₁, huLt, hvLt⟩ :=
        midpoint_min z₀.1 z₀.2.2 hz₀.1 hz₀.2.2.2.2.1
          hv₀ hloop htot
      exact ⟨z₁, hz₁, hmin₁, hu₁, hv₁, Or.inl huLt⟩
    · by_cases hv₀ : z₀.2.2 = 0
      · have hFzero : F (z₀.1, 0) = z₀.1 := by
          dsimp only [F]
          with_unfolding_all
            exact expMapIntrinsic_zero
              (I := 𝓘(Real, E)) gExt hExt z₀.1
        have hloop : F (z₀.1, z₀.2.1) = z₀.1 := by
          rw [hz₀.2.2.1, hv₀, hFzero]
        have htot :
            total z₀ = ell (z₀.1, z₀.2.1) := by
          have hell0 : ell (z₀.1, 0) = 0 := by
            have hzero :
                Real.sqrt (gExt.inner z₀.1
                  ((tangentSpaceModelContinuousLinearEquiv
                    (I := 𝓘(Real, E)) z₀.1).symm (0 : E))
                  ((tangentSpaceModelContinuousLinearEquiv
                    (I := 𝓘(Real, E)) z₀.1).symm (0 : E))) = 0 := by
              rw [map_zero, map_zero, Real.sqrt_zero]
            with_unfolding_all exact hzero
          dsimp only [total]
          rw [hv₀, hell0, add_zero]
        obtain ⟨z₁, hz₁, hmin₁, hu₁, hv₁, huLt, hvLt⟩ :=
          midpoint_min z₀.1 z₀.2.1 hz₀.1 hz₀.2.2.2.1
            hu₀ hloop htot
        exact ⟨z₁, hz₁, hmin₁, hu₁, hv₁, Or.inl huLt⟩
      · exact ⟨z₀, hz₀, hmin, hu₀, hv₀, hslack⟩
  exact hnormalize

theorem exists_periodic_geodesic_of_expMapIntrinsic_eq
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {a L : ℝ} :
    let : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    let : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    let : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E :=
      hcomplete.complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    (∀ x y q : E, ‖x‖ ≤ a → ‖y‖ ≤ a →
      Real.sqrt (gExt.inner x q q) ≤ L →
      intrinsicGeodesic gExt hExt x q 1 = y →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x q t‖ ≤ a) →
    (∀ x q : E, ‖x‖ ≤ a → Real.sqrt (gExt.inner x q q) ≤ L →
      ¬ IsConjVec gExt hExt x q) →
    ∀ x y u v : E, ‖x‖ ≤ a → ‖y‖ ≤ a →
      Real.sqrt (gExt.inner x u u) < L →
      Real.sqrt (gExt.inner x v v) < L →
      intrinsicGeodesic gExt hExt x u 1 = y →
      intrinsicGeodesic gExt hExt x v 1 = y → u ≠ v →
      ∃ x₁ u₁ : E, ‖x₁‖ ≤ a ∧ u₁ ≠ 0 ∧
        Real.sqrt (gExt.inner x₁ u₁ u₁) ≤ L ∧
        ∃ T : ℝ, 0 < T ∧
          (∀ s : ℝ, intrinsicGeodesic gExt hExt x₁ u₁ (s + T) =
            intrinsicGeodesic gExt hExt x₁ u₁ s) ∧
          ∀ t ∈ Ioo (0 : ℝ) (2 * T),
            ‖intrinsicGeodesic gExt hExt x₁ u₁ t‖ ≤ a := by
  dsimp only
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    hcomplete.complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  intro hcore hshortNotConj x y u v hx hy huL hvL huEnd hvEnd huv
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  have hLpos : 0 < L := (Real.sqrt_nonneg _).trans_lt huL
  have hcompact : IsCompact (shortBigons F ell a L) ∧ Continuous ell := by
    with_unfolding_all
      exact short_geodesic_bigons_compact gExt hcomplete hshortNotConj hLpos
  obtain ⟨hbadCompact, hellCont⟩ := hcompact
  let zInitial : E × E × E := (x, u, v)
  have hzInitial : zInitial ∈ shortBigons F ell a L := by
    refine ⟨hx, ?_, ?_, huL.le, hvL.le, huv⟩
    · have hFu : F (x, u) = y := by
        with_unfolding_all
          change intrinsicGeodesic (I := 𝓘(Real, E))
            gExt hExt x u 1 = y
          exact huEnd
      simpa only [zInitial, hFu] using hy
    · have hFu : F (x, u) = y := by
        with_unfolding_all
          change intrinsicGeodesic (I := 𝓘(Real, E))
            gExt hExt x u 1 = y
          exact huEnd
      have hFv : F (x, v) = y := by
        with_unfolding_all
          change intrinsicGeodesic (I := 𝓘(Real, E))
            gExt hExt x v 1 = y
          exact hvEnd
      simp only [zInitial, hFu, hFv]
  have hbadNonempty : (shortBigons F ell a L).Nonempty :=
    ⟨zInitial, hzInitial⟩
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  have htotal : Continuous total :=
    (hellCont.comp
      (continuous_fst.prodMk continuous_snd.fst)).add
      (hellCont.comp
        (continuous_fst.prodMk continuous_snd.snd))
  obtain ⟨z₀, hz₀, hmin⟩ :=
    hbadCompact.exists_isMinOn hbadNonempty htotal.continuousOn
  have hminInitial : total z₀ ≤ total zInitial :=
    (isMinOn_iff.mp hmin) zInitial hzInitial
  have htotalLt : total z₀ < 2 * L := by
    dsimp only [total, zInitial] at hminInitial ⊢
    exact hminInitial.trans_lt
      (by simpa only [ell, two_mul] using add_lt_add huL hvL)
  have hnormalized : ∃ z₁ : E × E × E,
      z₁ ∈ shortBigons F ell a L ∧ IsMinOn total (shortBigons F ell a L) z₁ ∧
      z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
      (ell (z₁.1, z₁.2.1) < L ∨ ell (z₁.1, z₁.2.2) < L) := by
    with_unfolding_all
      exact exists_nonzero_minimal_bigon gExt hcomplete hcore z₀ hz₀ hmin htotalLt
  obtain ⟨z₁, hz₁, hmin₁, hu₁, hv₁, hslack₁⟩ := hnormalized
  have hperiodic : ∃ T : ℝ, 0 < T ∧
      (∀ s : ℝ, intrinsicGeodesic gExt hExt z₁.1 z₁.2.1 (s + T) =
        intrinsicGeodesic gExt hExt z₁.1 z₁.2.1 s) ∧
      ∀ t ∈ Ioo (0 : ℝ) (2 * T),
        ‖intrinsicGeodesic gExt hExt z₁.1 z₁.2.1 t‖ ≤ a := by
    with_unfolding_all
      exact exists_period_of_minimal_bigon
        gExt hcomplete hcore
        (fun x q hx hq => hshortNotConj x q hx hq.le)
        z₁ hz₁ hmin₁ hu₁ hv₁ hslack₁
  obtain ⟨T, hT, hperiod, hstay⟩ := hperiodic
  exact ⟨z₁.1, z₁.2.1, hz₁.1, hu₁, hz₁.2.2.2.1, T, hT, hperiod, hstay⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential
