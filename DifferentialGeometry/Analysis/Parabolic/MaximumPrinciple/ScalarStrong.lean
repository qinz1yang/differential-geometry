import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Strong
import DifferentialGeometry.Geometry.Metric.MetricBounds
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private abbrev StrongEuclidean := EuclideanSpace Real (Fin (Module.finrank Real E))

private def strongChartRadiusSq (a c x : M) : Real :=
  ‖(toEuclidean (E := E)) (extChartAt I a x - extChartAt I a c)‖ ^ 2

private theorem strongChartRadiusSq_contMDiffOn
    (a c : M) :
    ContMDiffOn I 𝓘(Real, Real) ∞ (strongChartRadiusSq (I := I) a c)
      (chartAt H a).source := by
  unfold strongChartRadiusSq
  intro x hx
  have hq : ContDiff Real ∞
      (fun z : E => ‖(toEuclidean (E := E)) (z - extChartAt I a c)‖ ^ 2) := by
    exact ((toEuclidean (E := E)).contDiff.comp
      (contDiff_id.sub contDiff_const)).norm_sq Real
  simpa only [Function.comp_apply] using
    (hq.contMDiff.contMDiffAt.comp x
      (((contMDiffOn_extChartAt (I := I) (x := a)) x hx).contMDiffAt
        ((chartAt H a).open_source.mem_nhds hx))).contMDiffWithinAt

private def strongPropagationRadius [T2Space M]
    {a : M} (b : SmoothBumpFunction I a) (c : M) (Q : Real) (x : M) : Real :=
  b x * strongChartRadiusSq (I := I) a c x + Q * (1 - b x)

private def globalStrongStaticMetricFamily
    (g : SmoothRiemannianMetric I M) :
    MetricConnectionFamily (I := I) (M := M) Real where
  metric := fun _ => g
  connection := fun _ => LeviCivita (I := I) g
  metricCompatible := by
    intro t
    simpa using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)

private def shiftedStrongMetricFamily
    (G : MetricConnectionFamily (I := I) (M := M) Real) (a : Real) :
    MetricConnectionFamily (I := I) (M := M) Real where
  metric := fun s => G.metric (a + s)
  connection := fun s => G.connection (a + s)
  metricCompatible := fun s => G.metricCompatible (a + s)

omit [FiniteDimensional Real E] in
@[simp] private theorem shiftedStrongMetricFamily_metric
    (G : MetricConnectionFamily (I := I) (M := M) Real) (a s : Real) :
    (shiftedStrongMetricFamily G a).metric s = G.metric (a + s) := by
  rfl

omit [FiniteDimensional Real E] in
@[simp] private theorem shiftedStrongMetricFamily_connection
    (G : MetricConnectionFamily (I := I) (M := M) Real) (a s : Real) :
    (shiftedStrongMetricFamily G a).connection s = G.connection (a + s) := by
  rfl

@[simp] private theorem globalStrongStaticMetricFamily_metric
    (g : SmoothRiemannianMetric I M) (t : Real) :
    (globalStrongStaticMetricFamily (I := I) g).metric t = g := by
  rfl

private theorem globalStrongStaticMetricFamily_parabolicOperator
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) (T : Real)
    (X : Real → (x : M) → TangentSpace I x)
    (f : Real → M → Real) {t : Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ (f t)) (x : M) :
    parabolicOperatorWithDrift (I := I) (globalStrongStaticMetricFamily (I := I) g)
        T X f t x =
      derivWithin (fun s => f s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨f t, hf⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (f t) x)) := by
  have hlapAt := laplacianAt_eq_delta (I := I)
    (globalStrongStaticMetricFamily (I := I) g) t hf rfl x
  unfold parabolicOperatorWithDrift heatOperatorWithDrift driftTerm gradientAt
  rw [hlapAt]
  rfl

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem vadd_Icc_eq_Icc (a T : Real) :
    a +ᵥ Set.Icc (0 : Real) (T - a) = Set.Icc a T := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    constructor <;> dsimp <;> linarith [hs.1, hs.2]
  · intro ht
    refine ⟨t - a, ?_, by simp⟩
    constructor <;> linarith [ht.1, ht.2]

private theorem strongPropagationRadius_contMDiff [T2Space M]
    {a c : M} (b : SmoothBumpFunction I a)
    (Q : Real) :
    ContMDiff I 𝓘(Real, Real) ∞ (strongPropagationRadius (I := I) b c Q) := by
  unfold strongPropagationRadius
  have hfirst : ContMDiff I 𝓘(Real, Real) ∞
      (fun x => b x * strongChartRadiusSq (I := I) a c x) := by
    simpa only [smul_eq_mul] using
      b.contMDiff_smul (strongChartRadiusSq_contMDiffOn (I := I) a c)
  exact hfirst.add (contMDiff_const.mul (contMDiff_const.sub b.contMDiff))

omit [IsManifold I ∞ M] in
private theorem strongPropagationRadius_nonneg [T2Space M]
    {a c : M} (b : SmoothBumpFunction I a) {Q : Real} (hQ : 0 ≤ Q) (x : M) :
    0 ≤ strongPropagationRadius (I := I) b c Q x := by
  exact add_nonneg
    (mul_nonneg b.nonneg (sq_nonneg _))
    (mul_nonneg hQ (sub_nonneg.mpr b.le_one))

omit [IsManifold I ∞ M] in
private theorem strongPropagationRadius_pos_of_ne [T2Space M]
    {a c : M} (b : SmoothBumpFunction I a)
    (hc : c ∈ (chartAt H a).source) {Q : Real} (hQ : 0 < Q)
    {x : M} (hxc : x ≠ c) :
    0 < strongPropagationRadius (I := I) b c Q x := by
  by_cases hb : b x = 0
  · simp [strongPropagationRadius, hb, hQ]
  · have hbx : 0 < b x := lt_of_le_of_ne b.nonneg (Ne.symm hb)
    have hx : x ∈ (chartAt H a).source := by
      apply b.support_subset_source
      simpa [Function.mem_support] using hb
    have hchart : extChartAt I a x ≠ extChartAt I a c := by
      intro heq
      apply hxc
      have := congrArg (extChartAt I a).symm heq
      rw [(extChartAt I a).left_inv
          (show x ∈ (extChartAt I a).source by simpa [extChartAt_source] using hx),
        (extChartAt I a).left_inv
          (show c ∈ (extChartAt I a).source by simpa [extChartAt_source] using hc)] at this
      exact this
    have hq : 0 < strongChartRadiusSq (I := I) a c x := by
      unfold strongChartRadiusSq
      have hsub : extChartAt I a x - extChartAt I a c ≠ 0 :=
        sub_ne_zero.mpr hchart
      have heucl : (toEuclidean (E := E))
          (extChartAt I a x - extChartAt I a c) ≠ 0 := by
        simpa using (toEuclidean (E := E)).injective.ne hsub
      positivity
    unfold strongPropagationRadius
    exact add_pos_of_pos_of_nonneg (mul_pos hbx hq)
      (mul_nonneg hQ.le (sub_nonneg.mpr b.le_one))

private theorem exists_strongPropagationRadius_sublevel_subset
    [T2Space M] [CompactSpace M]
    {a c : M} (b : SmoothBumpFunction I a)
    (hc : c ∈ (chartAt H a).source) {Q : Real} (hQ : 0 < Q)
    {V : Set M} (hV : V ∈ nhds c) :
    ∃ r : Real, 0 < r ∧
      {x | strongPropagationRadius (I := I) b c Q x < r} ⊆ V := by
  rcases mem_nhds_iff.mp hV with ⟨U, hUV, hUopen, hcU⟩
  by_cases hK : (Uᶜ : Set M).Nonempty
  · have hKcompact : IsCompact (Uᶜ : Set M) := hUopen.isClosed_compl.isCompact
    obtain ⟨x0, hx0, hx0min⟩ := hKcompact.exists_isMinOn hK
      (strongPropagationRadius_contMDiff (I := I) (c := c) b Q).continuous.continuousOn
    have hx0c : x0 ≠ c := by
      intro heq
      subst x0
      exact hx0 hcU
    have hx0pos : 0 < strongPropagationRadius (I := I) b c Q x0 :=
      strongPropagationRadius_pos_of_ne (I := I) b hc hQ hx0c
    refine ⟨strongPropagationRadius (I := I) b c Q x0 / 2, by linarith, ?_⟩
    intro x hx
    apply hUV
    by_contra hxU
    have hmin := hx0min (show x ∈ Uᶜ by simpa using hxU)
    change strongPropagationRadius (I := I) b c Q x0 ≤
      strongPropagationRadius (I := I) b c Q x at hmin
    change strongPropagationRadius (I := I) b c Q x <
      strongPropagationRadius (I := I) b c Q x0 / 2 at hx
    linarith
  · refine ⟨1, by positivity, ?_⟩
    intro x _
    apply hUV
    by_contra hxU
    exact hK ⟨x, by simpa using hxU⟩

omit [IsManifold I ∞ M] in
private theorem strongPropagationRadius_lt_imp [T2Space M]
    {a c x : M} (b : SmoothBumpFunction I a) {Q R : Real}
    (hRQ : R < Q) (h : strongPropagationRadius (I := I) b c Q x < R) :
    0 < b x ∧ strongChartRadiusSq (I := I) a c x < Q := by
  have hb0 := b.nonneg (x := x)
  unfold strongPropagationRadius at h
  have hfactor : b x * (strongChartRadiusSq (I := I) a c x - Q) < 0 := by
    nlinarith
  have hbne : b x ≠ 0 := by
    intro hb
    rw [hb, zero_mul] at hfactor
    exact (lt_irrefl 0) hfactor
  have hbpos : 0 < b x := lt_of_le_of_ne hb0 (Ne.symm hbne)
  rcases (mul_neg_iff.mp hfactor) with hcase | hcase
  · exact ⟨hbpos, by linarith [hcase.2]⟩
  · exact (not_lt_of_ge hb0 hcase.1).elim

omit [IsManifold I ∞ M] in
private theorem strongPropagationRadius_eventuallyEq [T2Space M]
    {a c x : M} (b : SmoothBumpFunction I a)
    (hx : x ∈ (chartAt H a).source)
    (hd : dist (extChartAt I a x) (extChartAt I a a) < b.rIn)
    (Q : Real) :
    EventuallyEq (nhds x) (strongPropagationRadius (I := I) b c Q)
      (strongChartRadiusSq (I := I) a c) := by
  filter_upwards [b.eventuallyEq_one_of_dist_lt hx hd] with y hy
  simp [strongPropagationRadius, hy]

private theorem fderiv_chartRadiusSq_apply_self (z z0 : E) :
    fderiv Real
        (fun w : E => ‖(toEuclidean (E := E)) (w - z0)‖ ^ 2) z (z - z0) =
      2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2 := by
  have h := (((toEuclidean (E := E)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const z0))).norm_sq
  change fderiv Real
      (fun x => ‖((toEuclidean (E := E) : E → StrongEuclidean) ∘
        fun y => id y - z0) x‖ ^ 2) z (z - z0) = _
  rw [h.fderiv]
  simp only [id_eq, Function.comp_apply, map_sub, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp', coe_innerSL_apply,
    ContinuousLinearEquiv.coe_coe, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm ((toEuclidean (E := E)) z0) ((toEuclidean (E := E)) z)]
  rw [norm_sub_sq_real]
  rw [real_inner_comm ((toEuclidean (E := E)) z0) ((toEuclidean (E := E)) z)]
  ring

private theorem strongChartRadiusSq_mfderiv_ne_zero
    {a c x : M} (hc : c ∈ (chartAt H a).source)
    (hx : x ∈ (chartAt H a).source) (hxc : x ≠ c) :
    mfderiv I 𝓘(Real, Real) (strongChartRadiusSq (I := I) a c) x ≠ 0 := by
  let z : E := extChartAt I a x
  let z0 : E := extChartAt I a c
  let q : E → Real := fun w => ‖(toEuclidean (E := E)) (w - z0)‖ ^ 2
  have hcomp :
      mfderiv I 𝓘(Real, Real) (strongChartRadiusSq (I := I) a c) x =
        (fderiv Real q z).comp (mfderiv I 𝓘(Real, E) (extChartAt I a) x) := by
    have hq : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real) q z := by
      have hqcd : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ q :=
        (((toEuclidean (E := E)).contDiff.comp
          (contDiff_id.sub contDiff_const)).norm_sq Real).contMDiff
      exact hqcd.mdifferentiable (by simp) z
    have hchart : MDifferentiableAt I 𝓘(Real, E) (extChartAt I a) x :=
      mdifferentiableAt_extChartAt (I := I) hx
    simpa only [strongChartRadiusSq, q, z, mfderiv_eq_fderiv, Function.comp_apply] using
      mfderiv_comp x hq hchart
  intro hzero
  have hqzero : fderiv Real q z = 0 := by
    have hinv := isInvertible_mfderiv_extChartAt (I := I)
      (show x ∈ (extChartAt I a).source by simpa [extChartAt_source] using hx)
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hinv.surjective v
    have happ := congrArg (fun L : TangentSpace I x →L[Real] Real => L w) hzero
    rw [hcomp] at happ
    simp only [ContinuousLinearMap.comp_apply] at happ
    calc
      fderiv Real q z v = fderiv Real q z
          ((mfderiv I 𝓘(Real, E) (extChartAt I a) x) w) := by rw [hw]
      _ = 0 := by simpa using happ
  have hz_ne : z ≠ z0 := by
    intro hz
    apply hxc
    have hs := congrArg (extChartAt I a).symm hz
    rw [(extChartAt I a).left_inv
      (show x ∈ (extChartAt I a).source by simpa [extChartAt_source] using hx),
      (extChartAt I a).left_inv
        (show c ∈ (extChartAt I a).source by simpa [extChartAt_source] using hc)] at hs
    exact hs
  have hL_ne : (toEuclidean (E := E)) (z - z0) ≠ 0 := by
    intro hL
    have hsub := (toEuclidean (E := E)).injective
      (show (toEuclidean (E := E)) (z - z0) =
        (toEuclidean (E := E)) 0 by simpa using hL)
    exact (sub_ne_zero.mpr hz_ne) hsub
  have happ := fderiv_chartRadiusSq_apply_self (E := E) z z0
  rw [hqzero] at happ
  simp only [ContinuousLinearMap.zero_apply] at happ
  have hpos : 0 < 2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2 := by
    positivity
  linarith

private theorem strongPropagationRadius_gradient_ne_zero
    [T2Space M] [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) {a c x : M}
    (b : SmoothBumpFunction I a) (hc : c ∈ (chartAt H a).source)
    (hx : x ∈ (chartAt H a).source)
    (hd : dist (extChartAt I a x) (extChartAt I a a) < b.rIn)
    (hxc : x ≠ c) (Q : Real) :
    gradientFun (I := I) g (strongPropagationRadius (I := I) b c Q) x ≠ 0 := by
  have hev := strongPropagationRadius_eventuallyEq (I := I) (c := c) b hx hd Q
  have hmf : mfderiv I 𝓘(Real, Real)
      (strongPropagationRadius (I := I) b c Q) x ≠ 0 := by
    rw [hev.mfderiv_eq]
    exact strongChartRadiusSq_mfderiv_ne_zero (I := I) hc hx hxc
  intro hgrad
  apply hmf
  apply ContinuousLinearMap.ext
  intro v
  have hinner := inner_gradientFun (I := I) g
    (strongPropagationRadius (I := I) b c Q) x v
  rw [hgrad] at hinner
  simpa using hinner.symm

omit [IsManifold I ∞ M] in
private theorem strongChartRadiusSq_lt_imp_mem_core
    {a c x : M} (b : SmoothBumpFunction I a)
    (hc_dist : dist (extChartAt I a c) (extChartAt I a a) < b.rIn)
    (hq : strongChartRadiusSq (I := I) a c x <
      ((b.rIn - dist (extChartAt I a c) (extChartAt I a a)) /
        (2 * (‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1))) ^ 2) :
    dist (extChartAt I a x) (extChartAt I a a) < b.rIn := by
  let C : Real := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1
  let s : Real :=
    (b.rIn - dist (extChartAt I a c) (extChartAt I a a)) / (2 * C)
  have hC : 0 < C := by
    dsimp [C]
    linarith [norm_nonneg
      (toEuclidean (E := E)).symm.toContinuousLinearMap]
  have hgap : 0 < b.rIn - dist (extChartAt I a c) (extChartAt I a a) :=
    sub_pos.mpr hc_dist
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hxc_eucl : ‖(toEuclidean (E := E))
      (extChartAt I a x - extChartAt I a c)‖ < s := by
    apply (sq_lt_sq₀ (norm_nonneg _) hs.le).mp
    simpa only [strongChartRadiusSq, s, C] using hq
  have hxc : dist (extChartAt I a x) (extChartAt I a c) < C * s := by
    have hop := (toEuclidean (E := E)).symm.toContinuousLinearMap.le_opNorm
      ((toEuclidean (E := E)) (extChartAt I a x - extChartAt I a c))
    rw [dist_eq_norm]
    calc
      ‖extChartAt I a x - extChartAt I a c‖ ≤
          ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ *
            ‖(toEuclidean (E := E))
              (extChartAt I a x - extChartAt I a c)‖ := by
        simpa using hop
      _ < C * s := by
        apply mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
        · dsimp [C]
          linarith [norm_nonneg
            (toEuclidean (E := E)).symm.toContinuousLinearMap]
        · exact hxc_eucl
        · exact (norm_nonneg _)
        · exact hC
  calc
    dist (extChartAt I a x) (extChartAt I a a) ≤
        dist (extChartAt I a x) (extChartAt I a c) +
          dist (extChartAt I a c) (extChartAt I a a) := dist_triangle _ _ _
    _ < C * s + dist (extChartAt I a c) (extChartAt I a a) :=
      by simpa [add_comm] using
        add_lt_add_right hxc (dist (extChartAt I a c) (extChartAt I a a))
    _ < b.rIn := by
      have hCs : C * s =
          (b.rIn - dist (extChartAt I a c) (extChartAt I a a)) / 2 := by
        dsimp [s]
        field_simp
      rw [hCs]
      nlinarith

private theorem exists_positive_terminal_cylinder
    {T : Real} (hT : 0 ≤ T) (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    {c : M} (hc : 0 < u T c) :
    ∃ delta eta : Real, 0 < delta ∧ 0 < eta ∧ ∃ V ∈ nhds c,
      ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x ∈ V, eta ≤ u t x := by
  let eta : Real := u T c / 2
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  have hp : (T, c) ∈ spacetimeSlab (M := M) T :=
    ⟨⟨hT, le_rfl⟩, Set.mem_univ c⟩
  have htarget : Set.Ioi eta ∈ nhds (u T c) := by
    exact Ioi_mem_nhds (by dsimp [eta]; linarith)
  have hpre : (fun p : Real × M => u p.1 p.2) ⁻¹' Set.Ioi eta ∈
      nhdsWithin (T, c) (spacetimeSlab (M := M) T) :=
    (hu_cont (T, c) hp).preimage_mem_nhdsWithin htarget
  change (fun p : Real × M => u p.1 p.2) ⁻¹' Set.Ioi eta ∈
      nhdsWithin (T, c) (Set.Icc 0 T ×ˢ Set.univ) at hpre
  rcases mem_nhdsWithin_prod_iff.mp hpre with ⟨U, hU, V, hV, hUV⟩
  rcases Metric.mem_nhdsWithin_iff.mp hU with ⟨delta, hdelta, hball⟩
  have hV' : V ∈ nhds c := by simpa using hV
  refine ⟨delta, eta, hdelta, heta, V, hV', ?_⟩
  intro t ht htclose x hx
  have htball : t ∈ Metric.ball T delta := by
    change dist t T < delta
    rw [Real.dist_eq]
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith
  have htU : t ∈ U := hball ⟨htball, ht⟩
  have htx : (t, x) ∈ U ×ˢ V := ⟨htU, hx⟩
  have hpos := hUV htx
  exact le_of_lt hpos

private theorem fixed_metric_spatial_zero_drift
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {c : M} (hc : 0 < u T c) (y : M) :
    0 < u T y := by
  let P : Set M := {x | 0 < u T x}
  have hTs : T ∈ Set.Icc (0 : Real) T := ⟨hT.le, le_rfl⟩
  have hPopen : IsOpen P := by
    exact isOpen_lt continuous_const (hu_space T hTs hT).continuous
  have hPclosed : IsClosed P := by
    rw [← closure_subset_iff_isClosed]
    intro a ha
    by_cases haP : a ∈ P
    · exact haP
    let b : SmoothBumpFunction I a := Classical.choice inferInstance
    let C : Real :=
      ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1
    have hC : 0 < C := by
      dsimp [C]
      linarith [norm_nonneg
        (toEuclidean (E := E)).symm.toContinuousLinearMap]
    let S : Set E :=
      Metric.ball (extChartAt I a a) (b.rIn / 2) ∩
        {z | ‖(toEuclidean (E := E)) (z - extChartAt I a a)‖ <
          b.rIn / (4 * C)}
    have hSopen : IsOpen S := by
      exact Metric.isOpen_ball.inter (isOpen_lt (by fun_prop) (by fun_prop))
    have haS : extChartAt I a a ∈ S := by
      constructor
      · change dist (extChartAt I a a) (extChartAt I a a) < b.rIn / 2
        rw [dist_self]
        exact half_pos b.rIn_pos
      · change ‖(toEuclidean (E := E))
          (extChartAt I a a - extChartAt I a a)‖ < b.rIn / (4 * C)
        rw [sub_self, map_zero, norm_zero]
        exact div_pos b.rIn_pos (mul_pos (by norm_num) hC)
    let U : Set M := (chartAt H a).source ∩ extChartAt I a ⁻¹' S
    have hUopen : IsOpen U := isOpen_extChartAt_preimage a hSopen
    have haU : a ∈ U := ⟨mem_chart_source H a, haS⟩
    obtain ⟨c, hcU, hcP⟩ := (mem_closure_iff.mp ha) U hUopen haU
    have hcsource : c ∈ (chartAt H a).source := hcU.1
    have hc_dist_half :
        dist (extChartAt I a c) (extChartAt I a a) < b.rIn / 2 := hcU.2.1
    have hc_dist :
        dist (extChartAt I a c) (extChartAt I a a) < b.rIn := by
      linarith [b.rIn_pos]
    have hc_eucl_small :
        ‖(toEuclidean (E := E))
          (extChartAt I a c - extChartAt I a a)‖ < b.rIn / (4 * C) := hcU.2.2
    let s : Real :=
      (b.rIn - dist (extChartAt I a c) (extChartAt I a a)) / (2 * C)
    have hs : 0 < s := by
      dsimp [s]
      exact div_pos (sub_pos.mpr hc_dist) (mul_pos (by norm_num) hC)
    have hsmall_lt_s : b.rIn / (4 * C) < s := by
      have hden : 0 < 4 * C := mul_pos (by norm_num) hC
      calc
        b.rIn / (4 * C) <
            (2 * (b.rIn - dist (extChartAt I a c) (extChartAt I a a))) /
              (4 * C) := by
          apply (div_lt_div_iff₀ hden hden).mpr
          nlinarith [hc_dist_half]
        _ = s := by
          dsimp [s]
          field_simp
          ring
    have hc_eucl : ‖(toEuclidean (E := E))
        (extChartAt I a c - extChartAt I a a)‖ < s :=
      hc_eucl_small.trans hsmall_lt_s
    let Q : Real := s ^ 2
    have hQ : 0 < Q := sq_pos_of_pos hs
    have hqaQ : strongChartRadiusSq (I := I) a c a < Q := by
      apply (sq_lt_sq₀ (norm_nonneg _) hs.le).mpr
      dsimp [strongChartRadiusSq, Q]
      simpa only [map_sub, norm_sub_rev] using hc_eucl
    obtain ⟨delta, eta, hdelta, heta, V, hV, hlocal⟩ :=
      exists_positive_terminal_cylinder (M := M) hT.le u hu_cont hcP
    obtain ⟨r, hr, hrV⟩ := exists_strongPropagationRadius_sublevel_subset (I := I)
      b hcsource hQ hV
    let rho : M → Real := strongPropagationRadius (I := I) b c Q
    have hrho : ContMDiff I 𝓘(Real, Real) ∞ rho :=
      strongPropagationRadius_contMDiff (I := I) b Q
    have hrho_nonneg : ∀ x : M, 0 ≤ rho x :=
      strongPropagationRadius_nonneg (I := I) b hQ.le
    have hbc : b c = 1 := b.one_of_dist_le hcsource hc_dist.le
    have hrhoc : rho c = 0 := by
      simp [rho, strongPropagationRadius, strongChartRadiusSq, hbc]
    have hrhoa : rho a = strongChartRadiusSq (I := I) a c a := by
      simp [rho, strongPropagationRadius]
    let R : Real := (rho a + Q) / 2
    have hrhoaR : rho a < R := by
      dsimp [R]
      rw [hrhoa]
      linarith
    have hRQ : R < Q := by
      dsimp [R]
      rw [hrhoa]
      linarith
    have hR : 0 < R := lt_of_le_of_lt (hrho_nonneg a) hrhoaR
    have hcompact : IsCompact {x : M | r ≤ rho x ∧ rho x ≤ R} := by
      have hclosed : IsClosed (rho ⁻¹' Set.Icc r R) :=
        isClosed_Icc.preimage hrho.continuous
      change IsCompact (rho ⁻¹' Set.Icc r R)
      exact hclosed.isCompact
    have hgrad : ∀ x : M, r ≤ rho x → rho x ≤ R →
        gradientFun (I := I) g rho x ≠ 0 := by
      intro x hxr hxR
      have hmidR : R < (R + Q) / 2 := by linarith
      have hmidQ : (R + Q) / 2 < Q := by linarith
      have hltmid : rho x < (R + Q) / 2 := hxR.trans_lt hmidR
      have hrad := strongPropagationRadius_lt_imp (I := I) b hmidQ hltmid
      have hbx : b x ≠ 0 := ne_of_gt hrad.1
      have hxsource : x ∈ (chartAt H a).source := by
        apply b.support_subset_source
        simpa [Function.mem_support] using hbx
      have hxcore :
          dist (extChartAt I a x) (extChartAt I a a) < b.rIn := by
        apply strongChartRadiusSq_lt_imp_mem_core (I := I) b hc_dist
        simpa [Q, s, C] using hrad.2
      have hxc : x ≠ c := by
        intro heq
        subst x
        rw [hrhoc] at hxr
        linarith
      exact strongPropagationRadius_gradient_ne_zero (I := I) g b hcsource
        hxsource hxcore hxc Q
    have hlocal' : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
        rho x < r → eta ≤ u t x := by
      intro t ht htnear x hxr
      exact hlocal t ht htnear x (hrV hxr)
    have hpos := scalar_strong_maximum_principle_fixed_metric_of_barrier (I := I)
      g hT u hu_cont hu_nonneg hu_time hu_space hu_super hrho hrho_nonneg
      hR hdelta heta hlocal' hcompact hgrad hrhoaR
    exact (haP hpos).elim
  have hPuniv : P = Set.univ :=
    IsClopen.eq_univ ⟨hPclosed, hPopen⟩ ⟨c, hc⟩
  have hyP : y ∈ P := by rw [hPuniv]; exact Set.mem_univ y
  exact hyP

private theorem fixed_metric_lower_bound_from_positive_time
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T a m : Real} (ha : 0 < a) (haT : a ≤ T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    (hinit : ∀ x : M, m ≤ u a x) :
    ∀ t ∈ Set.Icc a T, ∀ x : M, m ≤ u t x := by
  let S : Real := T - a
  have hS : 0 ≤ S := sub_nonneg.mpr haT
  let v : Real → M → Real := fun s x => u (a + s) x - m
  let G : MetricConnectionFamily (I := I) (M := M) Real :=
    globalStrongStaticMetricFamily (I := I) g
  have hshift : a +ᵥ Set.Icc (0 : Real) S = Set.Icc a T := by
    dsimp [S]
    exact vadd_Icc_eq_Icc (a := a) (T := T)
  have hsub : Set.Icc a T ⊆ Set.Icc (0 : Real) T := by
    intro t ht
    exact ⟨ha.le.trans ht.1, ht.2⟩
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) S) := by
    have hmap : Set.MapsTo (fun p : Real × M => (a + p.1, p.2))
        (spacetimeSlab (M := M) S) (spacetimeSlab (M := M) T) := by
      intro p hp
      exact ⟨⟨by linarith [ha, hp.1.1], by dsimp [S] at hp; linarith [hp.1.2]⟩,
        Set.mem_univ p.2⟩
    have hcomp := hu_cont.comp (by fun_prop) hmap
    simpa [v] using hcomp.sub continuous_const.continuousOn
  have hv0 : ∀ x : M, 0 ≤ v 0 x := by
    intro x
    simpa [v] using sub_nonneg.mpr (hinit x)
  have hv_time : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => v q x) (Set.Icc 0 S) s := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    have hmap : Set.MapsTo (fun q : Real => a + q)
        (Set.Icc 0 S) (Set.Icc 0 T) := by
      intro q hq'
      apply hsub
      rw [← hshift]
      exact ⟨q, hq', rfl⟩
    have hcomp := (hu_time (a + s) hq hqpos x).comp s
      (by fun_prop) hmap
    simpa [v] using hcomp.sub_const m
  have hv_space : ∀ s ∈ Set.Icc 0 S, 0 < s →
      ContMDiff I 𝓘(Real, Real) ∞ (v s) := by
    intro s hs hspos
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    simpa [v] using (hu_space (a + s) hq hqpos).sub contMDiff_const
  have hv_mdiff : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v s) x := by
    intro s hs hspos x
    exact (hv_space s hs hspos).mdifferentiable (by simp) x
  have hv_grad : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (v s) y) x := by
    intro s hs hspos x
    simpa [G] using gradientFun_mdiffAt (I := I) g (hv_space s hs hspos) x
  have hv_super : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G S (fun _ _ => 0) v s x := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    have hderiv_shift := derivWithin_comp_const_add
      (fun q : Real => u q x) a (Set.Icc 0 S) s
    rw [hshift] at hderiv_shift
    have haTlt : a < T := by
      dsimp [S] at hs
      linarith [hs.2, hspos]
    have hqaT : a + s ∈ Set.Icc a T := by
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hderiv_subset := derivWithin_subset hsub
      ((uniqueDiffOn_Icc haTlt).uniqueDiffWithinAt hqaT)
      (hu_time (a + s) hq hqpos x)
    have hderiv : derivWithin (fun q => v q x) (Set.Icc 0 S) s =
        derivWithin (fun q => u q x) (Set.Icc 0 T) (a + s) := by
      rw [show (fun q => v q x) =
          fun q => u (a + q) x - m from rfl]
      rw [derivWithin_sub_const]
      exact hderiv_shift.trans hderiv_subset
    have hheat := heatOperatorWithDrift_sub_const (I := I) G s
      (fun _ : M => 0) m
      (fun y => (hu_space (a + s) hq hqpos).mdifferentiable (by simp) y) x
    have hlapAt := laplacianAt_eq_delta (I := I) G s
      (hu_space (a + s) hq hqpos) rfl x
    unfold parabolicOperatorWithDrift
    rw [hderiv]
    change 0 ≤ derivWithin (fun q => u q x) (Set.Icc 0 T) (a + s) -
      heatOperatorWithDrift (I := I) G s (fun _ : M => 0) (v s) x
    rw [show heatOperatorWithDrift (I := I) G s (fun _ : M => 0) (v s) x =
        heatOperatorWithDrift (I := I) G s (fun _ : M => 0) (u (a + s)) x by
      simpa [v] using hheat]
    unfold heatOperatorWithDrift driftTerm
    rw [hlapAt]
    simpa [G] using hu_super (a + s) hq hqpos x
  have hv_nonneg := strict_barrier_positive_region (I := I) G S (fun _ _ => 0) v
    hv_cont hv0 hv_time hv_mdiff hv_grad
    (fun s hs hspos x _ => hv_super s hs hspos x)
  intro t ht x
  have hs : t - a ∈ Set.Icc (0 : Real) S := by
    dsimp [S]
    constructor <;> linarith [ht.1, ht.2]
  have hv := hv_nonneg (t - a) hs x
  simpa [v] using hv

private theorem exists_positive_time_of_initial_value
    {T : Real} (hT : 0 < T) (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    {x : M} (hx : 0 < u 0 x) :
    ∃ t ∈ Set.Ioc (0 : Real) T, 0 < u t x := by
  let eta : Real := u 0 x / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hcurve : ContinuousOn (fun t : Real => u t x) (Set.Icc 0 T) := by
    have hmap : Set.MapsTo (fun t : Real => (t, x)) (Set.Icc 0 T)
        (spacetimeSlab (M := M) T) := by
      intro t ht
      exact ⟨ht, Set.mem_univ x⟩
    simpa using hu_cont.comp (by fun_prop) hmap
  have htarget : Set.Ioi eta ∈ nhds (u 0 x) :=
    Ioi_mem_nhds (by dsimp [eta]; linarith)
  have hpre : (fun t : Real => u t x) ⁻¹' Set.Ioi eta ∈
      nhdsWithin 0 (Set.Icc 0 T) :=
    (hcurve 0 ⟨le_rfl, hT.le⟩).preimage_mem_nhdsWithin htarget
  rcases Metric.mem_nhdsWithin_iff.mp hpre with ⟨epsilon, hepsilon, hball⟩
  let t : Real := min (T / 2) (epsilon / 2)
  have ht : 0 < t := lt_min (half_pos hT) (half_pos hepsilon)
  have htT : t ≤ T := (min_le_left _ _).trans (half_le_self hT.le)
  have htball : t ∈ Metric.ball (0 : Real) epsilon := by
    change dist t 0 < epsilon
    rw [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg ht.le]
    exact (min_le_right _ _).trans_lt (half_lt_self hepsilon)
  have hpos := hball ⟨htball, ⟨ht.le, htT⟩⟩
  exact ⟨t, ⟨ht, htT⟩, heta.trans hpos⟩

private theorem scalar_strong_maximum_principle_fixed_metric_spatial_at
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T t : Real} (ht : 0 < t) (htT : t ≤ T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ s ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u s x)
    (hu_time : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => u q x) (Set.Icc 0 T) s)
    (hu_space : ∀ s ∈ Set.Icc 0 T, 0 < s →
      ContMDiff I 𝓘(Real, Real) ∞ (u s))
    (hu_super : ∀ (s : Real) (hs : s ∈ Set.Icc 0 T) (hspos : 0 < s)
      (x : M),
      0 ≤ derivWithin (fun q => u q x) (Set.Icc 0 T) s -
        Δ_g (I := I) g ⟨u s, hu_space s hs hspos⟩ x)
    {c : M} (hc : 0 < u t c) (y : M) :
    0 < u t y := by
  have hsub : Set.Icc (0 : Real) t ⊆ Set.Icc 0 T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htT⟩
  have hu_time' : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => u q x) (Set.Icc 0 t) s := by
    intro s hs hspos x
    exact (hu_time s (hsub hs) hspos x).mono hsub
  have hu_space' : ∀ s ∈ Set.Icc 0 t, 0 < s →
      ContMDiff I 𝓘(Real, Real) ∞ (u s) := by
    intro s hs hspos
    exact hu_space s (hsub hs) hspos
  have hu_super' : ∀ (s : Real) (hs : s ∈ Set.Icc 0 t) (hspos : 0 < s)
      (x : M),
      0 ≤ derivWithin (fun q => u q x) (Set.Icc 0 t) s -
        Δ_g (I := I) g ⟨u s, hu_space' s hs hspos⟩ x := by
    intro s hs hspos x
    have hderiv := derivWithin_subset hsub
      ((uniqueDiffOn_Icc ht).uniqueDiffWithinAt hs)
      (hu_time s (hsub hs) hspos x)
    rw [hderiv]
    exact hu_super s (hsub hs) hspos x
  exact fixed_metric_spatial_zero_drift (I := I)
    g ht u (hu_cont.mono (fun p hp => ⟨hsub hp.1, hp.2⟩))
    (fun s hs x => hu_nonneg s (hsub hs) x) hu_time' hu_space'
    hu_super' hc y

private theorem fixed_metric_zero_drift
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  intro t ht x
  apply le_antisymm (le_of_not_gt ?_) (hu_nonneg t ht x)
  intro htx
  obtain ⟨a, ha, haT, c, hc⟩ :
      ∃ a : Real, 0 < a ∧ a ≤ T ∧ ∃ c : M, 0 < u a c := by
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨a, haI, haPos⟩ :=
        exists_positive_time_of_initial_value (M := M) hT u hu_cont htx
      exact ⟨a, haI.1, haI.2, x, haPos⟩
    · exact ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2, x, htx⟩
  have hslice : ∀ z : M, 0 < u a z := by
    intro z
    exact scalar_strong_maximum_principle_fixed_metric_spatial_at (I := I)
      g ha haT u hu_cont hu_nonneg hu_time hu_space hu_super hc z
  obtain ⟨xm, _, hxmin⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
    Set.univ_nonempty (hu_space a ⟨ha.le, haT⟩ ha).continuous.continuousOn
  let m : Real := u a xm
  have hm : 0 < m := hslice xm
  have hinit : ∀ z : M, m ≤ u a z := by
    intro z
    exact hxmin (Set.mem_univ z)
  have hlower := fixed_metric_lower_bound_from_positive_time (I := I)
    g ha haT u hu_cont hu_time hu_space hu_super hinit T ⟨haT, le_rfl⟩ y
  rw [hy] at hlower
  exact (not_lt_of_ge hlower hm).elim

private theorem fixed_metric_positive_zero_drift
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (le_of_not_gt hy)
    (hu_nonneg T ⟨hT.le, le_rfl⟩ y)
  have hpast := fixed_metric_zero_drift (I := I)
    g hT u hu_cont hu_nonneg hu_time hu_space hu_super hy0 t ht x
  linarith

private theorem fixed_metric_with_drift_strong_maximum_principle_of_barrier
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {C : Real} (hC : 0 ≤ C)
    (hX : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      g.inner x (X t x) (X t x) ≤ C)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)))
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hcompact : IsCompact {x : M | r ≤ rho x ∧ rho x ≤ R})
    (hgrad_ne : ∀ x : M, r ≤ rho x → rho x ≤ R →
      gradientFun (I := I) g rho x ≠ 0)
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let K : Set M := {x : M | r ≤ rho x ∧ rho x ≤ R}
  let q : M → Real := fun x => g.inner x
    (gradientFun (I := I) g rho x) (gradientFun (I := I) g rho x)
  let ell : M → Real := fun x => |Δ_g (I := I) g ⟨rho, hrho⟩ x|
  have hq_cont : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hgrad : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% fun y : M => gradientFun (I := I) g rho y) x :=
      (gradientFun_smooth (I := I) g hrho).contMDiffAt
    exact (CovariantDerivative.metric_inner_contMDiffAt
      (I := I) g hgrad hgrad le_rfl).continuousAt
  have hell_cont : Continuous ell :=
    continuous_abs.comp (Δ_g_contMDiff (I := I) g ⟨rho, hrho⟩).continuous
  obtain ⟨m, B, hm, hB, hgrad_lower, hheat_upper⟩ :
      ∃ m B : Real, 0 < m ∧ 0 ≤ B ∧
        (∀ x ∈ K, m ≤ q x) ∧
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ K,
          Δ_g (I := I) g ⟨rho, hrho⟩ x +
            g.inner x (X t x) (gradientFun (I := I) g rho x) ≤ B) := by
    by_cases hKne : K.Nonempty
    · obtain ⟨xm, hxm, hxmin⟩ := hcompact.exists_isMinOn
        (by simpa [K] using hKne) hq_cont.continuousOn
      obtain ⟨xq, hxq, hxqmax⟩ := hcompact.exists_isMaxOn
        (by simpa [K] using hKne) hq_cont.continuousOn
      obtain ⟨xB, hxB, hxBmax⟩ := hcompact.exists_isMaxOn
        (by simpa [K] using hKne) hell_cont.continuousOn
      have hqm : 0 < q xm := g.pos xm _ (hgrad_ne xm hxm.1 hxm.2)
      have hqq : 0 ≤ q xq := metric_inner_self_nonneg (I := I) (M := M) g _ _
      refine ⟨q xm, ell xB + C + q xq, hqm, by positivity,
        (fun x hx => hxmin (by simpa [K] using hx)), ?_⟩
      intro t ht x hx
      have hqx : q x ≤ q xq := hxqmax (by simpa [K] using hx)
      have hq0 : 0 ≤ q x := metric_inner_self_nonneg (I := I) (M := M) g _ _
      have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g x
        (X t x) (gradientFun (I := I) g rho x)
      have hsq : (g.inner x (X t x) (gradientFun (I := I) g rho x)) ^ 2 ≤
          C * q xq := by
        exact hcs.trans (mul_le_mul (hX t ht x) hqx hq0 hC)
      have hdrift : g.inner x (X t x) (gradientFun (I := I) g rho x) ≤
          C + q xq := by
        nlinarith [sq_nonneg (C - q xq),
          sq_nonneg (g.inner x (X t x) (gradientFun (I := I) g rho x) +
            C + q xq)]
      have hlap := hxBmax (by simpa [K] using hx)
      change |Δ_g (I := I) g ⟨rho, hrho⟩ x| ≤ ell xB at hlap
      have hself : Δ_g (I := I) g ⟨rho, hrho⟩ x ≤ ell xB :=
        (le_abs_self _).trans hlap
      linarith
    · refine ⟨1, 0, by positivity, le_rfl, ?_, ?_⟩
      · intro x hx
        exact (hKne ⟨x, hx⟩).elim
      · intro t ht x hx
        exact (hKne ⟨x, hx⟩).elim
  let kappa : Real := max (R / T ^ 2) (R / delta ^ 2) + 1
  have hT_sq : 0 < T ^ 2 := sq_pos_of_pos hT
  have hdelta_sq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    linarith [le_max_left (R / T ^ 2) (R / delta ^ 2), div_pos hR hT_sq]
  have hinit : R ≤ kappa * T ^ 2 := by
    apply le_of_lt ((div_lt_iff₀ hT_sq).mp ?_)
    dsimp [kappa]
    linarith [le_max_left (R / T ^ 2) (R / delta ^ 2)]
  have htime : R ≤ kappa * delta ^ 2 := by
    apply le_of_lt ((div_lt_iff₀ hdelta_sq).mp ?_)
    dsimp [kappa]
    linarith [le_max_right (R / T ^ 2) (R / delta ^ 2)]
  let alpha : Real := (2 * kappa * T + B) / m + 1
  have hnum : 0 ≤ 2 * kappa * T + B := by positivity
  have halpha : 0 < alpha := by
    dsimp [alpha]
    have := div_nonneg hnum hm.le
    linarith
  have hdom : 2 * kappa * T + B ≤ alpha * m := by
    apply le_of_lt ((div_lt_iff₀ hm).mp ?_)
    dsimp [alpha]
    linarith
  apply scalar_strong_maximum_principle_fixed_metric_with_drift_of_barrier (I := I)
    g hT X u hu_cont hu_nonneg hu_time hu_space hu_super hrho hrho_nonneg
    hR hdelta heta hlocal (m := m) (B := B) (kappa := kappa) (alpha := alpha)
  · intro x hxr hxR
    exact hgrad_lower x ⟨hxr, hxR⟩
  · intro t ht htpos x hxr hxR
    exact hheat_upper t ht x ⟨hxr, hxR⟩
  · exact hkappa
  · exact hinit
  · exact htime
  · exact halpha
  · exact hdom
  · exact hy

theorem scalar_strong_maximum_principle_fixed_metric_with_drift_spatial
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {C : Real} (hC : 0 ≤ C)
    (hX : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      g.inner x (X t x) (X t x) ≤ C)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)))
    {c : M} (hc : 0 < u T c) (y : M) :
    0 < u T y := by
  let P : Set M := {x | 0 < u T x}
  have hTs : T ∈ Set.Icc (0 : Real) T := ⟨hT.le, le_rfl⟩
  have hPopen : IsOpen P := by
    exact isOpen_lt continuous_const (hu_space T hTs hT).continuous
  have hPclosed : IsClosed P := by
    rw [← closure_subset_iff_isClosed]
    intro a ha
    by_cases haP : a ∈ P
    · exact haP
    let b : SmoothBumpFunction I a := Classical.choice inferInstance
    let Cchart : Real :=
      ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1
    have hCchart : 0 < Cchart := by
      dsimp [Cchart]
      linarith [norm_nonneg
        (toEuclidean (E := E)).symm.toContinuousLinearMap]
    let S : Set E :=
      Metric.ball (extChartAt I a a) (b.rIn / 2) ∩
        {z | ‖(toEuclidean (E := E)) (z - extChartAt I a a)‖ <
          b.rIn / (4 * Cchart)}
    have hSopen : IsOpen S := by
      exact Metric.isOpen_ball.inter (isOpen_lt (by fun_prop) (by fun_prop))
    have haS : extChartAt I a a ∈ S := by
      constructor
      · change dist (extChartAt I a a) (extChartAt I a a) < b.rIn / 2
        rw [dist_self]
        exact half_pos b.rIn_pos
      · change ‖(toEuclidean (E := E))
          (extChartAt I a a - extChartAt I a a)‖ < b.rIn / (4 * Cchart)
        rw [sub_self, map_zero, norm_zero]
        exact div_pos b.rIn_pos (mul_pos (by norm_num) hCchart)
    let U : Set M := (chartAt H a).source ∩ extChartAt I a ⁻¹' S
    have hUopen : IsOpen U := isOpen_extChartAt_preimage a hSopen
    have haU : a ∈ U := ⟨mem_chart_source H a, haS⟩
    obtain ⟨c, hcU, hcP⟩ := (mem_closure_iff.mp ha) U hUopen haU
    have hcsource : c ∈ (chartAt H a).source := hcU.1
    have hc_dist_half :
        dist (extChartAt I a c) (extChartAt I a a) < b.rIn / 2 := hcU.2.1
    have hc_dist :
        dist (extChartAt I a c) (extChartAt I a a) < b.rIn := by
      linarith [b.rIn_pos]
    have hc_eucl_small :
        ‖(toEuclidean (E := E))
          (extChartAt I a c - extChartAt I a a)‖ < b.rIn / (4 * Cchart) := hcU.2.2
    let s : Real :=
      (b.rIn - dist (extChartAt I a c) (extChartAt I a a)) / (2 * Cchart)
    have hs : 0 < s := by
      dsimp [s]
      exact div_pos (sub_pos.mpr hc_dist) (mul_pos (by norm_num) hCchart)
    have hsmall_lt_s : b.rIn / (4 * Cchart) < s := by
      have hden : 0 < 4 * Cchart := mul_pos (by norm_num) hCchart
      calc
        b.rIn / (4 * Cchart) <
            (2 * (b.rIn - dist (extChartAt I a c) (extChartAt I a a))) /
              (4 * Cchart) := by
          apply (div_lt_div_iff₀ hden hden).mpr
          nlinarith [hc_dist_half]
        _ = s := by
          dsimp [s]
          field_simp
          ring
    have hc_eucl : ‖(toEuclidean (E := E))
        (extChartAt I a c - extChartAt I a a)‖ < s :=
      hc_eucl_small.trans hsmall_lt_s
    let Q : Real := s ^ 2
    have hQ : 0 < Q := sq_pos_of_pos hs
    have hqaQ : strongChartRadiusSq (I := I) a c a < Q := by
      apply (sq_lt_sq₀ (norm_nonneg _) hs.le).mpr
      dsimp [strongChartRadiusSq, Q]
      simpa only [map_sub, norm_sub_rev] using hc_eucl
    obtain ⟨delta, eta, hdelta, heta, V, hV, hlocal⟩ :=
      exists_positive_terminal_cylinder (M := M) hT.le u hu_cont hcP
    obtain ⟨r, hr, hrV⟩ := exists_strongPropagationRadius_sublevel_subset (I := I)
      b hcsource hQ hV
    let rho : M → Real := strongPropagationRadius (I := I) b c Q
    have hrho : ContMDiff I 𝓘(Real, Real) ∞ rho :=
      strongPropagationRadius_contMDiff (I := I) b Q
    have hrho_nonneg : ∀ x : M, 0 ≤ rho x :=
      strongPropagationRadius_nonneg (I := I) b hQ.le
    have hbc : b c = 1 := b.one_of_dist_le hcsource hc_dist.le
    have hrhoc : rho c = 0 := by
      simp [rho, strongPropagationRadius, strongChartRadiusSq, hbc]
    have hrhoa : rho a = strongChartRadiusSq (I := I) a c a := by
      simp [rho, strongPropagationRadius]
    let R : Real := (rho a + Q) / 2
    have hrhoaR : rho a < R := by
      dsimp [R]
      rw [hrhoa]
      linarith
    have hRQ : R < Q := by
      dsimp [R]
      rw [hrhoa]
      linarith
    have hR : 0 < R := lt_of_le_of_lt (hrho_nonneg a) hrhoaR
    have hcompact : IsCompact {x : M | r ≤ rho x ∧ rho x ≤ R} := by
      have hclosed : IsClosed (rho ⁻¹' Set.Icc r R) :=
        isClosed_Icc.preimage hrho.continuous
      change IsCompact (rho ⁻¹' Set.Icc r R)
      exact hclosed.isCompact
    have hgrad : ∀ x : M, r ≤ rho x → rho x ≤ R →
        gradientFun (I := I) g rho x ≠ 0 := by
      intro x hxr hxR
      have hmidR : R < (R + Q) / 2 := by linarith
      have hmidQ : (R + Q) / 2 < Q := by linarith
      have hltmid : rho x < (R + Q) / 2 := hxR.trans_lt hmidR
      have hrad := strongPropagationRadius_lt_imp (I := I) b hmidQ hltmid
      have hbx : b x ≠ 0 := ne_of_gt hrad.1
      have hxsource : x ∈ (chartAt H a).source := by
        apply b.support_subset_source
        simpa [Function.mem_support] using hbx
      have hxcore :
          dist (extChartAt I a x) (extChartAt I a a) < b.rIn := by
        apply strongChartRadiusSq_lt_imp_mem_core (I := I) b hc_dist
        simpa [Q, s, Cchart] using hrad.2
      have hxc : x ≠ c := by
        intro heq
        subst x
        rw [hrhoc] at hxr
        linarith
      exact strongPropagationRadius_gradient_ne_zero (I := I) g b hcsource
        hxsource hxcore hxc Q
    have hlocal' : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
        rho x < r → eta ≤ u t x := by
      intro t ht htnear x hxr
      exact hlocal t ht htnear x (hrV hxr)
    have hpos :=
      fixed_metric_with_drift_strong_maximum_principle_of_barrier (I := I)
        g hT X hC hX u hu_cont hu_nonneg hu_time hu_space hu_super hrho hrho_nonneg
      hR hdelta heta hlocal' hcompact hgrad hrhoaR
    exact (haP hpos).elim
  have hPuniv : P = Set.univ :=
    IsClopen.eq_univ ⟨hPclosed, hPopen⟩ ⟨c, hc⟩
  have hyP : y ∈ P := by rw [hPuniv]; exact Set.mem_univ y
  exact hyP

private theorem fixed_metric_with_drift_lower_bound_from_positive_time
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T a m : Real} (ha : 0 < a) (haT : a ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)))
    (hinit : ∀ x : M, m ≤ u a x) :
    ∀ t ∈ Set.Icc a T, ∀ x : M, m ≤ u t x := by
  let S : Real := T - a
  have hS : 0 ≤ S := sub_nonneg.mpr haT
  let v : Real → M → Real := fun s x => u (a + s) x - m
  let G : MetricConnectionFamily (I := I) (M := M) Real :=
    globalStrongStaticMetricFamily (I := I) g
  let X' : Real → (x : M) → TangentSpace I x := fun s x => X (a + s) x
  have hshift : a +ᵥ Set.Icc (0 : Real) S = Set.Icc a T := by
    dsimp [S]
    exact vadd_Icc_eq_Icc (a := a) (T := T)
  have hsub : Set.Icc a T ⊆ Set.Icc (0 : Real) T := by
    intro t ht
    exact ⟨ha.le.trans ht.1, ht.2⟩
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) S) := by
    have hmap : Set.MapsTo (fun p : Real × M => (a + p.1, p.2))
        (spacetimeSlab (M := M) S) (spacetimeSlab (M := M) T) := by
      intro p hp
      exact ⟨⟨by linarith [ha, hp.1.1], by dsimp [S] at hp; linarith [hp.1.2]⟩,
        Set.mem_univ p.2⟩
    have hcomp := hu_cont.comp (by fun_prop) hmap
    simpa [v] using hcomp.sub continuous_const.continuousOn
  have hv0 : ∀ x : M, 0 ≤ v 0 x := by
    intro x
    simpa [v] using sub_nonneg.mpr (hinit x)
  have hv_time : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => v q x) (Set.Icc 0 S) s := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    have hmap : Set.MapsTo (fun q : Real => a + q)
        (Set.Icc 0 S) (Set.Icc 0 T) := by
      intro q hq'
      apply hsub
      rw [← hshift]
      exact ⟨q, hq', rfl⟩
    have hcomp := (hu_time (a + s) hq hqpos x).comp s
      (by fun_prop) hmap
    simpa [v] using hcomp.sub_const m
  have hv_space : ∀ s ∈ Set.Icc 0 S, 0 < s →
      ContMDiff I 𝓘(Real, Real) ∞ (v s) := by
    intro s hs hspos
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    simpa [v] using (hu_space (a + s) hq hqpos).sub contMDiff_const
  have hv_mdiff : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v s) x := by
    intro s hs hspos x
    exact (hv_space s hs hspos).mdifferentiable (by simp) x
  have hv_grad : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (v s) y) x := by
    intro s hs hspos x
    simpa [G] using gradientFun_mdiffAt (I := I) g (hv_space s hs hspos) x
  have hv_super : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G S X' v s x := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    have hderiv_shift := derivWithin_comp_const_add
      (fun q : Real => u q x) a (Set.Icc 0 S) s
    rw [hshift] at hderiv_shift
    have haTlt : a < T := by
      dsimp [S] at hs
      linarith [hs.2, hspos]
    have hqaT : a + s ∈ Set.Icc a T := by
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hderiv_subset := derivWithin_subset hsub
      ((uniqueDiffOn_Icc haTlt).uniqueDiffWithinAt hqaT)
      (hu_time (a + s) hq hqpos x)
    have hderiv : derivWithin (fun q => v q x) (Set.Icc 0 S) s =
        derivWithin (fun q => u q x) (Set.Icc 0 T) (a + s) := by
      rw [show (fun q => v q x) =
          fun q => u (a + q) x - m from rfl]
      rw [derivWithin_sub_const]
      exact hderiv_shift.trans hderiv_subset
    have hheat := heatOperatorWithDrift_sub_const (I := I) G s
      (X' s) m
      (fun y => (hu_space (a + s) hq hqpos).mdifferentiable (by simp) y) x
    have hlapAt := laplacianAt_eq_delta (I := I) G s
      (hu_space (a + s) hq hqpos) rfl x
    unfold parabolicOperatorWithDrift
    rw [hderiv]
    change 0 ≤ derivWithin (fun q => u q x) (Set.Icc 0 T) (a + s) -
      heatOperatorWithDrift (I := I) G s (X' s) (v s) x
    rw [show heatOperatorWithDrift (I := I) G s (X' s) (v s) x =
        heatOperatorWithDrift (I := I) G s (X' s) (u (a + s)) x by
      simpa [v] using hheat]
    unfold heatOperatorWithDrift driftTerm gradientAt
    rw [hlapAt]
    simpa [G, X'] using hu_super (a + s) hq hqpos x
  have hv_nonneg := strict_barrier_positive_region (I := I) G S X' v
    hv_cont hv0 hv_time hv_mdiff hv_grad
    (fun s hs hspos x _ => hv_super s hs hspos x)
  intro t ht x
  have hs : t - a ∈ Set.Icc (0 : Real) S := by
    dsimp [S]
    constructor <;> linarith [ht.1, ht.2]
  have hv := hv_nonneg (t - a) hs x
  simpa [v] using hv

private theorem scalar_strong_maximum_principle_fixed_metric_with_drift_spatial_at
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T t : Real} (ht : 0 < t) (htT : t ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    {C : Real} (hC : 0 ≤ C)
    (hX : ∀ s ∈ Set.Icc 0 T, ∀ x : M,
      g.inner x (X s x) (X s x) ≤ C)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ s ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u s x)
    (hu_time : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => u q x) (Set.Icc 0 T) s)
    (hu_space : ∀ s ∈ Set.Icc 0 T, 0 < s →
      ContMDiff I 𝓘(Real, Real) ∞ (u s))
    (hu_super : ∀ (s : Real) (hs : s ∈ Set.Icc 0 T) (hspos : 0 < s)
      (x : M),
      0 ≤ derivWithin (fun q => u q x) (Set.Icc 0 T) s -
        (Δ_g (I := I) g ⟨u s, hu_space s hs hspos⟩ x +
          g.inner x (X s x) (gradientFun (I := I) g (u s) x)))
    {c : M} (hc : 0 < u t c) (y : M) :
    0 < u t y := by
  have hsub : Set.Icc (0 : Real) t ⊆ Set.Icc 0 T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htT⟩
  have hu_time' : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => u q x) (Set.Icc 0 t) s := by
    intro s hs hspos x
    exact (hu_time s (hsub hs) hspos x).mono hsub
  have hu_space' : ∀ s ∈ Set.Icc 0 t, 0 < s →
      ContMDiff I 𝓘(Real, Real) ∞ (u s) := by
    intro s hs hspos
    exact hu_space s (hsub hs) hspos
  have hu_super' : ∀ (s : Real) (hs : s ∈ Set.Icc 0 t) (hspos : 0 < s)
      (x : M),
      0 ≤ derivWithin (fun q => u q x) (Set.Icc 0 t) s -
        (Δ_g (I := I) g ⟨u s, hu_space' s hs hspos⟩ x +
          g.inner x (X s x) (gradientFun (I := I) g (u s) x)) := by
    intro s hs hspos x
    have hderiv := derivWithin_subset hsub
      ((uniqueDiffOn_Icc ht).uniqueDiffWithinAt hs)
      (hu_time s (hsub hs) hspos x)
    rw [hderiv]
    exact hu_super s (hsub hs) hspos x
  exact scalar_strong_maximum_principle_fixed_metric_with_drift_spatial (I := I)
    g ht X hC (fun s hs x => hX s (hsub hs) x) u (hu_cont.mono (fun p hp => ⟨hsub hp.1, hp.2⟩))
    (fun s hs x => hu_nonneg s (hsub hs) x) hu_time' hu_space'
    hu_super' hc y

theorem scalar_strong_maximum_principle_fixed_metric_with_drift
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {C : Real} (hC : 0 ≤ C)
    (hX : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      g.inner x (X t x) (X t x) ≤ C)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)))
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  intro t ht x
  apply le_antisymm (le_of_not_gt ?_) (hu_nonneg t ht x)
  intro htx
  obtain ⟨a, ha, haT, c, hc⟩ :
      ∃ a : Real, 0 < a ∧ a ≤ T ∧ ∃ c : M, 0 < u a c := by
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨a, haI, haPos⟩ :=
        exists_positive_time_of_initial_value (M := M) hT u hu_cont htx
      exact ⟨a, haI.1, haI.2, x, haPos⟩
    · exact ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2, x, htx⟩
  have hslice : ∀ z : M, 0 < u a z := by
    intro z
    exact scalar_strong_maximum_principle_fixed_metric_with_drift_spatial_at (I := I)
      g ha haT X hC hX u hu_cont hu_nonneg hu_time hu_space hu_super hc z
  obtain ⟨xm, _, hxmin⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
    Set.univ_nonempty (hu_space a ⟨ha.le, haT⟩ ha).continuous.continuousOn
  let m : Real := u a xm
  have hm : 0 < m := hslice xm
  have hinit : ∀ z : M, m ≤ u a z := by
    intro z
    exact hxmin (Set.mem_univ z)
  have hlower := fixed_metric_with_drift_lower_bound_from_positive_time (I := I)
    g ha haT X u hu_cont hu_time hu_space hu_super hinit T ⟨haT, le_rfl⟩ y
  rw [hy] at hlower
  exact (not_lt_of_ge hlower hm).elim

theorem scalar_strong_maximum_principle_fixed_metric_with_drift_positive
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {C : Real} (hC : 0 ≤ C)
    (hX : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      g.inner x (X t x) (X t x) ≤ C)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)))
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (le_of_not_gt hy)
    (hu_nonneg T ⟨hT.le, le_rfl⟩ y)
  have hpast := scalar_strong_maximum_principle_fixed_metric_with_drift (I := I)
    g hT X hC hX u hu_cont hu_nonneg hu_time hu_space hu_super hy0 t ht x
  linarith

private theorem time_dependent_metric_with_drift_strong_maximum_principle_of_barrier
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hcompact : IsCompact {x : M | r ≤ rho x ∧ rho x ≤ R})
    (hgrad_ne : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      gradientFun (I := I) (G.metric t) rho x ≠ 0)
    (hgrad_cont : ContinuousOn (fun p : Real × M =>
      (G.metric p.1).inner p.2
        (gradientFun (I := I) (G.metric p.1) rho p.2)
        (gradientFun (I := I) (G.metric p.1) rho p.2))
      (spacetimeSlab (M := M) T))
    (hheat_cont : ContinuousOn (fun p : Real × M =>
      heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
      (spacetimeSlab (M := M) T))
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let K : Set M := {x : M | r ≤ rho x ∧ rho x ≤ R}
  let S : Set (Real × M) := Set.Icc 0 T ×ˢ K
  let q : Real × M → Real := fun p => (G.metric p.1).inner p.2
    (gradientFun (I := I) (G.metric p.1) rho p.2)
    (gradientFun (I := I) (G.metric p.1) rho p.2)
  let ell : Real × M → Real := fun p =>
    |heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2|
  have hScompact : IsCompact S := isCompact_Icc.prod hcompact
  have hq_cont : ContinuousOn q S := by
    exact hgrad_cont.mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
  have hell_cont : ContinuousOn ell S := by
    exact (hheat_cont.abs).mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
  obtain ⟨m, B, hm, hB, hgrad_lower, hheat_upper⟩ :
      ∃ m B : Real, 0 < m ∧ 0 ≤ B ∧
        (∀ p ∈ S, m ≤ q p) ∧
        (∀ p ∈ S,
          heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2 ≤ B) := by
    by_cases hKne : K.Nonempty
    · have hSne : S.Nonempty := by
        obtain ⟨x, hx⟩ := hKne
        exact ⟨(0, x), ⟨⟨le_rfl, hT.le⟩, hx⟩⟩
      obtain ⟨pm, hpm, hpmin⟩ := hScompact.exists_isMinOn hSne hq_cont
      obtain ⟨pB, hpB, hpBmax⟩ := hScompact.exists_isMaxOn hSne hell_cont
      have hqm : 0 < q pm := by
        exact (G.metric pm.1).pos pm.2 _
          (hgrad_ne pm.1 hpm.1 pm.2 hpm.2.1 hpm.2.2)
      refine ⟨q pm, ell pB, hqm, by positivity, hpmin, ?_⟩
      intro p hp
      have habs := hpBmax hp
      have hself := le_abs_self
        (heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
      change |heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2| ≤
        ell pB at habs
      exact hself.trans habs
    · refine ⟨1, 0, by positivity, le_rfl, ?_, ?_⟩
      · intro p hp
        exact (hKne ⟨p.2, hp.2⟩).elim
      · intro p hp
        exact (hKne ⟨p.2, hp.2⟩).elim
  let kappa : Real := max (R / T ^ 2) (R / delta ^ 2) + 1
  have hT_sq : 0 < T ^ 2 := sq_pos_of_pos hT
  have hdelta_sq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    linarith [le_max_left (R / T ^ 2) (R / delta ^ 2), div_pos hR hT_sq]
  have hinit : R ≤ kappa * T ^ 2 := by
    apply le_of_lt ((div_lt_iff₀ hT_sq).mp ?_)
    dsimp [kappa]
    linarith [le_max_left (R / T ^ 2) (R / delta ^ 2)]
  have htime : R ≤ kappa * delta ^ 2 := by
    apply le_of_lt ((div_lt_iff₀ hdelta_sq).mp ?_)
    dsimp [kappa]
    linarith [le_max_right (R / T ^ 2) (R / delta ^ 2)]
  let alpha : Real := (2 * kappa * T + B) / m + 1
  have hnum : 0 ≤ 2 * kappa * T + B := by positivity
  have halpha : 0 < alpha := by
    dsimp [alpha]
    have := div_nonneg hnum hm.le
    linarith
  have hdom : 2 * kappa * T + B ≤ alpha * m := by
    apply le_of_lt ((div_lt_iff₀ hm).mp ?_)
    dsimp [alpha]
    linarith
  apply scalar_strong_maximum_principle_of_barrier (I := I)
    G hT X u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hrho
    hrho_nonneg hR hdelta heta hlocal (m := m) (B := B)
    (kappa := kappa) (alpha := alpha)
  · intro t ht htpos x hxr hxR
    exact hgrad_lower (t, x) ⟨ht, hxr, hxR⟩
  · intro t ht htpos x hxr hxR
    exact hheat_upper (t, x) ⟨ht, hxr, hxR⟩
  · exact hkappa
  · exact hinit
  · exact htime
  · exact halpha
  · exact hdom
  · exact hy

private theorem time_dependent_metric_strong_maximum_principle_of_barrier
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hcompact : IsCompact {x : M | r ≤ rho x ∧ rho x ≤ R})
    (hgrad_ne : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      gradientFun (I := I) (G.metric t) rho x ≠ 0)
    (hgrad_cont : ContinuousOn (fun p : Real × M =>
      (G.metric p.1).inner p.2
        (gradientFun (I := I) (G.metric p.1) rho p.2)
        (gradientFun (I := I) (G.metric p.1) rho p.2))
      (spacetimeSlab (M := M) T))
    (hlaplacian_cont : ContinuousOn (fun p : Real × M =>
      laplacianAt (I := I) G p.1 rho p.2)
      (spacetimeSlab (M := M) T))
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let K : Set M := {x : M | r ≤ rho x ∧ rho x ≤ R}
  let S : Set (Real × M) := Set.Icc 0 T ×ˢ K
  let q : Real × M → Real := fun p => (G.metric p.1).inner p.2
    (gradientFun (I := I) (G.metric p.1) rho p.2)
    (gradientFun (I := I) (G.metric p.1) rho p.2)
  let ell : Real × M → Real := fun p => |laplacianAt (I := I) G p.1 rho p.2|
  have hScompact : IsCompact S := isCompact_Icc.prod hcompact
  have hq_cont : ContinuousOn q S := by
    exact hgrad_cont.mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
  have hell_cont : ContinuousOn ell S := by
    exact (hlaplacian_cont.abs).mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩)
  obtain ⟨m, B, hm, hB, hgrad_lower, hlap_upper⟩ :
      ∃ m B : Real, 0 < m ∧ 0 ≤ B ∧
        (∀ p ∈ S, m ≤ q p) ∧
        (∀ p ∈ S, laplacianAt (I := I) G p.1 rho p.2 ≤ B) := by
    by_cases hKne : K.Nonempty
    · have hSne : S.Nonempty := by
        obtain ⟨x, hx⟩ := hKne
        exact ⟨(0, x), ⟨⟨le_rfl, hT.le⟩, hx⟩⟩
      obtain ⟨pm, hpm, hpmin⟩ := hScompact.exists_isMinOn hSne hq_cont
      obtain ⟨pB, hpB, hpBmax⟩ := hScompact.exists_isMaxOn hSne hell_cont
      have hqm : 0 < q pm := by
        exact (G.metric pm.1).pos pm.2 _
          (hgrad_ne pm.1 hpm.1 pm.2 hpm.2.1 hpm.2.2)
      refine ⟨q pm, ell pB, hqm, by positivity, hpmin, ?_⟩
      intro p hp
      have habs := hpBmax hp
      have hself := le_abs_self (laplacianAt (I := I) G p.1 rho p.2)
      change |laplacianAt (I := I) G p.1 rho p.2| ≤ ell pB at habs
      exact hself.trans habs
    · refine ⟨1, 0, by positivity, le_rfl, ?_, ?_⟩
      · intro p hp
        exact (hKne ⟨p.2, hp.2⟩).elim
      · intro p hp
        exact (hKne ⟨p.2, hp.2⟩).elim
  let kappa : Real := max (R / T ^ 2) (R / delta ^ 2) + 1
  have hT_sq : 0 < T ^ 2 := sq_pos_of_pos hT
  have hdelta_sq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    linarith [le_max_left (R / T ^ 2) (R / delta ^ 2), div_pos hR hT_sq]
  have hinit : R ≤ kappa * T ^ 2 := by
    apply le_of_lt ((div_lt_iff₀ hT_sq).mp ?_)
    dsimp [kappa]
    linarith [le_max_left (R / T ^ 2) (R / delta ^ 2)]
  have htime : R ≤ kappa * delta ^ 2 := by
    apply le_of_lt ((div_lt_iff₀ hdelta_sq).mp ?_)
    dsimp [kappa]
    linarith [le_max_right (R / T ^ 2) (R / delta ^ 2)]
  let alpha : Real := (2 * kappa * T + B) / m + 1
  have hnum : 0 ≤ 2 * kappa * T + B := by positivity
  have halpha : 0 < alpha := by
    dsimp [alpha]
    have := div_nonneg hnum hm.le
    linarith
  have hdom : 2 * kappa * T + B ≤ alpha * m := by
    apply le_of_lt ((div_lt_iff₀ hm).mp ?_)
    dsimp [alpha]
    linarith
  apply scalar_strong_maximum_principle_time_dependent_metric_of_barrier (I := I)
    G hT u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hrho
    hrho_nonneg hR hdelta heta hlocal (m := m) (B := B)
    (kappa := kappa) (alpha := alpha)
  · intro t ht htpos x hxr hxR
    exact hgrad_lower (t, x) ⟨ht, hxr, hxR⟩
  · intro t ht htpos x hxr hxR
    exact hlap_upper (t, x) ⟨ht, hxr, hxR⟩
  · exact hkappa
  · exact hinit
  · exact htime
  · exact halpha
  · exact hdom
  · exact hy

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {c : M} (hc : 0 < u T c) (y : M) :
    0 < u T y := by
  let P : Set M := {x | 0 < u T x}
  have hTs : T ∈ Set.Icc (0 : Real) T := ⟨hT.le, le_rfl⟩
  have huT_cont : Continuous (u T) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hu_mdiff T hTs hT x).continuousAt
  have hPopen : IsOpen P := isOpen_lt continuous_const huT_cont
  have hPclosed : IsClosed P := by
    rw [← closure_subset_iff_isClosed]
    intro a ha
    by_cases haP : a ∈ P
    · exact haP
    let b : SmoothBumpFunction I a := Classical.choice inferInstance
    let Cchart : Real :=
      ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1
    have hCchart : 0 < Cchart := by
      dsimp [Cchart]
      linarith [norm_nonneg
        (toEuclidean (E := E)).symm.toContinuousLinearMap]
    let S : Set E :=
      Metric.ball (extChartAt I a a) (b.rIn / 2) ∩
        {z | ‖(toEuclidean (E := E)) (z - extChartAt I a a)‖ <
          b.rIn / (4 * Cchart)}
    have hSopen : IsOpen S := by
      exact Metric.isOpen_ball.inter (isOpen_lt (by fun_prop) (by fun_prop))
    have haS : extChartAt I a a ∈ S := by
      constructor
      · change dist (extChartAt I a a) (extChartAt I a a) < b.rIn / 2
        rw [dist_self]
        exact half_pos b.rIn_pos
      · change ‖(toEuclidean (E := E))
          (extChartAt I a a - extChartAt I a a)‖ < b.rIn / (4 * Cchart)
        rw [sub_self, map_zero, norm_zero]
        exact div_pos b.rIn_pos (mul_pos (by norm_num) hCchart)
    let U : Set M := (chartAt H a).source ∩ extChartAt I a ⁻¹' S
    have hUopen : IsOpen U := isOpen_extChartAt_preimage a hSopen
    have haU : a ∈ U := ⟨mem_chart_source H a, haS⟩
    obtain ⟨c, hcU, hcP⟩ := (mem_closure_iff.mp ha) U hUopen haU
    have hcsource : c ∈ (chartAt H a).source := hcU.1
    have hc_dist_half :
        dist (extChartAt I a c) (extChartAt I a a) < b.rIn / 2 := hcU.2.1
    have hc_dist :
        dist (extChartAt I a c) (extChartAt I a a) < b.rIn := by
      linarith [b.rIn_pos]
    have hc_eucl_small :
        ‖(toEuclidean (E := E))
          (extChartAt I a c - extChartAt I a a)‖ < b.rIn / (4 * Cchart) := hcU.2.2
    let s : Real :=
      (b.rIn - dist (extChartAt I a c) (extChartAt I a a)) / (2 * Cchart)
    have hs : 0 < s := by
      dsimp [s]
      exact div_pos (sub_pos.mpr hc_dist) (mul_pos (by norm_num) hCchart)
    have hsmall_lt_s : b.rIn / (4 * Cchart) < s := by
      have hden : 0 < 4 * Cchart := mul_pos (by norm_num) hCchart
      calc
        b.rIn / (4 * Cchart) <
            (2 * (b.rIn - dist (extChartAt I a c) (extChartAt I a a))) /
              (4 * Cchart) := by
          apply (div_lt_div_iff₀ hden hden).mpr
          nlinarith [hc_dist_half]
        _ = s := by
          dsimp [s]
          field_simp
          ring
    have hc_eucl : ‖(toEuclidean (E := E))
        (extChartAt I a c - extChartAt I a a)‖ < s :=
      hc_eucl_small.trans hsmall_lt_s
    let Q : Real := s ^ 2
    have hQ : 0 < Q := sq_pos_of_pos hs
    have hqaQ : strongChartRadiusSq (I := I) a c a < Q := by
      apply (sq_lt_sq₀ (norm_nonneg _) hs.le).mpr
      dsimp [strongChartRadiusSq, Q]
      simpa only [map_sub, norm_sub_rev] using hc_eucl
    obtain ⟨delta, eta, hdelta, heta, V, hV, hlocal⟩ :=
      exists_positive_terminal_cylinder (M := M) hT.le u hu_cont hcP
    obtain ⟨r, hr, hrV⟩ := exists_strongPropagationRadius_sublevel_subset (I := I)
      b hcsource hQ hV
    let rho : M → Real := strongPropagationRadius (I := I) b c Q
    have hrho : ContMDiff I 𝓘(Real, Real) ∞ rho :=
      strongPropagationRadius_contMDiff (I := I) b Q
    have hrho_nonneg : ∀ x : M, 0 ≤ rho x :=
      strongPropagationRadius_nonneg (I := I) b hQ.le
    have hbc : b c = 1 := b.one_of_dist_le hcsource hc_dist.le
    have hrhoc : rho c = 0 := by
      simp [rho, strongPropagationRadius, strongChartRadiusSq, hbc]
    have hrhoa : rho a = strongChartRadiusSq (I := I) a c a := by
      simp [rho, strongPropagationRadius]
    let R : Real := (rho a + Q) / 2
    have hrhoaR : rho a < R := by
      dsimp [R]
      rw [hrhoa]
      linarith
    have hRQ : R < Q := by
      dsimp [R]
      rw [hrhoa]
      linarith
    have hR : 0 < R := lt_of_le_of_lt (hrho_nonneg a) hrhoaR
    have hcompact : IsCompact {x : M | r ≤ rho x ∧ rho x ≤ R} := by
      have hclosed : IsClosed (rho ⁻¹' Set.Icc r R) :=
        isClosed_Icc.preimage hrho.continuous
      change IsCompact (rho ⁻¹' Set.Icc r R)
      exact hclosed.isCompact
    have hgrad : ∀ t ∈ Set.Icc 0 T, ∀ x : M, r ≤ rho x → rho x ≤ R →
        gradientFun (I := I) (G.metric t) rho x ≠ 0 := by
      intro t _ x hxr hxR
      have hmidR : R < (R + Q) / 2 := by linarith
      have hmidQ : (R + Q) / 2 < Q := by linarith
      have hltmid : rho x < (R + Q) / 2 := hxR.trans_lt hmidR
      have hrad := strongPropagationRadius_lt_imp (I := I) b hmidQ hltmid
      have hbx : b x ≠ 0 := ne_of_gt hrad.1
      have hxsource : x ∈ (chartAt H a).source := by
        apply b.support_subset_source
        simpa [Function.mem_support] using hbx
      have hxcore :
          dist (extChartAt I a x) (extChartAt I a a) < b.rIn := by
        apply strongChartRadiusSq_lt_imp_mem_core (I := I) b hc_dist
        simpa [Q, s, Cchart] using hrad.2
      have hxc : x ≠ c := by
        intro heq
        subst x
        rw [hrhoc] at hxr
        linarith
      exact strongPropagationRadius_gradient_ne_zero (I := I) (G.metric t) b hcsource
        hxsource hxcore hxc Q
    have hlocal' : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
        rho x < r → eta ≤ u t x := by
      intro t ht htnear x hxr
      exact hlocal t ht htnear x (hrV hxr)
    have hpos :=
      time_dependent_metric_with_drift_strong_maximum_principle_of_barrier (I := I)
      G hT X u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hrho
      hrho_nonneg hR hdelta heta hlocal' hcompact hgrad
      (hgrad_cont rho hrho) (hheat_cont rho hrho) hrhoaR
    exact (haP hpos).elim
  have hPuniv : P = Set.univ :=
    IsClopen.eq_univ ⟨hPclosed, hPopen⟩ ⟨c, hc⟩
  have hyP : y ∈ P := by rw [hPuniv]; exact Set.mem_univ y
  exact hyP

theorem scalar_strong_maximum_principle_time_dependent_metric_spatial
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hlaplacian_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    {c : M} (hc : 0 < u T c) (y : M) :
    0 < u T y := by
  let X : Real → (x : M) → TangentSpace I x := fun _ x => 0
  have hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T) := by
    intro rho hrho
    simpa [heatOperatorWithDrift, driftTerm, gradientAt, X] using
      hlaplacian_cont rho hrho
  have hu_super' : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x := by
    intro t ht htpos x
    simpa [parabolicOperatorWithDrift, heatOperatorWithDrift, driftTerm,
      gradientAt, X] using hu_super t ht htpos x
  exact scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial
    (I := I) G hT X hgrad_cont hheat_cont u hu_cont hu_nonneg
      hu_time hu_mdiff hu_grad hu_super' hc y

private theorem time_dependent_metric_with_drift_lower_bound_from_positive_time
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T a m : Real} (ha : 0 < a) (haT : a ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    (hinit : ∀ x : M, m ≤ u a x) :
    ∀ t ∈ Set.Icc a T, ∀ x : M, m ≤ u t x := by
  let S : Real := T - a
  have hS : 0 ≤ S := sub_nonneg.mpr haT
  let v : Real → M → Real := fun s x => u (a + s) x - m
  let G' : MetricConnectionFamily (I := I) (M := M) Real :=
    shiftedStrongMetricFamily G a
  let X' : Real → (x : M) → TangentSpace I x := fun s x => X (a + s) x
  have hshift : a +ᵥ Set.Icc (0 : Real) S = Set.Icc a T := by
    dsimp [S]
    exact vadd_Icc_eq_Icc (a := a) (T := T)
  have hsub : Set.Icc a T ⊆ Set.Icc (0 : Real) T := by
    intro t ht
    exact ⟨ha.le.trans ht.1, ht.2⟩
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) S) := by
    have hmap : Set.MapsTo (fun p : Real × M => (a + p.1, p.2))
        (spacetimeSlab (M := M) S) (spacetimeSlab (M := M) T) := by
      intro p hp
      exact ⟨⟨by linarith [ha, hp.1.1], by dsimp [S] at hp; linarith [hp.1.2]⟩,
        Set.mem_univ p.2⟩
    have hcomp := hu_cont.comp (by fun_prop) hmap
    simpa [v] using hcomp.sub continuous_const.continuousOn
  have hv0 : ∀ x : M, 0 ≤ v 0 x := by
    intro x
    simpa [v] using sub_nonneg.mpr (hinit x)
  have hv_time : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => v q x) (Set.Icc 0 S) s := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    have hmap : Set.MapsTo (fun q : Real => a + q)
        (Set.Icc 0 S) (Set.Icc 0 T) := by
      intro q hq'
      apply hsub
      rw [← hshift]
      exact ⟨q, hq', rfl⟩
    have hcomp := (hu_time (a + s) hq hqpos x).comp s
      (by fun_prop) hmap
    simpa [v] using hcomp.sub_const m
  have hv_mdiff : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v s) x := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    exact (hu_mdiff (a + s) hq (by linarith) x).sub mdifferentiableAt_const
  have hv_grad : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G'.metric s) (v s) y) x := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    have heq : (fun y : M => gradientFun (I := I) (G'.metric s) (v s) y) =
        fun y : M => gradientFun (I := I) (G.metric (a + s)) (u (a + s)) y := by
      funext y
      rw [show v s = fun z => u (a + s) z - m from rfl]
      rw [gradientFun_sub (I := I) (G'.metric s)
        (hu_mdiff (a + s) hq hqpos y) mdifferentiableAt_const]
      rw [gradientFun_const, sub_zero]
      rfl
    rw [show (T% fun y : M =>
        gradientFun (I := I) (G'.metric s) (v s) y) =
        (T% fun y : M =>
          gradientFun (I := I) (G.metric (a + s)) (u (a + s)) y) by
      funext y
      simpa using congrFun heq y]
    exact hu_grad (a + s) hq hqpos x
  have hv_super : ∀ s ∈ Set.Icc 0 S, 0 < s → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G' S X' v s x := by
    intro s hs hspos x
    have hq : a + s ∈ Set.Icc (0 : Real) T := by
      apply hsub
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hqpos : 0 < a + s := by linarith
    have hderiv_shift := derivWithin_comp_const_add
      (fun q : Real => u q x) a (Set.Icc 0 S) s
    rw [hshift] at hderiv_shift
    have haTlt : a < T := by
      dsimp [S] at hs
      linarith [hs.2, hspos]
    have hqaT : a + s ∈ Set.Icc a T := by
      rw [← hshift]
      exact ⟨s, hs, rfl⟩
    have hderiv_subset := derivWithin_subset hsub
      ((uniqueDiffOn_Icc haTlt).uniqueDiffWithinAt hqaT)
      (hu_time (a + s) hq hqpos x)
    have hderiv : derivWithin (fun q => v q x) (Set.Icc 0 S) s =
        derivWithin (fun q => u q x) (Set.Icc 0 T) (a + s) := by
      rw [show (fun q => v q x) = fun q => u (a + q) x - m from rfl]
      rw [derivWithin_sub_const]
      exact hderiv_shift.trans hderiv_subset
    have hheat := heatOperatorWithDrift_sub_const (I := I) G' s
      (X' s) m (fun y => hu_mdiff (a + s) hq hqpos y) x
    unfold parabolicOperatorWithDrift
    rw [hderiv]
    rw [show heatOperatorWithDrift (I := I) G' s (X' s) (v s) x =
        heatOperatorWithDrift (I := I) G' s (X' s) (u (a + s)) x by
      simpa [v] using hheat]
    simpa [G', X', shiftedStrongMetricFamily, heatOperatorWithDrift, driftTerm,
      gradientAt, parabolicOperatorWithDrift] using
        hu_super (a + s) hq hqpos x
  have hv_nonneg := strict_barrier_positive_region (I := I) G' S X' v
    hv_cont hv0 hv_time hv_mdiff hv_grad
    (fun s hs hspos x _ => hv_super s hs hspos x)
  intro t ht x
  have hs : t - a ∈ Set.Icc (0 : Real) S := by
    dsimp [S]
    constructor <;> linarith [ht.1, ht.2]
  have hv := hv_nonneg (t - a) hs x
  simpa [v] using hv

private theorem time_dependent_metric_lower_bound_from_positive_time
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T a m : Real} (ha : 0 < a) (haT : a ≤ T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    (hinit : ∀ x : M, m ≤ u a x) :
    ∀ t ∈ Set.Icc a T, ∀ x : M, m ≤ u t x := by
  let X : Real → (x : M) → TangentSpace I x := fun _ x => 0
  have hu_super' : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x := by
    intro t ht htpos x
    simpa [parabolicOperatorWithDrift, heatOperatorWithDrift, driftTerm,
      gradientAt, X] using hu_super t ht htpos x
  exact time_dependent_metric_with_drift_lower_bound_from_positive_time
    (I := I) G ha haT X u hu_cont hu_time hu_mdiff hu_grad hu_super' hinit

private theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial_at
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T t : Real} (ht : 0 < t) (htT : t ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ s ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u s x)
    (hu_time : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => u q x) (Set.Icc 0 T) s)
    (hu_mdiff : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u s) x)
    (hu_grad : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (u s) y) x)
    (hu_super : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u s x)
    {c : M} (hc : 0 < u t c) (y : M) :
    0 < u t y := by
  have hsub : Set.Icc (0 : Real) t ⊆ Set.Icc 0 T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htT⟩
  have hgrad_cont' : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) t) := by
    intro rho hrho
    exact (hgrad_cont rho hrho).mono fun p hp => ⟨hsub hp.1, hp.2⟩
  have hheat_cont' : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) t) := by
    intro rho hrho
    exact (hheat_cont rho hrho).mono fun p hp => ⟨hsub hp.1, hp.2⟩
  have hu_time' : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => u q x) (Set.Icc 0 t) s := by
    intro s hs hspos x
    exact (hu_time s (hsub hs) hspos x).mono hsub
  have hu_mdiff' : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u s) x := by
    intro s hs hspos x
    exact hu_mdiff s (hsub hs) hspos x
  have hu_grad' : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (u s) y) x := by
    intro s hs hspos x
    exact hu_grad s (hsub hs) hspos x
  have hu_super' : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G t X u s x := by
    intro s hs hspos x
    have hderiv := derivWithin_subset hsub
      ((uniqueDiffOn_Icc ht).uniqueDiffWithinAt hs)
      (hu_time s (hsub hs) hspos x)
    rw [parabolicOperatorWithDrift_eq, hderiv]
    exact hu_super s (hsub hs) hspos x
  exact scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial
    (I := I) G ht X hgrad_cont' hheat_cont' u
    (hu_cont.mono fun p hp => ⟨hsub hp.1, hp.2⟩)
    (fun s hs x => hu_nonneg s (hsub hs) x) hu_time' hu_mdiff'
    hu_grad' hu_super' hc y

private theorem scalar_strong_maximum_principle_time_dependent_metric_spatial_at
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T t : Real} (ht : 0 < t) (htT : t ≤ T)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hlaplacian_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ s ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u s x)
    (hu_time : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun q => u q x) (Set.Icc 0 T) s)
    (hu_mdiff : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u s) x)
    (hu_grad : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (u s) y) x)
    (hu_super : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      0 ≤ derivWithin (fun q => u q x) (Set.Icc 0 T) s -
        laplacianAt (I := I) G s (u s) x)
    {c : M} (hc : 0 < u t c) (y : M) :
    0 < u t y := by
  let X : Real → (x : M) → TangentSpace I x := fun _ x => 0
  have hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T) := by
    intro rho hrho
    simpa [heatOperatorWithDrift, driftTerm, gradientAt, X] using
      hlaplacian_cont rho hrho
  have hu_super' : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u s x := by
    intro s hs hspos x
    simpa [parabolicOperatorWithDrift, heatOperatorWithDrift, driftTerm,
      gradientAt, X] using hu_super s hs hspos x
  exact
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial_at
      (I := I) G ht htT X hgrad_cont hheat_cont u hu_cont hu_nonneg
        hu_time hu_mdiff hu_grad hu_super' hc y

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  intro t ht x
  apply le_antisymm (le_of_not_gt ?_) (hu_nonneg t ht x)
  intro htx
  obtain ⟨a, ha, haT, c, hc⟩ :
      ∃ a : Real, 0 < a ∧ a ≤ T ∧ ∃ c : M, 0 < u a c := by
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨a, haI, haPos⟩ :=
        exists_positive_time_of_initial_value (M := M) hT u hu_cont htx
      exact ⟨a, haI.1, haI.2, x, haPos⟩
    · exact ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2, x, htx⟩
  have hslice : ∀ z : M, 0 < u a z := by
    intro z
    exact
      scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial_at
        (I := I) G ha haT X hgrad_cont hheat_cont u hu_cont hu_nonneg
          hu_time hu_mdiff hu_grad hu_super hc z
  have hua_cont : Continuous (u a) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hu_mdiff a ⟨ha.le, haT⟩ ha z).continuousAt
  obtain ⟨xm, _, hxmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
      Set.univ_nonempty hua_cont.continuousOn
  let m : Real := u a xm
  have hm : 0 < m := hslice xm
  have hinit : ∀ z : M, m ≤ u a z := by
    intro z
    exact hxmin (Set.mem_univ z)
  have hlower :=
    time_dependent_metric_with_drift_lower_bound_from_positive_time (I := I)
      G ha haT X u hu_cont hu_time hu_mdiff hu_grad hu_super hinit
      T ⟨haT, le_rfl⟩ y
  rw [hy] at hlower
  exact (not_lt_of_ge hlower hm).elim

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_positive
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (le_of_not_gt hy)
    (hu_nonneg T ⟨hT.le, le_rfl⟩ y)
  have hpast :=
    scalar_strong_maximum_principle_time_dependent_metric_with_drift (I := I)
      G hT X hgrad_cont hheat_cont u hu_cont hu_nonneg hu_time
        hu_mdiff hu_grad hu_super hy0 t ht x
  linarith

theorem scalar_strong_maximum_principle_time_dependent_metric
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hlaplacian_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  intro t ht x
  apply le_antisymm (le_of_not_gt ?_) (hu_nonneg t ht x)
  intro htx
  obtain ⟨a, ha, haT, c, hc⟩ :
      ∃ a : Real, 0 < a ∧ a ≤ T ∧ ∃ c : M, 0 < u a c := by
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨a, haI, haPos⟩ :=
        exists_positive_time_of_initial_value (M := M) hT u hu_cont htx
      exact ⟨a, haI.1, haI.2, x, haPos⟩
    · exact ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2, x, htx⟩
  have hslice : ∀ z : M, 0 < u a z := by
    intro z
    exact scalar_strong_maximum_principle_time_dependent_metric_spatial_at (I := I)
      G ha haT hgrad_cont hlaplacian_cont u hu_cont hu_nonneg hu_time
      hu_mdiff hu_grad hu_super hc z
  have hua_cont : Continuous (u a) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hu_mdiff a ⟨ha.le, haT⟩ ha z).continuousAt
  obtain ⟨xm, _, hxmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
      Set.univ_nonempty hua_cont.continuousOn
  let m : Real := u a xm
  have hm : 0 < m := hslice xm
  have hinit : ∀ z : M, m ≤ u a z := by
    intro z
    exact hxmin (Set.mem_univ z)
  have hlower := time_dependent_metric_lower_bound_from_positive_time (I := I)
    G ha haT u hu_cont hu_time hu_mdiff hu_grad hu_super hinit
    T ⟨haT, le_rfl⟩ y
  rw [hy] at hlower
  exact (not_lt_of_ge hlower hm).elim

theorem scalar_strong_maximum_principle_time_dependent_metric_positive
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hlaplacian_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (le_of_not_gt hy)
    (hu_nonneg T ⟨hT.le, le_rfl⟩ y)
  have hpast := scalar_strong_maximum_principle_time_dependent_metric (I := I)
    G hT hgrad_cont hlaplacian_cont u hu_cont hu_nonneg hu_time
    hu_mdiff hu_grad hu_super hy0 t ht x
  linarith

private theorem time_dependent_potential_exp_rescale_super
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x - V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x) :
    ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin
          (fun s => Real.exp (-L * s) * u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t
          (fun y => Real.exp (-L * t) * u t y) x := by
  let X : Real → (x : M) → TangentSpace I x := fun _ x => 0
  intro t ht htpos x
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hscale : DifferentiableWithinAt Real
      (fun s => Real.exp (-L * s)) (Set.Icc 0 T) t := by
    fun_prop
  have hident := parabolic_exp_rescale_identity (I := I)
    G T L X u t huniq (hu_mdiff t ht htpos) x
    (hu_grad t ht htpos x) (hu_time t ht htpos x) hscale
  have hVu : 0 ≤ (V t x - L) * u t x :=
    mul_nonneg (sub_nonneg.mpr (hV t ht x)) (hu_nonneg t ht x)
  have hop : parabolicOperatorWithDrift (I := I) G T X u t x =
      derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x := by
    rw [parabolicOperatorWithDrift_eq]
    rw [show X t = (fun y : M => (0 : TangentSpace I y)) from rfl]
    rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt]
  have hbase : 0 ≤
      parabolicOperatorWithDrift (I := I) G T X u t x - L * u t x := by
    rw [hop]
    linarith [hu_super t ht htpos x]
  have hzP : 0 ≤ parabolicOperatorWithDrift (I := I) G T X
      (fun s y => Real.exp (-L * s) * u s y) t x := by
    rw [hident]
    exact mul_nonneg (Real.exp_pos _).le hbase
  rw [parabolicOperatorWithDrift_eq] at hzP
  rw [show X t = (fun y : M => (0 : TangentSpace I y)) from rfl] at hzP
  rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt] at hzP
  exact hzP

theorem scalar_strong_maximum_principle_time_dependent_metric_with_potential
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hlaplacian_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x - V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  let z : Real → M → Real := fun t x => Real.exp (-L * t) * u t x
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact (by fun_prop : Continuous
      (fun p : Real × M => Real.exp (-L * p.1))).continuousOn.mul hu_cont
  have hz_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ z t x := by
    intro t ht x
    exact mul_nonneg (Real.exp_pos _).le (hu_nonneg t ht x)
  have hscale_time : ∀ t : Real,
      DifferentiableWithinAt Real (fun s => Real.exp (-L * s))
        (Set.Icc 0 T) t := by
    intro t
    fun_prop
  have hz_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => z s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (hscale_time t).mul (hu_time t ht htpos x)
  have hz_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (z t) x := by
    intro t ht htpos x
    exact (hu_mdiff t ht htpos x).const_smul (Real.exp (-L * t))
  have hz_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (z t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) =
          (T% fun y : M => Real.exp (-L * t) •
            gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      change gradientFun (I := I) (G.metric t)
        (Real.exp (-L * t) • u t) y = _
      exact gradientFun_const_smul (I := I) (G.metric t)
        (Real.exp (-L * t)) (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_const.smul_section (hu_grad t ht htpos x)
  have hz_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => z s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (z t) x := by
    simpa only [z] using time_dependent_potential_exp_rescale_super (I := I)
      G hT V L u hu_nonneg hu_time hu_mdiff hu_grad hu_super hV
  have hzy : z T y = 0 := by simp [z, hy]
  have hzzero := scalar_strong_maximum_principle_time_dependent_metric (I := I)
    G hT hgrad_cont hlaplacian_cont z hz_cont hz_nonneg hz_time
    hz_mdiff hz_grad hz_super hzy
  intro t ht x
  have hz := hzzero t ht x
  change Real.exp (-L * t) * u t x = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

theorem scalar_strong_maximum_principle_time_dependent_metric_with_potential_positive
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hlaplacian_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x - V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (le_of_not_gt hy)
    (hu_nonneg T ⟨hT.le, le_rfl⟩ y)
  have hpast :=
    scalar_strong_maximum_principle_time_dependent_metric_with_potential (I := I)
      G hT hgrad_cont hlaplacian_cont V L u hu_cont hu_nonneg hu_time
      hu_mdiff hu_grad hu_super hV hy0 t ht x
  linarith

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x -
        V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  let z : Real → M → Real := fun t x => Real.exp (-L * t) * u t x
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact (by fun_prop : Continuous
      (fun p : Real × M => Real.exp (-L * p.1))).continuousOn.mul hu_cont
  have hz_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ z t x := by
    intro t ht x
    exact mul_nonneg (Real.exp_pos _).le (hu_nonneg t ht x)
  have hz_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => z s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    have hscale : DifferentiableWithinAt Real
        (fun s => Real.exp (-L * s)) (Set.Icc 0 T) t := by
      fun_prop
    exact hscale.mul (hu_time t ht htpos x)
  have hz_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (z t) x := by
    intro t ht htpos x
    exact (hu_mdiff t ht htpos x).const_smul (Real.exp (-L * t))
  have hz_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (z t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) =
          (T% fun y : M => Real.exp (-L * t) •
            gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      change gradientFun (I := I) (G.metric t)
        (Real.exp (-L * t) • u t) y = _
      exact gradientFun_const_smul (I := I) (G.metric t)
        (Real.exp (-L * t)) (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_const.smul_section (hu_grad t ht htpos x)
  have hz_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X z t x := by
    intro t ht htpos x
    simpa only [z] using parabolic_exp_rescale_nonneg_of_potential (I := I)
      G T hT L X V u t ht (hu_mdiff t ht htpos) x
        (hu_grad t ht htpos x) (hu_time t ht htpos x)
        (hu_nonneg t ht x) (hV t ht x) (hu_super t ht htpos x)
  have hzy : z T y = 0 := by simp [z, hy]
  have hzzero :=
    scalar_strong_maximum_principle_time_dependent_metric_with_drift (I := I)
      G hT X hgrad_cont hheat_cont z hz_cont hz_nonneg hz_time
        hz_mdiff hz_grad hz_super hzy
  intro t ht x
  have hz := hzzero t ht x
  change Real.exp (-L * t) * u t x = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential_positive
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x -
        V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (le_of_not_gt hy)
    (hu_nonneg T ⟨hT.le, le_rfl⟩ y)
  have hpast :=
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential
      (I := I) G hT X hgrad_cont hheat_cont V L u hu_cont hu_nonneg
        hu_time hu_mdiff hu_grad hu_super hV hy0 t ht x
  linarith

theorem scalar_strong_maximum_principle_fixed_metric_spatial
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {c : M} (hc : 0 < u T c) (y : M) :
    0 < u T y := by
  apply scalar_strong_maximum_principle_fixed_metric_with_drift_spatial (I := I)
    g hT (fun _ x => (0 : TangentSpace I x)) (C := 0) le_rfl
    (fun _ _ _ => by simp) u hu_cont hu_nonneg hu_time hu_space
  · intro t ht htpos x
    simpa using hu_super t ht htpos x
  · exact hc

theorem scalar_strong_maximum_principle_fixed_metric
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  apply scalar_strong_maximum_principle_fixed_metric_with_drift (I := I)
    g hT (fun _ x => (0 : TangentSpace I x)) (C := 0) le_rfl
    (fun _ _ _ => by simp) u hu_cont hu_nonneg hu_time hu_space
  · intro t ht htpos x
    simpa using hu_super t ht htpos x
  · exact hy

theorem scalar_strong_maximum_principle_fixed_metric_positive
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  apply scalar_strong_maximum_principle_fixed_metric_with_drift_positive (I := I)
    g hT (fun _ x => (0 : TangentSpace I x)) (C := 0) le_rfl
    (fun _ _ _ => by simp) u hu_cont hu_nonneg hu_time hu_space
  · intro s hs hspos z
    simpa using hu_super s hs hspos z
  · exact ht
  · exact hx

private theorem potential_exp_rescale_super
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hz_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun y => Real.exp (-L * t) * u t y))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)) -
        V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x) :
    ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M),
      0 ≤ derivWithin
          (fun s => Real.exp (-L * s) * u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g
            ⟨fun y => Real.exp (-L * t) * u t y, hz_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g
            (fun y => Real.exp (-L * t) * u t y) x)) := by
  let G : MetricConnectionFamily (I := I) (M := M) Real :=
    globalStrongStaticMetricFamily (I := I) g
  intro t ht htpos x
  have hscale_time : DifferentiableWithinAt Real
      (fun s => Real.exp (-L * s)) (Set.Icc 0 T) t := by
    fun_prop
  have hu_mdiff : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y := fun y =>
    (hu_space t ht htpos).mdifferentiable (by simp) y
  have hu_grad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g (u t) y) x :=
    gradientFun_mdiffAt (I := I) g (hu_space t ht htpos) x
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hident := parabolic_exp_rescale_identity (I := I)
    G T L X u t huniq hu_mdiff x (by simpa [G] using hu_grad)
    (hu_time t ht htpos x) hscale_time
  have hbase : 0 ≤
      derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)) -
        L * u t x := by
    have hVu : 0 ≤ (V t x - L) * u t x :=
      mul_nonneg (sub_nonneg.mpr (hV t ht x)) (hu_nonneg t ht x)
    linarith [hu_super t ht htpos x]
  have hopEq := globalStrongStaticMetricFamily_parabolicOperator (I := I)
    g T X u (hu_space t ht htpos) x
  have hopEqG : parabolicOperatorWithDrift (I := I) G T X u t x =
      derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)) := by
    simpa only [G] using hopEq
  have hoperator : 0 ≤
      parabolicOperatorWithDrift (I := I) G T X u t x - L * u t x := by
    rw [hopEqG]
    exact hbase
  have hzP : 0 ≤ parabolicOperatorWithDrift (I := I) G T X
      (fun s y => Real.exp (-L * s) * u s y) t x := by
    rw [hident]
    exact mul_nonneg (Real.exp_pos _).le hoperator
  have hopZ := globalStrongStaticMetricFamily_parabolicOperator (I := I)
    g T X (fun s y => Real.exp (-L * s) * u s y)
      (hz_space t ht htpos) x
  have hopZG : parabolicOperatorWithDrift (I := I) G T X
      (fun s y => Real.exp (-L * s) * u s y) t x =
      derivWithin (fun s => Real.exp (-L * s) * u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g
            ⟨fun y => Real.exp (-L * t) * u t y, hz_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g
            (fun y => Real.exp (-L * t) * u t y) x)) := by
    simpa only [G] using hopZ
  rw [hopZG] at hzP
  exact hzP

theorem scalar_strong_maximum_principle_fixed_metric_with_drift_and_potential
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {C : Real} (hC : 0 ≤ C)
    (hX : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      g.inner x (X t x) (X t x) ≤ C)
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)) -
        V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  let z : Real → M → Real := fun t x => Real.exp (-L * t) * u t x
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact (by fun_prop : Continuous (fun p : Real × M => Real.exp
      (-L * p.1))).continuousOn.mul hu_cont
  have hz_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ z t x := by
    intro t ht x
    exact mul_nonneg (Real.exp_pos _).le (hu_nonneg t ht x)
  have hz_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => z s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    have hscale : DifferentiableWithinAt Real
        (fun s => Real.exp (-L * s)) (Set.Icc 0 T) t := by
      fun_prop
    exact hscale.mul (hu_time t ht htpos x)
  have hz_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (z t) := by
    intro t ht htpos
    exact contMDiff_const.mul (hu_space t ht htpos)
  have hz_super := potential_exp_rescale_super (I := I) g hT X V L u
    hu_nonneg hu_time hu_space hz_space hu_super hV
  have hzy : z T y = 0 := by simp [z, hy]
  have hzzero := scalar_strong_maximum_principle_fixed_metric_with_drift (I := I)
    g hT X hC hX z hz_cont hz_nonneg hz_time hz_space hz_super hzy
  intro t ht x
  have hz := hzzero t ht x
  change Real.exp (-L * t) * u t x = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

theorem scalar_strong_maximum_principle_fixed_metric_with_drift_and_potential_positive
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {C : Real} (hC : 0 ≤ C)
    (hX : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      g.inner x (X t x) (X t x) ≤ C)
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)) -
        V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (le_of_not_gt hy)
    (hu_nonneg T ⟨hT.le, le_rfl⟩ y)
  have hpast := scalar_strong_maximum_principle_fixed_metric_with_drift_and_potential
    (I := I) g hT X hC hX V L u hu_cont
    hu_nonneg hu_time hu_space hu_super hV hy0 t ht x
  linarith

end

end DifferentialGeometry.Analysis.Parabolic
