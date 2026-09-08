import DifferentialGeometry.Geometry.Operator.Operators
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace SmoothBumpFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private abbrev ChartEuclidean := EuclideanSpace Real (Fin (Module.finrank Real E))

def chartRadiusSq (a c x : M) : Real :=
  ‖(toEuclidean (E := E)) (extChartAt I a x - extChartAt I a c)‖ ^ 2

private theorem chartRadiusSq_contMDiffOn
    (a c : M) :
    ContMDiffOn I 𝓘(Real, Real) ∞ (chartRadiusSq (I := I) a c)
      (chartAt H a).source := by
  unfold chartRadiusSq
  intro x hx
  have hq : ContDiff Real ∞
      (fun z : E => ‖(toEuclidean (E := E)) (z - extChartAt I a c)‖ ^ 2) := by
    exact ((toEuclidean (E := E)).contDiff.comp
      (contDiff_id.sub contDiff_const)).norm_sq Real
  rw [show (fun x : M =>
      ‖(toEuclidean (E := E)) (extChartAt I a x - extChartAt I a c)‖ ^ 2) =
        (fun z : E => ‖(toEuclidean (E := E)) (z - extChartAt I a c)‖ ^ 2) ∘
          extChartAt I a by
    funext y
    rfl]
  exact (hq.contMDiff.contMDiffAt.comp x
    (((contMDiffOn_extChartAt (I := I) (x := a)) x hx).contMDiffAt
      ((chartAt H a).open_source.mem_nhds hx))).contMDiffWithinAt

def cutoffChartRadiusSq
    {a : M} (b : SmoothBumpFunction I a) (c : M) (Q : Real) (x : M) : Real :=
  b x * chartRadiusSq (I := I) a c x + Q * (1 - b x)

theorem cutoffChartRadiusSq_contMDiff [T2Space M]
    {a c : M} (b : SmoothBumpFunction I a)
    (Q : Real) :
    ContMDiff I 𝓘(Real, Real) ∞ (cutoffChartRadiusSq (I := I) b c Q) := by
  unfold cutoffChartRadiusSq
  have hfirst : ContMDiff I 𝓘(Real, Real) ∞
      (fun x => b x * chartRadiusSq (I := I) a c x) := by
    simpa only [smul_eq_mul] using
      b.contMDiff_smul (chartRadiusSq_contMDiffOn (I := I) a c)
  exact hfirst.add (contMDiff_const.mul (contMDiff_const.sub b.contMDiff))

omit [IsManifold I ∞ M] in
theorem cutoffChartRadiusSq_nonneg
    {a c : M} (b : SmoothBumpFunction I a) {Q : Real} (hQ : 0 ≤ Q) (x : M) :
    0 ≤ cutoffChartRadiusSq (I := I) b c Q x := by
  exact add_nonneg
    (mul_nonneg b.nonneg (sq_nonneg _))
    (mul_nonneg hQ (sub_nonneg.mpr b.le_one))

omit [IsManifold I ∞ M] in
theorem cutoffChartRadiusSq_pos_of_ne
    {a c : M} (b : SmoothBumpFunction I a)
    (hc : c ∈ (chartAt H a).source) {Q : Real} (hQ : 0 < Q)
    {x : M} (hxc : x ≠ c) :
    0 < cutoffChartRadiusSq (I := I) b c Q x := by
  by_cases hb : b x = 0
  · simp [cutoffChartRadiusSq, hb, hQ]
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
    have hq : 0 < chartRadiusSq (I := I) a c x := by
      unfold chartRadiusSq
      have hsub : extChartAt I a x - extChartAt I a c ≠ 0 :=
        sub_ne_zero.mpr hchart
      have heucl : (toEuclidean (E := E))
          (extChartAt I a x - extChartAt I a c) ≠ 0 := by
        simpa using (toEuclidean (E := E)).injective.ne hsub
      positivity
    unfold cutoffChartRadiusSq
    exact add_pos_of_pos_of_nonneg (mul_pos hbx hq)
      (mul_nonneg hQ.le (sub_nonneg.mpr b.le_one))

omit [IsManifold I ∞ M] in
theorem pos_and_chartRadiusSq_lt_of_cutoffChartRadiusSq_lt
    {a c x : M} (b : SmoothBumpFunction I a) {Q R : Real}
    (hRQ : R < Q) (h : cutoffChartRadiusSq (I := I) b c Q x < R) :
    0 < b x ∧ chartRadiusSq (I := I) a c x < Q := by
  have hb0 := b.nonneg (x := x)
  unfold cutoffChartRadiusSq at h
  have hfactor : b x * (chartRadiusSq (I := I) a c x - Q) < 0 := by
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
private theorem cutoffChartRadiusSq_eventuallyEq
    {a c x : M} (b : SmoothBumpFunction I a)
    (hx : x ∈ (chartAt H a).source)
    (hd : dist (extChartAt I a x) (extChartAt I a a) < b.rIn)
    (Q : Real) :
    EventuallyEq (nhds x) (cutoffChartRadiusSq (I := I) b c Q)
      (chartRadiusSq (I := I) a c) := by
  filter_upwards [b.eventuallyEq_one_of_dist_lt hx hd] with y hy
  simp [cutoffChartRadiusSq, hy]

private theorem fderiv_chartRadiusSq_apply_self (z z0 : E) :
    fderiv Real
        (fun w : E => ‖(toEuclidean (E := E)) (w - z0)‖ ^ 2) z (z - z0) =
      2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2 := by
  have h := (((toEuclidean (E := E)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const z0))).norm_sq
  change fderiv Real
      (fun x => ‖((toEuclidean (E := E) : E → ChartEuclidean) ∘
        fun y => id y - z0) x‖ ^ 2) z (z - z0) = _
  rw [h.fderiv]
  simp only [id_eq, Function.comp_apply, map_sub, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.sub_comp, FunLike.coe_smul,
    FunLike.coe_sub, ContinuousLinearMap.coe_comp, coe_innerSL_apply,
    ContinuousLinearEquiv.coe_coe, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm ((toEuclidean (E := E)) z0) ((toEuclidean (E := E)) z)]
  rw [norm_sub_sq_real]
  rw [real_inner_comm ((toEuclidean (E := E)) z0) ((toEuclidean (E := E)) z)]
  ring

private theorem chartRadiusSq_mfderiv_ne_zero
    {a c x : M} (hc : c ∈ (chartAt H a).source)
    (hx : x ∈ (chartAt H a).source) (hxc : x ≠ c) :
    mfderiv I 𝓘(Real, Real) (chartRadiusSq (I := I) a c) x ≠ 0 := by
  let z : E := extChartAt I a x
  let z0 : E := extChartAt I a c
  let q : E → Real := fun w => ‖(toEuclidean (E := E)) (w - z0)‖ ^ 2
  have hq : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real) q z := by
    have hqcd : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ q :=
      (((toEuclidean (E := E)).contDiff.comp
        (contDiff_id.sub contDiff_const)).norm_sq Real).contMDiff
    exact hqcd.mdifferentiable (by simp) z
  have hchart : MDifferentiableAt I 𝓘(Real, E) (extChartAt I a) x :=
    mdifferentiableAt_extChartAt (I := I) hx
  have hfun : chartRadiusSq (I := I) a c = q ∘ extChartAt I a := by
    funext y
    rfl
  have hcomp :
      mvfderiv I (chartRadiusSq (I := I) a c) x =
        (mvfderiv 𝓘(Real, E) q z).comp
          (mfderiv I 𝓘(Real, E) (extChartAt I a) x) := by
    rw [hfun]
    exact mvfderiv_comp x hq hchart
  intro hzero
  have hmvzero : mvfderiv I (chartRadiusSq (I := I) a c) x = 0 := by
    simp [mvfderiv, hzero]
  let v : TangentSpace 𝓘(Real, E) z :=
    (NormedSpace.fromTangentSpace (𝕜 := Real) (E := E) z).symm (z - z0)
  have hinv := isInvertible_mfderiv_extChartAt (I := I)
    (show x ∈ (extChartAt I a).source by simpa [extChartAt_source] using hx)
  obtain ⟨w, hw⟩ := hinv.surjective v
  have happzero := congrArg
    (fun L : TangentSpace I x →L[Real] Real => L w) hmvzero
  rw [hcomp] at happzero
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at happzero
  rw [hw] at happzero
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
  have happmv : mvfderiv 𝓘(Real, E) q z v =
      2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2 := by
    dsimp [v]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    change fderiv Real q z (z - z0) =
      2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2
    simpa [q] using happ
  rw [happmv] at happzero
  have hpos : 0 < 2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2 := by
    positivity
  exact hpos.ne' happzero

private theorem cutoffChartRadiusSq_mfderiv_ne_zero
    {a c x : M} (b : SmoothBumpFunction I a) (hc : c ∈ (chartAt H a).source)
    (hx : x ∈ (chartAt H a).source)
    (hd : dist (extChartAt I a x) (extChartAt I a a) < b.rIn)
    (hxc : x ≠ c) (Q : Real) :
    mfderiv I 𝓘(Real, Real) (cutoffChartRadiusSq (I := I) b c Q) x ≠ 0 := by
  have hev := cutoffChartRadiusSq_eventuallyEq (I := I) (c := c) b hx hd Q
  rw [hev.mfderiv_eq]
  exact chartRadiusSq_mfderiv_ne_zero (I := I) hc hx hxc

theorem cutoffChartRadiusSq_gradient_ne_zero
    (g : SmoothRiemannianMetric I M) {a c x : M}
    (b : SmoothBumpFunction I a) (hc : c ∈ (chartAt H a).source)
    (hx : x ∈ (chartAt H a).source)
    (hd : dist (extChartAt I a x) (extChartAt I a a) < b.rIn)
    (hxc : x ≠ c) (Q : Real) :
    gradientFun (I := I) g (cutoffChartRadiusSq (I := I) b c Q) x ≠ 0 := by
  intro hgrad
  apply cutoffChartRadiusSq_mfderiv_ne_zero b hc hx hd hxc Q
  apply ContinuousLinearMap.ext
  intro v
  have hinner := inner_gradientFun (I := I) g
    (cutoffChartRadiusSq (I := I) b c Q) x v
  rw [hgrad] at hinner
  apply (NormedSpace.fromTangentSpace
    (cutoffChartRadiusSq (I := I) b c Q x)).injective
  simpa [mvfderiv] using hinner.symm

omit [IsManifold I ∞ M] in
theorem dist_lt_rIn_of_chartRadiusSq_lt
    {a c x : M} (b : SmoothBumpFunction I a)
    (hc_dist : dist (extChartAt I a c) (extChartAt I a a) < b.rIn)
    (hq : chartRadiusSq (I := I) a c x <
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
    simpa only [chartRadiusSq, s, C] using hq
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

theorem isCompact_sublevel_cutoffChartRadiusSq [T2Space M]
    {a c : M} (b : SmoothBumpFunction I a) {Q R : Real} (hRQ : R < Q) :
    IsCompact {x : M | cutoffChartRadiusSq (I := I) b c Q x ≤ R} := by
  apply b.hasCompactSupport.of_isClosed_subset
    (isClosed_le (cutoffChartRadiusSq_contMDiff (I := I) b Q).continuous continuous_const)
  intro x hx
  change cutoffChartRadiusSq (I := I) b c Q x ≤ R at hx
  apply subset_tsupport
  intro hb
  have heq : cutoffChartRadiusSq (I := I) b c Q x = Q := by
    simp [cutoffChartRadiusSq, hb]
  rw [heq] at hx
  exact (not_le_of_gt hRQ) hx

theorem exists_cutoffChartRadiusSq_sublevel_subset [T2Space M]
    {a c : M} (b : SmoothBumpFunction I a)
    (hc : c ∈ (chartAt H a).source) {Q : Real} (hQ : 0 < Q)
    {V : Set M} (hV : V ∈ nhds c) :
    ∃ r : Real, 0 < r ∧
      {x | cutoffChartRadiusSq (I := I) b c Q x < r} ⊆ V := by
  obtain ⟨U, hUV, hUopen, hcU⟩ := mem_nhds_iff.mp hV
  let rho := cutoffChartRadiusSq (I := I) b c Q
  let K : Set M := {x | rho x ≤ Q / 2} ∩ Uᶜ
  have hK : IsCompact K :=
    (isCompact_sublevel_cutoffChartRadiusSq b (half_lt_self hQ)).inter_right hUopen.isClosed_compl
  by_cases hKne : K.Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hKne
      (cutoffChartRadiusSq_contMDiff (I := I) b Q).continuous.continuousOn
    have hx0c : x0 ≠ c := by
      intro heq
      exact hx0.2 (heq ▸ hcU)
    have hpos : 0 < rho x0 := cutoffChartRadiusSq_pos_of_ne b hc hQ hx0c
    refine ⟨min (Q / 2) (rho x0 / 2), lt_min (half_pos hQ) (half_pos hpos), ?_⟩
    intro x hx
    change rho x < min (Q / 2) (rho x0 / 2) at hx
    apply hUV
    by_contra hxU
    have hxK : x ∈ K := ⟨hx.le.trans (min_le_left _ _), hxU⟩
    have hvalue := hmin hxK
    have hhalf := hx.trans_le (min_le_right (Q / 2) (rho x0 / 2))
    change rho x0 ≤ rho x at hvalue
    linarith only [hpos, hvalue, hhalf]
  · refine ⟨Q / 2, half_pos hQ, ?_⟩
    intro x hx
    change rho x < Q / 2 at hx
    apply hUV
    by_contra hxU
    exact hKne ⟨x, hx.le, hxU⟩

theorem exists_annulus_neighborhood [T2Space M]
    (a : M) {Omega : Set M} (hOmega : Omega ∈ nhds a) :
    ∃ U : Set M, IsOpen U ∧ a ∈ U ∧ IsCompact (closure U) ∧ closure U ⊆ Omega ∧
      ∀ c ∈ U, ∀ y ∈ U, c ≠ y → ∀ V : Set M, V ∈ nhds c →
        ∃ (rho : M → Real) (r R : Real),
          ContMDiff I 𝓘(Real, Real) ∞ rho ∧ rho c = 0 ∧ 0 < r ∧ r < R ∧
          IsCompact {z : M | r ≤ rho z ∧ rho z ≤ R} ∧
          {z : M | r ≤ rho z ∧ rho z ≤ R} ⊆ Omega ∧
          r ≤ rho y ∧ rho y < R ∧
          (∀ z, rho z = r → z ∈ V) ∧
          ∀ (g : SmoothRiemannianMetric I M),
            ∀ z ∈ {z : M | r ≤ rho z ∧ rho z ≤ R},
              gradientFun (I := I) g rho z ≠ 0 := by
  obtain ⟨b, -, hbOmega⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) a).mem_iff.mp hOmega
  let C : Real := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    linarith [norm_nonneg (toEuclidean (E := E)).symm.toContinuousLinearMap]
  let S : Set E := Metric.ball (extChartAt I a a) (b.rIn / 2) ∩
    {z | ‖(toEuclidean (E := E)) (z - extChartAt I a a)‖ < b.rIn / (8 * C)}
  have hSopen : IsOpen S :=
    Metric.isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const)
  let U : Set M := (chartAt H a).source ∩ extChartAt I a ⁻¹' S
  have hUopen : IsOpen U := isOpen_extChartAt_preimage a hSopen
  have haU : a ∈ U := by
    refine ⟨mem_chart_source H a, ?_, ?_⟩
    · change dist (extChartAt I a a) (extChartAt I a a) < b.rIn / 2
      simpa only [dist_self] using half_pos b.rIn_pos
    · change ‖(toEuclidean (E := E))
        (extChartAt I a a - extChartAt I a a)‖ < b.rIn / (8 * C)
      simp only [sub_self, map_zero, norm_zero]
      exact div_pos b.rIn_pos (mul_pos (by norm_num) hC)
  have hcore {x : M} (hx : x ∈ U) :
      dist (extChartAt I a x) (extChartAt I a a) < b.rIn := by
    have hhalf : dist (extChartAt I a x) (extChartAt I a a) < b.rIn / 2 := hx.2.1
    linarith only [hhalf, b.rIn_pos]
  have hbone {x : M} (hx : x ∈ U) : b x = 1 := b.one_of_dist_le hx.1 (hcore hx).le
  have hUsupport : U ⊆ tsupport b := by
    intro x hx
    apply subset_tsupport
    change b x ≠ 0
    rw [hbone hx]
    exact one_ne_zero
  have hclosureSupport : closure U ⊆ tsupport b :=
    closure_minimal hUsupport (isClosed_tsupport _)
  refine ⟨U, hUopen, haU,
    b.hasCompactSupport.of_isClosed_subset isClosed_closure hclosureSupport,
    hclosureSupport.trans hbOmega, ?_⟩
  intro c hc y hy hcy V hV
  have hc_dist : dist (extChartAt I a c) (extChartAt I a a) < b.rIn := hcore hc
  let scale : Real :=
    (b.rIn - dist (extChartAt I a c) (extChartAt I a a)) / (2 * C)
  have hscale : 0 < scale := div_pos (sub_pos.mpr hc_dist) (by positivity)
  have hsmall : b.rIn / (4 * C) < scale := by
    have hden : 0 < 4 * C := by positivity
    have hcHalf : dist (extChartAt I a c) (extChartAt I a a) < b.rIn / 2 := hc.2.1
    calc
      b.rIn / (4 * C) <
          (2 * (b.rIn - dist (extChartAt I a c) (extChartAt I a a))) / (4 * C) := by
        apply (div_lt_div_iff₀ hden hden).mpr
        nlinarith only [hcHalf, hden]
      _ = scale := by dsimp only [scale]; field_simp; ring
  have hySmall : ‖(toEuclidean (E := E))
      (extChartAt I a y - extChartAt I a a)‖ < b.rIn / (8 * C) := hy.2.2
  have hcSmall : ‖(toEuclidean (E := E))
      (extChartAt I a a - extChartAt I a c)‖ < b.rIn / (8 * C) := by
    have hcSmall' : ‖(toEuclidean (E := E))
        (extChartAt I a c - extChartAt I a a)‖ < b.rIn / (8 * C) := hc.2.2
    simpa only [map_sub, norm_sub_rev] using hcSmall'
  have hcySmall : ‖(toEuclidean (E := E))
      (extChartAt I a y - extChartAt I a c)‖ < b.rIn / (4 * C) := by
    have heq : (toEuclidean (E := E)) (extChartAt I a y - extChartAt I a c) =
        (toEuclidean (E := E)) (extChartAt I a y - extChartAt I a a) +
          (toEuclidean (E := E)) (extChartAt I a a - extChartAt I a c) := by
      rw [← map_add]
      congr 1
      abel
    rw [heq]
    apply (norm_add_le _ _).trans_lt
    have hsum := add_lt_add hySmall hcSmall
    have heqDiv : b.rIn / (8 * C) + b.rIn / (8 * C) = b.rIn / (4 * C) := by
      field_simp
      ring
    rwa [heqDiv] at hsum
  let Q : Real := scale ^ 2
  have hQ : 0 < Q := sq_pos_of_pos hscale
  let rho : M → Real := cutoffChartRadiusSq (I := I) b c Q
  have hrho : ContMDiff I 𝓘(Real, Real) ∞ rho := cutoffChartRadiusSq_contMDiff b Q
  have hrhoc : rho c = 0 := by
    simp [rho, cutoffChartRadiusSq, chartRadiusSq, hbone hc]
  have hrhoy : 0 < rho y := cutoffChartRadiusSq_pos_of_ne b hc.1 hQ (Ne.symm hcy)
  have hyQ : rho y < Q := by
    rw [show rho y = chartRadiusSq (I := I) a c y by
      simp [rho, cutoffChartRadiusSq, hbone hy]]
    exact (sq_lt_sq₀ (norm_nonneg _) hscale.le).mpr (hcySmall.trans hsmall)
  obtain ⟨r0, hr0, hr0V⟩ := exists_cutoffChartRadiusSq_sublevel_subset b hc.1 hQ hV
  let r : Real := min (r0 / 2) (rho y / 2)
  have hr : 0 < r := lt_min (half_pos hr0) (half_pos hrhoy)
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (half_lt_self hr0)
  have hry : r < rho y := (min_le_right _ _).trans_lt (half_lt_self hrhoy)
  let R : Real := (rho y + Q) / 2
  have hyR : rho y < R := by dsimp only [R]; linarith only [hyQ]
  have hRQ : R < Q := by dsimp only [R]; linarith only [hyQ]
  have hbandCompact : IsCompact {z : M | r ≤ rho z ∧ rho z ≤ R} :=
    (isCompact_sublevel_cutoffChartRadiusSq b hRQ).inter_left
      (isClosed_le continuous_const hrho.continuous)
  have hrad {z : M} (hz : rho z ≤ R) :
      0 < b z ∧ chartRadiusSq (I := I) a c z < Q := by
    have hmidR : R < (R + Q) / 2 := by linarith only [hRQ]
    have hmidQ : (R + Q) / 2 < Q := by linarith only [hRQ]
    exact pos_and_chartRadiusSq_lt_of_cutoffChartRadiusSq_lt b hmidQ (hz.trans_lt hmidR)
  refine ⟨rho, r, R, hrho, hrhoc, hr, hry.trans hyR, hbandCompact, ?_,
    hry.le, hyR, ?_, ?_⟩
  · intro z hz
    exact hbOmega (subset_tsupport _ (hrad hz.2).1.ne')
  · intro z hz
    apply hr0V
    change rho z < r0
    rw [hz]
    exact hrr0
  · intro g z hz
    have hradz := hrad hz.2
    have hzsource : z ∈ (chartAt H a).source := b.support_subset_source hradz.1.ne'
    have hzcore : dist (extChartAt I a z) (extChartAt I a a) < b.rIn := by
      apply dist_lt_rIn_of_chartRadiusSq_lt b hc_dist
      simpa only [Q, scale, C] using hradz.2
    have hzc : z ≠ c := by
      intro heq
      subst z
      have hrc := hz.1
      rw [hrhoc] at hrc
      exact (not_le_of_gt hr) hrc
    exact cutoffChartRadiusSq_gradient_ne_zero g b hc.1 hzsource hzcore hzc Q

omit [IsManifold I ∞ M] in
private theorem isConnected_sublevel_cutoffChartRadiusSq [I.Boundaryless]
    {a : M} (b : SmoothBumpFunction I a)
    {Q R : Real} (hR : 0 < R) (hRQ : R < Q)
    (hQ : Q ≤ (b.rIn / (2 * (‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1))) ^ 2) :
    IsConnected {x | cutoffChartRadiusSq (I := I) b a Q x < R} := by
  let L := toEuclidean (E := E)
  let C : Real := ‖L.symm.toContinuousLinearMap‖ + 1
  let s : Real := b.rIn / (2 * C)
  let p : EuclideanSpace Real (Fin (Module.finrank Real E)) → E :=
    fun w => extChartAt I a a + L.symm w
  have hC : 0 < C := by
    dsimp [C]
    linarith [norm_nonneg L.symm.toContinuousLinearMap]
  have hs : 0 < s := div_pos b.rIn_pos (by positivity)
  have hRs : Real.sqrt R < s := by
    apply (Real.sqrt_lt hR.le hs.le).mpr
    exact hRQ.trans_le hQ
  have hpdist {w : EuclideanSpace Real (Fin (Module.finrank Real E))}
      (hw : w ∈ Metric.ball 0 (Real.sqrt R)) :
      dist (p w) (extChartAt I a a) < b.rIn := by
    have hwnorm : ‖w‖ < s := by
      have hw0 : ‖w‖ < Real.sqrt R := by simpa using hw
      exact hw0.trans hRs
    have hop := L.symm.toContinuousLinearMap.le_opNorm w
    have hn : ‖L.symm w‖ < C * s := calc
      ‖L.symm w‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖w‖ := hop
      _ < C * s := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
        (by dsimp [C]; linarith) hwnorm (norm_nonneg _) hC
    have hCs : C * s = b.rIn / 2 := by
      dsimp [s]
      field_simp
    rw [hCs] at hn
    have heq : dist (p w) (extChartAt I a a) = ‖L.symm w‖ := by
      simp [p, dist_eq_norm]
    rw [heq]
    exact hn.trans (half_lt_self b.rIn_pos)
  have hptarget {w : EuclideanSpace Real (Fin (Module.finrank Real E))}
      (hw : w ∈ Metric.ball 0 (Real.sqrt R)) : p w ∈ (extChartAt I a).target := by
    apply b.ball_subset
    refine ⟨(hpdist hw).trans b.rIn_lt_rOut, ?_⟩
    rw [I.range_eq_univ]
    trivial
  have heq : {x | cutoffChartRadiusSq (I := I) b a Q x < R} =
      ((extChartAt I a).symm ∘ p) '' Metric.ball 0 (Real.sqrt R) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hbx, hqx⟩ := pos_and_chartRadiusSq_lt_of_cutoffChartRadiusSq_lt b hRQ hx
      have hxsource : x ∈ (chartAt H a).source :=
        b.support_subset_source (by simpa [Function.mem_support] using hbx.ne')
      have hdist : dist (extChartAt I a x) (extChartAt I a a) < b.rIn := by
        apply dist_lt_rIn_of_chartRadiusSq_lt b (c := a)
        · simpa using b.rIn_pos
        · simpa only [dist_self, sub_zero] using hqx.trans_le hQ
      have hbone : b x = 1 := b.one_of_dist_le hxsource hdist.le
      have hqR : chartRadiusSq (I := I) a a x < R := by
        simpa [cutoffChartRadiusSq, hbone] using hx
      let w := L (extChartAt I a x - extChartAt I a a)
      refine ⟨w, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right]
        apply (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
        rw [Real.sq_sqrt hR.le]
        exact hqR
      · have hpw : p w = extChartAt I a x := by simp [p, w]
        change (extChartAt I a).symm (p w) = x
        rw [hpw]
        exact (extChartAt I a).left_inv (by simpa only [extChartAt_source] using hxsource)
    · rintro ⟨w, hw, rfl⟩
      have hy := (extChartAt I a).map_target (hptarget hw)
      have hychart := (extChartAt I a).right_inv (hptarget hw)
      have hbone : b ((extChartAt I a).symm (p w)) = 1 := by
        apply b.one_of_dist_le (by simpa only [extChartAt_source] using hy)
        rw [hychart]
        exact (hpdist hw).le
      change cutoffChartRadiusSq (I := I) b a Q ((extChartAt I a).symm (p w)) < R
      rw [cutoffChartRadiusSq, hbone]
      simp only [one_mul, sub_self, mul_zero, add_zero]
      have hw' : ‖w‖ < Real.sqrt R := by simpa using hw
      have hw2 := (sq_lt_sq₀ (norm_nonneg w) (Real.sqrt_nonneg R)).mpr hw'
      rw [Real.sq_sqrt hR.le] at hw2
      unfold chartRadiusSq
      rw [hychart]
      simpa only [p, L, add_sub_cancel_left, ContinuousLinearEquiv.apply_symm_apply] using hw2
  rw [heq]
  apply ((convex_ball (0 : EuclideanSpace Real (Fin (Module.finrank Real E))))
    (Real.sqrt R)).isConnected (Metric.nonempty_ball.mpr (Real.sqrt_pos.mpr hR)) |>.image
  apply (continuousOn_extChartAt_symm (I := I) a).comp
  · exact (continuous_const.add L.symm.continuous).continuousOn
  · exact fun w hw => hptarget hw

theorem exists_regular_sublevel_subset [I.Boundaryless] [T2Space M]
    (a : M) {V : Set M} (hV : V ∈ nhds a) :
    ∃ (rho : M → Real) (R : Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho ∧ rho a = 0 ∧
      (∀ x : M, 0 ≤ rho x) ∧ (∀ x : M, x ≠ a → 0 < rho x) ∧ 0 < R ∧
      IsConnected {x : M | rho x < R} ∧
      IsCompact {x : M | rho x ≤ R} ∧ {x : M | rho x ≤ R} ⊆ V ∧
      ∀ x : M, 0 < rho x → rho x ≤ R →
        mfderiv I 𝓘(Real, Real) rho x ≠ 0 := by
  obtain ⟨b, -, hbV⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) a).mem_iff.mp hV
  let C : Real := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    linarith [norm_nonneg (toEuclidean (E := E)).symm.toContinuousLinearMap]
  let scale : Real := b.rIn / (2 * C)
  have hscale : 0 < scale := div_pos b.rIn_pos (by positivity)
  let Q : Real := scale ^ 2
  have hQ : 0 < Q := sq_pos_of_pos hscale
  let rho : M → Real := cutoffChartRadiusSq (I := I) b a Q
  let R : Real := Q / 2
  have hrho : ContMDiff I 𝓘(Real, Real) ∞ rho := cutoffChartRadiusSq_contMDiff b Q
  have hrhoa : rho a = 0 := by
    simp [rho, cutoffChartRadiusSq, chartRadiusSq]
  have hR : 0 < R := half_pos hQ
  have hRQ : R < Q := half_lt_self hQ
  have hrad {x : M} (hx : rho x ≤ R) :
      0 < b x ∧ chartRadiusSq (I := I) a a x < Q := by
    have hmidR : R < (R + Q) / 2 := by linarith only [hRQ]
    have hmidQ : (R + Q) / 2 < Q := by linarith only [hRQ]
    exact pos_and_chartRadiusSq_lt_of_cutoffChartRadiusSq_lt b hmidQ
      (hx.trans_lt hmidR)
  refine ⟨rho, R, hrho, hrhoa,
    cutoffChartRadiusSq_nonneg b hQ.le,
    fun x hx => cutoffChartRadiusSq_pos_of_ne b (mem_chart_source H a) hQ hx, hR,
    isConnected_sublevel_cutoffChartRadiusSq b hR hRQ (le_refl Q),
    isCompact_sublevel_cutoffChartRadiusSq b hRQ, ?_, ?_⟩
  · intro x hx
    exact hbV (subset_tsupport b (hrad hx).1.ne')
  · intro x hxpos hxR
    have hradx := hrad hxR
    have hxsource : x ∈ (chartAt H a).source := b.support_subset_source hradx.1.ne'
    have hxcore : dist (extChartAt I a x) (extChartAt I a a) < b.rIn := by
      apply dist_lt_rIn_of_chartRadiusSq_lt (c := a) (x := x) b
        (by simpa only [dist_self] using b.rIn_pos)
      simpa only [Q, scale, C, dist_self, sub_zero] using hradx.2
    have hxa : x ≠ a := by
      intro heq
      subst x
      rw [hrhoa] at hxpos
      exact (lt_irrefl 0) hxpos
    exact cutoffChartRadiusSq_mfderiv_ne_zero b
      (mem_chart_source H a) hxsource hxcore hxa Q

end SmoothBumpFunction
