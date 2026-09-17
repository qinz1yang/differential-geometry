import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalRadialReserve


set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 : ℝ} {x : M} {t : ℝ}


theorem CanonicalWitness.one_le_comparison_constant
    (W : CanonicalWitness S eps C1 C2 x t) : 1 ≤ C2 :=
  one_le_of_le_mul_right₀ W.Q_pos
    (W.scalar_bounds x (interior_subset W.center_inside)).2


theorem CanonicalWitness.alternative_eq_neck_or_cap_of_mul_scalar_lt {y : M}
    (W : CanonicalWitness S eps C1 C2 x t) (hy : y ∈ connectedComponent x)
    (hscalar : C2 * S.scalar t y < S.scalar t x) :
    (∃ neck : LocalNeck S eps x t W.domain.carrier,
      W.alternative = CanonicalAlternative.neck neck) ∨
    ∃ cap : LocalCap S eps x t W.domain.carrier,
      ∃ hdepth : ∀ z ∈ cap.tube,
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z,
        W.alternative = CanonicalAlternative.cap cap hdepth := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hproper : W.domain.carrier ≠ connectedComponent x := by
    intro hwhole
    have hbound := (W.scalar_bounds y (hwhole.symm ▸ hy)).1
    have hmul := mul_le_mul_of_nonneg_left hbound hC2.le
    have hcancel : C2 * (C2⁻¹ * S.scalar t x) = S.scalar t x := by
      rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul]
    rw [hcancel] at hmul
    exact (not_le_of_gt hscalar) hmul
  cases W.alternative with
  | neck data => exact Or.inl ⟨data, rfl⟩
  | cap data deep => exact Or.inr ⟨data, deep, rfl⟩
  | positive whole data hsec => exact (hproper whole).elim
  | round whole data => exact (hproper whole).elim


theorem CanonicalWitness.strict_curvature_volume_reserves
    (W : CanonicalWitness S eps C1 C2 x t) :
    let C := max C1 C2 + 1
    1 ≤ C ∧ C1 < C ∧ C2 < C ∧
      (∀ y ∈ W.domain.carrier,
        C⁻¹ * S.scalar t x < S.scalar t y ∧ S.scalar t y < C * S.scalar t x) ∧
      (∀ y ∈ W.domain.carrier,
        Real.sqrt (FlowMetricBall.rmNormSq S t y) < C * S.scalar t x) ∧
      (W.alternative.requiresVolume →
        ENNReal.ofReal (C⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) <
          riemannianVolumeMeasure I3 M (S.base.metric t) W.domain.carrier) := by
  let C := max C1 C2 + 1
  have hc1 : C1 < C := by dsimp only [C]; linarith [le_max_left C1 C2]
  have hc2 : C2 < C := by dsimp only [C]; linarith [le_max_right C1 C2]
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hinv : C⁻¹ < C2⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt hC2 hc2
  have hupper : C2 * S.scalar t x < C * S.scalar t x :=
    mul_lt_mul_of_pos_right hc2 W.Q_pos
  refine ⟨W.one_le_comparison_constant.trans hc2.le, hc1, hc2, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨(mul_lt_mul_of_pos_right hinv W.Q_pos).trans_le (W.scalar_bounds y hy).1,
      (W.scalar_bounds y hy).2.trans_lt hupper⟩
  · intro y hy
    exact (W.rm_bound y hy).trans_lt hupper
  · intro hvolume
    have hden : 0 < S.scalar t x * Real.sqrt (S.scalar t x) :=
      mul_pos W.Q_pos (Real.sqrt_pos.mpr W.Q_pos)
    have hratio : C⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x)) <
        C2⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x)) := by
      simpa only [div_eq_mul_inv] using mul_lt_mul_of_pos_right hinv (inv_pos.mpr hden)
    exact ((ENNReal.ofReal_lt_ofReal_iff (div_pos (inv_pos.mpr hC2) hden)).mpr hratio).trans_le
      (W.volume hvolume)

omit [T2Space M] [SigmaCompactSpace M] in
private theorem sectional_area_nonneg (g : SmoothRiemannianMetric I3 M) (y : M)
    (v w : TangentSpace I3 y) :
    0 ≤ g.inner y v v * g.inner y w w - (g.inner y v w) ^ 2 := by
  let G := (Tensor0SBundle.tangentMetricDataGen (I := I3) g y).metric
  let : PreInnerProductSpace.Core ℝ (TangentSpace I3 y) := G.toCore.toCore
  let : Inner ℝ (TangentSpace I3 y) := G.toCore.toCore.toInner
  have hcs := InnerProductSpace.Core.inner_mul_inner_self_le
    (𝕜 := ℝ) (F := TangentSpace I3 y) v w
  have hvw : Inner.inner ℝ v w = g.inner y v w :=
    Tensor0SBundle.TangentMetricDataGen.inner_eq_gen
      (Tensor0SBundle.tangentMetricDataGen (I := I3) g y) v w
  have hwv : Inner.inner ℝ w v = g.inner y v w := by
    calc
      _ = g.inner y w v := Tensor0SBundle.TangentMetricDataGen.inner_eq_gen
        (Tensor0SBundle.tangentMetricDataGen (I := I3) g y) w v
      _ = _ := g.symm y w v
  have hvv : Inner.inner ℝ v v = g.inner y v v :=
    Tensor0SBundle.TangentMetricDataGen.inner_eq_gen
      (Tensor0SBundle.tangentMetricDataGen (I := I3) g y) v v
  have hww : Inner.inner ℝ w w = g.inner y w w :=
    Tensor0SBundle.TangentMetricDataGen.inner_eq_gen
      (Tensor0SBundle.tangentMetricDataGen (I := I3) g y) w w
  rw [hvw, hwv, hvv, hww] at hcs
  apply sub_nonneg.mpr
  simpa [Real.norm_eq_abs, pow_two] using hcs

omit [T2Space M] [SigmaCompactSpace M] in
theorem SecLower.mono {g : SmoothRiemannianMetric I3 M} {a b : ℝ} {U : Set M}
    (h : SecLower g b U) (hab : a ≤ b) : SecLower g a U := by
  intro y hy v w
  exact (mul_le_mul_of_nonneg_right hab (sectional_area_nonneg g y v w)).trans (h y hy v w)


def CanonicalAlternative.mono_constant {C C' : ℝ} {U : Set M}
    (A : CanonicalAlternative S eps C x t U) (hC : 0 < C) (hCC : C ≤ C')
    (hQ : 0 ≤ S.scalar t x) : CanonicalAlternative S eps C' x t U := by
  cases A with
  | neck data => exact .neck data
  | cap data deep => exact .cap data deep
  | positive whole data hsec =>
    have hinv : C'⁻¹ ≤ C⁻¹ := (inv_le_inv₀ (hC.trans_le hCC) hC).mpr hCC
    exact .positive whole data (hsec.mono (mul_le_mul_of_nonneg_right hinv hQ))
  | round whole data => exact .round whole data

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem CanonicalAlternative.mono_constant_requiresVolume
    {C C' : ℝ} {U : Set M} (A : CanonicalAlternative S eps C x t U)
    (hC : 0 < C) (hCC : C ≤ C') (hQ : 0 ≤ S.scalar t x) :
    (A.mono_constant hC hCC hQ).requiresVolume = A.requiresVolume := by
  cases A <;> rfl


def CanonicalWitness.enlarge_constants (W : CanonicalWitness S eps C1 C2 x t)
    {C1' C2' : ℝ} (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    CanonicalWitness S eps C1' C2' x t := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hinv : C2'⁻¹ ≤ C2⁻¹ := (inv_le_inv₀ (hC2.trans_le h2) hC2).mpr h2
  have hupper : C2 * S.scalar t x ≤ C2' * S.scalar t x :=
    mul_le_mul_of_nonneg_right h2 W.Q_pos.le
  refine {
    Q_pos := W.Q_pos
    time_mem := W.time_mem
    eps_pos := W.eps_pos
    eps_lt_one := W.eps_lt_one
    domain := W.domain
    center_inside := W.center_inside
    radius := W.radius
    radius_lower := W.radius_lower
    radius_upper := W.radius_upper.trans (div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _))
    ball_inside := W.ball_inside
    inside_ball := W.inside_ball
    scalar_bounds := fun y hy =>
      ⟨(mul_le_mul_of_nonneg_right hinv W.Q_pos.le).trans (W.scalar_bounds y hy).1,
        (W.scalar_bounds y hy).2.trans hupper⟩
    rm_bound := fun y hy => (W.rm_bound y hy).trans hupper
    alternative := W.alternative.mono_constant hC2 h2 W.Q_pos.le
    volume := ?_
    gradient := ?_
    time_derivative := W.time_derivative.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)) }
  · intro hvolume
    have hvolume' : W.alternative.requiresVolume := by
      simpa only [CanonicalAlternative.mono_constant_requiresVolume] using hvolume
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) (W.volume hvolume')
    exact div_le_div_of_nonneg_right hinv
      (mul_nonneg W.Q_pos.le (Real.sqrt_nonneg _))
  · intro v
    exact (W.gradient v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 W.Q_pos.le)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))


@[simp] theorem CanonicalWitness.enlarge_constants_domain
    (W : CanonicalWitness S eps C1 C2 x t) {C1' C2' : ℝ}
    (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    (W.enlarge_constants h1 h2).domain = W.domain := rfl


@[simp] theorem CanonicalWitness.enlarge_constants_requiresVolume
    (W : CanonicalWitness S eps C1 C2 x t) {C1' C2' : ℝ}
    (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    (W.enlarge_constants h1 h2).alternative.requiresVolume = W.alternative.requiresVolume := by
  exact CanonicalAlternative.mono_constant_requiresVolume W.alternative
    (zero_lt_one.trans_le W.one_le_comparison_constant) h2 W.Q_pos.le


theorem CanonicalWitness.exists_strict_reserve_witness
    (W : CanonicalWitness S eps C1 C2 x t) :
    let C := max C1 C2 + 1
    1 ≤ C ∧ ∃ W' : CanonicalWitness S eps C C x t,
      W'.domain = W.domain ∧ ∃ a b margin : ℝ,
        0 < a ∧ 0 < margin ∧ b < (2 - margin) * a ∧
        riemannianClosedBallOf (I := I3) (S.base.metric t) x a ⊆ W'.domain.carrier ∧
        W'.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x b ∧
        (∀ y ∈ W'.domain.carrier,
          C⁻¹ * S.scalar t x < S.scalar t y ∧ S.scalar t y < C * S.scalar t x) ∧
        (∀ y ∈ W'.domain.carrier,
          Real.sqrt (FlowMetricBall.rmNormSq S t y) < C * S.scalar t x) ∧
        (W'.alternative.requiresVolume →
          ENNReal.ofReal (C⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) <
            riemannianVolumeMeasure I3 M (S.base.metric t) W'.domain.carrier) := by
  obtain ⟨hC, h1, h2, hscalar, hrm, hvolume⟩ := W.strict_curvature_volume_reserves
  let W' := W.enlarge_constants h1.le h2.le
  obtain ⟨a, b, margin, ha, har, hm, hab, _, houter⟩ := W'.exists_radial_reserve
  have hinner : riemannianClosedBallOf (I := I3) (S.base.metric t) x a ⊆ W'.domain.carrier := by
    intro y hy
    apply W'.ball_inside
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (ha.trans har)).mpr har)
  refine ⟨hC, W', rfl, a, b, margin, ha, hm, hab, hinner, houter, hscalar, hrm, ?_⟩
  intro hv
  apply hvolume
  simpa only [W', CanonicalWitness.enlarge_constants_requiresVolume] using hv

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
