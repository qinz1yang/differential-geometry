import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowScalarPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M] {D : RealTimeInterval}

theorem scalar_le_four_mul_max_of_gradient_bound (S : SolutionOn (I := I) (M := M) D)
    {Cgrad : ℝ≥0} {qcan t r : ℝ} {x y : M}
    (hgrad : ∀ w, qcan < S.scalar t w → ∀ v : TangentSpace I w,
      |scalarDifferential (I := I) S t w v| ≤
        Cgrad * S.scalar t w * Real.sqrt (S.scalar t w) *
          Real.sqrt ((S.base.metric t).inner w v v))
    (hx : 0 < S.scalar t x)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (S.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I) (S.base.metric t) x r) :
    S.scalar t y ≤ 4 * max (S.scalar t x) qcan := by
  set N := max (S.scalar t x) qcan with hNdef
  have hN : 0 < N := hx.trans_le (le_max_left _ _)
  set m := Real.sqrt N with hmdef
  have hm : 0 < m := Real.sqrt_pos.2 hN
  have hmsq : m ^ 2 = N := Real.sq_sqrt hN.le
  have hC : (0 : ℝ) ≤ Cgrad := Cgrad.coe_nonneg
  set r0 := max r 0 with hr0def
  have hr0 : 0 ≤ r0 := le_max_right _ _
  have hy0 : y ∈ riemannianClosedBallOf (I := I) (S.base.metric t) x r0 :=
    riemannianClosedBallOf_mono (I := I) _ _ (le_max_left _ _) hy
  have hr0b : (Cgrad : ℝ) * r0 * m ≤ 1 / 4 := by
    rcases le_total r 0 with h | h
    · rw [hr0def, max_eq_right h]
      norm_num
    · rwa [hr0def, max_eq_left h]
  set η := 1 / (16 * ((Cgrad : ℝ) + 1) * m) with hηdef
  have hη : 0 < η := by positivity
  have hηb : (Cgrad : ℝ) * η * m ≤ 1 / 16 := by
    rw [hηdef, show (Cgrad : ℝ) * (1 / (16 * ((Cgrad : ℝ) + 1) * m)) * m =
      (Cgrad : ℝ) / (16 * ((Cgrad : ℝ) + 1)) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨gam, hgam, hgam0, hgam1, hspeed⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall (I := I) (S.base.metric t) hr0 hη hy0
  have hcont : ContinuousOn (fun sig : ℝ => S.scalar t (gam sig)) (Icc 0 1) :=
    (((scalarSmoothOfSolution (I := I) S t).continuous).comp hgam.continuous).continuousOn
  have hkey : ∀ τ ∈ Icc (0 : ℝ) 1, (fun sig : ℝ => S.scalar t (gam sig)) τ ≤ 4 * N := by
    refine forall_le_of_no_crossing (B := 9 / 4 * N) (by linarith) hcont ?_
    intro uu vv h0u huv hv1 hge hstart hend
    have hsub : Icc uu vv ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc h0u hv1
    have hpos : ∀ w ∈ Icc uu vv, 0 < S.scalar t (gam w) := fun w hw =>
      lt_of_lt_of_le (by positivity) (hge w hw)
    have hqw : ∀ w ∈ Icc uu vv, qcan < S.scalar t (gam w) := fun w hw =>
      lt_of_lt_of_le (by linarith [le_max_right (S.scalar t x) qcan]) (hge w hw)
    have hderiv : ∀ w ∈ Icc uu vv,
        HasDerivAt (fun sig : ℝ => (Real.sqrt (S.scalar t (gam sig)))⁻¹)
          (-(1 / (2 * Real.sqrt (S.scalar t (gam w))) *
              scalarDifferential (I := I) S t (gam w)
                (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
              Real.sqrt (S.scalar t (gam w)) ^ 2) w := fun w hw =>
      hasDerivAt_inv_sqrt (hasDerivAt_scalar_comp (I := I) S t hgam w) (hpos w hw)
    have hbdd : ∀ w ∈ Icc uu vv,
        |-(1 / (2 * Real.sqrt (S.scalar t (gam w))) *
            scalarDifferential (I := I) S t (gam w)
              (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
            Real.sqrt (S.scalar t (gam w)) ^ 2| ≤
          (Cgrad : ℝ) / 2 * Real.sqrt ((S.base.metric t).inner (gam w)
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) := by
      intro w hw
      refine abs_deriv_inv_sqrt_le (hpos w hw) ?_
      have hgd := hgrad (gam w) (hqw w hw) (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
      refine hgd.trans_eq ?_
      ring
    have hbud := abs_sub_le_of_hasDerivAt_of_lintegral_le
      (f := fun sig : ℝ => (Real.sqrt (S.scalar t (gam sig)))⁻¹)
      (a := uu) (b := vv)
      (v := fun w : ℝ => Real.sqrt ((S.base.metric t).inner (gam w)
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))))
      huv hsub (by positivity) (by positivity) hderiv hbdd hspeed.le
    have hstart' : S.scalar t (gam uu) ≤ max (9 / 4 * N) (S.scalar t (gam 0)) := hstart
    rw [hgam0] at hstart'
    have hstart2 : S.scalar t (gam uu) ≤ 9 / 4 * N :=
      hstart'.trans (max_le le_rfl ((le_max_left (S.scalar t x) qcan).trans (by linarith)))
    have hend' : 4 * N ≤ S.scalar t (gam vv) := hend
    have hsu : Real.sqrt (S.scalar t (gam uu)) ≤ 3 / 2 * m := by
      calc Real.sqrt (S.scalar t (gam uu)) ≤ Real.sqrt ((3 / 2 * m) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [mul_pow, hmsq]; linarith)
        _ = 3 / 2 * m := Real.sqrt_sq (by positivity)
    have hsv : 2 * m ≤ Real.sqrt (S.scalar t (gam vv)) := by
      calc 2 * m = Real.sqrt ((2 * m) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (S.scalar t (gam vv)) :=
            Real.sqrt_le_sqrt (by rw [mul_pow, hmsq]; linarith)
    have hA : (3 / 2 * m)⁻¹ ≤ (Real.sqrt (S.scalar t (gam uu)))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 (hpos uu (left_mem_Icc.2 huv))) hsu
    have hB : (Real.sqrt (S.scalar t (gam vv)))⁻¹ ≤ (2 * m)⁻¹ :=
      inv_anti₀ (by positivity) hsv
    have hgap : (3 / 2 * m)⁻¹ - (2 * m)⁻¹ ≤ (Cgrad : ℝ) / 2 * (r0 + η) := by
      have := neg_abs_le ((Real.sqrt (S.scalar t (gam vv)))⁻¹ -
        (Real.sqrt (S.scalar t (gam uu)))⁻¹)
      linarith
    have hgapm : (3 / 2 * m)⁻¹ - (2 * m)⁻¹ = 1 / 6 * m⁻¹ := by
      field_simp
      ring
    rw [hgapm] at hgap
    have hmul := mul_le_mul_of_nonneg_right hgap hm.le
    rw [mul_assoc, inv_mul_cancel₀ hm.ne'] at hmul
    nlinarith
  have h1 := hkey 1 ⟨by norm_num, le_rfl⟩
  simp only [hgam1] at h1
  exact h1

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem scalar_le_four_mul_max_of_gradient_bound_at_time
    {Cgrad : ℝ≥0} {qcan t r : ℝ} {x y : P.Carrier}
    (hgrad : ∀ w, qcan < G.flow.scalar t w → ∀ v : TangentSpace I3 w,
      |scalarDifferential G.flow t w v| ≤
        Cgrad * G.flow.scalar t w * Real.sqrt (G.flow.scalar t w) *
          Real.sqrt ((G.flow.base.metric t).inner w v v))
    (hx : 0 < G.flow.scalar t x)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (G.flow.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t) x r) :
    G.flow.scalar t y ≤ 4 * max (G.flow.scalar t x) qcan := by
  have : IsManifold I3 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)
  exact scalar_le_four_mul_max_of_gradient_bound G.flow hgrad hx hr hy

theorem scalar_le_four_mul_max_of_gradientBoundBefore
    {Cgrad : ℝ≥0} {qcan t₀ t r : ℝ} {x y : P.Carrier}
    (hG : G.GradientBoundBefore Cgrad qcan t₀) (ht : t ∈ Ioo a t₀)
    (hx : 0 < G.flow.scalar t x)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (G.flow.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t) x r) :
    G.flow.scalar t y ≤ 4 * max (G.flow.scalar t x) qcan :=
  G.scalar_le_four_mul_max_of_gradient_bound_at_time (fun w hw => hG w t ht hw) hx hr hy

theorem scalar_le_four_mul_max_of_gradientBoundOn
    {Cgrad : ℝ≥0} {qcan t₀ η t r : ℝ} {x y : P.Carrier}
    (hG : G.GradientBoundOn Cgrad qcan t₀ η) (hat : a < t) (ht₀ : t₀ ≤ t)
    (htη : t < t₀ + η) (hts : t < s)
    (hx : 0 < G.flow.scalar t x)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (G.flow.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t) x r) :
    G.flow.scalar t y ≤ 4 * max (G.flow.scalar t x) qcan :=
  G.scalar_le_four_mul_max_of_gradient_bound_at_time
    (fun w hw => hG w t hat ht₀ htη hts hw) hx hr hy

private theorem scalar_le_two_mul_of_derivativeBoundBefore_at
    {Ctime : ℝ≥0} {qcan K t v : ℝ} (y : P.Carrier)
    (hG : G.DerivativeBoundBefore Ctime qcan t) (hts : t < s)
    (hav : a ≤ v) (hvt : v ≤ t) (hK : 0 < K) (hqcan : qcan ≤ K)
    (hscalar : G.flow.scalar t y ≤ K) (htime : Ctime * K * (t - v) ≤ 1 / 2) :
    G.flow.scalar v y ≤ 2 * K := by
  have hsub : Icc a t ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier :=
    fun _ hw => ⟨hw.1, hw.2.trans_lt hts⟩
  have hlip : LipschitzOnWith Ctime (fun w => (max K (G.flow.scalar w y))⁻¹) (Icc a t) := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
      (r' := fun w => derivWithin (fun z => G.flow.scalar z y) (Iic w) w) hK
    · intro w hw
      exact (G.equation.scalarTime hw hsub y).continuousWithinAt
    · intro w hw _
      have hd : DifferentiableAt ℝ (fun z => G.flow.scalar z y) w :=
        (G.equation.scalarTime (K := Ioo a t) hw (Ioo_subset_Icc_self.trans hsub)
          y).differentiableAt (Ioo_mem_nhds hw.1 hw.2)
      rw [hd.derivWithin (uniqueDiffWithinAt_Iic w)]
      exact hd.hasDerivAt
    · exact fun w hw hR => hG y w hw (hqcan.trans_lt hR)
  have hd := hlip.dist_le_mul v ⟨hav, hvt⟩ t ⟨hav.trans hvt, le_rfl⟩
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm v t, abs_of_nonneg (sub_nonneg.mpr hvt),
    max_eq_left hscalar] at hd
  have hlow := (abs_le.mp hd).1
  have hhalf : (Ctime : ℝ) * (t - v) ≤ (2 * K)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 2 * K)]
    nlinarith
  have htwo : K⁻¹ = 2 * (2 * K)⁻¹ := by field_simp
  have hinv : (2 * K)⁻¹ ≤ (max K (G.flow.scalar v y))⁻¹ := by linarith
  exact (le_max_right K _).trans
    ((inv_le_inv₀ (by positivity : 0 < 2 * K) (hK.trans_le (le_max_left K _))).mp hinv)

theorem scalar_le_eight_mul_max_of_gradient_bound_of_derivativeBoundBefore
    {Cgrad Ctime : ℝ≥0} {qcan t r v : ℝ} {x y : P.Carrier}
    (hgrad : ∀ w, qcan < G.flow.scalar t w → ∀ e : TangentSpace I3 w,
      |scalarDifferential G.flow t w e| ≤
        Cgrad * G.flow.scalar t w * Real.sqrt (G.flow.scalar t w) *
          Real.sqrt ((G.flow.base.metric t).inner w e e))
    (hderiv : G.DerivativeBoundBefore Ctime qcan t) (hts : t < s)
    (hx : 0 < G.flow.scalar t x)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (G.flow.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t) x r)
    (hav : a ≤ v) (hvt : v ≤ t)
    (htime : Ctime * max (G.flow.scalar t x) qcan * (t - v) ≤ 1 / 8) :
    G.flow.scalar v y ≤ 8 * max (G.flow.scalar t x) qcan := by
  have hN : 0 < max (G.flow.scalar t x) qcan := hx.trans_le (le_max_left _ _)
  have hspace := G.scalar_le_four_mul_max_of_gradient_bound_at_time hgrad hx hr hy
  have h := scalar_le_two_mul_of_derivativeBoundBefore_at G y hderiv hts hav hvt
    (by positivity : 0 < 4 * max (G.flow.scalar t x) qcan)
    (by linarith [le_max_right (G.flow.scalar t x) qcan]) hspace (by nlinarith)
  linarith

theorem scalar_le_eight_mul_max_of_gradientBoundBefore_of_derivativeBoundBefore
    {Cgrad Ctime : ℝ≥0} {qcan t₀ t r v : ℝ} {x y : P.Carrier}
    (hG : G.GradientBoundBefore Cgrad qcan t₀) (hD : G.DerivativeBoundBefore Ctime qcan t₀)
    (ht : t ∈ Ioo a t₀) (hts : t < s)
    (hx : 0 < G.flow.scalar t x)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (G.flow.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t) x r)
    (hav : a ≤ v) (hvt : v ≤ t)
    (htime : Ctime * max (G.flow.scalar t x) qcan * (t - v) ≤ 1 / 8) :
    G.flow.scalar v y ≤ 8 * max (G.flow.scalar t x) qcan :=
  G.scalar_le_eight_mul_max_of_gradient_bound_of_derivativeBoundBefore
    (fun w hw => hG w t ht hw) (G.derivativeBoundBefore_mono ht.2.le hD) hts hx hr hy hav hvt
    htime

end OrientedThreeStage.IncomingSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
