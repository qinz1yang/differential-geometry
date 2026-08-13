import DifferentialGeometry.Analysis.ODE.Nagumo
import DifferentialGeometry.Analysis.Convex.ProperConeFace
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ProperCone

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set Filter
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [completeF : CompleteSpace F]

structure IsInnerProductHeatReactionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (reaction : Real → M → F → F)
    (u : Real → M → F) : Prop where
  jointCont :
    ContinuousOn (fun q : Real × M ↦ u q.1 q.2) (D.carrier ×ˢ univ)
  scalarSliceSmooth :
    ∀ y : F, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (innerScalarization u y t)
  equation :
    ∀ y : F, ∀ t : Real, t ∈ D.regular → ∀ x : M,
      HasDerivAt (fun s : Real ↦ innerScalarization u y s x)
        (laplacianAt (I := I) G t (innerScalarization u y t) x +
          inner Real (reaction t x (u t x)) y) t

private theorem deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc
    {f : Real → Real} {a d : Real} (ha : 0 < a)
    (hmax : IsMaxOn f (Set.Icc 0 a) a)
    (hderiv : HasDerivAt f d a) :
    0 ≤ d := by
  have hdir : -(a / 2) ∈ posTangentConeAt (Set.Icc 0 a) a := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [show a + -(a / 2) = a / 2 by ring, segment_symm,
      segment_eq_Icc (by linarith : a / 2 ≤ a)]
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt hdir
  have heval : (ContinuousLinearMap.toSpanSingleton Real d) (-(a / 2)) =
      -(a / 2) * d := by
    simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  rw [heval] at hnonpos
  nlinarith

include completeF in
theorem closed_convex_heat_reaction_mem_of_supporting_normal
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : Set F) (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex Real C)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p ∈ C, ∀ ν : F,
      (∀ q ∈ C, inner Real ν (q - p) ≤ 0) →
        inner Real ν (reaction t x p) ≤ 0)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  classical
  have hIco : ∀ t : Real, t ∈ Set.Ico 0 T → ∀ x : M, u t x ∈ C := by
    intro t ht x
    by_contra hout
    have htpos : 0 < t := by
      by_contra htzero
      have : t = 0 := le_antisymm (not_lt.mp htzero) ht.1
      exact hout (by simpa [this] using hinit x)
    let K : Real := (L : Real) + 1
    let d : Real × M → Real := fun q ↦
      Real.exp (-K * q.1) * Metric.infDist (u q.1 q.2) C
    let Q : Set (Real × M) := Set.Icc 0 t ×ˢ (Set.univ : Set M)
    have hQcompact : IsCompact Q :=
      (isCompact_Icc (a := (0 : Real)) (b := t)).prod CompactSpace.isCompact_univ
    have hQne : Q.Nonempty :=
      ⟨(0, x), Set.mk_mem_prod ⟨le_rfl, htpos.le⟩ (Set.mem_univ x)⟩
    have hQsub : Q ⊆ (RealTimeInterval.closed 0 T hT).carrier ×ˢ univ := by
      intro q hq
      exact ⟨⟨hq.1.1, hq.1.2.trans ht.2.le⟩, hq.2⟩
    have hdcont : ContinuousOn d Q := by
      have hexp : Continuous (fun q : Real × M ↦ Real.exp (-K * q.1)) := by
        fun_prop
      exact hexp.continuousOn.mul
        ((Metric.continuous_infDist_pt C).comp_continuousOn (hsol.jointCont.mono hQsub))
    obtain ⟨q₀, hq₀Q, hq₀max⟩ := hQcompact.exists_isMaxOn hQne hdcont
    have hdtxpos : 0 < d (t, x) := by
      apply mul_pos (Real.exp_pos _)
      exact (hclosed.notMem_iff_infDist_pos hne).mp hout
    have hdq₀pos : 0 < d q₀ := lt_of_lt_of_le hdtxpos (hq₀max ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩)
    have hq₀tpos : 0 < q₀.1 := by
      by_contra hnonpos
      have hzero : q₀.1 = 0 := le_antisymm (not_lt.mp hnonpos) hq₀Q.1.1
      have : d q₀ = 0 := by
        simp [d, hzero, Metric.infDist_zero_of_mem (hinit q₀.2)]
      linarith
    have hq₀reg : q₀.1 ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change q₀.1 ∈ Set.Ioo 0 T
      exact ⟨hq₀tpos, lt_of_le_of_lt hq₀Q.1.2 ht.2⟩
    obtain ⟨p, hpC, hpmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex (u q₀.1 q₀.2)
    let ν : F := u q₀.1 q₀.2 - p
    have hdist₀ : Metric.infDist (u q₀.1 q₀.2) C = ‖ν‖ := by
      rw [Metric.infDist_eq_iInf]
      simpa [ν, dist_eq_norm] using hpmin.symm
    have hνpos : 0 < ‖ν‖ := by
      have : 0 < Metric.infDist (u q₀.1 q₀.2) C := by
        exact (mul_pos_iff_of_pos_left (Real.exp_pos (-K * q₀.1))).mp
          (by simpa [d] using hdq₀pos)
      simpa [hdist₀] using this
    have hnormal : ∀ q ∈ C, inner Real ν (q - p) ≤ 0 := by
      exact (norm_eq_iInf_iff_real_inner_le_zero hconvex hpC).mp hpmin
    have hsupport : ∀ s : Real, ∀ y : M,
        inner Real (u s y - p) ν ≤ Metric.infDist (u s y) C * ‖ν‖ := by
      intro s y
      obtain ⟨q, hqC, hqmin⟩ :=
        exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex (u s y)
      have hqdist : ‖u s y - q‖ = Metric.infDist (u s y) C := by
        rw [Metric.infDist_eq_iInf]
        simpa [dist_eq_norm] using hqmin
      calc
        inner Real (u s y - p) ν =
            inner Real (u s y - q) ν + inner Real (q - p) ν := by
          rw [← inner_add_left]
          congr 2
          abel
        _ ≤ ‖u s y - q‖ * ‖ν‖ + 0 :=
          add_le_add (real_inner_le_norm _ _) (by simpa [real_inner_comm] using hnormal q hqC)
        _ = Metric.infDist (u s y) C * ‖ν‖ := by rw [hqdist, add_zero]
    let z : Real → M → Real := fun s y ↦
      Real.exp (-K * s) * inner Real (u s y - p) ν
    have hzmax : ∀ r ∈ Q, z r.1 r.2 ≤ z q₀.1 q₀.2 := by
      intro r hr
      have hleft := mul_le_mul_of_nonneg_left (hsupport r.1 r.2)
        (Real.exp_pos (-K * r.1)).le
      have hright := mul_le_mul_of_nonneg_right (hq₀max hr) (norm_nonneg ν)
      have hz₀ : z q₀.1 q₀.2 = d q₀ * ‖ν‖ := by
        simp only [z, d, ν, real_inner_self_eq_norm_sq, hdist₀]
        ring
      calc
        z r.1 r.2 ≤ Real.exp (-K * r.1) *
            (Metric.infDist (u r.1 r.2) C * ‖ν‖) := hleft
        _ = d r * ‖ν‖ := by simp only [d]; ring
        _ ≤ d q₀ * ‖ν‖ := hright
        _ = z q₀.1 q₀.2 := hz₀.symm
    have hzspatial : IsLocalMax (z q₀.1) q₀.2 := by
      exact Filter.Eventually.of_forall (fun y ↦
        hzmax (q₀.1, y) ⟨hq₀Q.1, mem_univ y⟩)
    have hq₀carrier : q₀.1 ∈ (RealTimeInterval.closed 0 T hT).carrier :=
      (RealTimeInterval.closed 0 T hT).regular_subset hq₀reg
    have hzslice : ContMDiff I 𝓘(Real, Real) ∞ (z q₀.1) := by
      simpa only [z, innerScalarization, inner_sub_left] using
        contMDiff_const.mul
          ((hsol.scalarSliceSmooth ν q₀.1 hq₀carrier).sub contMDiff_const)
    have hzlap : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 ≤ 0 :=
      laplacianAt_nonpos_at_spatial_max (I := I) G q₀.1 hzspatial hzslice
    have hztimeMax : IsMaxOn (fun s ↦ z s q₀.2) (Set.Icc 0 q₀.1) q₀.1 := by
      intro s hs
      exact hzmax (s, q₀.2) ⟨⟨hs.1, hs.2.trans hq₀Q.1.2⟩, mem_univ q₀.2⟩
    have hscalarEq := hsol.equation ν q₀.1 hq₀reg q₀.2
    have hexpDeriv : HasDerivAt (fun s : Real ↦ Real.exp (-K * s))
        (Real.exp (-K * q₀.1) * (-K)) q₀.1 := by
      have hinner : HasDerivAt (fun s : Real ↦ -K * s) (-K) q₀.1 := by
        simpa using (hasDerivAt_id q₀.1).const_mul (-K)
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_exp (-K * q₀.1)).comp q₀.1 hinner
    have hzderiv : HasDerivAt (fun s ↦ z s q₀.2)
        (Real.exp (-K * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (innerScalarization u ν q₀.1) q₀.2 +
              inner Real (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν) -
          K * Real.exp (-K * q₀.1) * inner Real (u q₀.1 q₀.2 - p) ν) q₀.1 := by
      convert hexpDeriv.mul (hscalarEq.sub_const (inner Real p ν)) using 1
      · funext s
        simp only [z, innerScalarization, inner_sub_left, Pi.mul_apply]
      · simp only [innerScalarization, inner_sub_left]
        ring
    have hztime : 0 ≤
        Real.exp (-K * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (innerScalarization u ν q₀.1) q₀.2 +
              inner Real (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν) -
          K * Real.exp (-K * q₀.1) * inner Real (u q₀.1 q₀.2 - p) ν :=
      deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc hq₀tpos hztimeMax hzderiv
    have hscalarSmooth := hsol.scalarSliceSmooth ν q₀.1 hq₀carrier
    have hscalarMDiff : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real) (innerScalarization u ν q₀.1) y :=
      fun y ↦ hscalarSmooth.mdifferentiable (by simp) y
    have hzlapEq : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 =
        Real.exp (-K * q₀.1) *
          laplacianAt (I := I) G q₀.1 (innerScalarization u ν q₀.1) q₀.2 := by
      have hsub : laplacianAt (I := I) G q₀.1
          (fun y : M ↦ innerScalarization u ν q₀.1 y - inner Real p ν) q₀.2 =
          laplacianAt (I := I) G q₀.1 (innerScalarization u ν q₀.1) q₀.2 := by
        exact laplacian_sub_const (I := I) (G.connection q₀.1) (G.metric q₀.1)
          (inner Real p ν) hscalarMDiff q₀.2
      have hsubSmooth : ContMDiff I 𝓘(Real, Real) ∞
          (fun y : M ↦ innerScalarization u ν q₀.1 y - inner Real p ν) :=
        hscalarSmooth.sub contMDiff_const
      have hsmul := laplacianAt_smul (I := I) G q₀.1
        (Real.exp (-K * q₀.1))
        (fun y ↦ hsubSmooth.mdifferentiable (by simp) y)
        (gradientFun_mdiffAt (I := I) (G.metric q₀.1) hsubSmooth q₀.2)
      have hfun : z q₀.1 = Real.exp (-K * q₀.1) •
          (fun y : M ↦ innerScalarization u ν q₀.1 y - inner Real p ν) := by
        funext y
        simp [z, innerScalarization, inner_sub_left]
      rw [hfun, hsmul, hsub]
    have hparabolicNonneg : 0 ≤
        Real.exp (-K * q₀.1) *
          (inner Real (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν - K * ‖ν‖ ^ 2) := by
      rw [hzlapEq] at hzlap
      rw [show u q₀.1 q₀.2 - p = ν from rfl,
        real_inner_self_eq_norm_sq] at hztime
      nlinarith [Real.exp_pos (-K * q₀.1)]
    have hreactionp : inner Real ν (reaction q₀.1 q₀.2 p) ≤ 0 :=
      hreaction q₀.1 hq₀reg q₀.2 p hpC ν hnormal
    have hLip := (hL q₀.1 hq₀reg q₀.2).norm_sub_le
      (u q₀.1 q₀.2) p
    have hinnerLip : inner Real ν
        (reaction q₀.1 q₀.2 (u q₀.1 q₀.2) - reaction q₀.1 q₀.2 p) ≤
          (L : Real) * ‖ν‖ ^ 2 := by
      calc
        _ ≤ ‖ν‖ * ‖reaction q₀.1 q₀.2 (u q₀.1 q₀.2) -
            reaction q₀.1 q₀.2 p‖ := real_inner_le_norm _ _
        _ ≤ ‖ν‖ * ((L : Real) * ‖u q₀.1 q₀.2 - p‖) :=
          mul_le_mul_of_nonneg_left hLip (norm_nonneg ν)
        _ = (L : Real) * ‖ν‖ ^ 2 := by rw [show u q₀.1 q₀.2 - p = ν from rfl]; ring
    have hreaction :
        inner Real (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν ≤
          (L : Real) * ‖ν‖ ^ 2 := by
      rw [real_inner_comm] at hreactionp hinnerLip
      rw [inner_sub_left] at hinnerLip
      linarith
    have hstrict :
        Real.exp (-K * q₀.1) *
          (inner Real (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν - K * ‖ν‖ ^ 2) < 0 := by
      apply mul_neg_of_pos_of_neg (Real.exp_pos _)
      dsimp [K]
      nlinarith [sq_pos_of_pos hνpos]
    linarith
  intro t ht x
  rcases eq_or_lt_of_le ht.2 with htEq | htlt
  · by_cases hTzero : T = 0
    · have htzero : t = 0 := by rw [htEq, hTzero]
      simpa [htzero] using hinit x
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
      rw [htEq]
      have hcont := hsol.jointCont (T, x) ⟨⟨hT, le_rfl⟩, mem_univ x⟩
      have htend : Filter.Tendsto (fun s : Real ↦ u s x)
          (𝓝[<] T) (𝓝 (u T x)) := by
        have hpair : Filter.Tendsto (fun s : Real ↦ (s, x))
            (𝓝[<] T) (𝓝 (T, x)) := by
          refine Filter.Tendsto.prodMk_nhds ?_ tendsto_const_nhds
          exact nhdsWithin_le_nhds
        have hevent : ∀ᶠ s in 𝓝[<] T,
            (s, x) ∈ Set.Icc (0 : Real) T ×ˢ (Set.univ : Set M) := by
          have hpos : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
          have hpos' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds hpos
          filter_upwards [hpos', self_mem_nhdsWithin] with s hs hslt
          exact ⟨⟨le_of_lt hs, le_of_lt hslt⟩, Set.mem_univ x⟩
        have hpairWithin : Filter.Tendsto (fun s : Real ↦ (s, x))
            (𝓝[<] T) (𝓝[Set.Icc 0 T ×ˢ Set.univ] (T, x)) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨hpair, hevent⟩
        exact hcont.tendsto.comp hpairWithin
      apply hclosed.mem_of_tendsto htend
      have hpos : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
      have hpos' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds hpos
      filter_upwards [hpos', self_mem_nhdsWithin] with s hs hslt
      exact hIco s ⟨le_of_lt hs, hslt⟩ x
  · exact hIco t ⟨ht.1, htlt⟩ x

include completeF in
theorem closed_convex_heat_reaction_mem_of_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : Set F) (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex Real C)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (htangent : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p ∈ C,
      reaction t x p ∈ posTangentConeAt C p)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  apply closed_convex_heat_reaction_mem_of_supporting_normal
    (I := I) G hT C hne hclosed hconvex reaction u hsol L hL
  · intro t ht x p hp ν hnormal
    have hmax : IsMaxOn (fun q : F ↦ inner Real ν q) C p := by
      intro q hq
      change inner Real ν q ≤ inner Real ν p
      rw [← sub_nonpos]
      simpa [inner_sub_right] using hnormal q hq
    exact hmax.localize.hasFDerivWithinAt_nonpos
      (innerSL Real ν).hasFDerivAt.hasFDerivWithinAt (htangent t ht x p hp)
  · exact hinit

theorem properCone_heat_reaction_mem_of_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (htangent : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p ∈ C,
      reaction t x p ∈ posTangentConeAt (C : Set F) p)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C :=
  closed_convex_heat_reaction_mem_of_tangent
    (I := I) G hT C C.nonempty C.isClosed C.convex reaction u hsol L hL htangent hinit

include completeF in
theorem properCone_heat_reaction_mem_of_dualZeroFace_nonneg
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      ∀ φ : StrongDual Real F, ProperCone.IsDualElement C φ →
        ∀ p ∈ ProperCone.dualZeroFace C φ, 0 ≤ φ (reaction t x p))
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  apply closed_convex_heat_reaction_mem_of_supporting_normal
    (I := I) G hT C C.nonempty C.isClosed C.convex reaction u hsol L hL
  · intro t ht x p hp ν hnormal
    let φ : StrongDual Real F := -(innerSL Real ν)
    have hνp_nonneg : 0 ≤ inner Real ν p := by
      have h := hnormal 0 C.zero_mem
      simpa using h
    have hνp_nonpos : inner Real ν p ≤ 0 := by
      have h2p : (2 : Real) • p ∈ C := C.smul_mem hp (by norm_num)
      have h := hnormal ((2 : Real) • p) h2p
      simpa [two_smul] using h
    have hνp : inner Real ν p = 0 := le_antisymm hνp_nonpos hνp_nonneg
    have hφ : ProperCone.IsDualElement C φ := by
      intro q hq
      have h := hnormal q hq
      simp only [φ, ContinuousLinearMap.neg_apply, innerSL_apply_apply]
      rw [inner_sub_right, hνp] at h
      linarith
    have hpface : p ∈ ProperCone.dualZeroFace C φ := by
      rw [ProperCone.mem_dualZeroFace]
      refine ⟨hp, ?_⟩
      simp [φ, hνp]
    have h := hreaction t ht x φ hφ p hpface
    simpa [φ] using h
  · exact hinit

theorem properCone_heat_reaction_mem_of_mapsTo
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      MapsTo (reaction t x) C C)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  apply properCone_heat_reaction_mem_of_tangent
    (I := I) G hT C reaction u hsol L hL
  · intro t ht x p hp
    have htan := sub_mem_posTangentConeAt_of_segment_subset
      (C.convex.segment_subset hp (C.add_mem hp (hreaction t ht x hp)))
    simpa using htan
  · exact hinit

end

end DifferentialGeometry.Analysis.Parabolic
