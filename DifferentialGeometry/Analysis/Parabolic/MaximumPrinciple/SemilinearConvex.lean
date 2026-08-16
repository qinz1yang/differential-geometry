import DifferentialGeometry.Analysis.ODE.Nagumo
import DifferentialGeometry.Analysis.Convex.ProperConeFace
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ProperCone
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

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

lemma mem_closed_convex_iff_forall_exists_inner_le
    {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    {C : Set F} (hclosed : IsClosed C) (hconvex : Convex Real C) (p : F) :
    p ∈ C ↔ ∀ ν : F, ∃ q ∈ C, inner ℝ ν p ≤ inner ℝ ν q := by
  constructor
  · intro hp ν
    exact ⟨p, hp, le_rfl⟩
  · intro hp
    have hInter := iInter_halfSpaces_eq (E := F) (s := C) hconvex hclosed
    rw [← hInter]
    simp only [mem_iInter, mem_setOf_eq]
    intro l
    let ν : F := (InnerProductSpace.toDual ℝ F).symm l
    have hl : l = InnerProductSpace.toDual ℝ F ν := by
      dsimp [ν]
      simp
    rcases hp ν with ⟨q, hq, hle⟩
    refine ⟨q, hq, ?_⟩
    rw [hl]
    simpa [InnerProductSpace.toDual_apply_apply] using hle

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
theorem closed_convex_heat_reaction_mem_of_timeDep_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : Real → Set F)
    (K : Set (WithLp 2 (F × ℝ)))
    (hK_eq : K = {q : WithLp 2 (F × ℝ) |
      (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp q).1 ∈ C (WithLp.ofLp q).2})
    (hKne : K.Nonempty) (hKclosed : IsClosed K) (hKconvex : Convex Real K)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (fun q : WithLp 2 (F × ℝ) =>
        WithLp.toLp 2 (reaction (WithLp.ofLp q).2 x (WithLp.ofLp q).1, (1 : Real))))
    (htangent : ∀ τ : Real, τ ∈ Set.Ico 0 T → ∀ x : M, ∀ p : F, p ∈ C τ →
      (WithLp.toLp 2 (reaction τ x p, (1 : Real))) ∈ posTangentConeAt K
        (WithLp.toLp 2 (p, τ)))
    (htangent_fiber : ∀ τ : Real, τ ∈ Set.Icc 0 T → ∀ x : M, ∀ p : F, p ∈ C τ →
      reaction τ x p ∈ posTangentConeAt (C τ) p)
    (hinit : ∀ x : M, u 0 x ∈ C 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t := by
  classical
  let F' : Type _ := WithLp 2 (F × ℝ)
  let u' : Real → M → F' := fun t x => WithLp.toLp 2 (u t x, t)
  let reac' : Real → M → F' → F' := fun _t x q =>
    WithLp.toLp 2 (reaction (WithLp.ofLp q).2 x (WithLp.ofLp q).1, (1 : Real))
  have hsol' : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reac' u' := by
    refine ⟨?_, ?_, ?_⟩
    · have hcont : ContinuousOn (fun q : Real × M => u q.1 q.2)
          ((RealTimeInterval.closed 0 T hT).carrier ×ˢ (Set.univ : Set M)) := hsol.jointCont
      have htime : ContinuousOn (fun q : Real × M => q.1)
          ((RealTimeInterval.closed 0 T hT).carrier ×ˢ (Set.univ : Set M)) := continuous_fst.continuousOn
      have hprod : ContinuousOn (fun q : Real × M => (u q.1 q.2, q.1))
          ((RealTimeInterval.closed 0 T hT).carrier ×ˢ (Set.univ : Set M)) := hcont.prodMk htime
      exact (WithLp.prod_continuous_toLp (p := 2) (α := F) (β := ℝ)).comp_continuousOn' hprod
    · intro y t ht
      have h1 : ContMDiff I 𝓘(Real, Real) ∞ (innerScalarization u (WithLp.ofLp y).1 t) :=
        hsol.scalarSliceSmooth (WithLp.ofLp y).1 t ht
      have hconst : ContMDiff I 𝓘(Real, Real) ∞ (fun _x : M => (WithLp.ofLp y).2 * t) := contMDiff_const
      have hsum := h1.add hconst
      change ContMDiff I 𝓘(Real, Real) ∞ (fun x : M => inner ℝ (u' t x) y)
      have hfun : (fun x : M => inner ℝ (u' t x) y) =
          fun x : M => innerScalarization u (WithLp.ofLp y).1 t x + (WithLp.ofLp y).2 * t := by
        funext x
        have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := by
          intro a b
          rw [mul_comm]
          rfl
        rw [real_inner_comm, WithLp.prod_inner_apply]
        simp only [u']
        simp [innerScalarization, real_inner_comm, hreal]
      rw [hfun]
      exact hsum
    · intro y t ht x
      have h1 := hsol.equation (WithLp.ofLp y).1 t ht x
      have hid : HasDerivAt (fun s : Real => (WithLp.ofLp y).2 * s) (WithLp.ofLp y).2 t := by
        simpa using (hasDerivAt_id t).const_mul (WithLp.ofLp y).2
      have hsum := h1.add hid
      have hfun : (fun s : Real => innerScalarization u (WithLp.ofLp y).1 s x + (WithLp.ofLp y).2 * s) =
          fun s : Real => inner ℝ (u' s x) y := by
        funext s
        have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := by
          intro a b
          rw [mul_comm]
          rfl
        rw [real_inner_comm, WithLp.prod_inner_apply]
        simp only [u']
        simp [innerScalarization, real_inner_comm, hreal]
      have htarget :
          laplacianAt (I := I) G t (innerScalarization u (WithLp.ofLp y).1 t) x +
              inner ℝ (reaction t x (u t x)) (WithLp.ofLp y).1 + (WithLp.ofLp y).2 =
            laplacianAt (I := I) G t (fun x : M => inner ℝ (u' t x) y) x +
              inner ℝ (reac' t x (u' t x)) y := by
        have hlapl : laplacianAt (I := I) G t (fun x : M => inner ℝ (u' t x) y) x =
            laplacianAt (I := I) G t (innerScalarization u (WithLp.ofLp y).1 t) x := by
          have hfunx : (fun x : M => inner ℝ (u' t x) y) =
              fun x : M => innerScalarization u (WithLp.ofLp y).1 t x + (WithLp.ofLp y).2 * t := by
            funext x
            have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := by
              intro a b
              rw [mul_comm]
              rfl
            rw [real_inner_comm, WithLp.prod_inner_apply]
            simp only [u']
            simp [innerScalarization, real_inner_comm, hreal]
          rw [hfunx]
          have hconst : ContMDiff I 𝓘(Real, Real) ∞ (fun _ : M => (WithLp.ofLp y).2 * t) := contMDiff_const
          have hsum_lap := laplacianAt_add (I := I) G (t := t)
            (f := innerScalarization u (WithLp.ofLp y).1 t)
            (h := fun _ : M => (WithLp.ofLp y).2 * t) (x := x)
            ((hsol.scalarSliceSmooth (WithLp.ofLp y).1 t ((RealTimeInterval.closed 0 T hT).regular_subset ht)).mdifferentiable (by simp))
            (hconst.mdifferentiable (by simp))
            (gradientFun_mdiffAt (I := I) (G.metric t) (hsol.scalarSliceSmooth (WithLp.ofLp y).1 t ((RealTimeInterval.closed 0 T hT).regular_subset ht)) x)
            (gradientFun_mdiffAt (I := I) (G.metric t) hconst x)
          have hconst_lap : laplacianAt (I := I) G t (fun _ : M => (WithLp.ofLp y).2 * t) x = 0 := by
            change laplacian (I := I) (G.connection t) (G.metric t)
                (fun _ : M => (WithLp.ofLp y).2 * t) x = 0
            exact laplacian_const (I := I) (G.connection t) (G.metric t) ((WithLp.ofLp y).2 * t) x
          rw [hconst_lap] at hsum_lap
          simpa using hsum_lap
        rw [hlapl]
        rw [real_inner_comm, WithLp.prod_inner_apply]
        simp only [u', reac']
        have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := by
          intro a b
          rw [mul_comm]
          rfl
        simp [real_inner_comm, hreal]
        ring
      change HasDerivAt (fun s : Real => inner ℝ (u' s x) y)
        (laplacianAt (I := I) G t (fun x : M => inner ℝ (u' t x) y) x +
          inner ℝ (reac' t x (u' t x)) y) t
      rw [← hfun]
      rw [← htarget]
      exact hsum
  have hL' : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reac' t x) := by
    intro t ht x
    simpa [reac'] using hL t ht x
  have hIco : ∀ t : Real, t ∈ Set.Ico 0 T → ∀ x : M, u' t x ∈ K := by
    intro t ht x
    by_contra hout
    have htpos : 0 < t := by
      by_contra htzero
      have : t = 0 := le_antisymm (not_lt.mp htzero) ht.1
      exact hout (by
        rw [hK_eq]
        constructor
        · constructor
          · have h0 : 0 ≤ (u' t x).ofLp.2 := by simp [u', this]
            exact h0
          · have hT' : (u' t x).ofLp.2 ≤ T := by simpa [u', this] using hT
            exact hT'
        · simpa [u', this] using hinit x)
    let KK : Real := (L : Real) + 1
    let d : Real × M → Real := fun q ↦
      Real.exp (-KK * q.1) * Metric.infDist (u' q.1 q.2) K
    let Q : Set (Real × M) := Set.Icc 0 t ×ˢ (Set.univ : Set M)
    have hQcompact : IsCompact Q :=
      (isCompact_Icc (a := (0 : Real)) (b := t)).prod CompactSpace.isCompact_univ
    have hQne : Q.Nonempty :=
      ⟨(0, x), Set.mk_mem_prod ⟨le_rfl, htpos.le⟩ (Set.mem_univ x)⟩
    have hQsub : Q ⊆ (RealTimeInterval.closed 0 T hT).carrier ×ˢ univ := by
      intro q hq
      exact ⟨⟨hq.1.1, hq.1.2.trans ht.2.le⟩, hq.2⟩
    have hdcont : ContinuousOn d Q := by
      have hexp : Continuous (fun q : Real × M ↦ Real.exp (-KK * q.1)) := by
        fun_prop
      have hinf : ContinuousOn (fun q : Real × M => Metric.infDist (u' q.1 q.2) K) Q := by
        have hcont : ContinuousOn (fun q : Real × M => u' q.1 q.2) Q :=
          hsol'.jointCont.mono hQsub
        exact (Metric.continuous_infDist_pt K).comp_continuousOn hcont
      exact hexp.continuousOn.mul hinf
    obtain ⟨q₀, hq₀Q, hq₀max⟩ := hQcompact.exists_isMaxOn hQne hdcont
    have hdtxpos : 0 < d (t, x) := by
      apply mul_pos (Real.exp_pos _)
      exact (hKclosed.notMem_iff_infDist_pos hKne).mp hout
    have hdq₀pos : 0 < d q₀ := lt_of_lt_of_le hdtxpos (hq₀max ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩)
    have hq₀tpos : 0 < q₀.1 := by
      by_contra hnonpos
      have hzero : q₀.1 = 0 := le_antisymm (not_lt.mp hnonpos) hq₀Q.1.1
      have : d q₀ = 0 := by
        have hinit' : u' 0 q₀.2 ∈ K := by
          rw [hK_eq]
          exact ⟨⟨le_rfl, hT⟩, by simpa [u'] using hinit q₀.2⟩
        simp [d, hzero, Metric.infDist_zero_of_mem hinit']
      linarith
    have hq₀reg : q₀.1 ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change q₀.1 ∈ Set.Ioo 0 T
      exact ⟨hq₀tpos, lt_of_le_of_lt hq₀Q.1.2 ht.2⟩
    obtain ⟨p, hpK, hpmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex hKne hKclosed.isComplete hKconvex (u' q₀.1 q₀.2)
    let ν' : F' := u' q₀.1 q₀.2 - p
    have hdist₀ : Metric.infDist (u' q₀.1 q₀.2) K = ‖ν'‖ := by
      rw [Metric.infDist_eq_iInf]
      rw [show ν' = u' q₀.1 q₀.2 - p from rfl]
      rw [show (fun z : K => dist (u' q₀.1 q₀.2) ↑z) = fun z : K => ‖u' q₀.1 q₀.2 - ↑z‖ by
        funext z
        exact dist_eq_norm _ _]
      rw [hpmin]
    have hνpos : 0 < ‖ν'‖ := by
      have : 0 < Metric.infDist (u' q₀.1 q₀.2) K := by
        exact (mul_pos_iff_of_pos_left (Real.exp_pos (-KK * q₀.1))).mp
          (by simpa [d] using hdq₀pos)
      simpa [hdist₀] using this
    have hnormal : ∀ q ∈ K, inner ℝ ν' (q - p) ≤ 0 := by
      exact (norm_eq_iInf_iff_real_inner_le_zero hKconvex hpK).mp hpmin
    have hsupport : ∀ s : Real, ∀ y : M,
        inner ℝ (u' s y - p) ν' ≤ Metric.infDist (u' s y) K * ‖ν'‖ := by
      intro s y
      obtain ⟨q, hqK, hqmin⟩ :=
        exists_norm_eq_iInf_of_complete_convex hKne hKclosed.isComplete hKconvex (u' s y)
      have hqdist : ‖u' s y - q‖ = Metric.infDist (u' s y) K := by
        rw [Metric.infDist_eq_iInf]
        rw [show (fun z : K => dist (u' s y) ↑z) = fun z : K => ‖u' s y - ↑z‖ by
          funext z
          exact dist_eq_norm _ _]
        rw [← hqmin]
      calc
        inner ℝ (u' s y - p) ν' =
            inner ℝ (u' s y - q) ν' + inner ℝ (q - p) ν' := by
          rw [← inner_add_left]
          congr 2
          abel
        _ ≤ ‖u' s y - q‖ * ‖ν'‖ + 0 :=
          add_le_add (real_inner_le_norm _ _) (by simpa [real_inner_comm] using hnormal q hqK)
        _ = Metric.infDist (u' s y) K * ‖ν'‖ := by rw [hqdist, add_zero]
    let z : Real → M → Real := fun s y ↦
      Real.exp (-KK * s) * inner ℝ (u' s y - p) ν'
    have hzmax : ∀ r ∈ Q, z r.1 r.2 ≤ z q₀.1 q₀.2 := by
      intro r hr
      have hleft := mul_le_mul_of_nonneg_left (hsupport r.1 r.2)
        (Real.exp_pos (-KK * r.1)).le
      have hright := mul_le_mul_of_nonneg_right (hq₀max hr) (norm_nonneg ν')
      have hz₀ : z q₀.1 q₀.2 = d q₀ * ‖ν'‖ := by
        simp only [z, d, ν', real_inner_self_eq_norm_sq, hdist₀]
        ring
      calc
        z r.1 r.2 ≤ Real.exp (-KK * r.1) *
            (Metric.infDist (u' r.1 r.2) K * ‖ν'‖) := hleft
        _ = d r * ‖ν'‖ := by simp only [d]; ring
        _ ≤ d q₀ * ‖ν'‖ := hright
        _ = z q₀.1 q₀.2 := hz₀.symm
    have hzspatial : IsLocalMax (z q₀.1) q₀.2 := by
      exact Filter.Eventually.of_forall (fun y ↦
        hzmax (q₀.1, y) ⟨hq₀Q.1, mem_univ y⟩)
    have hq₀carrier : q₀.1 ∈ (RealTimeInterval.closed 0 T hT).carrier :=
      (RealTimeInterval.closed 0 T hT).regular_subset hq₀reg
    have hzslice : ContMDiff I 𝓘(Real, Real) ∞ (z q₀.1) := by
      simpa only [z, innerScalarization, inner_sub_left] using
        contMDiff_const.mul
          ((hsol'.scalarSliceSmooth ν' q₀.1 hq₀carrier).sub contMDiff_const)
    have hzlap : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 ≤ 0 :=
      laplacianAt_nonpos_at_spatial_max (I := I) G q₀.1 hzspatial hzslice
    have hztimeMax : IsMaxOn (fun s ↦ z s q₀.2) (Set.Icc 0 q₀.1) q₀.1 := by
      intro s hs
      exact hzmax (s, q₀.2) ⟨⟨hs.1, hs.2.trans hq₀Q.1.2⟩, mem_univ q₀.2⟩
    have hscalarEq := hsol'.equation ν' q₀.1 hq₀reg q₀.2
    have hexpDeriv : HasDerivAt (fun s : Real ↦ Real.exp (-KK * s))
        (Real.exp (-KK * q₀.1) * (-KK)) q₀.1 := by
      have hinner : HasDerivAt (fun s : Real ↦ -KK * s) (-KK) q₀.1 := by
        simpa using (hasDerivAt_id q₀.1).const_mul (-KK)
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_exp (-KK * q₀.1)).comp q₀.1 hinner
    have hzderiv : HasDerivAt (fun s ↦ z s q₀.2)
        (Real.exp (-KK * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (innerScalarization u' ν' q₀.1) q₀.2 +
              inner ℝ (reac' q₀.1 q₀.2 (u' q₀.1 q₀.2)) ν') -
          KK * Real.exp (-KK * q₀.1) * inner ℝ (u' q₀.1 q₀.2 - p) ν') q₀.1 := by
      convert hexpDeriv.mul (hscalarEq.sub_const (inner ℝ p ν')) using 1
      · funext s
        simp only [z, innerScalarization, inner_sub_left, Pi.mul_apply]
      · simp only [innerScalarization, inner_sub_left]
        ring
    have hztime : 0 ≤
        Real.exp (-KK * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (innerScalarization u' ν' q₀.1) q₀.2 +
              inner ℝ (reac' q₀.1 q₀.2 (u' q₀.1 q₀.2)) ν') -
          KK * Real.exp (-KK * q₀.1) * inner ℝ (u' q₀.1 q₀.2 - p) ν' :=
      deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc hq₀tpos hztimeMax hzderiv
    have hscalarSmooth := hsol'.scalarSliceSmooth ν' q₀.1 hq₀carrier
    have hscalarMDiff : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real) (innerScalarization u' ν' q₀.1) y :=
      fun y ↦ hscalarSmooth.mdifferentiable (by simp) y
    have hzlapEq : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 =
        Real.exp (-KK * q₀.1) *
          laplacianAt (I := I) G q₀.1 (innerScalarization u' ν' q₀.1) q₀.2 := by
      have hsub : laplacianAt (I := I) G q₀.1
          (fun y : M ↦ innerScalarization u' ν' q₀.1 y - inner ℝ p ν') q₀.2 =
          laplacianAt (I := I) G q₀.1 (innerScalarization u' ν' q₀.1) q₀.2 := by
        exact laplacian_sub_const (I := I) (G.connection q₀.1) (G.metric q₀.1)
          (inner ℝ p ν') hscalarMDiff q₀.2
      have hsubSmooth : ContMDiff I 𝓘(Real, Real) ∞
          (fun y : M ↦ innerScalarization u' ν' q₀.1 y - inner ℝ p ν') :=
        hscalarSmooth.sub contMDiff_const
      have hsmul := laplacianAt_smul (I := I) G q₀.1
        (Real.exp (-KK * q₀.1))
        (fun y ↦ hsubSmooth.mdifferentiable (by simp) y)
        (gradientFun_mdiffAt (I := I) (G.metric q₀.1) hsubSmooth q₀.2)
      have hfun : z q₀.1 = Real.exp (-KK * q₀.1) •
          (fun y : M ↦ innerScalarization u' ν' q₀.1 y - inner ℝ p ν') := by
        funext y
        dsimp [z, innerScalarization]
        congr 1
        rw [inner_sub_left]
        rw [real_inner_comm]
        rfl
      rw [hfun, hsmul, hsub]
    have hparabolicNonneg : 0 ≤
        Real.exp (-KK * q₀.1) *
          (inner ℝ (reac' q₀.1 q₀.2 (u' q₀.1 q₀.2)) ν' - KK * ‖ν'‖ ^ 2) := by
      rw [hzlapEq] at hzlap
      rw [show u' q₀.1 q₀.2 - p = ν' from rfl,
        real_inner_self_eq_norm_sq] at hztime
      nlinarith [Real.exp_pos (-KK * q₀.1)]
    have hpK' : (WithLp.ofLp p).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp p).1 ∈ C (WithLp.ofLp p).2 := by
      rw [hK_eq] at hpK
      exact hpK
    have hreactionp : inner ℝ ν' (reac' q₀.1 q₀.2 p) ≤ 0 := by
      have hmax : IsMaxOn (fun q : F' ↦ inner ℝ ν' q) K p := by
        intro q hq
        change inner ℝ ν' q ≤ inner ℝ ν' p
        rw [← sub_nonpos]
        simpa [inner_sub_right] using hnormal q hq
      by_cases hp2lt : (WithLp.ofLp p).2 < T
      · have htau : (WithLp.ofLp p).2 ∈ Set.Ico 0 T := ⟨hpK'.1.1, hp2lt⟩
        have htan := htangent (WithLp.ofLp p).2 htau q₀.2 (WithLp.ofLp p).1 hpK'.2
        have hcone : reac' q₀.1 q₀.2 p ∈ posTangentConeAt K p := by
          simpa [reac', WithLp.toLp_ofLp] using htan
        exact hmax.localize.hasFDerivWithinAt_nonpos
          (innerSL ℝ ν').hasFDerivAt.hasFDerivWithinAt hcone
      · have hp2eq : (WithLp.ofLp p).2 = T := le_antisymm hpK'.1.2 (le_of_not_gt hp2lt)
        have hν2 : (WithLp.ofLp ν').2 = q₀.1 - T := by
          dsimp [ν']
          change (WithLp.ofLp (u' q₀.1 q₀.2 - p)).2 = q₀.1 - T
          have h2 : (WithLp.ofLp (u' q₀.1 q₀.2 - p)).2 = q₀.1 - (WithLp.ofLp p).2 := by
            rw [WithLp.ofLp_sub]
            simp [u']
          rw [h2, hp2eq]
        have hmaxf : IsMaxOn (fun q : F ↦ inner ℝ (WithLp.ofLp ν').1 q) (C T) (WithLp.ofLp p).1 := by
          intro q hq
          have hqK : WithLp.toLp 2 (q, T) ∈ K := by
            rw [hK_eq]
            constructor
            · change T ∈ Set.Icc 0 T
              exact ⟨hT, le_rfl⟩
            · simpa [hp2eq] using hq
          change inner ℝ (WithLp.ofLp ν').1 q ≤ inner ℝ (WithLp.ofLp ν').1 (WithLp.ofLp p).1
          have hq' := hnormal (WithLp.toLp 2 (q, T)) hqK
          have hsub : WithLp.toLp 2 (q, T) - p =
              WithLp.toLp 2 (q - (WithLp.ofLp p).1, T - (WithLp.ofLp p).2) := by
            rw [← WithLp.ofLp_toLp 2 (WithLp.toLp 2 (q, T) - p)]
            congr 1
          rw [hsub] at hq'
          rw [WithLp.prod_inner_apply] at hq'
          rw [hp2eq] at hq'
          have hq'' : inner ℝ (WithLp.ofLp ν').1 (q - (WithLp.ofLp p).1) ≤ 0 := by
            have hq''' : inner ℝ (WithLp.ofLp ν').1 (q - (WithLp.ofLp p).1) +
                (WithLp.ofLp ν').2 * (T - T) ≤ 0 := by
              simpa [hp2eq] using hq'
            linarith
          change inner ℝ (WithLp.ofLp ν').1 q ≤ inner ℝ (WithLp.ofLp ν').1 (WithLp.ofLp p).1
          have hq''' : inner ℝ (WithLp.ofLp ν').1 q - inner ℝ (WithLp.ofLp ν').1 (WithLp.ofLp p).1 ≤ 0 := by
            have hx := hq''
            rw [inner_sub_right] at hx
            exact hx
          exact sub_nonpos.mp hq'''
        have hp1 : (WithLp.ofLp p).1 ∈ C T := by
          have h := hpK'.2
          rw [hp2eq] at h
          exact h
        have htanf := htangent_fiber T ⟨hT, le_rfl⟩ q₀.2 (WithLp.ofLp p).1 hp1
        have hreacf : inner ℝ (WithLp.ofLp ν').1 (reaction T q₀.2 (WithLp.ofLp p).1) ≤ 0 :=
          hmaxf.localize.hasFDerivWithinAt_nonpos
            (innerSL ℝ (WithLp.ofLp ν').1).hasFDerivAt.hasFDerivWithinAt htanf
        have hmain : inner ℝ ν' (reac' q₀.1 q₀.2 p) ≤ 0 := by
          dsimp [reac']
          rw [WithLp.prod_inner_apply]
          have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := by
            intro a b
            rw [mul_comm]
            rfl
          rw [hreal]
          change inner ℝ (WithLp.ofLp ν').1 (reaction (WithLp.ofLp p).2 q₀.2 (WithLp.ofLp p).1) +
              (WithLp.ofLp ν').2 * 1 ≤ 0
          rw [hp2eq]
          have hq0lt : q₀.1 - T < 0 := sub_neg.mpr hq₀reg.2
          nlinarith [hreacf, hν2, hq0lt]
        exact hmain
    have hLip := (hL' q₀.1 hq₀reg q₀.2).norm_sub_le
      (u' q₀.1 q₀.2) p
    have hinnerLip : inner ℝ ν'
        (reac' q₀.1 q₀.2 (u' q₀.1 q₀.2) - reac' q₀.1 q₀.2 p) ≤
          (L : Real) * ‖ν'‖ ^ 2 := by
      calc
        _ ≤ ‖ν'‖ * ‖reac' q₀.1 q₀.2 (u' q₀.1 q₀.2) -
            reac' q₀.1 q₀.2 p‖ := real_inner_le_norm _ _
        _ ≤ ‖ν'‖ * ((L : Real) * ‖u' q₀.1 q₀.2 - p‖) :=
          mul_le_mul_of_nonneg_left hLip (norm_nonneg ν')
        _ = (L : Real) * ‖ν'‖ ^ 2 := by rw [show u' q₀.1 q₀.2 - p = ν' from rfl]; ring
    have hreaction :
        inner ℝ (reac' q₀.1 q₀.2 (u' q₀.1 q₀.2)) ν' ≤
          (L : Real) * ‖ν'‖ ^ 2 := by
      rw [real_inner_comm] at hreactionp hinnerLip
      rw [inner_sub_left] at hinnerLip
      linarith
    have hstrict :
        Real.exp (-KK * q₀.1) *
          (inner ℝ (reac' q₀.1 q₀.2 (u' q₀.1 q₀.2)) ν' - KK * ‖ν'‖ ^ 2) < 0 := by
      apply mul_neg_of_pos_of_neg (Real.exp_pos _)
      dsimp [KK]
      nlinarith [sq_pos_of_pos hνpos]
    linarith
  intro t ht x
  rcases eq_or_lt_of_le ht.2 with htEq | htlt
  · by_cases hTzero : T = 0
    · have htzero : t = 0 := by rw [htEq, hTzero]
      simpa [htzero] using hinit x
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
      rw [htEq]
      have hcont := hsol'.jointCont (T, x) ⟨⟨hT, le_rfl⟩, mem_univ x⟩
      have htend : Filter.Tendsto (fun s : Real ↦ u' s x)
          (𝓝[<] T) (𝓝 (u' T x)) := by
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
      have hmemK : u' T x ∈ K := by
        apply hKclosed.mem_of_tendsto htend
        have hpos : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
        have hpos' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds hpos
        filter_upwards [hpos', self_mem_nhdsWithin] with s hs hslt
        exact hIco s ⟨le_of_lt hs, hslt⟩ x
      rw [hK_eq] at hmemK
      exact hmemK.2
  · have hmemK := hIco t ⟨ht.1, htlt⟩ x
    rw [hK_eq] at hmemK
    exact hmemK.2

theorem timeDepHalfspace_heat_reaction_mem_of_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (ν : F) (hν : ν ≠ 0) (s : Real → Real)
    (hsdiff : ∀ t : Real, t ∈ Set.Icc 0 T →
      DifferentiableWithinAt Real s (Set.Icc 0 T) t)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (htangent : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F,
      inner ℝ ν p = s t →
        inner ℝ ν (reaction t x p) ≤
          derivWithin s (Set.Icc 0 T) t)
    (hinit : ∀ x : M, inner ℝ ν (u 0 x) ≤ s 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, inner ℝ ν (u t x) ≤ s t := by
  classical
  let c : Real → Real := fun t => s t / ‖ν‖ ^ 2
  let v : Real → M → F := fun t x => u t x - c t • ν
  let reac' : Real → M → F → F := fun t x p =>
    reaction t x (p + c t • ν) - (derivWithin s (Set.Icc 0 T) t / ‖ν‖ ^ 2) • ν
  have hnorm_ne : ‖ν‖ ≠ 0 := norm_ne_zero_iff.mpr hν
  have hnorm2_ne : ‖ν‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm_ne
  have hsol' : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reac' v := by
    refine ⟨?_, ?_, ?_⟩
    · have hc_cont : ContinuousOn c (Set.Icc 0 T) := by
        intro t ht
        exact (hsdiff t ht).continuousWithinAt.div_const (‖ν‖ ^ 2)
      have hc_cont' : ContinuousOn (fun q : Real × M => c q.1)
          ((RealTimeInterval.closed 0 T hT).carrier ×ˢ (Set.univ : Set M)) :=
        hc_cont.comp continuous_fst.continuousOn (by intro q hq; exact hq.1)
      have hsmul_cont : Continuous fun r : Real => r • ν :=
        continuous_id.smul continuous_const
      have hconst_smul : ContinuousOn (fun q : Real × M => c q.1 • ν)
          ((RealTimeInterval.closed 0 T hT).carrier ×ˢ (Set.univ : Set M)) :=
        hsmul_cont.comp_continuousOn hc_cont'
      have hsub : ContinuousOn (fun q : Real × M => u q.1 q.2 - c q.1 • ν)
          ((RealTimeInterval.closed 0 T hT).carrier ×ˢ (Set.univ : Set M)) :=
        hsol.jointCont.sub hconst_smul
      simpa [v, sub_eq_add_neg] using hsub
    · intro y t ht
      have h1 := hsol.scalarSliceSmooth y t ht
      have hconst : ContMDiff I 𝓘(Real, Real) ∞
          (fun _x : M => c t * inner ℝ ν y) := contMDiff_const
      change ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => inner ℝ (u t x - (s t / ‖ν‖ ^ 2) • ν) y)
      simpa [c, innerScalarization, inner_sub_left, real_inner_smul_left]
        using h1.sub hconst
    · intro y t ht x
      have htIcc : t ∈ Set.Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hsdw : HasDerivWithinAt s (derivWithin s (Set.Icc 0 T) t) (Set.Icc 0 T) t :=
        (hsdiff t htIcc).hasDerivWithinAt
      have hsd : HasDerivAt s (derivWithin s (Set.Icc 0 T) t) t :=
        hsdw.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      have hcd : HasDerivAt (fun r : Real => c r) (derivWithin s (Set.Icc 0 T) t / ‖ν‖ ^ 2) t := by
        simpa [c] using hsd.div_const (‖ν‖ ^ 2)
      have hB : HasDerivAt (fun r : Real => c r * inner ℝ ν y)
          ((derivWithin s (Set.Icc 0 T) t / ‖ν‖ ^ 2) * inner ℝ ν y) t :=
        hcd.mul_const (inner ℝ ν y)
      have hA := hsol.equation y t ht x
      have hAB : HasDerivAt (fun r : Real =>
          innerScalarization u y r x - c r * inner ℝ ν y)
          (laplacianAt (I := I) G t (innerScalarization u y t) x +
              inner ℝ (reaction t x (u t x)) y -
            (derivWithin s (Set.Icc 0 T) t / ‖ν‖ ^ 2) * inner ℝ ν y) t := by
        simpa [innerScalarization] using hA.sub hB
      have hfun : (fun r : Real => innerScalarization v y r x) =
          fun r : Real => innerScalarization u y r x - c r * inner ℝ ν y := by
        funext r
        simp [v, c, innerScalarization, inner_sub_left, real_inner_smul_left]
      have hlap_eq : laplacianAt (I := I) G t (innerScalarization v y t) x =
          laplacianAt (I := I) G t (innerScalarization u y t) x := by
        have hconst : ContMDiff I 𝓘(Real, Real) ∞
            (fun _x : M => c t * inner ℝ ν y) := contMDiff_const
        have hconst_mdiff : ∀ z : M,
            MDifferentiableAt I 𝓘(Real, Real) (fun _x : M => c t * inner ℝ ν y) z :=
          fun z => hconst.mdifferentiable (by simp) z
        have hlap_const : laplacianAt (I := I) G t
            (fun _x : M => c t * inner ℝ ν y) x = 0 := by
          change laplacian (I := I) (G.connection t) (G.metric t)
              (fun _x : M => c t * inner ℝ ν y) x = 0
          exact laplacian_const (I := I) (G.connection t) (G.metric t)
            (c t * inner ℝ ν y) x
        have hf_mdiff : ∀ z : M,
            MDifferentiableAt I 𝓘(Real, Real) (innerScalarization u y t) z :=
          fun z => (hsol.scalarSliceSmooth y t
            ((RealTimeInterval.closed 0 T hT).regular_subset ht)).mdifferentiable (by simp) z
        have hsub_lap := laplacian_sub_const (I := I) (G.connection t) (G.metric t)
          (f := innerScalarization u y t) (c := c t * inner ℝ ν y) hf_mdiff x
        have hfunx : innerScalarization v y t =
            innerScalarization u y t - fun _x : M => c t * inner ℝ ν y := by
          funext z
          simp [v, c, innerScalarization, inner_sub_left, real_inner_smul_left]
        rw [hfunx]
        change laplacian (G.connection t) (G.metric t)
            (fun y_1 : M => innerScalarization u y t y_1 - c t * inner ℝ ν y) x =
          laplacian (G.connection t) (G.metric t) (innerScalarization u y t) x
        rw [hsub_lap]
      have htarget : laplacianAt (I := I) G t (innerScalarization v y t) x +
          inner ℝ (reac' t x (v t x)) y =
          laplacianAt (I := I) G t (innerScalarization u y t) x +
            inner ℝ (reaction t x (u t x)) y -
            (derivWithin s (Set.Icc 0 T) t / ‖ν‖ ^ 2) * inner ℝ ν y := by
        rw [hlap_eq]
        have hv : v t x = u t x - c t • ν := rfl
        have hvadd : v t x + c t • ν = u t x := by
          rw [hv]
          abel
        have hinner_reac : inner ℝ (reac' t x (v t x)) y =
            inner ℝ (reaction t x (u t x)) y -
              (derivWithin s (Set.Icc 0 T) t / ‖ν‖ ^ 2) * inner ℝ ν y := by
          dsimp [reac']
          rw [hvadd]
          rw [inner_sub_left, real_inner_smul_left]
        rw [hinner_reac]
        ring
      rw [← hfun] at hAB
      convert hAB using 1
  let hC : Set F := {p | inner ℝ ν p ≤ 0}
  have hCne : hC.Nonempty := ⟨0, by simp [hC]⟩
  have hCclosed : IsClosed hC := isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hCconvex : Convex Real hC := by
    rw [convex_iff_forall_pos]
    intro p hp q hq a b ha hb hab
    change inner ℝ ν (a • p + b • q) ≤ 0
    have hxy : inner ℝ ν (a • p + b • q) = a * inner ℝ ν p + b * inner ℝ ν q := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [hxy]
    have hp' : inner ℝ ν p ≤ 0 := by simpa [hC] using hp
    have hq' : inner ℝ ν q ≤ 0 := by simpa [hC] using hq
    nlinarith [hp', hq']
  have hL' : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reac' t x) := by
    intro t ht x
    refine LipschitzWith.of_dist_le_mul ?_
    intro a b
    have h := (hL t ht x).dist_le_mul (a + c t • ν) (b + c t • ν)
    simpa [reac', dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      add_sub_assoc] using h
  have htan' : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F, p ∈ hC →
      reac' t x p ∈ posTangentConeAt hC p := by
    intro t ht x p hp
    by_cases hp_int : inner ℝ ν p < 0
    · let w : F := reac' t x p
      let δ : ℝ := (- inner ℝ ν p) / (2 * (|inner ℝ ν w| + 1))
      have hδ : 0 < δ := by
        have hnum : 0 < - inner ℝ ν p := neg_pos.mpr hp_int
        have hden : 0 < 2 * (|inner ℝ ν w| + 1) := by positivity
        dsimp [δ]
        exact div_pos hnum hden
      have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, p + r • w ∈ hC := by
        rw [eventually_nhdsWithin_iff]
        refine mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ) ?_
        intro r hr hrpos
        have hrlt : r < δ := hr.2
        change inner ℝ ν (p + r • w) ≤ 0
        rw [inner_add_right, real_inner_smul_right]
        have hle_abs : inner ℝ ν w ≤ |inner ℝ ν w| := le_abs_self _
        have h1 : r * inner ℝ ν w ≤ r * |inner ℝ ν w| :=
          mul_le_mul_of_nonneg_left hle_abs (le_of_lt hrpos)
        have habs_nonneg : 0 ≤ |inner ℝ ν w| := abs_nonneg _
        have hdenpos : 0 < |inner ℝ ν w| + 1 := by nlinarith
        have h2a : r * |inner ℝ ν w| ≤ r * (|inner ℝ ν w| + 1) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (le_of_lt hrpos)
        have h2 : r * |inner ℝ ν w| < δ * (|inner ℝ ν w| + 1) :=
          lt_of_le_of_lt h2a (mul_lt_mul_of_pos_right hrlt hdenpos)
        have hδeq : δ * (|inner ℝ ν w| + 1) = (- inner ℝ ν p) / 2 := by
          dsimp [δ]
          field_simp
        have hneg : inner ℝ ν p + r * inner ℝ ν w < 0 := by
          nlinarith [hp_int, h1, h2, hδeq]
        exact le_of_lt hneg
      exact mem_posTangentConeAt_of_frequently_mem (Eventually.frequently hev)
    · have hp' : inner ℝ ν p ≤ 0 := by simpa [hC] using hp
      have hp0 : inner ℝ ν p = 0 := by
        exact le_antisymm hp' (le_of_not_gt hp_int)
      let q : F := p + c t • ν
      have hq_eq : inner ℝ ν q = s t := by
        dsimp [q, c]
        rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hp0, zero_add]
        field_simp [hnorm2_ne]
      have hreac_le := htangent t ht x q hq_eq
      have hw : inner ℝ ν (reac' t x p) ≤ 0 := by
        dsimp [reac']
        rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        dsimp [q] at hq_eq hreac_le
        field_simp [hnorm2_ne]
        nlinarith
      have hpw : p + reac' t x p ∈ hC := by
        change inner ℝ ν (p + reac' t x p) ≤ 0
        rw [inner_add_right]
        nlinarith [hw]
      have hseg : openSegment ℝ p (p + reac' t x p) ⊆ hC :=
        hCconvex.openSegment_subset hp hpw
      simpa using (sub_mem_posTangentConeAt_of_openSegment_subset hseg)
  have hinit' : ∀ x : M, v 0 x ∈ hC := by
    intro x
    have hsmul : inner ℝ ν ((s 0 / ‖ν‖ ^ 2) • ν) = s 0 := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hnorm2_ne]
    have hv : inner ℝ ν (u 0 x - (s 0 / ‖ν‖ ^ 2) • ν) ≤ 0 := by
      rw [inner_sub_right, hsmul]
      linarith [hinit x]
    change v 0 x ∈ hC
    change inner ℝ ν (u 0 x - (s 0 / ‖ν‖ ^ 2) • ν) ≤ 0
    exact hv
  have hmain := closed_convex_heat_reaction_mem_of_tangent
    (I := I) (M := M) G hT hC hCne hCclosed hCconvex reac' v hsol' L hL' htan' hinit'
  intro t ht x
  have hv : v t x ∈ hC := hmain t ht x
  change inner ℝ ν (u t x - (s t / ‖ν‖ ^ 2) • ν) ≤ 0 at hv
  have hv' : inner ℝ ν (u t x) - inner ℝ ν ((s t / ‖ν‖ ^ 2) • ν) ≤ 0 := by
    simpa [inner_sub_right] using hv
  have hsmul : inner ℝ ν ((s t / ‖ν‖ ^ 2) • ν) = s t := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hnorm2_ne]
  linarith


theorem closed_convex_timeDep_heat_reaction_mem_of_supporting_normal
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : Real → Set F)
    (support : Real → F → Real)
    (hsupp : ∀ t : Real, ∀ p : F, p ∈ C t ↔ ∀ ν : F, inner ℝ ν p ≤ support t ν)
    (h0 : ∀ t : Real, support t 0 = 0)
    (hsdiff : ∀ ν : F, ∀ t : Real, t ∈ Set.Icc 0 T →
      DifferentiableWithinAt Real (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F,
      ∀ ν : F, ν ≠ 0 → inner ℝ ν p = support t ν →
        inner ℝ ν (reaction t x p) ≤
          derivWithin (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hinit : ∀ x : M, u 0 x ∈ C 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t := by
  intro t ht x
  rw [hsupp]
  intro ν
  by_cases hν : ν = 0
  · subst ν
    simp [h0]
  · have hνne : ν ≠ 0 := hν
    have hinitν : ∀ y : M, inner ℝ ν (u 0 y) ≤ support 0 ν := by
      intro y
      have hu0 : u 0 y ∈ C 0 := hinit y
      exact (hsupp 0 (u 0 y)).1 hu0 ν
    exact timeDepHalfspace_heat_reaction_mem_of_tangent
      (I := I) (M := M) G hT ν hνne (fun s => support s ν) (hsdiff ν)
      reaction u hsol L hL
      (fun t ht x p hp_eq => hreaction t ht x p ν hνne hp_eq)
      hinitν t ht x


end

end DifferentialGeometry.Analysis.Parabolic
