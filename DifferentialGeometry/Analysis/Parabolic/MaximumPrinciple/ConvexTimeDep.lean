import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SemilinearConvex

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [CompleteSpace F]

def IsConvexSupportFamily (C : Real → Set F) (support : Real → F → Real) : Prop :=
  ∀ t p, p ∈ C t ↔ ∀ ν : F, inner ℝ ν p ≤ support t ν

include E in
omit [CompleteSpace F] in
theorem closed_convex_timeDep_heat_reaction_mem_of_support_family
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (C : Real → Set F) (support : Real → F → Real)
    (hsupp : IsConvexSupportFamily C support)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT.le) G reaction u)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      t ∈ (RealTimeInterval.closed 0 T hT.le).regular)
    (hsupport_cont : ∀ ν : F,
      ContinuousOn (fun t : Real => support t ν) (Set.Icc 0 T))
    (hsupport_time : ∀ ν : F, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      DifferentiableWithinAt Real (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F, ∀ ν : F,
      inner ℝ (reaction t x p) ν ≤ derivWithin (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hinit : ∀ x : M, u 0 x ∈ C 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t := by
  intro t ht x
  rw [hsupp]
  intro ν
  let uν : Real → M → Real := innerScalarization u ν
  let cν : Real → Real := fun s => support s ν
  let w : Real → M → Real := fun s y => cν s - uν s y
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have hlin : ContinuousOn (fun p : Real × M => cν p.1)
        (spacetimeSlab (M := M) T) := by
      refine (hsupport_cont ν).comp continuous_fst.continuousOn ?_
      intro p hp
      exact hp.1
    have hscalar_cont : ContinuousOn (fun p : Real × M => uν p.1 p.2)
        (spacetimeSlab (M := M) T) := by
      have hjoint := hsol.jointCont
      have hsub : spacetimeSlab (M := M) T ⊆
          (RealTimeInterval.closed 0 T hT.le).carrier ×ˢ (Set.univ : Set M) := by
        intro p hp
        exact ⟨hp.1, hp.2⟩
      have hcont := hjoint.mono hsub
      have hinner : ContinuousOn (fun p : Real × M => inner ℝ ν (u p.1 p.2))
          (spacetimeSlab (M := M) T) :=
        (innerSL ℝ ν).continuous.comp_continuousOn hcont
      have hinner' : ContinuousOn (fun p : Real × M => inner ℝ (u p.1 p.2) ν)
          (spacetimeSlab (M := M) T) := by
        convert hinner using 1
        ext p
        exact real_inner_comm _ _
      simpa [uν, innerScalarization] using hinner'
    simpa [w, cν] using hlin.sub hscalar_cont
  have hw0 : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    have hu0 : u 0 x ∈ C 0 := hinit x
    have hle := (hsupp 0 (u 0 x)).mp hu0 ν
    dsimp [w, cν, uν, innerScalarization]
    exact sub_nonneg.mpr (by simpa [real_inner_comm] using hle)
  have hw_time : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t := by
    intro s hs hs_pos x
    have hdiff_support : DifferentiableWithinAt Real (fun r : Real => support r ν)
        (Set.Icc 0 T) s := hsupport_time ν s hs hs_pos
    have hreg : s ∈ (RealTimeInterval.closed 0 T hT.le).regular := hregular s hs hs_pos
    have hderiv := hsol.equation ν s hreg x
    have hdiff_u : DifferentiableWithinAt Real (fun r : Real => uν r x)
        (Set.Icc 0 T) s := hderiv.differentiableAt.differentiableWithinAt
    simpa [w, cν, uν, innerScalarization] using hdiff_support.sub hdiff_u
  have hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro s hs _ x
    have hs_carrier : s ∈ (RealTimeInterval.closed 0 T hT.le).carrier := hs
    have hsmooth := hsol.scalarSliceSmooth ν s hs_carrier
    have hmdiff : MDifferentiableAt I 𝓘(Real, Real) (uν s) x :=
      hsmooth.mdifferentiable (by simp) x
    simpa [w, cν, uν, innerScalarization] using
      (mdifferentiableAt_const : MDifferentiableAt I 𝓘(Real, Real)
        (fun _y : M => support s ν) x).sub hmdiff
  have hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro s hs _ x
    have hs_carrier : s ∈ (RealTimeInterval.closed 0 T hT.le).carrier := hs
    have hsmooth := hsol.scalarSliceSmooth ν s hs_carrier
    have hfw : ContMDiff I 𝓘(Real, Real) ∞ (w s) := by
      simpa [w, cν, uν, innerScalarization] using contMDiff_const.sub hsmooth
    exact gradientFun_mdiffAt (I := I) (G.metric s) hfw x
  have hnegative : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      w t x < 0 →
        0 ≤ parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x)) w t x := by
    intro s hs hs_pos x hwneg
    have hreg : s ∈ (RealTimeInterval.closed 0 T hT.le).regular := hregular s hs hs_pos
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) s :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt hs
    have hderiv_u := hsol.equation ν s hreg x
    have hderiv_u_within :
        derivWithin (fun r : Real => uν r x) (Set.Icc 0 T) s =
          laplacianAt (I := I) G s (uν s) x + inner ℝ (reaction s x (u s x)) ν := by
      have h := hderiv_u.hasDerivWithinAt.derivWithin huniq
      simpa [uν, innerScalarization] using h
    have hpar_u :
        parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x)) uν s x =
          inner ℝ (reaction s x (u s x)) ν := by
      unfold parabolicOperatorWithDrift
      rw [hderiv_u_within]
      simp [uν, heatOperatorWithDrift]
    have hsupport_time_s : DifferentiableWithinAt Real
        (fun r : Real => support r ν) (Set.Icc 0 T) s :=
      hsupport_time ν s hs hs_pos
    have hsupport_space : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real) (fun _ : M => support s ν) y :=
      fun y => mdifferentiableAt_const
    have hsupport_grad : MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (fun _ : M => support s ν) y) x :=
      gradientFun_mdiffAt (I := I) (G.metric s) contMDiff_const x
    have hu_time_s : DifferentiableWithinAt Real
        (fun r : Real => uν r x) (Set.Icc 0 T) s :=
      hderiv_u.differentiableAt.differentiableWithinAt
    have hu_space_s : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (uν s) y :=
      fun y => (hsol.scalarSliceSmooth ν s hs).mdifferentiable (by simp) y
    have hu_grad_s : MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (uν s) y) x :=
      gradientFun_mdiffAt (I := I) (G.metric s) (hsol.scalarSliceSmooth ν s hs) x
    have hpar_support :
        parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x))
            (fun _r _y => support _r ν) s x =
          derivWithin (fun r : Real => support r ν) (Set.Icc 0 T) s := by
      unfold parabolicOperatorWithDrift
      simp only [heatOperatorWithDrift, driftTerm_zero_drift, laplacianAt]
      have hlap0 : laplacian (I := I) (G.connection s) (G.metric s)
          (fun _ : M => support s ν) x = 0 :=
        laplacian_const (I := I) (G.connection s) (G.metric s)
          (support s ν) x
      rw [hlap0]
      ring
    have hpar_sub := parabolic_sub (I := I) G T
      (fun _t x => (0 : TangentSpace I x))
      (fun r y => support r ν) uν s x
      hsupport_time_s hu_time_s hsupport_space hu_space_s hsupport_grad hu_grad_s
    have hpar_w :
        parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x)) w s x =
          derivWithin (fun r : Real => support r ν) (Set.Icc 0 T) s -
            inner ℝ (reaction s x (u s x)) ν := by
      rw [show parabolicOperatorWithDrift (I := I) G T
            (fun _t x => (0 : TangentSpace I x)) w s x =
          parabolicOperatorWithDrift (I := I) G T
            (fun _t x => (0 : TangentSpace I x))
            (fun r y => support r ν - uν r y) s x by rfl]
      rw [hpar_sub, hpar_support, hpar_u]
    have hreaction := hreaction s ⟨hs_pos, hreg.2⟩ x (u s x) ν
    have hreaction' : inner ℝ (reaction s x (u s x)) ν ≤
        derivWithin (fun r : Real => support r ν) (Set.Icc 0 T) s := by
      simpa [real_inner_comm] using hreaction
    rw [hpar_w]
    exact sub_nonneg.mpr hreaction'
  have hw_nonneg := strict_barrier_nonnegative_of_positive_time (I := I)
    (G := G) (T := T) (X := fun _t x => (0 : TangentSpace I x)) (w := w)
    hw_cont hw0 hw_time hw_mdiff hw_grad hnegative
  have hw_nonneg_at : 0 ≤ w t x := hw_nonneg t ht x
  exact sub_nonneg.mp (by simpa [w, cν, uν, innerScalarization, real_inner_comm] using hw_nonneg_at)

theorem closed_convex_timeDep_heat_reaction_mem_of_support_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (C : Real → Set F) (N : Set F) (support support' : Real → F → Real)
    (hCclosed : ∀ t : Real, IsClosed (C t))
    (hCconvex : ∀ t : Real, Convex ℝ (C t))
    (hCne : ∀ t : Real, (C t).Nonempty)
    (hsupp : ∀ t p, p ∈ C t ↔ ∀ ν : F, ν ∈ N → inner ℝ ν p ≤ support t ν)
    (hsupport_sup : ∀ t ν, ν ∈ N →
      support t ν = sSup {x : ℝ | ∃ q : F, q ∈ C t ∧ x = inner ℝ ν q})
    (hNnormal : ∀ t : Real, ∀ p : F, p ∈ C t → ∀ ν : F,
      (∀ q : F, q ∈ C t → inner ℝ ν (q - p) ≤ 0) → ν ∈ N)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT.le) G reaction u)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (hCdist_cont : ContinuousOn
      (fun q : Real × M => Metric.infDist (u q.1 q.2) (C q.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hsupport_cont : ∀ ν : F, ν ∈ N →
      ContinuousOn (fun t : Real => support t ν) (Set.Icc 0 T))
    (hsupport_time : ∀ ν : F, ν ∈ N → ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      HasDerivAt (fun s : Real => support s ν) (support' t ν) t)
    (htangent : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ∀ p : F,
      p ∈ C t → ∀ ν : F, ν ∈ N → support t ν = inner ℝ ν p →
        inner ℝ (reaction t x p) ν ≤ support' t ν)
    (hinit : ∀ x : M, u 0 x ∈ C 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t := by
  have hIco : ∀ t : Real, t ∈ Set.Ico 0 T → ∀ x : M, u t x ∈ C t := by
    intro t ht x
    by_contra hout
    have houtC : u t x ∉ C t := hout
    let KK : Real := (L : Real) + 1
    let d : Real × M → Real := fun q ↦
      Real.exp (-KK * q.1) * Metric.infDist (u q.1 q.2) (C q.1)
    let Q : Set (Real × M) := Set.Icc 0 t ×ˢ (Set.univ : Set M)
    have hQcompact : IsCompact Q :=
      (isCompact_Icc (a := (0 : Real)) (b := t)).prod CompactSpace.isCompact_univ
    have hQne : Q.Nonempty :=
      ⟨(0, x), Set.mk_mem_prod ⟨le_rfl, ht.1⟩ (Set.mem_univ x)⟩
    have hQsub : Q ⊆ (RealTimeInterval.closed 0 T hT.le).carrier ×ˢ univ := by
      intro q hq
      exact ⟨⟨hq.1.1, hq.1.2.trans ht.2.le⟩, hq.2⟩
    have hdcont : ContinuousOn d Q := by
      have hexp : Continuous (fun q : Real × M ↦ Real.exp (-KK * q.1)) := by
        fun_prop
      have hinf : ContinuousOn (fun q : Real × M => Metric.infDist (u q.1 q.2) (C q.1)) Q :=
        hCdist_cont.mono hQsub
      exact hexp.continuousOn.mul hinf
    obtain ⟨q₀, hq₀Q, hq₀max⟩ := hQcompact.exists_isMaxOn hQne hdcont
    have hdtxpos : 0 < d (t, x) := by
      apply mul_pos (Real.exp_pos _)
      exact (hCclosed t).notMem_iff_infDist_pos (hCne t) |>.mp houtC
    have hdq₀pos : 0 < d q₀ := lt_of_lt_of_le hdtxpos (hq₀max ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩)
    have hq₀tpos : 0 < q₀.1 := by
      by_contra hnonpos
      have hzero : q₀.1 = 0 := le_antisymm (not_lt.mp hnonpos) hq₀Q.1.1
      have : d q₀ = 0 := by
        have hinit' : u 0 q₀.2 ∈ C 0 := hinit q₀.2
        have hinitC : u q₀.1 q₀.2 ∈ C q₀.1 := by
          simpa [hzero] using hinit'
        have hz : Metric.infDist (u q₀.1 q₀.2) (C q₀.1) = 0 :=
          Metric.infDist_zero_of_mem hinitC
        dsimp [d]
        rw [hzero]
        have hz0 : Metric.infDist (u 0 q₀.2) (C 0) = 0 := Metric.infDist_zero_of_mem (hinit q₀.2)
        simp [hz0]
      linarith
    have hq₀reg : q₀.1 ∈ (RealTimeInterval.closed 0 T hT.le).regular := by
      change q₀.1 ∈ Set.Ioo 0 T
      exact ⟨hq₀tpos, lt_of_le_of_lt hq₀Q.1.2 ht.2⟩
    obtain ⟨p, hpC, hpmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex (hCne q₀.1) (hCclosed q₀.1).isComplete
        (hCconvex q₀.1) (u q₀.1 q₀.2)
    let ν' : F := u q₀.1 q₀.2 - p
    have hdist₀ : Metric.infDist (u q₀.1 q₀.2) (C q₀.1) = ‖ν'‖ := by
      rw [Metric.infDist_eq_iInf]
      rw [show ν' = u q₀.1 q₀.2 - p from rfl]
      rw [show (fun z : C q₀.1 => dist (u q₀.1 q₀.2) ↑z) = fun z : C q₀.1 => ‖u q₀.1 q₀.2 - ↑z‖ by
        funext z
        exact dist_eq_norm _ _]
      rw [hpmin]
    have hνpos : 0 < ‖ν'‖ := by
      have : 0 < Metric.infDist (u q₀.1 q₀.2) (C q₀.1) := by
        exact (mul_pos_iff_of_pos_left (Real.exp_pos (-KK * q₀.1))).mp
          (by simpa [d] using hdq₀pos)
      simpa [hdist₀] using this
    have hnormal : ∀ q ∈ C q₀.1, inner ℝ ν' (q - p) ≤ 0 := by
      exact (norm_eq_iInf_iff_real_inner_le_zero (hCconvex q₀.1) hpC).mp hpmin
    have hν'N : ν' ∈ N := hNnormal q₀.1 p hpC ν' hnormal
    have hsupp_eq : support q₀.1 ν' = inner ℝ ν' p := by
      apply le_antisymm
      · rw [hsupport_sup q₀.1 ν' hν'N]
        refine csSup_le ?_ ?_
        · rcases hCne q₀.1 with ⟨w, hw⟩
          refine ⟨inner ℝ ν' w, ?_⟩
          exact ⟨w, hw, rfl⟩
        · rintro x ⟨q, hq, rfl⟩
          have hqle := hnormal q hq
          have hqle' : inner ℝ ν' q - inner ℝ ν' p ≤ 0 := by
            have h := hqle
            rw [show inner ℝ ν' (q - p) = inner ℝ ν' q - inner ℝ ν' p by
              rw [inner_sub_right]] at h
            exact h
          linarith
      · exact (hsupp q₀.1 p).mp hpC ν' hν'N
    have hmain : inner ℝ (u q₀.1 q₀.2) ν' - support q₀.1 ν' = ‖ν'‖ ^ 2 := by
      rw [hsupp_eq]
      calc
        inner ℝ (u q₀.1 q₀.2) ν' - inner ℝ ν' p
            = inner ℝ ν' (u q₀.1 q₀.2) - inner ℝ ν' p := by
              rw [real_inner_comm]
        _ = inner ℝ ν' (u q₀.1 q₀.2 - p) := by
              rw [← inner_sub_right]
        _ = inner ℝ ν' ν' := by
              simp [ν']
        _ = ‖ν'‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
    have hsupport : ∀ s : Real, ∀ y : M,
        inner ℝ (u s y) ν' - support s ν' ≤ Metric.infDist (u s y) (C s) * ‖ν'‖ := by
      intro s y
      obtain ⟨q, hqC, hqmin⟩ :=
        exists_norm_eq_iInf_of_complete_convex (hCne s) (hCclosed s).isComplete
          (hCconvex s) (u s y)
      have hqdist : ‖u s y - q‖ = Metric.infDist (u s y) (C s) := by
        rw [Metric.infDist_eq_iInf]
        rw [show (fun z : C s => dist (u s y) ↑z) = fun z : C s => ‖u s y - ↑z‖ by
          funext z
          exact dist_eq_norm _ _]
        rw [← hqmin]
      have hqle : inner ℝ q ν' ≤ support s ν' := by
        simpa [real_inner_comm] using ((hsupp s q).mp hqC ν' hν'N)
      have huq : inner ℝ (u s y - q) ν' ≤ ‖u s y - q‖ * ‖ν'‖ := real_inner_le_norm _ _
      calc
        inner ℝ (u s y) ν' - support s ν'
            = inner ℝ (u s y - q) ν' + (inner ℝ q ν' - support s ν') := by
              conv_lhs =>
                rw [show u s y = (u s y - q) + q by abel]
              rw [inner_add_left]
              ring_nf
        _ ≤ ‖u s y - q‖ * ‖ν'‖ + 0 := by
              have hqle' : inner ℝ q ν' ≤ support s ν' := hqle
              exact add_le_add huq (sub_nonpos.mpr hqle')
        _ = Metric.infDist (u s y) (C s) * ‖ν'‖ := by
              rw [hqdist]
              ring
    let z : Real → M → Real := fun s y ↦
      Real.exp (-KK * s) * (inner ℝ (u s y) ν' - support s ν')
    have hzmax : ∀ r ∈ Q, z r.1 r.2 ≤ z q₀.1 q₀.2 := by
      intro r hr
      have hleft := mul_le_mul_of_nonneg_left (hsupport r.1 r.2)
        (Real.exp_pos (-KK * r.1)).le
      have hright := mul_le_mul_of_nonneg_right (hq₀max hr) (norm_nonneg ν')
      have hz₀ : z q₀.1 q₀.2 = d q₀ * ‖ν'‖ := by
        simp only [z, d, hdist₀, hmain]
        ring
      calc
        z r.1 r.2 ≤ Real.exp (-KK * r.1) *
            (Metric.infDist (u r.1 r.2) (C r.1) * ‖ν'‖) := hleft
        _ = d r * ‖ν'‖ := by simp only [d]; ring
        _ ≤ d q₀ * ‖ν'‖ := hright
        _ = z q₀.1 q₀.2 := hz₀.symm
    have hzspatial : IsLocalMax (z q₀.1) q₀.2 := by
      exact Filter.Eventually.of_forall (fun y ↦
        hzmax (q₀.1, y) ⟨hq₀Q.1, mem_univ y⟩)
    have hq₀carrier : q₀.1 ∈ (RealTimeInterval.closed 0 T hT.le).carrier :=
      (RealTimeInterval.closed 0 T hT.le).regular_subset hq₀reg
    have hzslice : ContMDiff I 𝓘(Real, Real) ∞ (z q₀.1) := by
      have huν : ContMDiff I 𝓘(Real, Real) ∞
          (fun y : M => inner ℝ (u q₀.1 y) ν') := by
        have hsmooth := hsol.scalarSliceSmooth ν' q₀.1 hq₀carrier
        simpa [innerScalarization, real_inner_comm] using hsmooth
      have hdiff : ContMDiff I 𝓘(Real, Real) ∞
          (fun y : M => inner ℝ (u q₀.1 y) ν' - support q₀.1 ν') :=
        huν.sub contMDiff_const
      simpa [z] using contMDiff_const.mul hdiff
    have hzlap : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 ≤ 0 :=
      laplacianAt_nonpos_at_spatial_max (I := I) G q₀.1 hzspatial hzslice
    have hztimeMax : IsMaxOn (fun s ↦ z s q₀.2) (Set.Icc 0 q₀.1) q₀.1 := by
      intro s hs
      exact hzmax (s, q₀.2) ⟨⟨hs.1, hs.2.trans hq₀Q.1.2⟩, mem_univ q₀.2⟩
    have hscalarEq := hsol.equation ν' q₀.1 hq₀reg q₀.2
    have hsupport_time_s : HasDerivAt (fun r : Real => support r ν')
        (support' q₀.1 ν') q₀.1 :=
      hsupport_time ν' hν'N q₀.1 hq₀carrier hq₀tpos
    have hexpDeriv : HasDerivAt (fun s : Real ↦ Real.exp (-KK * s))
        (Real.exp (-KK * q₀.1) * (-KK)) q₀.1 := by
      have hinner : HasDerivAt (fun s : Real ↦ -KK * s) (-KK) q₀.1 := by
        simpa using (hasDerivAt_id q₀.1).const_mul (-KK)
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_exp (-KK * q₀.1)).comp q₀.1 hinner
    have hzderiv : HasDerivAt (fun s ↦ z s q₀.2)
        (Real.exp (-KK * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (innerScalarization u ν' q₀.1) q₀.2 +
              inner ℝ (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν' -
              support' q₀.1 ν') -
          KK * Real.exp (-KK * q₀.1) *
            (inner ℝ (u q₀.1 q₀.2) ν' - support q₀.1 ν')) q₀.1 := by
      have hinnerDiff : HasDerivAt
          (fun s : Real => inner ℝ (u s q₀.2) ν' - support s ν')
          (laplacianAt (I := I) G q₀.1 (innerScalarization u ν' q₀.1) q₀.2 +
            inner ℝ (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν' -
            support' q₀.1 ν') q₀.1 := by
        simpa [innerScalarization, real_inner_comm] using hscalarEq.sub hsupport_time_s
      convert hexpDeriv.mul hinnerDiff using 1
      · ring
    have hztime : 0 ≤
        Real.exp (-KK * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (innerScalarization u ν' q₀.1) q₀.2 +
              inner ℝ (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν' -
              support' q₀.1 ν') -
          KK * Real.exp (-KK * q₀.1) *
            (inner ℝ (u q₀.1 q₀.2) ν' - support q₀.1 ν') :=
      deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc hq₀tpos hztimeMax hzderiv
    have hscalarSmooth := hsol.scalarSliceSmooth ν' q₀.1 hq₀carrier
    have hscalarMDiff : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real) (innerScalarization u ν' q₀.1) y :=
      fun y ↦ hscalarSmooth.mdifferentiable (by simp) y
    have hzlapEq : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 =
        Real.exp (-KK * q₀.1) *
          laplacianAt (I := I) G q₀.1 (innerScalarization u ν' q₀.1) q₀.2 := by
      have hsub : laplacianAt (I := I) G q₀.1
          (fun y : M ↦ innerScalarization u ν' q₀.1 y - support q₀.1 ν') q₀.2 =
          laplacianAt (I := I) G q₀.1 (innerScalarization u ν' q₀.1) q₀.2 := by
        exact laplacian_sub_const (I := I) (G.connection q₀.1) (G.metric q₀.1)
          (support q₀.1 ν') hscalarMDiff q₀.2
      have hsubSmooth : ContMDiff I 𝓘(Real, Real) ∞
          (fun y : M ↦ innerScalarization u ν' q₀.1 y - support q₀.1 ν') :=
        hscalarSmooth.sub contMDiff_const
      have hsmul := laplacianAt_smul (I := I) G q₀.1
        (Real.exp (-KK * q₀.1))
        (fun y ↦ hsubSmooth.mdifferentiable (by simp) y)
        (gradientFun_mdiffAt (I := I) (G.metric q₀.1) hsubSmooth q₀.2)
      have hfun : z q₀.1 = Real.exp (-KK * q₀.1) •
          (fun y : M ↦ innerScalarization u ν' q₀.1 y - support q₀.1 ν') := by
        funext y
        simp [z, innerScalarization]
      rw [hfun, hsmul, hsub]
    have hparabolicNonneg : 0 ≤
        Real.exp (-KK * q₀.1) *
          (inner ℝ (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν' -
            support' q₀.1 ν' - KK * ‖ν'‖ ^ 2) := by
      rw [hzlapEq] at hzlap
      rw [hmain] at hztime
      have hL' : laplacianAt (I := I) G q₀.1 (innerScalarization u ν' q₀.1) q₀.2 ≤ 0 := by
        have hpos : 0 < Real.exp (-KK * q₀.1) := Real.exp_pos _
        nlinarith
      nlinarith [hL', hztime, Real.exp_pos (-KK * q₀.1)]
    have htan := htangent q₀.1 hq₀carrier q₀.2 p hpC ν' hν'N hsupp_eq
    have hreactionp : inner ℝ ν' (reaction q₀.1 q₀.2 p) ≤ support' q₀.1 ν' := by
      simpa [real_inner_comm] using htan
    have hLip := (hL q₀.1 hq₀reg q₀.2).norm_sub_le
      (u q₀.1 q₀.2) p
    have hinnerLip : inner ℝ ν'
        (reaction q₀.1 q₀.2 (u q₀.1 q₀.2) - reaction q₀.1 q₀.2 p) ≤
          (L : Real) * ‖ν'‖ ^ 2 := by
      calc
        _ ≤ ‖ν'‖ * ‖reaction q₀.1 q₀.2 (u q₀.1 q₀.2) -
            reaction q₀.1 q₀.2 p‖ := real_inner_le_norm _ _
        _ ≤ ‖ν'‖ * ((L : Real) * ‖u q₀.1 q₀.2 - p‖) :=
          mul_le_mul_of_nonneg_left hLip (norm_nonneg ν')
        _ = (L : Real) * ‖ν'‖ ^ 2 := by
              rw [show u q₀.1 q₀.2 - p = ν' from rfl]
              ring
    have hreaction :
        inner ℝ (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν' - support' q₀.1 ν' ≤
          (L : Real) * ‖ν'‖ ^ 2 := by
      rw [real_inner_comm] at hreactionp hinnerLip
      rw [inner_sub_left] at hinnerLip
      linarith
    have hstrict :
        Real.exp (-KK * q₀.1) *
          (inner ℝ (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ν' -
            support' q₀.1 ν' - KK * ‖ν'‖ ^ 2) < 0 := by
      apply mul_neg_of_pos_of_neg (Real.exp_pos _)
      dsimp [KK]
      nlinarith [sq_pos_of_pos hνpos]
    linarith
  intro t ht x
  rcases eq_or_lt_of_le ht.2 with htEq | htlt
  · by_cases hTzero : T = 0
    · have htzero : t = 0 := by rw [htEq, hTzero]
      simpa [htzero] using hinit x
    · have hTpos : 0 < T := hT
      rw [htEq]
      have hcont := hsol.jointCont (T, x) ⟨⟨le_of_lt hT, le_rfl⟩, mem_univ x⟩
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
        simpa using hcont.tendsto.comp hpairWithin
      have hmemC : u T x ∈ C T := by
        rw [hsupp T (u T x)]
        intro ν hν
        have h1 : Filter.Tendsto (fun s : Real => support s ν) (𝓝[<] T) (𝓝 (support T ν)) := by
          have hwithin : Filter.Tendsto (fun s : Real => support s ν)
              (𝓝[Set.Icc 0 T] T) (𝓝 (support T ν)) :=
            (hsupport_cont ν hν).continuousWithinAt
              (show T ∈ Set.Icc 0 T from ⟨le_of_lt hTpos, le_rfl⟩)
          have hmem : Set.Icc 0 T ∈ 𝓝[Set.Iio T] T := by
            rw [mem_nhdsWithin]
            refine ⟨Set.Ioi (T / 2), isOpen_Ioi, (by linarith : T / 2 < T), ?_⟩
            rintro s ⟨hsgt, hslt⟩
            have hs1 : T / 2 < s := hsgt
            have hs2 : s < T := hslt
            exact ⟨by linarith, le_of_lt hs2⟩
          have hfilter : 𝓝[Set.Iio T] T ≤ 𝓝[Set.Icc 0 T] T := by
            have heq : 𝓝[Set.Iio T] T = 𝓝[Set.Iio T ∩ Set.Icc 0 T] T := by
              exact (nhdsWithin_inter_of_mem' hmem).symm
            rw [heq]
            exact nhdsWithin_mono T (by intro s hs; exact hs.2)
          exact hwithin.mono_left hfilter
        have h2 : Filter.Tendsto (fun s : Real => inner ℝ (u s x) ν)
            (𝓝[<] T) (𝓝 (inner ℝ (u T x) ν)) := by
          simpa [real_inner_comm] using (((innerSL ℝ ν).continuous.tendsto _).comp htend)
        have htend' : Filter.Tendsto
            (fun s : Real => inner ℝ (u s x) ν - support s ν)
            (𝓝[<] T) (𝓝 (inner ℝ (u T x) ν - support T ν)) :=
          h2.sub h1
        have hevent : ∀ᶠ s in 𝓝[<] T, inner ℝ (u s x) ν - support s ν ≤ 0 := by
          have hpos : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
          have hpos' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds hpos
          filter_upwards [hpos', self_mem_nhdsWithin] with s hs hslt
          have huC : u s x ∈ C s := hIco s ⟨le_of_lt hs, hslt⟩ x
          have hle := (hsupp s (u s x)).mp huC ν hν
          have hle' : inner ℝ (u s x) ν ≤ support s ν := by
            simpa [real_inner_comm] using hle
          linarith
        have hnonpos : inner ℝ (u T x) ν - support T ν ≤ 0 :=
          le_of_tendsto htend' hevent
        have hle' : inner ℝ (u T x) ν ≤ support T ν := by linarith
        simpa [real_inner_comm] using hle'
      exact hmemC
  · exact hIco t ⟨ht.1, htlt⟩ x

omit [CompleteSpace F] in
theorem closed_convex_timeDep_heat_reaction_mem_of_support_family_unbounded
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (C : Real → Set F) (N : Set F) (support : Real → F → Real)
    (hsupp : ∀ t p, p ∈ C t ↔ ∀ ν : F, ν ∈ N → inner ℝ ν p ≤ support t ν)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT.le) G reaction u)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      t ∈ (RealTimeInterval.closed 0 T hT.le).regular)
    (hsupport_cont : ∀ ν : F, ν ∈ N →
      ContinuousOn (fun t : Real => support t ν) (Set.Icc 0 T))
    (hsupport_time : ∀ ν : F, ν ∈ N → ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      DifferentiableWithinAt Real (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F, ∀ ν : F,
      ν ∈ N → support t ν < inner ℝ ν p →
        inner ℝ (reaction t x p) ν ≤ derivWithin (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hinit : ∀ x : M, u 0 x ∈ C 0) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t := by
  intro t ht x
  rw [hsupp]
  intro ν hν
  let uν : Real → M → Real := innerScalarization u ν
  let cν : Real → Real := fun s => support s ν
  let w : Real → M → Real := fun s y => cν s - uν s y
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have hlin : ContinuousOn (fun p : Real × M => cν p.1)
        (spacetimeSlab (M := M) T) := by
      refine (hsupport_cont ν hν).comp continuous_fst.continuousOn ?_
      intro p hp
      exact hp.1
    have hscalar_cont : ContinuousOn (fun p : Real × M => uν p.1 p.2)
        (spacetimeSlab (M := M) T) := by
      have hjoint := hsol.jointCont
      have hsub : spacetimeSlab (M := M) T ⊆
          (RealTimeInterval.closed 0 T hT.le).carrier ×ˢ (Set.univ : Set M) := by
        intro p hp
        exact ⟨hp.1, hp.2⟩
      have hcont := hjoint.mono hsub
      have hinner : ContinuousOn (fun p : Real × M => inner ℝ ν (u p.1 p.2))
          (spacetimeSlab (M := M) T) :=
        (innerSL ℝ ν).continuous.comp_continuousOn hcont
      have hinner' : ContinuousOn (fun p : Real × M => inner ℝ (u p.1 p.2) ν)
          (spacetimeSlab (M := M) T) := by
        convert hinner using 1
        ext p
        exact real_inner_comm _ _
      simpa [uν, innerScalarization] using hinner'
    simpa [w, cν] using hlin.sub hscalar_cont
  have hw0 : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    have hu0 : u 0 x ∈ C 0 := hinit x
    have hle := (hsupp 0 (u 0 x)).mp hu0 ν hν
    dsimp [w, cν, uν, innerScalarization]
    exact sub_nonneg.mpr (by simpa [real_inner_comm] using hle)
  have hw_time : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t := by
    intro s hs hs_pos x
    have hdiff_support : DifferentiableWithinAt Real (fun r : Real => support r ν)
        (Set.Icc 0 T) s := hsupport_time ν hν s hs hs_pos
    have hreg : s ∈ (RealTimeInterval.closed 0 T hT.le).regular := hregular s hs hs_pos
    have hderiv := hsol.equation ν s hreg x
    have hdiff_u : DifferentiableWithinAt Real (fun r : Real => uν r x)
        (Set.Icc 0 T) s := hderiv.differentiableAt.differentiableWithinAt
    simpa [w, cν, uν, innerScalarization] using hdiff_support.sub hdiff_u
  have hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro s hs _ x
    have hs_carrier : s ∈ (RealTimeInterval.closed 0 T hT.le).carrier := hs
    have hsmooth := hsol.scalarSliceSmooth ν s hs_carrier
    have hmdiff : MDifferentiableAt I 𝓘(Real, Real) (uν s) x :=
      hsmooth.mdifferentiable (by simp) x
    simpa [w, cν, uν, innerScalarization] using
      (mdifferentiableAt_const : MDifferentiableAt I 𝓘(Real, Real)
        (fun _y : M => support s ν) x).sub hmdiff
  have hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro s hs _ x
    have hs_carrier : s ∈ (RealTimeInterval.closed 0 T hT.le).carrier := hs
    have hsmooth := hsol.scalarSliceSmooth ν s hs_carrier
    have hfw : ContMDiff I 𝓘(Real, Real) ∞ (w s) := by
      simpa [w, cν, uν, innerScalarization] using contMDiff_const.sub hsmooth
    exact gradientFun_mdiffAt (I := I) (G.metric s) hfw x
  have hnegative : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      w t x < 0 →
        0 ≤ parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x)) w t x := by
    intro s hs hs_pos x hwneg
    have hreg : s ∈ (RealTimeInterval.closed 0 T hT.le).regular := hregular s hs hs_pos
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) s :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt hs
    have hderiv_u := hsol.equation ν s hreg x
    have hderiv_u_within :
        derivWithin (fun r : Real => uν r x) (Set.Icc 0 T) s =
          laplacianAt (I := I) G s (uν s) x + inner ℝ (reaction s x (u s x)) ν := by
      have h := hderiv_u.hasDerivWithinAt.derivWithin huniq
      simpa [uν, innerScalarization] using h
    have hpar_u :
        parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x)) uν s x =
          inner ℝ (reaction s x (u s x)) ν := by
      unfold parabolicOperatorWithDrift
      rw [hderiv_u_within]
      simp [uν, heatOperatorWithDrift]
    have hsupport_time_s : DifferentiableWithinAt Real
        (fun r : Real => support r ν) (Set.Icc 0 T) s :=
      hsupport_time ν hν s hs hs_pos
    have hsupport_space : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real) (fun _ : M => support s ν) y :=
      fun y => mdifferentiableAt_const
    have hsupport_grad : MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (fun _ : M => support s ν) y) x :=
      gradientFun_mdiffAt (I := I) (G.metric s) contMDiff_const x
    have hu_time_s : DifferentiableWithinAt Real
        (fun r : Real => uν r x) (Set.Icc 0 T) s :=
      hderiv_u.differentiableAt.differentiableWithinAt
    have hu_space_s : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (uν s) y :=
      fun y => (hsol.scalarSliceSmooth ν s hs).mdifferentiable (by simp) y
    have hu_grad_s : MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (uν s) y) x :=
      gradientFun_mdiffAt (I := I) (G.metric s) (hsol.scalarSliceSmooth ν s hs) x
    have hpar_support :
        parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x))
            (fun _r _y => support _r ν) s x =
          derivWithin (fun r : Real => support r ν) (Set.Icc 0 T) s := by
      unfold parabolicOperatorWithDrift
      simp only [heatOperatorWithDrift, driftTerm_zero_drift, laplacianAt]
      have hlap0 : laplacian (I := I) (G.connection s) (G.metric s)
          (fun _ : M => support s ν) x = 0 :=
        laplacian_const (I := I) (G.connection s) (G.metric s)
          (support s ν) x
      rw [hlap0]
      ring
    have hpar_sub := parabolic_sub (I := I) G T
      (fun _t x => (0 : TangentSpace I x))
      (fun r y => support r ν) uν s x
      hsupport_time_s hu_time_s hsupport_space hu_space_s hsupport_grad hu_grad_s
    have hpar_w :
        parabolicOperatorWithDrift (I := I) G T (fun _t x => (0 : TangentSpace I x)) w s x =
          derivWithin (fun r : Real => support r ν) (Set.Icc 0 T) s -
            inner ℝ (reaction s x (u s x)) ν := by
      rw [show parabolicOperatorWithDrift (I := I) G T
            (fun _t x => (0 : TangentSpace I x)) w s x =
          parabolicOperatorWithDrift (I := I) G T
            (fun _t x => (0 : TangentSpace I x))
            (fun r y => support r ν - uν r y) s x by rfl]
      rw [hpar_sub, hpar_support, hpar_u]
    have hviol : support s ν < inner ℝ ν (u s x) := by
      have hwneg' : cν s < uν s x := by
        dsimp [w] at hwneg
        linarith
      simpa [cν, uν, innerScalarization, real_inner_comm] using hwneg'
    have hreaction := hreaction s ⟨hs_pos, hreg.2⟩ x (u s x) ν hν hviol
    have hreaction' : inner ℝ (reaction s x (u s x)) ν ≤
        derivWithin (fun r : Real => support r ν) (Set.Icc 0 T) s := by
      simpa [real_inner_comm] using hreaction
    rw [hpar_w]
    exact sub_nonneg.mpr hreaction'
  have hw_nonneg := strict_barrier_nonnegative_of_positive_time (I := I)
    (G := G) (T := T) (X := fun _t x => (0 : TangentSpace I x)) (w := w)
    hw_cont hw0 hw_time hw_mdiff hw_grad hnegative
  have hw_nonneg_at : 0 ≤ w t x := hw_nonneg t ht x
  exact sub_nonneg.mp (by simpa [w, cν, uν, innerScalarization, real_inner_comm] using hw_nonneg_at)



include E in
omit [CompleteSpace F] in
theorem closed_convex_heat_reaction_mem_of_support_family_constant
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (C : Set F) (support : F → Real)
    (hsupp : ∀ p : F, p ∈ C ↔ ∀ ν : F, inner ℝ ν p ≤ support ν)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT.le) G reaction u)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      t ∈ (RealTimeInterval.closed 0 T hT.le).regular)
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F, ∀ ν : F,
      inner ℝ (reaction t x p) ν ≤ 0)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  let C' : Real → Set F := fun _ => C
  let support' : Real → F → Real := fun _ ν => support ν
  have hsupp' : IsConvexSupportFamily C' support' := by
    intro t p
    exact hsupp p
  have hsupport_cont : ∀ ν : F,
      ContinuousOn (fun t : Real => support' t ν) (Set.Icc 0 T) := by
    intro ν
    exact continuousOn_const
  have hsupport_time : ∀ ν : F, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      DifferentiableWithinAt Real (fun s : Real => support' s ν) (Set.Icc 0 T) t := by
    intro ν t ht hpos
    simpa [support'] using
      (differentiableWithinAt_const (c := support ν) :
        DifferentiableWithinAt ℝ (fun _ : ℝ => support ν) (Set.Icc 0 T) t)
  have hreaction' : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F, ∀ ν : F,
      inner ℝ (reaction t x p) ν ≤ derivWithin (fun s : Real => support' s ν) (Set.Icc 0 T) t := by
    intro t ht x p ν
    have h := hreaction t ht x p ν
    have hderiv : derivWithin (fun _ : Real => support ν) (Set.Icc 0 T) t = 0 := by
      exact (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T) (c := support ν)).derivWithin
        ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    simpa [support', hderiv] using h
  have hmain := closed_convex_timeDep_heat_reaction_mem_of_support_family
    (I := I) (M := M) G hT C' support' hsupp' reaction u hsol hregular
    hsupport_cont hsupport_time hreaction' (by intro x; exact hinit x)
  intro t ht x
  exact hmain t ht x


def translateSupport (s : F → Real) (v : F) : Real → F → Real :=
  fun t ν => s ν + t * inner ℝ ν v

omit [CompleteSpace F] in
theorem isConvexSupportFamily_translate
    {C : Set F} {s : F → Real}
    (hs : ∀ p : F, p ∈ C ↔ ∀ ν : F, inner ℝ ν p ≤ s ν)
    (v : F) :
    IsConvexSupportFamily
      (fun t : Real => {p : F | ∃ q : F, q ∈ C ∧ p = q + t • v})
      (translateSupport s v) := by
  intro t p
  constructor
  · rintro ⟨q, hq, rfl⟩ ν
    have hqν := (hs q).mp hq ν
    dsimp [translateSupport]
    have hinner : inner ℝ (q + t • v) ν = inner ℝ q ν + t * inner ℝ v ν := by
      simp [inner_add_left, inner_smul_left]
    have htarget : inner ℝ ν (q + t • v) ≤ s ν + t * inner ℝ ν v := by
      rw [real_inner_comm]
      rw [hinner]
      have hqν' : inner ℝ q ν ≤ s ν := by simpa [real_inner_comm] using hqν
      have hv : inner ℝ v ν = inner ℝ ν v := real_inner_comm _ _
      calc
        inner ℝ q ν + t * inner ℝ v ν
            = inner ℝ q ν + t * inner ℝ ν v := by rw [hv]
        _ ≤ s ν + t * inner ℝ ν v := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right hqν' (t * inner ℝ ν v))
    exact htarget
  · intro hp
    let q : F := p - t • v
    have hq : ∀ ν : F, inner ℝ q ν ≤ s ν := by
      intro ν
      have h := hp ν
      dsimp [translateSupport] at h
      have hpν : inner ℝ p ν ≤ s ν + t * inner ℝ ν v := by
        simpa [real_inner_comm] using h
      have hqν : inner ℝ q ν = inner ℝ p ν - t * inner ℝ v ν := by
        dsimp [q]
        simp [inner_sub_left, inner_smul_left]
      have hv : inner ℝ v ν = inner ℝ ν v := real_inner_comm _ _
      calc
        inner ℝ q ν = inner ℝ p ν - t * inner ℝ v ν := hqν
        _ = inner ℝ p ν - t * inner ℝ ν v := by rw [hv]
        _ ≤ s ν := by linarith
    refine ⟨q, (hs q).mpr (fun ν => by simpa [real_inner_comm] using hq ν), ?_⟩
    dsimp [q]
    abel

include E in
omit [CompleteSpace F] in
theorem translated_convex_heat_reaction_mem
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (C : Set F) (s : F → Real)
    (hs : ∀ p : F, p ∈ C ↔ ∀ ν : F, inner ℝ ν p ≤ s ν)
    (v : F)
    (reaction : Real → M → F → F)
    (u : Real → M → F)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT.le) G reaction u)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      t ∈ (RealTimeInterval.closed 0 T hT.le).regular)
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F, ∀ ν : F,
      inner ℝ (reaction t x p) ν ≤ inner ℝ ν v)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      ∃ q : F, q ∈ C ∧ u t x = q + t • v := by
  let C' : Real → Set F := fun t => {p : F | ∃ q : F, q ∈ C ∧ p = q + t • v}
  let support' : Real → F → Real := translateSupport s v
  have hsupp' : IsConvexSupportFamily C' support' := isConvexSupportFamily_translate hs v
  have hsupport_cont : ∀ ν : F,
      ContinuousOn (fun t : Real => support' t ν) (Set.Icc 0 T) := by
    intro ν
    have hlin : ContinuousOn (fun t : Real => s ν + t * inner ℝ ν v) (Set.Icc 0 T) := by
      fun_prop
    simpa [support', translateSupport] using hlin
  have hsupport_time : ∀ ν : F, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      DifferentiableWithinAt Real (fun r : Real => support' r ν) (Set.Icc 0 T) t := by
    intro ν t ht hpos
    have hlin : DifferentiableWithinAt Real
        (fun r : Real => s ν + r * inner ℝ ν v) (Set.Icc 0 T) t := by
      fun_prop
    simpa [support', translateSupport] using hlin
  have hreaction' : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F, ∀ ν : F,
      inner ℝ (reaction t x p) ν ≤ derivWithin (fun r : Real => support' r ν) (Set.Icc 0 T) t := by
    intro t ht x p ν
    have h := hreaction t ht x p ν
    have hderiv : derivWithin (fun r : Real => support' r ν) (Set.Icc 0 T) t = inner ℝ ν v := by
      change derivWithin (fun r : Real => s ν + r * inner ℝ ν v) (Set.Icc 0 T) t =
          inner ℝ ν v
      have hid : HasDerivWithinAt (fun r : Real => r) 1 (Set.Icc 0 T) t :=
        hasDerivWithinAt_id (x := t) (s := Set.Icc 0 T)
      have hmul : HasDerivWithinAt (fun r : Real => r * inner ℝ ν v)
          (inner ℝ ν v) (Set.Icc 0 T) t := by
        simpa using (hid.mul_const (inner ℝ ν v))
      have hlin : HasDerivWithinAt (fun r : Real => s ν + r * inner ℝ ν v)
          (inner ℝ ν v) (Set.Icc 0 T) t := by
        convert (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T) (c := s ν)).add hmul using 1; simp
      exact hlin.derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    rw [hderiv]
    simpa using h
  have hmain := closed_convex_timeDep_heat_reaction_mem_of_support_family
    (I := I) (M := M) G hT C' support' hsupp' reaction u hsol hregular
    hsupport_cont hsupport_time hreaction'
    (by intro x; exact ⟨u 0 x, hinit x, by simp⟩)
  intro t ht x
  exact hmain t ht x

omit [CompleteSpace F] in
theorem isConvexSupportFamily_const {C : Set F} {s : F → Real}
    (hs : ∀ p : F, p ∈ C ↔ ∀ ν : F, inner ℝ ν p ≤ s ν) :
    IsConvexSupportFamily (fun _ : Real => C) (fun (_ : Real) (ν : F) => s ν) := by
  intro t p
  exact hs p

omit [CompleteSpace F] in
theorem derivWithin_translateSupport
    {s : F → Real} (v : F) (ν : F) {T t : Real} (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T) :
    derivWithin (fun r : Real => translateSupport s v r ν) (Set.Icc 0 T) t =
      inner ℝ ν v := by
  change derivWithin (fun r : Real => s ν + r * inner ℝ ν v) (Set.Icc 0 T) t =
      inner ℝ ν v
  have hid : HasDerivWithinAt (fun r : Real => r) 1 (Set.Icc 0 T) t :=
    hasDerivWithinAt_id (x := t) (s := Set.Icc 0 T)
  have hmul : HasDerivWithinAt (fun r : Real => r * inner ℝ ν v)
      (inner ℝ ν v) (Set.Icc 0 T) t := by
    simpa using (hid.mul_const (inner ℝ ν v))
  have hlin : HasDerivWithinAt (fun r : Real => s ν + r * inner ℝ ν v)
      (inner ℝ ν v) (Set.Icc 0 T) t := by
    convert (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T) (c := s ν)).add hmul using 1; simp
  exact hlin.derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)

omit [CompleteSpace F] in
theorem continuousOn_translateSupport (s : F → Real) (v : F) (ν : F) (T : Real) :
    ContinuousOn (fun t : Real => translateSupport s v t ν) (Set.Icc 0 T) := by
  have hlin : ContinuousOn (fun t : Real => s ν + t * inner ℝ ν v) (Set.Icc 0 T) := by
    fun_prop
  simpa [translateSupport] using hlin

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem continuousOn_constSupport (s : F → Real) (ν : F) (T : Real) :
    ContinuousOn (fun _ : Real => s ν) (Set.Icc 0 T) := by
  exact continuousOn_const

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem derivWithin_constSupport (s : F → Real) (ν : F) {T t : Real} (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T) :
    derivWithin (fun _ : Real => s ν) (Set.Icc 0 T) t = 0 := by
  exact (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T) (c := s ν)).derivWithin
    ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)

omit [CompleteSpace F] in
theorem differentiableWithinAt_translateSupport (s : F → Real) (v : F) (ν : F)
    (T t : Real) :
    DifferentiableWithinAt Real (fun r : Real => translateSupport s v r ν)
      (Set.Icc 0 T) t := by
  have hlin : DifferentiableWithinAt Real
      (fun r : Real => s ν + r * inner ℝ ν v) (Set.Icc 0 T) t := by
    fun_prop
  simpa [translateSupport] using hlin

end DifferentialGeometry.Analysis.Parabolic
