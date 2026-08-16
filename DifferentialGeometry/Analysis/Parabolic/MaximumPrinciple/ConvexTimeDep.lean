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
