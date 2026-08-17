import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SemilinearConvex
import DifferentialGeometry.Geometry.Curvature.Realized.Operators

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
variable [∀ x, CompleteSpace (V x)]
variable [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

def bundleInnerScalarization
    (u : Real → (x : M) → V x) (ν : (x : M) → V x) : Real → M → Real :=
  fun t x => inner ℝ (u t x) (ν x)

def IsBundleConvexSupportFamily (F : Type uF) [NormedAddCommGroup F]
    [InnerProductSpace Real F] [CompleteSpace F]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    (C : Real → (x : M) → Set (V x)) (support : Real → (x : M) → V x → Real) : Prop :=
  ∀ t x p, p ∈ C t x ↔
    ∀ ν : Cₛ^∞⟮I; F, V⟯, inner ℝ p (ν x) ≤ support t x (ν x)

structure IsBundleHeatReactionOn (F : Type uF) [NormedAddCommGroup F]
    [InnerProductSpace Real F] [CompleteSpace F]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    (Flat : (x : M) → Cₛ^∞⟮I; F, V⟯ → Prop)
    (D : RealTimeInterval) (G : MetricConnectionFamily (I := I) (M := M) Real)
    (source : Real → (x : M) → V x → V x → Real)
    (u : Real → (x : M) → V x) : Prop where
  scalarJointCont :
    ∀ ν : Cₛ^∞⟮I; F, V⟯,
      ContinuousOn (fun q : Real × M => bundleInnerScalarization u ν q.1 q.2)
        (D.carrier ×ˢ (Set.univ : Set M))
  scalarSliceSmooth :
    ∀ ν : Cₛ^∞⟮I; F, V⟯, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (bundleInnerScalarization u ν t)
  equation :
    ∀ ν : Cₛ^∞⟮I; F, V⟯, ∀ t : Real, t ∈ D.regular → ∀ x : M,
      Flat x ν →
      HasDerivAt (fun s : Real => bundleInnerScalarization u ν s x)
        (laplacianAt (I := I) G t (bundleInnerScalarization u ν t) x +
          source t x (u t x) (ν x)) t

structure HasFlatSupportSections (I : ModelWithCorners Real E H) (F : Type uF)
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    (Flat : (x : M) → Cₛ^∞⟮I; F, V⟯ → Prop)
    (N : (x : M) → Set (V x)) (support : Real → (x : M) → V x → Real) : Prop where
  exists_flat : ∀ t : Real, ∀ x₀ : M, ∀ ν' : V x₀, ν' ∈ N x₀ →
    ∃ ν : Cₛ^∞⟮I; F, V⟯,
      Flat x₀ ν ∧
      ν x₀ = ν' ∧
      (∀ x : M, ν x ∈ N x) ∧
      (∀ x : M, ‖ν x‖ ≤ ‖ν'‖) ∧
      ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∀ y : M, y ∈ U →
        support t y (ν y) = support t x₀ ν'

omit [CompleteSpace E] in
theorem bundleClosedConvex_timeDep_heat_reaction_mem_of_support_tangent
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (Flat : (x : M) → Cₛ^∞⟮I; F, V⟯ → Prop)
    (C : Real → (x : M) → Set (V x)) (N : (x : M) → Set (V x))
    (support support' : Real → (x : M) → V x → Real)
    (hCclosed : ∀ t x, IsClosed (C t x))
    (hCconvex : ∀ t x, Convex ℝ (C t x))
    (hCne : ∀ t x, (C t x).Nonempty)
    (hsupp : ∀ t x p, p ∈ C t x ↔ ∀ ν : V x, ν ∈ N x → inner ℝ ν p ≤ support t x ν)
    (hsupport_sup : ∀ t x ν, ν ∈ N x →
      support t x ν = sSup {r : ℝ | ∃ q : V x, q ∈ C t x ∧ r = inner ℝ q ν})
    (hNnormal : ∀ t x, ∀ p : V x, p ∈ C t x → ∀ ν : V x,
      (∀ q : V x, q ∈ C t x → inner ℝ ν (q - p) ≤ 0) → ν ∈ N x)
    (source : Real → (x : M) → V x → V x → Real)
    (u : Real → (x : M) → V x)
    (hsol : IsBundleHeatReactionOn F Flat (RealTimeInterval.closed 0 T hT.le) G source u)
    (R : ℝ)
    (hbound : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, ‖u t x‖ ≤ R)
    (hCzero : ∀ t x, (0 : V x) ∈ C t x)
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ ν : V x,
      LipschitzOnWith (L * ‖ν‖₊) (fun p : V x => source t x p ν) (Metric.closedBall 0 (2 * R)))
    (hCdist_cont : ContinuousOn
      (fun q : Real × M => Metric.infDist (u q.1 q.2) (C q.1 q.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)))
    (hflat : HasFlatSupportSections (I := I) F Flat N support)
    (hsupport_cont : ∀ ν : Cₛ^∞⟮I; F, V⟯, ∀ x : M,
      ContinuousOn (fun t : Real => support t x (ν x)) (Set.Icc 0 T))
    (hsupport_time : ∀ ν : Cₛ^∞⟮I; F, V⟯, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      HasDerivAt (fun s : Real => support s x (ν x)) (support' t x (ν x)) t)
    (htangent : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M, ∀ p : V x,
      p ∈ C t x → ∀ ν : V x, ν ∈ N x → support t x ν = inner ℝ ν p →
        source t x p ν ≤ support' t x ν)
    (hinit : ∀ x : M, u 0 x ∈ C 0 x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t x := by
  have hIco : ∀ t : Real, t ∈ Set.Ico 0 T → ∀ x : M, u t x ∈ C t x := by
    intro t ht x
    by_contra hout
    have houtC : u t x ∉ C t x := hout
    let KK : Real := (L : Real) + 1
    let d : Real × M → Real := fun q ↦
      Real.exp (-KK * q.1) * Metric.infDist (u q.1 q.2) (C q.1 q.2)
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
      have hinf : ContinuousOn (fun q : Real × M => Metric.infDist (u q.1 q.2) (C q.1 q.2)) Q :=
        hCdist_cont.mono hQsub
      exact hexp.continuousOn.mul hinf
    obtain ⟨q₀, hq₀Q, hq₀max⟩ := hQcompact.exists_isMaxOn hQne hdcont
    have hdtxpos : 0 < d (t, x) := by
      apply mul_pos (Real.exp_pos _)
      exact (hCclosed t x).notMem_iff_infDist_pos (hCne t x) |>.mp houtC
    have hdq₀pos : 0 < d q₀ := lt_of_lt_of_le hdtxpos (hq₀max ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩)
    have hq₀tpos : 0 < q₀.1 := by
      by_contra hnonpos
      have hzero : q₀.1 = 0 := le_antisymm (not_lt.mp hnonpos) hq₀Q.1.1
      have : d q₀ = 0 := by
        have hinit' : u 0 q₀.2 ∈ C 0 q₀.2 := hinit q₀.2
        have hinitC : u q₀.1 q₀.2 ∈ C q₀.1 q₀.2 := by
          simpa [hzero] using hinit'
        have hz : Metric.infDist (u q₀.1 q₀.2) (C q₀.1 q₀.2) = 0 :=
          Metric.infDist_zero_of_mem hinitC
        dsimp [d]
        rw [hzero]
        have hz0 : Metric.infDist (u 0 q₀.2) (C 0 q₀.2) = 0 := Metric.infDist_zero_of_mem (hinit q₀.2)
        simp [hz0]
      linarith
    have hq₀reg : q₀.1 ∈ (RealTimeInterval.closed 0 T hT.le).regular := by
      change q₀.1 ∈ Set.Ioo 0 T
      exact ⟨hq₀tpos, lt_of_le_of_lt hq₀Q.1.2 ht.2⟩
    have hq₀carrier : q₀.1 ∈ (RealTimeInterval.closed 0 T hT.le).carrier :=
      (RealTimeInterval.closed 0 T hT.le).regular_subset hq₀reg
    obtain ⟨p, hpC, hpmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex (hCne q₀.1 q₀.2) (hCclosed q₀.1 q₀.2).isComplete
        (hCconvex q₀.1 q₀.2) (u q₀.1 q₀.2)
    let ν' : V q₀.2 := u q₀.1 q₀.2 - p
    have hdist₀ : Metric.infDist (u q₀.1 q₀.2) (C q₀.1 q₀.2) = ‖ν'‖ := by
      rw [Metric.infDist_eq_iInf]
      rw [show ν' = u q₀.1 q₀.2 - p from rfl]
      rw [show (fun z : C q₀.1 q₀.2 => dist (u q₀.1 q₀.2) ↑z) =
          fun z : C q₀.1 q₀.2 => ‖u q₀.1 q₀.2 - ↑z‖ by
        funext z
        exact dist_eq_norm _ _]
      rw [hpmin]
    have hνpos : 0 < ‖ν'‖ := by
      have : 0 < Metric.infDist (u q₀.1 q₀.2) (C q₀.1 q₀.2) := by
        exact (mul_pos_iff_of_pos_left (Real.exp_pos (-KK * q₀.1))).mp
          (by simpa [d] using hdq₀pos)
      simpa [hdist₀] using this
    have hnormal : ∀ q ∈ C q₀.1 q₀.2, inner ℝ ν' (q - p) ≤ 0 := by
      exact (norm_eq_iInf_iff_real_inner_le_zero (hCconvex q₀.1 q₀.2) hpC).mp hpmin
    have hν'N : ν' ∈ N q₀.2 := hNnormal q₀.1 q₀.2 p hpC ν' hnormal
    rcases hflat.exists_flat q₀.1 q₀.2 ν' hν'N with
      ⟨ν₀, hν₀flat, hν₀at, hν₀N, hν₀norm, U, hUopen, hx₀U, hflatU⟩
    have hsupp_eq : support q₀.1 q₀.2 ν' = inner ℝ ν' p := by
      apply le_antisymm
      · rw [hsupport_sup q₀.1 q₀.2 ν' hν'N]
        refine csSup_le ?_ ?_
        · rcases hCne q₀.1 q₀.2 with ⟨w, hw⟩
          refine ⟨inner ℝ ν' w, ?_⟩
          exact ⟨w, hw, (real_inner_comm ν' w).symm⟩
        · rintro r ⟨q, hq, hr⟩
          subst r
          have hqle := hnormal q hq
          have hqle' : inner ℝ q ν' - inner ℝ ν' p ≤ 0 := by
            rw [real_inner_comm]
            rw [← inner_sub_right]
            exact hqle
          linarith
      · exact (hsupp q₀.1 q₀.2 p).mp hpC ν' hν'N
    have hmain : inner ℝ (u q₀.1 q₀.2) ν' - support q₀.1 q₀.2 ν' = ‖ν'‖ ^ 2 := by
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
        inner ℝ (u s y) (ν₀ y) - support s y (ν₀ y) ≤ Metric.infDist (u s y) (C s y) * ‖ν₀ y‖ := by
      intro s y
      obtain ⟨q, hqC, hqmin⟩ :=
        exists_norm_eq_iInf_of_complete_convex (hCne s y) (hCclosed s y).isComplete
          (hCconvex s y) (u s y)
      have hqdist : ‖u s y - q‖ = Metric.infDist (u s y) (C s y) := by
        rw [Metric.infDist_eq_iInf]
        rw [show (fun z : C s y => dist (u s y) ↑z) = fun z : C s y => ‖u s y - ↑z‖ by
          funext z
          exact dist_eq_norm _ _]
        rw [← hqmin]
      have hqle : inner ℝ q (ν₀ y) ≤ support s y (ν₀ y) := by
        simpa [real_inner_comm] using ((hsupp s y q).mp hqC (ν₀ y) (hν₀N y))
      have huq : inner ℝ (u s y - q) (ν₀ y) ≤ ‖u s y - q‖ * ‖ν₀ y‖ := real_inner_le_norm _ _
      calc
        inner ℝ (u s y) (ν₀ y) - support s y (ν₀ y)
            = inner ℝ (u s y - q) (ν₀ y) + (inner ℝ q (ν₀ y) - support s y (ν₀ y)) := by
              conv_lhs =>
                rw [show u s y = (u s y - q) + q by abel]
              rw [inner_add_left]
              ring_nf
        _ ≤ ‖u s y - q‖ * ‖ν₀ y‖ + 0 := by
              have hqle' : inner ℝ q (ν₀ y) ≤ support s y (ν₀ y) := hqle
              exact add_le_add huq (sub_nonpos.mpr hqle')
        _ = Metric.infDist (u s y) (C s y) * ‖ν₀ y‖ := by
              rw [hqdist]
              ring
    let z : Real → M → Real := fun s y ↦
      Real.exp (-KK * s) * (inner ℝ (u s y) (ν₀ y) - support s y (ν₀ y))
    have hzmax : ∀ r ∈ Q, z r.1 r.2 ≤ z q₀.1 q₀.2 := by
      intro r hr
      have hleft := mul_le_mul_of_nonneg_left (hsupport r.1 r.2)
        (Real.exp_pos (-KK * r.1)).le
      have hright := mul_le_mul_of_nonneg_right (hq₀max hr) (norm_nonneg ν')
      have hmid : Real.exp (-KK * r.1) *
          (Metric.infDist (u r.1 r.2) (C r.1 r.2) * ‖ν₀ r.2‖) ≤
          Real.exp (-KK * r.1) *
            (Metric.infDist (u r.1 r.2) (C r.1 r.2) * ‖ν'‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hν₀norm r.2) Metric.infDist_nonneg)
          (Real.exp_pos (-KK * r.1)).le
      have hz₀ : z q₀.1 q₀.2 = d q₀ * ‖ν'‖ := by
        simp only [z, d, hν₀at, hdist₀, hmain]
        ring
      calc
        z r.1 r.2 ≤ Real.exp (-KK * r.1) *
            (Metric.infDist (u r.1 r.2) (C r.1 r.2) * ‖ν₀ r.2‖) := hleft
        _ ≤ Real.exp (-KK * r.1) *
            (Metric.infDist (u r.1 r.2) (C r.1 r.2) * ‖ν'‖) := hmid
        _ = d r * ‖ν'‖ := by simp only [d]; ring
        _ ≤ d q₀ * ‖ν'‖ := hright
        _ = z q₀.1 q₀.2 := hz₀.symm
    have hzspatial : IsLocalMax (z q₀.1) q₀.2 :=
      Filter.Eventually.of_forall (fun y ↦
        hzmax (q₀.1, y) ⟨hq₀Q.1, mem_univ y⟩)
    let c : Real := support q₀.1 q₀.2 ν'
    let z' : M → Real := fun y =>
      Real.exp (-KK * q₀.1) * (bundleInnerScalarization u ν₀ q₀.1 y - c)
    have hUmem : U ∈ 𝓝 q₀.2 := hUopen.mem_nhds hx₀U
    have heq_z : (z q₀.1) =ᶠ[nhds q₀.2] z' := by
      filter_upwards [hUmem] with y hy
      simp [z, z', c, bundleInnerScalarization, hflatU y hy]
    have hz'ContMDiff : ContMDiff I 𝓘(Real, Real) ∞ z' := by
      have hg := hsol.scalarSliceSmooth ν₀ q₀.1 hq₀carrier
      dsimp [z']
      exact contMDiff_const.mul (hg.sub contMDiff_const)
    have hzContMDiffAt : ContMDiffAt I 𝓘(Real, Real) ∞ (z q₀.1) q₀.2 :=
      hz'ContMDiff.contMDiffAt.congr_of_eventuallyEq heq_z
    have hf : MDifferentiableAt I 𝓘(Real, Real) (z q₀.1) q₀.2 :=
      hzContMDiffAt.mdifferentiableAt (by simp)
    have hf_near : ∀ᶠ y in nhds q₀.2, MDifferentiableAt I 𝓘(Real, Real) (z q₀.1) y := by
      filter_upwards [heq_z.eventuallyEq_nhds] with y hy
      exact (hz'ContMDiff.contMDiffAt.mdifferentiableAt (by simp)).congr_of_eventuallyEq hy
    have hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric q₀.1) (z q₀.1) y) q₀.2 := by
      have hgrad' : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric q₀.1) z' y) q₀.2 :=
        (gradientFun_contMDiffAt (I := I) (G.metric q₀.1) hz'ContMDiff.contMDiffAt).mdifferentiableAt
          (by simp)
      have hgrad_eq : (fun y : M => gradientFun (I := I) (G.metric q₀.1) (z q₀.1) y) =ᶠ[nhds q₀.2]
          (fun y : M => gradientFun (I := I) (G.metric q₀.1) z' y) := by
        filter_upwards [heq_z.eventuallyEq_nhds] with y hy
        unfold gradientFun metricSharp
        rw [hy.mfderiv_eq]
      have htotal :
          (T% fun y : M => gradientFun (I := I) (G.metric q₀.1) (z q₀.1) y) =ᶠ[nhds q₀.2]
            (T% fun y : M => gradientFun (I := I) (G.metric q₀.1) z' y) := by
        filter_upwards [hgrad_eq] with y hy
        change TotalSpace.mk' E y (gradientFun (I := I) (G.metric q₀.1) (z q₀.1) y) =
          TotalSpace.mk' E y (gradientFun (I := I) (G.metric q₀.1) z' y)
        rw [hy]
      exact hgrad'.congr_of_eventuallyEq htotal
    have hzlap : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 ≤ 0 :=
      laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint (I := I) G q₀.1 hzspatial
        BoundarylessManifold.isInteriorPoint hf hf_near hgrad
    have hztimeMax : IsMaxOn (fun s ↦ z s q₀.2) (Set.Icc 0 q₀.1) q₀.1 := by
      intro s hs
      exact hzmax (s, q₀.2) ⟨⟨hs.1, hs.2.trans hq₀Q.1.2⟩, mem_univ q₀.2⟩
    have hscalarEq := hsol.equation ν₀ q₀.1 hq₀reg q₀.2 hν₀flat
    have hsupport_time_s : HasDerivAt (fun r : Real => support r q₀.2 (ν₀ q₀.2))
        (support' q₀.1 q₀.2 (ν₀ q₀.2)) q₀.1 :=
      hsupport_time ν₀ q₀.1 hq₀carrier hq₀tpos q₀.2
    have hexpDeriv : HasDerivAt (fun s : Real ↦ Real.exp (-KK * s))
        (Real.exp (-KK * q₀.1) * (-KK)) q₀.1 := by
      have hinner : HasDerivAt (fun s : Real ↦ -KK * s) (-KK) q₀.1 := by
        simpa using (hasDerivAt_id q₀.1).const_mul (-KK)
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_exp (-KK * q₀.1)).comp q₀.1 hinner
    have hinnerDiff : HasDerivAt
        (fun s : Real => inner ℝ (u s q₀.2) (ν₀ q₀.2) - support s q₀.2 (ν₀ q₀.2))
        (laplacianAt (I := I) G q₀.1 (bundleInnerScalarization u ν₀ q₀.1) q₀.2 +
          source q₀.1 q₀.2 (u q₀.1 q₀.2) (ν₀ q₀.2) -
          support' q₀.1 q₀.2 (ν₀ q₀.2)) q₀.1 := by
      simpa [bundleInnerScalarization, real_inner_comm] using hscalarEq.sub hsupport_time_s
    have hzderiv : HasDerivAt (fun s ↦ z s q₀.2)
        (Real.exp (-KK * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (bundleInnerScalarization u ν₀ q₀.1) q₀.2 +
              source q₀.1 q₀.2 (u q₀.1 q₀.2) (ν₀ q₀.2) -
              support' q₀.1 q₀.2 (ν₀ q₀.2)) -
          KK * Real.exp (-KK * q₀.1) *
            (inner ℝ (u q₀.1 q₀.2) (ν₀ q₀.2) - support q₀.1 q₀.2 (ν₀ q₀.2))) q₀.1 := by
      convert hexpDeriv.mul hinnerDiff using 1
      · ring
    have hztime : 0 ≤
        Real.exp (-KK * q₀.1) *
            (laplacianAt (I := I) G q₀.1 (bundleInnerScalarization u ν₀ q₀.1) q₀.2 +
              source q₀.1 q₀.2 (u q₀.1 q₀.2) (ν₀ q₀.2) -
              support' q₀.1 q₀.2 (ν₀ q₀.2)) -
          KK * Real.exp (-KK * q₀.1) *
            (inner ℝ (u q₀.1 q₀.2) (ν₀ q₀.2) - support q₀.1 q₀.2 (ν₀ q₀.2)) :=
      deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc hq₀tpos hztimeMax hzderiv
    have hz'f_near : ∀ᶠ y in nhds q₀.2, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => bundleInnerScalarization u ν₀ q₀.1 y - c) y := by
      have hg := hsol.scalarSliceSmooth ν₀ q₀.1 hq₀carrier
      exact Filter.Eventually.of_forall (fun y =>
        (hg.mdifferentiable (by simp) y).sub mdifferentiableAt_const)
    have hz'grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric q₀.1)
        (fun y : M => bundleInnerScalarization u ν₀ q₀.1 y - c) y) q₀.2 := by
      have hg := hsol.scalarSliceSmooth ν₀ q₀.1 hq₀carrier
      exact gradientFun_mdiffAt (I := I) (G.metric q₀.1) (hg.sub contMDiff_const) q₀.2
    have hzlapEq : laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2 =
        Real.exp (-KK * q₀.1) *
          laplacianAt (I := I) G q₀.1 (bundleInnerScalarization u ν₀ q₀.1) q₀.2 := by
      have hcongr := laplacian_congr_of_eventuallyEq (I := I) (G.connection q₀.1) (G.metric q₀.1)
        hzContMDiffAt hz'ContMDiff.contMDiffAt heq_z
      have hsmul : laplacian (I := I) (G.connection q₀.1) (G.metric q₀.1) z' q₀.2 =
          Real.exp (-KK * q₀.1) * laplacian (I := I) (G.connection q₀.1) (G.metric q₀.1)
            (fun y : M => bundleInnerScalarization u ν₀ q₀.1 y - c) q₀.2 := by
        have hsm := laplacian_smul_at (I := I) (G.connection q₀.1) (G.metric q₀.1)
          (Real.exp (-KK * q₀.1)) hz'f_near hz'grad
        simpa [z', Pi.smul_def, smul_eq_mul] using hsm
      have haddc : laplacian (I := I) (G.connection q₀.1) (G.metric q₀.1)
          (fun y : M => bundleInnerScalarization u ν₀ q₀.1 y - c) q₀.2 =
          laplacianAt (I := I) G q₀.1 (bundleInnerScalarization u ν₀ q₀.1) q₀.2 := by
        have hg_near : ∀ᶠ y in nhds q₀.2, MDifferentiableAt I 𝓘(Real, Real)
            (bundleInnerScalarization u ν₀ q₀.1) y := by
          have hg := hsol.scalarSliceSmooth ν₀ q₀.1 hq₀carrier
          exact Filter.Eventually.of_forall (fun y => hg.mdifferentiable (by simp) y)
        have hgradg : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric q₀.1)
            (bundleInnerScalarization u ν₀ q₀.1) y) q₀.2 := by
          have hg := hsol.scalarSliceSmooth ν₀ q₀.1 hq₀carrier
          exact gradientFun_mdiffAt (I := I) (G.metric q₀.1) hg q₀.2
        have hadd := laplacian_add_const (I := I) (G.connection q₀.1) (G.metric q₀.1) (-c)
          hg_near hgradg
        simpa [laplacianAt, sub_eq_add_neg, add_comm] using hadd
      calc
        laplacianAt (I := I) G q₀.1 (z q₀.1) q₀.2
            = laplacian (I := I) (G.connection q₀.1) (G.metric q₀.1) (z q₀.1) q₀.2 := by rfl
        _ = laplacian (I := I) (G.connection q₀.1) (G.metric q₀.1) z' q₀.2 := hcongr
        _ = Real.exp (-KK * q₀.1) * laplacian (I := I) (G.connection q₀.1) (G.metric q₀.1)
              (fun y : M => bundleInnerScalarization u ν₀ q₀.1 y - c) q₀.2 := hsmul
        _ = Real.exp (-KK * q₀.1) *
              laplacianAt (I := I) G q₀.1 (bundleInnerScalarization u ν₀ q₀.1) q₀.2 := by
                rw [haddc]
    have hparabolicNonneg : 0 ≤
        Real.exp (-KK * q₀.1) *
          (source q₀.1 q₀.2 (u q₀.1 q₀.2) ν' - support' q₀.1 q₀.2 ν' - KK * ‖ν'‖ ^ 2) := by
      rw [hzlapEq] at hzlap
      rw [hν₀at, hmain] at hztime
      have hL' : laplacianAt (I := I) G q₀.1 (bundleInnerScalarization u ν₀ q₀.1) q₀.2 ≤ 0 := by
        have hpos : 0 < Real.exp (-KK * q₀.1) := Real.exp_pos _
        nlinarith
      nlinarith [hL', hztime, Real.exp_pos (-KK * q₀.1)]
    have hsupp_eq' : support q₀.1 q₀.2 (ν₀ q₀.2) = inner ℝ (ν₀ q₀.2) p := by
      rw [hν₀at]
      exact hsupp_eq
    have hreactionp : source q₀.1 q₀.2 p (ν₀ q₀.2) ≤ support' q₀.1 q₀.2 (ν₀ q₀.2) :=
      htangent q₀.1 hq₀carrier hq₀tpos q₀.2 p hpC (ν₀ q₀.2) (hν₀N q₀.2) hsupp_eq'
    have hRge : 0 ≤ R := by
      have hb := hbound 0 ⟨le_rfl, le_of_lt hT⟩ q₀.2
      exact le_trans (norm_nonneg _) hb
    have hu_ball : u q₀.1 q₀.2 ∈ Metric.closedBall (0 : V q₀.2) (2 * R) := by
      have hb : ‖u q₀.1 q₀.2‖ ≤ 2 * R := by
        have hb0 := hbound q₀.1 hq₀carrier q₀.2
        nlinarith
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm, sub_zero] using hb
    have hp_ball : p ∈ Metric.closedBall (0 : V q₀.2) (2 * R) := by
      have hdist : ‖p‖ ≤ ‖u q₀.1 q₀.2‖ + ‖u q₀.1 q₀.2 - p‖ :=
        norm_le_norm_add_norm_sub (u q₀.1 q₀.2) p
      have hinf : Metric.infDist (u q₀.1 q₀.2) (C q₀.1 q₀.2) ≤ ‖u q₀.1 q₀.2‖ := by
        simpa [dist_eq_norm, sub_zero] using
          Metric.infDist_le_dist_of_mem (x := u q₀.1 q₀.2) (hCzero q₀.1 q₀.2)
      have hdistp : ‖u q₀.1 q₀.2 - p‖ = Metric.infDist (u q₀.1 q₀.2) (C q₀.1 q₀.2) := by
        simpa [ν'] using hdist₀.symm
      have hb : ‖p‖ ≤ 2 * R := by
        have hb0 := hbound q₀.1 hq₀carrier q₀.2
        nlinarith
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm, sub_zero] using hb
    have hLip := (hL q₀.1 hq₀reg q₀.2 (ν₀ q₀.2)).norm_sub_le hu_ball hp_ball
    have hinnerLip : source q₀.1 q₀.2 (u q₀.1 q₀.2) (ν₀ q₀.2) -
        source q₀.1 q₀.2 p (ν₀ q₀.2) ≤ (L : Real) * ‖ν'‖ ^ 2 := by
      have hle' : source q₀.1 q₀.2 (u q₀.1 q₀.2) (ν₀ q₀.2) -
          source q₀.1 q₀.2 p (ν₀ q₀.2) ≤ (L : Real) * ‖ν'‖ * ‖u q₀.1 q₀.2 - p‖ := by
        have habs : |source q₀.1 q₀.2 (u q₀.1 q₀.2) (ν₀ q₀.2) -
            source q₀.1 q₀.2 p (ν₀ q₀.2)| ≤ (L : Real) * ‖ν'‖ * ‖u q₀.1 q₀.2 - p‖ := by
          simpa [hν₀at, mul_assoc, mul_left_comm, mul_comm] using hLip
        exact (abs_le.mp habs).2
      calc
        source q₀.1 q₀.2 (u q₀.1 q₀.2) (ν₀ q₀.2) - source q₀.1 q₀.2 p (ν₀ q₀.2)
            ≤ (L : Real) * ‖ν'‖ * ‖u q₀.1 q₀.2 - p‖ := hle'
        _ = (L : Real) * ‖ν'‖ ^ 2 := by
              rw [show u q₀.1 q₀.2 - p = ν' from rfl]
              ring
    have hreaction : source q₀.1 q₀.2 (u q₀.1 q₀.2) ν' - support' q₀.1 q₀.2 ν' ≤
        (L : Real) * ‖ν'‖ ^ 2 := by
      rw [hν₀at] at hinnerLip hreactionp
      linarith
    have hstrict :
        Real.exp (-KK * q₀.1) *
          (source q₀.1 q₀.2 (u q₀.1 q₀.2) ν' - support' q₀.1 q₀.2 ν' -
            KK * ‖ν'‖ ^ 2) < 0 := by
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
      have hmemC : u T x ∈ C T x := by
        rw [hsupp T x (u T x)]
        intro ν hν
        rcases hflat.exists_flat T x ν hν with
          ⟨ν₀, _hν₀flat, hν₀at, hν₀N, _hν₀norm, _U, _hUopen, _hx₀U, _hflatU⟩
        have h1 : Filter.Tendsto (fun s : Real => support s x (ν₀ x)) (𝓝[<] T)
            (𝓝 (support T x (ν₀ x))) := by
          have hwithin : Filter.Tendsto (fun s : Real => support s x (ν₀ x))
              (𝓝[Set.Icc 0 T] T) (𝓝 (support T x (ν₀ x))) :=
            (hsupport_cont ν₀ x).continuousWithinAt
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
        have h2 : Filter.Tendsto (fun s : Real => inner ℝ (u s x) (ν₀ x))
            (𝓝[<] T) (𝓝 (inner ℝ (u T x) (ν₀ x))) := by
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
          have hcont := (hsol.scalarJointCont ν₀ (T, x)
            ⟨⟨le_of_lt hTpos, le_rfl⟩, Set.mem_univ x⟩)
          simpa [bundleInnerScalarization, real_inner_comm] using hcont.tendsto.comp hpairWithin
        have htend' : Filter.Tendsto
            (fun s : Real => inner ℝ (u s x) (ν₀ x) - support s x (ν₀ x))
            (𝓝[<] T) (𝓝 (inner ℝ (u T x) (ν₀ x) - support T x (ν₀ x))) :=
          h2.sub h1
        have hevent' : ∀ᶠ s in 𝓝[<] T, inner ℝ (u s x) (ν₀ x) - support s x (ν₀ x) ≤ 0 := by
          have hpos : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
          have hpos' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds hpos
          filter_upwards [hpos', self_mem_nhdsWithin] with s hs hslt
          have huC : u s x ∈ C s x := hIco s ⟨le_of_lt hs, hslt⟩ x
          have hle := (hsupp s x (u s x)).mp huC (ν₀ x) (hν₀N x)
          have hle' : inner ℝ (u s x) (ν₀ x) ≤ support s x (ν₀ x) := by
            simpa [real_inner_comm] using hle
          linarith
        have hnonpos : inner ℝ (u T x) (ν₀ x) - support T x (ν₀ x) ≤ 0 :=
          le_of_tendsto htend' hevent'
        have hle' : inner ℝ (u T x) (ν₀ x) ≤ support T x (ν₀ x) := by linarith
        simpa [hν₀at, real_inner_comm] using hle'
      exact hmemC
  · exact hIco t ⟨ht.1, htlt⟩ x

end DifferentialGeometry.Analysis.Parabolic
