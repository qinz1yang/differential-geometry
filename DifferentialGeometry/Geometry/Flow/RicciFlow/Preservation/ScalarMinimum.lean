import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M]

theorem scalar_lower_bound_of_compact
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b c : ℝ}
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hinit : ∀ x : M, c ≤ S.scalar a x) :
    ∀ t ∈ Icc a b, ∀ x : M, c ≤ S.scalar t x := by
  let S' := S.timeShift a
  have hS' : IsSolutionOn S' := isSolutionOn_timeShift hS a
  let T := b - a
  let G := flowG S'
  have hslab' : Icc 0 T ⊆ (D.timeShift a).carrier := by
    intro t ht
    exact hslab ⟨by dsimp [T] at ht; linarith [ht.1],
      by dsimp [T] at ht; linarith [ht.2]⟩
  have hregular' : Ioo 0 T ⊆ (D.timeShift a).regular := by
    intro t ht
    exact hregular ⟨by dsimp [T] at ht; linarith [ht.1],
      by dsimp [T] at ht; linarith [ht.2]⟩
  let w := fun t x => S'.scalar t x - c
  have hwcont : ContinuousOn (fun p : ℝ × M => w p.1 p.2) (spacetimeSlab T) :=
    (hS'.scalarCont.mono (prod_mono hslab' subset_rfl)).sub continuousOn_const
  have hwinit (x : M) : 0 ≤ w 0 x := by
    simpa [w, S'] using sub_nonneg.mpr (hinit x)
  have htime (t : ℝ) (ht : t ∈ Ioo 0 T) (x : M) :
      DifferentiableWithinAt ℝ (fun s => S'.scalar s x) (Icc 0 T) t :=
    scalarTimeOfSolution S' hS' (K := Icc 0 T) ⟨ht.1.le, ht.2.le⟩ hslab' x
  have hspace (t : ℝ) (x : M) :
      MDifferentiableAt I 𝓘(ℝ, ℝ) (S'.scalar t) x :=
    (scalarSmoothOfSolution S' t).mdifferentiableAt (by simp)
  have hparabolic (t : ℝ) (ht : t ∈ Ioo 0 T) (x : M) :
      0 ≤ parabolicOperatorWithDrift G T (fun _ _ => 0) w t x := by
    have hT : 0 < T := ht.1.trans ht.2
    have huniq := (uniqueDiffOn_Icc hT) t ⟨ht.1.le, ht.2.le⟩
    have hevolution := scalar_curvature_evolution S' hS' ⟨t, hregular' ht⟩ x
    have hd : derivWithin (fun r => S'.scalar r x) (Icc 0 T) t =
        laplacianAt G t (S'.scalar t) x +
          2 * normSq0S (S'.family.metric t) x 2 (S'.ricci t x) :=
      (hevolution.mono hslab').derivWithin huniq
    have hw := parabolic_sub_time_curve_identity G T (fun _ _ => 0)
      S'.scalar (fun _ => c) t (hspace t) x (htime t ht x)
      (differentiableWithinAt_const c)
    change 0 ≤ parabolicOperatorWithDrift G T (fun _ _ => 0)
      (fun s y => S'.scalar s y - c) t x
    have hconst : derivWithin (fun _ : ℝ => c) (Icc 0 T) t = 0 :=
      (hasDerivWithinAt_const (x := t) (s := Icc 0 T) (c := c)).derivWithin huniq
    rw [hw, hconst, sub_zero, parabolicOperatorWithDrift_eq, hd,
      heatOperatorWithDrift_zero_drift]
    have hn := normSq0S_nonneg (S'.family.metric t) x 2 (S'.ricci t x)
    change 0 ≤ laplacianAt G t (S'.scalar t) x + 2 * _ -
      laplacianAt G t (S'.scalar t) x
    linarith only [hn]
  have hw := strict_barrier_nonnegative_of_positive_time_interior G T (fun _ _ => 0) w
    hwcont hwinit
    (fun t ht x => (htime t ht x).sub_const c)
    (fun t _ x => (hspace t x).sub mdifferentiableAt_const)
    (fun t _ x => gradientFun_mdiffAt (G.metric t)
      ((scalarSmoothOfSolution S' t).sub contMDiff_const) x)
    (fun t ht x _ => hparabolic t ht x)
  intro t ht x
  have hw' := hw (t - a) ⟨by linarith [ht.1], by dsimp [T]; linarith [ht.2]⟩ x
  simpa [w, S', sub_nonneg] using hw'

theorem exists_scalar_le_at_earlier_time_of_compact
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b : ℝ} (hab : a ≤ b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (y : M) :
    ∃ x : M, S.scalar a x ≤ S.scalar b y := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn ⟨y, mem_univ y⟩
    (scalarSmoothOfSolution S a).continuous.continuousOn
  exact ⟨x, scalar_lower_bound_of_compact S hS hslab hregular
    (fun z => hx (mem_univ z)) b ⟨hab, le_rfl⟩ y⟩

end DifferentialGeometry.PDE.RicciFlow
