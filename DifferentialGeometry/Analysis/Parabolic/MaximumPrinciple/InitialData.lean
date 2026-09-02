import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.BoundaryHopf
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ScalarStrong

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem scalar_heat_positive_of_initial_point
    [I.Boundaryless]
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
        ΔG (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {c : M} (hc : 0 < u 0 c) :
    ∀ y : M, 0 < u T y := by
  let τ : Real := T / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    linarith
  have hτT : τ ≤ T := by
    dsimp [τ]
    linarith
  have hτmem : τ ∈ Set.Icc (0 : Real) T := ⟨hτ.le, hτT⟩
  have hu_contτ : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) τ) := by
    apply hu_cont.mono
    intro p hp
    rw [spacetimeSlab] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hτT⟩, hp.2⟩
  have hu_nonnegτ : ∀ t ∈ Set.Icc 0 τ, ∀ x : M, 0 ≤ u t x := by
    intro t ht x
    exact hu_nonneg t ⟨ht.1, ht.2.trans hτT⟩ x
  have hu_timeτ : ∀ t ∈ Set.Icc 0 τ, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 τ) t := by
    intro t ht htpos x
    exact (hu_time t ⟨ht.1, ht.2.trans hτT⟩ htpos x).mono
      (Set.Icc_subset_Icc_right hτT)
  have hu_spaceτ : ∀ t ∈ Set.Icc 0 τ, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t) := by
    intro t ht htpos
    exact hu_space t ⟨ht.1, ht.2.trans hτT⟩ htpos
  have hu_superτ : ∀ (t : Real) (ht : t ∈ Set.Icc 0 τ) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 τ) t -
        ΔG (I := I) g ⟨u t, hu_spaceτ t ht htpos⟩ x := by
    intro t ht htpos x
    have htT : t ∈ Set.Icc (0 : Real) T := ⟨ht.1, ht.2.trans hτT⟩
    have hderiv : derivWithin (fun s => u s x) (Set.Icc 0 τ) t =
        derivWithin (fun s => u s x) (Set.Icc 0 T) t := by
      exact derivWithin_subset (Set.Icc_subset_Icc le_rfl hτT)
        ((uniqueDiffOn_Icc hτ).uniqueDiffWithinAt ht)
        (hu_time t htT htpos x)
    rw [hderiv]
    simpa using hu_super t htT htpos x
  have hτzero : ∃ x : M, 0 < u τ x := by
    by_contra hnot
    have hzero : ∀ x : M, u τ x = 0 := by
      intro x
      have hle : u τ x ≤ 0 := le_of_not_gt (fun hx => hnot ⟨x, hx⟩)
      exact le_antisymm hle (hu_nonnegτ τ ⟨hτ.le, le_rfl⟩ x)
    have hpast := scalar_strong_maximum_principle_fixed_metric (I := I)
      g hτ u hu_contτ hu_nonnegτ hu_timeτ hu_spaceτ hu_superτ
      (y := c) (hzero c)
    have hczero : u 0 c = 0 := hpast 0 ⟨le_rfl, hτ.le⟩ c
    linarith
  obtain ⟨xτ, hxτ⟩ := hτzero
  intro y
  exact scalar_strong_maximum_principle_fixed_metric_positive (I := I)
    g hT u hu_cont hu_nonneg hu_time hu_space hu_super hτmem hxτ y

section Dirichlet

theorem scalar_dirichlet_solution_nonnegative
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real → (x : M) → TangentSpace I x)
    (a : Real) (ha : 0 ≤ a)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_initial : ∀ x : M, 0 ≤ u 0 x)
    (hu_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      u t (p : M) = 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_equation : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G T X u t x = -a * u t x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x := by
  apply strict_barrier_on_compact_manifold_with_boundary
    (I := I) G T X u hu_cont hu_initial
  · intro t ht p
    rw [hu_boundary t ht p]
  · exact hu_time
  · exact hu_mdiff
  · exact hu_grad
  · intro t ht htpos x hx hneg
    rw [hu_equation t ht htpos x hx]
    simpa only [mul_neg, neg_mul] using
      mul_nonneg ha (neg_nonneg.mpr hneg.le)

end Dirichlet

end

end DifferentialGeometry.Analysis.Parabolic
