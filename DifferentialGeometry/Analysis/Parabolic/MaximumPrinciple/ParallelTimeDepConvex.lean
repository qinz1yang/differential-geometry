import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ConvexTimeDep
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ParallelCone

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u uE uH uF

variable {M : Type u}
variable (F : M → Type uF)
  [∀ x, NormedAddCommGroup (F x)]
  [∀ x, InnerProductSpace Real (F x)]

def IsParallelTimeDepConvexFamily
    (P : LinearIsometricTransport F)
    (C : Real → (x : M) → Set (F x)) : Prop :=
  ∀ t x y, P.transport x y '' (C t x) = C t y

namespace IsParallelTimeDepConvexFamily

variable {F} {P : LinearIsometricTransport F} {C : Real → (x : M) → Set (F x)}

theorem transport_mem_iff
    (h : IsParallelTimeDepConvexFamily F P C)
    (t : Real) (x y : M) (v : F x) :
    P.transport x y v ∈ C t y ↔ v ∈ C t x := by
  constructor
  · intro hv
    have hxy : P.transport y x (P.transport x y v) ∈ C t x := by
      have hmem : P.transport x y v ∈ P.transport x y '' (C t x) := by
        rw [h t x y]
        exact hv
      rcases hmem with ⟨w, hw, hEq⟩
      have hvw : P.transport y x (P.transport x y v) = w := by
        calc
          P.transport y x (P.transport x y v) = P.transport y x (P.transport x y w) := by rw [hEq]
          _ = w := by
            have htrans : P.transport y x (P.transport x y w) = P.transport x x w := by
              change ((P.transport x y).trans (P.transport y x)) w = (P.transport x x) w
              rw [P.transport_trans x y x]
            rw [htrans, P.transport_refl x]
            rfl
      simpa [hvw] using hw
    simpa using hxy
  · intro hv
    rw [← h t x y]
    exact ⟨v, hv, rfl⟩

theorem mapsTo_transport
    (h : IsParallelTimeDepConvexFamily F P C)
    (t : Real) (x y : M) :
    MapsTo (P.transport x y) (C t x) (C t y) := by
  intro v hv
  exact (h.transport_mem_iff t x y v).2 hv

end IsParallelTimeDepConvexFamily

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parallelTimeDepConvex_heat_reaction_mem_of_support_family
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (P : LinearIsometricTransport F) (x₀ : M)
    (C : Real → (x : M) → Set (F x))
    (hC : IsParallelTimeDepConvexFamily F P C)
    (support : Real → F x₀ → Real)
    (hsupp : IsConvexSupportFamily (fun t => C t x₀) support)
    (reaction : Real → (x : M) → F x → F x)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT.le) G
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u))
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      t ∈ (RealTimeInterval.closed 0 T hT.le).regular)
    (hsupport_cont : ∀ ν : F x₀,
      ContinuousOn (fun t : Real => support t ν) (Set.Icc 0 T))
    (hsupport_time : ∀ ν : F x₀, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t →
      DifferentiableWithinAt Real (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F x, ∀ ν : F x₀,
      inner Real (reaction t x p) (P.transport x₀ x ν) ≤
        derivWithin (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hinit : ∀ x : M, u 0 x ∈ C 0 x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t x := by
  have hfixed : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C t x₀ := by
    apply closed_convex_timeDep_heat_reaction_mem_of_support_family
      (I := I) (M := M) G hT (fun t => C t x₀) support hsupp
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u) hsol hregular
      hsupport_cont hsupport_time
    · intro t ht x p ν
      have hreaction' := hreaction t ht x (P.transport x₀ x p) ν
      have hinner : inner ℝ (P.transport x x₀ (reaction t x (P.transport x₀ x p))) ν =
          inner ℝ (reaction t x (P.transport x₀ x p)) (P.transport x₀ x ν) := by
        have hmap := (P.transport x x₀).inner_map_map
          (reaction t x (P.transport x₀ x p)) (P.transport x₀ x ν)
        simpa [P.transport_trans_apply F x₀ x x₀] using hmap
      simpa [transportedReactionFamily, hinner] using hreaction'
    · intro x
      exact (hC.transport_mem_iff 0 x x₀ (u 0 x)).2 (hinit x)
  intro t ht x
  exact (hC.transport_mem_iff t x x₀ (u t x)).1 (hfixed t ht x)


theorem parallelTimeDepConvex_heat_reaction_mem_of_tangent
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F) (x₀ : M)
    (C : Real → (x : M) → Set (F x))
    (hC : IsParallelTimeDepConvexFamily F P C)
    (K : Set (WithLp 2 (F x₀ × ℝ)))
    (hK_eq : K = {q : WithLp 2 (F x₀ × ℝ) |
      (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧ (WithLp.ofLp q).1 ∈ C (WithLp.ofLp q).2 x₀})
    (hKne : K.Nonempty) (hKclosed : IsClosed K) (hKconvex : Convex Real K)
    (reaction : Real → (x : M) → F x → F x)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u))
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (fun q : WithLp 2 (F x₀ × ℝ) =>
        WithLp.toLp 2 (transportedReactionFamily F P x₀ reaction (WithLp.ofLp q).2 x
          (WithLp.ofLp q).1, (1 : Real))))
    (htangent : ∀ τ : Real, τ ∈ Set.Ico 0 T → ∀ x : M, ∀ p : F x₀, p ∈ C τ x₀ →
      WithLp.toLp 2 (transportedReactionFamily F P x₀ reaction τ x p, (1 : Real)) ∈
        posTangentConeAt K (WithLp.toLp 2 (p, τ)))
    (htangent_fiber : ∀ τ : Real, τ ∈ Set.Icc 0 T → ∀ x : M, ∀ p : F x₀, p ∈ C τ x₀ →
      transportedReactionFamily F P x₀ reaction τ x p ∈ posTangentConeAt (C τ x₀) p)
    (hinit : ∀ x : M, u 0 x ∈ C 0 x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t x := by
  have hfixed : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C t x₀ := by
    apply closed_convex_heat_reaction_mem_of_timeDep_tangent
      (I := I) (M := M) G hT (fun τ => C τ x₀) K hK_eq hKne hKclosed hKconvex
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u) hsol L hL htangent htangent_fiber
    intro x
    exact (hC.transport_mem_iff 0 x x₀ (u 0 x)).2 (hinit x)
  intro t ht x
  exact (hC.transport_mem_iff t x x₀ (u t x)).1 (hfixed t ht x)

theorem parallelTimeDepConvex_heat_reaction_mem_of_supporting_normal
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F) (x₀ : M)
    (C : Real → (x : M) → Set (F x))
    (hC : IsParallelTimeDepConvexFamily F P C)
    (support : Real → F x₀ → Real)
    (hsupp : ∀ t : Real, ∀ p : F x₀,
      p ∈ C t x₀ ↔ ∀ ν : F x₀, inner ℝ ν p ≤ support t ν)
    (h0 : ∀ t : Real, support t 0 = 0)
    (hsupport_time : ∀ ν : F x₀, ∀ t : Real, t ∈ Set.Icc 0 T →
      DifferentiableWithinAt Real (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (reaction : Real → (x : M) → F x → F x)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u))
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (transportedReactionFamily F P x₀ reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p : F x₀,
      ∀ ν : F x₀, ν ≠ 0 → inner ℝ ν p = support t ν →
        inner ℝ ν (transportedReactionFamily F P x₀ reaction t x p) ≤
          derivWithin (fun s : Real => support s ν) (Set.Icc 0 T) t)
    (hinit : ∀ x : M, u 0 x ∈ C 0 x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C t x := by
  have hfixed : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C t x₀ := by
    apply closed_convex_timeDep_heat_reaction_mem_of_supporting_normal
      (I := I) (M := M) G hT (fun t => C t x₀) support hsupp h0 hsupport_time
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u) hsol L hL hreaction
    · intro x
      exact (hC.transport_mem_iff 0 x x₀ (u 0 x)).2 (hinit x)
  intro t ht x
  exact (hC.transport_mem_iff t x x₀ (u t x)).1 (hfixed t ht x)


end DifferentialGeometry.Analysis.Parabolic

end
