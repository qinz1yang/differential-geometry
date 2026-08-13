import DifferentialGeometry.Analysis.ODE.InvariantSetEquiv
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ProperCone
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SemilinearConvex
import DifferentialGeometry.Geometry.Connection.ParallelTransport.InvariantCone

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH uF

variable {M : Type u}
variable (F : M → Type uF)
  [∀ x, NormedAddCommGroup (F x)]
  [∀ x, InnerProductSpace Real (F x)]

def transportedSectionFamily
    (P : LinearIsometricTransport F) (x₀ : M)
    (u : Real → ∀ x, F x) : Real → M → F x₀ :=
  fun t ↦ P.transportSectionTo F x₀ (u t)

@[simp]
theorem transportedSectionFamily_apply
    (P : LinearIsometricTransport F) (x₀ : M)
    (u : Real → ∀ x, F x) (t : Real) (x : M) :
    transportedSectionFamily F P x₀ u t x = P.transport x x₀ (u t x) :=
  rfl

def transportedReactionFamily
    (P : LinearIsometricTransport F) (x₀ : M)
    (reaction : Real → (x : M) → F x → F x) :
    Real → M → F x₀ → F x₀ :=
  fun t x v ↦ P.transport x x₀ (reaction t x (P.transport x₀ x v))

@[simp]
theorem transportedReactionFamily_apply
    (P : LinearIsometricTransport F) (x₀ : M)
    (reaction : Real → (x : M) → F x → F x)
    (t : Real) (x : M) (v : F x₀) :
    transportedReactionFamily F P x₀ reaction t x v =
      P.transport x x₀ (reaction t x (P.transport x₀ x v)) :=
  rfl

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem parallelProperCone_heat_pot_supersolution_mem_of_potential_le
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (potential : Real → M → Real)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerDualHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G potential (C x₀)
        (transportedSectionFamily F P x₀ u))
    (B : Real)
    (hpotential : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, potential t x ≤ B)
    (hinit : ∀ x : M, u 0 x ∈ C x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C x := by
  have hfixed : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C x₀ := by
    apply properCone_heat_pot_supersolution_mem_of_potential_le
      (I := I) G hT potential (C x₀) (transportedSectionFamily F P x₀ u)
      hsol B hpotential
    intro x
    exact (hC.transport_mem_iff F x x₀ (u 0 x)).2 (hinit x)
  intro t ht x
  apply (hC.transport_mem_iff F x x₀ (u t x)).1
  simpa using hfixed t ht x

omit [CompleteSpace E] in
theorem parallelProperCone_heat_supersolution_mem
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerDualHeatSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G (C x₀)
        (transportedSectionFamily F P x₀ u))
    (hinit : ∀ x : M, u 0 x ∈ C x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C x := by
  exact parallelProperCone_heat_pot_supersolution_mem_of_potential_le
    (I := I) F G hT (fun _ _ ↦ 0) P C hC x₀ u hsol 0 (by simp) hinit

omit [CompleteSpace E] in
theorem parallelProperCone_heat_reaction_mem_of_tangent
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (reaction : Real → (x : M) → F x → F x)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u))
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (htangent : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M, ∀ p ∈ C x,
      reaction t x p ∈ posTangentConeAt (C x : Set (F x)) p)
    (hinit : ∀ x : M, u 0 x ∈ C x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C x := by
  have hfixed : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C x₀ := by
    apply properCone_heat_reaction_mem_of_tangent
      (I := I) G hT (C x₀) (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u) hsol L
    · intro t ht x
      simpa [transportedReactionFamily, Function.comp_def] using
        (P.transport x x₀).lipschitz.comp
          ((hL t ht x).comp (P.transport x₀ x).lipschitz)
    · intro t ht x p hp
      let q : F x := P.transport x₀ x p
      have hq : q ∈ C x := (hC.transport_mem_iff F x₀ x p).2 hp
      have htangentq := htangent t ht x q hq
      have hmapped := ContinuousLinearEquiv.mapsTo_posTangentConeAt
        (P.transport x x₀).toContinuousLinearEquiv htangentq
      have himage : (P.transport x x₀).toContinuousLinearEquiv ''
          (C x : Set (F x)) = (C x₀ : Set (F x₀)) := by
        simpa only using hC.image_transport F x x₀
      rw [himage] at hmapped
      simpa [transportedReactionFamily, q] using hmapped
    · intro x
      exact (hC.transport_mem_iff F x x₀ (u 0 x)).2 (hinit x)
  intro t ht x
  apply (hC.transport_mem_iff F x x₀ (u t x)).1
  simpa using hfixed t ht x

omit [CompleteSpace E] in
theorem parallelProperCone_heat_reaction_mem_of_mapsTo
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (reaction : Real → (x : M) → F x → F x)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u))
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      MapsTo (reaction t x) (C x) (C x))
    (hinit : ∀ x : M, u 0 x ∈ C x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C x := by
  apply parallelProperCone_heat_reaction_mem_of_tangent
    (I := I) F G hT P C hC x₀ reaction u hsol L hL
  · intro t ht x p hp
    have htan := sub_mem_posTangentConeAt_of_segment_subset
      ((C x).convex.segment_subset hp ((C x).add_mem hp (hreaction t ht x hp)))
    simpa using htan
  · exact hinit

omit [CompleteSpace E] in
theorem parallelProperCone_heat_reaction_mem_of_dualZeroFace_nonneg
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (reaction : Real → (x : M) → F x → F x)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerProductHeatReactionOn
      (RealTimeInterval.closed 0 T hT) G
        (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u))
    (L : NNReal)
    (hL : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      LipschitzWith L (reaction t x))
    (hreaction : ∀ t : Real, t ∈ Set.Ioo 0 T → ∀ x : M,
      ∀ φ : StrongDual Real (F x), ProperCone.IsDualElement (C x) φ →
        ∀ p ∈ ProperCone.dualZeroFace (C x) φ, 0 ≤ φ (reaction t x p))
    (hinit : ∀ x : M, u 0 x ∈ C x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C x := by
  have hfixed : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C x₀ := by
    apply properCone_heat_reaction_mem_of_dualZeroFace_nonneg
      (I := I) G hT (C x₀) (transportedReactionFamily F P x₀ reaction)
        (transportedSectionFamily F P x₀ u) hsol L
    · intro t ht x
      simpa [transportedReactionFamily, Function.comp_def] using
        (P.transport x x₀).lipschitz.comp
          ((hL t ht x).comp (P.transport x₀ x).lipschitz)
    · intro t ht x φ hφ p hp
      let e := (P.transport x₀ x).toContinuousLinearEquiv
      let ψ : StrongDual Real (F x) := φ.comp e.symm.toContinuousLinearMap
      have hψ : ProperCone.IsDualElement (C x) ψ := by
        rw [← hC x₀ x]
        exact hφ.comp_symm e
      let q : F x := P.transport x₀ x p
      have hq : q ∈ ProperCone.dualZeroFace (C x) ψ := by
        exact (hC.transport_mem_dualZeroFace_iff F x₀ x φ p).2 hp
      simpa [transportedReactionFamily, e, ψ, q] using
        hreaction t ht x ψ hψ q hq
    · intro x
      exact (hC.transport_mem_iff F x x₀ (u 0 x)).2 (hinit x)
  intro t ht x
  apply (hC.transport_mem_iff F x x₀ (u t x)).1
  simpa using hfixed t ht x

end

end DifferentialGeometry.Analysis.Parabolic
