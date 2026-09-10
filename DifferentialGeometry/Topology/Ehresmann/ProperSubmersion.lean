import DifferentialGeometry.Topology.Ehresmann.RelatedFlows
import DifferentialGeometry.Topology.Ehresmann.SmoothLift
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false

open scoped ContDiff Manifold Topology

namespace Poincare.Topology.Ehresmann

theorem isProperMap_iff_compact_preimage_definition
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [CompactlyCoherentSpace Y] (f : X → Y) :
    IsProperMap f ↔ Continuous f ∧
      ∀ ⦃K : Set Y⦄, IsCompact K → IsCompact (f ⁻¹' K) :=
  isProperMap_iff_isCompact_preimage

theorem isCompact_fiber_of_isProperMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsProperMap f) (y : Y) :
    IsCompact (f ⁻¹' {y}) :=
  hf.isCompact_preimage isCompact_singleton

theorem isCompact_tsupport_of_subset_preimage
    {X Y VX VY : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero VX] [Zero VY]
    (f : X → Y) (Xfield : X → VX) (Yfield : Y → VY)
    (hf : IsProperMap f) (hY : IsCompact (tsupport Yfield))
    (hsupport : tsupport Xfield ⊆ f ⁻¹' tsupport Yfield) :
    IsCompact (tsupport Xfield) :=
  IsCompact.of_isClosed_subset (hf.isCompact_preimage hY)
    (isClosed_tsupport Xfield) hsupport

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

theorem exists_compactlySupported_smoothDerivativeLift_of_local
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (f : M → N) (hf : IsProperMap f)
    (Z : (y : N) → TangentSpace J y) (hZ : IsCompact (tsupport Z))
    (Hloc : ∀ x₀ : M,
      ∃ U ∈ 𝓝 x₀, ∃ Xloc : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent ∞
            (fun x : M ↦ (⟨x, Xloc x⟩ : TangentBundle I M)) U ∧
          (∀ x ∈ U, mfderiv I J f x (Xloc x) = Z (f x)) ∧
          (∀ x ∈ U, Z (f x) = 0 → Xloc x = 0)) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ x, mfderiv I J f x (X x) = Z (f x)) ∧
      tsupport X ⊆ f ⁻¹' tsupport Z ∧ IsCompact (tsupport X) := by
  rcases exists_smoothDerivativeLift_of_local f hf.continuous Z Hloc with
    ⟨X, hrel, hsupp⟩
  exact ⟨X, hrel, hsupp,
    isCompact_tsupport_of_subset_preimage f X Z hf hZ hsupp⟩

theorem exists_compactlySupported_relatedFlow_of_local
    [CompleteSpace E] [FiniteDimensional ℝ E'] [CompleteSpace E']
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]
    (f : M → N) (hf : IsProperMap f) (hfSmooth : ContMDiff I J 1 f)
    (Z : (y : N) → TangentSpace J y)
    (hZsmooth : ContMDiff J J.tangent ∞
      (fun y : N ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (hZcompact : IsCompact (tsupport Z))
    (Hloc : ∀ x₀ : M,
      ∃ U ∈ nhds x₀, ∃ Xloc : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent ∞
            (fun x : M ↦ (⟨x, Xloc x⟩ : TangentBundle I M)) U ∧
          (∀ x ∈ U, mfderiv I J f x (Xloc x) = Z (f x)) ∧
          (∀ x ∈ U, Z (f x) = 0 → Xloc x = 0)) :
    ∃ (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
        (hXcompact : IsCompact (tsupport X)),
      (∀ x, mfderiv I J f x (X x) = Z (f x)) ∧
      tsupport X ⊆ f ⁻¹' tsupport Z ∧
      ∀ (t : ℝ) (x : M),
        f (compactSupportFlowDiffeomorph X X.contMDiff hXcompact t x) =
          compactSupportFlowDiffeomorph Z hZsmooth hZcompact t (f x) := by
  rcases exists_compactlySupported_smoothDerivativeLift_of_local
      f hf Z hZcompact Hloc with ⟨X, hrel, hsupport, hXcompact⟩
  refine ⟨X, hXcompact, hrel, hsupport, ?_⟩
  intro t x
  exact compactSupportFlowDiffeomorph_map_of_mfderiv_eq
    f hfSmooth X X.contMDiff hXcompact Z hZsmooth hZcompact hrel t x

theorem exists_compactlySupported_smoothDerivativeLift_of_surjective
    [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → N) (hf : IsProperMap f) (hfSmooth : ContMDiff I J ∞ f)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x))
    (Z : (y : N) → TangentSpace J y)
    (hZsmooth : ContMDiff J J.tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (hZcompact : IsCompact (tsupport Z)) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ x, mfderiv I J f x (X x) = Z (f x)) ∧
      tsupport X ⊆ f ⁻¹' tsupport Z ∧ IsCompact (tsupport X) :=
  exists_compactlySupported_smoothDerivativeLift_of_local f hf Z hZcompact
    (fun x ↦ exists_local_smoothDerivativeLift_of_surjective
      f hfSmooth Z hZsmooth x (hsurj x))

theorem exists_compactlySupported_relatedFlow_of_surjective
    [CompleteSpace E] [FiniteDimensional ℝ E'] [CompleteSpace E']
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]
    (f : M → N) (hf : IsProperMap f) (hfSmooth : ContMDiff I J ∞ f)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x))
    (Z : (y : N) → TangentSpace J y)
    (hZsmooth : ContMDiff J J.tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (hZcompact : IsCompact (tsupport Z)) :
    ∃ (X : Cₛ^∞⟮I; E, TangentSpace I⟯) (hXcompact : IsCompact (tsupport X)),
      (∀ x, mfderiv I J f x (X x) = Z (f x)) ∧
      tsupport X ⊆ f ⁻¹' tsupport Z ∧
      ∀ (t : ℝ) (x : M),
        f (compactSupportFlowDiffeomorph X X.contMDiff hXcompact t x) =
          compactSupportFlowDiffeomorph Z hZsmooth hZcompact t (f x) :=
  exists_compactlySupported_relatedFlow_of_local f hf (hfSmooth.of_le (by norm_num))
    Z hZsmooth hZcompact (fun x ↦ exists_local_smoothDerivativeLift_of_surjective
      f hfSmooth Z hZsmooth x (hsurj x))

end Poincare.Topology.Ehresmann
