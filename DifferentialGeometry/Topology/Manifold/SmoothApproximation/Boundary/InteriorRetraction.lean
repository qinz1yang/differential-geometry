import DifferentialGeometry.Topology.Manifold.Embedding.CompactRetraction
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior

/-!
# Smooth retraction near a compact subset of the interior of a manifold with boundary

`exists_smooth_retraction_near_interior_compact`: let `M` be a compact Hausdorff manifold whose
model may have boundary or corners, `e : M → F` a smooth topological embedding into a
finite-dimensional normed space with injective differential at interior points, and `C ⊆ int M`
compact and nonempty. Then there are an open `U ⊇ e '' C` and a map `r : F → M`, smooth on `U`
with values in `int M`, such that `r (e x) = x` whenever `e x ∈ U`.

Route: the interior `int M` with its boundaryless interior atlas
(`DifferentialGeometry.Manifold.interiorChartedSpace`) satisfies the hypotheses of the tree's
`exists_smooth_neighborhood_retraction_of_isCompact`; differentials are compared by
`mfderiv_interiorAtlas` and `mfderiv_openRestriction`; finally `e '' ∂M` (compact) is removed
from `U`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Smooth retraction onto a manifold with boundary near a compact subset of its interior. -/
theorem exists_smooth_retraction_near_interior_compact {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ x, I.IsInteriorPoint x → Injective (mfderiv I 𝓘(ℝ, F) e x))
    {C : Set M} (hC : IsCompact C) (hCi : C ⊆ I.interior M) (hCne : C.Nonempty) :
    ∃ (r : F → M) (U : Set F), IsOpen U ∧ e '' C ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, F) I ∞ r U ∧ MapsTo r U (I.interior M) ∧
      ∀ x, e x ∈ U → r (e x) = x := by
  have h0 : (∞ : ℕ∞ω) ≠ 0 := by simp
  let U₀ : TopologicalSpace.Opens M := intrinsicInterior I ∞ h0
  obtain ⟨c, hc⟩ := hCne
  let c₀ : U₀ := ⟨c, hCi hc⟩
  have : Nonempty U₀ := ⟨c₀⟩
  let eY : U₀ → F := fun p => e p
  have heY : ContMDiff I 𝓘(ℝ, F) ∞ eY := he.comp contMDiff_subtype_val
  let _ := interiorChartedSpace I ∞ (M := U₀)
  have : IsManifold 𝓘(ℝ, E) ∞ U₀ := interiorIsManifold I ∞
  have heY' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ eY :=
    he.comp (contMDiff_intrinsicInterior_val I ∞ h0)
  have hembY : _root_.Topology.IsEmbedding eY := hemb.comp _root_.Topology.IsEmbedding.subtypeVal
  have hiY : ∀ p : U₀, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) eY p) := by
    intro p
    have h1 := mfderiv_interiorAtlas I (M := U₀) heY p
    have h2 := mfderiv_openRestriction I (U := U₀) he p p.property
    simp only at h1 h2
    have key : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) eY p : E →L[ℝ] F) = (mfderiv I 𝓘(ℝ, F) e p : E →L[ℝ] F) :=
      h1.trans h2
    have hinj := hi p p.property
    intro v w hvw
    apply hinj
    have hv := DFunLike.congr_fun key v
    have hw := DFunLike.congr_fun key w
    exact hv.symm.trans (hvw.trans hw)
  have hK : IsCompact ((Subtype.val : U₀ → M) ⁻¹' C) :=
    _root_.Topology.IsEmbedding.subtypeVal.isCompact_preimage_iff
      (by rw [Subtype.range_coe]; exact hCi) |>.mpr hC
  obtain ⟨rY, U, hU, hKU, hrY, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction_of_isCompact
      heY' hembY hiY hK
  let r : F → M := fun z => (rY z : M)
  have hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U :=
    (contMDiff_intrinsicInterior_val I ∞ h0).comp_contMDiffOn hrY
  have hbc : IsCompact (e '' I.boundary M) :=
    ((I.isClosed_boundary h0).isCompact).image he.continuous
  refine ⟨r, U \ e '' I.boundary M, hU.sdiff hbc.isClosed, ?_, hr.mono sdiff_subset,
    fun z _ => (rY z).property, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨hKU ⟨⟨x, hCi hx⟩, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, hyx⟩
    have := hemb.injective hyx
    subst this
    exact (I.isInteriorPoint_iff_not_isBoundaryPoint y).mp (hCi hx) hy
  · intro x hx
    have hxi : I.IsInteriorPoint x := by
      rw [I.isInteriorPoint_iff_not_isBoundaryPoint]
      exact fun hb => hx.2 ⟨x, hb, rfl⟩
    exact congrArg Subtype.val (hleft ⟨x, hxi⟩ hx.1)

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
