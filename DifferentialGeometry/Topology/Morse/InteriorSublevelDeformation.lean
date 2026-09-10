import DifferentialGeometry.Topology.Morse.SublevelDeformation
import DifferentialGeometry.Topology.Morse.ModelTransport
import DifferentialGeometry.Topology.Morse.SublevelRestriction

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology.Homotopy
namespace Poincare.Morse
variable {m : ℕ} {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_sublevelHomotopyEquivUnder_of_interiorSublevel
    (e : E ≃L[ℝ] MorseModel (m + 1)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hr : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x)
    (hinterior : sublevel f b ⊆ I.interior M)
    {B : Type*} [TopologicalSpace B] (j : C(B, SublevelSpace f a)) :
    ∃ h : HomotopyEquivUnder ((sublevelInclusion f hab).comp j) j,
      h.invFun = sublevelInclusion f hab := by
  let _ : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let U := Poincare.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let g : U → ℝ := fun x => f x
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.comp contMDiff_subtype_val
  let _ := Poincare.Manifold.interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := Poincare.Manifold.interiorIsManifold I ∞
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g :=
    hgold.comp (Poincare.Manifold.contMDiff_interiorAtlas_id I ∞)
  let J := (𝓘(ℝ, E)).transContinuousLinearEquiv e
  let _ : J.Boundaryless := ⟨by
    rw [ModelWithCorners.transContinuousLinearEquiv_range,
      ModelWithCorners.range_eq_univ, image_univ]
    exact e.surjective.range_eq⟩
  have hgJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ g := by simpa [J] using hg
  have hcompactg : IsCompact (g ⁻¹' Icc a b) := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact
    intro x hx
    exact ⟨⟨x, hinterior hx.2⟩, rfl⟩
  have hrg : ∀ x ∈ g ⁻¹' Icc a b, mfderiv J 𝓘(ℝ, ℝ) g x ≠ 0 := by
    intro x hx hc
    have hxs := (isCriticalPointAt_transContinuousLinearEquiv_iff
      𝓘(ℝ, E) e hg BoundarylessManifold.isInteriorPoint).mp hc
    have hxo := (isCriticalPointAt_interiorAtlas I hgold x).mp hxs
    exact hr x hx ((isCriticalPointAt_openRestriction I hf x x.property).mp hxo)
  have hlo : sublevel f a ⊆ (U : Set M) := fun _ hx => hinterior (hx.trans hab)
  let ea := sublevelRestrictionHomeomorph (U : Set M) f a hlo
  let eb := sublevelRestrictionHomeomorph (U : Set M) f b hinterior
  let ja : C(B, SublevelSpace g a) :=
    (⟨ea.symm, ea.symm.continuous_toFun⟩ : C(SublevelSpace f a, SublevelSpace g a)).comp j
  obtain ⟨h, hi⟩ := exists_sublevelHomotopyEquivUnder J hgJ hab hcompactg hrg ja
  let hup := HomotopyEquivUnder.ofHomeomorph
    ((sublevelInclusion f hab).comp j) ((sublevelInclusion g hab).comp ja) eb.symm
    (by ext x; rfl)
  let hlow := HomotopyEquivUnder.ofHomeomorph ja j ea (by ext x; rfl)
  refine ⟨(hup.trans h rfl).trans hlow rfl, ?_⟩
  simp only [HomotopyEquivUnder.trans_invFun, hi]
  rfl

end Poincare.Morse
