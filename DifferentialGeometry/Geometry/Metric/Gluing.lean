import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
private theorem contMDiffAt_of_inclusion {U V : TopologicalSpace.Opens M}
    (hUV : U ≤ V) (f : V → ℝ) (x : U)
    (hf : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : U => f (TopologicalSpace.Opens.inclusion hUV y)) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ f (TopologicalSpace.Opens.inclusion hUV x) := by
  classical
  let F : M → ℝ := fun y => if hy : y ∈ V then f ⟨y, hy⟩ else 0
  have hFU : (fun y : U => F (y : M)) =
      (fun y : U => f (TopologicalSpace.Opens.inclusion hUV y)) := by
    funext y
    simp only [F, dite_eq_left (hUV y.property)]
  have hFV : (fun y : V => F (y : M)) = f := by
    funext y
    simp only [F, dite_eq_left y.property]
  have hF : ContMDiffAt I 𝓘(ℝ) ∞ F (x : M) := by
    apply contMDiffAt_subtype_iff.mp
    rw [hFU]
    exact hf
  rw [← hFV]
  exact contMDiffAt_subtype_iff.mpr hF

omit [T2Space M] in
private theorem contMDiff_tangent_inclusion {U V : TopologicalSpace.Opens M}
    (hUV : U ≤ V)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : V → Type _)) :
    ContMDiff I I.tangent ∞
      (fun y : U => (⟨y, Y (TopologicalSpace.Opens.inclusion hUV y)⟩ : TangentBundle I U)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hinv : ∀ y : U,
      (mfderiv I I (TopologicalSpace.Opens.inclusion hUV : U → V) y).IsInvertible := by
    intro y
    rw [mfderiv_opens_incl]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E)
  have hpb := Y.contMDiff.mpullback_vectorField
    (f := TopologicalSpace.Opens.inclusion hUV) (contMDiff_inclusion hUV) hinv
    (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  have heq : ∀ y : U,
      VectorField.mpullback I I (TopologicalSpace.Opens.inclusion hUV)
        (fun z : V => Y z) y = Y (TopologicalSpace.Opens.inclusion hUV y) := by
    intro y
    apply (hinv y).inverse_apply_eq.mpr
    rw [mfderiv_opens_incl]
    rfl
  simpa only [heq] using hpb

private def gluedInner (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (x : ↥(U ⊔ V)) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := by
  classical
  exact if hxU : (x : M) ∈ U then gU.inner ⟨x, hxU⟩
    else gV.inner ⟨x, x.property.resolve_left hxU⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem gluedInner_of_left (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (x : ↥(U ⊔ V)) (hx : (x : M) ∈ U) :
    gluedInner U V gU gV x = gU.inner ⟨x, hx⟩ := by
  classical
  exact dite_eq_left hx

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem gluedInner_of_not_left (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (x : ↥(U ⊔ V)) (hx : (x : M) ∉ U) :
    gluedInner U V gU gV x = gV.inner ⟨x, x.property.resolve_left hx⟩ := by
  classical
  exact dite_eq_right hx

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem gluedInner_left (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (x : U) : gluedInner U V gU gV (TopologicalSpace.Opens.inclusion le_sup_left x) = gU.inner x :=
  gluedInner_of_left U V gU gV _ x.property

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem gluedInner_right (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w)
    (x : V) : gluedInner U V gU gV (TopologicalSpace.Opens.inclusion le_sup_right x) = gV.inner x := by
  classical
  by_cases hxU : (x : M) ∈ U
  · refine (gluedInner_of_left U V gU gV _ hxU).trans ?_
    ext v w
    exact heq x hxU x.property v w
  · exact gluedInner_of_not_left U V gU gV _ hxU

private theorem gluedInner_contMDiff (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : ↥(U ⊔ V) => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : ↥(U ⊔ V) => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        x (gluedInner U V gU gV x)) := by
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : ↥(U ⊔ V) => TangentSpace I x →L[ℝ] ℝ)
    (φ := gluedInner U V gU gV)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : ↥(U ⊔ V) => ℝ) (φ := fun x => gluedInner U V gU gV x (Y x))
  intro Z
  have hlocal : ∀ (O : TopologicalSpace.Opens M) (hO : O ≤ U ⊔ V)
      (gO : SmoothRiemannianMetric I O)
      (hOeq : ∀ x : O, gluedInner U V gU gV (TopologicalSpace.Opens.inclusion hO x) = gO.inner x),
      ContMDiff I 𝓘(ℝ) ∞ (fun x : O =>
        gluedInner U V gU gV (TopologicalSpace.Opens.inclusion hO x)
          (Y (TopologicalSpace.Opens.inclusion hO x))
          (Z (TopologicalSpace.Opens.inclusion hO x))) := by
    intro O hO gO hOeq
    have htotal := ContMDiff.clm_bundle_apply₂
      (E₁ := fun x : O => TangentSpace I x) (E₂ := fun x : O => TangentSpace I x)
      (E₃ := fun _ : O => ℝ) (b := fun x : O => x) (ψ := gO.inner)
      (v := fun x => Y (TopologicalSpace.Opens.inclusion hO x))
      (w := fun x => Z (TopologicalSpace.Opens.inclusion hO x))
      gO.contMDiff (contMDiff_tangent_inclusion hO Y) (contMDiff_tangent_inclusion hO Z)
    intro x
    have hat := htotal x
    rw [contMDiffAt_totalSpace] at hat
    simp only [hOeq]
    simpa using! hat.2
  have hscalar : ContMDiff I 𝓘(ℝ) ∞ (fun x => gluedInner U V gU gV x (Y x) (Z x)) := by
    intro x
    rcases x.property with hx | hx
    · exact contMDiffAt_of_inclusion (I := I) (U := U) (V := U ⊔ V) le_sup_left _ ⟨(x : M), hx⟩
        ((hlocal U le_sup_left gU (gluedInner_left U V gU gV)).contMDiffAt)
    · exact contMDiffAt_of_inclusion (I := I) (U := V) (V := U ⊔ V) le_sup_right _ ⟨(x : M), hx⟩
        ((hlocal V le_sup_right gV (gluedInner_right U V gU gV heq)).contMDiffAt)
  intro x
  rw [contMDiffAt_section]
  refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

def glueMetric (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w) :
    SmoothRiemannianMetric I ↥(U ⊔ V) where
  inner := gluedInner U V gU gV
  symm x v w := by
    classical
    by_cases hx : (x : M) ∈ U
    · rw [gluedInner_of_left U V gU gV x hx]
      exact gU.symm ⟨x, hx⟩ v w
    · rw [gluedInner_of_not_left U V gU gV x hx]
      exact gV.symm ⟨x, x.property.resolve_left hx⟩ v w
  pos x v hv := by
    classical
    by_cases hx : (x : M) ∈ U
    · rw [gluedInner_of_left U V gU gV x hx]
      exact gU.pos ⟨x, hx⟩ v hv
    · rw [gluedInner_of_not_left U V gU gV x hx]
      exact gV.pos ⟨x, x.property.resolve_left hx⟩ v hv
  isVonNBounded x := by
    classical
    by_cases hx : (x : M) ∈ U
    · rw [gluedInner_of_left U V gU gV x hx]
      exact gU.isVonNBounded ⟨x, hx⟩
    · rw [gluedInner_of_not_left U V gU gV x hx]
      exact gV.isVonNBounded ⟨x, x.property.resolve_left hx⟩
  contMDiff := gluedInner_contMDiff U V gU gV heq

theorem glueMetric_inner_left (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w)
    (x : U) (v w : TangentSpace I x) :
    (glueMetric U V gU gV heq).inner (TopologicalSpace.Opens.inclusion le_sup_left x) v w =
      gU.inner x v w := by
  change gluedInner U V gU gV _ v w = _
  rw [gluedInner_left]
  rfl

theorem glueMetric_inner_right (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w)
    (x : V) (v w : TangentSpace I x) :
    (glueMetric U V gU gV heq).inner (TopologicalSpace.Opens.inclusion le_sup_right x) v w =
      gV.inner x v w := by
  change gluedInner U V gU gV _ v w = _
  rw [gluedInner_right U V gU gV heq]
  rfl

theorem glueMetric_restrict_left (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w) :
    (glueMetric U V gU gV heq).restrictOpenOfSubset le_sup_left = gU := by
  apply SmoothRiemannianMetric.ext_inner
  exact glueMetric_inner_left U V gU gV heq

theorem glueMetric_restrict_right (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w) :
    (glueMetric U V gU gV heq).restrictOpenOfSubset le_sup_right = gV := by
  apply SmoothRiemannianMetric.ext_inner
  exact glueMetric_inner_right U V gU gV heq

end DifferentialGeometry.Geometry.Metric
