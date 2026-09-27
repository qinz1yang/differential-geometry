import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
private theorem family_contMDiffAt_of_inclusion {U V : TopologicalSpace.Opens M}
    (hUV : U ≤ V) (f : V → ℝ) (x : U)
    (hf : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : U => f (TopologicalSpace.Opens.inclusion hUV y)) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ f (TopologicalSpace.Opens.inclusion hUV x) := by
  classical
  let F : M → ℝ := fun y => if hy : y ∈ V then f ⟨y, hy⟩ else 0
  have hFU : (fun y : U => F (y : M)) =
      (fun y : U => f (TopologicalSpace.Opens.inclusion hUV y)) := by
    funext y
    simp only [F, dif_pos (hUV y.property)]
  have hFV : (fun y : V => F (y : M)) = f := by
    funext y
    simp only [F, dif_pos y.property]
  have hF : ContMDiffAt I 𝓘(ℝ) ∞ F (x : M) := by
    apply contMDiffAt_subtype_iff.mp
    rw [hFU]
    exact hf
  rw [← hFV]
  exact contMDiffAt_subtype_iff.mpr hF

omit [T2Space M] in
private theorem family_contMDiff_tangent_inclusion {U V : TopologicalSpace.Opens M}
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

variable {ι : Type*} (U : ι → Opens M) (g : ∀ i, SmoothRiemannianMetric I (U i))

private def familyInner (x : ↥(⨆ i, U i)) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g (Opens.mem_iSup.mp x.property).choose).inner ⟨x.val, (Opens.mem_iSup.mp x.property).choose_spec⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem familyInner_on
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (x : U i) : familyInner U g (Opens.inclusion (le_iSup U i) x) = (g i).inner x := by
  ext v w
  exact heq _ i x.val _ x.property v w

private theorem familyInner_contMDiff
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : ↥(⨆ i, U i) => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : ↥(⨆ i, U i) => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        x (familyInner U g x)) := by
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : ↥(⨆ i, U i) => TangentSpace I x →L[ℝ] ℝ)
    (φ := familyInner U g)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : ↥(⨆ i, U i) => ℝ) (φ := fun x => familyInner U g x (Y x))
  intro Z
  have hlocal (i : ι) : ContMDiff I 𝓘(ℝ) ∞ (fun x : U i =>
      familyInner U g (Opens.inclusion (le_iSup U i) x)
        (Y (Opens.inclusion (le_iSup U i) x)) (Z (Opens.inclusion (le_iSup U i) x))) := by
    have htotal := ContMDiff.clm_bundle_apply₂
      (E₁ := fun x : U i => TangentSpace I x) (E₂ := fun x : U i => TangentSpace I x)
      (E₃ := fun _ : U i => ℝ) (b := fun x : U i => x) (ψ := (g i).inner)
      (v := fun x => Y (Opens.inclusion (le_iSup U i) x))
      (w := fun x => Z (Opens.inclusion (le_iSup U i) x))
      (g i).contMDiff (family_contMDiff_tangent_inclusion (le_iSup U i) Y)
        (family_contMDiff_tangent_inclusion (le_iSup U i) Z)
    intro x
    have hat := htotal x
    rw [contMDiffAt_totalSpace] at hat
    simp only [familyInner_on U g heq]
    simpa using! hat.2
  have hscalar : ContMDiff I 𝓘(ℝ) ∞ (fun x => familyInner U g x (Y x) (Z x)) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact family_contMDiffAt_of_inclusion (I := I) (U := U i) (V := ⨆ i, U i)
      (le_iSup U i) _ ⟨x.val, hi⟩ (hlocal i).contMDiffAt
  intro x
  rw [contMDiffAt_section]
  refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

def glueMetricFamily
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) :
    SmoothRiemannianMetric I ↥(⨆ i, U i) where
  inner := familyInner U g
  symm x v w := (g (Opens.mem_iSup.mp x.property).choose).symm _ v w
  pos x v hv := (g (Opens.mem_iSup.mp x.property).choose).pos _ v hv
  isVonNBounded x := (g (Opens.mem_iSup.mp x.property).choose).isVonNBounded _
  contMDiff := familyInner_contMDiff U g heq

theorem glueMetricFamily_inner
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (x : U i) (v w : TangentSpace I x) :
    (glueMetricFamily U g heq).inner (Opens.inclusion (le_iSup U i) x) v w = (g i).inner x v w := by
  change familyInner U g _ v w = _
  rw [familyInner_on U g heq]
  rfl

theorem glueMetricFamily_restrict
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) (i : ι) :
    (glueMetricFamily U g heq).restrictOpenOfSubset (le_iSup U i) = g i := by
  apply SmoothRiemannianMetric.ext_inner
  exact glueMetricFamily_inner U g heq i

theorem glueMetricFamily_unique
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (g' : SmoothRiemannianMetric I ↥(⨆ i, U i))
    (h : ∀ (i : ι) (x : U i) (v w : TangentSpace I x),
      g'.inner (Opens.inclusion (le_iSup U i) x) v w = (g i).inner x v w) :
    g' = glueMetricFamily U g heq := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
  exact (h i ⟨x.val, hi⟩ v w).trans (glueMetricFamily_inner U g heq i ⟨x.val, hi⟩ v w).symm

def glueMetricFamilyOn (V : Opens M) (hU : ∀ i, U i ≤ V)
    (hcover : ∀ x : V, ∃ i, x.val ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) : SmoothRiemannianMetric I V := by
  have hsup : (⨆ i, U i) = V := le_antisymm (iSup_le hU) (fun x hx => Opens.mem_iSup.mpr (hcover ⟨x, hx⟩))
  exact hsup ▸ glueMetricFamily U g heq

theorem glueMetricFamilyOn_inner (V : Opens M) (hU : ∀ i, U i ≤ V)
    (hcover : ∀ x : V, ∃ i, x.val ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (x : U i) (v w : TangentSpace I x) :
    (glueMetricFamilyOn U g V hU hcover heq).inner (Opens.inclusion (hU i) x) v w = (g i).inner x v w := by
  have hsup : (⨆ i, U i) = V := le_antisymm (iSup_le hU) (fun x hx => Opens.mem_iSup.mpr (hcover ⟨x, hx⟩))
  subst V
  exact glueMetricFamily_inner U g heq i x v w

end DifferentialGeometry.Geometry.Metric
