import DifferentialGeometry.Tensor.BilinearForm.Coordinates
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

private theorem tangentCoordChange_opens_finite {V : Opens M} (p q x : V)
    (hxp : (x : M) ∈ (chartAt H (p : M)).source) :
    (tangentBundleCore I V).coordChange (achart H p) (achart H q) x
      = (tangentBundleCore I M).coordChange (achart H (p : M)) (achart H (q : M)) (x : M) := by
  rw [tangentBundleCore_coordChange_achart, tangentBundleCore_coordChange_achart]
  have hsrc : x ∈ (chartAt H p).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hxp
  have hval : extChartAt I p x = extChartAt I (p : M) (x : M) := rfl
  have hev : (extChartAt I q ∘ (extChartAt I p).symm)
      =ᶠ[𝓝[Set.range I] extChartAt I (p : M) (x : M)]
      (extChartAt I (q : M) ∘ (extChartAt I (p : M)).symm) := by
    rw [← hval]
    filter_upwards [(chartAt H p).extend_target_mem_nhdsWithin (I := I) hsrc] with y hy
    have hy' : I.symm y ∈ (chartAt H p).target := by
      rw [OpenPartialHomeomorph.extend_target] at hy
      exact hy.1
    have hw : Subtype.val ((chartAt H p).symm (I.symm y))
        = (chartAt H (p : M)).symm (I.symm y) := by
      rw [TopologicalSpace.Opens.chartAt_eq] at hy' ⊢
      exact OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ hy'
    change extChartAt I q ((extChartAt I p).symm y)
        = extChartAt I (q : M) ((extChartAt I (p : M)).symm y)
    have hsy : (extChartAt I p).symm y = ((chartAt H p).symm (I.symm y) : V) := rfl
    have hsy' : (extChartAt I (p : M)).symm y
        = (chartAt H (p : M)).symm (I.symm y) := rfl
    rw [hsy, hsy']
    change I (chartAt H q ((chartAt H p).symm (I.symm y)))
        = I (chartAt H (q : M) ((chartAt H (p : M)).symm (I.symm y)))
    rw [← hw]
    rfl
  exact hev.fderivWithin_eq
    (hev.eq_of_nhdsWithin ⟨(chartAt H (p : M)) (x : M), rfl⟩)


private theorem symmL_opens_eq {V : Opens M} (p x : V)
    (hx : (x : M) ∈ (chartAt H (p : M)).source) :
    (trivializationAt E (TangentSpace I : V → Type _) p).symmL ℝ x =
      (trivializationAt E (TangentSpace I : M → Type _) (p : M)).symmL ℝ (x : M) := by
  have hxu : x ∈ (chartAt H p).source := by
    rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  rw [TangentBundle.symmL_trivializationAt_eq_core hxu,
    TangentBundle.symmL_trivializationAt_eq_core hx]
  exact tangentCoordChange_opens_finite p x x hx

private theorem bilinear_trivialization_opens
    (b : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {V : Opens M} (p x : V) (hx : (x : M) ∈ (chartAt H (p : M)).source) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : V => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) p
      ⟨x, b (x : M)⟩).2 =
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (p : M)
      ⟨(x : M), b (x : M)⟩).2 := by
  have hxu : x ∈ (chartAt H p).source := by
    rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  ext v w
  have h₁ := DifferentialGeometry.BilinearForm.trivializationAt_apply (I := I) p hxu
    (b (x : M)) v w
  have h₂ := DifferentialGeometry.BilinearForm.trivializationAt_apply (I := I) (p : M) hx
    (b (x : M)) v w
  have hv := congrArg (fun L => L v) (symmL_opens_eq (I := I) p x hx)
  have hw := congrArg (fun L => L w) (symmL_opens_eq (I := I) p x hx)
  exact h₁.trans ((congrArg₂ (fun u v => b (x : M) u v) hv hw).trans h₂.symm)

private theorem contMDiffAt_bilinear_of_restrict
    {n : ℕ∞ω} (V : Opens M)
    (b : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : V)
    (hb : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y : V => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : V => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
        y (b (y : M))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
        y (b y)) (x : M) := by
  have hb' := (contMDiffAt_section (IB := I) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun y : V => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (s := fun y => b (y : M)) x).mp hb
  apply (contMDiffAt_section (IB := I) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (s := b) (x : M)).mpr
  apply (contMDiffAt_subtype_iff (U := V) (x := x)).mp
  apply hb'.congr_of_eventuallyEq
  filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
  have hya : (y : M) ∈ (chartAt H (x : M)).source := by
    rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source] at hy
    exact hy
  exact (bilinear_trivialization_opens b x y hya).symm


theorem exists_unique_contMDiffMetric_of_open_cover
    {n : ℕ∞ω} {ι : Type*} (U : ι → Opens M)
    (g : ∀ i, ContMDiffRiemannianMetric I n E (TangentSpace I : U i → Type _))
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j)
      (v w : TangentSpace I x), (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) :
    ∃! G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _),
      ∀ (i : ι) (x : U i) (v w : TangentSpace I (x : M)),
        G.inner (x : M) v w = (g i).inner x v w := by
  classical
  let b : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
    (g (hcover x).choose).inner ⟨x, (hcover x).choose_spec⟩
  have hb (i : ι) (x : U i) : b (x : M) = (g i).inner x := by
    ext v w
    exact heq _ i x.val _ x.property v w
  have hregular : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x (b x)) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    apply contMDiffAt_bilinear_of_restrict (U i) b ⟨x, hi⟩
    simpa only [hb] using (g i).contMDiff.contMDiffAt (x := (⟨x, hi⟩ : U i))
  let G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _) := {
    inner := b
    symm := fun x v w => (g (hcover x).choose).symm _ v w
    pos := fun x v hv => (g (hcover x).choose).pos _ v hv
    isVonNBounded := fun x => (g (hcover x).choose).isVonNBounded _
    contMDiff := hregular }
  have hG : ∀ (i : ι) (x : U i) (v w : TangentSpace I (x : M)),
      G.inner (x : M) v w = (g i).inner x v w := by
    intro i x v w
    exact congrArg (fun B => B v w) (hb i x)
  refine ⟨G, hG, ?_⟩
  intro G' hG'
  have hinner : G'.inner = G.inner := by
    funext x
    obtain ⟨i, hi⟩ := hcover x
    ext v w
    exact (hG' i ⟨x, hi⟩ v w).trans (hG i ⟨x, hi⟩ v w).symm
  cases G' with
  | mk inner symm pos isVonNBounded contMDiff =>
    change inner = b at hinner
    cases hinner
    rfl

end DifferentialGeometry.Geometry.Metric
