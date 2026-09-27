import DifferentialGeometry.Bundle.OrthogonalRightInverse
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.Algebra.Support

noncomputable section
open scoped ContDiff Manifold Topology
open Bundle
open DifferentialGeometry
open DifferentialGeometry.Geometry.VectorBundle

namespace DifferentialGeometry.Geometry.Submersion

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] in
private theorem smooth_frame_section
    (e : Trivialization E (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [MemTrivializationAtlas e] {U : Set M} (hU : U ⊆ e.baseSet)
    {g : M → E} (hg : ContMDiffOn I 𝓘(ℝ, E) ∞ g U) :
    ContMDiffOn I I.tangent ∞
      (fun x ↦ (⟨x, e.symmL ℝ x (g x)⟩ : TangentBundle I M)) U := by
  rw [e.contMDiffOn_iff (fun x hx ↦ e.mem_source.mpr (hU hx))]
  refine ⟨contMDiffOn_id, hg.congr ?_⟩
  intro x hx
  rw [e.symmL_apply (hU hx), e.apply_mk_symm (hU hx)]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_local_horizontal_lift
    (g : SmoothRiemannianMetric I M) (f : M → N) (hf : ContMDiff I J ∞ f)
    (Z : (y : N) → TangentSpace J y)
    (hZ : ContMDiff J J.tangent ∞ (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (x₀ : M) (hsurj : Function.Surjective (mfderiv I J f x₀)) :
    ∃ U ∈ 𝓝 x₀, ∃ X : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) U ∧
      (∀ x ∈ U, mfderiv I J f x (X x) = Z (f x)) ∧
      ∀ x ∈ U, ∀ v, mfderiv I J f x v = 0 → g.inner x (X x) v = 0 := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e' := trivializationAt E' (TangentSpace J : N → Type _) (f x₀)
  let U := e.baseSet ∩ f ⁻¹' e'.baseSet
  have he₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have he'₀ : f x₀ ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' (f x₀)
  have hU : U ∈ 𝓝 x₀ := Filter.inter_mem
    (e.open_baseSet.mem_nhds he₀)
    (hf.continuous.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds he'₀))
  let A : M → E →L[ℝ] E' := fun x ↦
    (e'.continuousLinearMapAt ℝ (f x)).comp
      ((mfderiv I J f x).comp (e.symmL ℝ x))
  have hA : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E') ∞ A U := by
    apply contMDiffOn_clm_apply_iff.mpr
    intro v
    have hs := smooth_frame_section e (U := U) Set.inter_subset_left
      (contMDiffOn_const (c := v))
    have hd := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp_contMDiffOn hs
    have hc := (e'.contMDiffOn (IB := J) (n := ∞)).comp hd
      (fun x hx ↦ e'.mem_source.mpr hx.2)
    exact (contMDiff_snd.comp_contMDiffOn hc).congr (fun x hx ↦
      e'.continuousLinearMapAt_apply_of_mem ℝ hx.2 _)
  have hAsurj : Function.Surjective (A x₀) := by
    let p := e.continuousLinearEquivAt ℝ x₀ he₀
    let q := e'.continuousLinearEquivAt ℝ (f x₀) he'₀
    have h := q.surjective.comp (hsurj.comp p.symm.surjective)
    simpa only [A, p, q, Function.comp_def, ContinuousLinearMap.coe_comp,
      Trivialization.coe_continuousLinearEquivAt_eq,
      Trivialization.symm_continuousLinearEquivAt_eq] using h
  let G : M → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ (g.inner x (e.symmL ℝ x v)).comp (e.symmL ℝ x)
      map_add' := by
        intro v w
        ext u
        simp only [map_add, ContinuousLinearMap.comp_apply, add_apply]
      map_smul' := by
        intro c v
        ext u
        simp only [map_smul, ContinuousLinearMap.comp_apply, smul_apply]
        rfl }
  have hG : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ G U := by
    apply contMDiffOn_clm_apply_iff.mpr
    intro v
    apply contMDiffOn_clm_apply_iff.mpr
    intro w x hx
    have hv := smooth_frame_section e (U := U) Set.inter_subset_left
      (contMDiffOn_const (c := v))
    have hw := smooth_frame_section e (U := U) Set.inter_subset_left
      (contMDiffOn_const (c := w))
    have h1 := ContMDiffWithinAt.clm_bundle_apply (b := id)
      (E₁ := TangentSpace I) (E₂ := fun x ↦ TangentSpace I x →L[ℝ] ℝ)
      (ϕ := g.inner) (v := fun x ↦ e.symmL ℝ x v) (g.contMDiff x).contMDiffWithinAt (hv x hx)
    have h2 := ContMDiffWithinAt.clm_bundle_apply (b := id)
      (E₁ := TangentSpace I) (E₂ := fun _ : M ↦ ℝ)
      (ϕ := fun x ↦ g.inner x (e.symmL ℝ x v)) (v := fun x ↦ e.symmL ℝ x w)
      h1 (hw x hx)
    exact (contMDiffWithinAt_section (F := ℝ) (E := Bundle.Trivial M ℝ)).mp h2
  have hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < G x v v := by
    intro x hx v hv
    apply g.pos
    intro hz
    apply hv
    rw [← e.continuousLinearMapAt_symmL (R := ℝ) hx.1 v, hz, map_zero]
  obtain ⟨V, hV, hVU, R, hR, hright, horth⟩ :=
    exists_contMDiffOn_rightInverse_orthogonal_ker hG hpos hA hU hAsurj
  let z : M → E' := fun x ↦ e'.continuousLinearMapAt ℝ (f x) (Z (f x))
  have hz : ContMDiffOn I 𝓘(ℝ, E') ∞ z V := by
    have hc := (e'.contMDiffOn (IB := J) (n := ∞)).comp
      (hZ.comp hf).contMDiffOn (fun x hx ↦ e'.mem_source.mpr (hVU hx).2)
    exact (contMDiff_snd.comp_contMDiffOn hc).congr (fun x hx ↦
      e'.continuousLinearMapAt_apply_of_mem ℝ (hVU hx).2 _)
  refine ⟨V, hV, (fun x ↦ e.symmL ℝ x (R x (z x))),
    smooth_frame_section e (fun x hx ↦ (hVU hx).1) (hR.clm_apply hz), ?_, ?_⟩
  · intro x hx
    apply (e'.continuousLinearEquivAt ℝ (f x) (hVU hx).2).injective
    simpa only [A, z, ContinuousLinearMap.comp_apply,
      Trivialization.coe_continuousLinearEquivAt_eq] using hright x hx (z x)
  · intro x hx v hv
    let p := e.continuousLinearEquivAt ℝ x (hVU hx).1
    have hp : e.symmL ℝ x (p v) = v := by
      simpa only [p, Trivialization.symm_continuousLinearEquivAt_eq] using p.symm_apply_apply v
    have hk : A x (p v) = 0 := by simp only [A, ContinuousLinearMap.comp_apply, hp, hv, map_zero]
    have hh := horth x hx (z x) (p v) hk
    change g.inner x (e.symmL ℝ x (R x (z x))) (e.symmL ℝ x (p v)) = 0 at hh
    rwa [hp] at hh

set_option backward.isDefEq.respectTransparency false in
theorem exists_unique_smooth_horizontal_lift
    (g : SmoothRiemannianMetric I M) (f : M → N) (hf : ContMDiff I J ∞ f)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x))
    (Z : (y : N) → TangentSpace J y)
    (hZ : ContMDiff J J.tangent ∞ (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N))) :
    ∃! X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ x, mfderiv I J f x (X x) = Z (f x)) ∧
      (∀ x v, mfderiv I J f x v = 0 → g.inner x (X x) v = 0) ∧
      tsupport X ⊆ f ⁻¹' tsupport Z := by
  classical
  choose U hU X hs hr ho using fun x ↦ exists_local_horizontal_lift g f hf Z hZ x (hsurj x)
  let Y : (x : M) → TangentSpace I x := fun x ↦ X x x
  have hrel : ∀ x, mfderiv I J f x (Y x) = Z (f x) := fun x ↦ hr x x (mem_of_mem_nhds (hU x))
  have horth : ∀ x v, mfderiv I J f x v = 0 → g.inner x (Y x) v = 0 :=
    fun x ↦ ho x x (mem_of_mem_nhds (hU x))
  have heq : ∀ x y, y ∈ U x → Y y = X x y := by
    intro x y hy
    exact eq_of_apply_eq_of_orthogonal_ker (V := TangentSpace I y)
      (W := TangentSpace J (f y)) (g.inner y) (g.pos y) (mfderiv I J f y)
      ((hrel y).trans (hr x y hy).symm) (horth y) (ho x y hy)
  have hY : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) := by
    intro x
    apply ((hs x).congr (fun y hy ↦ by rw [heq x y hy])).contMDiffAt (hU x)
  refine ⟨⟨Y, hY⟩, ⟨hrel, horth, ?_⟩, ?_⟩
  · change closure (Function.support Y) ⊆ f ⁻¹' closure (Function.support Z)
    apply closure_minimal _ (isClosed_closure.preimage hf.continuous)
    intro x hx
    apply subset_closure
    intro hz
    apply hx
    exact eq_of_apply_eq_of_orthogonal_ker (V := TangentSpace I x)
      (W := TangentSpace J (f x)) (g.inner x) (g.pos x) (mfderiv I J f x)
      (by rw [hrel, hz]; exact (mfderiv I J f x).map_zero.symm) (horth x)
      (by intro v _; exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ ↦ L v) (g.inner x).map_zero)
  · intro X' hX'
    ext x
    exact eq_of_apply_eq_of_orthogonal_ker (V := TangentSpace I x)
      (W := TangentSpace J (f x)) (g.inner x) (g.pos x) (mfderiv I J f x)
      ((hX'.1 x).trans (hrel x).symm) (hX'.2.1 x) (horth x)

end DifferentialGeometry.Geometry.Submersion
