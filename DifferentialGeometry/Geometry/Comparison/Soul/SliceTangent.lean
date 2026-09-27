import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSlice
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

noncomputable section

open Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]



private theorem mem_of_hasDerivAt_of_eventually {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {p : Submodule ℝ F} (hp : IsClosed (p : Set F)) {γ : ℝ → F}
    {c : F} (hγ : HasDerivAt γ c 0)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t - γ 0 ∈ p) : c ∈ p := by
  have hmono : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ fun t ht => ne_of_gt ht
  refine hp.mem_of_tendsto (hγ.tendsto_slope.mono_left hmono) ?_
  filter_upwards [h] with t ht
  have hslope : slope γ 0 t = (t - 0)⁻¹ • (γ t - γ 0) := by
    rw [slope_def_module]
  rw [hslope]
  exact p.smul_mem _ ht



def IsSliceVelocity (I : ModelWithCorners ℝ E H) (S : Set M) (x : M)
    (v : TangentSpace I x) : Prop :=
  ∃ f : ℝ → M, f 0 = x ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ S) ∧
    MDifferentiableAt 𝓘(ℝ, ℝ) I f 0 ∧
    mfderiv 𝓘(ℝ, ℝ) I f 0 (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ)) = v

def sliceTangent (I : ModelWithCorners ℝ E H) (S : Set M) (x : M) :
    Submodule ℝ (TangentSpace I x) :=
  Submodule.span ℝ {v : TangentSpace I x | IsSliceVelocity I S x v}

theorem mem_sliceTangent_of_curve {S : Set M} {x : M} {f : ℝ → M} (h0 : f 0 = x)
    (hS : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ S)
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f 0) :
    (mfderiv 𝓘(ℝ, ℝ) I f 0 (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ)) :
      TangentSpace I x) ∈ sliceTangent I S x :=
  Submodule.subset_span ⟨f, h0, hS, hf, rfl⟩


theorem sliceTangent_mono {S T : Set M} (h : S ⊆ T) (x : M) :
    sliceTangent I S x ≤ sliceTangent I T x := by
  apply Submodule.span_mono
  rintro v ⟨f, h0, hS, hf, hv⟩
  exact ⟨f, h0, hS.mono fun t ht => h ht, hf, hv⟩



private theorem mfderiv_symm_apply_mfderiv
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} {x : M} (hxc : x ∈ c.source)
    (v : TangentSpace I x) :
    mfderiv 𝓘(ℝ, E) I c.symm (c x) (mfderiv I 𝓘(ℝ, E) c x v) = v := by
  have hcdiff : MDifferentiableAt I 𝓘(ℝ, E) c x := c.mdifferentiableAt (by simp) hxc
  have hcx : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I c.symm (c x) :=
    c.symm.mdifferentiableAt (by simp) hcx
  have hcomp : mfderiv I I (fun y : M => c.symm (c y)) x =
      (mfderiv 𝓘(ℝ, E) I c.symm (c x)).comp (mfderiv I 𝓘(ℝ, E) c x) :=
    mfderiv_comp x hsymm hcdiff
  have heq : (fun y : M => c.symm (c y)) =ᶠ[𝓝 x] id := by
    filter_upwards [c.open_source.mem_nhds hxc] with y hy
    exact c.toPartialEquiv.left_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hcomp.symm

theorem sliceTangent_eq_comap {S : Set M} {x : M} (hx : x ∈ S)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} {A : AffineSubspace ℝ E}
    (hA : FiniteDimensional ℝ A.direction) (hxc : x ∈ c.source)
    (himage : c.toPartialEquiv.IsImage S (A : Set E)) :
    sliceTangent I S x = Submodule.comap (mfderiv I 𝓘(ℝ, E) c x).toLinearMap
      (show Submodule ℝ (TangentSpace 𝓘(ℝ, E) (c x)) from A.direction) := by
  have hfin : FiniteDimensional ℝ A.direction := hA
  have hclosed : IsClosed (A.direction : Set E) := A.direction.closed_of_finiteDimensional
  have hcdiff : MDifferentiableAt I 𝓘(ℝ, E) c x := c.mdifferentiableAt (by simp) hxc
  have hxA : c x ∈ A := (himage.apply_mem_iff hxc).2 hx
  have hcx : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  apply le_antisymm
  · rw [sliceTangent, Submodule.span_le]
    rintro v ⟨f, h0, hS, hf, rfl⟩
    have hcont : ContinuousAt f 0 := hf.continuousAt
    have hxf : f 0 = x := h0
    have hsrc : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ c.source := by
      refine hcont.preimage_mem_nhds ?_
      rw [hxf]
      exact c.open_source.mem_nhds hxc
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c (f t)) 0 := by
      refine MDifferentiableAt.comp (0 : ℝ) ?_ hf
      rw [hxf]
      exact hcdiff
    have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c (f t)) 0 =
        (mfderiv I 𝓘(ℝ, E) c (f 0)).comp (mfderiv 𝓘(ℝ, ℝ) I f 0) := by
      refine mfderiv_comp (0 : ℝ) ?_ hf
      rw [hxf]
      exact hcdiff
    have hdiffat : DifferentiableAt ℝ (fun t : ℝ => c (f t)) 0 := by
      rw [← mdifferentiableAt_iff_differentiableAt]
      exact hcomp
    have hderiv : HasDerivAt (fun t : ℝ => c (f t))
        (fderiv ℝ (fun t : ℝ => c (f t)) 0 1) 0 :=
      hdiffat.hasFDerivAt.hasDerivAt
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (fun t : ℝ => c (f t)) t - (fun t : ℝ => c (f t)) 0 ∈ A.direction := by
      filter_upwards [hS, hsrc.filter_mono nhdsWithin_le_nhds] with t htS htsrc
      have h2 : c (f 0) ∈ A := by rw [hxf]; exact hxA
      exact A.vsub_mem_direction ((himage.apply_mem_iff htsrc).2 htS) h2
    have hres := mem_of_hasDerivAt_of_eventually hclosed hderiv hmem
    have hfm : fderiv ℝ (fun t : ℝ => c (f t)) 0 =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c (f t)) 0 := mfderiv_eq_fderiv.symm
    rw [hfm, hchain, hxf] at hres
    exact hres
  · intro v hv
    have hw : mfderiv I 𝓘(ℝ, E) c x v ∈ A.direction := hv
    set w : E := mfderiv I 𝓘(ℝ, E) c x v with hwdef
    set gcurve : ℝ → E := fun t => c x + t • w with hgdef
    have hgderiv : HasDerivAt gcurve w 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id (0 : ℝ)
      have h2 : HasDerivAt (fun t : ℝ => t • w) ((1 : ℝ) • w) 0 :=
        HasDerivAt.smul_const h1 w
      have h3 : HasDerivAt (fun t : ℝ => c x + t • w) ((1 : ℝ) • w) 0 :=
        HasDerivAt.const_add (c x) h2
      simpa [hgdef] using h3
    have hg0 : gcurve 0 = c x := by simp [hgdef]
    have hgt : ∀ᶠ t in 𝓝 (0 : ℝ), gcurve t ∈ c.target := by
      refine hgderiv.continuousAt.preimage_mem_nhds ?_
      rw [hg0]
      exact c.open_target.mem_nhds hcx
    have hf0 : c.symm (gcurve 0) = x := by
      rw [hg0]
      exact c.toPartialEquiv.left_inv hxc
    have hfS : ∀ᶠ t in 𝓝 (0 : ℝ), c.symm (gcurve t) ∈ S := by
      filter_upwards [hgt] with t ht
      have hsrc : c.symm (gcurve t) ∈ c.source := c.toPartialEquiv.map_target ht
      refine (himage.apply_mem_iff hsrc).1 ?_
      rw [show c (c.symm (gcurve t)) = gcurve t from c.toPartialEquiv.right_inv ht, hgdef]
      have hmem : t • w +ᵥ c x ∈ A :=
        A.vadd_mem_of_mem_direction (A.direction.smul_mem t hw) hxA
      simpa [vadd_eq_add, add_comm] using hmem
    have hsymm0 : MDifferentiableAt 𝓘(ℝ, E) I c.symm (gcurve 0) := by
      rw [hg0]
      exact c.symm.mdifferentiableAt (by simp) hcx
    have hgm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gcurve 0 := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact hgderiv.differentiableAt
    have hfm : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun t : ℝ => c.symm (gcurve t)) 0 :=
      MDifferentiableAt.comp (0 : ℝ) hsymm0 hgm
    have hchain : mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => c.symm (gcurve t)) 0 =
        (mfderiv 𝓘(ℝ, E) I c.symm (gcurve 0)).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gcurve 0) :=
      mfderiv_comp (0 : ℝ) hsymm0 hgm
    have hgval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gcurve 0
        (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ)) = w := by
      have hd : deriv gcurve 0 = w := HasDerivAt.deriv hgderiv
      rw [mfderiv_eq_fderiv]
      exact hd
    have hvel : mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => c.symm (gcurve t)) 0
        (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ)) = v := by
      rw [hchain]
      have hstep : (mfderiv 𝓘(ℝ, E) I c.symm (gcurve 0)).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gcurve 0)
          (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ)) =
          mfderiv 𝓘(ℝ, E) I c.symm (gcurve 0) w := by
        rw [ContinuousLinearMap.comp_apply, hgval]
      rw [hstep, hg0, hwdef]
      exact mfderiv_symm_apply_mfderiv hxc v
    exact Submodule.subset_span
      ⟨fun t : ℝ => c.symm (gcurve t), hf0, hfS.filter_mono nhdsWithin_le_nhds, hfm, hvel⟩

theorem mfderiv_mem_of_eventually_mem {S : Set M} {x : M}
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} (hxc : x ∈ c.source)
    {K : Submodule ℝ E} (hKclosed : IsClosed (K : Set E))
    (hS : ∀ᶠ y in 𝓝 x, y ∈ S → (c y : E) ∈ K) (hxK : (c x : E) ∈ K)
    {v : TangentSpace I x} (hv : v ∈ sliceTangent I S x) :
    (mfderiv I 𝓘(ℝ, E) c x v : E) ∈ K := by
  have hcdiff : MDifferentiableAt I 𝓘(ℝ, E) c x := c.mdifferentiableAt (by simp) hxc
  have hle : sliceTangent I S x ≤ Submodule.comap (mfderiv I 𝓘(ℝ, E) c x).toLinearMap
      (show Submodule ℝ (TangentSpace 𝓘(ℝ, E) (c x)) from K) := by
    rw [sliceTangent, Submodule.span_le]
    rintro u ⟨f, h0, hSf, hf, rfl⟩
    have hxf : f 0 = x := h0
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c (f t)) 0 := by
      refine MDifferentiableAt.comp (0 : ℝ) ?_ hf
      rw [hxf]
      exact hcdiff
    have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c (f t)) 0 =
        (mfderiv I 𝓘(ℝ, E) c (f 0)).comp (mfderiv 𝓘(ℝ, ℝ) I f 0) := by
      refine mfderiv_comp (0 : ℝ) ?_ hf
      rw [hxf]
      exact hcdiff
    have hdiffat : DifferentiableAt ℝ (fun t : ℝ => c (f t)) 0 := by
      rw [← mdifferentiableAt_iff_differentiableAt]
      exact hcomp
    have hderiv : HasDerivAt (fun t : ℝ => c (f t))
        (fderiv ℝ (fun t : ℝ => c (f t)) 0 1) 0 :=
      hdiffat.hasFDerivAt.hasDerivAt
    have hSnear : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ S → (c (f t) : E) ∈ K := by
      have hcont : Tendsto f (𝓝 (0 : ℝ)) (𝓝 x) := by
        have hct : Tendsto f (𝓝 (0 : ℝ)) (𝓝 (f 0)) := hf.continuousAt
        rwa [hxf] at hct
      exact hcont.eventually hS
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (fun t : ℝ => c (f t)) t - (fun t : ℝ => c (f t)) 0 ∈ K := by
      filter_upwards [hSf, hSnear.filter_mono nhdsWithin_le_nhds] with t htS htK
      have h2 : (c (f 0) : E) ∈ K := by
        rw [hxf]
        exact hxK
      exact K.sub_mem (htK htS) h2
    have hres := mem_of_hasDerivAt_of_eventually hKclosed hderiv hmem
    have hfm : fderiv ℝ (fun t : ℝ => c (f t)) 0 =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c (f t)) 0 := mfderiv_eq_fderiv.symm
    rw [hfm, hchain, hxf] at hres
    exact hres
  exact hle hv


theorem mem_sliceTangent_chart_iff {S : Set M} {x : M} (hx : x ∈ S)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} {A : AffineSubspace ℝ E}
    (hA : FiniteDimensional ℝ A.direction) (hxc : x ∈ c.source)
    (himage : c.toPartialEquiv.IsImage S (A : Set E)) {v : TangentSpace I x} :
    v ∈ sliceTangent I S x ↔ (mfderiv I 𝓘(ℝ, E) c x v : E) ∈ A.direction := by
  rw [sliceTangent_eq_comap hx hA hxc himage]
  exact Iff.rfl

theorem finrank_sliceTangent {S : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d S)
    {x : M} (hx : x ∈ S) : Module.finrank ℝ (sliceTangent I S x) = d := by
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ c x :=
    c.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ hxc
  have hmapeq : (mfderiv I 𝓘(ℝ, E) c x).toLinearMap =
      ((hloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv :
        TangentSpace I x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (c x)) := rfl
  rw [sliceTangent_eq_comap hx hA hxc himage, hmapeq,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  exact hdim



section OpenInSubspace

variable [FiniteDimensional ℝ E]

theorem IsEmbeddedSlice.preimage_val_mem_nhds {L : Submodule ℝ E} {S : Set E} {d : ℕ}
    (hS : IsEmbeddedSlice 𝓘(ℝ, E) d S) (hSL : S ⊆ (L : Set E))
    (hd : Module.finrank ℝ L = d) {x : E} (hx : x ∈ S) :
    (Subtype.val : L → E) ⁻¹' S ∈ 𝓝 (⟨x, hSL hx⟩ : L) := by
  obtain ⟨L', U, f, W, hL'fin, hL'dim, hUopen, h0U, hfC, hfinj, hf0, hWopen, hxW, hfim⟩ :=
    hS.exists_param hx
  have hL'fin' : FiniteDimensional ℝ L' := hL'fin
  have hxL : x ∈ L := hSL hx
  have hLclosed : IsClosed (L : Set E) := L.closed_of_finiteDimensional
  have hfat : ContDiffAt ℝ ∞ f 0 := hfC.contDiffAt (hUopen.mem_nhds h0U)
  have hfdiff : DifferentiableAt ℝ f 0 := hfat.differentiableAt (by simp)
  have hfd : HasFDerivAt f (fderiv ℝ f 0) 0 := hfdiff.hasFDerivAt
  have hfU : ∀ u ∈ U, f u ∈ S := by
    intro u hu
    have hmem : f u ∈ W ∩ S := by
      rw [← hfim]
      exact ⟨u, hu, rfl⟩
    exact hmem.2
  have hrange : ∀ u : L', fderiv ℝ f 0 u ∈ L := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ => t) (1 : ℝ) 0 := hasDerivAt_id' 0
    have hsm : HasDerivAt (fun t : ℝ => t • u) u 0 := by
      simpa using HasDerivAt.smul_const h1 u
    have hfd0 : HasFDerivAt f (fderiv ℝ f 0) ((fun t : ℝ => t • u) 0) := by
      simpa using hfd
    have hcurve : HasDerivAt (fun t : ℝ => f (t • u)) (fderiv ℝ f 0 u) 0 :=
      HasFDerivAt.comp_hasDerivAt (0 : ℝ) hfd0 hsm
    have hcont : ContinuousAt (fun t : ℝ => t • u) 0 :=
      (continuous_id.smul continuous_const).continuousAt
    have hUev : ∀ᶠ t in 𝓝 (0 : ℝ), t • u ∈ U := by
      refine hcont.preimage_mem_nhds ?_
      simpa using hUopen.mem_nhds h0U
    refine mem_of_hasDerivAt_of_eventually hLclosed hcurve ?_
    filter_upwards [hUev.filter_mono nhdsWithin_le_nhds] with t ht
    have hb1 : f (t • u) ∈ L := hSL (hfU _ ht)
    have hb2 : f ((0 : ℝ) • u) ∈ L := by
      rw [zero_smul, hf0]
      exact hxL
    exact L.sub_mem hb1 hb2
  obtain ⟨K, hK⟩ := L.exists_isCompl
  have hπcont : Continuous (L.projectionOnto K hK) :=
    (L.projectionOnto K hK).continuous_of_finiteDimensional
  set πc : E →L[ℝ] L := ⟨L.projectionOnto K hK, hπcont⟩ with hπdef
  have hπL : ∀ (y : E) (hy : y ∈ L), πc y = (⟨y, hy⟩ : L) := fun y hy =>
    Submodule.projectionOnto_apply_of_mem_left hK hy
  set T : L' →L[ℝ] L := πc.comp (fderiv ℝ f 0) with hTdef
  have hTinj : Function.Injective T := by
    intro a b hab
    apply hfinj
    have ha : fderiv ℝ f 0 a ∈ L := hrange a
    have hb : fderiv ℝ f 0 b ∈ L := hrange b
    have hsub : (⟨fderiv ℝ f 0 a, ha⟩ : L) = (⟨fderiv ℝ f 0 b, hb⟩ : L) := by
      rw [← hπL _ ha, ← hπL _ hb]
      exact hab
    exact congrArg Subtype.val hsub
  have hdimeq : Module.finrank ℝ L' = Module.finrank ℝ L := by rw [hL'dim, hd]
  have hTsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimeq
      (f := T.toLinearMap)).1 hTinj
  set e : L' ≃L[ℝ] L := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.2 hTinj) (LinearMap.range_eq_top.2 hTsurj) with hedef
  have hecoe : (e : L' →L[ℝ] L) = T := rfl
  have hgC : ContDiffAt ℝ ∞ (fun u : L' => πc (f u)) 0 :=
    πc.contDiff.contDiffAt.comp 0 hfat
  have hgfd : HasFDerivAt (fun u : L' => πc (f u)) T 0 :=
    HasFDerivAt.comp (0 : L') (πc.hasFDerivAt) hfd
  have hstrict : HasStrictFDerivAt (fun u : L' => πc (f u)) (e : L' →L[ℝ] L) 0 := by
    have h := hgC.hasStrictFDerivAt (by simp)
    rwa [hgfd.fderiv, ← hecoe] at h
  have hmapnhds : Filter.map (fun u : L' => πc (f u)) (𝓝 0) = 𝓝 (πc (f 0)) :=
    hstrict.map_nhds_eq_of_equiv
  have hgimg : (fun u : L' => πc (f u)) '' U ∈ 𝓝 (πc (f 0)) := by
    rw [← hmapnhds]
    exact Filter.image_mem_map (hUopen.mem_nhds h0U)
  have hg0 : πc (f 0) = (⟨x, hxL⟩ : L) := by
    rw [hf0]
    exact hπL x hxL
  rw [hg0] at hgimg
  refine Filter.mem_of_superset hgimg ?_
  rintro _ ⟨u, hu, rfl⟩
  have hfuS : f u ∈ S := hfU u hu
  have hval : ((πc (f u) : L) : E) = f u := congrArg Subtype.val (hπL _ (hSL hfuS))
  change ((πc (f u) : L) : E) ∈ S
  rw [hval]
  exact hfuS


theorem IsEmbeddedSlice.isOpen_preimage_val {L : Submodule ℝ E} {S : Set E} {d : ℕ}
    (hS : IsEmbeddedSlice 𝓘(ℝ, E) d S) (hSL : S ⊆ (L : Set E))
    (hd : Module.finrank ℝ L = d) :
    IsOpen ((Subtype.val : L → E) ⁻¹' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨y, hy⟩ hyS
  exact hS.preimage_val_mem_nhds hSL hd hyS

end OpenInSubspace

end DifferentialGeometry.Geometry
