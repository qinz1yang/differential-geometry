import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrder

/-!
# The tangent space of a finite-order slice (lane CMS3-SLICE, group G1)

For a slice chart `c` of order `k ≠ 0` at `x ∈ S` (`c` carries `S` onto the affine subspace `A`), the
generic tangent space `sliceTangent I S x` (span of one-sided velocities of curves eventually in `S`) is
the preimage of `A.direction` under `dc_x` (`sliceTangent_eq_comap_ofOrder`); hence it has dimension `d`
for a `d`-slice (`finrank_sliceTangent_ofOrder`). Ports of the smooth `sliceTangent_eq_comap` and
`finrank_sliceTangent` (`Soul/SliceTangent.lean`), whose charts are `C^∞`.
-/

set_option autoImplicit false

noncomputable section

open Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞}

/-- A curve with eventually (for `t > 0`) increments in a closed subspace has its derivative there. -/
theorem mem_of_hasDerivAt_of_eventually_sub_mem {F : Type*} [NormedAddCommGroup F]
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

/-- `dc⁻¹ ∘ dc = id` at a point of the source of a partial diffeomorphism of order `k ≠ 0`. -/
theorem mfderiv_symm_apply_mfderiv_ofOrder (hk : k ≠ 0)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {x : M} (hxc : x ∈ c.source)
    (v : TangentSpace I x) :
    mfderiv 𝓘(ℝ, E) I c.symm (c x) (mfderiv I 𝓘(ℝ, E) c x v) = v := by
  have hcdiff : MDifferentiableAt I 𝓘(ℝ, E) c x := c.mdifferentiableAt hk hxc
  have hcx : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I c.symm (c x) := c.symm.mdifferentiableAt hk hcx
  have hcomp : mfderiv I I (fun y : M => c.symm (c y)) x =
      (mfderiv 𝓘(ℝ, E) I c.symm (c x)).comp (mfderiv I 𝓘(ℝ, E) c x) :=
    mfderiv_comp x hsymm hcdiff
  have heq : (fun y : M => c.symm (c y)) =ᶠ[𝓝 x] id := by
    filter_upwards [c.open_source.mem_nhds hxc] with y hy
    exact c.toPartialEquiv.left_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hcomp.symm

/-- **Tangent space in a slice chart of order `k ≠ 0`.** -/
theorem sliceTangent_eq_comap_ofOrder (hk : k ≠ 0) {S : Set M} {x : M} (hx : x ∈ S)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {A : AffineSubspace ℝ E}
    (hA : FiniteDimensional ℝ A.direction) (hxc : x ∈ c.source)
    (himage : c.toPartialEquiv.IsImage S (A : Set E)) :
    sliceTangent I S x = Submodule.comap (mfderiv I 𝓘(ℝ, E) c x).toLinearMap
      (show Submodule ℝ (TangentSpace 𝓘(ℝ, E) (c x)) from A.direction) := by
  have hclosed : IsClosed (A.direction : Set E) := A.direction.closed_of_finiteDimensional
  have hcdiff : MDifferentiableAt I 𝓘(ℝ, E) c x := c.mdifferentiableAt hk hxc
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
    have hres := mem_of_hasDerivAt_of_eventually_sub_mem hclosed hderiv hmem
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
      exact c.symm.mdifferentiableAt hk hcx
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
      exact mfderiv_symm_apply_mfderiv_ofOrder hk hxc v
    exact Submodule.subset_span
      ⟨fun t : ℝ => c.symm (gcurve t), hf0, hfS.filter_mono nhdsWithin_le_nhds, hfm, hvel⟩

/-- Membership in the tangent space of a slice, read in a slice chart of order `k ≠ 0`. -/
theorem mem_sliceTangent_chart_iff_ofOrder (hk : k ≠ 0) {S : Set M} {x : M} (hx : x ∈ S)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {A : AffineSubspace ℝ E}
    (hA : FiniteDimensional ℝ A.direction) (hxc : x ∈ c.source)
    (himage : c.toPartialEquiv.IsImage S (A : Set E)) {v : TangentSpace I x} :
    v ∈ sliceTangent I S x ↔ (mfderiv I 𝓘(ℝ, E) c x v : E) ∈ A.direction := by
  rw [sliceTangent_eq_comap_ofOrder hk hx hA hxc himage]
  exact Iff.rfl

/-- **The tangent space of a `d`-slice of order `k ≠ 0` has dimension `d`.** -/
theorem finrank_sliceTangent_ofOrder (hk : k ≠ 0) {S : Set M} {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I k d S) {x : M} (hx : x ∈ S) :
    Module.finrank ℝ (sliceTangent I S x) = d := by
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, E) k c x := c.isLocalDiffeomorphAt I 𝓘(ℝ, E) k hxc
  have hmapeq : (mfderiv I 𝓘(ℝ, E) c x).toLinearMap =
      ((hloc.mfderivToContinuousLinearEquiv hk).toLinearEquiv :
        TangentSpace I x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (c x)) := rfl
  rw [sliceTangent_eq_comap_ofOrder hk hx hA hxc himage, hmapeq,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  exact hdim

/-- The tangent space of a slice is finite-dimensional. -/
theorem finiteDimensional_sliceTangent_ofOrder (hk : k ≠ 0) {S : Set M} {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I k d S) {x : M} (hx : x ∈ S) :
    FiniteDimensional ℝ (sliceTangent I S x) := by
  obtain ⟨c, A, hA, hxc, -, himage⟩ := hS x hx
  have : FiniteDimensional ℝ A.direction := hA
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, E) k c x := c.isLocalDiffeomorphAt I 𝓘(ℝ, E) k hxc
  set D := hloc.mfderivToContinuousLinearEquiv hk with hD
  have hmem : ∀ v : sliceTangent I S x, (D (v : TangentSpace I x) : E) ∈ A.direction := fun v =>
    (mem_sliceTangent_chart_iff_ofOrder hk hx hA hxc himage).1 v.2
  let f : sliceTangent I S x →ₗ[ℝ] A.direction :=
    { toFun := fun v => ⟨D (v : TangentSpace I x), hmem v⟩
      map_add' := fun v w => Subtype.ext (map_add D (v : TangentSpace I x) (w : TangentSpace I x))
      map_smul' := fun a v => Subtype.ext (map_smul D a (v : TangentSpace I x)) }
  refine FiniteDimensional.of_injective f ?_
  intro v w hvw
  apply Subtype.ext
  apply D.injective
  exact congrArg Subtype.val hvw

end DifferentialGeometry.Geometry.FiniteSoul
