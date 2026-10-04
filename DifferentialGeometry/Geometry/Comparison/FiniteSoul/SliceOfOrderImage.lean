import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderTangent
import DifferentialGeometry.Geometry.Comparison.Soul.ConeSlice

/-!
# Inverse-function-theorem pieces for finite-order slices (lane CMS3-SLICE, group G2)

Ports, at a finite order `k`, of the smooth `ImmersedSlice.lean`, `ConeSlice.lean` and
`SliceTangent.lean` (`IsEmbeddedSlice.preimage_val_mem_nhds`):

* `IsEmbeddedSliceOfOrder.exists_param`: local `C^k` parametrization of a slice of the model space;
* `exists_slice_image_ofOrder` (rank-`d` IFT): the image of a small open set under a `C^k` map with
  injective differential is a `C^k` slice. The tree's finite-order IFT
  (`Coordinates.exists_partialDiffeomorph_of_contMDiffOn`) needs `k ≠ ∞`; the case `k = ∞` goes
  through its `_infty` version;
* `exists_cone_image_ofOrder`: the cone `(x, t) ↦ t • f x` over a transverse `C^k` patch, pushed by a
  partial diffeomorphism of order `k`, is a `(dim + 1)`-slice;
* `IsEmbeddedSliceOfOrder.smul_image`: dilations of the model space preserve slices;
* `IsEmbeddedSliceOfOrder.exists_ball_affine_subset`: a `d`-slice of `E` inside a `d`-dimensional affine
  subspace `A` contains a relative ball of `A` around each of its points;
* `IsEmbeddedSliceOfOrder.exists_open_inter_subset` (slice in slice): if `T ⊆ V` are `d`-slices of the
  carrier then `T` is relatively open in `V` (local uniqueness of slices of equal dimension).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry (coneDeriv hasFDerivAt_cone coneDeriv_injective)

section Model

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Local `C^k` parametrization of a slice of the model space** (`k ≠ 0`). -/
theorem IsEmbeddedSliceOfOrder.exists_param {k : WithTop ℕ∞} (hk : k ≠ 0) {S : Set E} {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) k d S) {x : E} (hx : x ∈ S) :
    ∃ (L : Submodule ℝ E) (U : Set L) (f : L → E) (W : Set E),
      FiniteDimensional ℝ L ∧ Module.finrank ℝ L = d ∧ IsOpen U ∧ (0 : L) ∈ U ∧
        ContDiffOn ℝ k f U ∧ Function.Injective (fderiv ℝ f 0) ∧ f 0 = x ∧
        IsOpen W ∧ x ∈ W ∧ f '' U = W ∩ S := by
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  let L : Submodule ℝ E := A.direction
  let : FiniteDimensional ℝ L := hA
  let shift : L → E := fun v => (v : E) + c x
  let U : Set L := shift ⁻¹' c.target
  let f : L → E := fun v => c.symm (shift v)
  have hcx : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  have hcxA : c x ∈ A := (himage.apply_mem_iff hxc).2 hx
  have hshift : ContDiff ℝ k shift := L.subtypeL.contDiff.add contDiff_const
  have hzero : shift 0 = c x := by simp [shift]
  have hU : IsOpen U := c.open_target.preimage hshift.continuous
  have h0U : (0 : L) ∈ U := by change shift 0 ∈ c.target; rwa [hzero]
  have hf : ContDiffOn ℝ k f U :=
    c.symm.contMDiffOn_toFun.contDiffOn.comp hshift.contDiffOn (fun _ hv => hv)
  have hcLocal := c.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) k hcx
  have hcinj : Function.Injective (fderiv ℝ (c.symm : E → E) (c x)) := by
    intro v w hvw
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.injective
    have hinj : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (c.symm : E → E) (c x)) :=
      (hcLocal.mfderivToContinuousLinearEquiv hk).injective
    apply hinj
    rw [mfderiv_eq_fderiv]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using
      congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.symm (c x))).symm hvw
  have hcDiff : DifferentiableAt ℝ (c.symm : E → E) (c x) :=
    (hcLocal.mdifferentiableAt hk).differentiableAt
  have hdf : HasFDerivAt f ((fderiv ℝ (c.symm : E → E) (c x)).comp L.subtypeL) 0 := by
    have hdc : HasFDerivAt (c.symm : E → E) (fderiv ℝ (c.symm : E → E) (c x)) (shift 0) := by
      rw [hzero]
      exact hcDiff.hasFDerivAt
    exact hdc.comp 0 (L.subtypeL.hasFDerivAt.add_const (c x))
  have hinj : Function.Injective (fderiv ℝ f 0) := by
    rw [hdf.fderiv]
    exact hcinj.comp L.subtype_injective
  have hfzero : f 0 = x := by
    change c.toPartialEquiv.symm (shift 0) = x
    rw [hzero]
    exact c.toPartialEquiv.left_inv hxc
  have him : f '' U = c.source ∩ S := by
    apply Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      have hfv : f v ∈ c.source := c.toPartialEquiv.map_target hv
      refine ⟨hfv, (himage.apply_mem_iff hfv).1 ?_⟩
      change c.toPartialEquiv (c.toPartialEquiv.symm (shift v)) ∈ A
      rw [c.toPartialEquiv.right_inv hv]
      exact A.vadd_mem_of_mem_direction v.property hcxA
    · rintro y ⟨hyc, hyS⟩
      have hcy : c y ∈ A := (himage.apply_mem_iff hyc).2 hyS
      let v : L := ⟨c y - c x, A.vsub_mem_direction hcy hcxA⟩
      have hshiftv : shift v = c y := sub_add_cancel _ _
      have hv : v ∈ U := by
        change shift v ∈ c.target; rw [hshiftv]; exact c.toPartialEquiv.map_source hyc
      refine ⟨v, hv, ?_⟩
      change c.toPartialEquiv.symm (shift v) = y
      rw [hshiftv]
      exact c.toPartialEquiv.left_inv hyc
  exact ⟨L, U, f, c.source, inferInstance, hdim, hU, h0U, hf, hinj, hfzero,
    c.open_source, hxc, him⟩

/-- **Rank-`d` inverse function theorem, slice form** (`1 ≤ k ≤ ∞`). -/
theorem exists_slice_image_ofOrder [CompleteSpace E] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {k : ℕ∞} (hk : 1 ≤ k) {f : F → E} {U : Set F} {a : F}
    (hU : IsOpen U) (ha : a ∈ U) (hf : ContDiffOn ℝ k f U)
    (hinj : Function.Injective (fderiv ℝ f a)) :
    ∃ V : Set F, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ InjOn f V ∧
      IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (k : WithTop ℕ∞) (Module.finrank ℝ F) (f '' V) := by
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
    exact (zero_lt_one.trans_le this).ne'
  let D := fderiv ℝ f a
  let R : Submodule ℝ E := D.range
  obtain ⟨Q, hRQ⟩ := R.exists_isCompl
  let eD : F ≃L[ℝ] R := D.equivRange hinj R.closed_of_finiteDimensional
  let e : (F × Q) ≃L[ℝ] E :=
    (eD.prodCongr (ContinuousLinearEquiv.refl ℝ Q)).trans
      (R.prodEquivOfIsTopCompl Q (Submodule.IsCompl.isTopCompl_of_isClosed hRQ
        R.closed_of_finiteDimensional Q.closed_of_finiteDimensional))
  have he (z : F × Q) : e z = D z.1 + (z.2 : E) := by
    simp only [e, eD, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsTopCompl, Submodule.coe_prodEquivOfIsCompl']
    rfl
  let j : F →L[ℝ] E := e.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ F Q)
  have hj (x : F) : j x = D x := by
    change e (x, 0) = D x
    simpa only [Submodule.coe_zero, add_zero] using he (x, 0)
  have hej (x : F) : e.symm (j x) = (x, 0) := e.symm_apply_apply (x, 0)
  let aug : F × Q → E := fun z => f z.1 + (z.2 : E)
  have hfa : DifferentiableAt ℝ f a := (hf.contDiffAt (hU.mem_nhds ha)).differentiableAt hk0
  have hdaug : HasFDerivAt aug e.toContinuousLinearMap (a, 0) := by
    have hleft := hfa.hasFDerivAt.comp (a, (0 : Q)) (ContinuousLinearMap.fst ℝ F Q).hasFDerivAt
    have hright := (Q.subtypeL.comp (ContinuousLinearMap.snd ℝ F Q)).hasFDerivAt (x := (a, 0))
    convert! hleft.add hright using 1
  let H : E → E := fun y => aug (e.symm y)
  let W : Set E := e.symm ⁻¹' (U ×ˢ (univ : Set Q))
  have hW : IsOpen W := (hU.prod isOpen_univ).preimage e.symm.continuous
  have haW : j a ∈ W := by change e.symm (j a) ∈ U ×ˢ univ; rw [hej]; exact ⟨ha, mem_univ _⟩
  have haug : ContDiffOn ℝ k aug (U ×ˢ (univ : Set Q)) :=
    (hf.comp contDiffOn_fst fun _ hz => hz.1).add
      (Q.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hH : ContDiffOn ℝ k H W :=
    haug.comp e.symm.contDiff.contDiffOn (fun _ hy => hy)
  have hdH : HasFDerivAt H (ContinuousLinearMap.id ℝ E) (j a) := by
    have hdaug' : HasFDerivAt aug e.toContinuousLinearMap (e.symm (j a)) := by rwa [hej]
    convert! hdaug'.comp (j a) e.symm.hasFDerivAt using 1
    ext y
    exact (e.apply_symm_apply y).symm
  have hop : IsOpen {L : E →L[ℝ] E | L.IsInvertible} := by
    convert! ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := E) using 1
  have hId : (fderiv ℝ H (j a)).IsInvertible := by
    rw [hdH.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hInv := ((hH.contDiffAt (hW.mem_nhds haW)).continuousAt_fderiv hk0).preimage_mem_nhds
    (hop.mem_nhds hId)
  obtain ⟨W', hW'sub, hW'open, haW'⟩ := mem_nhds_iff.1 (inter_mem (hW.mem_nhds haW) hInv)
  have hinv : ∀ y ∈ W',
      (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) y H)
        (extChartAt 𝓘(ℝ, E) y y)).IsInvertible := by
    intro y hy
    have hyInv : (fderiv ℝ H y).IsInvertible := (hW'sub hy).2
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.id_comp, Function.comp_id, id_eq] using hyInv
  have hHW' : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (k : WithTop ℕ∞) H W' :=
    (hH.mono (hW'sub.trans inter_subset_left)).contMDiffOn
  obtain ⟨c, hac, hcW', hHc⟩ : ∃ c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E (k : WithTop ℕ∞),
      j a ∈ c.source ∧ c.source ⊆ W' ∧ EqOn H c c.source := by
    rcases eq_or_ne k ⊤ with rfl | hktop
    · exact Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
        (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) hW'open haW' hHW' hinv
    · exact Coordinates.exists_partialDiffeomorph_of_contMDiffOn
        (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) (by exact_mod_cast hk) (by exact_mod_cast hktop)
        hW'open haW' hHW' (hinv _ haW')
  let V : Set F := j ⁻¹' c.source
  have hVU : V ⊆ U := by
    intro x hx
    have hh : e.symm (j x) ∈ U ×ˢ (univ : Set Q) := (hW'sub (hcW' hx)).1
    rw [hej] at hh
    exact hh.1
  have hcj (x : F) (hx : x ∈ V) : c (j x) = f x := by
    rw [← hHc hx]
    change aug (e.symm (j x)) = f x
    rw [hej]
    exact add_zero _
  have hfinj : InjOn f V := by
    intro x hx y hy hxy
    apply hinj
    rw [← hj x, ← hj y]
    apply c.toPartialEquiv.injOn hx hy
    rw [hcj x hx, hcj y hy, hxy]
  have himage : c.toPartialEquiv.IsImage (R : Set E) (f '' V) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, hxy⟩
      have heq : y = j x := c.toPartialEquiv.injOn hy hx (by rw [hcj x hx, hxy])
      rw [heq, hj]
      exact D.mem_range_self x
    · rintro ⟨x, hx⟩
      have hjx : j x = y := (hj x).trans hx
      have hxV : x ∈ V := by change j x ∈ c.source; rwa [hjx]
      exact ⟨x, hxV, by rw [← hcj x hxV, hjx]⟩
  refine ⟨V, c.open_source.preimage j.continuous, hac, hVU, hfinj, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨c.symm, R.toAffineSubspace, inferInstance, ?_, ?_, himage.symm⟩
  · rw [← hcj z hz]
    exact c.toPartialEquiv.map_source hz
  · rw [Submodule.toAffineSubspace_direction]
    exact eD.finrank_eq.symm

/-- **Cone over a transverse patch** (`1 ≤ k ≤ ∞`), pushed by a partial diffeomorphism of order `k`. -/
theorem exists_cone_image_ofOrder [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ∞} (hk : 1 ≤ k)
    {f : F → E} {U : Set F} {a : F} {J : Set ℝ} {t : ℝ}
    (B : PartialDiffeomorph 𝓘(ℝ, E) I E M (k : WithTop ℕ∞))
    (hU : IsOpen U) (ha : a ∈ U) (hJ : IsOpen J) (htJ : t ∈ J)
    (hf : ContDiffOn ℝ k f U) (hinj : Function.Injective (fderiv ℝ f a))
    (ht : t ≠ 0) (htrans : f a ∉ (fderiv ℝ f a).range) (hbase : t • f a ∈ B.source) :
    ∃ V : Set (F × ℝ), IsOpen V ∧ (a, t) ∈ V ∧ V ⊆ U ×ˢ J ∧
      (fun z : F × ℝ => z.2 • f z.1) '' V ⊆ B.source ∧
      IsEmbeddedSliceOfOrder I (k : WithTop ℕ∞) (Module.finrank ℝ F + 1)
        (B '' ((fun z : F × ℝ => z.2 • f z.1) '' V)) := by
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
    exact (zero_lt_one.trans_le this).ne'
  let cone : F × ℝ → E := fun z => z.2 • f z.1
  have hs : ContDiffOn ℝ k cone (U ×ˢ J) :=
    contDiffOn_snd.smul (hf.comp contDiffOn_fst fun _ hz => hz.1)
  let W : Set (F × ℝ) := (U ×ˢ J) ∩ cone ⁻¹' B.source
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage (hU.prod hJ) B.open_source
  have hd := hasFDerivAt_cone
    ((hf.contDiffAt (hU.mem_nhds ha)).differentiableAt hk0).hasFDerivAt (t := t)
  obtain ⟨V, hV, haV, hVW, _, hVS⟩ := exists_slice_image_ofOrder hk hW ⟨⟨ha, htJ⟩, hbase⟩
    (hs.mono inter_subset_left) (by rw [hd.fderiv]; exact coneDeriv_injective hinj ht htrans)
  have hVB : cone '' V ⊆ B.source := by rintro _ ⟨z, hz, rfl⟩; exact (hVW hz).2
  refine ⟨V, hV, haV, hVW.trans inter_subset_left, hVB, ?_⟩
  simpa only [Module.finrank_prod, Module.finrank_self] using hVS.image B hVB

/-- Dilations of the model space preserve slices of every order `k ≤ ∞`. -/
theorem IsEmbeddedSliceOfOrder.smul_image {k : ℕ∞} {S : Set E} {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (k : WithTop ℕ∞) d S) {t : ℝ} (ht : t ≠ 0) :
    IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (k : WithTop ℕ∞) d ((fun x : E => t • x) '' S) := by
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
  let P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E (k : WithTop ℕ∞) :=
    DifferentialGeometry.PartialDiffeomorph.ofLE e.toDiffeomorph.toPartialDiffeomorph
      (by exact_mod_cast le_top)
  have him := hS.image P (fun x _ => mem_univ x)
  have heq : (P : E → E) '' S = (fun x : E => t • x) '' S := Set.image_congr' (fun _ => rfl)
  rwa [heq] at him

/-- **A `d`-slice inside a `d`-dimensional affine subspace is relatively open in it** (`k ≠ 0`). -/
theorem IsEmbeddedSliceOfOrder.exists_ball_affine_subset [FiniteDimensional ℝ E]
    {k : WithTop ℕ∞} (hk : k ≠ 0) {S : Set E} {d : ℕ} (hS : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) k d S)
    {A : AffineSubspace ℝ E} (hSA : S ⊆ (A : Set E)) (hd : Module.finrank ℝ A.direction = d)
    {x : E} (hx : x ∈ S) : ∃ ε > 0, ∀ a ∈ A, dist a x < ε → a ∈ S := by
  obtain ⟨L', U, f, W, hL'fin, hL'dim, hUopen, h0U, hfC, hfinj, hf0, -, -, hfim⟩ :=
    hS.exists_param hk hx
  have : FiniteDimensional ℝ L' := hL'fin
  set L : Submodule ℝ E := A.direction with hLdef
  have hxA : x ∈ A := hSA hx
  have hLclosed : IsClosed (L : Set E) := L.closed_of_finiteDimensional
  have hfat : ContDiffAt ℝ k f 0 := hfC.contDiffAt (hUopen.mem_nhds h0U)
  have hfd : HasFDerivAt f (fderiv ℝ f 0) 0 := (hfat.differentiableAt hk).hasFDerivAt
  have hfU : ∀ u ∈ U, f u ∈ S := by
    intro u hu
    have hmem : f u ∈ W ∩ S := by
      rw [← hfim]
      exact ⟨u, hu, rfl⟩
    exact hmem.2
  have hrange : ∀ u : L', fderiv ℝ f 0 u ∈ L := by
    intro u
    have hsm : HasDerivAt (fun t : ℝ => t • u) u 0 := by
      simpa using HasDerivAt.smul_const (hasDerivAt_id' (0 : ℝ)) u
    have hfd0 : HasFDerivAt f (fderiv ℝ f 0) ((fun t : ℝ => t • u) 0) := by
      simpa using hfd
    have hcurve : HasDerivAt (fun t : ℝ => f (t • u)) (fderiv ℝ f 0 u) 0 :=
      HasFDerivAt.comp_hasDerivAt (0 : ℝ) hfd0 hsm
    have hUev : ∀ᶠ t in 𝓝 (0 : ℝ), t • u ∈ U := by
      refine (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds ?_
      simpa using hUopen.mem_nhds h0U
    refine mem_of_hasDerivAt_of_eventually_sub_mem hLclosed hcurve ?_
    filter_upwards [hUev.filter_mono nhdsWithin_le_nhds] with t ht
    have hb2 : f ((0 : ℝ) • u) = x := by rw [zero_smul, hf0]
    rw [hb2]
    exact A.vsub_mem_direction (hSA (hfU _ ht)) hxA
  obtain ⟨K, hK⟩ := L.exists_isCompl
  set πc : E →L[ℝ] L := ⟨L.projectionOnto K hK,
    (L.projectionOnto K hK).continuous_of_finiteDimensional⟩ with hπdef
  have hπL : ∀ (y : E) (hy : y ∈ L), πc y = (⟨y, hy⟩ : L) := fun y hy =>
    Submodule.projectionOnto_apply_of_mem_left hK hy
  set T : L' →L[ℝ] L := πc.comp (fderiv ℝ f 0) with hTdef
  have hTinj : Function.Injective T := by
    intro a b hab
    apply hfinj
    have hsub : (⟨fderiv ℝ f 0 a, hrange a⟩ : L) = (⟨fderiv ℝ f 0 b, hrange b⟩ : L) := by
      rw [← hπL _ (hrange a), ← hπL _ (hrange b)]
      exact hab
    exact congrArg Subtype.val hsub
  have hdimeq : Module.finrank ℝ L' = Module.finrank ℝ L := by rw [hL'dim, hd]
  have hTsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimeq
      (f := T.toLinearMap)).1 hTinj
  set e : L' ≃L[ℝ] L := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.2 hTinj) (LinearMap.range_eq_top.2 hTsurj) with hedef
  have hecoe : (e : L' →L[ℝ] L) = T := rfl
  set G : L' → L := fun u => πc (f u - x) with hGdef
  have hGC : ContDiffAt ℝ k G 0 := πc.contDiff.contDiffAt.comp 0 (hfat.sub contDiffAt_const)
  have hGfd : HasFDerivAt G T 0 :=
    HasFDerivAt.comp (0 : L') πc.hasFDerivAt (hfd.sub_const x)
  have hstrict : HasStrictFDerivAt G (e : L' →L[ℝ] L) 0 := by
    have h := hGC.hasStrictFDerivAt hk
    rwa [hGfd.fderiv, ← hecoe] at h
  have hmapnhds : Filter.map G (𝓝 0) = 𝓝 (G 0) := hstrict.map_nhds_eq_of_equiv
  have hG0 : G 0 = 0 := by
    change πc (f 0 - x) = 0
    rw [hf0, sub_self, map_zero]
  have hgimg : G '' U ∈ 𝓝 (0 : L) := by
    rw [← hG0, ← hmapnhds]
    exact Filter.image_mem_map (hUopen.mem_nhds h0U)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hgimg
  refine ⟨ε, hε, fun a ha hax => ?_⟩
  have hmem : a - x ∈ L := A.vsub_mem_direction ha hxA
  have haball : (⟨a - x, hmem⟩ : L) ∈ Metric.ball (0 : L) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖a - x‖ < ε
    rwa [← dist_eq_norm]
  obtain ⟨u, hu, hGu⟩ := hball haball
  have hfuS : f u ∈ S := hfU u hu
  have hfx : f u - x ∈ L := A.vsub_mem_direction (hSA hfuS) hxA
  have hval : f u - x = a - x := by
    have h1 := congrArg Subtype.val hGu
    change ((πc (f u - x) : L) : E) = a - x at h1
    rwa [hπL _ hfx] at h1
  have hau : a = f u := by
    have := congrArg (· + x) hval
    simpa using this.symm
  rw [hau]
  exact hfuS

end Model

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Slice in slice** (`k ≠ 0`): if `T ⊆ V` are slices of the same dimension, `T` is relatively open
in `V` near each of its points. -/
theorem IsEmbeddedSliceOfOrder.exists_open_inter_subset {k : WithTop ℕ∞} (hk : k ≠ 0) {d : ℕ}
    {T V : Set M} (hT : IsEmbeddedSliceOfOrder I k d T) (hV : IsEmbeddedSliceOfOrder I k d V)
    (hTV : T ⊆ V) {x : M} (hx : x ∈ T) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ∩ V ⊆ T := by
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hV x (hTV hx)
  have : FiniteDimensional ℝ A.direction := hA
  set T' : Set E := c '' (T ∩ c.source) with hT'def
  have hT' : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) k d T' :=
    (hT.inter_open c.open_source).image c (fun _ hy => hy.2)
  have hT'A : T' ⊆ (A : Set E) := by
    rintro _ ⟨y, ⟨hyT, hyc⟩, rfl⟩
    exact (himage.apply_mem_iff hyc).2 (hTV hyT)
  have hcx : c x ∈ T' := ⟨x, ⟨hx, hxc⟩, rfl⟩
  obtain ⟨ε, hε, hball⟩ := hT'.exists_ball_affine_subset hk hT'A hdim hcx
  refine ⟨c.source ∩ c ⁻¹' Metric.ball (c x) ε,
    c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball,
    ⟨hxc, Metric.mem_ball_self hε⟩, ?_⟩
  rintro y ⟨⟨hyc, hyball⟩, hyV⟩
  have hcyA : c y ∈ A := (himage.apply_mem_iff hyc).2 hyV
  obtain ⟨z, ⟨hzT, hzc⟩, hzy⟩ := hball (c y) hcyA hyball
  have : z = y := c.toPartialEquiv.injOn hzc hyc hzy
  rw [← this]
  exact hzT

end Carrier

end DifferentialGeometry.Geometry.FiniteSoul
