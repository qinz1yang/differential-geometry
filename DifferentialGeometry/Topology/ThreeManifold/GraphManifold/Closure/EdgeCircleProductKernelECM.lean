import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyEdgeCircleSolidTorus

/-!
# E4a–E4c kernel: a smooth disk bundle over the circle is a fibre-preserving product

Draft 74, packages E4a / E4b / E4c (`EdgeComponentModels.circleTriv`, disposition D74-12). The
abstract kernel on a compact connected oriented manifold `M` with boundary (model `𝓡∂ 3`) with a
smooth submersion `p : M → S¹` that is also a submersion on `∂M` (curve form) and a smooth disk
`fibre` onto the whole fibre `p⁻¹{1}`.

The tree already contains the whole chain (lift flow, orientation of the monodromy, the disk
isotopy kernel, the mapping-torus lemma) in the D2S1 lane; what is NEW here is

* the explicit fibre-preserving product (`p (T (x, z)) = z`; the tree's
  `nonempty_solidTorus_diffeomorph_of_liftFlow` only returns `Nonempty` of a solid-torus
  diffeomorphism), with its slices and its boundary (`range_slice_edge_circle_product_ECM`,
  `isBoundaryPoint_edge_circle_product_ECM`);
* an AMBIENT form: the disk is not required to be a smooth embedding into `M` (the immersion
  criterion needs a boundaryless source, so for a sublevel manifold `M` with boundary this is not
  available), only `ι ∘ fibre` is a smooth embedding into an ambient manifold `N` for a smooth
  `ι : M → N` (here `ι = Subtype.val` into the carrier). The smoothness of the inverse of the disk
  chart is then taken from the ambient embedding (`IsSmoothEmbedding.contMDiff_lift`).

* **E4a** `diskCircle_cut_returnMap_ECM`: the boundary-preserving lift flow `Φ` of the rotation, cut
  open along the fibre over `1`: the return map `μ` of `Φ` on the disk is a diffeomorphism of the
  disk, and it preserves the orientation (`monodromy_preservesOrientation_ECM`).
* **E4b** `diskReturnMap_product_correction_ECM`: an orientation-preserving disk diffeomorphism is
  smoothly isotopic to the identity. This is the tree's
  `exists_diskIsotopy_from_refl_of_preservesOrientation` (rim lift plus the rel-rim Smale-level
  step of lane D2S1-RIM): the kernel NEEDS NO new named input.
  `diskReturnMap_seam_isotopy_ECM` is the seam form used for the product.
* **E4c** `edge_circle_product_kernel_ECM`: the explicit fibre-preserving product
  `T : D² × S¹ ≃ₘ M` with `p (T (x, z)) = z`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsKernel_ECM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothKernel_ECM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

attribute [local instance] finrank_real_complex_fact'

local instance closedCellNonemptyKernel_ECM : Nonempty (ClosedCell 2) :=
  ⟨closedCellCenter 2⟩

/-! ## E4a: the return map of the lift flow -/

/-- The return map of the flow on the fibre is smooth, the smoothness of the disk chart being taken
from the ambient embedding `ι ∘ fibre`. -/
theorem contMDiff_fibreReturnMap_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] (ι : M → N)
    (hι : ContMDiff (𝓡∂ 3) J' ∞ ι) {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q) {fibre : ClosedCell 2 → M}
    (hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre) (hφ : IsSmoothEmbedding (𝓡∂ 2) J' ∞ (ι ∘ fibre))
    (hrange : range fibre = p ⁻¹' {1}) {s : ℝ} (hs : Circle.exp s = 1) :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (fibreReturnMap Φ fibre s) := by
  have hret := fibre_fibreReturnMap hΦp hrange hs
  have hg : ContMDiff (𝓡∂ 2) J' ∞ (fun x => ι (Φ s (fibre x))) :=
    hι.comp (hΦ.comp (contMDiff_const.prodMk hfibre_sm))
  have hgf : range (fun x => ι (Φ s (fibre x))) ⊆ range (ι ∘ fibre) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨fibreReturnMap Φ fibre s x, by simp only [Function.comp_apply, hret]⟩
  have hlift : fibreReturnMap Φ fibre s = hφ.lift (fun x => ι (Φ s (fibre x))) hgf := by
    funext x
    apply hφ.isEmbedding.injective
    rw [hφ.comp_lift hgf x]
    simp only [Function.comp_apply, hret]
  rw [hlift]
  exact hφ.contMDiff_lift hg hgf

/-- The monodromy of the flow on the fibre over `1` is a diffeomorphism of the disk. -/
theorem exists_monodromy_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] (ι : M → N)
    (hι : ContMDiff (𝓡∂ 3) J' ∞ ι) {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q) {fibre : ClosedCell 2 → M}
    (hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre) (hfibre_inj : Injective fibre)
    (hφ : IsSmoothEmbedding (𝓡∂ 2) J' ∞ (ι ∘ fibre)) (hrange : range fibre = p ⁻¹' {1}) :
    ∃ μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2,
      ∀ x, fibre (μ x) = Φ (2 * Real.pi) (fibre x) := by
  refine ⟨{ toFun := fibreReturnMap Φ fibre (2 * Real.pi)
            invFun := fibreReturnMap Φ fibre (-(2 * Real.pi))
            left_inv := fibreReturnMap_neg_apply hΦadd hΦp hfibre_inj hrange Circle.exp_two_pi
            right_inv := fun x => ?_
            contMDiff_toFun := contMDiff_fibreReturnMap_ECM ι hι hΦ hΦp hfibre_sm hφ hrange
              Circle.exp_two_pi
            contMDiff_invFun := contMDiff_fibreReturnMap_ECM ι hι hΦ hΦp hfibre_sm hφ hrange
              (by rw [Circle.exp_neg, Circle.exp_two_pi, inv_one]) },
    fun x => fibre_fibreReturnMap hΦp hrange Circle.exp_two_pi x⟩
  have h := fibreReturnMap_neg_apply hΦadd hΦp hfibre_inj hrange
    (s := -(2 * Real.pi)) (by rw [Circle.exp_neg, Circle.exp_two_pi, inv_one]) x
  rwa [neg_neg] at h

section Orientation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- The monodromy preserves every orientation of the disk when the total space is oriented and
connected (copy of the tree's `monodromyDiffeomorph_preservesOrientation`, with the smooth disk
inclusion given by its smoothness and injective differential only). -/
theorem monodromy_preservesOrientation_ECM [ConnectedSpace M]
    (oM : ManifoldOrientation (𝓡∂ 3) M 3) {p : M → Circle} (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦ0 : ∀ q, Φ 0 q = q) (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q) {fibre : ClosedCell 2 → M}
    (hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hfibre_d : ∀ x, Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) fibre x)) (hrange : range fibre = p ⁻¹' {1})
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)
    (hfμ : ∀ x, fibre (μ x) = Φ (2 * Real.pi) (fibre x))
    (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2) : μ.preservesOrientation o o := by
  let _ : PreconnectedSpace (ClosedCell 2) := closedCell_two_preconnectedSpace
  obtain ⟨x₀, hx₀⟩ := exists_fixedPoint_closedCell_two μ.continuous
  set q₀ := fibre x₀ with hq₀
  have hq₀fix : Φ (2 * Real.pi) q₀ = q₀ := by
    rw [hq₀, ← hfμ, hx₀]
  -- `Φ (2π)` preserves `oM`, hence has positive determinant at its fixed point `q₀`
  have hΦpres : (Φ (2 * Real.pi)).preservesOrientation oM oM :=
    DifferentialGeometry.Topology.Manifold.preservesOrientation_of_contMDiff_flow oM Φ hΦ0 hΦ
      (2 * Real.pi)
  have hdetΦ := (preservesOrientation_iff_det_mfderiv_pos_of_apply_eq oM q₀
    hq₀fix).mp hΦpres
  rw [preservesOrientation_iff_det_mfderiv_pos_of_apply_eq o x₀ hx₀]
  -- the data of the block decomposition
  have hp1 : ∀ x, p (fibre x) = 1 := by
    intro x
    have h : fibre x ∈ p ⁻¹' {1} := hrange ▸ mem_range_self x
    exact h
  have hcp : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ (fun q => (p q : ℂ)) :=
    contMDiff_coe_sphere.comp hp
  let γ : ℝ → M := fun t => Φ t q₀
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ := hΦ.comp (contMDiff_id.prodMk contMDiff_const)
  have hγ0 : γ 0 = q₀ := hΦ0 q₀
  let ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ := mfderiv (𝓡∂ 3) 𝓘(ℝ, ℂ) (fun q => (p q : ℂ)) q₀
  let X : EuclideanSpace ℝ (Fin 3) := mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 3) γ 0 1
  let i : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv (𝓡∂ 2) (𝓡∂ 3) fibre x₀
  let T : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡∂ 3) (𝓡∂ 3) (Φ (2 * Real.pi)) q₀
  let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv (𝓡∂ 2) (𝓡∂ 2) μ x₀
  have hmd_cp : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ, ℂ) (fun q => (p q : ℂ)) q₀ :=
    hcp.mdifferentiableAt (by simp)
  have hmd_fibre : ∀ x, MDifferentiableAt (𝓡∂ 2) (𝓡∂ 3) fibre x :=
    fun x => hfibre_sm.mdifferentiableAt (by simp)
  have hmd_Φ : ∀ q, MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (Φ (2 * Real.pi)) q :=
    fun q => (Φ (2 * Real.pi)).contMDiff.mdifferentiableAt (by simp)
  have hmd_μ : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) μ x₀ := μ.contMDiff.mdifferentiableAt (by simp)
  have hmd_γ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 3) γ 0 := hγ.mdifferentiableAt (by simp)
  -- `ℓ` kills the fibre directions
  have hℓi : ∀ w, ℓ (i w) = 0 := by
    intro w
    have hconst : (fun q => (p q : ℂ)) ∘ fibre = fun _ => (1 : ℂ) := by
      funext x
      simp [hp1 x]
    have h := mfderiv_comp_apply_of_eq x₀ hmd_cp (hmd_fibre x₀) rfl w
    rw [hconst, mfderiv_const] at h
    exact h.symm
  -- `ℓ` does not kill the flow direction
  have hX : ℓ X ≠ 0 := by
    have hcomp : (fun q => (p q : ℂ)) ∘ γ = fun t : ℝ => ((Circle.exp t * p q₀ : Circle) : ℂ) := by
      funext t
      simp only [Function.comp_apply, γ, hΦp]
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) hmd_cp hmd_γ hγ0 (1 : ℝ)
    rw [hcomp] at h
    change _ = ℓ X at h
    rw [← h]
    exact mfderiv_circle_rotation_coe_ne_zero (p q₀)
  -- `T` acts on the fibre directions as `A`
  have hTA : ∀ w, T (i w) = i (A w) := by
    intro w
    have hfun : fibre ∘ μ = (Φ (2 * Real.pi)) ∘ fibre := by
      funext x
      exact hfμ x
    have h1 := mfderiv_comp_apply_of_eq x₀ (hmd_fibre x₀) hmd_μ hx₀ w
    have h2 := mfderiv_comp_apply_of_eq x₀ (hmd_Φ q₀) (hmd_fibre x₀) rfl w
    rw [hfun] at h1
    exact h2.symm.trans h1
  -- `T` fixes the flow direction
  have hTX : T X = X := by
    have hfun : (Φ (2 * Real.pi)) ∘ γ = γ := by
      funext t
      change Φ (2 * Real.pi) (Φ t q₀) = Φ t q₀
      rw [← hΦadd, add_comm, hΦadd, hq₀fix]
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) (hmd_Φ q₀) hmd_γ hγ0 (1 : ℝ)
    rw [hfun] at h
    exact h.symm
  have hi : Injective i := hfibre_d x₀
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 := by
    simp
  have hdet := det_eq_det_of_invariant_of_fixed hdim i.toLinearMap hi ℓ.toLinearMap hℓi X hX
    T.toLinearMap A.toLinearMap hTA hTX
  change 0 < LinearMap.det A.toLinearMap
  rw [← hdet]
  exact hdetΦ

end Orientation

/-! ## The inverse of the turn map -/

/-- The inverse of the turn map is smooth (ambient form of the tree's
`contMDiff_liftFlowTurnInv`). -/
theorem contMDiff_liftFlowTurnInv_ECM {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] (ι : M → N)
    (hι : ContMDiff (𝓡∂ 3) J' ∞ ι) {p : M → Circle}
    (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    {fibre : ClosedCell 2 → M} (hfibre_inj : Injective fibre)
    (hφ : IsSmoothEmbedding (𝓡∂ 2) J' ∞ (ι ∘ fibre))
    (hrange : range fibre = p ⁻¹' {1}) {K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)}
    (hKi : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1))
    {ε : ℝ} (hε : 0 < ε) (hlo : ∀ t x, t < ε → K t x = x)
    (hhi : ∀ t x, 1 - ε < t → Φ (2 * Real.pi) (fibre (K t x)) = fibre x) :
    ContMDiff (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) ∞ (liftFlowTurnInv Φ fibre K p) := by
  intro q₀
  refine ContMDiffAt.prodMk ?_ (hp q₀)
  set r₀ := circleTurnAngle (p q₀) with hr₀
  have hloc := AddCircle.isLocalDiffeomorph_coe r₀
  let C := AddCircle.diffeomorphCircle
  let σ : M → ℝ := fun q => hloc.localInverse (C.symm (p q))
  have hz₀ : C.symm (p q₀) = (r₀ : AddCircle (1 : ℝ)) := by
    rw [hr₀]
    unfold circleTurnAngle
    rw [AddCircle.coe_equivIco]
  have hσ₀ : σ q₀ = r₀ := by
    change hloc.localInverse (C.symm (p q₀)) = r₀
    rw [hz₀]
    exact hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hCp : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun q => C.symm (p q)) := C.symm.contMDiff.comp hp
  have hσ : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ σ q₀ := by
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ hloc.localInverse (C.symm (p q₀)) := by
      rw [hz₀]
      exact hloc.contMDiffAt_localInverse
    exact h1.comp q₀ (hCp q₀)
  have hsrc : ∀ᶠ q in 𝓝 q₀, C.symm (p q) ∈ hloc.localInverse.source :=
    hCp.continuous.continuousAt.preimage_mem_nhds
      (hloc.localInverse_open_source.mem_nhds (by rw [hz₀]; exact hloc.localInverse_mem_source))
  have hpσ : ∀ᶠ q in 𝓝 q₀, p q = Circle.exp (2 * Real.pi * σ q) := by
    filter_upwards [hsrc] with q hq
    rw [← addCircle_diffeomorphCircle_coe]
    change p q = C (hloc.localInverse (C.symm (p q)) : AddCircle (1 : ℝ))
    rw [hloc.localInverse_right_inv hq]
    exact (C.apply_symm_apply (p q)).symm
  have hint : ∀ᶠ q in 𝓝 q₀, σ q ∈ Ioo (-(min ε 1)) 1 := by
    have hmem : σ q₀ ∈ Ioo (-(min ε 1)) 1 := by
      rw [hσ₀]
      exact ⟨lt_of_lt_of_le (neg_neg_of_pos (lt_min hε one_pos)) (circleTurnAngle_mem _).1,
        (circleTurnAngle_mem _).2⟩
    exact hσ.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
  have hone : ∀ᶠ q in 𝓝 q₀, Φ (-(2 * Real.pi * σ q)) q ∈ range fibre := by
    filter_upwards [hpσ] with q hq
    rw [hrange]
    change p (Φ (-(2 * Real.pi * σ q)) q) = 1
    rw [hΦp, hq, ← Circle.exp_add, neg_add_cancel, Circle.exp_zero]
  let g : M → ClosedCell 2 := fun q => invFun fibre (Φ (-(2 * Real.pi * σ q)) q)
  have hpair : ContMDiffAt (𝓡∂ 3) (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) ∞
      (fun q => (-(2 * Real.pi * σ q), q)) q₀ :=
    ((contMDiffAt_const.mul hσ).neg).prodMk contMDiffAt_id
  have hΦσ : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (fun q => Φ (-(2 * Real.pi * σ q)) q) q₀ :=
    ContMDiffAt.comp (g := fun x : ℝ × M => Φ x.1 x.2) q₀ (hΦ _) hpair
  have hfg : (fibre ∘ g) =ᶠ[𝓝 q₀] (fun q => Φ (-(2 * Real.pi * σ q)) q) := by
    filter_upwards [hone] with q hq
    exact Function.invFun_eq hq
  have hιΦσ : ContMDiffAt (𝓡∂ 3) J' ∞ (fun q => ι (Φ (-(2 * Real.pi * σ q)) q)) q₀ :=
    hι.contMDiffAt.comp q₀ hΦσ
  have hfg' : ((ι ∘ fibre) ∘ g) =ᶠ[𝓝 q₀] (fun q => ι (Φ (-(2 * Real.pi * σ q)) q)) := by
    filter_upwards [hfg] with q hq
    exact congrArg ι hq
  have hgc : ContinuousAt g q₀ :=
    hφ.isEmbedding.isInducing.continuousAt_iff.mpr (hιΦσ.continuousAt.congr hfg'.symm)
  have hg : ContMDiffAt (𝓡∂ 3) (𝓡∂ 2) ∞ g q₀ :=
    (ContMDiffAt.iff_comp_isImmersionAt (hφ.isImmersion.isImmersionAt (g q₀))).mpr
      ⟨hgc, hιΦσ.congr_of_eventuallyEq hfg'⟩
  have hloc' : ContMDiffAt (𝓡∂ 3) (𝓡∂ 2) ∞ (fun q => (K (σ q)).symm (g q)) q₀ :=
    (hKi (g q₀, σ q₀)).comp q₀ (hg.prodMk hσ)
  apply hloc'.congr_of_eventuallyEq
  filter_upwards [hpσ, hint, hone] with q hq hqi hqo
  change (K (circleTurnAngle (p q))).symm
    (invFun fibre (Φ (-(2 * Real.pi * circleTurnAngle (p q))) q)) =
    (K (σ q)).symm (g q)
  rw [hq, circleTurnAngle_exp]
  by_cases h0 : 0 ≤ σ q
  · rw [Int.fract_eq_self.mpr ⟨h0, hqi.2⟩]
  · replace h0 := not_le.mp h0
    have hfr : Int.fract (σ q) = σ q + 1 := by
      rw [← Int.self_sub_floor]
      have hfl : ⌊σ q⌋ = -1 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith [hqi.1, min_le_right ε 1]
      rw [hfl]
      push_cast
      ring
    have hKσ : (K (σ q)).symm (g q) = g q := by
      apply (K (σ q)).injective
      change K (σ q) ((K (σ q)).symm (g q)) = K (σ q) (g q)
      rw [Diffeomorph.apply_symm_apply, hlo _ _ (by linarith)]
    rw [hKσ, hfr]
    have hgy : fibre (g q) = Φ (-(2 * Real.pi * σ q)) q := Function.invFun_eq hqo
    have hseam := hhi (σ q + 1) (g q) (by linarith [hqi.1, min_le_left ε 1])
    have hfK : fibre (K (σ q + 1) (g q)) = Φ (-(2 * Real.pi * (σ q + 1))) q := by
      rw [← liftFlow_neg_apply hΦadd (2 * Real.pi) (fibre (K (σ q + 1) (g q))), hseam, hgy,
        ← hΦadd]
      congr 2
      ring
    apply (K (σ q + 1)).injective
    change K (σ q + 1) ((K (σ q + 1)).symm
      (invFun fibre (Φ (-(2 * Real.pi * (σ q + 1))) q))) = K (σ q + 1) (g q)
    rw [Diffeomorph.apply_symm_apply, ← hfK, Function.leftInverse_invFun hfibre_inj]

/-! ## E4a, E4b, E4c -/

/-- The differential of the disk chart is injective. -/
theorem mfderiv_fibre_injective_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] (ι : M → N)
    (hι : ContMDiff (𝓡∂ 3) J' ∞ ι) {fibre : ClosedCell 2 → M}
    (hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre) (hφ : IsSmoothEmbedding (𝓡∂ 2) J' ∞ (ι ∘ fibre))
    (x : ClosedCell 2) : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) fibre x) := by
  have hinj := hφ.isImmersion.mfderiv_injective (by simp) x
  rw [mfderiv_comp x (hι.mdifferentiableAt (by simp)) (hfibre_sm.mdifferentiableAt (by simp))]
    at hinj
  exact Function.Injective.of_comp hinj

/-- **E4a: the cut map and the return map.** The lift flow of the rotation of the circle, and the
return map `μ` of the flow on the fibre over `1`: a diffeomorphism of the disk preserving the
orientation. -/
theorem diskCircle_cut_returnMap_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] (oM : ManifoldOrientation (𝓡∂ 3) M 3) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
    {J' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (ι : M → N) (hι : ContMDiff (𝓡∂ 3) J' ∞ ι)
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
    (hbd : ∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (p ∘ γ) 0 ≠ 0)
    (fibre : ClosedCell 2 → M) (hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hφ : IsSmoothEmbedding (𝓡∂ 2) J' ∞ (ι ∘ fibre)) (hrange : range fibre = p ⁻¹' {1}) :
    ∃ Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2) ∧
      (∀ s t q, Φ (s + t) q = Φ s (Φ t q)) ∧ (∀ t q, p (Φ t q) = Circle.exp t * p q) ∧
      ∃ μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2,
        (∀ x, fibre (μ x) = Φ (2 * Real.pi) (fibre x)) ∧
        μ.preservesOrientation DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation
          DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation := by
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hΦp⟩ := exists_circleLiftFlow_of_boundary_submersion p hp hsub hbd
  have hinj : Injective fibre := hφ.isEmbedding.injective.of_comp
  obtain ⟨μ, hμ⟩ := exists_monodromy_ECM ι hι hΦ hΦadd hΦp hfibre_sm hinj hφ hrange
  exact ⟨Φ, hΦ, hΦadd, hΦp, μ, hμ, monodromy_preservesOrientation_ECM oM hp hΦ hΦ0 hΦadd hΦp
    hfibre_sm (mfderiv_fibre_injective_ECM ι hι hfibre_sm hφ) hrange μ hμ
    DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation⟩

/-- **E4b: the product correction.** An orientation-preserving diffeomorphism of the closed disk is
smoothly isotopic to the identity: a family `K t` of diffeomorphisms, jointly smooth with jointly
smooth inverses, equal to the identity for `t < ε` and to `μ` for `t > 1 − ε`. No collar or rim
hypothesis is needed (the rim is handled inside the tree's kernel). -/
theorem diskReturnMap_product_correction_ECM
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)
    (hμ : μ.preservesOrientation
      DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation
      DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation) :
    ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = x) ∧ (∀ t x, 1 - ε < t → K t x = μ x) :=
  exists_diskIsotopy_from_refl_of_preservesOrientation
    DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation μ hμ

/-- **E4b, seam form.** If `μ` is the return map of a flow `Φ` on the fibre `fibre`, the isotopy of
the inverse return map starts at the identity and ends at a diffeomorphism that undoes one full turn
of the flow on the fibre. -/
theorem diskReturnMap_seam_isotopy_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M))
    (fibre : ClosedCell 2 → M) (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)
    (hμ : ∀ x, fibre (μ x) = Φ (2 * Real.pi) (fibre x))
    (hμo : μ.preservesOrientation
      DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation
      DifferentialGeometry.Topology.Manifold.closedDiskPositiveOrientation) :
    ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = x) ∧
        (∀ t x, 1 - ε < t → Φ (2 * Real.pi) (fibre (K t x)) = fibre x) := by
  obtain ⟨K, hK, hKi, ε, hε, hlo, hhi⟩ := diskReturnMap_product_correction_ECM μ.symm
    (Diffeomorph.preservesOrientation_symm hμo)
  refine ⟨K, hK, hKi, ε, hε, hlo, fun t x ht => ?_⟩
  rw [hhi t x ht, ← hμ, Diffeomorph.apply_symm_apply]

/-- **E4c: the fibre-preserving product.** The disk bundle `p : M → S¹` is the direct product
`D² × S¹`: a diffeomorphism `T : D² × S¹ ≃ₘ M` with `p (T (x, z)) = z`. It is the turn map
`(x, z) ↦ Φ (2π r) (fibre (K r x))`, `r` the angle of `z` in turns. -/
theorem edge_circle_product_kernel_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] (oM : ManifoldOrientation (𝓡∂ 3) M 3) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
    {J' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (ι : M → N) (hι : ContMDiff (𝓡∂ 3) J' ∞ ι)
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
    (hbd : ∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (p ∘ γ) 0 ≠ 0)
    (fibre : ClosedCell 2 → M) (hfibre_sm : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hφ : IsSmoothEmbedding (𝓡∂ 2) J' ∞ (ι ∘ fibre)) (hrange : range fibre = p ⁻¹' {1}) :
    ∃ T : (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ M, ∀ q, p (T q) = q.2 := by
  obtain ⟨Φ, hΦ, hΦadd, hΦp, μ, hμ, hμo⟩ := diskCircle_cut_returnMap_ECM oM ι hι p hp hsub hbd
    fibre hfibre_sm hφ hrange
  obtain ⟨K, hK, hKi, ε, hε, hlo, hhi⟩ := diskReturnMap_seam_isotopy_ECM Φ fibre μ hμ hμo
  have hinj : Injective fibre := hφ.isEmbedding.injective.of_comp
  let T : (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ M :=
    { toFun := liftFlowTurnMap Φ fibre K
      invFun := liftFlowTurnInv Φ fibre K p
      left_inv := liftFlowTurnInv_turnMap hΦadd hΦp hinj hrange K
      right_inv := liftFlowTurnMap_turnInv hΦadd hΦp hrange K
      contMDiff_toFun := contMDiff_liftFlowTurnMap hΦ hΦadd hfibre_sm hK hε hlo hhi
      contMDiff_invFun :=
        contMDiff_liftFlowTurnInv_ECM ι hι hp hΦ hΦadd hΦp hinj hφ hrange hKi hε hlo hhi }
  refine ⟨T, fun q => ?_⟩
  obtain ⟨x, z⟩ := q
  have hp1 : p (fibre (K (circleTurnAngle z) x)) = 1 := by
    have h : fibre (K (circleTurnAngle z) x) ∈ p ⁻¹' {1} := hrange ▸ mem_range_self _
    exact h
  change p (Φ (2 * Real.pi * circleTurnAngle z) (fibre (K (circleTurnAngle z) x))) = z
  rw [hΦp, hp1, mul_one, exp_circleTurnAngle]

/-- The slices of the product are the whole fibres of `p`. -/
theorem range_slice_edge_circle_product_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {p : M → Circle}
    (T : (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ M) (hT : ∀ q, p (T q) = q.2)
    (z : Circle) : range (fun x : ClosedCell 2 => T (x, z)) = p ⁻¹' {z} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact hT (x, z)
  · intro hy
    refine ⟨(T.symm y).1, ?_⟩
    have h2 : (T.symm y).2 = z := by
      have := hT (T.symm y)
      rw [Diffeomorph.apply_symm_apply] at this
      exact this.symm.trans hy
    have h3 : (T.symm y) = ((T.symm y).1, z) := Prod.ext rfl h2
    change T ((T.symm y).1, z) = y
    rw [← h3, Diffeomorph.apply_symm_apply]

/-- The product carries `∂D² × S¹` onto the boundary of `M`: a point of the slice over `z` is a
boundary point of `M` iff it lies on the rim of the disk. -/
theorem isBoundaryPoint_edge_circle_product_ECM {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (T : (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ M) {x : ClosedCell 2} (z : Circle) :
    (𝓡∂ 3).IsBoundaryPoint (T (x, z)) ↔ x ∈ diskRim := by
  rw [← (T.isLocalDiffeomorph (x, z)).isBoundaryPoint_iff (by simp)]
  have hb := ModelWithCorners.boundary_of_boundaryless_right (I := 𝓡∂ 2) (J := 𝓡 1)
    (M := ClosedCell 2) (N := Circle)
  change (x, z) ∈ ((𝓡∂ 2).prod (𝓡 1)).boundary (ClosedCell 2 × Circle) ↔ x ∈ diskRim
  rw [hb]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

end GC.GraphManifold.Assembly
