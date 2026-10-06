import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2
import DifferentialGeometry.Topology.Maps.SaturatedFaces

/-!
# BCG07 F5 / F5z, part 1: isolation of the base value of a saturated regular zero set
(lane S-BCG-ROWS; generic, any smooth manifolds)

* `mfderiv_surjective_of_isSmoothEmbedding_BGR`: a smooth embedding `φ : ℝ¹ × F → M` between
  manifolds of the same dimension has onto differential (injective + `finrank` count);
* `mfderiv_comp_vertical_BGR`, `mfderiv_comp_horizontal_BGR`: the differential of `Fd ∘ φ` at
  `(0, z₀)` on the vertical `(0, b)` and horizontal `(a, 0)` directions;
* `exists_isOpen_slice_isolated_BGR`: if `Fd ∘ φ ≡ c` on the slice `{0} × F` and `d Fd ≠ 0` at
  `φ (0, z₀)`, then `Fd (φ (s e₁, z₀)) = c` only at `s = 0` near `0`;
* **`exists_isOpen_inter_image_zero_eq_singleton_BGR`**: for a smooth product chart
  (`SmoothProductChartAt_BIFc`, `k = 1`) of `f` at `w`, a smooth `Fd` equal to `c` on the fibre
  over `w`, the level `{Fd = c} ∩ X` saturated over `f`, and `d Fd ≠ 0` at a fibre point, the base
  value `w` is isolated in `f '' ({Fd = c} ∩ X)` — the `hiso` input of the closed chapter's
  `eq_fiber_of_isPreconnected_of_isolated` (ZSP03 `j = 3`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]

/-- A smooth embedding of a product `ℝ¹ × F` onto a neighbourhood-sized piece of an `M` of the same
dimension has onto differential at every point. -/
theorem mfderiv_surjective_of_isSmoothEmbedding_BGR
    {φ : EuclideanSpace ℝ (Fin 1) × F → M}
    (hφ : IsSmoothEmbedding ((𝓡 1).prod IF) IM ∞ φ)
    (hdim : Module.finrank ℝ EM = 1 + Module.finrank ℝ EF) (q : EuclideanSpace ℝ (Fin 1) × F) :
    Surjective (mfderiv ((𝓡 1).prod IF) IM φ q) := by
  have hinj : Injective (mfderiv ((𝓡 1).prod IF) IM φ q) :=
    hφ.isImmersion.mfderiv_injective (by simp) q
  have : FiniteDimensional ℝ (TangentSpace ((𝓡 1).prod IF) q) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1) × EF))
  have : FiniteDimensional ℝ (TangentSpace IM (φ q)) := inferInstanceAs (FiniteDimensional ℝ EM)
  have hfin : Module.finrank ℝ (TangentSpace ((𝓡 1).prod IF) q) =
      Module.finrank ℝ (TangentSpace IM (φ q)) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EF) = Module.finrank ℝ EM
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, hdim]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := (mfderiv ((𝓡 1).prod IF) IM φ q).toLinearMap)).mp hinj

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EF] in
/-- The differential of `Fd ∘ φ` at `(0, z₀)` vanishes on the vertical directions `(0, b)` when
`Fd ∘ φ` vanishes on the slice `{0} × F`. -/
theorem mfderiv_comp_vertical_BGR
    {φ : EuclideanSpace ℝ (Fin 1) × F → M} (hφ : IsSmoothEmbedding ((𝓡 1).prod IF) IM ∞ φ)
    {Fd : M → ℝ} (hFd : ContMDiff IM 𝓘(ℝ, ℝ) ∞ Fd) {z₀ : F} {c : ℝ}
    (hzero : ∀ z, Fd (φ (0, z)) = c) (b : EF) :
    mfderiv ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) (Fd ∘ φ) (0, z₀)
      (show TangentSpace ((𝓡 1).prod IF) ((0 : EuclideanSpace ℝ (Fin 1)), z₀) from (0, b)) = 0 := by
  have hA : ContMDiff ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) ∞ (Fd ∘ φ) := hFd.comp hφ.contMDiff
  have hι : MDifferentiableAt IF ((𝓡 1).prod IF)
      (fun z : F => ((0 : EuclideanSpace ℝ (Fin 1)), z)) z₀ :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hcomp := mfderiv_comp z₀ ((hA (0, z₀)).mdifferentiableAt (by simp)) hι
  have hconst : ((Fd ∘ φ) ∘ fun z : F => ((0 : EuclideanSpace ℝ (Fin 1)), z)) =
      fun _ => c := funext hzero
  have hder := mfderiv_prodMk (I := IF) (I' := 𝓡 1) (I'' := IF)
    (f := fun _ : F => (0 : EuclideanSpace ℝ (Fin 1))) (g := id) (x := z₀)
    mdifferentiableAt_const mdifferentiableAt_id
  rw [hconst] at hcomp
  have h2 := congrArg (fun L => L b) hcomp
  have hmk : mfderiv IF ((𝓡 1).prod IF) (Prod.mk (0 : EuclideanSpace ℝ (Fin 1))) z₀ =
      (mfderiv IF (𝓡 1) (fun _ : F => (0 : EuclideanSpace ℝ (Fin 1))) z₀).prod
        (mfderiv IF IF id z₀) := hder
  rw [mfderiv_const, mfderiv_id] at hmk
  simp only [mfderiv_const, hmk] at h2
  exact h2.symm

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EF] in
/-- The horizontal part: `D(Fd ∘ φ)(0, z₀)(a, 0) = D(t ↦ Fd (φ (t, z₀)))(0) a`. -/
theorem mfderiv_comp_horizontal_BGR
    {φ : EuclideanSpace ℝ (Fin 1) × F → M} (hφ : IsSmoothEmbedding ((𝓡 1).prod IF) IM ∞ φ)
    {Fd : M → ℝ} (hFd : ContMDiff IM 𝓘(ℝ, ℝ) ∞ Fd) {z₀ : F} (a : EuclideanSpace ℝ (Fin 1)) :
    DifferentiableAt ℝ (fun t : EuclideanSpace ℝ (Fin 1) => Fd (φ (t, z₀))) 0 ∧
    fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 1) => Fd (φ (t, z₀))) 0 a =
      mfderiv ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) (Fd ∘ φ) (0, z₀)
        (show TangentSpace ((𝓡 1).prod IF) ((0 : EuclideanSpace ℝ (Fin 1)), z₀) from (a, 0)) := by
  have hA : ContMDiff ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) ∞ (Fd ∘ φ) := hFd.comp hφ.contMDiff
  have hι : MDifferentiableAt (𝓡 1) ((𝓡 1).prod IF)
      (fun t : EuclideanSpace ℝ (Fin 1) => (t, z₀)) 0 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hAd : MDifferentiableAt ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) (Fd ∘ φ)
      ((0 : EuclideanSpace ℝ (Fin 1)), z₀) :=
    (hA (0, z₀)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ)
      ((Fd ∘ φ) ∘ fun t : EuclideanSpace ℝ (Fin 1) => (t, z₀)) 0 := hAd.comp 0 hι
  refine ⟨hg.differentiableAt, ?_⟩
  have hcomp := mfderiv_comp (0 : EuclideanSpace ℝ (Fin 1)) hAd hι
  have hder := mfderiv_prodMk (I := 𝓡 1) (I' := 𝓡 1) (I'' := IF)
    (f := id) (g := fun _ : EuclideanSpace ℝ (Fin 1) => z₀) (x := (0 : EuclideanSpace ℝ (Fin 1)))
    mdifferentiableAt_id mdifferentiableAt_const
  have hmk : mfderiv (𝓡 1) ((𝓡 1).prod IF) (fun t : EuclideanSpace ℝ (Fin 1) => (t, z₀)) 0 =
      (mfderiv (𝓡 1) (𝓡 1) id 0).prod
        (mfderiv (𝓡 1) IF (fun _ : EuclideanSpace ℝ (Fin 1) => z₀) 0) := hder
  rw [mfderiv_const, mfderiv_id] at hmk
  have h2 := congrArg (fun L => L a) hcomp
  simp only [hmk] at h2
  have h3 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ((Fd ∘ φ) ∘ fun t : EuclideanSpace ℝ (Fin 1) => (t, z₀)) 0 a =
      fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 1) => Fd (φ (t, z₀))) 0 a := by
    rw [mfderiv_eq_fderiv]
    rfl
  exact h3.symm.trans h2

/-- **A regular zero of `Fd` that contains a whole slice is isolated along the base direction**:
if `φ : ℝ¹ × F → M` is a smooth embedding between manifolds of the same dimension, `Fd` smooth with
`Fd ∘ φ = 0` on `{0} × F` and `d Fd ≠ 0` at `φ (0, z₀)`, then `Fd (φ (s e₁, z₀)) = 0` only at
`s = 0` for `s` near `0`. -/
theorem exists_isOpen_slice_isolated_BGR
    {φ : EuclideanSpace ℝ (Fin 1) × F → M} (hφ : IsSmoothEmbedding ((𝓡 1).prod IF) IM ∞ φ)
    (hdim : Module.finrank ℝ EM = 1 + Module.finrank ℝ EF)
    {Fd : M → ℝ} (hFd : ContMDiff IM 𝓘(ℝ, ℝ) ∞ Fd) {z₀ : F} {c : ℝ}
    (hzero : ∀ z, Fd (φ (0, z)) = c) (hreg : mfderiv IM 𝓘(ℝ, ℝ) Fd (φ (0, z₀)) ≠ 0) :
    ∃ O : Set ℝ, IsOpen O ∧ (0 : ℝ) ∈ O ∧
      ∀ s ∈ O, Fd (φ (s • EuclideanSpace.single (0 : Fin 1) (1 : ℝ), z₀)) = c → s = 0 := by
  set e₁ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℝ) with he₁
  have hA : ContMDiff ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) ∞ (Fd ∘ φ) := hFd.comp hφ.contMDiff
  obtain ⟨hgd, hgeq⟩ := mfderiv_comp_horizontal_BGR hφ hFd (z₀ := z₀) e₁
  have hu : HasDerivAt (fun s : ℝ => Fd (φ (s • e₁, z₀)))
      (fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 1) => Fd (φ (t, z₀))) 0 e₁) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • e₁) e₁ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const e₁
    have h2 : HasFDerivAt (fun t : EuclideanSpace ℝ (Fin 1) => Fd (φ (t, z₀)))
        (fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 1) => Fd (φ (t, z₀))) 0)
        ((fun s : ℝ => s • e₁) 0) := by
      simpa using hgd.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hne : fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 1) => Fd (φ (t, z₀))) 0 e₁ ≠ 0 := by
    intro h0
    apply hreg
    have hsurj := mfderiv_surjective_of_isSmoothEmbedding_BGR hφ hdim (0, z₀)
    have hhor : ∀ a : EuclideanSpace ℝ (Fin 1),
        mfderiv ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) (Fd ∘ φ) (0, z₀)
          (show TangentSpace ((𝓡 1).prod IF) ((0 : EuclideanSpace ℝ (Fin 1)), z₀) from (a, 0)) =
          0 := fun a => by
      rw [← (mfderiv_comp_horizontal_BGR hφ hFd (z₀ := z₀) a).2]
      have ha : a = a 0 • e₁ := by
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        simp [he₁]
      rw [ha, map_smul, h0, smul_zero]
      rfl
    have hall : mfderiv ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) (Fd ∘ φ) (0, z₀) = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      obtain ⟨a, b⟩ : EuclideanSpace ℝ (Fin 1) × EF := v
      have hsplit : (show TangentSpace ((𝓡 1).prod IF) ((0 : EuclideanSpace ℝ (Fin 1)), z₀)
          from (a, b)) = (show TangentSpace ((𝓡 1).prod IF) ((0 : EuclideanSpace ℝ (Fin 1)), z₀)
            from (a, 0)) + (show TangentSpace ((𝓡 1).prod IF)
              ((0 : EuclideanSpace ℝ (Fin 1)), z₀) from (0, b)) :=
        Prod.ext (add_zero a).symm (zero_add b).symm
      change mfderiv ((𝓡 1).prod IF) 𝓘(ℝ, ℝ) (Fd ∘ φ) (0, z₀)
        (show TangentSpace ((𝓡 1).prod IF) ((0 : EuclideanSpace ℝ (Fin 1)), z₀) from (a, b)) = 0
      rw [hsplit, map_add, hhor a, mfderiv_comp_vertical_BGR hφ hFd hzero b, add_zero]
    refine ContinuousLinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := hsurj w
    have hcomp := mfderiv_comp ((0 : EuclideanSpace ℝ (Fin 1)), z₀)
      ((hFd (φ (0, z₀))).mdifferentiableAt (by simp))
      ((hφ.contMDiff (0, z₀)).mdifferentiableAt (by simp))
    have h3 := congrArg (fun L => L v) hcomp
    rw [hall] at h3
    exact h3.symm
  obtain ⟨O, hO, hOs⟩ := exists_isOpen_inter_preimage_eq_singleton_of_hasDerivAt hu hne
  refine ⟨O, hO, ?_, fun s hs hs0 => ?_⟩
  · have h0 : (0 : ℝ) ∈ ({0} : Set ℝ) := rfl
    rw [← hOs] at h0
    exact h0.1
  · have h0 : (fun s : ℝ => Fd (φ (s • e₁, z₀))) 0 = c := by
      simp only [zero_smul]
      exact hzero z₀
    have hmem : s ∈ O ∩ (fun s : ℝ => Fd (φ (s • e₁, z₀))) ⁻¹'
        {(fun s : ℝ => Fd (φ (s • e₁, z₀))) 0} :=
      ⟨hs, by rw [mem_preimage, mem_singleton_iff, h0]; exact hs0⟩
    rw [hOs] at hmem
    exact hmem

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Isolation of the base value of a regular zero set that is saturated over a product chart**:
`f` has a smooth product chart (`k = 1`, fibre `F`) at `w`, `Fd` is smooth and vanishes on the
fibre `X ∩ f⁻¹{w}`, `{Fd = 0} ∩ X` is saturated (a union of whole `f`-fibres inside `X`), and
`d Fd ≠ 0` at a point `p` of the fibre; then `w` is isolated in `f '' ({Fd = 0} ∩ X)`. -/
theorem exists_isOpen_inter_image_zero_eq_singleton_BGR
    {f : M → H} {X : Set M} {B : Set H} {w : H}
    (hchart : SmoothProductChartAt_BIFc IM IF (F := F) 1 f X B w) (hB : f '' X ⊆ B)
    (hdim : Module.finrank ℝ EM = 1 + Module.finrank ℝ EF)
    {Fd : M → ℝ} (hFd : ContMDiff IM 𝓘(ℝ, ℝ) ∞ Fd) {c : ℝ}
    (hfib : ∀ q ∈ X, f q = w → Fd q = c)
    (hsat : ∀ q ∈ X, ∀ q' ∈ X, f q = f q' → Fd q = c → Fd q' = c)
    {p : M} (hpX : p ∈ X) (hpw : f p = w) (hreg : mfderiv IM 𝓘(ℝ, ℝ) Fd p ≠ 0) :
    ∃ O : Set H, IsOpen O ∧ O ∩ f '' ({q | Fd q = c} ∩ X) = {w} := by
  obtain ⟨σ, φ, O', h0, hσs, hσe, hσi, hO', hrσ, hφ, hr, hf⟩ := hchart
  have hp_mem : p ∈ X ∩ f ⁻¹' range σ := ⟨hpX, ⟨0, by rw [h0, hpw]⟩⟩
  rw [← hr] at hp_mem
  obtain ⟨⟨t₁, z₀⟩, hp⟩ := hp_mem
  have ht₁ : t₁ = 0 := hσe.injective (by rw [← hf t₁ z₀, hp, hpw, h0])
  subst ht₁
  have hzero : ∀ z, Fd (φ (0, z)) = c := fun z => by
    have hmem : φ (0, z) ∈ range φ := mem_range_self _
    rw [hr] at hmem
    exact hfib _ hmem.1 (by rw [hf, h0])
  have hreg' : mfderiv IM 𝓘(ℝ, ℝ) Fd (φ (0, z₀)) ≠ 0 := by
    rw [show φ ((0 : EuclideanSpace ℝ (Fin 1)), z₀) = p from hp]
    exact hreg
  obtain ⟨Os, hOs, h0Os, hOsE⟩ := exists_isOpen_slice_isolated_BGR hφ hdim hFd hzero hreg'
  set O₁ : Set (EuclideanSpace ℝ (Fin 1)) := (fun t => t 0) ⁻¹' Os with hO₁def
  have hO₁ : IsOpen O₁ := hOs.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous
  have h0O₁ : (0 : EuclideanSpace ℝ (Fin 1)) ∈ O₁ := h0Os
  have hkey : ∀ t ∈ O₁, Fd (φ (t, z₀)) = c → t = 0 := fun t ht h => by
    have htt : t = t 0 • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp
    have h' := hOsE (t 0) ht (by rw [← htt]; exact h)
    rw [htt, h', zero_smul]
  obtain ⟨V, hV, hVO⟩ := hσe.isInducing.isOpen_iff.mp hO₁
  have hφX : ∀ t z, φ (t, z) ∈ X := fun t z => by
    have hmem : φ (t, z) ∈ range φ := mem_range_self _
    rw [hr] at hmem
    exact hmem.1
  refine ⟨V ∩ O', hV.inter hO', ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyV, hyO'⟩, q, ⟨hqF, hqX⟩, rfl⟩
    have hyσ : f q ∈ range σ := by
      rw [hrσ]
      exact ⟨hB ⟨q, hqX, rfl⟩, hyO'⟩
    obtain ⟨t, ht⟩ := hyσ
    have htO₁ : t ∈ O₁ := by
      rw [← hVO]
      change σ t ∈ V
      rw [ht]
      exact hyV
    have hqφ : q ∈ range φ := by
      rw [hr]
      exact ⟨hqX, ⟨t, ht⟩⟩
    obtain ⟨⟨t', z⟩, hq⟩ := hqφ
    have htt' : t' = t := hσe.injective (by rw [← hf t' z, hq, ht])
    have hfeq : f q = f (φ (t, z₀)) := by rw [hf, ht]
    have hz : Fd (φ (t, z₀)) = c := hsat q hqX _ (hφX t z₀) hfeq hqF
    have ht0 := hkey t htO₁ hz
    subst ht0
    rw [mem_singleton_iff, ← ht, h0]
  · intro hy
    rw [mem_singleton_iff] at hy
    subst hy
    have hFp : Fd p = c := hfib p hpX hpw
    refine ⟨⟨?_, ?_⟩, p, ⟨hFp, hpX⟩, hpw⟩
    · have : (0 : EuclideanSpace ℝ (Fin 1)) ∈ σ ⁻¹' V := by rw [hVO]; exact h0O₁
      rw [mem_preimage, h0] at this
      exact this
    · have : σ 0 ∈ range σ := mem_range_self _
      rw [hrσ] at this
      rw [h0] at this
      exact this.2

end Generic

end DifferentialGeometry.Geometry.Collapse
