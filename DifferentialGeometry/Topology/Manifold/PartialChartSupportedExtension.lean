/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SupportedExtension

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F P H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ F H}

private theorem mapsTo_of_injective_of_fix_compl {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K U : Set X} (hKU : K ⊆ U)
    (hfix : ∀ x, x ∉ K → f x = x) : MapsTo f U U := by
  intro x hx
  by_contra hfx
  have he : f (f x) = f x := hfix _ (fun h ↦ hfx (hKU h))
  exact hfx ((hf he).symm ▸ hx)

theorem contMDiff_extendChartById_of_mapsTo [T2Space M]
    (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    {f : P × E → E} (hf : ContDiff ℝ ∞ f)
    (hmap : ∀ p, MapsTo (fun z ↦ f (p, z)) e.target e.target)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ p z, z ∉ K → f (p, z) = z) :
    ContMDiff (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M ↦ extendChartById e (fun z ↦ f (q.1, z)) q.2) := by
  exact contMDiff_extendById_of_contMDiff_of_mapsTo e he hei
    (hf.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)) hmap hK hKt hfix

omit [NormedSpace ℝ E] in
theorem leftInverse_extendChartById_of_mapsTo
    (e : OpenPartialHomeomorph M E) {f g : E → E}
    (hgf : Function.LeftInverse g f) (hf : MapsTo f e.target e.target) :
    Function.LeftInverse (extendChartById e g) (extendChartById e f) := by
  exact leftInverse_extendById_of_mapsTo e hgf hf

theorem exists_diffeomorph_extension_of_partial_chart_family [T2Space M]
    (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (D : P → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hD : ContDiff ℝ ∞ (fun q : P × E ↦ D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : P × E ↦ (D q.1).symm q.2))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ p z, z ∉ K → D p z = z ∧ (D p).symm z = z) :
    ∃ J : P → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M ↦ (J q.1).symm q.2) ∧
      (∀ p x, J p x = extendChartById e (D p) x ∧
        (J p).symm x = extendChartById e (D p).symm x) ∧
      IsCompact (e.symm '' K) ∧ e.symm '' K ⊆ e.source ∧
      ∀ p x, x ∉ e.symm '' K → J p x = x ∧ (J p).symm x = x := by
  have hmap (p : P) : MapsTo (D p) e.target e.target :=
    mapsTo_of_injective_of_fix_compl (D p).injective hKt (fun z hz ↦ (hfix p z hz).1)
  have hmapi (p : P) : MapsTo (D p).symm e.target e.target :=
    mapsTo_of_injective_of_fix_compl (D p).symm.injective hKt (fun z hz ↦ (hfix p z hz).2)
  have hF := contMDiff_extendChartById_of_mapsTo e he hei hD hmap hK hKt
    (fun p z hz ↦ (hfix p z hz).1)
  have hG := contMDiff_extendChartById_of_mapsTo e he hei hDi hmapi hK hKt
    (fun p z hz ↦ (hfix p z hz).2)
  let J (p : P) : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := extendChartById e (D p)
          invFun := extendChartById e (D p).symm
          left_inv := leftInverse_extendChartById_of_mapsTo e (D p).symm_apply_apply (hmap p)
          right_inv := leftInverse_extendChartById_of_mapsTo e (D p).apply_symm_apply (hmapi p) }
      contMDiff_toFun := hF.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hG.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨J, hF, hG, fun _ _ ↦ ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact hK.image_of_continuousOn (hei.continuousOn.mono hKt)
  · rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hKt hz)
  · intro p x hx
    exact ⟨extendChartById_eq_of_notMem_image e _ (fun z hz ↦ (hfix p z hz).1) hx,
      extendChartById_eq_of_notMem_image e _ (fun z hz ↦ (hfix p z hz).2) hx⟩

theorem exists_diffeomorph_family_image_of_partial_chart [T2Space M]
    (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (D : P → E ≃ₘ[ℝ] E)
    (hD : ContDiff ℝ ∞ (fun q : P × E => D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : P × E => (D q.1).symm q.2))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ p z, z ∉ K → D p z = z ∧ (D p).symm z = z)
    {A : Set M} {B : P → Set M} {C : Set E} {T : P → Set E}
    (hA : e.IsImage A C) (hB : ∀ p, e.IsImage (B p) (T p))
    (houtside : ∀ p x, x ∉ e.source → (x ∈ A ↔ x ∈ B p))
    (himage : ∀ p, D p '' C = T p) :
    ∃ J : P → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M => (J q.1).symm q.2) ∧
      (∀ p, J p '' A = B p) ∧
      (∀ p x, J p x = extendChartById e (D p) x ∧
        (J p).symm x = extendChartById e (D p).symm x) ∧
      IsCompact (e.symm '' K) ∧ e.symm '' K ⊆ e.source ∧
      ∀ p x, x ∉ e.symm '' K → J p x = x ∧ (J p).symm x = x := by
  obtain ⟨J, hJ, hJi, hJe, hJK, hJKs, hJfix⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family e he hei D hD hDi hK hKt hfix
  refine ⟨J, hJ, hJi, ?_, hJe, hJK, hJKs, hJfix⟩
  intro p
  have hmap : MapsTo (D p) e.target e.target :=
    mapsTo_of_injective_of_fix_compl (D p).injective hKt (fun z hz => (hfix p z hz).1)
  have hm (x : M) : J p x ∈ B p ↔ x ∈ A := by
    rw [(hJe p x).1]
    apply OpenPartialHomeomorph.extendById_mem_iff e (D p) hmap hA (hB p) (houtside p) _ x
    intro y _
    rw [← himage p, Set.mem_image]
    exact ⟨fun ⟨z, hz, hzy⟩ => (D p).injective hzy ▸ hz,
      fun hy => ⟨y, hy, rfl⟩⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hm y).mpr hy
  · intro hx
    refine ⟨(J p).symm x, ?_, (J p).apply_symm_apply x⟩
    apply (hm _).mp
    rwa [(J p).apply_symm_apply]

end DifferentialGeometry.Topology.Manifold
