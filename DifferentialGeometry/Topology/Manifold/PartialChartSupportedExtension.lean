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
  let c : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
    { e.symm with contMDiffOn_toFun := hei, contMDiffOn_invFun := he }
  exact c.exists_diffeomorph_family_extension (IP := 𝓘(ℝ, P)) D
    (hD.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd))
    (hDi.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)) hK hKt
    (fun p z hz => (hfix p z hz).1)

private theorem mapsTo_of_injective_of_fix_compl {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K U : Set X} (hKU : K ⊆ U)
    (hfix : ∀ x, x ∉ K → f x = x) : MapsTo f U U := by
  intro x hx
  by_contra hfx
  have he : f (f x) = f x := hfix _ (fun h ↦ hfx (hKU h))
  exact hfx ((hf he).symm ▸ hx)

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
    apply extendChartById_mem_iff e (D p) hmap hA (hB p) (houtside p) _ x
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
