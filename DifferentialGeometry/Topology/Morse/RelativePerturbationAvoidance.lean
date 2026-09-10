import DifferentialGeometry.Topology.Morse.RelativePerturbationManifold

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace Poincare.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}


theorem surjective_parameterDifferential_partialDiffeomorph_symm_iff {n : ℕ} {φ : Fin n → M → ℝ}
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {z : E} (hz : z ∈ c.target) :
    Surjective (parameterDifferential (I := 𝓘(ℝ, E)) (fun i w => φ i (c.symm w)) z) ↔
      Surjective (parameterDifferential (I := I) φ (c.symm z)) := by
  refine ⟨?_,surjective_parameterDifferential_partialDiffeomorph_symm hφ c hz⟩
  intro h B
  let L : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  have hL : L.IsInvertible := Poincare.VectorField.isInvertible_mfderiv_partialDiffeomorph c.symm (by simp) hz
  obtain ⟨p,hp⟩ := h (B.comp L)
  refine ⟨p,?_⟩
  rw [parameterDifferential_partialDiffeomorph_symm hφ c hz] at hp
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := hL.surjective v
  exact congrArg (fun T : E →L[ℝ] ℝ => T w) hp

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]


theorem exists_open_surjective_parameterDifferential {n : ℕ} {φ : Fin n → M → ℝ}
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) {x : M} (hx : I.IsInteriorPoint x)
    (hreg : Surjective (parameterDifferential (I := I) φ x)) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V,
      I.IsInteriorPoint y ∧ Surjective (parameterDifferential (I := I) φ y) := by
  obtain ⟨W,F,hW,hxW,hWc,hF⟩ := exists_contDiff_interiorChart_extensions hφ hx
  let c := Poincare.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have heq : ∀ z ∈ W, parameterDifferential (I := 𝓘(ℝ, E)) F z =
      parameterDifferential (I := 𝓘(ℝ, E)) (fun i w => φ i (c.symm w)) z := by
    intro z hz
    apply parameterDifferential_eq_of_eventuallyEq
    intro i
    filter_upwards [hW.mem_nhds hz] with w hw
    exact (hF i).2.2.2 hw
  let R := {z : E | Surjective (parameterDifferential (I := 𝓘(ℝ, E)) F z)}
  have hR : IsOpen R := isOpen_regularPerturbationBase (fun i => (hF i).1)
  have hxR : c x ∈ R := by
    change Surjective (parameterDifferential (I := 𝓘(ℝ, E)) F (c x))
    rw [heq _ hxW]
    apply surjective_parameterDifferential_partialDiffeomorph_symm hφ c (hWc hxW)
    exact (congrArg (fun t => Surjective (parameterDifferential (I := I) φ t)) (c.left_inv hxc)).mpr hreg
  refine ⟨c.source ∩ c ⁻¹' (W ∩ R),
    c.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage c.open_source (hW.inter hR),
    ⟨hxc,hxW,hxR⟩,?_⟩
  intro y hy
  refine ⟨Poincare.Manifold.isInteriorPoint_of_mem_interiorChart_source I ∞ (by simp) hy.1,?_⟩
  have hyR : Surjective (parameterDifferential (I := 𝓘(ℝ, E)) F (c y)) := hy.2.2
  rw [heq _ hy.2.1] at hyR
  have hh := (surjective_parameterDifferential_partialDiffeomorph_symm_iff hφ c (hWc hy.2.1)).mp hyR
  exact (congrArg (fun t => Surjective (parameterDifferential (I := I) φ t)) (c.left_inv hy.1)).mp hh


theorem eventually_mfderiv_finitePerturbation_ne_zero {n : ℕ} {f : M → ℝ}
    {φ : Fin n → M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) {x : M} (hx : I.IsInteriorPoint x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∀ᶠ q : (Fin n → ℝ) × M in 𝓝 (0,x), mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ q.1) q.2 ≠ 0 := by
  let g : Option (Fin n) → M → ℝ := fun i => match i with | none => f | some j => φ j
  have hg : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (g i) := by
    intro i
    cases i with
    | none => exact hf
    | some j => exact hφ j
  obtain ⟨W,F,hW,hxW,hWc,hF⟩ := exists_contDiff_interiorChart_extensions hg hx
  let c := Poincare.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hccont : ContinuousAt c x := c.toOpenPartialHomeomorph.continuousOn.continuousAt (c.open_source.mem_nhds hxc)
  have hFeq : ∀ p z, z ∈ W → finitePerturbation (F none) (fun i => F (some i)) p =ᶠ[𝓝 z]
      (fun w => finitePerturbation f φ p (c.symm w)) := by
    intro p z hz
    filter_upwards [hW.mem_nhds hz] with w hw
    unfold finitePerturbation
    congr 1
    · exact (hF none).2.2.2 hw
    · exact Finset.sum_congr rfl fun i _ => congrArg (fun t : ℝ => p i * t) ((hF (some i)).2.2.2 hw)
  let G := perturbationDifferential (F none) (fun i => F (some i))
  have hG : Continuous G := (contDiff_perturbationDifferential (hF none).1 (fun i => (hF (some i)).1)).continuous
  have hG0 : G (0,c x) ≠ 0 := by
    change fderiv ℝ (finitePerturbation (F none) (fun i => F (some i)) 0) (c x) ≠ 0
    rw [(hFeq 0 (c x) hxW).fderiv_eq,finitePerturbation_zero]
    intro hz
    have hh := (fderiv_scalar_partialDiffeomorph_symm_eq_zero_iff hf c (hWc hxW)).mp hz
    let D : M → E →L[ℝ] ℝ := fun y => mfderiv I 𝓘(ℝ, ℝ) f y
    apply hcrit
    exact (congrArg D (c.left_inv hxc)).symm.trans hh
  have hJ : ContinuousAt (fun q : (Fin n → ℝ) × M => (q.1,c q.2)) (0,x) :=
    continuous_fst.continuousAt.prodMk (hccont.comp (continuous_snd.continuousAt))
  have hnear : ∀ᶠ q : (Fin n → ℝ) × M in 𝓝 (0,x), G (q.1,c q.2) ≠ 0 :=
    hJ.eventually ((isOpen_ne.preimage hG).mem_nhds hG0)
  have hsource : ∀ᶠ q : (Fin n → ℝ) × M in 𝓝 (0,x), q.2 ∈ c.source :=
    continuous_snd.continuousAt.eventually (c.open_source.mem_nhds hxc)
  have hWnear : ∀ᶠ q : (Fin n → ℝ) × M in 𝓝 (0,x), c q.2 ∈ W :=
    (hccont.comp continuous_snd.continuousAt).eventually (hW.mem_nhds hxW)
  filter_upwards [hnear,hsource,hWnear] with q hq hqs hqW
  intro hqcrit
  apply hq
  change fderiv ℝ (finitePerturbation (F none) (fun i => F (some i)) q.1) (c q.2) = 0
  rw [(hFeq q.1 (c q.2) hqW).fderiv_eq]
  apply (fderiv_scalar_partialDiffeomorph_symm_eq_zero_iff (contMDiff_finitePerturbation hf hφ q.1)
    c (hWc hqW)).mpr
  let D : M → E →L[ℝ] ℝ := fun y => mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ q.1) y
  exact (congrArg D (c.left_inv hqs)).trans hqcrit


theorem exists_radius_mfderiv_finitePerturbation_ne_zero {n : ℕ} {f : M → ℝ}
    {φ : Fin n → M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) {K : Set M}
    (hK : IsCompact K) (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hcrit : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : Fin n → ℝ, ‖p‖ < ε → ∀ x ∈ K,
      mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x ≠ 0 := by
  have hnear : ∀ᶠ p : Fin n → ℝ in 𝓝 0, ∀ x ∈ K,
      mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x ≠ 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact eventually_mfderiv_finitePerturbation_ne_zero hf hφ (hKI x hx) (hcrit x hx)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨ε,hε,fun p hp => hball (by simpa only [Metric.mem_ball,dist_zero_right] using hp)⟩


theorem exists_open_radius_critical_mem_surjective_parameterDifferential {n : ℕ} {f : M → ℝ}
    {φ : Fin n → M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i))
    (hc : ∀ i, HasCompactSupport (φ i))
    (hs : ∀ i, tsupport (φ i) ⊆ {x | I.IsInteriorPoint x})
    {K : Set M} (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hreg : ∀ x ∈ K, Surjective (parameterDifferential (I := I) φ x))
    (hcrit : ∀ x, mfderiv I 𝓘(ℝ, ℝ) f x = 0 → x ∈ K) :
    ∃ (R : Set M) (ε : ℝ), IsOpen R ∧ K ⊆ R ∧
      (∀ x ∈ R, I.IsInteriorPoint x ∧ Surjective (parameterDifferential (I := I) φ x)) ∧
      0 < ε ∧ ∀ p : Fin n → ℝ, ‖p‖ < ε → ∀ x,
        mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x = 0 → x ∈ R := by
  classical
  choose V hV hxV hregV using fun x : K =>
    exists_open_surjective_parameterDifferential hφ (hKI x x.property) (hreg x x.property)
  let R : Set M := ⋃ x : K, V x
  have hR : IsOpen R := isOpen_iUnion hV
  have hKR : K ⊆ R := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hRR : ∀ x ∈ R, I.IsInteriorPoint x ∧ Surjective (parameterDifferential (I := I) φ x) := by
    intro x hx
    obtain ⟨y,hy⟩ := mem_iUnion.mp hx
    exact hregV y x hy
  let C : Set M := ⋃ i, tsupport (φ i)
  have hC : IsCompact C := isCompact_iUnion hc
  have hCI : C ⊆ {x | I.IsInteriorPoint x} := iUnion_subset hs
  have hL : IsCompact (C ∩ Rᶜ) := hC.inter_right hR.isClosed_compl
  obtain ⟨ε,hε,havoid⟩ := exists_radius_mfderiv_finitePerturbation_ne_zero hf hφ hL
    (fun x hx => hCI hx.1) (fun x hx hzero => hx.2 (hKR (hcrit x hzero)))
  obtain ⟨N,hN,hCN,hfix⟩ := exists_open_finitePerturbation_eq (f := f) (φ := φ)
    (U := C) (fun i => subset_iUnion (fun i => tsupport (φ i)) i)
  refine ⟨R,ε,hR,hKR,hRR,hε,fun p hp x hx => ?_⟩
  by_cases hxC : x ∈ C
  · by_contra hxR
    exact havoid p hp x ⟨hxC,hxR⟩ hx
  · have heq : finitePerturbation f φ p =ᶠ[𝓝 x] f := by
      filter_upwards [hN.mem_nhds (hCN hxC)] with y hy
      exact hfix p hy
    apply hKR
    apply hcrit
    exact heq.mfderiv_eq.symm.trans hx

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem critical_finitePerturbation_mem_support_union {n : ℕ} {f : M → ℝ}
    {φ : Fin n → M → ℝ} {K : Set M}
    (hcrit : ∀ x, mfderiv I 𝓘(ℝ, ℝ) f x = 0 → x ∈ K)
    (p : Fin n → ℝ) {x : M} (hx : mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x = 0) :
    x ∈ (⋃ i, tsupport (φ i)) ∪ K := by
  by_cases hxC : x ∈ ⋃ i, tsupport (φ i)
  · exact Or.inl hxC
  · apply Or.inr
    obtain ⟨N,hN,hCN,hfix⟩ := exists_open_finitePerturbation_eq (f := f) (φ := φ)
      (U := ⋃ i, tsupport (φ i)) (fun i => subset_iUnion (fun i => tsupport (φ i)) i)
    have heq : finitePerturbation f φ p =ᶠ[𝓝 x] f := by
      filter_upwards [hN.mem_nhds (hCN hxC)] with y hy
      exact hfix p hy
    exact hcrit x (heq.mfderiv_eq.symm.trans hx)

end Poincare.Morse
