import DifferentialGeometry.Topology.Morse.RegularLevel.VectorField

open Set Filter Manifold Topology
open scoped ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_unitSpeedVectorField_eq_nhds_on_compact
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K C U : Set M}
    (hK : IsCompact K) (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I f x)
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U)
    (W : (x : M) → TangentSpace I x)
    (hW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle I M)) U)
    (hWdf : ∀ x ∈ U,
      (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (W x)) = -1) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ K, (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ≤ 0) ∧
      ∀ᶠ x in 𝓝ˢ C, V x = W x := by
  obtain ⟨V₀, hV₀, hsupp₀, hdf₀, hrate₀⟩ :=
    exists_unitSpeedVectorField_on_compact I f hf K hK hregular
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨B, hB, hCB, hBU, hBcompact⟩ := exists_open_between_and_isCompact_closure hC hU hCU
  obtain ⟨A, hA, hCA, hAB, _⟩ := exists_open_between_and_isCompact_closure hC hB hCB
  obtain ⟨ρ, hρzero, hρone, hρbound⟩ := exists_contMDiffMap_zero_one_of_isClosed I
    hB.isClosed_compl isClosed_closure
    (disjoint_left.mpr (fun x hxB hxA => hxB (hAB hxA))) (n := ⊤)
  have hsuppρ : tsupport (ρ : M → ℝ) ⊆ closure B := by
    apply closure_mono
    intro x hx
    by_contra hxB
    exact hx (hρzero hxB)
  have hρW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, (ρ x : ℝ) • W x⟩ : TangentBundle I M)) :=
    ContMDiffOn.smul_section_of_tsupport ρ.contMDiff.contMDiffOn hU (hsuppρ.trans hBU) hW
  let V : (x : M) → TangentSpace I x := fun x => (1 - ρ x) • V₀ x + (ρ x : ℝ) • W x
  have hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) :=
    ((contMDiff_const.sub ρ.contMDiff).smul_section hV₀).add_section hρW
  have hsuppV : tsupport V ⊆ tsupport V₀ ∪ closure B := by
    apply (closure_minimal ?_ ((isClosed_tsupport V₀).union isClosed_closure))
    intro x hx
    by_contra hxunion
    have hxV₀ : x ∉ tsupport V₀ := fun h => hxunion (Or.inl h)
    have hxB : x ∉ B := fun h => hxunion (Or.inr (subset_closure h))
    have hzero : V₀ x = 0 := Function.notMem_support.mp (fun h => hxV₀ (subset_tsupport V₀ h))
    exact hx (by
      simp only [V, hzero, hρzero hxB, Pi.zero_apply, sub_zero, one_smul, zero_smul, add_zero]
      rfl)
  let d (x : M) : TangentSpace I x →L[ℝ] ℝ :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, ℝ) f x)
  have hformula (x : M) : d x (V x) = (1 - ρ x) * d x (V₀ x) + ρ x * d x (W x) := by
    simp only [V, map_add, map_smul, smul_eq_mul]
  have hzero_outside {x : M} (hx : x ∉ U) : ρ x = 0 :=
    hρzero (fun hxB => hx (hBU (subset_closure hxB)))
  refine ⟨V, hV, (hsupp₀.union hBcompact).of_isClosed_subset (isClosed_tsupport V) hsuppV, ?_, ?_, ?_⟩
  · intro x hx
    change d x (V x) = -1
    rw [hformula, show d x (V₀ x) = -1 from hdf₀ x hx]
    by_cases hxU : x ∈ U
    · rw [show d x (W x) = -1 from hWdf x hxU]
      ring
    · rw [hzero_outside hxU]
      ring
  · intro x
    change -1 ≤ d x (V x) ∧ d x (V x) ≤ 0
    have hrate : -1 ≤ d x (V₀ x) ∧ d x (V₀ x) ≤ 0 := hrate₀ x
    rw [hformula]
    by_cases hxU : x ∈ U
    · rw [show d x (W x) = -1 from hWdf x hxU]
      have hb := hρbound x
      have hnonneg : 0 ≤ 1 - ρ x := by linarith [hb.2]
      constructor
      · nlinarith [mul_nonneg hnonneg (show 0 ≤ d x (V₀ x) + 1 by linarith [hrate.1])]
      · nlinarith [hb.1, mul_nonpos_of_nonneg_of_nonpos hnonneg hrate.2]
    · simpa only [hzero_outside hxU, sub_zero, one_mul, zero_mul, add_zero] using hrate
  · filter_upwards [hA.mem_nhdsSet.mpr hCA] with x hx
    simp only [V, hρone (subset_closure hx), Pi.one_apply, sub_self, zero_smul, one_smul, zero_add]

theorem exists_unitSpeedVectorField_eq_nhds_on_union
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I f x)
    {ι : Type*} {C U : ι → Set M} (hC : IsCompact (⋃ i, C i))
    (hU : ∀ i, IsOpen (U i)) (hCU : ∀ i, C i ⊆ U i)
    (W : ι → (x : M) → TangentSpace I x)
    (hW : ∀ i, ContMDiffOn I I.tangent ∞
      (fun x => (⟨x, W i x⟩ : TangentBundle I M)) (U i))
    (hWdf : ∀ i, ∀ x ∈ U i,
      (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (W i x)) = -1)
    (hagree : ∀ i j, ∀ x ∈ U i ∩ U j, W i x = W j x) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ K, (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (V x)) ≤ 0) ∧
      ∀ i, ∀ᶠ x in 𝓝ˢ (C i), V x = W i x := by
  classical
  let W₀ : (x : M) → TangentSpace I x := fun x =>
    if h : ∃ i, x ∈ U i then W (Classical.choose h) x else 0
  have heq (i : ι) {x : M} (hx : x ∈ U i) : W₀ x = W i x := by
    dsimp only [W₀]
    rw [dif_pos ⟨i, hx⟩]
    exact hagree _ i x ⟨Classical.choose_spec (show ∃ j, x ∈ U j from ⟨i, hx⟩), hx⟩
  have hW₀ : ContMDiffOn I I.tangent ∞
      (fun x => (⟨x, W₀ x⟩ : TangentBundle I M)) (⋃ i, U i) := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have hlocal : (fun y => (⟨y, W₀ y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
        (fun y => (⟨y, W i y⟩ : TangentBundle I M)) := by
      filter_upwards [(hU i).mem_nhds hxi] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle I M)) (heq i hy)
    exact (((hW i x hxi).contMDiffAt ((hU i).mem_nhds hxi)).congr_of_eventuallyEq
      hlocal).contMDiffWithinAt
  have hdf₀ : ∀ x ∈ ⋃ i, U i,
      (NormedSpace.fromTangentSpace (f x)) (mfderiv I 𝓘(ℝ, ℝ) f x (W₀ x)) = -1 := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rw [heq i hxi]
    exact hWdf i x hxi
  obtain ⟨V, hV, hsupp, hdf, hrate, hVW⟩ :=
    exists_unitSpeedVectorField_eq_nhds_on_compact hf hK hregular hC
      (isOpen_iUnion hU) (iUnion_mono hCU) W₀ hW₀ hdf₀
  refine ⟨V, hV, hsupp, hdf, hrate, ?_⟩
  intro i
  filter_upwards [hVW.filter_mono (nhdsSet_mono (subset_iUnion C i)),
    (hU i).mem_nhdsSet.mpr (hCU i)] with x hx hxi
  exact hx.trans (heq i hxi)

end DifferentialGeometry.Topology.Morse
