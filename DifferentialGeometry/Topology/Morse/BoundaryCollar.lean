import DifferentialGeometry.Topology.Diffeomorph.Collar
import DifferentialGeometry.Topology.Morse.BoundaryRegularVectorField

open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.Morse

private theorem exists_contDiff_boundary_tangent_unit_field_near_compact
    {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} {B W : Set (Fin (n + 1) → ℝ)}
    (hg : ContDiff ℝ ∞ g) (hB : IsCompact B) (hW : IsOpen W) (hBW : B ⊆ W)
    (hregular : ∀ z ∈ B, z 0 ≠ 0 → fderiv ℝ g z ≠ 0)
    (hboundary : ∀ z ∈ B, z 0 = 0 →
      fderiv ℝ (fun x : Fin n → ℝ => g (Fin.cons 0 x)) (Fin.tail z) ≠ 0) :
    ∃ Y : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
      ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      (∀ z, z 0 = 0 → Y z 0 = 0) ∧
      (∀ z, 0 ≤ fderiv ℝ g z (Y z) ∧ fderiv ℝ g z (Y z) ≤ 1) ∧
      ∃ N, IsOpen N ∧ B ⊆ N ∧ N ⊆ W ∧
        ∀ z ∈ N, fderiv ℝ g z (Y z) = 1 := by
  let F : ℝ × (Fin (n + 1) → ℝ) → ℝ := fun p => g p.2 - p.1
  let ι : (Fin (n + 1) → ℝ) → ℝ × (Fin (n + 1) → ℝ) := fun z => (0, z)
  have hι : ContDiff ℝ ∞ ι := contDiff_const.prodMk contDiff_id
  have hF : ContDiff ℝ ∞ F := (hg.comp contDiff_snd).sub contDiff_fst
  have hKW : ι '' B ⊆ Prod.snd ⁻¹' W := by
    rintro p ⟨z, hz, rfl⟩
    exact hBW hz
  have hKregular : ∀ p ∈ ι '' B, p.2 0 ≠ 0 →
      fderiv ℝ (fun z => F (p.1, z)) p.2 ≠ 0 := by
    rintro p ⟨z, hz, rfl⟩ hzero
    simpa only [F, ι, sub_zero] using hregular z hz hzero
  have hKboundary : ∀ p ∈ ι '' B, p.2 0 = 0 →
      fderiv ℝ (fun x : Fin n → ℝ => F (p.1, Fin.cons 0 x)) (Fin.tail p.2) ≠ 0 := by
    rintro p ⟨z, hz, rfl⟩ hzero
    simpa only [F, ι, sub_zero] using hboundary z hz hzero
  obtain ⟨V, hV, hVc, hVs, hVb, _, U, hU, hKU, hUW, hrate⟩ :=
    exists_contDiff_boundary_tangent_vector_field_near_compact hF
      (hB.image hι.continuous) (hW.preimage continuous_snd) hKW hKregular hKboundary
  let Y := V ∘ ι
  have hYc : HasCompactSupport Y := by
    apply HasCompactSupport.of_support_subset_isCompact (hVc.isCompact.image continuous_snd)
    intro z hz
    exact ⟨ι z, subset_tsupport V hz, rfl⟩
  have hYs : tsupport Y ⊆ W := by
    intro z hz
    exact hVs (tsupport_comp_subset_preimage V hι.continuous hz)
  let N := ι ⁻¹' U
  have hN : IsOpen N := hU.preimage hι.continuous
  have hBN : B ⊆ N := fun z hz => hKU ⟨z, hz, rfl⟩
  have hNW : N ⊆ W := fun _ hz => hUW hz
  have hYrate : ∀ z ∈ N, fderiv ℝ g z (Y z) = 1 := by
    intro z hz
    simpa only [Y, Function.comp_def, F, ι, sub_zero, deriv_const_sub_id, neg_neg] using
      hrate (ι z) hz
  obtain ⟨C, _, hBC, hCN⟩ := exists_compact_between hB hN hBN
  obtain ⟨ψ, hψone, hψzero, hψrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, Fin (n + 1) → ℝ)
      hB.isClosed hBC (n := ⊤)
  obtain ⟨Q, hQ, hBQ, hQone⟩ := eventually_nhdsSet_iff_exists.mp hψone
  let Z := fun z => ψ z • Y z
  have hψ : ContDiff ℝ ∞ ψ := contMDiff_iff_contDiff.mp ψ.contMDiff
  have hs : Function.support Z ⊆ Function.support Y := by
    intro z hz hy
    exact hz (by simp only [Z, hy, smul_zero])
  have hZrate (z) : fderiv ℝ g z (Z z) = ψ z := by
    by_cases hzero : ψ z = 0
    · simp only [Z, hzero, zero_smul, map_zero]
    · have hzC : z ∈ C := by
        by_contra hn
        exact hzero (hψzero z hn)
      simp only [Z, map_smul, hYrate z (hCN hzC), smul_eq_mul, mul_one]
  refine ⟨Z, hψ.smul (hV.comp hι), hYc.mono hs,
    (closure_mono hs).trans hYs, ?_, ?_, Q ∩ N, hQ.inter hN,
    Set.subset_inter hBQ hBN, (fun _ hz => hNW hz.2), ?_⟩
  · intro z hz
    change ψ z * V (ι z) 0 = 0
    rw [hVb (ι z) hz, mul_zero]
  · intro z
    rw [hZrate]
    exact hψrange z
  · intro z hz
    rw [hZrate, hQone z hz.1]


private theorem fderiv_collar_velocity_eq_one
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    (Φ : OpenPartialHomeomorph (N × ℝ) E)
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ Φ.source)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ)
    (hheight : ∀ q ∈ Φ.source, f (Φ q) = c + q.2)
    (x : E) (hx : x ∈ Φ.target) :
    fderiv ℝ f x
      (deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2) = 1 := by
  let q := Φ.symm x
  have hq : q ∈ Φ.source := Φ.map_target hx
  have hsm : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun t => Φ (q.1, t)) q.2 :=
    (hΦ.contMDiffAt (Φ.open_source.mem_nhds hq)).comp q.2
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hd := (contMDiffAt_iff_contDiffAt.mp hsm).differentiableAt (by simp)
  have hcomp := ((hf.differentiable (by simp) x).hasFDerivAt).comp_hasDerivAt_of_eq
    q.2 hd.hasDerivAt (Φ.right_inv hx).symm
  have heq : (fun t => f (Φ (q.1, t))) =ᶠ[𝓝 q.2] fun t => c + t := by
    have hc : Continuous (fun t : ℝ => (q.1, t)) :=
      continuous_const.prodMk continuous_id
    filter_upwards [hc.continuousAt (Φ.open_source.mem_nhds hq)] with t ht
    exact hheight (q.1, t) ht
  have hone : HasDerivAt (fun t => f (Φ (q.1, t))) 1 q.2 :=
    ((hasDerivAt_id q.2).const_add c).congr_of_eventuallyEq heq
  exact hcomp.unique hone

theorem exists_contDiff_boundary_tangent_vector_field_eq_collar_velocity
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) (Fin (n + 1) → ℝ))
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target)
    {g : (Fin (n + 1) → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) {c : ℝ}
    (hheight : ∀ q ∈ Φ.source, g (Φ q) = c + q.2)
    {A : Set N} (hA : IsCompact A) {ε : ℝ}
    (hw : A ×ˢ Set.Icc (-ε) ε ⊆ Φ.source)
    (hplane : ∀ x ∈ Φ '' (A ×ˢ Set.Icc (-ε) ε), x 0 ≠ 0)
    {B W : Set (Fin (n + 1) → ℝ)}
    (hB : IsCompact B) (hW : IsOpen W) (hBW : B ⊆ W)
    (hTW : Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ W)
    (hregular : ∀ x ∈ B, x 0 ≠ 0 → fderiv ℝ g x ≠ 0)
    (hboundary : ∀ x ∈ B, x 0 = 0 →
      fderiv ℝ (fun z : Fin n → ℝ => g (Fin.cons 0 z)) (Fin.tail x) ≠ 0) :
    ∃ Y : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
      ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      (∀ x, x 0 = 0 → Y x 0 = 0) ∧
      (∀ x, 0 ≤ fderiv ℝ g x (Y x) ∧ fderiv ℝ g x (Y x) ≤ 1) ∧
      ∃ U P : Set (Fin (n + 1) → ℝ), IsOpen U ∧
        B ∪ Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ U ∧ U ⊆ W ∧
        (∀ x ∈ U, fderiv ℝ g x (Y x) = 1) ∧
        IsOpen P ∧ Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P ∧ P ⊆ U ∩ Φ.target ∧
        Set.EqOn Y
          (fun x => deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2) P := by
  let T := Φ '' (A ×ˢ Set.Icc (-ε) ε)
  have hT : IsCompact T :=
    (hA.prod isCompact_Icc).image_of_continuousOn (hΦ.continuousOn.mono hw)
  have hTt : T ⊆ Φ.target := Set.image_subset_iff.mpr (fun _ hx => Φ.map_source (hw hx))
  let X := fun x => deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2
  have hXrate (x) (hx : x ∈ Φ.target) : fderiv ℝ g x (X x) = 1 :=
    fderiv_collar_velocity_eq_one Φ hΦ g hg c hheight x hx
  have hreg : ∀ x ∈ B ∪ T, x 0 ≠ 0 → fderiv ℝ g x ≠ 0 := by
    intro x hx hz
    rcases hx with hx | hx
    · exact hregular x hx hz
    · intro heq
      have hone := hXrate x (hTt hx)
      rw [heq, zero_apply] at hone
      exact zero_ne_one hone
  have hbdy : ∀ x ∈ B ∪ T, x 0 = 0 →
      fderiv ℝ (fun z : Fin n → ℝ => g (Fin.cons 0 z)) (Fin.tail x) ≠ 0 := by
    intro x hx hz
    rcases hx with hx | hx
    · exact hboundary x hx hz
    · exact (hplane x hx hz).elim
  obtain ⟨Y₀, hY₀, hY₀c, hY₀s, hY₀b, hY₀bound, U, hU, hBTU, hUW, hY₀rate⟩ :=
    exists_contDiff_boundary_tangent_unit_field_near_compact hg (hB.union hT) hW
      (Set.union_subset hBW hTW) hreg hbdy
  obtain ⟨V, hV, hVc, hVt, O, hO, hTO, hOt, hVO⟩ :=
    Φ.exists_contDiff_vector_field_eq_collar_velocity hΦ hi hA hw
  have hTU : T ⊆ U := Set.subset_union_right.trans hBTU
  have hZ : IsOpen {x : Fin (n + 1) → ℝ | x 0 ≠ 0} :=
    (isClosed_eq (continuous_apply 0) continuous_const).isOpen_compl
  obtain ⟨C, hC, hTC, hCsub⟩ := exists_compact_between hT ((hO.inter hU).inter hZ)
    (Set.subset_inter (Set.subset_inter hTO hTU) (fun x hx => hplane x hx))
  have hCOU : C ⊆ O ∩ U := fun _ hx => (hCsub hx).1
  obtain ⟨χ, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, Fin (n + 1) → ℝ)
      hT.isClosed hTC (n := ⊤)
  obtain ⟨Q, hQ, hTQ, hQone⟩ := eventually_nhdsSet_iff_exists.mp hχone
  let Y := fun x => χ x • V x + (1 - χ x) • Y₀ x
  have hχ : ContDiff ℝ ∞ χ := contMDiff_iff_contDiff.mp χ.contMDiff
  have hYC : tsupport Y ⊆ C ∪ tsupport Y₀ := by
    apply closure_minimal _ (hC.isClosed.union (isClosed_tsupport Y₀))
    intro x hx
    by_contra hn
    have hxC : x ∉ C := fun h => hn (Or.inl h)
    have hxY : x ∉ tsupport Y₀ := fun h => hn (Or.inr h)
    exact hx (by simp [Y, hχzero x hxC, image_eq_zero_of_notMem_tsupport hxY])
  have hYrate (x) (hx : x ∈ U) : fderiv ℝ g x (Y x) = 1 := by
    by_cases hzero : χ x = 0
    · simpa only [Y, hzero, zero_smul, sub_zero, one_smul, zero_add] using hY₀rate x hx
    · have hxC : x ∈ C := by
        by_contra hn
        exact hzero (hχzero x hn)
      have hrate : fderiv ℝ g x (V x) = 1 := by
        rw [hVO (hCOU hxC).1]
        exact hXrate x (hOt (hCOU hxC).1)
      simp only [Y, map_add, map_smul, hrate, hY₀rate x hx, smul_eq_mul, mul_one]
      ring
  refine ⟨Y, (hχ.smul hV).add ((contDiff_const.sub hχ).smul hY₀),
    (hC.union hY₀c.isCompact).of_isClosed_subset (isClosed_tsupport Y) hYC,
    hYC.trans (Set.union_subset (fun _ hx => hUW (hCOU hx).2) hY₀s),
    ?_, ?_, U, Q ∩ O ∩ U, hU, hBTU, hUW, hYrate,
    (hQ.inter hO).inter hU, Set.subset_inter (Set.subset_inter hTQ hTO) hTU,
    (fun _ hx => ⟨hx.2, hOt hx.1.2⟩), ?_⟩
  · intro x hx
    have hxC : x ∉ C := fun h => (hCsub h).2 hx
    simp only [Y, hχzero x hxC, zero_smul, sub_zero, one_smul, zero_add]
    exact hY₀b x hx
  · intro x
    by_cases hzero : χ x = 0
    · simpa only [Y, hzero, zero_smul, sub_zero, one_smul, zero_add] using hY₀bound x
    · have hxC : x ∈ C := by
        by_contra hn
        exact hzero (hχzero x hn)
      rw [hYrate x (hCOU hxC).2]
      exact ⟨zero_le_one, le_rfl⟩
  · intro x hx
    simp only [Y, hQone x hx.1.1, one_smul, sub_self, zero_smul, add_zero]
    exact hVO hx.1.2


end DifferentialGeometry.Topology.Morse
