import DifferentialGeometry.Topology.Morse.RelativePerturbationZeroLocus
import DifferentialGeometry.Topology.Morse.RegularZeroTangent

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace Poincare.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem surjective_kernel_projection_iff
    {P B T : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup T] [NormedSpace ℝ T] (D : (P × E) →L[ℝ] B) (L : T →L[ℝ] (P × E))
    (hL : L.toLinearMap.range = D.ker) (hP : Surjective (D.comp (ContinuousLinearMap.inl ℝ P E))) :
    Surjective ((ContinuousLinearMap.fst ℝ P E).comp L) ↔
      Surjective (D.comp (ContinuousLinearMap.inr ℝ P E)) := by
  have hsplit (p : P) (e : E) : D (p,e) = D (p,0) + D (0,e) := by
    rw [← map_add]
    simp
  constructor
  · intro hπ b
    obtain ⟨p,hp⟩ := hP b
    obtain ⟨t,ht⟩ := hπ p
    have hz : D (L t) = 0 := by
      apply (LinearMap.mem_ker).mp
      rw [← hL]
      exact ⟨t,rfl⟩
    refine ⟨-(L t).2,?_⟩
    change D (0,-(L t).2) = b
    have hh : D (p,(L t).2) = 0 := by simpa only [show p = (L t).1 from ht.symm] using hz
    rw [hsplit] at hh
    change D (p,0) = b at hp
    have hn : D (0,-(L t).2) = -(D (0,(L t).2)) := by rw [← map_neg]; simp only [Prod.neg_mk, neg_zero]
    rw [hn]
    exact neg_eq_iff_add_eq_zero.mpr (by simpa only [hp, add_comm] using hh)
  · intro he p
    obtain ⟨e,he⟩ := he (-D (p,0))
    have hmem : (p,e) ∈ L.toLinearMap.range := by
      rw [hL]
      change D (p,e) = 0
      change D (0,e) = -D (p,0) at he
      rw [hsplit,he,add_neg_cancel]
    obtain ⟨t,ht⟩ := hmem
    exact ⟨t,congrArg Prod.fst ht⟩


theorem range_mfderiv_perturbationZero_inclusion {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (q : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0}) :
    let _ := perturbationZeroChartedSpace hf hφ
    LinearMap.range (show (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) × E) from
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) × E)
        (Subtype.val : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
          perturbationDifferential f φ q = 0} → (Fin n → ℝ) × E) q).toLinearMap =
      (fderiv ℝ (perturbationDifferential f φ) q.val).ker := by
  let hr := fun q (hq : q ∈ regularPerturbationDomain φ) (_ : perturbationDifferential f φ q = 0) =>
    surjective_fderiv_perturbationDifferential hf hφ q hq.2
  let C := regularZeroChartedSpace (isOpen_regularPerturbationDomain hφ)
    ((contDiff_perturbationDifferential hf hφ).of_le (by simp)).contDiffOn hr
  have hh : ∀ (d : ℕ) (hd : Module.finrank ℝ ((Fin n → ℝ) × E) -
      Module.finrank ℝ (E →L[ℝ] ℝ) = d),
      let _ : ChartedSpace (Fin d → ℝ)
        {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := hd ▸ C
      LinearMap.range (show (Fin d → ℝ) →L[ℝ] ((Fin n → ℝ) × E) from
        mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, (Fin n → ℝ) × E)
          (Subtype.val : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
            perturbationDifferential f φ q = 0} → (Fin n → ℝ) × E) q).toLinearMap =
        (fderiv ℝ (perturbationDifferential f φ) q.val).ker := by
    intro d hd
    cases hd
    exact range_mfderiv_regularZero_inclusion _ _ _ q
  exact hh n (perturbationZero_finrank (E := E) (n := n))

omit [FiniteDimensional ℝ E] in
theorem fderiv_fderiv_finitePerturbation {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q : (Fin n → ℝ) × E) :
    fderiv ℝ (fderiv ℝ (finitePerturbation f φ q.1)) q.2 =
      (fderiv ℝ (perturbationDifferential f φ) q).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) E) := by
  exact (((contDiff_perturbationDifferential hf hφ).differentiable (by simp) q).hasFDerivAt.comp
    q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv

omit [FiniteDimensional ℝ E] in
theorem fderiv_perturbationDifferential_comp_inl {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q : (Fin n → ℝ) × E) :
    (fderiv ℝ (perturbationDifferential f φ) q).comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) E) =
      parameterDifferential (I := 𝓘(ℝ, E)) φ q.2 := by
  have hd := ((contDiff_perturbationDifferential hf hφ).differentiable (by simp) q).hasFDerivAt
  have hh := hd.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
  exact hh.unique
    (hasFDerivAt_perturbationDifferential_parameter (hf.differentiable (by simp) q.2)
      (fun i => (hφ i).differentiable (by simp) q.2) q.1)


theorem regular_perturbationZero_projection_iff {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (q : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0}) :
    let _ := perturbationZeroChartedSpace hf hφ
    Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (fun y : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
        perturbationDifferential f φ q = 0} => y.val.1) q) ↔
      Bijective (fderiv ℝ (fderiv ℝ (finitePerturbation f φ q.val.1)) q.val.2) := by
  let _ := perturbationZeroChartedSpace hf hφ
  let P := Fin n → ℝ
  let Z := {q : P × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0}
  let L : P →L[ℝ] (P × E) := mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P × E) (Subtype.val : Z → P × E) q
  let D := fderiv ℝ (perturbationDifferential f φ) q.val
  let H := fderiv ℝ (fderiv ℝ (finitePerturbation f φ q.val.1)) q.val.2
  let DP : P →L[ℝ] P := mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) (fun y : Z => y.val.1) q
  have hL : L.toLinearMap.range = D.ker := range_mfderiv_perturbationZero_inclusion hf hφ q
  have hDP : DP = (ContinuousLinearMap.fst ℝ P E).comp L :=
    ((ContinuousLinearMap.fst ℝ P E).hasMFDerivAt.comp q
      ((contMDiff_perturbationZero_inclusion hf hφ).mdifferentiableAt one_ne_zero).hasMFDerivAt).mfderiv
  have hH : H = D.comp (ContinuousLinearMap.inr ℝ P E) := fderiv_fderiv_finitePerturbation hf hφ q.val
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
    exact (Subspace.dual_finrank_eq).symm
  have hbij : Bijective H ↔ Surjective H :=
    ⟨fun h => h.2, fun h => ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr h,h⟩⟩
  change Surjective DP ↔ Bijective H
  rw [hDP,hbij,hH]
  apply surjective_kernel_projection_iff D L hL
  change Surjective ((fderiv ℝ (perturbationDifferential f φ) q.val).comp
    (ContinuousLinearMap.inl ℝ (Fin n → ℝ) E))
  rw [fderiv_perturbationDifferential_comp_inl hf hφ q.val]
  exact q.property.1.2


theorem ae_nondegenerate_finitePerturbation {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
    (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.Measure.IsAddHaarMeasure μ] :
    ∀ᵐ p ∂μ, ∀ x : E, Surjective (parameterDifferential (I := 𝓘(ℝ, E)) φ x) →
      fderiv ℝ (finitePerturbation f φ p) x = 0 →
      Bijective (fderiv ℝ (fderiv ℝ (finitePerturbation f φ p)) x) := by
  let _ := perturbationZeroChartedSpace hf hφ
  have hh := ae_regular_perturbationZero_projection hf hφ μ
  filter_upwards [hh] with p hp x hx hcrit
  let q : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} :=
    ⟨(p,x),⟨mem_univ _,hx⟩,hcrit⟩
  exact (regular_perturbationZero_projection_iff hf hφ q).mp (hp q rfl)


theorem exists_relative_nondegenerate_finitePerturbation {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      (∃ N : Set E, IsOpen N ∧ Uᶜ ⊆ N ∧ ∀ p, EqOn (finitePerturbation f φ p) f N) ∧
      ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)), ∀ x ∈ K,
        fderiv ℝ (finitePerturbation f φ p) x = 0 →
        Bijective (fderiv ℝ (fderiv ℝ (finitePerturbation f φ p)) x) := by
  obtain ⟨n,φ,hφ,_,hreg⟩ := exists_supported_regularPerturbationDomain hK hU hKU
  have hfix := exists_open_finitePerturbation_eq (f := f) (φ := φ) (fun i => (hφ i).2.2)
  refine ⟨n,φ,hφ,hfix,?_⟩
  filter_upwards [ae_nondegenerate_finitePerturbation (φ := φ) hf (fun i => (hφ i).1)
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))]
    with p hp x hx hc
  have hxreg : (p,x) ∈ regularPerturbationDomain φ :=
    hreg (show (p,x) ∈ (univ ×ˢ K : Set ((Fin n → ℝ) × E)) from ⟨mem_univ p,hx⟩)
  exact hp x hxreg.2 hc


theorem exists_arbitrarily_small_relative_nondegenerate_finitePerturbation
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (φ : Fin n → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      (∃ N : Set E, IsOpen N ∧ Uᶜ ⊆ N ∧ ∀ p, EqOn (finitePerturbation f φ p) f N) ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : Fin n → ℝ, ‖p‖ < ε ∧ ∀ x ∈ K,
        fderiv ℝ (finitePerturbation f φ p) x = 0 →
        Bijective (fderiv ℝ (fderiv ℝ (finitePerturbation f φ p)) x) := by
  obtain ⟨n,φ,hφ,hfix,hae⟩ := exists_relative_nondegenerate_finitePerturbation hf hK hU hKU
  refine ⟨n,φ,hφ,hfix,fun ε hε => ?_⟩
  obtain ⟨p,hp,hreg⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) 0 hε).ne'
    (MeasureTheory.ae_restrict_of_ae hae)
  exact ⟨p,by simpa only [Metric.mem_ball, dist_zero_right] using hp,hreg⟩

end Poincare.Morse
