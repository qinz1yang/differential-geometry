import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.CutoffChartComponentMemWkp
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.SobolevComposition
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.HigherOrderBound
open DifferentialGeometry.Geometry.Curvature


noncomputable section


open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open Analysis.Laplacian.SmoothFChartResidualBilinearBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tsupport_chartPushedRaw_subset_chartImage
    (α : M) {u : M → ℝ}
    (hu_support : tsupport u ⊆ (chartAt H α).source) :
    tsupport (chartPushedRaw (I := I) (M := M) α u) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' (tsupport u) := by
  classical
  have h_image_compact :
      IsCompact ((fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        (tsupport u)) :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α
      (isClosed_tsupport u).isCompact hu_support
  refine closure_minimal ?_ h_image_compact.isClosed
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hy_off
  have hy_off' : y ∉ (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport u)) := by
    intro hy_in
    apply hy_off
    obtain ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩ := hy_in
    exact ⟨x, hx_support, by rw [← hzy, ← hxz]⟩
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) (u := u) α hy_target hy_off')
  · exact hy (chartPushedRaw_apply_of_notMem (I := I) (M := M) α u hy_target)

private lemma wkpCompositionConstant_pos
    {d : ℕ} {kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (p : ℝ≥0∞) :
    0 < Φ.wkpCompositionConstant k p := by
  unfold SmoothDiffeoBoundedAtOrder.wkpCompositionConstant
  have h_card_pos : (0 : ℝ) <
      (Finset.range (k + 1)).sum (fun j => (Fintype.card (Fin j → Fin d) : ℝ)) := by
    have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    have h_at_zero : (Fintype.card (Fin 0 → Fin d) : ℝ) = 1 := by
      have h_card : Fintype.card (Fin 0 → Fin d) = 1 := by
        rw [Fintype.card_fun]; simp
      exact_mod_cast h_card
    have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun j => (Fintype.card (Fin j → Fin d) : ℝ))
      (fun j _ => by positivity) h_zero_in
    exact lt_of_lt_of_le (h_at_zero ▸ zero_lt_one) h_le
  have h_fact_pos : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have h_deriv_pos : (0 : ℝ) < Φ.derivBoundMaxOne ^ k :=
    pow_pos Φ.derivBoundMaxOne_pos k
  have h_jacobian_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
  have h_rpow_pos : (0 : ℝ) < (1 / Φ.jacobianLowerBound) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (by positivity) _
  have h_k1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ k
  positivity

private lemma wkpComp_const'_nonneg
    {d : ℕ} {kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (p : ℝ≥0∞) :
    0 ≤ Φ.wkpCompositionConstant k p :=
  (wkpCompositionConstant_pos Φ k p).le

private lemma wkpNorm_comp_smoothDiffeoBoundedAtOrder_le
    {d : ℕ} [NeZero d] {kmax : ℕ} (k : ℕ) (hk : k ≤ kmax)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkp (d := d) k p u Ω')
    (hu_compactSupport : HasCompactSupport u) (hu_support : tsupport u ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) k p (fun x => u (Φ.toFun x)) Ω ≤
      ENNReal.ofReal (Φ.wkpCompositionConstant k p) * iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  exact Φ.wkpNorm_comp_le hp_one hp_top hΩ hΩ' k hk hu hu_compactSupport hu_support

omit [CompleteSpace E] in
private lemma wkpNorm_chartTransitionTransportCLM_le
    (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)),
      MemWkp (d := Module.finrank ℝ E) k 2
        (fun y => (f : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) →
      MemWkp (d := Module.finrank ℝ E) k 2
        (fun y => ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
        (fun y => ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
          (fun y => (f : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set cM : M → ℝ := transportCoeffManifold (I := I) (M := M) r s β α P₀ Q
    with hcM_def
  set cE : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α cM with hcE_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  set Tβ : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hTβ_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hTβ_open : IsOpen Tβ := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hcM_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cM :=
    contMDiff_transportCoeffManifold (I := I) (M := M) r s β α P₀ Q
  have hcM_support_α : tsupport cM ⊆ (chartAt H α).source :=
    tsupport_transportCoeffManifold_subset_sourceα (I := I) (M := M) r s β α P₀ Q
  have hcM_support_β : tsupport cM ⊆ (chartAt H β).source :=
    tsupport_transportCoeffManifold_subset_sourceβ (I := I) (M := M) r s β α P₀ Q
  set Kc : Set M := tsupport cM with hKc_def
  have hKc_compact : IsCompact Kc := (isClosed_tsupport cM).isCompact
  have hKc_in_α : Kc ⊆ (chartAt H α).source := hcM_support_α
  have hKc_in_β : Kc ⊆ (chartAt H β).source := hcM_support_β
  have hcE_smooth : ContDiff ℝ ∞ cE :=
    Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M) hcM_smooth hcM_support_α
  have hcE_smooth' : ContDiff ℝ (⊤ : ℕ∞) cE := hcE_smooth
  have hcE_compact : HasCompactSupport cE :=
    chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) hcM_support_α
  obtain ⟨Ccoeff, hCcoeff_nn, hCcoeff_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) hcE_smooth' hcE_compact k
  have hcE_tsupp_subset :
      tsupport cE ⊆ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' Kc :=
    tsupport_chartPushedRaw_subset_chartImage (I := I) (M := M) α hcM_support_α
  obtain ⟨Ωαβ, Ωβα, hΩαβ_open, hΩβα_open, hΩαβ_subset_target,
    hΩβα_subset_target, _hΩαβ_overlap, _hΩβα_overlap, hKc_image_in_Ωαβ, Φ,
    hΦ_eq, _hΦ_inv_eq⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      α β hKc_compact hKc_in_α hKc_in_β k
  set KEα : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' Kc with hKEα_def
  have hKEα_compact : IsCompact KEα :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKc_compact hKc_in_α
  have hKEα_in_Ωαβ : KEα ⊆ Ωαβ := hKc_image_in_Ωαβ
  have hcE_tsupp_Ωαβ : tsupport cE ⊆ Ωαβ := hcE_tsupp_subset.trans hKEα_in_Ωαβ
  set KEβ : Set EuclN := Φ.toFun '' KEα with hKEβ_def
  have hKEβ_compact : IsCompact KEβ :=
    hKEα_compact.image Φ.continuous_toFun
  have hKEβ_in_Ωβα : KEβ ⊆ Ωβα := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hz
    have hy_Ωαβ : y ∈ Ωαβ := hKEα_in_Ωαβ hy
    rw [← hyz]
    exact Φ.bijOn.mapsTo hy_Ωαβ
  set Uβ : Set EuclN := Ωβα ∩ Tβ with hUβ_def
  have hUβ_open : IsOpen Uβ := hΩβα_open.inter hTβ_open
  have hKEβ_in_Uβ : KEβ ⊆ Uβ :=
    Set.subset_inter hKEβ_in_Ωβα (hKEβ_in_Ωβα.trans hΩβα_subset_target)
  obtain ⟨δ, χ, _hδ_pos, _hδ_subset, hχ_smooth, hχ_compact, _hχ_range,
    hχ_one, hχ_support⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hKEβ_compact hUβ_open hKEβ_in_Uβ
  have hχ_support_Ωβα : tsupport χ ⊆ Ωβα := fun y hy => (hχ_support hy).1
  have hχ_support_Tβ : tsupport χ ⊆ Tβ := fun y hy => (hχ_support hy).2
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ) hχ_compact k
  obtain ⟨Kχ, hKχ_pos, hKχ_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := d) k (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      hTβ_open (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ) hCχ_nn
      (fun j hj y _ => hCχ_bound y j hj)
  obtain ⟨Kc', hKc'_pos, hKc'_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := d) k (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      hΩαβ_open hcE_smooth' hCcoeff_nn
      (fun j hj y _ => hCcoeff_bound y j hj)
  set Kcomp : ℝ := Φ.wkpCompositionConstant k 2 with hKcomp_def
  have hKcomp_nn : 0 ≤ Kcomp := wkpComp_const'_nonneg Φ k 2
  refine ⟨Kc' * (Kcomp * Kχ), by positivity, ?_⟩
  intro f hf
  set T : EuclN → ℝ := fun y => (f : EuclN → ℝ) y with hT_def
  set v : EuclN → ℝ := fun y => χ y * T y with hv_def
  have hv_support_χ : tsupport v ⊆ tsupport χ :=
    tsupport_smul_subset_left χ T
  have hv_support_Ωβα : tsupport v ⊆ Ωβα := hv_support_χ.trans hχ_support_Ωβα
  have hv_compact : HasCompactSupport v := hχ_compact.mul_right
  have hv_memWkp_Tβ : MemWkp (d := d) k 2 v Tβ :=
    MemWkp.smul_smooth_bounded (d := d) k (by norm_num) hTβ_open
      (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
      (fun j hj y _ => hCχ_bound y j hj) hf
  have hv_memWkp_Ωβα : MemWkp (d := d) k 2 v Ωβα :=
    MemWkp.mono_set (d := d) (by norm_num) hΩβα_open
      hΩβα_subset_target hv_memWkp_Tβ
  have hv_comp_memWkp_Ωαβ : MemWkp (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ :=
    MemWkp.comp_smoothDiffeoBoundedAtOrder (d := d) k (le_refl k)
      (by norm_num) (by norm_num) hΩαβ_open hΩβα_open Φ
      hv_memWkp_Ωβα hv_compact hv_support_Ωβα
  set w : EuclN → ℝ := fun y => cE y * v (Φ.toFun y) with hw_def
  have hw_memWkp_Ωαβ : MemWkp (d := d) k 2 w Ωαβ :=
    MemWkp.smul_smooth_bounded (d := d) k (by norm_num) hΩαβ_open
      hcE_smooth' (fun j hj y _ => hCcoeff_bound y j hj) hv_comp_memWkp_Ωαβ
  have hw_support_cE : tsupport w ⊆ tsupport cE := by
    refine closure_mono ?_
    intro y hy
    rw [Function.mem_support] at hy
    have hcE_ne : cE y ≠ 0 := by
      intro h0
      apply hy
      simp only [hw_def, h0, zero_mul]
    exact Function.mem_support.mpr hcE_ne
  have hw_support_Ωαβ : tsupport w ⊆ Ωαβ := hw_support_cE.trans hcE_tsupp_Ωαβ
  have hw_compact : HasCompactSupport w :=
    hcE_compact.of_isClosed_subset (isClosed_tsupport w) hw_support_cE
  have h_coeFn : (fun y => ((chartTransitionTransportCLM
        (I := I) (M := M) r s β α P₀ Q f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα]
      (fun y => cE y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) :=
    chartTransitionTransportCLM_coeFn_aeEq
      (I := I) (M := M) r s β α P₀ Q f
  have h_pointwise : (fun y => cE y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) = w := by
    funext y
    by_cases hcE_zero : cE y = 0
    · simp only [hw_def, hcE_zero, zero_mul]
    · have hy_tsupp_cE : y ∈ tsupport cE :=
        subset_tsupport cE (Function.mem_support.mpr hcE_zero)
      have hy_KEα : y ∈ KEα := hcE_tsupp_subset hy_tsupp_cE
      have hy_Ωαβ : y ∈ Ωαβ := hKEα_in_Ωαβ hy_KEα
      have hT_eq : chartTransitionEuclid (I := I) (M := M) α β y = Φ.toFun y :=
        (hΦ_eq y hy_Ωαβ).symm
      have hΦy_KEβ : Φ.toFun y ∈ KEβ := ⟨y, hy_KEα, rfl⟩
      have hχ_Φy : χ (Φ.toFun y) = 1 :=
        hχ_one (Φ.toFun y) (Metric.self_subset_cthickening KEβ hΦy_KEβ)
      have hv_Φy : v (Φ.toFun y) =
          (f : EuclN → ℝ) (Φ.toFun y) := by
        simp only [hv_def, hT_def, hχ_Φy, one_mul]
      simp only [hw_def, hT_eq, hv_Φy]
  have h_ae : (fun y => ((chartTransitionTransportCLM
        (I := I) (M := M) r s β α P₀ Q f :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα] w := by
    refine h_coeFn.trans ?_
    rw [h_pointwise]
  have hw_memWkp_Tα : MemWkp (d := d) k 2 w Tα :=
    MemWkp.extend_zero (d := d) (by norm_num)
      hΩαβ_open hTα_open hΩαβ_subset_target hw_memWkp_Ωαβ hw_support_Ωαβ hw_compact
  refine ⟨(MemWkp_congr_ae (d := d) (by norm_num) hTα_open h_ae).mpr hw_memWkp_Tα,
    ?_⟩
  rw [wkpNorm_congr_ae (d := d) (by norm_num) hTα_open h_ae]
  have h_w_norm_extend :
      iteratedWeakSobolevNorm (d := d) k 2 w Tα = iteratedWeakSobolevNorm (d := d) k 2 w Ωαβ :=
    wkpNorm_extend_zero (d := d) (by norm_num)
      hΩαβ_open hTα_open hΩαβ_subset_target hw_memWkp_Ωαβ hw_support_Ωαβ hw_compact
  rw [h_w_norm_extend]
  have h_w_le_v_comp :
      iteratedWeakSobolevNorm (d := d) k 2 w Ωαβ ≤
        ENNReal.ofReal Kc' *
          iteratedWeakSobolevNorm (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ := by
    have := hKc'_bound (u := fun y => v (Φ.toFun y)) hv_comp_memWkp_Ωαβ
    have h_eq : (fun y => cE y * (fun y => v (Φ.toFun y)) y) = w := by
      funext y; rfl
    rwa [h_eq] at this
  refine h_w_le_v_comp.trans ?_
  have h_v_comp_le :
      iteratedWeakSobolevNorm (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ ≤
        ENNReal.ofReal Kcomp * iteratedWeakSobolevNorm (d := d) k 2 v Ωβα :=
    wkpNorm_comp_smoothDiffeoBoundedAtOrder_le (d := d) k (le_refl k)
      (by norm_num) (by norm_num) hΩαβ_open hΩβα_open Φ
      hv_memWkp_Ωβα hv_compact hv_support_Ωβα
  have h_v_norm_extend :
      iteratedWeakSobolevNorm (d := d) k 2 v Tβ = iteratedWeakSobolevNorm (d := d) k 2 v Ωβα :=
    wkpNorm_extend_zero (d := d) (by norm_num)
      hΩβα_open hTβ_open hΩβα_subset_target hv_memWkp_Ωβα hv_support_Ωβα hv_compact
  have h_v_le_f :
      iteratedWeakSobolevNorm (d := d) k 2 v Tβ ≤
        ENNReal.ofReal Kχ *
          iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y) Tβ := by
    have := hKχ_bound (u := fun y => (f : EuclN → ℝ) y) hf
    have h_eq : (fun y => χ y * (fun y => (f : EuclN → ℝ) y) y) = v := by
      funext y; rfl
    rwa [h_eq] at this
  calc
    ENNReal.ofReal Kc' *
        iteratedWeakSobolevNorm (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ
      ≤ ENNReal.ofReal Kc' *
          (ENNReal.ofReal Kcomp * iteratedWeakSobolevNorm (d := d) k 2 v Ωβα) := by
        exact mul_le_mul_of_nonneg_left h_v_comp_le (zero_le)
    _ = ENNReal.ofReal Kc' *
          (ENNReal.ofReal Kcomp * iteratedWeakSobolevNorm (d := d) k 2 v Tβ) := by
        rw [h_v_norm_extend]
    _ ≤ ENNReal.ofReal Kc' *
          (ENNReal.ofReal Kcomp *
            (ENNReal.ofReal Kχ *
              iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y) Tβ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (zero_le)
        exact mul_le_mul_of_nonneg_left h_v_le_f (zero_le)
    _ = ENNReal.ofReal (Kc' * (Kcomp * Kχ)) *
          iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y) Tβ := by
        rw [ENNReal.ofReal_mul hKc'_pos.le,
          ENNReal.ofReal_mul hKcomp_nn]
        ring

private lemma memWkp_finsetSum
    {d k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι : Type*} (T : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ T, MemWkp (d := d) k p (F i) Ω) :
    MemWkp (d := d) k p (fun y => ∑ i ∈ T, F i y) Ω := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := d) (k := k) (p := p) hp hΩ
  | insert a s ha ih =>
      have hF_a : MemWkp (d := d) k p (F a) Ω :=
        hF a (Finset.mem_insert_self a s)
      have hF_s : ∀ i ∈ s, MemWkp (d := d) k p (F i) Ω :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have h_sum_s : MemWkp (d := d) k p (fun y => ∑ i ∈ s, F i y) Ω := ih hF_s
      have h_add : MemWkp (d := d) k p
          (fun y => F a y + ∑ i ∈ s, F i y) Ω :=
        MemWkp.add (d := d) hp hΩ hF_a h_sum_s
      have h_eq : (fun y => ∑ i ∈ insert a s, F i y) =
          fun y => F a y + ∑ i ∈ s, F i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [h_eq]
      exact h_add

private lemma wkpNorm_double_sum_le
    {d : ℕ} {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι κ : Type*} (S : Finset ι) [Fintype κ]
    (F : ι → κ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ S, ∀ j : κ, MemWkp (d := d) k p (F i j) Ω) :
    iteratedWeakSobolevNorm (d := d) k p
        (fun y => ∑ i ∈ S, ∑ j : κ, F i j y) Ω ≤
      ∑ i ∈ S, ∑ j : κ, iteratedWeakSobolevNorm (d := d) k p (F i j) Ω := by
  classical
  have h_inner_mem : ∀ i ∈ S,
      MemWkp (d := d) k p (fun y => ∑ j : κ, F i j y) Ω := by
    intro i hi
    exact memWkp_finsetSum (d := d) hp hΩ (Finset.univ : Finset κ)
      (fun j => F i j) (fun j _ => hF i hi j)
  have h_outer := wkpNorm_sum_le (d := d) hp hΩ S
    (fun i y => ∑ j : κ, F i j y) h_inner_mem
  refine h_outer.trans ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  exact wkpNorm_sum_le (d := d) hp hΩ (Finset.univ : Finset κ)
    (fun j => F i j) (fun j _ => hF i hi j)

omit [CompleteSpace E] in
theorem wkpNorm_tensorL2ChartComponentCutoff_le_of_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (k : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) k 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : M → TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun β Q y =>
      ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_per : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      ∃ C : ℝ, 0 ≤ C ∧
        MemWkp (d := d) k 2 (F β Q) Tα ∧
        iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα ≤
          ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro β Q
    obtain ⟨C, hC_nn, hC_bound⟩ :=
      wkpNorm_chartTransitionTransportCLM_le (I := I) (M := M) r s β α P₀ Q k
    obtain ⟨h_mem, h_bound⟩ := hC_bound
      (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) (h_pou β Q)
    exact ⟨C, hC_nn, h_mem, h_bound⟩
  have hF_mem : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := d) k 2 (F β Q) Tα :=
    fun β Q => (h_per β Q).choose_spec.2.1
  set S : Finset M := transportChartCenters (I := I) (M := M) α with hS_def
  set Cfun : M → TensorCompIdx (E := E) r s → ℝ :=
    fun β Q => (h_per β Q).choose with hCfun_def
  have hCfun_nn : ∀ β Q, 0 ≤ Cfun β Q := fun β Q => (h_per β Q).choose_spec.1
  have hCfun_bound : ∀ β Q,
      iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα ≤
        ENNReal.ofReal (Cfun β Q) *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => (h_per β Q).choose_spec.2.2
  set C : ℝ := 1 + ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q
    with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have h_sum_nn : 0 ≤ ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q :=
      Finset.sum_nonneg (fun β _ =>
        Finset.sum_nonneg (fun Q _ => hCfun_nn β Q))
    linarith
  have hCfun_le_C : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s,
      Cfun β Q ≤ C := by
    intro β hβ Q
    rw [hC_def]
    have h_le_double :
        Cfun β Q ≤ ∑ β' ∈ S, ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q' := by
      have h_inner :
          Cfun β Q ≤ ∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q' :=
        Finset.single_le_sum
          (f := fun Q' => Cfun β Q')
          (fun Q' _ => hCfun_nn β Q') (Finset.mem_univ Q)
      have h_outer :
          (∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q') ≤
            ∑ β' ∈ S, ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q' :=
        Finset.single_le_sum
          (f := fun β' => ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q')
          (fun β' _ => Finset.sum_nonneg (fun Q' _ => hCfun_nn β' Q')) hβ
      exact h_inner.trans h_outer
    linarith
  refine ⟨C, hC_nn, ?_⟩
  have h_decomp : (fun y => ((tensorL2ChartComponentCutoff
        (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα]
      (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F β Q y) :=
    tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
      (I := I) (M := M) g r s u α P₀
  rw [wkpNorm_congr_ae (d := d) (by norm_num) hTα_open h_decomp]
  have h_double_le :
      iteratedWeakSobolevNorm (d := d) k 2
          (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F β Q y) Tα ≤
        ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα :=
    wkpNorm_double_sum_le (d := d) (by norm_num) hTα_open S F
      (fun β _ Q => hF_mem β Q)
  refine h_double_le.trans ?_
  have h_each_le : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα ≤
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
    intro β hβ Q
    refine (hCfun_bound β Q).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (zero_le)
    exact ENNReal.ofReal_le_ofReal (hCfun_le_C β hβ Q)
  refine (Finset.sum_le_sum (fun β hβ =>
    Finset.sum_le_sum (fun Q _ => h_each_le β hβ Q))).trans ?_
  refine le_of_eq ?_
  have h_inner_factor : ∀ β ∈ S,
      (∑ Q : TensorCompIdx (E := E) r s,
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) =
        ENNReal.ofReal C *
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro β _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl h_inner_factor, ← Finset.mul_sum]

omit [CompleteSpace E] in
theorem wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : TensorL2 r s g,
        (∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
            (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
                g r s u α P₀ :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            (∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                      g r s u β Q :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β)) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  set S : Finset M := transportChartCenters (I := I) (M := M) α with hS_def
  set F : TensorL2 r s g → M → TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun u β Q y =>
      ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  set Cfun : M → TensorCompIdx (E := E) r s → ℝ :=
    fun β Q =>
      (wkpNorm_chartTransitionTransportCLM_le (I := I) (M := M)
        r s β α P₀ Q k).choose
    with hCfun_def
  have hCfun_spec : ∀ β Q,
      0 ≤ Cfun β Q ∧
        ∀ f : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β),
          MemWkp (d := d) k 2 (fun y => (f : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) →
          MemWkp (d := d) k 2
              (fun y => ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Tα ∧
            iteratedWeakSobolevNorm (d := d) k 2
                (fun y => ((chartTransitionTransportCLM (I := I) (M := M) r s β α P₀ Q f :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
                Tα ≤
              ENNReal.ofReal (Cfun β Q) *
                iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β) := fun β Q =>
    (wkpNorm_chartTransitionTransportCLM_le (I := I) (M := M)
      r s β α P₀ Q k).choose_spec
  have hCfun_nn : ∀ β Q, 0 ≤ Cfun β Q := fun β Q => (hCfun_spec β Q).1
  set C : ℝ := 1 + ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q
    with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have h_sum_nn : 0 ≤ ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q :=
      Finset.sum_nonneg (fun β _ =>
        Finset.sum_nonneg (fun Q _ => hCfun_nn β Q))
    linarith
  have hCfun_le_C : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s, Cfun β Q ≤ C := by
    intro β hβ Q
    rw [hC_def]
    have h_inner : Cfun β Q ≤ ∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q' :=
      Finset.single_le_sum (f := fun Q' => Cfun β Q')
        (fun Q' _ => hCfun_nn β Q') (Finset.mem_univ Q)
    have h_outer :
        (∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q') ≤
          ∑ β' ∈ S, ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q' :=
      Finset.single_le_sum
        (f := fun β' => ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q')
        (fun β' _ => Finset.sum_nonneg (fun Q' _ => hCfun_nn β' Q')) hβ
    linarith [h_inner.trans h_outer]
  refine ⟨C, hC_nn, fun u h_pou => ?_⟩
  have hF_spec : ∀ β Q,
      MemWkp (d := d) k 2 (F u β Q) Tα ∧
        iteratedWeakSobolevNorm (d := d) k 2 (F u β Q) Tα ≤
          ENNReal.ofReal (Cfun β Q) *
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                  g r s u β Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := fun β Q =>
    (hCfun_spec β Q).2 (tensorL2ChartComponent (I := I) (M := M) g r s u β Q)
      (h_pou β Q)
  have hF_mem : ∀ β Q, MemWkp (d := d) k 2 (F u β Q) Tα :=
    fun β Q => (hF_spec β Q).1
  have h_decomp : (fun y => ((tensorL2ChartComponentCutoff
        (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα]
      (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F u β Q y) :=
    tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
      (I := I) (M := M) g r s u α P₀
  rw [wkpNorm_congr_ae (d := d) (by norm_num) hTα_open h_decomp]
  have h_double_le :
      iteratedWeakSobolevNorm (d := d) k 2
          (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F u β Q y) Tα ≤
        ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := d) k 2 (F u β Q) Tα :=
    wkpNorm_double_sum_le (d := d) (by norm_num) hTα_open S (F u)
      (fun β _ Q => hF_mem β Q)
  refine h_double_le.trans ?_
  have h_each_le : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := d) k 2 (F u β Q) Tα ≤
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
    intro β hβ Q
    refine (hF_spec β Q).2.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCfun_le_C β hβ Q)) (zero_le)
  refine (Finset.sum_le_sum (fun β hβ =>
    Finset.sum_le_sum (fun Q _ => h_each_le β hβ Q))).trans ?_
  refine le_of_eq ?_
  have h_inner_factor : ∀ β ∈ S,
      (∑ Q : TensorCompIdx (E := E) r s,
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) =
        ENNReal.ofReal C *
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro β _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl h_inner_factor, ← Finset.mul_sum]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
