import DifferentialGeometry.Geometry.Comparison.Variation.Coordinates.FixedChartIdentities
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [I.Boundaryless] in
private theorem chartVar_velocity
    (c : M) (y₀ c₀ : E) (η : Real → Real)
    (hη : ContDiff Real 1 η) (hη0 : η 0 = 0)
    (hη'0 : HasDerivAt η 1 0)
    (hmem : ∀ u : Real, y₀ + η u • c₀ ∈ (extChartAt I c).target)
    (hbase : (extChartAt I c).symm y₀ ∈ (chartAt H c).source) :
    ((mfderiv 𝓘(Real, Real) I
        (fun u : Real => (extChartAt I c).symm (y₀ + η u • c₀))
        0 (1 : Real)) : E) =
      (trivializationAt E (TangentSpace I) c).symmL Real
        ((extChartAt I c).symm y₀) c₀ := by
  set ζ : Real → M :=
    fun u : Real => (extChartAt I c).symm (y₀ + η u • c₀) with hζ
  have hsmooth_symm :
      ContMDiffOn 𝓘(Real, E) I 1 (extChartAt I c).symm
        (extChartAt I c).target :=
    contMDiffOn_extChartAt_symm (I := I) (n := (1 : Nat)) c
  have hηM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) 1 η := by
    rw [contMDiff_iff_contDiff]
    exact hη
  have hcurveE : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) 1
      (fun u : Real => y₀ + η u • c₀) :=
    contMDiff_const.add (hηM.smul contMDiff_const)
  have hζsmooth : ContMDiff 𝓘(Real, Real) I 1 ζ :=
    hsmooth_symm.comp_contMDiff hcurveE (fun u => hmem u)
  have hζ0 : ζ 0 ∈ (chartAt H c).source := by
    simp only [hζ, hη0, zero_smul, add_zero]
    exact hbase
  have hbridge :=
    MFDerivAlongCurve.raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
      (I := I) (M := M)
      (hζsmooth.contMDiffAt.mdifferentiableAt (by norm_num)) c hζ0
  rw [hbridge]
  have hζ0eq : ζ 0 = (extChartAt I c).symm y₀ := by
    simp only [hζ, hη0, zero_smul, add_zero]
  rw [hζ0eq]
  congr 1
  have hcomp_eq :
      (fun u : Real => extChartAt I c (ζ u)) =ᶠ[nhds 0]
        (fun u : Real => y₀ + η u • c₀) := by
    filter_upwards with u
    simp only [hζ]
    rw [PartialEquiv.right_inv _ (hmem u)]
  have hfd :
      fderiv Real ((extChartAt I c) ∘ ζ) 0 (1 : Real) =
        fderiv Real (fun u : Real => y₀ + η u • c₀) 0 (1 : Real) := by
    apply Filter.EventuallyEq.fderiv_eq at hcomp_eq
    rw [show ((extChartAt I c) ∘ ζ) =
      (fun u : Real => extChartAt I c (ζ u)) from rfl, hcomp_eq]
  rw [hfd]
  have hsmul : HasDerivAt (fun u : Real => η u • c₀) c₀ 0 := by
    simpa using hη'0.smul_const c₀
  have hderiv : HasDerivAt (fun u : Real => y₀ + η u • c₀) c₀ 0 := by
    change HasDerivAt ((fun _ : Real => y₀) + fun u : Real => η u • c₀) c₀ 0
    simpa only [zero_add] using (hasDerivAt_const (0 : Real) y₀).add hsmul
  rw [fderiv_apply_one_eq_deriv]
  exact hderiv.deriv

omit [I.Boundaryless] in
private theorem chartVar_smooth
    (c : M) (γ : Real → M) (V : Real → E) (η : Real → Real)
    (hγ : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ)
    (hV : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) (8 : Nat) V)
    (hη : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) (8 : Nat) η)
    (U : Set Real) (hUopen : IsOpen U)
    (hUsrc : ∀ t ∈ U, γ t ∈ (chartAt H c).source)
    (hsupp : tsupport V ⊆ U)
    (hmem : ∀ p : Real × Real, p.2 ∈ U →
      extChartAt I c (γ p.2) + η p.1 • V p.2 ∈ (extChartAt I c).target)
    (f : Real → Real → M)
    (hf_in : ∀ u t, t ∈ U → f u t = (extChartAt I c).symm
      (extChartAt I c (γ t) + η u • V t))
    (hf_out : ∀ u t, t ∉ tsupport V → f u t = γ t) :
    IsSmoothVariation (I := I) f := by
  apply contMDiff_of_locally_contMDiffOn
  intro p
  by_cases hp : p.2 ∈ U
  · refine ⟨{q : Real × Real | q.2 ∈ U},
      hUopen.preimage continuous_snd, hp, ?_⟩
    have hsmooth_symm : ContMDiffOn 𝓘(Real, E) I (8 : Nat)
        (extChartAt I c).symm (extChartAt I c).target :=
      contMDiffOn_extChartAt_symm (I := I) (n := (8 : Nat)) c
    have hcurve : ContMDiffOn
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, E) (8 : Nat)
        (fun q : Real × Real =>
          extChartAt I c (γ q.2) + η q.1 • V q.2)
        {q : Real × Real | q.2 ∈ U} := by
      have hext : ContMDiffOn I 𝓘(Real, E) (8 : Nat)
          (extChartAt I c) (chartAt H c).source :=
        contMDiffOn_extChartAt (I := I) (n := (8 : Nat)) (x := c)
      have hcomp : ContMDiffOn
          (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, E) (8 : Nat)
          (fun q : Real × Real => extChartAt I c (γ q.2))
          {q : Real × Real | q.2 ∈ U} := by
        apply hext.comp (hγ.comp contMDiff_snd).contMDiffOn
        intro q hq
        exact hUsrc q.2 hq
      exact hcomp.add
        ((hη.comp contMDiff_fst).contMDiffOn.smul
          (hV.comp contMDiff_snd).contMDiffOn)
    have hcompose : ContMDiffOn
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
        ((extChartAt I c).symm ∘
          (fun q : Real × Real =>
            extChartAt I c (γ q.2) + η q.1 • V q.2))
        {q : Real × Real | q.2 ∈ U} :=
      hsmooth_symm.comp hcurve (fun q hq => hmem q hq)
    apply hcompose.congr
    intro q hq
    exact hf_in q.1 q.2 hq
  · refine ⟨{q : Real × Real | q.2 ∉ tsupport V},
      (isClosed_tsupport V).isOpen_compl.preimage continuous_snd,
      (fun hcontra => hp (hsupp hcontra)), ?_⟩
    have hsmooth : ContMDiffOn
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
        (fun q : Real × Real => γ q.2)
        {q : Real × Real | q.2 ∉ tsupport V} :=
      (hγ.comp contMDiff_snd).contMDiffOn
    apply hsmooth.congr
    intro q hq
    exact hf_out q.1 q.2 hq

theorem exists_chartVar
    (c : M) (γ : Real → M) (V : Real → E)
    (hγ : ContMDiff 𝓘(Real, Real) I (8 : Nat) γ)
    (hV : ContDiff Real (8 : Nat) V) (hVc : HasCompactSupport V)
    (hsrc : ∀ t ∈ tsupport V, γ t ∈ (chartAt H c).source) :
    ∃ f : Real → Real → M,
      IsSmoothVariation (I := I) f ∧
      (∀ t, f 0 t = γ t) ∧
      (∀ t, ((mfderiv 𝓘(Real, Real) I
          (fun u : Real => f u t) 0 (1 : Real)) : E) =
        (trivializationAt E (TangentSpace I) c).symmL Real (γ t) (V t)) ∧
      (∀ u t, V t = 0 → f u t = γ t) := by
  classical
  let K : Set Real := tsupport V
  let U : Set Real := γ ⁻¹' (chartAt H c).source
  have hUopen : IsOpen U :=
    (chartAt H c).open_source.preimage hγ.continuous
  have hKsub : K ⊆ U := hsrc
  have hγKcompact : IsCompact (γ '' K) :=
    hVc.isCompact.image hγ.continuous
  have hγKsrc : γ '' K ⊆ (extChartAt I c).source := by
    rintro x ⟨t, ht, rfl⟩
    rw [extChartAt_source]
    exact hsrc t ht
  have hAcompact : IsCompact (extChartAt I c '' (γ '' K)) :=
    hγKcompact.image_of_continuousOn
      ((continuousOn_extChartAt c).mono hγKsrc)
  have hAtarget : extChartAt I c '' (γ '' K) ⊆ (extChartAt I c).target := by
    rintro y ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    apply (extChartAt I c).map_source
    rw [extChartAt_source]
    exact hsrc t ht
  obtain ⟨r, hr, hrsub⟩ :=
    hAcompact.exists_thickening_subset_open
      (isOpen_extChartAt_target c) hAtarget
  obtain ⟨C, hC⟩ :=
    hVc.isCompact.exists_bound_of_continuousOn hV.continuous.continuousOn
  let B : Real := |C| + 1
  have hB : 0 < B := by simp only [B]; positivity
  have hVB : ∀ t ∈ K, ‖V t‖ < B := by
    intro t ht
    exact (hC t ht).trans_lt (lt_of_le_of_lt (le_abs_self C) (lt_add_one |C|))
  let ρ : Real := r / (2 * B)
  have hρ : 0 < ρ := div_pos hr (mul_pos (by norm_num) hB)
  let η : Real → Real := fun u => ρ * Real.sin (u / ρ)
  have hηsmooth : ContDiff Real (8 : Nat) η :=
    contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ρ))
  have hη0 : η 0 = 0 := by simp [η]
  have hη'0 : HasDerivAt η 1 0 := by
    have hinner : HasDerivAt (fun u : Real => u / ρ) (1 / ρ) 0 := by
      simpa using (hasDerivAt_id (0 : Real)).div_const ρ
    have hsin : HasDerivAt Real.sin (Real.cos (0 / ρ)) (0 / ρ) :=
      Real.hasDerivAt_sin _
    have hmul := (hsin.comp 0 hinner).const_mul ρ
    simp only [Real.cos_zero, zero_div] at hmul
    rw [one_div] at hmul
    have hmul' : HasDerivAt (fun u : Real => ρ * Real.sin (u / ρ))
        (ρ * (1 * ρ⁻¹)) 0 := by
      simpa only [Function.comp_apply] using hmul
    have hcoef : ρ * (1 * ρ⁻¹) = 1 := by
      rw [one_mul, mul_inv_cancel₀ hρ.ne']
    rw [hcoef] at hmul'
    exact hmul'
  have hηbound : ∀ u, |η u| ≤ ρ := by
    intro u
    change |ρ * Real.sin (u / ρ)| ≤ ρ
    rw [abs_mul, abs_of_pos hρ]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hρ.le).trans_eq
      (mul_one ρ)
  have hpert : ∀ u t, t ∈ K → ‖η u • V t‖ < r := by
    intro u t ht
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |η u| * ‖V t‖ ≤ ρ * ‖V t‖ :=
        mul_le_mul_of_nonneg_right (hηbound u) (norm_nonneg _)
      _ < ρ * B := mul_lt_mul_of_pos_left (hVB t ht) hρ
      _ = r / 2 := by simp only [ρ]; field_simp
      _ < r := half_lt_self hr
  have hmem : ∀ u t, t ∈ U →
      extChartAt I c (γ t) + η u • V t ∈ (extChartAt I c).target := by
    intro u t htU
    by_cases ht : t ∈ K
    · apply hrsub
      rw [Metric.mem_thickening_iff]
      refine ⟨extChartAt I c (γ t), ?_, ?_⟩
      · exact ⟨γ t, ⟨t, ht, rfl⟩, rfl⟩
      · rw [dist_eq_norm, add_sub_cancel_left]
        exact hpert u t ht
    · have hV0 : V t = 0 := image_eq_zero_of_notMem_tsupport ht
      rw [hV0, smul_zero, add_zero]
      apply (extChartAt I c).map_source
      rw [extChartAt_source]
      exact htU
  let f : Real → Real → M := fun u t =>
    if t ∈ U then
      (extChartAt I c).symm (extChartAt I c (γ t) + η u • V t)
    else γ t
  have hf_in : ∀ u t, t ∈ U → f u t = (extChartAt I c).symm
      (extChartAt I c (γ t) + η u • V t) := by
    intro u t ht
    simp only [f, if_pos ht]
  have hf_out : ∀ u t, t ∉ K → f u t = γ t := by
    intro u t ht
    have hV0 : V t = 0 := image_eq_zero_of_notMem_tsupport ht
    by_cases htU : t ∈ U
    · simp only [f, if_pos htU, hV0, smul_zero, add_zero]
      apply PartialEquiv.left_inv
      rw [extChartAt_source]
      exact htU
    · simp only [f, if_neg htU]
  have hVM : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) (8 : Nat) V := by
    rw [contMDiff_iff_contDiff]
    exact hV
  have hηM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) (8 : Nat) η := by
    rw [contMDiff_iff_contDiff]
    exact hηsmooth
  have hfsmooth : IsSmoothVariation (I := I) f :=
    chartVar_smooth c γ V η hγ hVM hηM U hUopen
      (fun t ht => ht) hKsub (fun p hp => hmem p.1 p.2 hp)
      f hf_in hf_out
  refine ⟨f, hfsmooth, ?_, ?_, ?_⟩
  · intro t
    by_cases htU : t ∈ U
    · rw [hf_in 0 t htU, hη0, zero_smul, add_zero]
      apply PartialEquiv.left_inv
      rw [extChartAt_source]
      exact htU
    · simp only [f, if_neg htU]
  · intro t
    by_cases htU : t ∈ U
    · rw [show (fun u : Real => f u t) =
          (fun u : Real => (extChartAt I c).symm
            (extChartAt I c (γ t) + η u • V t)) by
          funext u; exact hf_in u t htU]
      have hleft : (extChartAt I c).symm (extChartAt I c (γ t)) = γ t := by
        apply PartialEquiv.left_inv
        rw [extChartAt_source]
        exact htU
      have hvel := chartVar_velocity c (extChartAt I c (γ t)) (V t) η
          (hηsmooth.of_le (by norm_num)) hη0 hη'0
          (fun u => hmem u t htU) (by
            change γ t ∈ (chartAt H c).source at htU
            simpa only [hleft] using htU)
      rw [hleft] at hvel
      exact hvel
    · have hV0 : V t = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro htK
        exact htU (hKsub htK)
      have hfconst : (fun u : Real => f u t) = fun _ : Real => γ t := by
        funext u
        simp only [f, if_neg htU]
      rw [hfconst, hV0, map_zero]
      simp only [mfderiv_const]
      change (0 : Real →L[Real] TangentSpace I (γ t)) (1 : Real) = 0
      exact zero_apply _
  · intro u t hV0
    by_cases htU : t ∈ U
    · rw [hf_in u t htU, hV0, smul_zero, add_zero]
      apply PartialEquiv.left_inv
      rw [extChartAt_source]
      exact htU
    · simp only [f, if_neg htU]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
