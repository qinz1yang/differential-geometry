import DifferentialGeometry.Geometry.Comparison.Busemann
import DifferentialGeometry.Geometry.Comparison.Distance.RadialIntegral

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open Analysis.Sobolev.IntrinsicLp
open Geometry.Curvature
open Geometry.Operator
open Geometry.Riemannian.BonnetMyers
open Geometry.Riemannian.Exponential
open Integral.DivergenceTheorem
open Integral.L2
open Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [NeZero (Module.finrank Real E)] [CompleteSpace E]
    [I.Boundaryless] [T2Space (TangentBundle I M)] in
private theorem dist_real_cont
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (p : M) :
    Continuous (fun y : M ↦ (riemannianEDist I p y).toReal) := by
  have hed : Continuous (fun y : M ↦ riemannianEDist I p y) :=
    (continuous_riemannianEDist_to (I := I) p).congr
      (fun _ ↦ Manifold.riemannianEDist_comm)
  apply continuousOn_univ.mp
  refine ENNReal.continuousOn_toReal.comp' hed.continuousOn ?_
  intro y _
  exact riemannianEDist_ne_top (I := I) p y

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem int_tendsto_compact
    (μ : Measure M) [IsLocallyFiniteMeasure μ]
    {F : Nat → M → Real} {f b : M → Real}
    (hF : ∀ n, Continuous (F n))
    (hb : Continuous b) (hb_cs : HasCompactSupport b)
    (hbound : ∀ n x, ‖F n x‖ ≤ b x)
    (hlim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence b
    (fun n ↦ (hF n).aestronglyMeasurable)
    (hb.integrable_of_hasCompactSupport hb_cs)
    (fun n ↦ Filter.Eventually.of_forall (hbound n))
    (Filter.Eventually.of_forall hlim)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
private theorem buse_lhs_tendsto
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    {p : M} {γ : Real → M} (hray : IsMinimizingRay (I := I) g p γ)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M) :
    Tendsto
      (fun n : Nat ↦ ∫ x,
        busemannApprox (I := I) γ n x * ΔG (I := I) g φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) atTop
      (nhds (∫ x, busemann (I := I) γ x * ΔG (I := I) g φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let ρ₀ : M → Real := fun x ↦ (riemannianEDist I (γ 0) x).toReal
  let A : Nat → M → Real := fun n x ↦
    busemannApprox (I := I) γ n x * ΔG (I := I) g φ x
  let _ : IsLocallyFiniteMeasure μ :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hρ₀_cont : Continuous ρ₀ := by
    simpa only [ρ₀] using dist_real_cont (I := I) (γ 0)
  have hΔ_cont : Continuous (ΔG (I := I) g φ) :=
    (Δ_g_contMDiff (I := I) g φ).continuous
  have hgrad_cs := hasCompactSupport_grad_g (I := I) g φ hφ
  have hΔ_cs : HasCompactSupport (ΔG (I := I) g φ) := by
    change HasCompactSupport
      (divergenceG (I := I) g (gradG (I := I) g φ))
    exact hasCompactSupport_divergence_g (I := I) g hgrad_cs
  have hA_cont (n : Nat) : Continuous (A n) := by
    have hρn := dist_real_cont (I := I) (γ (n : Real))
    exact (hρn.sub continuous_const).mul hΔ_cont
  have hbound_cont : Continuous
      (fun x : M ↦ ρ₀ x * ‖ΔG (I := I) g φ x‖) :=
    hρ₀_cont.mul hΔ_cont.norm
  have hbound_cs : HasCompactSupport
      (fun x : M ↦ ρ₀ x * ‖ΔG (I := I) g φ x‖) := hΔ_cs.norm.mul_left
  have hbound (n : Nat) (x : M) :
      ‖A n x‖ ≤ ρ₀ x * ‖ΔG (I := I) g φ x‖ := by
    have hlower := busemannApprox_lower_bound (I := I) hray x n
    have hupper := (busemannApprox_antitone (I := I) hray x) (Nat.zero_le n)
    have habs : |busemannApprox (I := I) γ n x| ≤ ρ₀ x := by
      rw [abs_le]
      constructor
      · simpa only [ρ₀] using hlower
      · simpa only [busemannApprox, ρ₀, Nat.cast_zero, sub_zero] using hupper
    simp only [A, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
  have hlim (x : M) : Tendsto (fun n ↦ A n x) atTop
      (nhds (busemann (I := I) γ x * ΔG (I := I) g φ x)) := by
    simpa only [A] using (busemann_tendsto (I := I) hray x).mul_const
      (ΔG (I := I) g φ x)
  simpa only [A, μ] using int_tendsto_compact μ hA_cont hbound_cont
    hbound_cs hbound hlim

omit [NeZero (Module.finrank Real E)] [CompleteSpace E]
    [I.Boundaryless] [T2Space (TangentBundle I M)] in
private theorem buse_rhs_tendsto
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    {p : M} {γ : Real → M} (hray : IsMinimizingRay (I := I) g p γ)
    (d : Nat) (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφ0 : ∀ x : M, 0 ≤ φ x) :
    Tendsto
        (fun n : Nat ↦ ∫ x,
          ((d : Nat) : Real) /
              (riemannianEDist I (γ (n : Real)) x).toReal * φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) atTop (nhds 0) ∧
      ∀ᶠ n : Nat in atTop,
        tsupport (φ : M → Real) ⊆ ({γ (n : Real)}ᶜ : Set M) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let ρ : Nat → M → Real := fun n x ↦
    (riemannianEDist I (γ (n : Real)) x).toReal
  let Q : Nat → M → Real := fun n x ↦ ((d : Nat) : Real) / ρ n x * φ x
  let _ : IsLocallyFiniteMeasure μ :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hρ_cont (n : Nat) : Continuous (ρ n) := by
    simpa only [ρ] using dist_real_cont (I := I) (γ (n : Real))
  obtain ⟨R, hR⟩ := bddAbove_def.mp
    ((show HasCompactSupport (φ : M → Real) from hφ).bddAbove_image
      (hρ_cont 0).continuousOn)
  have hR_point {x : M} (hx : x ∈ tsupport (φ : M → Real)) : ρ 0 x ≤ R :=
    hR (ρ 0 x) (mem_image_of_mem (ρ 0) hx)
  obtain ⟨N, hN⟩ := exists_nat_ge (max R 0 + 2)
  have hlower (n : Nat) (x : M) : (n : Real) ≤ ρ 0 x + ρ n x := by
    have h := busemannApprox_lower_bound (I := I) hray x n
    unfold busemannApprox at h
    have h' : -(ρ 0 x) ≤ ρ n x - (n : Real) := by
      simpa only [ρ, Nat.cast_zero] using h
    linarith
  have hρ_one (n : Nat) (hn : N ≤ n) {x : M}
      (hx : x ∈ tsupport (φ : M → Real)) : 1 ≤ ρ n x := by
    have hNn : (N : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hRmax : R ≤ max R 0 := le_max_left _ _
    have h := hlower n x
    have hxR := hR_point hx
    linarith
  have haway : ∀ᶠ n : Nat in atTop,
      tsupport (φ : M → Real) ⊆ ({γ (n : Real)}ᶜ : Set M) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx
    rw [mem_compl_iff, mem_singleton_iff]
    intro hxpole
    have hpos := hρ_one n hn hx
    subst x
    simp only [ρ, Manifold.riemannianEDist_self, ENNReal.toReal_zero] at hpos
    linarith
  have hφ_int : Integrable (φ : M → Real) μ :=
    φ.contMDiff.continuous.integrable_of_hasCompactSupport hφ
  have hQ_nonneg : ∀ᶠ n : Nat in atTop,
      0 ≤ ∫ x, Q n x ∂μ := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change (0 : Real) ≤ Q n x
      by_cases hx : x ∈ tsupport (φ : M → Real)
      · exact mul_nonneg
          (div_nonneg (Nat.cast_nonneg d) (zero_le_one.trans (hρ_one n hn hx)))
          (hφ0 x)
      · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp only [Q, hφx, mul_zero]
        exact le_rfl
  have hden_top : Tendsto (fun n : Nat ↦ (n : Real) - R) atTop atTop := by
    rw [tendsto_atTop]
    intro a
    obtain ⟨K, hK⟩ := exists_nat_ge (a + R)
    filter_upwards [eventually_ge_atTop K] with n hn
    have hKn : (K : Real) ≤ (n : Real) := by exact_mod_cast hn
    linarith
  have hQ_upper : ∀ᶠ n : Nat in atTop,
      (∫ x, Q n x ∂μ) ≤
        (((d : Nat) : Real) / ((n : Real) - R)) * ∫ x, φ x ∂μ := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hden_pos : 0 < (n : Real) - R := by
      have hRmax : R ≤ max R 0 := le_max_left _ _
      linarith
    calc
      (∫ x, Q n x ∂μ) ≤
          ∫ x, (((d : Nat) : Real) / ((n : Real) - R)) * φ x ∂μ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x ↦ by
            change (0 : Real) ≤ Q n x
            by_cases hx : x ∈ tsupport (φ : M → Real)
            · exact mul_nonneg
                (div_nonneg (Nat.cast_nonneg d)
                  (zero_le_one.trans (hρ_one n hn hx)))
                (hφ0 x)
            · simp only [Q, image_eq_zero_of_notMem_tsupport hx, mul_zero]
              exact le_rfl
        · exact hφ_int.const_mul _
        · exact Filter.Eventually.of_forall fun x ↦ by
            change Q n x ≤ (((d : Nat) : Real) / ((n : Real) - R)) * φ x
            by_cases hx : x ∈ tsupport (φ : M → Real)
            · have hden_le : (n : Real) - R ≤ ρ n x := by
                have h := hlower n x
                have hxR := hR_point hx
                linarith
              have hdiv := div_le_div_of_nonneg_left
                (Nat.cast_nonneg d) hden_pos hden_le
              exact mul_le_mul_of_nonneg_right hdiv (hφ0 x)
            · simp only [Q, image_eq_zero_of_notMem_tsupport hx, mul_zero]
              exact le_rfl
      _ = _ := by rw [integral_const_mul]
  have hupper_lim : Tendsto
      (fun n : Nat ↦ (((d : Nat) : Real) / ((n : Real) - R)) * ∫ x, φ x ∂μ)
      atTop (nhds 0) := by
    simpa only [zero_mul] using
      (hden_top.const_div_atTop ((d : Nat) : Real)).mul_const (∫ x, φ x ∂μ)
  have hlim : Tendsto (fun n : Nat ↦ ∫ x, Q n x ∂μ) atTop (nhds 0) :=
    squeeze_zero' hQ_nonneg hQ_upper hupper_lim
  refine ⟨?_, haway⟩
  simpa only [Q, ρ, μ] using hlim

omit [NeZero (Module.finrank Real E)] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
private theorem buse_test_le
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : Real → M}
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g 0)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφ0 : ∀ x : M, 0 ≤ φ x)
    (haway : ∀ᶠ n : Nat in atTop,
      tsupport (φ : M → Real) ⊆ ({γ (n : Real)}ᶜ : Set M)) :
    ∀ᶠ n : Nat in atTop,
      (∫ x, busemannApprox (I := I) γ n x * ΔG (I := I) g φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      ∫ x, (((Module.finrank Real E - 1 : Nat) : Real) /
          (riemannianEDist I (γ (n : Real)) x).toReal) * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsLocallyFiniteMeasure μ :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hΔ_cont : Continuous (ΔG (I := I) g φ) :=
    (Δ_g_contMDiff (I := I) g φ).continuous
  have hgrad_cs := hasCompactSupport_grad_g (I := I) g φ hφ
  have hΔ_cs : HasCompactSupport (ΔG (I := I) g φ) := by
    change HasCompactSupport
      (divergenceG (I := I) g (gradG (I := I) g φ))
    exact hasCompactSupport_divergence_g (I := I) g hgrad_cs
  have hΔ_zero : (∫ x, ΔG (I := I) g φ x ∂μ) = 0 := by
    simpa only [μ, Δ_g_def] using
      integral_divergence_eq_zero_of_hasCompactSupport
        (I := I) g (gradG (I := I) g φ) hgrad_cs
  filter_upwards [haway] with n hn
  have hdist := dist_isLaplacianLEDistributionalOn
    (I := I) g hEnorm (γ (n : Real)) hd hRic
  dsimp only at hdist
  have hle := hdist.test_le φ hφ hn hφ0
  have hρ_cont := dist_real_cont (I := I) (γ (n : Real))
  have hρΔ_int : Integrable
      (fun x : M ↦ (riemannianEDist I (γ (n : Real)) x).toReal *
        ΔG (I := I) g φ x) μ :=
    (hρ_cont.mul hΔ_cont).integrable_of_hasCompactSupport hΔ_cs.mul_left
  have hnΔ_int : Integrable
      (fun x : M ↦ (n : Real) * ΔG (I := I) g φ x) μ :=
    (continuous_const.mul hΔ_cont).integrable_of_hasCompactSupport hΔ_cs.mul_left
  calc
    (∫ x, busemannApprox (I := I) γ n x * ΔG (I := I) g φ x ∂μ) =
        (∫ x, (riemannianEDist I (γ (n : Real)) x).toReal *
          ΔG (I := I) g φ x ∂μ) -
          ∫ x, (n : Real) * ΔG (I := I) g φ x ∂μ := by
            rw [← integral_sub hρΔ_int hnΔ_int]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by
              simp only [busemannApprox]
              ring
    _ = ∫ x, (riemannianEDist I (γ (n : Real)) x).toReal *
          ΔG (I := I) g φ x ∂μ := by
      rw [integral_const_mul, hΔ_zero, mul_zero, sub_zero]
    _ ≤ _ := by simpa only [μ] using hle

omit [NeZero (Module.finrank Real E)] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
theorem busemann_isLaplacianLEDistributionalOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {γ : Real → M} (hray : IsMinimizingRay (I := I) g p γ)
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    IsLaplacianLEDistributionalOn (I := I) g (busemann (I := I) γ)
      (fun _ : M ↦ 0) univ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let d : Nat := Module.finrank Real E - 1
  let _ : IsLocallyFiniteMeasure μ :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hB_lip : ∀ x y, edist (busemann (I := I) γ x)
      (busemann (I := I) γ y) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g x y := by
    intro x y
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) x y)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hray x y)
  have hB_cont : Continuous (busemann (I := I) γ) :=
    intrinsic_lip_cont (I := I) g hB_lip
  refine ⟨isOpen_univ,
    hB_cont.locallyIntegrable.locallyIntegrableOn univ,
    continuous_const.locallyIntegrable.locallyIntegrableOn univ, ?_⟩
  intro φ hφ _hφ_univ hφ0
  have hrhs := buse_rhs_tendsto (I := I) g hray d φ hφ hφ0
  have htest := buse_test_le (I := I) g hEnorm hd hRic φ hφ hφ0 hrhs.2
  have hlhs := buse_lhs_tendsto (I := I) g hray φ hφ
  have hle := le_of_tendsto_of_tendsto hlhs hrhs.1 htest
  simpa only [μ, d, integral_zero, zero_mul] using hle

end DifferentialGeometry.Geometry.Riemannian
