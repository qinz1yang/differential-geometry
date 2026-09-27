import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace Geometry.Operator

structure IsLaplacianLEDistributionalOn
    (g : SmoothRiemannianMetric I M) (u b : M → Real) (U : Set M) : Prop where
  isOpen : IsOpen U
  function_locallyIntegrableOn : LocallyIntegrableOn u U
    (riemannianVolumeMeasure (I := I) (M := M) g)
  bound_locallyIntegrableOn : LocallyIntegrableOn b U
    (riemannianVolumeMeasure (I := I) (M := M) g)
  test_le : ∀ φ : C^∞⟮I, M; Real⟯,
    φ ∈ compactlySupportedSmoothFunctions I M →
    tsupport (φ : M → Real) ⊆ U →
    (∀ x : M, 0 ≤ φ x) →
    (∫ x, u x * ΔG (I := I) g φ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      ∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)

namespace IsLaplacianLEDistributionalOn

theorem mono
    {g : SmoothRiemannianMetric I M} {u b : M → Real} {U V : Set M}
    (h : IsLaplacianLEDistributionalOn (I := I) g u b U)
    (hV : IsOpen V) (hVU : V ⊆ U) :
    IsLaplacianLEDistributionalOn (I := I) g u b V where
  isOpen := hV
  function_locallyIntegrableOn := h.function_locallyIntegrableOn.mono_set hVU
  bound_locallyIntegrableOn := h.bound_locallyIntegrableOn.mono_set hVU
  test_le φ hφ hφV hφ_nonneg :=
    h.test_le φ hφ (hφV.trans hVU) hφ_nonneg

end IsLaplacianLEDistributionalOn

omit [I.Boundaryless] in
private theorem integrable_mul_test
    {g : SmoothRiemannianMetric I M} {f : M → Real} {U : Set M}
    (hf : LocallyIntegrableOn f U
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφU : tsupport (φ : M → Real) ⊆ U) :
    Integrable (fun x : M ↦ f x * φ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hφ_cs : HasCompactSupport (φ : M → Real) := hφ
  have hf_on : IntegrableOn f (tsupport (φ : M → Real))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hf.integrableOn_compact_subset hφU hφ_cs
  have hmul_on : IntegrableOn (fun x : M ↦ f x * φ x)
      (tsupport (φ : M → Real))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hf_on.mul_continuousOn φ.contMDiff.continuous.continuousOn hφ_cs
  exact (integrableOn_iff_integrable_of_support_subset
    ((support_mul_subset_right f (φ : M → Real)).trans
      (subset_tsupport (φ : M → Real)))).mp hmul_on

omit [SigmaCompactSpace M] in
private theorem tsupport_laplacian_subset
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; Real⟯) :
    tsupport (ΔG (I := I) g φ) ⊆ tsupport (φ : M → Real) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_not
  have heq : (φ : M → Real) =ᶠ[nhds x] (fun _ : M ↦ (0 : Real)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx_not)
  have hφ_eta :
      (⟨(φ : M → Real), φ.contMDiff⟩ : C^∞⟮I, M; Real⟯) = φ := by
    apply ContMDiffMap.ext
    intro y
    rfl
  have hlap := Δ_g_congr_of_eventuallyEq (I := I) g φ.contMDiff
    (contMDiff_const : ContMDiff I 𝓘(Real, Real) ∞ (fun _ : M ↦ (0 : Real))) heq
  have hzero : ΔG (I := I) g φ x = 0 := by
    rw [← hφ_eta, hlap]
    exact Δ_g_const (I := I) g 0 x
  exact hx hzero

omit [SigmaCompactSpace M] in
private theorem hasCompactSupport_laplacian
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M) :
    HasCompactSupport (ΔG (I := I) g φ) := by
  have hφ_cs : HasCompactSupport (φ : M → Real) := hφ
  refine HasCompactSupport.of_support_subset_isCompact hφ_cs ?_
  exact (subset_tsupport _).trans (tsupport_laplacian_subset (I := I) g φ)

namespace IsLaplacianLEDistributionalOn

theorem add
    {g : SmoothRiemannianMetric I M} {u₁ u₂ b₁ b₂ : M → Real} {U : Set M}
    (h₁ : IsLaplacianLEDistributionalOn (I := I) g u₁ b₁ U)
    (h₂ : IsLaplacianLEDistributionalOn (I := I) g u₂ b₂ U) :
    IsLaplacianLEDistributionalOn (I := I) g (u₁ + u₂) (b₁ + b₂) U where
  isOpen := h₁.isOpen
  function_locallyIntegrableOn :=
    h₁.function_locallyIntegrableOn.add h₂.function_locallyIntegrableOn
  bound_locallyIntegrableOn :=
    h₁.bound_locallyIntegrableOn.add h₂.bound_locallyIntegrableOn
  test_le φ hφ hφU hφ_nonneg := by
    let ψ : C^∞⟮I, M; Real⟯ :=
      ⟨ΔG (I := I) g φ, Δ_g_contMDiff (I := I) g φ⟩
    have hψ_cs : ψ ∈ compactlySupportedSmoothFunctions I M := by
      change HasCompactSupport (ΔG (I := I) g φ)
      exact hasCompactSupport_laplacian (I := I) g φ hφ
    have hψU : tsupport (ψ : M → Real) ⊆ U := by
      change tsupport (ΔG (I := I) g φ) ⊆ U
      exact (tsupport_laplacian_subset (I := I) g φ).trans hφU
    have hu₁Δ_int : Integrable
        (fun x : M ↦ u₁ x * ΔG (I := I) g φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      change Integrable (fun x : M ↦ u₁ x * (ψ : M → Real) x)
        (riemannianVolumeMeasure (I := I) (M := M) g)
      exact integrable_mul_test (I := I) h₁.function_locallyIntegrableOn ψ hψ_cs hψU
    have hu₂Δ_int : Integrable
        (fun x : M ↦ u₂ x * ΔG (I := I) g φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      change Integrable (fun x : M ↦ u₂ x * (ψ : M → Real) x)
        (riemannianVolumeMeasure (I := I) (M := M) g)
      exact integrable_mul_test (I := I) h₂.function_locallyIntegrableOn ψ hψ_cs hψU
    have hb₁φ_int : Integrable (fun x : M ↦ b₁ x * φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      integrable_mul_test (I := I) h₁.bound_locallyIntegrableOn φ hφ hφU
    have hb₂φ_int : Integrable (fun x : M ↦ b₂ x * φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      integrable_mul_test (I := I) h₂.bound_locallyIntegrableOn φ hφ hφU
    calc
      (∫ x, (u₁ + u₂) x * ΔG (I := I) g φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          (∫ x, u₁ x * ΔG (I := I) g φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, u₂ x * ΔG (I := I) g φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        simpa only [Pi.add_apply, add_mul] using integral_add hu₁Δ_int hu₂Δ_int
      _ ≤ (∫ x, b₁ x * φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, b₂ x * φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        add_le_add (h₁.test_le φ hφ hφU hφ_nonneg)
          (h₂.test_le φ hφ hφU hφ_nonneg)
      _ = ∫ x, (b₁ + b₂) x * φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        symm
        simpa only [Pi.add_apply, add_mul] using integral_add hb₁φ_int hb₂φ_int

theorem of_smooth
    (g : SmoothRiemannianMetric I M)
    {u b : M → Real} {U : Set M}
    (hU : IsOpen U)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (hb : LocallyIntegrableOn b U
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (hub : ∀ x ∈ U, ΔG (I := I) g ⟨u, hu⟩ x ≤ b x) :
    IsLaplacianLEDistributionalOn (I := I) g u b U := by
  let _ : IsLocallyFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  refine ⟨hU, hu.continuous.locallyIntegrable.locallyIntegrableOn U, hb, ?_⟩
  intro φ hφ hφU hφ_nonneg
  have hφ_cs : HasCompactSupport (φ : M → Real) := hφ
  have huΔφ_int : Integrable
      (fun x : M ↦ u x * ΔG (I := I) g φ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    exact (hu.continuous.mul
      (Δ_g_contMDiff (I := I) g φ).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_laplacian (I := I) g φ hφ).mul_left
  have hφΔu_int : Integrable
      (fun x : M ↦ φ x * ΔG (I := I) g ⟨u, hu⟩ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    exact (φ.contMDiff.continuous.mul
      (Δ_g_contMDiff (I := I) g ⟨u, hu⟩).continuous).integrable_of_hasCompactSupport
        hφ_cs.mul_right
  have hbφ_int : Integrable (fun x : M ↦ b x * φ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_mul_test (I := I) hb φ hφ hφU
  have hgreen := green_second_identity_of_hasCompactSupport (I := I) g
    (f := u) (h := (φ : M → Real)) hu φ.contMDiff (Or.inr hφ_cs)
  have hφ_eta :
      (⟨(φ : M → Real), φ.contMDiff⟩ : C^∞⟮I, M; Real⟯) = φ := by
    apply ContMDiffMap.ext
    intro y
    rfl
  rw [hφ_eta] at hgreen
  rw [integral_sub huΔφ_int hφΔu_int] at hgreen
  have hgreen_eq :
      (∫ x, u x * ΔG (I := I) g φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, φ x * ΔG (I := I) g ⟨u, hu⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    sub_eq_zero.mp hgreen
  have hpoint : ∀ x : M,
      φ x * ΔG (I := I) g ⟨u, hu⟩ x ≤ b x * φ x := by
    intro x
    by_cases hx : x ∈ U
    · calc
        φ x * ΔG (I := I) g ⟨u, hu⟩ x ≤ φ x * b x :=
          mul_le_mul_of_nonneg_left (hub x hx) (hφ_nonneg x)
        _ = b x * φ x := mul_comm _ _
    · have hφx : φ x = 0 := by
        by_contra hne
        exact hx (hφU (subset_tsupport _ (Function.mem_support.mpr hne)))
      simp only [hφx, zero_mul, mul_zero]
      exact le_rfl
  calc
    (∫ x, u x * ΔG (I := I) g φ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x, φ x * ΔG (I := I) g ⟨u, hu⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hgreen_eq
    _ ≤ ∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_mono_ae hφΔu_int hbφ_int (Filter.Eventually.of_forall hpoint)

theorem laplacian_le
    {g : SmoothRiemannianMetric I M} {u b : M → Real} {U : Set M}
    (h : IsLaplacianLEDistributionalOn (I := I) g u b U)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (hb : ContinuousOn b U) :
    ∀ x ∈ U, ΔG (I := I) g ⟨u, hu⟩ x ≤ b x := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsLocallyFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  let _ : μ.IsOpenPosMeasure := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  intro x hx
  by_contra hle
  let q : M → Real := fun y => ΔG (I := I) g ⟨u, hu⟩ y - b y
  have hqx : 0 < q x := by
    exact sub_pos.mpr (lt_of_not_ge hle)
  have hq_contOn : ContinuousOn q U := by
    exact (Δ_g_contMDiff (I := I) g ⟨u, hu⟩).continuous.continuousOn.sub hb
  have hq_contAt : ContinuousAt q x :=
    (hq_contOn x hx).continuousAt (h.isOpen.mem_nhds hx)
  have hqx_lt : q x / 2 < q x := by linarith
  obtain ⟨V₀, hV₀_nhd, hV₀_pos⟩ :
      ∃ V₀ ∈ 𝓝 x, ∀ y ∈ V₀, q x / 2 < q y := by
    have hev := hq_contAt.eventually (p := fun z : Real => q x / 2 < z) ?_
    · exact ⟨_, hev, fun y hy => hy⟩
    · exact eventually_nhds_iff.mpr
        ⟨Ioi (q x / 2), fun _ hy => hy, isOpen_Ioi, hqx_lt⟩
  rcases mem_nhds_iff.mp hV₀_nhd with ⟨W, hWV₀, hW_open, hxW⟩
  let V : Set M := W ∩ U
  have hV_open : IsOpen V := hW_open.inter h.isOpen
  have hxV : x ∈ V := ⟨hxW, hx⟩
  have hVU : V ⊆ U := Set.inter_subset_right
  have hq_pos : ∀ y ∈ V, 0 < q y := by
    intro y hy
    have hyq := hV₀_pos y (hWV₀ hy.1)
    linarith
  obtain ⟨χ, hχ_smooth, hχ_comp, hχ_one, hχ_supp, hχ_range⟩ :=
    Analysis.exists_mfd_bump (I := I) (K := ({x} : Set M)) (U := V)
      isCompact_singleton hV_open (by simpa only [singleton_subset_iff] using hxV)
  have hχ_nonneg : ∀ y : M, 0 ≤ χ y := by
    intro y
    exact (hχ_range ⟨y, rfl⟩).1
  have hχx : χ x = 1 := by
    simpa only [Pi.one_apply] using hχ_one.self_of_nhdsSet (mem_singleton x)
  let φ : C^∞⟮I, M; Real⟯ := ⟨χ, hχ_smooth⟩
  have hφ_comp : φ ∈ compactlySupportedSmoothFunctions I M := by
    exact hχ_comp
  have hφU : tsupport (φ : M → Real) ⊆ U := by
    change tsupport χ ⊆ U
    exact hχ_supp.trans hVU
  have huΔφ_int : Integrable
      (fun y : M => u y * ΔG (I := I) g φ y) μ := by
    exact (hu.continuous.mul
      (Δ_g_contMDiff (I := I) g φ).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_laplacian (I := I) g φ hφ_comp).mul_left
  have hχΔu_int : Integrable
      (fun y : M => χ y * ΔG (I := I) g ⟨u, hu⟩ y) μ := by
    exact (hχ_smooth.continuous.mul
      (Δ_g_contMDiff (I := I) g ⟨u, hu⟩).continuous).integrable_of_hasCompactSupport
        hχ_comp.mul_right
  have hΔuχ_int : Integrable
      (fun y : M => ΔG (I := I) g ⟨u, hu⟩ y * χ y) μ := by
    exact hχΔu_int.congr (Filter.Eventually.of_forall fun y => by
      exact mul_comm _ _)
  have hbχ_int : Integrable (fun y : M => b y * χ y) μ := by
    change Integrable (fun y : M => b y * (φ : M → Real) y) μ
    exact integrable_mul_test (I := I) h.bound_locallyIntegrableOn φ hφ_comp hφU
  have hgreen :
      ∫ y, (u y * ΔG (I := I) g φ y -
          χ y * ΔG (I := I) g ⟨u, hu⟩ y) ∂μ = 0 := by
    simpa only [μ, φ] using green_second_identity_of_hasCompactSupport (I := I) g
      (f := u) (h := χ) hu hχ_smooth (Or.inr hχ_comp)
  rw [integral_sub huΔφ_int hχΔu_int] at hgreen
  have hgreen_eq :
      (∫ y, u y * ΔG (I := I) g φ y ∂μ) =
        ∫ y, χ y * ΔG (I := I) g ⟨u, hu⟩ y ∂μ :=
    sub_eq_zero.mp hgreen
  have htest :
      (∫ y, u y * ΔG (I := I) g φ y ∂μ) ≤
        ∫ y, b y * (φ : M → Real) y ∂μ := by
    exact h.test_le φ hφ_comp hφU (by
      intro y
      exact hχ_nonneg y)
  have hcomm :
      (∫ y, ΔG (I := I) g ⟨u, hu⟩ y * χ y ∂μ) =
        ∫ y, χ y * ΔG (I := I) g ⟨u, hu⟩ y ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => mul_comm _ _
  have hpair :
      (∫ y, ΔG (I := I) g ⟨u, hu⟩ y * χ y ∂μ) ≤
        ∫ y, b y * χ y ∂μ := by
    calc
      (∫ y, ΔG (I := I) g ⟨u, hu⟩ y * χ y ∂μ) =
          ∫ y, χ y * ΔG (I := I) g ⟨u, hu⟩ y ∂μ := hcomm
      _ = ∫ y, u y * ΔG (I := I) g φ y ∂μ := hgreen_eq.symm
      _ ≤ ∫ y, b y * (φ : M → Real) y ∂μ := htest
      _ = ∫ y, b y * χ y ∂μ := by rfl
  have hqχ_int : Integrable (fun y : M => q y * χ y) μ := by
    refine (hΔuχ_int.sub hbχ_int).congr ?_
    exact Filter.Eventually.of_forall fun y => by simp [q, sub_mul]
  have hqχ_nonneg : ∀ y : M, 0 ≤ q y * χ y := by
    intro y
    by_cases hyV : y ∈ V
    · exact mul_nonneg (le_of_lt (hq_pos y hyV)) (hχ_nonneg y)
    · have hχy : χ y = 0 := by
        by_contra hχy
        exact hyV (hχ_supp (subset_tsupport _ hχy))
      simp only [hχy, mul_zero, le_refl]
  have hqχ_cont : Continuous (fun y : M => q y * χ y) := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hyU : y ∈ U
    · exact ((hq_contOn y hyU).continuousAt (h.isOpen.mem_nhds hyU)).mul
        hχ_smooth.continuous.continuousAt
    · have hyts : y ∉ tsupport χ := by
        intro hyts
        exact hyU (hVU (hχ_supp hyts))
      have hχ_zero : χ =ᶠ[𝓝 y] (fun _ : M => (0 : Real)) :=
        notMem_tsupport_iff_eventuallyEq.mp hyts
      have hprod_zero :
          (fun z : M => q z * χ z) =ᶠ[𝓝 y] (fun _ : M => (0 : Real)) :=
        hχ_zero.mono fun z hz => by simp only [hz, mul_zero]
      exact continuousAt_const.congr_of_eventuallyEq hprod_zero
  have hqχ_ne : q x * χ x ≠ 0 := by
    rw [hχx, mul_one]
    exact ne_of_gt hqx
  have hqχ_pos : 0 < ∫ y, q y * χ y ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero hqχ_cont hqχ_int hqχ_nonneg hqχ_ne
  have hqχ_eq :
      (∫ y, q y * χ y ∂μ) =
        (∫ y, ΔG (I := I) g ⟨u, hu⟩ y * χ y ∂μ) -
          ∫ y, b y * χ y ∂μ := by
    simpa only [q, sub_mul] using integral_sub hΔuχ_int hbχ_int
  have hqχ_nonpos : ∫ y, q y * χ y ∂μ ≤ 0 := by
    rw [hqχ_eq]
    linarith
  exact (not_lt_of_ge hqχ_nonpos) hqχ_pos

end IsLaplacianLEDistributionalOn
end Geometry.Operator
end DifferentialGeometry
