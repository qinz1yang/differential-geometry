import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FixedDensityCoefficientBounds
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalNirenbergCoercivity
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergEstimate

noncomputable section

open Manifold MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_local_dirichlet_nirenberg_lower_bound
    {T : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) T}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) T G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ T.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ J, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ hroom : Metric.cthickening δ (tsupport η) ⊆ Ω,
      ∀ t ∈ J, ∀ (k : Fin (Module.finrank ℝ EuN)) (s : ℝ) (hs : |s| ≤ δ)
        (u : H1ComplDirichlet q),
      let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
      lam / 2 * (∑ i, ∫ z, (η z * Sobolev.diffQuot k s (D i u) z)^2) ≤
        -(∑ i, ∑ j, ∫ z in Ω, D i u z *
          (densityOnEuclid q α z * invGramOnEuclid (G.metric t) α i j z) *
            D j (smoothMulH1ComplDirichlet q φ
              (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s
                ((Metric.cthickening_mono hs _).trans hroom) u)) z) + C * ‖u‖^2 := by
  let hcoeffs := exists_uniform_fixed_density_nirenberg_coefficients_bound hG hJc hJ q α φ
    hΩ (subset_closure.trans hΩs) hηc hηs
  let δ₁ := hcoeffs.choose
  have hδ₁ := hcoeffs.choose_spec.1
  let L₁ := hcoeffs.choose_spec.2.choose
  have hL₁ := hcoeffs.choose_spec.2.choose_spec.1
  have hroom₁ := hcoeffs.choose_spec.2.choose_spec.2.1
  have hcoeff := hcoeffs.choose_spec.2.choose_spec.2.2
  let herrors := exists_integral_sq_weakPartial_diffQuot_chartInverse_le q α hΩ hΩc hΩs hηc hηs
  let δ₂ := herrors.choose
  have hδ₂ := herrors.choose_spec.1
  let C₀ := herrors.choose_spec.2.choose
  have hC₀ := herrors.choose_spec.2.choose_spec.1
  have herror := herrors.choose_spec.2.choose_spec.2.2
  obtain ⟨L₂, hL₂⟩ := hηc.exists_bound_of_continuousOn
    (hη.continuous_fderiv (by simp)).continuousOn
  let L := max L₁ L₂
  let d : ℝ := Module.finrank ℝ EuN
  let ε := lam / (2 * (3 * d + 1))
  let Cgrad := d * ((4 * ε)⁻¹ * L^2 + L^4) + d * (L^2 / 2) + L^2 / 2
  let Cweak := d^2 * (ε⁻¹ * L^4 + 1) + d^2 * ((4 * ε)⁻¹ * L^2 + 1/2) +
    d * ((4 * ε)⁻¹ * L^2 + 1/2)
  let Cbar := max 0 (max Cgrad Cweak)
  have hCbar : 0 ≤ Cbar := le_max_left _ _
  have hroom : cthickening (min δ₁ δ₂) (tsupport η) ⊆ Ω :=
    (cthickening_mono (min_le_left _ _) _).trans hroom₁
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, Cbar * C₀,
    mul_nonneg hCbar hC₀, hroom, ?_⟩
  intro t ht k s hs u D
  have hs₁ : |s| ≤ δ₁ := hs.trans (min_le_left _ _)
  have hs₂ : |s| ≤ δ₂ := hs.trans (min_le_right _ _)
  have hηd (j) (z) (hz : z ∈ tsupport η) :
      |fderiv ℝ η z (EuclideanSpace.single j 1)| ≤ L := by
    calc
      _ = ‖fderiv ℝ η z (EuclideanSpace.single j 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ η z‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        (fderiv ℝ η z).le_opNorm _
      _ = ‖fderiv ℝ η z‖ := by rw [PiLp.norm_single, norm_one, mul_one]
      _ ≤ L₂ := hL₂ z hz
      _ ≤ L := le_max_right _ _
  have hb := local_dirichlet_nirenberg_lower_bound q α hΩ hΩc hΩs φ hφ
    (fun i j => invGramOnEuclid (G.metric t) α i j)
    (fun i j => (invGramOnEuclid_contDiffOn (G.metric t) α i j).continuousOn.mono
      (hΩs.trans (image_mono interior_subset))) hη hηc k s
    ((cthickening_mono hs _).trans hroom) u hηb hlam
    (hL₁.trans (le_max_left L₁ L₂)) (hcoer t ht)
    (fun i j z hz => ⟨((hcoeff t ht k s hs₁ z hz i j).1.1).trans (le_max_left _ _),
      ((hcoeff t ht k s hs₁ z hz i j).1.2).trans (le_max_left _ _)⟩)
    (fun i j z hz => ⟨((hcoeff t ht k s hs₁ z hz i j).2.1).trans (le_max_left _ _),
      ((hcoeff t ht k s hs₁ z hz i j).2.2).trans (le_max_left _ _)⟩) hηd
  apply hb.2.trans
  apply add_le_add_right
  exact (mul_le_mul_of_nonneg_left (herror k s hs₂ u) hCbar).trans_eq
    (mul_assoc _ _ _).symm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
