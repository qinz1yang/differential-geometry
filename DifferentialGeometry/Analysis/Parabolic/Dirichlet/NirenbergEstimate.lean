import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientBounds
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergCoercivity
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergEstimate

noncomputable section

open Manifold MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature

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

theorem exists_uniform_dirichletWeakFormCompl_nirenberg_lower_bound
    {T : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) T}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) T G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ T.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuN)) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' EuN p.2 (X p.1 p.2))
      (T.regular ×ˢ (trivializationAt EuN (TangentSpace I_hs) α).baseSet))
    (a : ℝ → ℝ) (ha : ContinuousOn a J)
    (Bx : ℝ) (hX : ∀ t ∈ J, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ J, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (G.metric t).inner x w w ∧
      (G.metric t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ J, riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ J, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        invGramOnEuclid (I := I_hs) (G.metric t) α i j y * ξ i * ξ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ hroom : Metric.cthickening δ (tsupport η) ⊆ Ω,
      ∀ t (ht : t ∈ J) (k : Fin (Module.finrank ℝ EuN)) (s : ℝ) (hs : |s| ≤ δ)
        (u : H1ComplDirichlet q),
      lam / 2 * (∑ i, ∫ z, (η z * Sobolev.diffQuot k s
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u) z)^2) ≤
      dirichletWeakFormCompl (G.metric t) (X t) (a t) Bx (hX t ht) hCg (hequiv t ht)
        Cv hCv0 hCvtop (hvol t ht) u
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
          (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s
            ((Metric.cthickening_mono hs (tsupport η)).trans hroom) u)) + C * ‖u‖^2 := by
  obtain ⟨δ₁, hδ₁, L₁, hL₁, hroom₁, hcoeff⟩ :=
    exists_uniform_chart_coefficients_translate_diffQuot_bound hG hJc hJ q α φ X hXsmooth
      hΩ (subset_closure.trans hΩs) hηc hηs
  obtain ⟨δ₂, hδ₂, C₀, hC₀, _, herror⟩ :=
    exists_integral_sq_weakPartial_diffQuot_chartInverse_le q α hΩ hΩc hΩs hηc hηs
  obtain ⟨L₂, hL₂⟩ := hηc.exists_bound_of_continuousOn
    (hη.continuous_fderiv (by simp)).continuousOn
  obtain ⟨A₀, hA₀⟩ := hJc.exists_bound_of_continuousOn ha
  let L := max L₁ L₂
  let d : ℝ := Module.finrank ℝ EuN
  let ε := lam / (2 * (3 * d + 1))
  let Cgrad := d * ((4 * ε)⁻¹ * L^2 + L^4) + d * (L^2 / 2) + L^2 / 2
  let Cweak := d^2 * (ε⁻¹ * L^4 + 1) + d^2 * ((4 * ε)⁻¹ * L^2 + 1/2) +
    d * ((4 * ε)⁻¹ * L^2 + 1/2)
  let Cbar := max 0 (max Cgrad (Cweak + A₀))
  have hCbar : 0 ≤ Cbar := le_max_left _ _
  have hroom : cthickening (min δ₁ δ₂) (tsupport η) ⊆ Ω :=
    (cthickening_mono (min_le_left _ _) _).trans hroom₁
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, Cbar * C₀,
    mul_nonneg hCbar hC₀, hroom, ?_⟩
  intro t ht k s hs u
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
  have hb := dirichletWeakFormCompl_volumeDensity_nirenberg_lower_bound
    (G.metric t) α hΩ hΩc hΩs (X t) (a t) Bx (hX t ht) hCg (hequiv t ht)
      Cv hCv0 hCvtop (hvol t ht) φ hφ hη hηc k s
      ((cthickening_mono hs _).trans hroom) u hηb (L := L) hlam (hcoer t ht)
      (fun i j z hz => ⟨((hcoeff t ht k s hs₁ z hz).1 i j).1.1.trans (le_max_left _ _),
        ((hcoeff t ht k s hs₁ z hz).1 i j).1.2.trans (le_max_left _ _)⟩)
      (fun i j z hz => ⟨((hcoeff t ht k s hs₁ z hz).1 i j).2.1.trans (le_max_left _ _),
        ((hcoeff t ht k s hs₁ z hz).1 i j).2.2.trans (le_max_left _ _)⟩)
      (fun i z hz => ⟨((hcoeff t ht k s hs₁ z hz).2 i).1.trans (le_max_left _ _),
        ((hcoeff t ht k s hs₁ z hz).2 i).2.trans (le_max_left _ _)⟩)
      hηd
  have hCa : max 0 (max Cgrad (Cweak + |a t|)) ≤ Cbar :=
    max_le_max le_rfl (max_le_max le_rfl (add_le_add_right
      (by simpa only [Real.norm_eq_abs] using hA₀ t ht) _))
  have herr := herror k s hs₂ u
  have herr0 : 0 ≤ (∑ i, ∫ z in tsupport η,
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z)^2) +
      ∫ z in tsupport η, (Sobolev.diffQuot k s
        (fun z => H1ComplDirichletToLp q u
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) z)^2 :=
    add_nonneg (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
      (integral_nonneg fun _ => sq_nonneg _)
  apply hb.2.trans
  apply add_le_add_right
  calc
    _ ≤ Cbar * ((∑ i, ∫ z in tsupport η,
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z)^2) +
        ∫ z in tsupport η, (Sobolev.diffQuot k s
          (fun z => H1ComplDirichletToLp q u
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) z)^2) :=
      mul_le_mul_of_nonneg_right hCa herr0
    _ ≤ Cbar * (C₀ * ‖u‖^2) := mul_le_mul_of_nonneg_left herr hCbar
    _ = _ := (mul_assoc _ _ _).symm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
