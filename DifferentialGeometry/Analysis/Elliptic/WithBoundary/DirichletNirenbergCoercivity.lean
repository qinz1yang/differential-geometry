import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergForm

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

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

theorem dirichletWeakFormCompl_volumeDensity_nirenberg_lower_bound
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u : H1ComplDirichlet q)
    (hηb : ∀ z, |η z| ≤ 1) {lam L : ℝ} (hlam : 0 < lam) :
    let e := toEuclidean (E := EuN)
    let ρ := fun (z : EuStd) => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun (i j : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun (i : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let U := fun (z : EuStd) => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    let P := fun (z : EuStd) => (riemannianVolumeDensitySmoothMap h q * φ) ((extChartAt I_hs α).symm (e.symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let R := fun i j z => (ρ z * A i j z) * fderiv ℝ P z (EuclideanSpace.single j 1)
    (∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, A i j y * ξ i * ξ j) →
    (∀ i j z, z ∈ tsupport η → |Sobolev.translate k s (A i j) z| ≤ L ∧
      |Sobolev.diffQuot k s (A i j) z| ≤ L) →
    (∀ i j z, z ∈ tsupport η → |Sobolev.translate k s (R i j) z| ≤ L ∧
      |Sobolev.diffQuot k s (R i j) z| ≤ L) →
    (∀ i z, z ∈ tsupport η → |Sobolev.translate k s (B i) z| ≤ L ∧
      |Sobolev.diffQuot k s (B i) z| ≤ L) →
    (∀ j z, z ∈ tsupport η → |fderiv ℝ η z (EuclideanSpace.single j 1)| ≤ L) →
    let d : ℝ := Module.finrank ℝ EuN
    let ε := lam / (2 * (3 * d + 1))
    let Cg := d * ((4 * ε)⁻¹ * L^2 + L^4) + d * (L^2 / 2) + L^2 / 2
    let Cw := d^2 * (ε⁻¹ * L^4 + 1) + d^2 * ((4 * ε)⁻¹ * L^2 + 1/2) +
      d * ((4 * ε)⁻¹ * L^2 + 1/2) + |a|
    let C := max 0 (max Cg Cw)
    0 ≤ C ∧ lam / 2 * (∑ i, ∫ z, (η z * Sobolev.diffQuot k s (D i u) z)^2) ≤
      dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap h q * φ)
          (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs u)) +
      C * ((∑ i, ∫ z in tsupport η, (D i u z)^2) + ∫ z in tsupport η, (Sobolev.diffQuot k s U z)^2) := by
  intro e ρ A B U P D R hcoer hAL hRL hBL hηd d ε Cg Cw C
  have htarget : closure Ω ⊆ chartTargetEuclid (I := I_hs) α := hΩs.trans (image_mono interior_subset)
  have hU : MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hAcont (i j) : ContinuousOn (A i j) Ω :=
    (invGramOnEuclid_contDiffOn h α i j).continuousOn.mono (subset_closure.trans htarget)
  have hRcont (i j) : ContinuousOn (R i j) Ω :=
    (weightedInvGramOnEuclid_mul_fderiv_chartInverse_contDiffOn h α hΩ
      (subset_closure.trans htarget) (riemannianVolumeDensitySmoothMap h q * φ) i j).continuousOn
  have hBcont (i) : ContinuousOn (B i) Ω :=
    (chartCoeffOnE_comp_toEuclidean_symm_contDiffOn α (subset_closure.trans htarget) X i).continuousOn
  have hflux := integral_nirenberg_flux_lower_bound_local hΩ.measurableSet hU (fun i => Lp.memLp (D i u))
    hAcont hRcont hBcont hη hηc hηb hlam hcoer k s a hηs hAL hRL hBL hηd
  have heq := dirichletWeakFormCompl_volumeDensity_smoothMul_dirichletNirenbergTest_eq_shifted_integral_chart
    h α hΩ hΩc hΩs X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol φ hφ hη hηc k s hηs u u
  refine ⟨hflux.1, ?_⟩
  exact hflux.2.trans_eq (congrArg (fun t : ℝ => t +
    C * ((∑ i, ∫ z in tsupport η, (D i u z)^2) + ∫ z in tsupport η, (Sobolev.diffQuot k s U z)^2)) heq).symm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
