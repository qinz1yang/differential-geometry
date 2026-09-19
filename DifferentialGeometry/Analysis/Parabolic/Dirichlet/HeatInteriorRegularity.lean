import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatNirenbergEnergy
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSecondDerivative
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_local_second_weak_derivative_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀)) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z)) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(timeMeasure T).restrict (Icc a b),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      ∀ᵐ t ∂(timeMeasure T).restrict (Icc a b), Sobolev.Euclidean.MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  obtain ⟨r, η, _, _, hη, hηc, hηrange, hηone, hηs⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood hΩ₀c hΩ hΩ₀Ω
  have hηb : ∀ z, |η z| ≤ 1 := by
    intro z
    have hz := hηrange (mem_range_self z)
    exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hex := exists_integral_cutoff_diffQuot_weakPartial_le_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hη hηc hηs hηb
  let δ := hex.choose
  have hδ := hex.choose_spec.1
  let C := hex.choose_spec.2.choose
  have hroom := hex.choose_spec.2.choose_spec.2.1
  have henergy := hex.choose_spec.2.choose_spec.2.2 u f w hwmass hwderiv
  obtain ⟨ζ, K, hζsmooth, hζc, hζpos, _, hζlip, hζ0, hζT, hζone⟩ :=
    Energy.exists_smooth_timeCutoff_eq_one_on_Icc ha hb
  have hζ : MemLp ζ ∞ volume := hζsmooth.continuous.memLp_of_hasCompactSupport hζc
  let A := C * ((K : ℝ) * (∫ t, ‖u t‖^2 ∂timeMeasure T) +
    (∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T) +
    (∫ t, ζ t * (∫ z in Ω, (f t
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))^2) ∂timeMeasure T))
  have hbound : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2)
        ∂(timeMeasure T).restrict (Icc a b)) ≤ A := by
    intro k h hhpos hh
    let E := fun t => ∑ i, ∫ z, (η z * Sobolev.diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2
    have hEI : Integrable E (timeMeasure T) := by
      apply integrable_finsetSum _
      intro i _
      exact Sobolev.integrable_integral_sq_cutoff_diffQuot_comp hΩ.measurableSet
        (hη.continuous.memLp_of_hasCompactSupport hηc) k h
        ((Metric.cthickening_mono hh _).trans hroom)
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp u)
    have hEpos (t) : 0 ≤ E t := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    have hi := Energy.integral_Icc_le_integral_mul_cutoff hEI hEpos
      (hζ.restrict (Icc (0 : ℝ) T)) hζpos hζone
    exact hi.trans (henergy k h hh ζ K (hζsmooth.of_le (by simp)) hζ
      (Eventually.of_forall hζpos) hζlip hζ0 hζT)
  exact exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict
    q α hΩ hΩc hΩs (Icc a b) u (hη.of_le (by simp)) hηc hΩ₀
      (fun z hz => hηone z (Metric.self_subset_cthickening _ (subset_closure hz))) hδ hroom hbound

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
