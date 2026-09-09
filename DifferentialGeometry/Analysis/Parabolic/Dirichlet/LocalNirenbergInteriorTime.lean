import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalNirenbergTimeEnergy
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
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

theorem exists_local_dirichlet_nirenberg_integral_Icc_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc a b, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j)
    {c d : ℝ} (hac : a < c) (hdb : d < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ Metric.cthickening δ (tsupport η) ⊆ Ω ∧
      ∀ (v : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)))
        (f : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
        (ℓ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (volume.restrict (Icc a b)))
        (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a)),
      (∀ᵐ s ∂timeMeasure (b - a), ∀ z,
        w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z)) →
      (w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s)) →
      (∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
        (∫ t in Icc a b, ℓ t (z t)) = (∫ t in Icc a b, β t (z t)) -
          ∫ t in Icc a b, (∑ i, ∑ j, ∫ y in Ω,
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
              (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
              dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y)) →
      (∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
        (∫ t in Icc a b, β t (z t)) = ∫ t in Icc a b, (∫ y in Ω,
          f (t,y) * H1ComplDirichletToLp q (z t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y)))) →
      ∀ k h, |h| ≤ δ →
        (∫ t in Icc c d, (∑ i, ∫ z, (η z * Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z)^2)
            ∂volume.restrict (Icc a b)) ≤
          C * ((∫ t in Icc a b, ‖v t‖^2) +
            (∫ t in Icc a b, (∫ z in Ω, (f (t,z))^2))) := by
  obtain ⟨δ, hδ, C, hC, hroom, henergy⟩ :=
    exists_local_dirichlet_nirenberg_time_energy_bound hG hab hreg q α hΩ hΩc hΩs
      φ hφ hη hηc hηs hηb hlam hcoer
  obtain ⟨ζ, K, hζsmooth, hζc, hζpos, hζle, hζlip, hζ0, hζT, hζone⟩ :=
    Energy.exists_smooth_timeCutoff_eq_one_on_Icc
      (show 0 < c - a by linarith) (show d - a < b - a by linarith)
  have hζ : MemLp ζ ∞ volume := hζsmooth.continuous.memLp_of_hasCompactSupport hζc
  refine ⟨δ, hδ, C * ((K : ℝ) + 1), by positivity, hroom, ?_⟩
  intro v f ℓ β w hwmass hwderiv hpair hsource k h hh
  let μ := volume.restrict (Icc a b)
  let E := fun t => ∑ i, ∫ z, (η z * Sobolev.diffQuot k h
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z)^2
  have hEI : Integrable E μ := by
    apply integrable_finsetSum _
    intro i _
    exact Sobolev.integrable_integral_sq_cutoff_diffQuot_comp hΩ.measurableSet
      (hη.continuous.memLp_of_hasCompactSupport hηc) k h
      ((Metric.cthickening_mono hh _).trans hroom)
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp v)
  have hEpos (t) : 0 ≤ E t :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hshift : MeasurePreserving (fun t : ℝ => t - a) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-a)
  have hχ : MemLp (fun t => ζ (t - a)) ∞ μ := (hζ.comp_measurePreserving hshift).restrict _
  have hχone (t : ℝ) (ht : t ∈ Icc c d) : ζ (t - a) = 1 :=
    hζone (t - a) ⟨sub_le_sub_right ht.1 a, sub_le_sub_right ht.2 a⟩
  have hinner := Energy.integral_Icc_le_integral_mul_cutoff hEI hEpos hχ
    (fun t => hζpos (t - a)) hχone
  have he := henergy v f ℓ β w hwmass hwderiv hpair hsource k h hh ζ K
    (hζsmooth.of_le (by simp)) hζ (Eventually.of_forall hζpos) hζlip hζ0 hζT
  have hU := (Lp.memLp v).norm.integrable_sq
  have hP := (Lp.memLp f).integrable_sq.integral_prod_left
  have hUle : (∫ t, ζ (t - a) * ‖v t‖^2 ∂μ) ≤ ∫ t, ‖v t‖^2 ∂μ := by
    apply integral_mono_ae (hU.mul_of_top_right hχ) hU
    exact Eventually.of_forall fun t => mul_le_of_le_one_left (sq_nonneg _) (hζle (t - a))
  have hPle : (∫ t, ζ (t - a) * (∫ z in Ω, (f (t,z))^2) ∂μ) ≤
      ∫ t, (∫ z in Ω, (f (t,z))^2) ∂μ := by
    apply integral_mono_ae (hP.mul_of_top_right hχ) hP
    exact Eventually.of_forall fun t => mul_le_of_le_one_left
      (integral_nonneg fun _ => sq_nonneg _) (hζle (t - a))
  have hPpos : 0 ≤ ∫ t, (∫ z in Ω, (f (t,z))^2) ∂μ :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  apply hinner.trans (he.trans ?_)
  have hu := mul_le_mul_of_nonneg_left hUle hC
  have hp := mul_le_mul_of_nonneg_left hPle hC
  have hkp := mul_nonneg hC (mul_nonneg K.coe_nonneg hPpos)
  change C * ((K : ℝ) * (∫ t, ‖v t‖^2 ∂μ) +
      (∫ t, ζ (t - a) * ‖v t‖^2 ∂μ) +
      (∫ t, ζ (t - a) * (∫ z in Ω, (f (t,z))^2) ∂μ)) ≤
    C * ((K : ℝ) + 1) * ((∫ t, ‖v t‖^2 ∂μ) +
      (∫ t, (∫ z in Ω, (f (t,z))^2) ∂μ))
  nlinarith only [hu, hp, hkp]


end DifferentialGeometry.Analysis.Parabolic.Dirichlet
