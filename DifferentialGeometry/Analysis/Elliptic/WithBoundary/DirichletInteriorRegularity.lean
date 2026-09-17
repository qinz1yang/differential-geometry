import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Local
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletCoordinateEnergy
import DifferentialGeometry.Analysis.Elliptic.Coefficients
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.HigherOrder

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Euclidean
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

theorem memWkp_chartInverse_dirichletLaplacianDomain_of_source
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω V : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hV : IsOpen V) (hVΩ : closure V ⊆ Ω)
    (u : dirichletLaplacianDomain q) (m : ℕ)
    (hf : MemWkp m 2 (fun z => densityOnEuclid q α z * dirichletLaplacian q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω) :
    MemWkp (m + 2) 2 (fun z => H1ComplDirichletToLp q (u : H1ComplDirichlet q)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) V := by
  have hVc : IsCompact (closure V) :=
    hΩc.of_isClosed_subset isClosed_closure (hVΩ.trans subset_closure)
  let : NeZero (Module.finrank ℝ EuN) := ⟨by simpa using (NeZero.ne n)⟩
  obtain ⟨B, hB, _⟩ := exists_smooth_metric_extension_of_subset_interior q α hΩc hΩs
  have htarget : closure Ω ⊆ chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (image_mono interior_subset)
  have hpos (z : EuStd) (hz : z ∈ closure Ω) : (B.a z).PosDef := by
    have heq : B.a z = Matrix.of (fun i j => weightedInvGramOnEuclid q α i j z) := by
      ext i j
      exact hB z hz i j
    rw [heq]
    exact weightedInvGramOnEuclid_posDef q α (htarget hz)
  obtain ⟨A, hA⟩ := ellipticCoeff_of_continuous_posDef_on_compact
    hΩ.measurableSet subset_closure hΩc B.a
    (fun i j => (B.smooth_a i j).continuous.measurable)
    (fun i j => (B.smooth_a i j).continuous.continuousOn) hpos
  let U : EuStd → ℝ := fun z => H1ComplDirichletToLp q (u : H1ComplDirichlet q)
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let f : EuStd → ℝ := fun z => -(densityOnEuclid q α z * dirichletLaplacian q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))
  let hu : DeGiorgi.MemW1pWitness 2 U Ω :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs
      (u : H1ComplDirichlet q)).memW1p.someWitness
  let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
  have hgrad (i : Fin (Module.finrank ℝ EuN)) :
      (fun z => D i (u : H1ComplDirichlet q) z) =ᵐ[volume.restrict Ω]
        fun z => hu.weakGrad z i :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
        (u : H1ComplDirichlet q)) (hu.isWeakGrad i)
      ((Lp.memLp _).locallyIntegrable (by norm_num))
      ((hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  have hdiv : DeGiorgi.HasWeakDiv (fun z => -f z)
      (fun z => DeGiorgi.matMulE (A.a z) (hu.weakGrad z)) Ω := by
    apply (hasWeakDiv_dirichlet_chart_gradient q α hΩ hΩc hΩs u).congr_ae
    · filter_upwards with z
      exact (neg_neg _).symm
    · filter_upwards [ae_all_iff.mpr hgrad, ae_restrict_mem hΩ.measurableSet] with z hz hzm
      apply PiLp.ext
      intro j
      simp only [DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hz i, hA, hB z (subset_closure hzm) j i]
      unfold weightedInvGramOnEuclid
      rw [invGramOnEuclid_symm_of_mem q α j i (htarget (subset_closure hzm))]
      exact mul_comm _ _
  have hfm : MemWkp m 2 f Ω := by
    simpa only [f, neg_one_mul, smul_eq_mul] using
      hf.const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ (-1 : ℝ)
  have hweak := (DeGiorgi.bilinFormOfCoeff_eq_integral_iff_hasWeakDiv
    hΩ hu hfm.memLp).mpr hdiv
  exact DeGiorgi.memWkp_add_two_of_bilinFormOfCoeff_eq_integral m
    hΩ hV hVc hVΩ hu hfm hweak B one_ne_zero
    (fun z hz i j => by rw [hA]; simp only [one_mul])

theorem memWkp_chartInverse_dirichletLaplacianDomain
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω V : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hV : IsOpen V) (hVΩ : closure V ⊆ Ω)
    (u : dirichletLaplacianDomain q) (m : ℕ)
    (hf : MemWkp m 2 (fun z => dirichletLaplacian q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω) :
    MemWkp (m + 2) 2 (fun z => H1ComplDirichletToLp q (u : H1ComplDirichlet q)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) V := by
  apply memWkp_chartInverse_dirichletLaplacianDomain_of_source q α hΩ hΩc hΩs hV hVΩ u m
  apply MemWkp.mul_contDiffOn (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
    ((toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior) hΩc hΩs
    ((densityOnEuclid_contDiffOn q α).mono (image_mono interior_subset)) hf

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
