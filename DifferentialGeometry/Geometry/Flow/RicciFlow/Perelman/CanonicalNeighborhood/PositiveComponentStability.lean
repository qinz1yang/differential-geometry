import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) D}

private theorem IsSolutionOn.continuousAt_least_curvature_eigenvalue
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M) :
    ContinuousAt (fun p : ℝ × M => leastCurvatureOperatorEigenvalueAt
      (S.base.metric p.1) p.2 (metricAlgebraicCurvatureTensorAt (S.base.metric p.1) p.2)) (t, x) := by
  obtain ⟨a, b, habmem, habnb, habreg⟩ := exists_Icc_mem_subset_of_mem_nhds (D.regular_isOpen.mem_nhds ht)
  have hat : a < t := (Icc_mem_nhds_iff.mp habnb).1
  have htb : t < b := (Icc_mem_nhds_iff.mp habnb).2
  have hab : 0 < b - a := sub_pos.mpr (hat.trans htb)
  let T := (S.timeShift a).timeRestrict (RealTimeInterval.closed 0 (b-a) hab.le)
  have hT : IsSolutionOn T := by
    apply isSolutionOn_timeRestrict (isSolutionOn_timeShift hS a)
    · intro s hs
      apply D.regular_subset
      apply habreg
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro s hs
      apply habreg
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hc := continuousOn_leastCurvatureOperatorEigenvalueAt_rm04 hab T hT
    (fun y => (VectorBundle.finrank_eq ℝ ThreeSpace (TangentSpace ThreeModel) y).trans (by simp [ThreeSpace]))
  have hn : Icc 0 (b-a) ×ˢ (univ : Set M) ∈ 𝓝 (t-a,x) :=
    prod_mem_nhds (Icc_mem_nhds (by linarith : 0 < t-a) (by linarith : t-a < b-a)) univ_mem
  have hcAt := hc.continuousAt hn
  have hcomp := hcAt.comp (x := (t,x)) ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousAt
  convert hcomp using 1
  funext p
  change leastCurvatureOperatorEigenvalueAt (S.base.metric p.1) p.2
    (metricAlgebraicCurvatureTensorAt (S.base.metric p.1) p.2) =
      leastCurvatureOperatorEigenvalueAt (S.base.metric (p.1 - a + a)) p.2
        (metricAlgebraicCurvatureTensorAt (S.base.metric (p.1 - a + a)) p.2)
  rw [sub_add_cancel]


open Perelman.CanonicalNeighborhood.FiniteHorn

theorem IsSolutionOn.eventually_secLower_on_compact
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular)
    {K : Set M} (hK : IsCompact K) {c d : ℝ} (hdc : d < c)
    (hsec : SecLower (S.base.metric t) c K) :
    ∀ᶠ s in 𝓝 t, SecLower (S.base.metric s) d K := by
  have heigen := (secLower_iff_le_leastCurvatureOperatorEigenvalueAt
    (S.base.metric t) (by simp [ThreeSpace]) c K).mp hsec
  have hevent : ∀ᶠ s in 𝓝 t, ∀ z ∈ K, d < leastCurvatureOperatorEigenvalueAt
      (S.base.metric s) z (metricAlgebraicCurvatureTensorAt (S.base.metric s) z) := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    exact (hS.continuousAt_least_curvature_eigenvalue ht z).eventually
      (Ioi_mem_nhds (hdc.trans_le (heigen z hz)))
  filter_upwards [hevent] with s hs
  exact (secLower_iff_le_leastCurvatureOperatorEigenvalueAt
    (S.base.metric s) (by simp [ThreeSpace]) d K).mpr (fun z hz => (hs z hz).le)

omit [IsManifold ThreeModel ∞ M] [T2Space M] in
private theorem isCompact_of_positiveComponent
    {U : Set M} (data : PositiveComponent U) : IsCompact U := by
  cases data with
  | sphere F hsource htarget =>
    have heq : F '' (univ : Set (Sphere 3)) = U := by
      rw [← hsource, F.toPartialEquiv.image_source_eq_target, htarget]
    rw [← heq]
    exact isCompact_univ.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono (by rw [hsource]))
  | projective Z presentation F hsource htarget =>
    have heq : F '' (univ : Set Z) = U := by
      rw [← hsource, F.toPartialEquiv.image_source_eq_target, htarget]
    rw [← heq]
    exact isCompact_univ.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono (by rw [hsource]))

theorem eventually_secLower_on_compact_connectedComponent
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    {U : Set M} (hU : U = connectedComponent x) (hK : IsCompact U)
    {C c : ℝ} (hC : 0 < C) (hQ : 0 < S.scalar t x)
    (hc : C⁻¹ * S.scalar t x < c) (hsec : SecLower (S.base.metric t) c U) :
    ∃ d : ℝ, 0 < d ∧ C⁻¹ * S.scalar t x < d ∧ d < c ∧
      ∀ᶠ p : ℝ × M in 𝓝 (t,x),
        p.1 ∈ D.regular ∧ U = connectedComponent p.2 ∧
        ∃ hRp : 0 < S.scalar p.1 p.2,
          C⁻¹ * S.scalar p.1 p.2 < d ∧ SecLower (S.base.metric p.1) d U ∧
          C⁻¹ < d / S.scalar p.1 p.2 ∧
          SecLower (scaleMetric (S.scalar p.1 p.2) hRp (S.base.metric p.1))
            (d / S.scalar p.1 p.2) U := by
  obtain ⟨d, hd, hdc⟩ := exists_between hc
  have hdpos : 0 < d := (mul_pos (inv_pos.mpr hC) hQ).trans hd
  have htime := hS.eventually_secLower_on_compact ht hK hdc hsec
  have hscalar : ContinuousAt (fun p : ℝ × M => S.scalar p.1 p.2) (t,x) :=
    hS.scalarCont.continuousAt (prod_mem_nhds (D.regular_mem_nhds ht) univ_mem)
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  have hmember : ∀ᶠ y in 𝓝 x, y ∈ connectedComponent x :=
    isOpen_connectedComponent.mem_nhds mem_connectedComponent
  refine ⟨d, hdpos, hd, hdc, ?_⟩
  filter_upwards [continuous_fst.continuousAt.eventually htime,
    continuous_fst.continuousAt.eventually (D.regular_isOpen.mem_nhds ht),
    continuous_snd.continuousAt.eventually hmember,
    (hscalar.const_mul C⁻¹).eventually (Iio_mem_nhds hd),
    hscalar.eventually (Ioi_mem_nhds hQ)] with p hp hpt hpx hpd hRp
  refine ⟨hpt, hU.trans (connectedComponent_eq hpx), hRp, hpd, hp,
    (lt_div_iff₀ hRp).mpr hpd, ?_⟩
  apply (secLower_scaleMetric_iff hRp (S.base.metric p.1) U).mpr
  rwa [div_mul_cancel₀ _ hRp.ne']


theorem eventually_secLower_on_positiveComponent
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    {U : Set M} (hU : U = connectedComponent x) (data : PositiveComponent U)
    {C c : ℝ} (hC : 0 < C) (hQ : 0 < S.scalar t x)
    (hc : C⁻¹ * S.scalar t x < c) (hsec : SecLower (S.base.metric t) c U) :
    ∃ d : ℝ, 0 < d ∧ C⁻¹ * S.scalar t x < d ∧ d < c ∧
      ∀ᶠ p : ℝ × M in 𝓝 (t,x),
        p.1 ∈ D.regular ∧ U = connectedComponent p.2 ∧
        ∃ hRp : 0 < S.scalar p.1 p.2,
          C⁻¹ * S.scalar p.1 p.2 < d ∧ SecLower (S.base.metric p.1) d U ∧
          C⁻¹ < d / S.scalar p.1 p.2 ∧
          SecLower (scaleMetric (S.scalar p.1 p.2) hRp (S.base.metric p.1))
            (d / S.scalar p.1 p.2) U := by
  exact eventually_secLower_on_compact_connectedComponent hS ht x hU
    (isCompact_of_positiveComponent data) hC hQ hc hsec

end DifferentialGeometry.PDE.RicciFlow
