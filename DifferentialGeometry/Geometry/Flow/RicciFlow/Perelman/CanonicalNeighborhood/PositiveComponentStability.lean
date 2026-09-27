import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.DerivativeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import DifferentialGeometry.Geometry.Metric.Family.DistanceContinuity
import DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ChartGramContinuity
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
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

end

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) D}

theorem IsSolutionOn.eventually_scalar_normalized_volume_bound_on_compact
    [SigmaCompactSpace M] (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    {K : Set M} (hK : IsCompact K) {C : ℝ} (hQ : 0 < S.scalar t x)
    (hvolume : ENNReal.ofReal (C⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) <
      riemannianVolumeMeasure ThreeModel M (S.base.metric t) K) :
    ∀ᶠ p : ℝ × M in 𝓝 (t,x),
      ENNReal.ofReal (C⁻¹ / (S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2))) <
        riemannianVolumeMeasure ThreeModel M (S.base.metric p.1) K := by
  have hcenter : ContinuousAt (fun p : ℝ × M => S.scalar p.1 p.2) (t,x) :=
    hS.scalarCont.continuousAt (prod_mem_nhds (D.regular_mem_nhds ht) univ_mem)
  have hden : ContinuousAt (fun p : ℝ × M =>
      S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2)) (t,x) := hcenter.mul hcenter.sqrt
  have hratio : ContinuousAt (fun p : ℝ × M =>
      C⁻¹ / (S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2))) (t,x) :=
    continuousAt_const.div hden (mul_pos hQ (Real.sqrt_pos.mpr hQ)).ne'
  have hbound : ContinuousAt (fun p : ℝ × M =>
      ENNReal.ofReal (C⁻¹ / (S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2)))) (t,x) :=
    ENNReal.continuous_ofReal.continuousAt.comp (f := fun p : ℝ × M =>
      C⁻¹ / (S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2))) hratio
  obtain ⟨v, hv, hvK⟩ := exists_between hvolume
  have htime : ∀ᶠ s in 𝓝 t, v < riemannianVolumeMeasure ThreeModel M (S.base.metric s) K :=
    eventually_lt_riemannianVolumeMeasure_on_compact (I := ThreeModel) S.base.metric
      (S.continuousOn_chartGram hS) (D.regular_mem_nhds ht) hK hvK
  have hvol : ∀ᶠ p : ℝ × M in 𝓝 (t,x),
      v < riemannianVolumeMeasure ThreeModel M (S.base.metric p.1) K :=
    (continuous_fst.tendsto (t,x)).eventually htime
  filter_upwards [hvol, hbound.eventually (Iio_mem_nhds hv)] with p hp hpb
  exact hpb.trans hp

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) D}

omit [SigmaCompactSpace M] in
private theorem closedBall_subset_compact_component
    (g : SmoothRiemannianMetric ThreeModel M) (x : M) {U : Set M}
    (hU : U = connectedComponent x) (hK : IsCompact U) (r : ℝ) :
    riemannianClosedBallOf g x r ⊆ interior U ∧ IsCompact (riemannianClosedBallOf g x r) := by
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  have hopen : IsOpen U := hU ▸ isOpen_connectedComponent
  have hsub : riemannianClosedBallOf g x r ⊆ U := by
    intro y hy
    have hr : ENNReal.ofReal r < ENNReal.ofReal (max r 0 + 1) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      linarith [le_max_left r 0]
    exact hU.symm ▸ Geometry.Metric.edistOf_ball_subset_connCompOpen g x (max r 0 + 1) (hy.trans_lt hr)
  exact ⟨by rw [hopen.interior_eq]; exact hsub,
    hK.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf g x r) hsub⟩

theorem eventually_compact_connectedComponent_reserves
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    {U : Set M} (hU : U = connectedComponent x) (hK : IsCompact U)
    {C1 C2 c r rout : ℝ} (hQ : 0 < S.scalar t x)
    (hc : C2⁻¹ * S.scalar t x < c) (hsec : SecLower (S.base.metric t) c U)
    (hr : 1 < Real.sqrt (S.scalar t x) * r) (hrC : Real.sqrt (S.scalar t x) * r < C1)
    (houter : U ⊆ riemannianBallOf (S.base.metric t) x rout)
    (hscalar : ∀ z ∈ U, C2⁻¹ * S.scalar t x < S.scalar t z ∧ S.scalar t z < C2 * S.scalar t x)
    (hrm : ∀ z ∈ U, Real.sqrt (normSq0S (S.base.metric t) z 4 (S.base.rm04 t z)) < C2 * S.scalar t x)
    (hvolume : ENNReal.ofReal (C2⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) <
      riemannianVolumeMeasure ThreeModel M (S.base.metric t) U) :
    ∃ d : ℝ, 0 < d ∧ d < c ∧ ∀ᶠ p : ℝ × M in 𝓝 (t,x),
      p.1 ∈ D.regular ∧ U = connectedComponent p.2 ∧
      ∃ hRp : 0 < S.scalar p.1 p.2,
        1 < Real.sqrt (S.scalar p.1 p.2) * r ∧ Real.sqrt (S.scalar p.1 p.2) * r < C1 ∧
        U ⊆ riemannianBallOf (S.base.metric p.1) p.2 rout ∧
        (∀ a : ℝ, riemannianClosedBallOf (S.base.metric p.1) p.2 a ⊆ interior U ∧
          IsCompact (riemannianClosedBallOf (S.base.metric p.1) p.2 a)) ∧
        (∀ z ∈ U, C2⁻¹ * S.scalar p.1 p.2 < S.scalar p.1 z ∧
          S.scalar p.1 z < C2 * S.scalar p.1 p.2 ∧
          Real.sqrt (normSq0S (S.base.metric p.1) z 4 (S.base.rm04 p.1 z)) < C2 * S.scalar p.1 p.2) ∧
        ENNReal.ofReal (C2⁻¹ / (S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2))) <
          riemannianVolumeMeasure ThreeModel M (S.base.metric p.1) U ∧
        C2⁻¹ * S.scalar p.1 p.2 < d ∧ SecLower (S.base.metric p.1) d U ∧
        C2⁻¹ < d / S.scalar p.1 p.2 ∧
        SecLower (scaleMetric (S.scalar p.1 p.2) hRp (S.base.metric p.1)) (d / S.scalar p.1 p.2) U := by
  have hC2 : 0 < C2 := pos_of_mul_pos_left (hQ.trans
    (hscalar x (hU.symm ▸ mem_connectedComponent)).2) hQ.le
  obtain ⟨d, hd, _, hdc, hsectional⟩ := eventually_secLower_on_compact_connectedComponent hS ht x hU hK hC2 hQ hc hsec
  have hcurv := hS.eventually_scalar_riemann_bounds_on_compact ht x hK hscalar hrm
  have hvol := hS.eventually_scalar_normalized_volume_bound_on_compact ht x hK hQ hvolume
  have hout := hS.smoothMetric.eventually_compact_subset_ball ht x hK houter
  have hradius : ContinuousAt (fun p : ℝ × M => Real.sqrt (S.scalar p.1 p.2) * r) (t,x) :=
    (hS.scalarCont.continuousAt (prod_mem_nhds (D.regular_mem_nhds ht) univ_mem)).sqrt.mul_const r
  refine ⟨d, hd, hdc, ?_⟩
  filter_upwards [hsectional,hcurv,hvol,hout,hradius.eventually (Ioo_mem_nhds hr hrC)] with p hs hcurv hvol hout hradius
  obtain ⟨hpt,hUp,hRp,hpd,hsec,hpn,hsecn⟩ := hs
  exact ⟨hpt,hUp,hRp,hradius.1,hradius.2,hout,
    closedBall_subset_compact_component (S.base.metric p.1) p.2 hUp hK,hcurv,hvol,hpd,hsec,hpn,hsecn⟩


theorem eventually_positiveComponent_reserves
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    {U : Set M} (hU : U = connectedComponent x) (data : PositiveComponent U)
    {C1 C2 c r rout : ℝ} (hQ : 0 < S.scalar t x)
    (hc : C2⁻¹ * S.scalar t x < c) (hsec : SecLower (S.base.metric t) c U)
    (hr : 1 < Real.sqrt (S.scalar t x) * r) (hrC : Real.sqrt (S.scalar t x) * r < C1)
    (houter : U ⊆ riemannianBallOf (S.base.metric t) x rout)
    (hscalar : ∀ z ∈ U, C2⁻¹ * S.scalar t x < S.scalar t z ∧ S.scalar t z < C2 * S.scalar t x)
    (hrm : ∀ z ∈ U, Real.sqrt (normSq0S (S.base.metric t) z 4 (S.base.rm04 t z)) < C2 * S.scalar t x)
    (hvolume : ENNReal.ofReal (C2⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) <
      riemannianVolumeMeasure ThreeModel M (S.base.metric t) U) :
    ∃ d : ℝ, 0 < d ∧ d < c ∧ ∀ᶠ p : ℝ × M in 𝓝 (t,x),
      p.1 ∈ D.regular ∧ U = connectedComponent p.2 ∧
      ∃ hRp : 0 < S.scalar p.1 p.2,
        1 < Real.sqrt (S.scalar p.1 p.2) * r ∧ Real.sqrt (S.scalar p.1 p.2) * r < C1 ∧
        U ⊆ riemannianBallOf (S.base.metric p.1) p.2 rout ∧
        (∀ a : ℝ, riemannianClosedBallOf (S.base.metric p.1) p.2 a ⊆ interior U ∧
          IsCompact (riemannianClosedBallOf (S.base.metric p.1) p.2 a)) ∧
        (∀ z ∈ U, C2⁻¹ * S.scalar p.1 p.2 < S.scalar p.1 z ∧
          S.scalar p.1 z < C2 * S.scalar p.1 p.2 ∧
          Real.sqrt (normSq0S (S.base.metric p.1) z 4 (S.base.rm04 p.1 z)) < C2 * S.scalar p.1 p.2) ∧
        ENNReal.ofReal (C2⁻¹ / (S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2))) <
          riemannianVolumeMeasure ThreeModel M (S.base.metric p.1) U ∧
        C2⁻¹ * S.scalar p.1 p.2 < d ∧ SecLower (S.base.metric p.1) d U ∧
        C2⁻¹ < d / S.scalar p.1 p.2 ∧
        SecLower (scaleMetric (S.scalar p.1 p.2) hRp (S.base.metric p.1)) (d / S.scalar p.1 p.2) U := by
  exact eventually_compact_connectedComponent_reserves hS ht x hU
    (isCompact_of_positiveComponent data) hQ hc hsec hr hrC houter hscalar hrm hvolume

end DifferentialGeometry.PDE.RicciFlow

end


noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := M) D}

theorem isOpen_setOf_positiveComponent_with_reserves
    (hS : IsSolutionOn S) (C1 C2 : ℝ) :
    IsOpen {p : ℝ × M | p.1 ∈ D.regular ∧
      ∃ U : Set M, Nonempty (PositiveComponent U) ∧ U = connectedComponent p.2 ∧
        0 < S.scalar p.1 p.2 ∧ ∃ c r rout : ℝ,
          C2⁻¹ * S.scalar p.1 p.2 < c ∧ SecLower (S.base.metric p.1) c U ∧
          1 < Real.sqrt (S.scalar p.1 p.2) * r ∧ Real.sqrt (S.scalar p.1 p.2) * r < C1 ∧
          rout < 2*r ∧ U ⊆ riemannianBallOf (S.base.metric p.1) p.2 rout ∧
          (∀ z ∈ U, C2⁻¹ * S.scalar p.1 p.2 < S.scalar p.1 z ∧
            S.scalar p.1 z < C2 * S.scalar p.1 p.2) ∧
          (∀ z ∈ U, Real.sqrt (normSq0S (S.base.metric p.1) z 4 (S.base.rm04 p.1 z)) <
            C2 * S.scalar p.1 p.2) ∧
          ENNReal.ofReal (C2⁻¹ / (S.scalar p.1 p.2 * Real.sqrt (S.scalar p.1 p.2))) <
            riemannianVolumeMeasure ThreeModel M (S.base.metric p.1) U ∧
          (S.base.metric p.1).inner p.2 (gradientFun (S.base.metric p.1) (S.scalar p.1) p.2)
            (gradientFun (S.base.metric p.1) (S.scalar p.1) p.2) < C2^2 * S.scalar p.1 p.2^3 ∧
          |derivWithin (fun t => S.scalar t p.2) (Iic p.1) p.1| < C2 * S.scalar p.1 p.2^2} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨ht,U,⟨data⟩,hU,hQ,c,r,rout,hc,hsec,hr,hrC,hrout,houter,hscalar,hrm,hvolume,hgrad,htime⟩
  obtain ⟨d, _, _, hnear⟩ := eventually_positiveComponent_reserves
    hS ht p.2 hU data hQ hc hsec hr hrC houter hscalar hrm hvolume
  have hresidual := S.scalar_derivative_residual_continuousOn hS C2 0
  have hzero : max
      ((S.base.metric p.1).inner p.2 (gradientFun (S.base.metric p.1) (S.scalar p.1) p.2)
        (gradientFun (S.base.metric p.1) (S.scalar p.1) p.2) - C2^2 * (max 0 (S.scalar p.1 p.2))^3)
      (|derivWithin (fun t => S.scalar t p.2) (Iic p.1) p.1| - C2 * (max 0 (S.scalar p.1 p.2))^2) < 0 := by
    rw [max_eq_right hQ.le, max_lt_iff]
    exact ⟨sub_neg.mpr hgrad, sub_neg.mpr htime⟩
  have hderiv := (hresidual.continuousAt
    ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨ht,mem_univ p.2⟩)).eventually (Iio_mem_nhds hzero)
  filter_upwards [hnear,hderiv] with q hq hdq
  obtain ⟨hqtime,hqU,hqR,hqr,hqrC,hqouter,_,hqscalar,hqvol,hqsec,hqseclower,_,_⟩ := hq
  have hqderiv :
      (S.base.metric q.1).inner q.2 (gradientFun (S.base.metric q.1) (S.scalar q.1) q.2)
        (gradientFun (S.base.metric q.1) (S.scalar q.1) q.2) < C2^2 * S.scalar q.1 q.2^3 ∧
      |derivWithin (fun t => S.scalar t q.2) (Iic q.1) q.1| < C2 * S.scalar q.1 q.2^2 := by
    simpa only [max_eq_right hqR.le, max_lt_iff, sub_neg] using hdq
  exact ⟨hqtime,U,⟨data⟩,hqU,hqR,d,r,rout,hqsec,hqseclower,hqr,hqrC,hrout,hqouter,
    (fun z hz => ⟨(hqscalar z hz).1,(hqscalar z hz).2.1⟩),
    (fun z hz => (hqscalar z hz).2.2),hqvol,hqderiv⟩

end DifferentialGeometry.PDE.RicciFlow
end
