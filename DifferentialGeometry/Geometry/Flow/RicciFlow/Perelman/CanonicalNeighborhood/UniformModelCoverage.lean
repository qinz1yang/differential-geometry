import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicBallOfCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelRestriction
import DifferentialGeometry.Topology.Manifold.ConnectedComponent
import DifferentialGeometry.Geometry.Curvature.OperatorNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingPullback

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
universe u

private theorem high_curvature_model_threshold_of_connected
    {eps kappa sigma eta : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hkappa : 0 < kappa)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M],
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
        ∀ (o : TangentOrientationSection M) (a b : ℝ),
        Icc a b ⊆ D.carrier → Ioo a b ⊆ D.regular →
        PhiAlmostNonnegative S (Icc a b) Phi →
        ParabolicallyKappaNoncollapsedBelowScale S (modelNoncollapseFactor * kappa) sigma →
        ∀ x t, t ∈ Icc (a+eta) b → Q₀ ≤ S.scalar t x →
          OrientedWitness S o eps kappa x t := by
  let A := eta⁻¹
  have hA : 0 < A := inv_pos.mpr heta
  obtain ⟨r,hr,hrsmall,hmodel⟩ := abstract_model_theorem (eps := eps) (kappa := kappa)
    (sigma := Real.sqrt A * sigma) (Phi := rescalePinchingFunction A Phi)
    heps heps1 hkappa (mul_pos (Real.sqrt_pos.mpr hA) hsigma) (hPhi.rescale hA)
  refine ⟨A/r^2,div_pos hA (sq_pos_of_pos hr),?_⟩
  intro M _ _ _ _ _ _ D S hS o a b hcarrier hregular hpinch hnoncollapse x t ht hhigh
  have hab : a < b := by linarith [ht.1,ht.2]
  have ha : a ∈ D.carrier := hcarrier ⟨le_rfl,hab.le⟩
  let P := parabolicSolution S a A hA ha
  let T := A*(b-a)
  have hT : 1 ≤ T := by
    have he : A*eta = 1 := inv_mul_cancel₀ heta.ne'
    have hh := mul_le_mul_of_nonneg_left (by linarith [ht.1,ht.2] : eta ≤ b-a) hA.le
    rwa [he] at hh
  let D' := RealTimeInterval.closed 0 T (zero_le_one.trans hT)
  let L := P.timeRestrict D'
  have htime : ∀ s ∈ Icc 0 T, a+s/A ∈ Icc a b := by
    intro s hs
    refine ⟨by linarith [div_nonneg hs.1 hA.le],?_⟩
    have hh := (div_le_iff₀ hA).mpr (show s ≤ (b-a)*A by simpa only [T,mul_comm] using hs.2)
    linarith
  have hsub : D'.carrier ⊆ (parabolicInterval D a A ha).carrier :=
    fun s hs => hcarrier (htime s hs)
  have hreg : D'.regular ⊆ (parabolicInterval D a A ha).regular := by
    intro s hs
    apply hregular
    change a < a+s/A ∧ a+s/A < b
    refine ⟨by linarith [div_pos hs.1 hA],?_⟩
    have hh := (div_lt_iff₀ hA).mpr (show s < (b-a)*A by simpa only [T,mul_comm] using hs.2)
    linarith
  have hL : IsSolutionOn L :=
    isSolutionOn_timeRestrict (parabolicSolution_isSolutionOn S hS a A hA ha) hsub hreg
  have hnoncol : ParabolicallyKappaNoncollapsedBelowScale L (modelNoncollapseFactor * kappa)
      (Real.sqrt A*sigma) :=
    parabolicallyKappaNoncollapsedBelowScale_timeRestrict hsub
      (parabolicallyKappaNoncollapsedBelowScale_parabolicSolution S a A hA ha _ sigma hnoncollapse)
  have hpin := phiAlmostNonnegative_paraSolution S hA ha hpinch
  have hpinL : PhiAlmostNonnegative L D'.carrier (rescalePinchingFunction A Phi) := by
    intro s hs y
    exact hpin s (htime s hs) y
  have hcurv : ∀ c d : ℝ, c ≤ d → Icc c d ⊆ D'.carrier →
      ∃ C : ℝ, ∀ s ∈ Icc c d, ∀ y : M, FlowMetricBall.rmNormSq L s y ≤ C := by
    intro c d _ hcd
    obtain ⟨C,_,hC⟩ := exists_curvature_bound_on_carrier_interval_of_isSolutionOn L hL hcd
    refine ⟨C,?_⟩
    intro s hs y
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04, metricRm04_apply,
      SolutionOn.family_metric] using hC s hs y
  have hhyp : ClosedModelHypotheses L kappa (Real.sqrt A*sigma) (rescalePinchingFunction A Phi) :=
    ⟨hL,fun _ _ => RiemannianMetricComplete.of_compact _,hcurv,hpinL,hnoncol⟩
  have hnormtime : parabolicTime a A (A*(t-a)) = t := by
    unfold parabolicTime
    rw [mul_div_cancel_left₀ _ hA.ne']
    ring
  have hmem : A*(t-a) ∈ Icc 1 T := by
    constructor
    · have he : A*eta = 1 := inv_mul_cancel₀ heta.ne'
      have hh := mul_le_mul_of_nonneg_left (by linarith [ht.1] : eta ≤ t-a) hA.le
      rwa [he] at hh
    · exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hA.le
  have hscalar : L.scalar (A*(t-a)) x = A⁻¹*S.scalar t x := by
    dsimp only [L,P]
    rw [scalar_timeRestrict,parabolicSolution_scalar]
    simp only [hnormtime]
  have hthreshold : r⁻¹^2 ≤ L.scalar (A*(t-a)) x := by
    rw [hscalar]
    have he : r⁻¹^2 = A⁻¹*(A/r^2) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hhigh (inv_nonneg.mpr hA.le)
  have hw := hmodel M o T hT L hhyp x (A*(t-a)) hmem hthreshold
  have hwP := orientedWitness_of_timeRestrict hsub hw
  have hwS := (orientedWitness_paraSolution_iff S o hA ha (A*(t-a)) x eps kappa).mp hwP
  rwa [hnormtime] at hwS

private theorem pinching_restrict_open
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {W : Set ℝ} {Phi : ℝ → ℝ} (hpin : PhiAlmostNonnegative S W Phi)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] :
    PhiAlmostNonnegative (solutionOnRestrictOpen S U) W Phi := by
  apply (phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt _ _ _ (by simp [ThreeSpace])).mpr
  have h := (phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt _ _ _ (by simp [ThreeSpace])).mp hpin
  intro t ht x
  change -Phi ((solutionOnRestrictOpen S U).scalar t x) ≤
    leastCurvatureOperatorEigenvalueAt ((S.base.metric t).restrictOpen U) x
      (metricAlgebraicCurvatureTensorAt ((S.base.metric t).restrictOpen U) x)
  rw [scalar_restrictOpen,leastCurvatureOperatorEigenvalueAt_restrictOpen]
  exact h t ht x.val

theorem exists_uniform_high_curvature_model_threshold
    {eps kappa sigma eta : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hkappa : 0 < kappa)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M],
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
        ∀ (o : TangentOrientationSection M) (a b : ℝ),
        Icc a b ⊆ D.carrier → Ioo a b ⊆ D.regular →
        PhiAlmostNonnegative S (Icc a b) Phi →
        ParabolicallyKappaNoncollapsedBelowScale S (modelNoncollapseFactor * kappa) sigma →
        ∀ x t, t ∈ Icc (a+eta) b → Q₀ ≤ S.scalar t x →
          OrientedWitness S o eps kappa x t := by
  obtain ⟨Q₀,hQ₀,hmodel⟩ := high_curvature_model_threshold_of_connected
    heps heps1 hkappa hsigma heta hPhi
  refine ⟨Q₀,hQ₀,?_⟩
  intro M _ _ _ _ _ D S hS o a b hcarrier hregular hpin hnc x t ht hhigh
  let U := connectedComponentOpen (I := I3) x
  let : CompactSpace U := connectedComponentOpen_compactSpace (I := I3) x
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := I3) x
  let y : U := connectedComponentPoint (I := I3) x
  have hU : IsClosed (U : Set M) := isClosed_connectedComponent
  let L := solutionOnRestrictOpen S U
  have hL : IsSolutionOn L := isSolutionOn_restrictOpen S hS U
  have hncL : ParabolicallyKappaNoncollapsedBelowScale L (modelNoncollapseFactor * kappa) sigma :=
    parabolicallyKappaNoncollapsedBelowScale_restrictOpen_of_isClosed hnc U hU
  have hpinL : PhiAlmostNonnegative L (Icc a b) Phi := pinching_restrict_open hpin U
  have hhighL : Q₀ ≤ L.scalar t y := by rw [scalar_restrictOpen]; exact hhigh
  have hw := hmodel U _ L hL (o.restrictOpen U) a b hcarrier hregular hpinL hncL y t ht hhighL
  exact hw.ofRestrictOpen hU o
theorem exists_uniform_incoming_high_curvature_model_threshold
    {eps kappa sigma eta : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hkappa : 0 < kappa)
    (hsigma : 0 < sigma) (heta : 0 < eta) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M],
      ∀ (a b : ℝ) (hab : a < b),
        ∀ S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen a b hab),
        IsSolutionOn S → ∀ o : TangentOrientationSection M,
        PhiAlmostNonnegative S (Ico a b) Phi →
        ParabolicallyKappaNoncollapsedBelowScale S (modelNoncollapseFactor * kappa) sigma →
        ∀ x t, t ∈ Ico (a+eta) b → Q₀ ≤ S.scalar t x →
          OrientedWitness S o eps kappa x t := by
  obtain ⟨Q₀,hQ₀,hmodel⟩ := exists_uniform_high_curvature_model_threshold
    heps heps1 hkappa hsigma heta hPhi
  refine ⟨Q₀,hQ₀,?_⟩
  intro M _ _ _ _ _ a b hab S hS o hpin hnc x t ht hhigh
  exact hmodel M _ S hS o a t
    (fun s hs => ⟨hs.1,hs.2.trans_lt ht.2⟩)
    (fun s hs => ⟨hs.1,hs.2.trans ht.2⟩)
    (fun s hs => hpin s ⟨hs.1,hs.2.trans_lt ht.2⟩) hnc x t ⟨ht.1,le_rfl⟩ hhigh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
