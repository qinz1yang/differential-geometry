import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Geodesic.Ray
import DifferentialGeometry.Topology.Order.IntermediateValue

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_high_curvature_geodesic_tail {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar c : ℝ, 0 < epsStar ∧ 0 < c ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ y : (X.term i).M, 12 < (X.term i).S.scalar 0 y →
              let L := metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y
              ∃ (γ : ℝ → (X.term i).M) (s : ℝ), s ∈ Ico 0 L ∧
                γ 0 = (X.term i).basepoint ∧ γ L = y ∧
                ContMDiff 𝓘(ℝ, ℝ) I3 ∞ γ ∧
                (∀ t, IsGeodesicAt ((X.term i).S.base.metric 0) γ t) ∧
                (∀ t, ((X.term i).S.base.metric 0).inner (γ t)
                  (mfderiv 𝓘(ℝ, ℝ) I3 γ t 1) (mfderiv 𝓘(ℝ, ℝ) I3 γ t 1) = 1) ∧
                (∀ t ∈ Icc 0 L, ∀ v ∈ Icc 0 L,
                  metricDistance ((X.term i).S.base.metric 0) (γ t) (γ v) = |t - v|) ∧
                (X.term i).S.scalar 0 (γ s) = 2 ∧
                (∀ t ∈ Ioc s L, 2 < (X.term i).S.scalar 0 (γ t)) ∧ c < L - s := by
  obtain ⟨epsStar, c, C, hepsStar, hc, _, hprop⟩ := canonical_neighborhood_local_propagation hkappa
  refine ⟨epsStar, c / Real.sqrt 3, hepsStar, by positivity, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X] with i hi
  intro y hy
  let _ : ConnectedSpace (X.term i).M := X.connected i
  let L := metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hpq : (X.term i).basepoint ≠ y := by
    intro h
    have hb : (X.term i).S.scalar 0 (X.term i).basepoint = 1 := X.base_one i
    rw [h] at hb
    linarith
  obtain ⟨γ, hstart, hend, hsmooth, hgeo, hunit, hdist⟩ :=
    DifferentialGeometry.Geometry.exists_unitSpeed_minimizing_geodesic_of_complete
      ((X.term i).S.base.metric 0) ⟨X.complete i 0 hzero⟩ (X.term i).basepoint y hpq
  change γ L = y at hend
  change ∀ t ∈ Icc 0 L, ∀ v ∈ Icc 0 L,
    metricDistance ((X.term i).S.base.metric 0) (γ t) (γ v) = |t - v| at hdist
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hcont : Continuous (fun t => (X.term i).S.scalar 0 (γ t)) :=
    (metricScalar_smooth (I := I3) ((X.term i).S.base.metric 0)).continuous.comp hsmooth.continuous
  obtain ⟨s, hs, hscalar, htail⟩ := hcont.continuousOn.exists_eq_and_forall_gt hL
    (show (X.term i).S.scalar 0 (γ 0) ≤ 2 by rw [hstart, X.base_one]; norm_num)
    (show 2 < (X.term i).S.scalar 0 (γ L) by rw [hend]; linarith)
  refine ⟨γ, s, hs, hstart, hend, hsmooth, hgeo, hunit, hdist, hscalar, htail, ?_⟩
  by_contra h
  change ¬ c / Real.sqrt 3 < L - s at h
  have hnear : metricDistance ((X.term i).S.base.metric 0) (γ s) y ≤ c / Real.sqrt 3 := by
    rw [← hend, hdist s ⟨hs.1, hs.2.le⟩ L ⟨hL, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr hs.2.le)]
    linarith [le_of_not_gt h]
  have hmem : (y, (0 : ℝ)) ∈ frozenBackwardCylinder (X.term i).S (γ s) 0 c c
      (1 + |(X.term i).S.scalar 0 (γ s)|) := by
    have hthree : 1 + |(X.term i).S.scalar 0 (γ s)| = 3 := by rw [hscalar]; norm_num
    rw [hthree]
    refine ⟨?_, ⟨by linarith [div_pos hc (by norm_num : (0 : ℝ) < 3)], le_rfl⟩⟩
    exact (ENNReal.le_ofReal_iff_toReal_le
      (riemannianEDistOf_ne_top ((X.term i).S.base.metric 0) (γ s) y)
      (by positivity)).mpr hnear
  have hbound := (hi 0 ⟨by linarith [X.depth_pos i], le_rfl⟩ (γ s)).2 y 0 hmem
  have hh := hbound.2.1
  rw [hscalar] at hh
  have hnum : 4 * (1 + |(2 : ℝ)|) = 12 := by norm_num
  rw [hnum] at hh
  exact (not_le.mpr hy) hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
