import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

noncomputable section

open Set Filter
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_uniform_recentered_backward_curvature_bound
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ A : ℝ, ∃ r δ C : ℝ, 0 < r ∧ 0 < δ ∧ 0 < C ∧
            ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
              ∀ s ∈ Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
                (X.term i).S.scalar s z ≤ A →
                Icc (s - δ) s ⊆ (X.interval i).carrier ∧
                ∀ y v, metricDistance ((X.term i).S.base.metric s) z y ≤ r →
                  v ∈ Icc (s - δ) s →
                  (X.term i).S.scalar v y ≤ C ∧
                    Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S v y) ≤ C := by
  obtain ⟨epsStar, c, K, hepsStar, hc, hK, hprop⟩ :=
    canonical_neighborhood_local_propagation.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi A
  let L0 := 1 + max A (6 * Phi 0)
  have hPhi0 : 0 < Phi 0 := hPhi.pos 0
  have hL0 : 0 < L0 := by dsimp [L0]; linarith [le_max_right A (6 * Phi 0)]
  refine ⟨c / Real.sqrt L0, c / L0, max (4 * L0) (K * (L0 + 1)),
    div_pos hc (Real.sqrt_pos.mpr hL0), div_pos hc hL0,
    lt_max_of_lt_left (mul_pos (by norm_num) hL0), ?_⟩
  intro X
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.scale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    X.pinching_error_eventually hPhi (L0 := L0) (by norm_num : (0 : ℝ) < 1)]
    with i hlocal hscale herror
  intro s hs z hz
  let L := 1 + |(X.term i).S.scalar s z|
  have hL : 0 < L := by dsimp [L]; positivity
  have hscarrier : s ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i, hs.1], hs.2⟩
  have hlow : -6 * Phi 0 ≤ (X.term i).S.scalar s z := by
    have hb := neg_six_mul_phi_zero_le_scalar (hPhi.rescale (X.scale_pos i))
      (X.pinching i) (by simp [ThreeSpace]) hscarrier z
    have hres : rescalePinchingFunction (X.scale i) Phi 0 = (X.scale i)⁻¹ * Phi 0 := by
      simp only [rescalePinchingFunction, mul_zero]
    rw [hres] at hb
    have hinv : (X.scale i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hscale
    nlinarith
  have hLle : L ≤ L0 := by
    have habs : |(X.term i).S.scalar s z| ≤ max A (6 * Phi 0) :=
      abs_le.mpr ⟨by linarith [le_max_right A (6 * Phi 0)],
        hz.trans (le_max_left A (6 * Phi 0))⟩
    dsimp [L, L0]
    linarith
  have hδle : c / L0 ≤ c / L := div_le_div_of_nonneg_left hc.le hL hLle
  have hrle : c / Real.sqrt L0 ≤ c / Real.sqrt L :=
    div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hL) (Real.sqrt_le_sqrt hLle)
  have hsubset : Icc (s - c / L0) s ⊆ Icc (s - c / L) s :=
    Icc_subset_Icc (by linarith) le_rfl
  obtain ⟨hcarrier, hbound⟩ := hlocal s hs z
  refine ⟨hsubset.trans hcarrier, ?_⟩
  intro y v hd hv
  let : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hfin := DifferentialGeometry.riemannianEDistOf_ne_top (I := I3)
    ((X.term i).S.base.metric s) z y
  have hball : y ∈ riemannianClosedBallOf (I := I3)
      ((X.term i).S.base.metric s) z (c / Real.sqrt L) :=
    (ENNReal.le_ofReal_iff_toReal_le hfin (div_pos hc (Real.sqrt_pos.mpr hL)).le).mpr
      (by simpa only [metricDistance] using hd.trans hrle)
  have hb := hbound y v ⟨hball, hsubset hv⟩
  have herr : (Phi (4 * X.scale i * L) + Phi 0) / X.scale i < 1 :=
    herror L ⟨by dsimp [L]; linarith [abs_nonneg ((X.term i).S.scalar s z)], hLle⟩
  refine ⟨hb.2.1.trans ((by linarith : 4 * L ≤ 4 * L0).trans (le_max_left _ _)), ?_⟩
  exact hb.2.2.trans ((mul_le_mul_of_nonneg_left (by linarith) hK.le).trans (le_max_right _ _))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
