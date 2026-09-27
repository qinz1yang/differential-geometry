import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarComparison

noncomputable section

open Filter
open scoped Topology

private theorem one_le_mul_sq_of_eventually_inv_sqrt_lt
    {q r : ℕ → ℝ} {Q R : ℝ}
    (hq : Tendsto q atTop (𝓝 Q))
    (hr : Tendsto r atTop (𝓝 R))
    (hQ : 0 < Q)
    (hlower : ∀ᶠ i in atTop, 1 / Real.sqrt (q i) < r i) :
    1 ≤ Q * R ^ 2 := by
  have hsq : Tendsto (fun i => Real.sqrt (q i)) atTop (𝓝 (Real.sqrt Q)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have hsqpos : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hinv : Tendsto (fun i => 1 / Real.sqrt (q i)) atTop
      (𝓝 (1 / Real.sqrt Q)) := by
    exact (tendsto_const_nhds.div hsq
      hsqpos)
  have hle : 1 / Real.sqrt Q ≤ R := le_of_tendsto_of_tendsto hinv hr (hlower.mono fun _ h => h.le)
  have hmul : 1 ≤ Real.sqrt Q * R := by
    simpa only [mul_comm] using (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mp hle
  calc
    1 ≤ (Real.sqrt Q * R) ^ 2 := by nlinarith [sq_nonneg (Real.sqrt Q * R - 1)]
    _ = Q * R ^ 2 := by rw [mul_pow, Real.sq_sqrt hQ.le]

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_scalar_mul_sq_distance_limit_lower_bound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ centers points : ∀ i, (X.term i).M,
              (∀ᶠ i in atTop, 2 ≤ (X.term i).S.scalar 0 (centers i)) →
              Tendsto (fun i => (X.term i).S.scalar 0 (points i)) atTop atTop →
              ∀ Q r : ℝ,
                Tendsto (fun i => (X.term i).S.scalar 0 (centers i)) atTop (nhds Q) →
                Tendsto (fun i => metricDistance ((X.term i).S.base.metric 0)
                  (centers i) (points i)) atTop (nhds r) →
                1 ≤ Q * r ^ 2 := by
  obtain ⟨epsStar, D, hepsStar, hD, hcmp⟩ :=
    exists_scalar_le_mul_scalar_of_modelCurvatureBound hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hsmall sigma hsigma Phi hPhi X centers points hhigh hcurv Q r hQ hr
  have hQtwo : 2 ≤ Q := ge_of_tendsto hQ hhigh
  have hQpos : 0 < Q := by linarith
  apply one_le_mul_sq_of_eventually_inv_sqrt_lt hQ hr hQpos
  filter_upwards [hhigh, hQ.eventually_lt_const (show Q < Q + 1 by linarith),
    hcurv.eventually_gt_atTop (D * (Q + 1))] with i hi hQi hpi
  let _ : ConnectedSpace (X.term i).M := X.connected i
  have hpos : 0 < (X.term i).S.scalar 0 (centers i) := by linarith
  by_contra hnot
  have hdist : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
      (centers i) (points i) ≤
        ENNReal.ofReal (1 / Real.sqrt ((X.term i).S.scalar 0 (centers i))) :=
    (ENNReal.le_ofReal_iff_toReal_le
      (riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric 0)
        (centers i) (points i)) (by positivity)).mpr
      (by simpa only [metricDistance] using le_of_not_gt hnot)
  have htime : (0 : ℝ) ∈ Set.Icc (-X.depth i) 0 :=
    ⟨neg_nonpos.mpr (X.depth_pos i).le, le_rfl⟩
  have hbound := hcmp eps heps hsmall sigma hsigma Phi hPhi X i 0 htime
    (centers i) hi (points i) hdist
  have hlt := mul_lt_mul_of_pos_left hQi hD
  exact (not_lt_of_ge hbound) (hlt.trans hpi)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
