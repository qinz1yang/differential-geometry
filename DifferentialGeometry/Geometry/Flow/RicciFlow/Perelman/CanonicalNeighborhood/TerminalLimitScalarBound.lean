import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCompactOrNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedSpatialNeckScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitFrontierInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitCompactness

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem terminal_limit_scalar_bound_frontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) : TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi := by
  obtain ⟨alpha0, ha0, hsmall0, hneckbound⟩ := exists_eventually_spatialNeck_scalar_upper_bound.{u}
  let alpha := neckModelTolerance alpha0 / 2
  have htol : neckModelTolerance alpha0 < alpha0 :=
    (neckModelTolerance_le_smallness alpha0).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha0 hsmall0)
  have ha : 0 < alpha := half_pos (neckModelTolerance_pos ha0)
  have hsmall : alpha < 1 / 32 := by dsimp only [alpha]; linarith
  have hnktol : 2 * alpha = neckModelTolerance alpha0 := by dsimp [alpha]; ring
  obtain ⟨epsStar, r, C, hepsStar, hr, hC, hwindow⟩ :=
    exists_windowed_scalar_comparison_or_spatial_neck.{u} kappa ha hsmall
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X hb hd P hcanonical hconn hcapture hpre hdomains hnested horient hnc
  have hnonneg := blowup_limit_nonnegative X hPhi P.limit P.subseq P.strictMono P.maps
    P.convergence.metrics hcanonical
  have hsec : HasNonnegativeSectionalCurvature P.limit.metric := by
    apply (hasNonnegativeSectionalCurvature_iff P.limit.metric).mpr
    intro x v w
    have hh := hnonneg x (mem_univ x) v w
    have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [zero_mul, metricRm04StandardAt, tensor04StandardAt, hvec] using hh
  obtain ⟨B, hB, hbound⟩ := hneckbound (X.toFlowSequence.atTime 0) P.limit P.subseq
    P.maps P.convergence.metrics hcanonical P.limit_complete hconn hsec
  refine ⟨max (max 2 C) (C * B), ?_⟩
  apply metricScalarAt_le_of_eventually_comparable_spatialNeck
    P.maps P.convergence.metrics hcanonical P.limit_complete hconn.toPreconnectedSpace
    hC.le hr.le hbound
  intro x hx
  have hlarge : ∀ᶠ i in atTop,
      max 2 C < (X.term (P.subseq i)).S.scalar 0 (P.maps.map i x) :=
    (KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      P.convergence.metrics hcanonical x).eventually (Ioi_mem_nhds hx)
  filter_upwards [hlarge] with i hi
  let _ : ConnectedSpace (X.term (P.subseq i)).M := X.connected (P.subseq i)
  have htwo : 2 < (X.term (P.subseq i)).S.scalar 0 (P.maps.map i x) :=
    (le_max_left 2 C).trans_lt hi
  have hCscalar : C < (X.term (P.subseq i)).S.scalar 0 (P.maps.map i x) :=
    (le_max_right 2 C).trans_lt hi
  obtain ⟨W, oN, hO⟩ := X.higher_good (P.subseq i) 0
    (show 0 ∈ Icc (-X.depth (P.subseq i)) 0 from
      ⟨by linarith [X.depth_pos (P.subseq i)], le_rfl⟩) (P.maps.map i x) htwo.le
  rcases hwindow (X.term (P.subseq i)).M (X.interval (P.subseq i))
      (X.term (P.subseq i)).S eps (P.maps.map i x) 0 W hle oN with hglobal | hneck
  · have hh := hglobal (X.term (P.subseq i)).basepoint
    have hbase := X.base_one (P.subseq i)
    rw [hbase, mul_one] at hh
    exact (not_le_of_gt hCscalar hh).elim
  · obtain ⟨y, ⟨nk⟩, hlo, hhi, hdist⟩ := hneck
    have hroot : 1 ≤ Real.sqrt ((X.term (P.subseq i)).S.scalar 0 (P.maps.map i x)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 ≤
        (X.term (P.subseq i)).S.scalar 0 (P.maps.map i x) by linarith)
    have hdist0 : metricDistance ((X.term (P.subseq i)).S.base.metric 0)
        (P.maps.map i x) (W.embedding y) ≤ r := by
      have hnn : 0 ≤ metricDistance ((X.term (P.subseq i)).S.base.metric 0)
          (P.maps.map i x) (W.embedding y) := ENNReal.toReal_nonneg
      nlinarith
    have hball : W.embedding y ∈ riemannianClosedBallOf
        ((X.term (P.subseq i)).S.base.metric 0) (P.maps.map i x) r :=
      (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top _ _ _) hr.le).mpr hdist0
    have hcompare : (X.term (P.subseq i)).S.scalar 0 (P.maps.map i x) ≤
        C * (X.term (P.subseq i)).S.scalar 0 (W.embedding y) := by
      have hh := mul_le_mul_of_nonneg_left hlo hC.le
      rwa [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at hh
    rw [hnktol] at nk
    exact ⟨W.embedding y, hball, ⟨nk⟩, hcompare⟩

theorem terminal_limit_exists {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) :=
  terminal_limit_global_bound_of_frontiers hPhi (terminal_limit_compactness_frontier hkappa hPhi)
    (terminal_limit_scalar_bound_frontier hPhi)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem terminal_limit_global_bound {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) := by
  obtain ⟨epsStar, hpos, h⟩ := terminal_limit_exists.{u} hkappa hPhi
  refine ⟨min epsStar sigma, lt_min hpos hsigma, ?_⟩
  intro eps heps hle X hb hd
  exact h eps heps (hle.trans (min_le_left epsStar sigma)) X hb hd

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
