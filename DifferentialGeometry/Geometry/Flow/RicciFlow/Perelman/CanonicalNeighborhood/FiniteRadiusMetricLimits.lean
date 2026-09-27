import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteRadiusInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.FiniteRadius
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.CompatibleChainLimitsGeneric

set_option autoImplicit false

noncomputable section

open Filter Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature CheegerGromovCompactness
open Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_compatible_metric_limits_below_controlled_radius
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ F : FiniteControlledRadius X, ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) →
            let Y := X.toFlowSequence.atTime 0
            ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ δ : ℕ → ℝ,
              (∀ n, 0 < δ n ∧ δ n ≤ ε n ∧ δ n ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
              Summable δ ∧
              ∃ Ψ : ∀ n, PartialDiffeomorph I3 I3
                  (Y.obj (σ n)).M (Y.obj (σ (n + 1))).M ∞,
                (∀ n, Ψ n (Y.obj (σ n)).basepoint = (Y.obj (σ (n + 1))).basepoint) ∧
                (∀ n, Nonempty (PartialDiffeomorphMetricApproximation
                  (riemannianClosedBallOf (Y.obj (σ n)).metric (Y.obj (σ n)).basepoint
                    (finiteComparisonRadius F.radius n)) (δ n) n (Ψ n)
                  (Y.obj (σ n)).metric (Y.obj (σ (n + 1))).metric)) ∧
                let M := fun n => (Y.obj (σ n)).M
                let g : ∀ n, SmoothRiemannianMetric I3 (M n) :=
                  fun n => (Y.obj (σ n)).metric
                let K : ∀ n, Set (M n) := fun n =>
                  riemannianClosedBallOf (g n) (Y.obj (σ n)).basepoint
                    (finiteStageRadius F.radius n)
                ∃ N : ℕ,
                  let Ψ' : ∀ j, PartialDiffeomorph I3 I3
                      (M (N + j)) (M (N + (j + 1))) ∞ := fun j => Ψ (N + j)
                  let U : ∀ j, Opens (M (N + j)) := fun j =>
                    ⟨riemannianBallOf (g (N + j)) (Y.obj (σ (N + j))).basepoint
                      (finiteStageRadius F.radius (N + j)), isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const⟩
                  ∃ _ : ∀ j k, PartialDiffeomorphMetricApproximation
                      (K (N + j)) (1 / 2) 0
                      (chainComp (Mf := fun j => M (N + j)) Ψ' j k)
                      (g (N + j)) (g (N + (j + k))),
                    ∃ hU : ∀ j k, (U j : Set (M (N + j))) ⊆
                        (chainComp (Mf := fun j => M (N + j)) Ψ' j k).source,
                      ∃ _ : ∀ j,
                          (chainComp (Mf := fun j => M (N + j)) Ψ' j 1 :
                            M (N + j) → M (N + (j + 1))) '' (U j : Set (M (N + j))) ⊆
                              (U (j + 1) : Set (M (N + (j + 1)))),
                        (∀ j p : ℕ, ∃ a : ℕ,
                          (chainComp (Mf := fun j => M (N + j)) Ψ' j a :
                            M (N + j) → M (N + (j + a))) '' (U j : Set (M (N + j))) ⊆
                              K (N + (j + a)) ∧
                          ∀ c : ℕ, Nonempty (PartialDiffeomorphMetricApproximation
                            (K (N + (j + a))) (1 / 2) p
                            (chainComp (Mf := fun j => M (N + j)) Ψ' (j + a) c)
                            (g (N + (j + a))) (g (N + ((j + a) + c))))) ∧
                        ∃ hne : ∀ j, Nonempty (U j),
                          let := hne
                          ∃ φ : ℕ → ℕ, StrictMono φ ∧
                            StrictMono (fun k => σ (N + φ k)) ∧
                            ∃ gInf : ∀ j, SmoothRiemannianMetric I3 (U j),
                              (∀ j,
                                letI : SigmaCompactSpace (U j) :=
                                  isSigmaCompact_iff_sigmaCompactSpace.mp
                                    (Geometry.isSigmaCompact_of_isOpen I3 (U j).isOpen)
                                MetricCInfConvergenceOnCompacts
                                  (fun k => PartialDiffeomorph.pullbackMetricOn
                                    (chainComp (Mf := fun j => M (N + j)) Ψ' j (φ k - j))
                                    (U j) (hU j (φ k - j)) (g (N + (j + (φ k - j)))))
                                  (gInf j) ((g (N + j)).restrictOpen (I := I3) (U j))) ∧
                              ∃ hU0 : ∀ j k, (U j : Set (M (N + j))) ⊆
                                  (chainComp Ψ (N + j) k).source,
                                ∃ hmap0 : ∀ j,
                                    (chainComp Ψ (N + j) 1 :
                                      M (N + j) → M (N + (j + 1))) ''
                                        (U j : Set (M (N + j))) ⊆
                                          (U (j + 1) : Set (M (N + (j + 1)))),
                                  let S := SmoothSeqSystem.ofPartialDiffeomorphs U
                                    (fun j => chainComp Ψ (N + j) 1)
                                    (fun j => hU0 j 1) hmap0
                                  S.MetricCocycle gInf := by
  classical
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨epsCurv, hepsCurv, hcurv⟩ :=
    exists_eventually_curvDerivNorm_bound_below_controlled_radius hmod
  obtain ⟨epsNC, hepsNC, hnc⟩ := exists_terminalSliceNoncollapsed.{u} hkappa
  refine ⟨min epsCurv epsNC, lt_min hepsCurv hepsNC, ?_⟩
  intro eps heps hle sigma Phi hPhi X F ε hε
  have hsmall : eps ≤ epsCurv := hle.trans (min_le_left _ _)
  obtain ⟨kappa', -, hncX⟩ := hnc Phi hPhi
  have hncX := hncX eps heps (hle.trans (min_le_right _ _)) sigma X
  let Y := X.toFlowSequence.atTime 0
  have hcomplete : SeqMetricComplete Y := by
    refine ⟨fun i => X.complete i 0 ?_⟩
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hjets : ∀ n p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop, HasLocalCurvDerivBound
        (Y.obj i) (Y.obj i).basepoint (finiteOuterRadius F.radius n) p C := by
    intro n p
    have hr : 0 ≤ finiteOuterRadius F.radius n :=
      ((finiteComparisonRadius_pos F.radius_pos n).trans
        (finiteComparisonRadius_lt_outerRadius F.radius_pos n)).le
    obtain ⟨C, hC, hbound⟩ := hcurv eps heps hsmall sigma Phi hPhi X F
      (finiteOuterRadius F.radius n) hr (finiteOuterRadius_lt F.radius_pos n)
    exact ⟨C p, hC p, hbound.mono fun i hi y hy => hi p y hy⟩
  have hinj : ∀ n, ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ i in atTop, ∀ y : (Y.obj i).M,
        riemannianEDistOf (Y.obj i).metric (Y.obj i).basepoint y ≤
          ENNReal.ofReal (finiteComparisonRadius F.radius n) →
            HasInjRadiusAt (Y.obj i) y eta := by
    intro n
    exact F.exists_eventually_hasInjRadiusAt_on_closedBall hncX hPhi
      (finiteComparisonRadius_pos F.radius_pos n).le
      (finiteComparisonRadius_lt F.radius_pos n)
  obtain ⟨σ, hσ, δ, hδ, hsum, Ψ, hbase, hstep, N, D0, hsource, hmaps, Dhi⟩ :=
    exists_subsequence_chain_metric_bounds_below_radius Y hcomplete X.connected
      F.radius_pos ε hε hjets hinj
  let M := fun n => (Y.obj (σ n)).M
  let g : ∀ n, SmoothRiemannianMetric I3 (M n) := fun n => (Y.obj (σ n)).metric
  let K : ∀ n, Set (M n) := fun n =>
    riemannianClosedBallOf (g n) (Y.obj (σ n)).basepoint (finiteStageRadius F.radius n)
  let Ψ' : ∀ j, PartialDiffeomorph I3 I3
      (M (N + j)) (M (N + (j + 1))) ∞ := fun j => Ψ (N + j)
  let U : ∀ j, Opens (M (N + j)) := fun j =>
    ⟨riemannianBallOf (g (N + j)) (Y.obj (σ (N + j))).basepoint
      (finiteStageRadius F.radius (N + j)), isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const⟩
  have hmap : ∀ j,
      (chainComp (Mf := fun j => M (N + j)) Ψ' j 1 :
        M (N + j) → M (N + (j + 1))) '' (U j : Set (M (N + j))) ⊆
          (U (j + 1) : Set (M (N + (j + 1)))) :=
    fun j => (hmaps j 1).image_subset
  have hne : ∀ j, Nonempty (U j) := by
    intro j
    refine ⟨⟨(Y.obj (σ (N + j))).basepoint, ?_⟩⟩
    change riemannianEDistOf (g (N + j)) _ _ < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (finiteStageRadius_pos F.radius_pos (N + j))
  refine ⟨σ, hσ, δ, hδ, hsum, Ψ, hbase, hstep, N, D0, hsource, hmap, Dhi, hne, ?_⟩
  let := hne
  let P : ∀ i, ProperMetricOn (Y.obj i) := fun i =>
    properMetricOn (Y.obj i) (hcomplete.complete i) (X.connected i)
  let : ∀ j, MetricSpace (M (N + j)) := fun j =>
    (P (σ (N + j))).ms.replaceTopology
      (ProperMetricOn.top_eq (Y.obj (σ (N + j))) (P (σ (N + j)))).symm
  have hUK : ∀ j, (U j : Set (M (N + j))) ⊆ K (N + j) := by
    intro j y hy
    change riemannianEDistOf (g (N + j)) (Y.obj (σ (N + j))).basepoint y ≤
      ENNReal.ofReal (finiteStageRadius F.radius (N + j))
    change riemannianEDistOf (g (N + j)) (Y.obj (σ (N + j))).basepoint y <
      ENNReal.ofReal (finiteStageRadius F.radius (N + j)) at hy
    exact hy.le
  obtain ⟨φ, hφ, gInf, hconv, hcompat⟩ :=
    exists_compatible_chain_pullback_metric_limits_on Ψ' (fun j => g (N + j))
      (fun j => K (N + j)) U hne hUK hsource hmap D0 Dhi
  refine ⟨φ, hφ, fun i j hij => hσ (Nat.add_lt_add_left (hφ hij) N),
    gInf, hconv, ?_⟩
  have hsource0 : ∀ j k, (U j : Set (M (N + j))) ⊆
      (chainComp Ψ (N + j) k).source := by
    intro j k
    have hcast : ∀ {a b : ℕ} (h : a = b)
        (G : PartialDiffeomorph I3 I3 (M (N + j)) (M a) ∞),
        (h ▸ G).source = G.source := by
      intro a b h G
      cases h
      rfl
    have hs : (chainComp (Mf := fun j => M (N + j)) Ψ' j k).source =
        (chainComp Ψ (N + j) k).source := by
      dsimp only [Ψ']
      rw [chainComp_shift_eq]
      exact hcast (Nat.add_assoc N j k) _
    rw [← hs]
    exact hsource j k
  have hmap0 : ∀ j,
      (chainComp Ψ (N + j) 1 : M (N + j) → M (N + (j + 1))) ''
        (U j : Set (M (N + j))) ⊆ (U (j + 1) : Set (M (N + (j + 1)))) := by
    intro j
    simpa only [chainComp_one_eq, Ψ'] using hmap j
  refine ⟨hsource0, hmap0, ?_⟩
  apply SmoothSeqSystem.MetricCocycle.ofSucc
  intro j x v w
  have hF : (SmoothSeqSystem.ofPartialDiffeomorphs U
      (fun j => chainComp Ψ (N + j) 1)
      (fun j => hsource0 j 1) hmap0).toSeqSystem.map (Nat.le_succ j) =
        PartialDiffeomorph.opensMap (chainComp Ψ (N + j) 1) (hmap0 j) := by
    unfold SmoothSeqSystem.ofPartialDiffeomorphs
    apply SmoothSeqSystem.ofSucc_map_succ
  rw [hF]
  have hmapsEq : PartialDiffeomorph.opensMap
      (chainComp (Mf := fun j => M (N + j)) Ψ' j 1) (hmap j) =
        PartialDiffeomorph.opensMap (chainComp Ψ (N + j) 1) (hmap0 j) := by
    funext z
    apply Subtype.ext
    change chainComp (Mf := fun j => M (N + j)) Ψ' j 1 z = chainComp Ψ (N + j) 1 z
    rw [chainComp_one_eq, chainComp_one_eq]
  have hh := (hcompat j x v w).symm
  rw [hmapsEq] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
