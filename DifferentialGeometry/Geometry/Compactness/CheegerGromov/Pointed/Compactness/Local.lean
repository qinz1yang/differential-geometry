import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.CompatibleChainLimits
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.Convergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff Topology
open Set TopologicalSpace Filter Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pointed_convergence_within_radius
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) {rho : ℝ} (hrho : 0 < rho)
    (hB : ∀ r : ℝ, 0 < r → r < rho → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (X.obj k).basepoint r)
          ε p Phi (X.obj k).metric (X.obj ℓ).metric)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : ℕ → ℝ,
      (∀ k, 0 < r k ∧ r k < rho) ∧ Tendsto r atTop (nhds rho) ∧
      ∃ L : PointedRiemannianManifold.{u, uE, uH} (I := I),
      ∃ Φ : PointedRiemannianConvergenceMaps (I := I) X L σ,
        ∃ C : PointedRiemannianConverges (I := I) X L σ Φ,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k) ∧
        (∀ k,
          letI : MetricSpace (X.obj (σ k)).M := (P (σ k)).ms
          Φ.target k = Metric.ball (X.obj (σ k)).basepoint (r k)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ∀ x ∈ Φ.source k, ∀ v : TangentSpace I x,
            (1 - ε) * L.metric.inner x v v ≤
              (X.obj (σ k)).metric.inner (Φ.partialDiffeomorph k x)
                (mfderiv I I (Φ.partialDiffeomorph k) x v)
                (mfderiv I I (Φ.partialDiffeomorph k) x v) ∧
            (X.obj (σ k)).metric.inner (Φ.partialDiffeomorph k x)
                (mfderiv I I (Φ.partialDiffeomorph k) x v)
                (mfderiv I I (Φ.partialDiffeomorph k) x v) ≤
              (1 + ε) * L.metric.inner x v v := by
  classical
  obtain ⟨σ, hσ, r, eta, hr, hrT, _hetaT, hdir⟩ :=
    exists_directed_approximate_isometry_subsequence_within_radius (I := I) P hrho hB
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  obtain ⟨Ψ, hbase, hdata⟩ := hdir
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  let : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  let : ∀ j, RiemannianBundle (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  let : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  have hnorm : ∀ j (x : (X.obj (σ j)).M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)) := by
    intro j x v
    with_unfolding_all exact
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (g j) x v)
  have hrmono : StrictMono r := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hs : 1 ≤ Real.sqrt (1 + eta j) := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + eta j by linarith [(hr j).2.2.1])
    exact (show r j ≤ Real.sqrt (1 + eta j) * r j by nlinarith [(hr j).1]).trans_lt
      (hr j).2.2.2.2
  have happrox : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b j) (r j)) δ p
          (chainComp (I := I) Ψ j l) (g j) (g (j + l))) := by
    intro δ hδ hδ1 p
    obtain ⟨J, hJ⟩ := hdata δ hδ hδ1 p
    refine ⟨J, fun j hj l => ?_⟩
    obtain ⟨D⟩ := hJ j hj l
    exact ⟨D.toMetricApproximation hδ hδ1 (min_le_left _ _) le_rfl⟩
  have himages : ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ a : ℕ, 1 ≤ a →
      (chainComp (I := I) Ψ j a : (X.obj (σ j)).M → (X.obj (σ (j + a))).M) ''
        Metric.ball (b j) (r j) ⊆ Metric.ball (b (j + a)) (r (j + a)) := by
    obtain ⟨J, hJ⟩ := hdata (1 / 2) (by norm_num) (by norm_num) 0
    refine ⟨J, fun j hj a ha => ?_⟩
    obtain ⟨D⟩ := hJ j hj a
    have De := D.toZeroOrderMetricApproximation (hr j).2.2.1 (hr j).2.2.2.1
      (min_le_right _ _)
    have hR : Real.sqrt (1 + eta j) * r j < r (j + a) :=
      (hr j).2.2.2.2.trans_le (hrmono.monotone (by omega))
    have Dball : MapMetricApproximationOn (I := I)
        (Metric.closedEBall (b j) (ENNReal.ofReal (r j))) (eta j) 0
        (chainComp (I := I) Ψ j a) (g j) (g (j + a)) := by
      rw [Metric.closedEBall_ofReal (hr j).1.le]
      exact De.forward
    have hsource : Metric.closedEBall (b j) (ENNReal.ofReal (r j)) ⊆
        (chainComp (I := I) Ψ j a).source := by
      rw [Metric.closedEBall_ofReal (hr j).1.le]
      exact De.source_sub
    have himg := MapMetricApproximationOn.image_metric_ball_subset (I := I)
      (chainComp (I := I) Ψ j a) (hnorm j) (hnorm (j + a))
      (hr j).1 le_rfl (hr j).2.2.1.le hR Dball hsource
    simpa only [chainComp_base (I := I) Ψ b hbase j a] using himg
  obtain ⟨j₀, _hj₀, _D0, hU, hmap, _φ, _hφ, gInf, _hconv, hclose, hstep⟩ :=
    exists_compatible_chain_pullback_metric_limits_on_balls (I := I) b Ψ g r
      (fun j => (hr j).1) happrox himages
  let U : ∀ n, Opens (X.obj (σ (j₀ + n))).M := fun n => ballOpen b r (j₀ + n)
  let O : ∀ n, U n := fun n => ⟨b (j₀ + n), Metric.mem_ball_self (hr (j₀ + n)).1⟩
  let : ∀ n, Nonempty (U n) := fun n => ⟨O n⟩
  let : ∀ n, SigmaCompactSpace (U n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
  have hcenter : ∀ n, S.toSeqSystem.map (Nat.zero_le n) (O 0) = O n := by
    intro n
    induction n with
    | zero => exact S.toSeqSystem.map_self 0 (O 0)
    | succ n ih =>
        have hsucc : S.toSeqSystem.map (Nat.le_succ n) =
            PartialDiffeomorph.opensMap (chainComp (I := I) Ψ (j₀ + n) 1) (hmap n) := by
          unfold S chainBallSystem SmoothSeqSystem.ofPartialDiffeomorphs
          apply SmoothSeqSystem.ofSucc_map_succ
        calc
          S.toSeqSystem.map (Nat.zero_le (n + 1)) (O 0) =
              S.toSeqSystem.map (Nat.le_succ n) (S.toSeqSystem.map (Nat.zero_le n) (O 0)) :=
            (S.toSeqSystem.map_map (Nat.zero_le n) (Nat.le_succ n) (O 0)).symm
          _ = S.toSeqSystem.map (Nat.le_succ n) (O n) := by rw [ih]
          _ = O (n + 1) := by
            rw [hsucc]
            apply Subtype.ext
            exact chainComp_base (I := I) Ψ b hbase (j₀ + n) 1
  let hgInf := chain_metric_cocycle (I := I) j₀ U Ψ hU hmap gInf hstep
  let L := pointedDirectLimitOfMetricCocycle S (O 0) gInf hgInf
  let C := chainAmbientPointedRiemannianConvergence (I := I) j₀ U Ψ g hU hmap
    gInf hstep hclose (O 0)
  let σtail := fun n => σ (j₀ + n)
  let XTail := X.subseq σtail
  let bTail : ∀ n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.map (Nat.zero_le n) (O 0) : (X.obj (σtail n)).M)
  let Φr : PointedRiemannianConvergenceMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianConvergenceMaps (I := I)
      (chainAmbientSeq (I := I) j₀ U S (O 0) g) L id
    exact chainAmbientMaps (I := I) j₀ U S (O 0) g gInf hgInf
  have hbase' : ∀ n,
      let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      let : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    with_unfolding_all
      change ((Function.invFun (S.toSeqSystem.incl n) (S.toSeqSystem.incl 0 (O 0)) : U n) :
        (X.obj (σtail n)).M) = (X.obj (σtail n)).basepoint
    have hfirst := congrArg Subtype.val (S.invIncl_incl_le (Nat.zero_le n) (O 0))
    with_unfolding_all rw [hfirst]
    exact congrArg Subtype.val (hcenter n)
  let Cr : PointedRiemannianConverges (I := I) (XTail.repoint bTail) L id Φr := by
    change PointedRiemannianConverges (I := I)
      (chainAmbientSeq (I := I) j₀ U S (O 0) g) L id
      (chainAmbientMaps (I := I) j₀ U S (O 0) g gInf hgInf)
    exact C
  let Cu := (Cr.unrepoint bTail hbase').ofSubseq σtail
  have htail : StrictMono (fun n : ℕ => j₀ + n) := fun a b hab => Nat.add_lt_add_left hab j₀
  refine ⟨σtail, hσ.comp htail, fun n => r (j₀ + n),
    fun n => ⟨(hr (j₀ + n)).1, (hr (j₀ + n)).2.1⟩,
    hrT.comp htail.tendsto_atTop, L, _, Cu, (fun n => ?_), (fun n => ?_), ?_⟩
  · with_unfolding_all rfl
  · change (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl).target =
      Metric.ball (b (j₀ + n)) (r (j₀ + n))
    rfl
  · intro ε hε
    obtain ⟨N, hN⟩ := hclose ε hε 0
    refine ⟨N, fun n hn => ?_⟩
    have hb := chain_ambient_map_inner_bounds (I := I) j₀ U S (O 0) g gInf hgInf n
      (fun x => by
        simpa only [chain_pullback_zero] using hN n hn 0 0 le_rfl x)
    with_unfolding_all exact hb

end DifferentialGeometry.CheegerGromovCompactness
