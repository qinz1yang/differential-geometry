import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalJetBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.IntrinsicSmoothness

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private local instance finiteJetFormNormedAdd :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance finiteJetFormNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private theorem curvatureJetTerm_majorant_congr {C C' : ℕ → ℝ} {N : ℕ}
    (hC : ∀ k, k ≤ N → C k = C' k) (B : IntrinsicJacobiJetAtom → ℝ)
    (t : CurvatureJetTerm) (ht : t.curvOrderAtMost N) :
    t.majorant C B = t.majorant C' B := by
  induction t with
  | zero => rfl
  | atom a => rfl
  | add x y ihx ihy =>
    exact congrArg₂ (· + ·) (ihx ht.1) (ihy ht.2)
  | scale c x ih =>
    exact congrArg (|c| * ·) (ih ht)
  | curv k slots ih =>
    simp only [CurvatureJetTerm.majorant]
    rw [hC k ht.1]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact ih i (ht.2 i)

private theorem jacobiJetBound_congr {C C' : ℕ → ℝ} {N : ℕ}
    (hC : ∀ k, k ≤ N → C k = C' k) (U D : ℝ)
    (n : ℕ) (hn : n ≤ N) : jacobiJetBound C U D n = jacobiJetBound C' U D n := by
  have hzero := hC 0 (Nat.zero_le N)
  have hrate : jacobiJetGrowthRate C U = jacobiJetGrowthRate C' U := by
    simp only [jacobiJetGrowthRate, hzero]
  induction n with
  | zero => simp only [jacobiJetBound, hrate]
  | succ n ih =>
    have hprev := ih (Nat.le_trans (Nat.le_succ n) hn)
    have hforce : jacobiJetForcingBound C U (jacobiJetBound C' U D n) n =
        jacobiJetForcingBound C' U (jacobiJetBound C' U D n) n :=
      curvatureJetTerm_majorant_congr hC _ _
        ((intrinsicJacobiResidualTerm.curvOrderAtMost (n + 1)).mono hn)
    simp only [jacobiJetBound, hprev, hrate, hforce]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem localLaunchSpeed_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p : P.M) (u a : E) {r R U D : Real} :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    Real.sqrt (P.metric.inner p a a) <= D ->
    |r| <= R ->
    0 <= D ->
    Real.sqrt (P.metric.inner p u u) + R * D <= U ->
    Real.sqrt
        (P.metric.inner p (u + r • a) (u + r • a)) <= U := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  intro ha hr hD hu
  have hR : 0 <= R := (abs_nonneg r).trans hr
  calc
    Real.sqrt
        (P.metric.inner p (u + r • a) (u + r • a)) <=
      Real.sqrt (P.metric.inner p u u) +
        Real.sqrt (P.metric.inner p (r • a) (r • a)) :=
      Geometry.Riemannian.sqrt_inner_add_le (I := I) P.metric p u (r • a)
    _ = Real.sqrt (P.metric.inner p u u) +
        |r| * Real.sqrt (P.metric.inner p a a) := by
      congr 1
      exact Geometry.Riemannian.sqrt_inner_smul
        (I := I) P.metric p r (show TangentSpace I p from a)
    _ <= Real.sqrt (P.metric.inner p u u) + R * D := by
      gcongr
    _ <= U := hu

private theorem intrinsicJacobiJets_le_of_curvature_bounds
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p : P.M) {R U D A : Real} (hD : 0 <= D) (hAU : U <= A)
    (N : Nat) (C : Nat -> Real) (hC : forall k : Nat, 0 <= C k)
    (hN : forall k : Nat, k <= N ->
      HasLocalCurvDerivBound (I := I) P p A k (C k))
    (u : E) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : Geometry.Riemannian.IsMetricNorm
        (I := I) (M := P.M) P.metric := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric x v
    let leafNorm : E -> E -> IntrinsicJacobiJetAtom -> Real -> Real -> Real :=
      fun a b atom r t =>
        Real.sqrt
          (P.metric.inner
            (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
            (atom.eval (I := I) P.metric hEnorm p u a b (r, t))
            (atom.eval (I := I) P.metric hEnorm p u a b (r, t)))
    Real.sqrt (P.metric.inner p u u) + R * D <= U ->
    forall n, n <= N -> forall (a b : E),
      Real.sqrt (P.metric.inner p a a) <= D ->
      Real.sqrt (P.metric.inner p b b) <= D ->
      forall r, |r| <= R ->
        (forall k, k <= n ->
          forall t, t ∈ Icc (0 : Real) 1 ->
            leafNorm a b (.bJet k) r t <= jacobiJetBound C U D n) ∧
        (forall k, k <= n ->
          forall t, t ∈ Icc (0 : Real) 1 ->
            leafNorm a b (.bTime k) r t <= jacobiJetBound C U D n) := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let _ : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : Geometry.Riemannian.IsMetricNorm
      (I := I) (M := P.M) P.metric := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v
  dsimp only
  intro hu n hnN
  induction n with
  | zero =>
      intro a b ha hb r hr
      have hU : 0 <= U := by
        have hR : 0 <= R := (abs_nonneg r).trans hr
        exact
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hR hD)).trans hu
      have hspeed :
          Real.sqrt
              (P.metric.inner p (u + r • a) (u + r • a)) <= U :=
        localLaunchSpeed_le (I := I) P p u a ha hr hD hu
      have hpair :=
        intrinsic_jacobi_jet_pair_le_of_local (I := I) P hcomplete hconn p
          (C0 := C 0) (U := U) (eps := 0) (delta := D) (A := A)
          (hC 0) hAU (hN 0 (by omega)) u a b 0 r
          hU hspeed (by norm_num)
          (by
            intro t ht
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b 0 (r, t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b 0 (r, t))) <= 0
            rw [intrinsicJetResidual_zero (I := I) P.metric hEnorm p u a b r t]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= D
            rw [IntrinsicJacobiJetAtom.b_jet_time_zero]
            simpa only [map_zero, Real.sqrt_zero] using hD)
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= D
            rw [IntrinsicJacobiJetAtom.b_time_zero]
            let u0 : TangentSpace I p :=
              show TangentSpace I p from u + r • a + (0 : Real) • b
            change Real.sqrt
              (P.metric.inner
                (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0) b b) <= D
            rw [intrinsicGeodesic_zero
              (I := I) P.metric hEnorm p u0]
            exact hb)
      have hrate : 0 <= jacobiJetGrowthRate C U := (jacobi_jet_growth_rate_pos C U).le
      constructor
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound D (jacobiJetGrowthRate C U) 0 t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b 0 (r, t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b 0 (r, t))) <=
                gronwallBound D (jacobiJetGrowthRate C U) 0 t
            simpa only [jacobiJetGrowthRate] using hpair.1 t ht
          _ <= gronwallBound D (jacobiJetGrowthRate C U) 0 1 :=
            gronwallBound_mono hD (by norm_num) hrate ht.2
          _ = jacobiJetBound C U D 0 := rfl
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound D (jacobiJetGrowthRate C U) 0 t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b 0 (s, t)) r t)
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b 0 (s, t)) r t)) <=
                gronwallBound D (jacobiJetGrowthRate C U) 0 t
            simpa only [jacobiJetGrowthRate] using hpair.2 t ht
          _ <= gronwallBound D (jacobiJetGrowthRate C U) 0 1 :=
            gronwallBound_mono hD (by norm_num) hrate ht.2
          _ = jacobiJetBound C U D 0 := rfl
  | succ n ih =>
      intro a b ha hb r hr
      have hU : 0 <= U := by
        have hR : 0 <= R := (abs_nonneg r).trans hr
        exact
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hR hD)).trans hu
      have hspeed :
          Real.sqrt
              (P.metric.inner p (u + r • a) (u + r • a)) <= U :=
        localLaunchSpeed_le (I := I) P p u a ha hr hD hu
      have hprev := ih (by omega) a b ha hb r hr
      have hself := ih (by omega) a a ha ha r hr
      have hcap : 0 <= jacobiJetBound C U D n :=
        jacobi_jet_bound_nonneg C hD n
      have heps : 0 <= jacobiJetForcingBound C U (jacobiJetBound C U D n) n :=
        jacobi_jet_forcing_bound_nonneg C hC hU hcap n
      have hres : forall t, t ∈ Ico (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))) <=
            jacobiJetForcingBound C U (jacobiJetBound C U D n) n := by
        intro t ht
        rw [show intrinsicJetResidual
              (I := I) P.metric hEnorm p u a b (n + 1) (r, t) =
            (intrinsicJacobiResidualTerm (n + 1)).eval
              (I := I) P.metric hEnorm p u a b (r, t) by
          exact congrFun
            (congrFun
              (intrinsic_jacobi_residual_term_eval
                (I := I) P.metric hEnorm p u a b (n + 1)) r) t]
        have hqt : riemannianEDistOf (I := I) P.metric p
            (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t)) <=
              ENNReal.ofReal A := by
          have ht0 : (0 : Real) <= t := ht.1
          have ht1 : t <= 1 := ht.2.le
          have hlaunch :
              intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t) =
                intrinsicGeodesic (I := I) P.metric hEnorm p (u + r • a) t := by
            simp only [intrinsicLaunch3, zero_smul, add_zero]
          rw [hlaunch]
          exact (intrinsicGeodesic_riemannianEDistOf_le (I := I) P hcomplete hconn
            hEnorm p (u + r • a) hspeed ht0 ht1).trans
            (ENNReal.ofReal_le_ofReal hAU)
        apply CurvatureJetTerm.eval_le_at_local_order
          (I := I) P.metric hEnorm p u a b N C hC
          (jacobiJetAtomBound U (jacobiJetBound C U D n))
          (fun atom => atom.atMost n) (A := A)
          (fun k x v hk hx =>
            HasCurvDerivBound.curv_op_n_le_local
              (I := I) P p (hN k hk) x hx v)
          (r, t) hqt
        · intro atom hatom
          have hbaseSelf :
              intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t) =
                intrinsicLaunch3 (I := I) P.metric hEnorm p u a a ((r, 0), t) := by
            simp only [intrinsicLaunch3, zero_smul, add_zero]
          cases atom with
          | pathT =>
              let u0 : TangentSpace I p :=
                show TangentSpace I p from
                  u + r • a + (0 : Real) • b
              have hspeedSq :=
                intrinsicGeodesic_speedSq_eq
                  (I := I) P.metric hEnorm p u0 t
              change Real.sqrt
                  (P.metric.inner
                    (intrinsicLaunch3
                      (I := I) P.metric hEnorm p u a b ((r, 0), t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))) <= U
              rw [show P.metric.inner
                    (intrinsicLaunch3
                      (I := I) P.metric hEnorm p u a b ((r, 0), t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t)) =
                  P.metric.inner p (u + r • a) (u + r • a) by
                simp only [IntrinsicJacobiJetAtom.eval, intrinsicLaunch3, varSnd]
                change P.metric.inner
                    (intrinsicGeodesic (I := I) P.metric hEnorm p u0 t)
                    (mfderiv 𝓘(Real, Real) I
                      (fun v => intrinsicGeodesic
                        (I := I) P.metric hEnorm p u0 v) t 1)
                    (mfderiv 𝓘(Real, Real) I
                      (fun v => intrinsicGeodesic
                        (I := I) P.metric hEnorm p u0 v) t 1) =
                  P.metric.inner p (u + r • a) (u + r • a)
                have hfun :
                    (fun v => intrinsicGeodesic
                      (I := I) P.metric hEnorm p u0 v) =
                      intrinsicGeodesic (I := I) P.metric hEnorm p u0 := rfl
                rw [hfun, hspeedSq]
                simp only [u0, zero_smul, add_zero]]
              exact hspeed
          | pathDt =>
              rw [IntrinsicJacobiJetAtom.path_dt_zero]
              simpa only [jacobiJetAtomBound, map_zero, Real.sqrt_zero] using
                (le_refl (0 : Real))
          | aJet k =>
              rw [IntrinsicJacobiJetAtom.a_jet_eq_self]
              rw [hbaseSelf]
              simpa only [jacobiJetAtomBound] using hself.1 k hatom t ⟨ht.1, ht.2.le⟩
          | aTime k =>
              rw [IntrinsicJacobiJetAtom.a_time_eq_self]
              rw [hbaseSelf]
              simpa only [jacobiJetAtomBound] using hself.2 k hatom t ⟨ht.1, ht.2.le⟩
          | bJet k =>
              simpa only [jacobiJetAtomBound] using hprev.1 k hatom t ⟨ht.1, ht.2.le⟩
          | bTime k =>
              simpa only [jacobiJetAtomBound] using hprev.2 k hatom t ⟨ht.1, ht.2.le⟩
        · exact (intrinsicJacobiResidualTerm.curvOrderAtMost (n + 1)).mono (by omega)
        · exact intrinsic_jacobi_residual_term_all_atoms n
      have hpair :=
        intrinsic_jacobi_jet_pair_le_of_local (I := I) P hcomplete hconn p
          (C0 := C 0) (U := U) (A := A)
          (eps := jacobiJetForcingBound C U (jacobiJetBound C U D n) n) (delta := 0)
          (hC 0) hAU (hN 0 (by omega)) u a b (n + 1) r
          hU hspeed heps hres
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= 0
            rw [IntrinsicJacobiJetAtom.b_jet_time_zero]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= 0
            rw [IntrinsicJacobiJetAtom.b_time_succ_time_zero]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
      have hrate : 0 <= jacobiJetGrowthRate C U := (jacobi_jet_growth_rate_pos C U).le
      have hnewPos : forall t, t ∈ Icc (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
            jacobiJetBound C U D (n + 1) := by
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound 0 (jacobiJetGrowthRate C U)
                (jacobiJetForcingBound C U (jacobiJetBound C U D n) n) t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))) <=
                gronwallBound 0 (jacobiJetGrowthRate C U)
                  (jacobiJetForcingBound C U (jacobiJetBound C U D n) n) t
            simpa only [jacobiJetGrowthRate] using hpair.1 t ht
          _ <= gronwallBound 0 (jacobiJetGrowthRate C U)
              (jacobiJetForcingBound C U (jacobiJetBound C U D n) n) 1 :=
            gronwallBound_mono (by norm_num) heps hrate ht.2
          _ <= jacobiJetBound C U D (n + 1) :=
            jacobi_jet_bound_step_le C U D n
      have hnewTime : forall t, t ∈ Icc (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
            jacobiJetBound C U D (n + 1) := by
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound 0 (jacobiJetGrowthRate C U)
                (jacobiJetForcingBound C U (jacobiJetBound C U D n) n) t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b (n + 1) (s, t)) r t)
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b (n + 1) (s, t)) r t)) <=
                gronwallBound 0 (jacobiJetGrowthRate C U)
                  (jacobiJetForcingBound C U (jacobiJetBound C U D n) n) t
            simpa only [jacobiJetGrowthRate] using hpair.2 t ht
          _ <= gronwallBound 0 (jacobiJetGrowthRate C U)
              (jacobiJetForcingBound C U (jacobiJetBound C U D n) n) 1 :=
            gronwallBound_mono (by norm_num) heps hrate ht.2
          _ <= jacobiJetBound C U D (n + 1) :=
            jacobi_jet_bound_step_le C U D n
      constructor
      · intro k hk t ht
        rcases Nat.lt_or_eq_of_le hk with hklt | rfl
        · exact (hprev.1 k (Nat.lt_succ_iff.mp hklt) t ht).trans
            (jacobi_jet_bound_le_succ C U D n)
        · exact hnewPos t ht
      · intro k hk t ht
        rcases Nat.lt_or_eq_of_le hk with hklt | rfl
        · exact (hprev.2 k (Nat.lt_succ_iff.mp hklt) t ht).trans
            (jacobi_jet_bound_le_succ C U D n)
        · exact hnewTime t ht
private theorem intrinsicMetricJet_le_of_curvature_bounds
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p : P.M) {A : Real}
    (N : Nat) (C : Nat -> Real) (hC : forall k : Nat, 0 <= C k)
    (hN : forall k : Nat, k <= N ->
      HasLocalCurvDerivBound (I := I) P p A k (C k))
    (u a b : E) (n : Nat) {U D : Real} (hD : 0 ≤ D) (hAU : U ≤ A) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric x v
    n ≤ N →
    Real.sqrt (P.metric.inner p u u) ≤ U →
    Real.sqrt (P.metric.inner p a a) ≤ D →
    Real.sqrt (P.metric.inner p b b) ≤ D →
    |intrinsicMetricJet (I := I) P.metric hEnorm p u a b n 0| ≤
      2 ^ n * jacobiJetBound C U D n ^ 2 := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let _ : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v
  dsimp only
  intro hnN hu ha hb
  have hjets :=
    intrinsicJacobiJets_le_of_curvature_bounds (I := I) P hcomplete hconn p
      (R := 0) (U := U) (D := D) (A := A) hD hAU N C hC hN u
      (by simpa using hu)
      n hnN a b ha hb 0 (by simp)
  apply intrinsic_metric_jet_abs_le (I := I) P.metric hEnorm p u a b n 0
    (jacobiJetBound C U D n) (jacobi_jet_bound_nonneg C hD n)
  intro k hk
  simpa only [IntrinsicJacobiJetAtom.eval, intrinsicLaunchJet] using
    hjets.1 k hk 1 (by constructor <;> norm_num)

theorem intrinsicFrameMetric_iteratedFDeriv_norm_le_of_curvature_bounds
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p : P.M) {A : Real}
    (N : Nat) (C : Nat -> Real)
    (hN : forall k : Nat, k <= N ->
      HasLocalCurvDerivBound (I := I) P p A k (C k))
    (z : E) (n : Nat) (U : Real) (hAU : U ≤ A)
    (hzU : ‖z‖ ≤ U) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric x v
    n ≤ N →
      ‖iteratedFDeriv Real n
          (intrinsicFrameMetric (I := I) P.metric hEnorm p) z‖ ≤
        ContinuousMultilinearMap.polarConst n *
          (2 * (2 ^ n * jacobiJetBound C U 1 n ^ 2)) := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let _ : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v
  dsimp only
  intro hnN
  have hsmooth : ContDiffAt Real ∞
      (intrinsicFrameMetric (I := I) P.metric hEnorm p) z :=
    (contDiff_intrinsicFrameMetric (I := I) P.metric hEnorm p).contDiffAt
  have hC (k : ℕ) (hk : k ≤ N) : 0 ≤ C k :=
    (show 0 ≤ curvDerivNorm (I := I) k P.metric p from Real.sqrt_nonneg _).trans
      (hN k hk p (by simp only [riemannianEDistOf_self]; exact bot_le))
  let C' : ℕ → ℝ := fun k => max 0 (C k)
  have hC' (k : ℕ) : 0 ≤ C' k := le_max_left _ _
  have hCeq (k : ℕ) (hk : k ≤ N) : C' k = C k := max_eq_right (hC k hk)
  have hN' : ∀ k, k ≤ N → HasLocalCurvDerivBound (I := I) P p A k (C' k) := by
    intro k hk
    rw [hCeq k hk]
    exact hN k hk
  let A :=
    iteratedFDeriv Real n
      (intrinsicFrameMetric (I := I) P.metric hEnorm p) z
  let S : Real := 2 ^ n * jacobiJetBound C U 1 n ^ 2
  have hS : 0 ≤ S := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have htwoS : 0 ≤ 2 * S := mul_nonneg (by norm_num) hS
  have hAsymm : A.IsSymmetric := by
    intro σ
    exact iterFDeriv_perm hsmooth σ
  have hdiag :
      ∀ a : E, ‖a‖ ≤ 1 → ‖A (fun _ => a)‖ ≤ 2 * S := by
    intro a ha
    let B : E →L[Real] E →L[Real] Real := A (fun _ => a)
    have hBsymm : ∀ v w : E, B v w = B w v := by
      intro v w
      have hmetric :
          (fun y : E =>
              intrinsicFrameMetric (I := I) P.metric hEnorm p y v w) =
            fun y : E =>
              intrinsicFrameMetric (I := I) P.metric hEnorm p y w v := by
        funext y
        rw [intrinsicFrameMetric_apply, intrinsicFrameMetric_apply]
        exact P.metric.symm _ _ _
      calc
        B v w =
            iteratedFDeriv Real n
              (fun y : E =>
                intrinsicFrameMetric (I := I) P.metric hEnorm p y v w) z
              (fun _ => a) := by
          exact (iterFDeriv_apply₂ hsmooth n v w (fun _ => a)).symm
        _ = iteratedFDeriv Real n
              (fun y : E =>
                intrinsicFrameMetric (I := I) P.metric hEnorm p y w v) z
              (fun _ => a) := by rw [hmetric]
        _ = B w v :=
          iterFDeriv_apply₂ hsmooth n w v (fun _ => a)
    have hBdiag : ∀ b : E, ‖b‖ ≤ 1 → |B b b| ≤ S := by
      intro b hb
      have hzu :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p z)
                (normalFrame (I := I) P.metric p z)) ≤ U := by
        simpa only [normalFrame_sqrt] using hzU
      have hau :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p a)
                (normalFrame (I := I) P.metric p a)) ≤ 1 := by
        simpa only [normalFrame_sqrt] using ha
      have hbu :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p b)
                (normalFrame (I := I) P.metric p b)) ≤ 1 := by
        simpa only [normalFrame_sqrt] using hb
      have hjet :=
        intrinsicMetricJet_le_of_curvature_bounds (I := I) P hcomplete hconn p N C' hC' hN'
          (normalFrame (I := I) P.metric p z)
          (normalFrame (I := I) P.metric p a)
          (normalFrame (I := I) P.metric p b) n
          (U := U) (D := 1) (by norm_num) hAU hnN hzu hau hbu
      rw [jacobiJetBound_congr hCeq U 1 n hnN] at hjet
      change
        |iteratedFDeriv Real n
            (intrinsicFrameMetric (I := I) P.metric hEnorm p) z
            (fun _ => a) b b| ≤ S
      rw [intrinsicMetric_diag_jet (I := I) P.metric hEnorm p z a b n
        hsmooth]
      exact hjet
    have hB :=
      ContinuousLinearMap.opNorm_le_diag2 B hBsymm hS hBdiag
    simpa only [B] using hB
  have hbound :=
    ContinuousMultilinearMap.opNorm_le_diag_unit
      hAsymm htwoS hdiag
  simpa only [A, S] using hbound

end DifferentialGeometry.CheegerGromovCompactness
