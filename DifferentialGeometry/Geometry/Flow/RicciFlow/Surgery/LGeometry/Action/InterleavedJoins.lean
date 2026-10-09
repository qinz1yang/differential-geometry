import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.InterleavedJointAction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u v z uSmoothJoin uPositiveStages uStageSmooth

def interleavedJoinEquiv (N : ℕ) :
    (Fin N ⊕ (Fin N ⊕ Fin 1)) ≃ Fin (2 * N + 1) := by
  let f : (Fin N ⊕ (Fin N ⊕ Fin 1)) → Fin (2 * N + 1)
    | .inl k => ⟨2 * k.val, by omega⟩
    | .inr (.inl k) => ⟨2 * k.val + 1, by omega⟩
    | .inr (.inr _) => ⟨2 * N, by omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Fin.val h
    rcases x with k | (k | k) <;> rcases y with l | (l | l)
    all_goals simp only [f] at hv
    all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals first | apply Fin.ext; omega | exact Subsingleton.elim _ _ | omega
  · intro i
    by_cases hi : i.val = 2 * N
    · exact ⟨.inr (.inr 0), Fin.ext hi.symm⟩
    · rcases Nat.mod_two_eq_zero_or_one i.val with h | h
      · refine ⟨.inl ⟨i.val / 2, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega
      · refine ⟨.inr (.inl ⟨i.val / 2, by omega⟩), ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega

theorem interleavedJoinEquiv_values (N : ℕ) :
    let L : (Fin N ⊕ (Fin N ⊕ Fin 1)) → (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) :=
      Sum.elim (fun k => .inl k.castSucc)
        (Sum.elim (fun k => .inr (.inl k)) (fun _ => .inl (Fin.last N)));
    let R : (Fin N ⊕ (Fin N ⊕ Fin 1)) → (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) :=
      Sum.elim (fun k => .inr (.inl k))
        (Sum.elim (fun k => .inl k.succ) (fun k => .inr (.inr k)));
    (∀ k : Fin N, interleavedJoinEquiv N (.inl k) = ⟨2 * k.val, by omega⟩) ∧
    (∀ k : Fin N, interleavedJoinEquiv N (.inr (.inl k)) = ⟨2 * k.val + 1, by omega⟩) ∧
    interleavedJoinEquiv N (.inr (.inr 0)) = Fin.last (2 * N) ∧
    (∀ k, interleavedPieceEquiv N (L k) = (interleavedJoinEquiv N k).castSucc) ∧
    (∀ k, interleavedPieceEquiv N (R k) = (interleavedJoinEquiv N k).succ) := by
  intro L R
  refine ⟨fun _ => rfl, fun _ => rfl, rfl, ?_, ?_⟩
  · intro k
    rcases k with k | (k | k) <;> rfl
  · intro k
    rcases k with k | (k | k)
    · rfl
    · apply Fin.ext
      change 2 * (k.val + 1) = 2 * k.val + 1 + 1
      omega
    · rfl

private theorem exists_stage_identity_join
    (H : ObservedHistory.{u}) (j k : Fin (H.eventCount + 1)) (hjk : j = k)
    {DJ DK : RealTimeInterval}
    (SJ : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) DJ)
    (SK : SolutionOn (I := ThreeModel) (M := (H.stage k).Carrier) DK)
    (hJ : ∀ t, SJ.base.metric t = H.stageMetric j t)
    (hK : ∀ t, SK.base.metric t = H.stageMetric k t)
    (alpha : ℝ → (H.stage j).Carrier) (beta : ℝ → (H.stage k).Carrier)
    (T r : ℝ) (hcurve : (hjk ▸ alpha) =ᶠ[𝓝 r] beta) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel (H.stage j).Carrier (H.stage k).Carrier ∞,
      F.source = univ ∧ (∀ x, HEq (F x) x) ∧
      alpha r ∈ F.source ∧ F (alpha r) = beta r ∧ F ∘ alpha =ᶠ[𝓝 r] beta ∧
      (∀ x ∈ F.source, ∀ V W : TangentSpace ThreeModel x,
        (SJ.base.metric (T - r ^ 2)).inner x V W =
          (SK.base.metric (T - r ^ 2)).inner (F x)
            (mfderiv ThreeModel ThreeModel (F : (H.stage j).Carrier → (H.stage k).Carrier) x V)
            (mfderiv ThreeModel ThreeModel (F : (H.stage j).Carrier → (H.stage k).Carrier) x W)) ∧
      (mfderiv ThreeModel ThreeModel (F : (H.stage j).Carrier → (H.stage k).Carrier) (alpha r)
        (lVelocity (I := ThreeModel) alpha r) : ThreeSpace) = lVelocity (I := ThreeModel) beta r ∧
      SJ.scalar (T - r ^ 2) (alpha r) = SK.scalar (T - r ^ 2) (beta r) ∧
      lRegularizedLagrangian SJ T alpha r = lRegularizedLagrangian SK T beta r := by
  subst k
  change alpha =ᶠ[𝓝 r] beta at hcurve
  let F := (Diffeomorph.refl ThreeModel (H.stage j).Carrier ∞).toPartialDiffeomorph
  have hcoe : (F : (H.stage j).Carrier → (H.stage j).Carrier) = id := rfl
  have hmetric (t : ℝ) : SJ.base.metric t = SK.base.metric t := (hJ t).trans (hK t).symm
  have hvel : lVelocity (I := ThreeModel) alpha r = lVelocity (I := ThreeModel) beta r := by
    unfold lVelocity
    rw [hcurve.mfderiv_eq]
    rfl
  refine ⟨F, rfl, fun _ => HEq.rfl, mem_univ _, hcurve.self_of_nhds, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hcoe, Function.id_comp] using hcurve
  · intro x _ V W
    rw [hcoe, mfderiv_id]
    simpa only [ContinuousLinearMap.id_apply, id_eq] using
      congrArg (fun g => g.inner x V W) (hmetric (T - r ^ 2))
  · rw [hcoe, mfderiv_id]
    exact hvel
  · change metricScalarAt (SJ.base.metric (T - r ^ 2)) (alpha r) =
      metricScalarAt (SK.base.metric (T - r ^ 2)) (beta r)
    rw [hmetric, hcurve.self_of_nhds]
  · simp only [lRegularizedLagrangian, SolutionOn.scalar, SolutionFamily.scalar,
      hmetric, hvel, hcurve.self_of_nhds]
    exact congrArg (fun x =>
      (1 / 2 : ℝ) * (SK.base.metric (T - r ^ 2)).inner x
        (lVelocity (I := ThreeModel) beta r) (lVelocity (I := ThreeModel) beta r) +
      2 * r ^ 2 * metricScalarAt (SK.base.metric (T - r ^ 2)) (beta r)) hcurve.self_of_nhds

theorem exists_interleaved_actual_joins
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) {N : ℕ}
    (j : Fin (N + 1) ≃ H.StageInterval first last)
    (e : Fin N ≃ {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last})
    (hfirst : (j (Fin.last N)).val = first)
    (W : (k : Fin N) → TopologicalSpace.Opens (H.event (e k).val).incoming.terminalRegularOpen)
    (DO : Fin (N + 1) → RealTimeInterval) (DS : Fin N → RealTimeInterval)
    (DT : RealTimeInterval)
    (SO : (k : Fin (N + 1)) →
      SolutionOn (I := ThreeModel) (M := (H.stage (j k).val).Carrier) (DO k))
    (SS : (k : Fin N) → SolutionOn (I := ThreeModel) (M := W k) (DS k))
    (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
    (hmetricO : ∀ t, (SO (Fin.last N)).base.metric t = H.stageMetric (j (Fin.last N)).val t)
    (hmetricT : ∀ t, ST.base.metric t = H.stageMetric first t)
    (alphaO : (k : Fin (N + 1)) → ℝ → (H.stage (j k).val).Carrier)
    (alphaS : (k : Fin N) → ℝ → W k) (alphaT : ℝ → (H.stage first).Carrier)
    (T : ℝ) (s : Fin (2 * N + 3) → ℝ)
    (Fn : (k : Fin N) → PartialDiffeomorph ThreeModel ThreeModel (W k)
      (H.stage (j k.castSucc).val).Carrier ∞)
    (Fo : (k : Fin N) → PartialDiffeomorph ThreeModel ThreeModel (W k)
      (H.stage (j k.succ).val).Carrier ∞)
    (newProjection : (k : Fin N) → W k → (H.stage (j k.castSucc).val).Carrier)
    (oldProjection : (k : Fin N) → W k → (H.stage (j k.succ).val).Carrier)
    (hnewMap : ∀ k, EqOn (newProjection k) (Fn k) (Fn k).source)
    (holdMap : ∀ k, EqOn (oldProjection k) (Fo k) (Fo k).source)
    (htail : (hfirst ▸ alphaO (Fin.last N)) =ᶠ[𝓝 (s ⟨2 * N + 1, by omega⟩)] alphaT)
    (hnew : ∀ k : Fin N,
      let c := s ⟨2 * k.val + 1, by omega⟩;
      (alphaO k.castSucc) c ∈ (Fn k).symm.source ∧
      ((Fn k).symm : _ → _) ∘ (alphaO k.castSucc) =ᶠ[𝓝 c] (alphaS k) ∧
      (∀ x ∈ (Fn k).symm.source, ∀ V W : TangentSpace ThreeModel x,
        ((SO k.castSucc).base.metric (T - c ^ 2)).inner x V W =
          ((SS k).base.metric (T - c ^ 2)).inner ((Fn k).symm x)
            (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) ((alphaO k.castSucc) c)
        (lVelocity (I := ThreeModel) (alphaO k.castSucc) c) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alphaS k) c ∧
      (SO k.castSucc).scalar (T - c ^ 2) ((alphaO k.castSucc) c) = (SS k).scalar (T - c ^ 2) ((alphaS k) c) ∧
      lRegularizedLagrangian (SO k.castSucc) T (alphaO k.castSucc) c = lRegularizedLagrangian (SS k) T (alphaS k) c)
    (hold : ∀ k : Fin N,
      let d := s ⟨2 * k.val + 2, by omega⟩;
      (alphaS k) d ∈ (Fo k).source ∧
      ((Fo k) : _ → _) ∘ (alphaS k) =ᶠ[𝓝 d] (alphaO k.succ) ∧
      (∀ x ∈ (Fo k).source, ∀ V W : TangentSpace ThreeModel x,
        ((SS k).base.metric (T - d ^ 2)).inner x V W =
          ((SO k.succ).base.metric (T - d ^ 2)).inner ((Fo k) x)
            (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) ((alphaS k) d)
        (lVelocity (I := ThreeModel) (alphaS k) d) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alphaO k.succ) d ∧
      (SS k).scalar (T - d ^ 2) ((alphaS k) d) = (SO k.succ).scalar (T - d ^ 2) ((alphaO k.succ) d) ∧
      lRegularizedLagrangian (SS k) T (alphaS k) d = lRegularizedLagrangian (SO k.succ) T (alphaO k.succ) d) :
    let K := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1);
    let M0 : K → Type u := ActualPieceCarrier H first last j e W;
    let D0 : K → RealTimeInterval := Sum.elim DO (Sum.elim DS (fun _ => DT));
    let S0 : (k : K) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
      Sum.rec (fun k => SO k) (Sum.rec (fun k => SS k) (fun _ => ST));
    let alpha0 : (k : K) → ℝ → M0 k :=
      Sum.rec (fun k => alphaO k) (Sum.rec (fun k => alphaS k) (fun _ => alphaT));
    let q := interleavedPieceEquiv N;
    let z := interleavedJoinEquiv N;
    let M : Fin (2 * N + 2) → Type u := fun i => M0 (q.symm i);
    let D : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
      fun i => S0 (q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (q.symm i);
    ∃ F : (i : Fin (2 * N + 1)) →
      PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞,
      (∀ i : Fin (2 * N + 1),
        let r := s i.castSucc.succ;
        (alpha i.castSucc) r ∈ (F i).source ∧
      (F i) ((alpha i.castSucc) r) = (alpha i.succ) r ∧
      ((F i) : _ → _) ∘ (alpha i.castSucc) =ᶠ[𝓝 r] (alpha i.succ) ∧
      (∀ x ∈ (F i).source, ∀ V W : TangentSpace ThreeModel x,
        ((S i.castSucc).base.metric (T - r ^ 2)).inner x V W =
          ((S i.succ).base.metric (T - r ^ 2)).inner ((F i) x)
            (mfderiv ThreeModel ThreeModel ((F i) : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((F i) : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((F i) : _ → _) ((alpha i.castSucc) r)
        (lVelocity (I := ThreeModel) (alpha i.castSucc) r) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha i.succ) r ∧
      (S i.castSucc).scalar (T - r ^ 2) ((alpha i.castSucc) r) = (S i.succ).scalar (T - r ^ 2) ((alpha i.succ) r) ∧
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) r = lRegularizedLagrangian (S i.succ) T (alpha i.succ) r) ∧
      (∀ k, HEq (F (z (.inl k))) (Fn k).symm) ∧
      (∀ k, HEq (F (z (.inr (.inl k)))) (Fo k)) ∧
      (∃ FT : PartialDiffeomorph ThreeModel ThreeModel
          (H.stage (j (Fin.last N)).val).Carrier (H.stage first).Carrier ∞,
        FT.source = univ ∧ (∀ x, HEq (FT x) x) ∧ HEq (F (Fin.last (2 * N))) FT) ∧
      (∀ f : (i : Fin (2 * N + 2)) → ℝ → ℝ → M i,
        let g := (Equiv.piCongrLeft' (fun k => ℝ → ℝ → M0 k) q).symm f;
        ∀ epsilon : ℝ,
        (∀ i : Fin (2 * N + 1),
          f i.castSucc epsilon (s i.castSucc.succ) ∈ (F i).source ∧
          F i (f i.castSucc epsilon (s i.castSucc.succ)) =
            f i.succ epsilon (s i.castSucc.succ)) →
        (∀ k : Fin N,
          newProjection k (g (.inr (.inl k)) epsilon (s ⟨2 * k.val + 1, by omega⟩)) =
            g (.inl k.castSucc) epsilon (s ⟨2 * k.val + 1, by omega⟩)) ∧
        (∀ k : Fin N,
          oldProjection k (g (.inr (.inl k)) epsilon (s ⟨2 * k.val + 2, by omega⟩)) =
            g (.inl k.succ) epsilon (s ⟨2 * k.val + 2, by omega⟩)) ∧
        HEq (g (.inl (Fin.last N)) epsilon (s ⟨2 * N + 1, by omega⟩))
          (g (.inr (.inr 0)) epsilon (s ⟨2 * N + 1, by omega⟩))) := by
  intro K M0 D0 S0 alpha0 q z M D S alpha
  let J := Fin N ⊕ (Fin N ⊕ Fin 1)
  let b := s ⟨2 * N + 1, by omega⟩
  obtain ⟨FT, hFTsource, hFTid, hFTmem, hFTpoint, hFTcenter, hFTmetric,
      hFTvelocity, hFTscalar, hFTlag⟩ :=
    H.exists_stage_identity_join (j (Fin.last N)).val first hfirst
      (SO (Fin.last N)) ST hmetricO hmetricT (alphaO (Fin.last N)) alphaT T b htail
  let L : J → K := Sum.elim (fun k => .inl k.castSucc)
    (Sum.elim (fun k => .inr (.inl k)) (fun _ => .inl (Fin.last N)))
  let R : J → K := Sum.elim (fun k => .inr (.inl k))
    (Sum.elim (fun k => .inl k.succ) (fun k => .inr (.inr k)))
  let F0 : (k : J) → PartialDiffeomorph ThreeModel ThreeModel (M0 (L k)) (M0 (R k)) ∞ :=
    Sum.rec (fun k => (Fn k).symm) (Sum.rec (fun k => Fo k) (fun _ => FT))
  let rho (k : J) := s (z k).castSucc.succ
  have hL (k : J) : q (L k) = (z k).castSucc := (interleavedJoinEquiv_values N).2.2.2.1 k
  have hR (k : J) : q (R k) = (z k).succ := (interleavedJoinEquiv_values N).2.2.2.2 k
  have hleft (i : Fin (2 * N + 1)) : q.symm i.castSucc = L (z.symm i) := by
    apply q.injective
    simp only [q.apply_symm_apply, hL, z.apply_symm_apply]
  have hright (i : Fin (2 * N + 1)) : q.symm i.succ = R (z.symm i) := by
    apply q.injective
    simp only [q.apply_symm_apply, hR, z.apply_symm_apply]
  have h0 (k : J) :
      (alpha0 (L k)) (rho k) ∈ (F0 k).source ∧
      ((F0 k) : _ → _) ∘ (alpha0 (L k)) =ᶠ[𝓝 (rho k)] (alpha0 (R k)) ∧
      (∀ x ∈ (F0 k).source, ∀ V W : TangentSpace ThreeModel x,
        ((S0 (L k)).base.metric (T - (rho k) ^ 2)).inner x V W =
          ((S0 (R k)).base.metric (T - (rho k) ^ 2)).inner ((F0 k) x)
            (mfderiv ThreeModel ThreeModel ((F0 k) : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((F0 k) : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((F0 k) : _ → _) ((alpha0 (L k)) (rho k))
        (lVelocity (I := ThreeModel) (alpha0 (L k)) (rho k)) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha0 (R k)) (rho k) ∧
      (S0 (L k)).scalar (T - (rho k) ^ 2) ((alpha0 (L k)) (rho k)) = (S0 (R k)).scalar (T - (rho k) ^ 2) ((alpha0 (R k)) (rho k)) ∧
      lRegularizedLagrangian (S0 (L k)) T (alpha0 (L k)) (rho k) = lRegularizedLagrangian (S0 (R k)) T (alpha0 (R k)) (rho k) := by
    rcases k with k | (k | k)
    · exact hnew k
    · exact hold k
    · fin_cases k
      exact ⟨hFTmem, hFTcenter, hFTmetric, hFTvelocity, hFTscalar, hFTlag⟩
  have hex (i : Fin (2 * N + 1)) :
      ∃ Fi : PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞,
        HEq Fi (F0 (z.symm i)) ∧
        (let r := s i.castSucc.succ;
          (alpha i.castSucc) r ∈ Fi.source ∧
      Fi ((alpha i.castSucc) r) = (alpha i.succ) r ∧
      (Fi : _ → _) ∘ (alpha i.castSucc) =ᶠ[𝓝 r] (alpha i.succ) ∧
      (∀ x ∈ Fi.source, ∀ V W : TangentSpace ThreeModel x,
        ((S i.castSucc).base.metric (T - r ^ 2)).inner x V W =
          ((S i.succ).base.metric (T - r ^ 2)).inner (Fi x)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x V)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel (Fi : _ → _) ((alpha i.castSucc) r)
        (lVelocity (I := ThreeModel) (alpha i.castSucc) r) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha i.succ) r ∧
      (S i.castSucc).scalar (T - r ^ 2) ((alpha i.castSucc) r) = (S i.succ).scalar (T - r ^ 2) ((alpha i.succ) r) ∧
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) r = lRegularizedLagrangian (S i.succ) T (alpha i.succ) r) := by
    have htransport (kl kr : K) (hl : kl = L (z.symm i)) (hr : kr = R (z.symm i)) :
      ∃ Fi : PartialDiffeomorph ThreeModel ThreeModel (M0 kl) (M0 kr) ∞,
        HEq Fi (F0 (z.symm i)) ∧
        (let r := s i.castSucc.succ;
          (alpha0 kl) r ∈ Fi.source ∧
      Fi ((alpha0 kl) r) = (alpha0 kr) r ∧
      (Fi : _ → _) ∘ (alpha0 kl) =ᶠ[𝓝 r] (alpha0 kr) ∧
      (∀ x ∈ Fi.source, ∀ V W : TangentSpace ThreeModel x,
        ((S0 kl).base.metric (T - r ^ 2)).inner x V W =
          ((S0 kr).base.metric (T - r ^ 2)).inner (Fi x)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x V)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel (Fi : _ → _) ((alpha0 kl) r)
        (lVelocity (I := ThreeModel) (alpha0 kl) r) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha0 kr) r ∧
      (S0 kl).scalar (T - r ^ 2) ((alpha0 kl) r) = (S0 kr).scalar (T - r ^ 2) ((alpha0 kr) r) ∧
      lRegularizedLagrangian (S0 kl) T (alpha0 kl) r = lRegularizedLagrangian (S0 kr) T (alpha0 kr) r) := by
      subst kl
      subst kr
      have hi := h0 (z.symm i)
      simp only [rho, z.apply_symm_apply] at hi
      refine ⟨F0 (z.symm i), HEq.rfl, hi.1, hi.2.1.self_of_nhds,
        hi.2.1, hi.2.2.1, ?_, hi.2.2.2.2⟩
      have hv := (h0 (z.symm i)).2.2.2.1
      have hc : rho (z.symm i) = s i.castSucc.succ := by
        simp only [rho, z.apply_symm_apply]
      exact hc ▸ hv
    exact htransport _ _ (hleft i) (hright i)
  choose F hFeq hF using hex
  refine ⟨F, hF, ?_, ?_, ⟨FT, hFTsource, hFTid, ?_⟩, ?_⟩
  · intro k
    exact (hFeq (z (.inl k))).trans (congr_arg_heq F0 (z.symm_apply_apply (.inl k)))
  · intro k
    exact (hFeq (z (.inr (.inl k)))).trans
      (congr_arg_heq F0 (z.symm_apply_apply (.inr (.inl k))))
  · have hz : z (.inr (.inr 0)) = Fin.last (2 * N) :=
      (interleavedJoinEquiv_values N).2.2.1
    exact (congr_arg_heq F hz.symm).trans ((hFeq (z (.inr (.inr 0)))).trans
      (congr_arg_heq F0 (z.symm_apply_apply (.inr (.inr 0)))))
  · intro f g epsilon hf
    have hg (i : Fin (2 * N + 2)) : g (q.symm i) = f i :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    have hcompat (k : J) :
        g (L k) epsilon (rho k) ∈ (F0 k).source ∧
        F0 k (g (L k) epsilon (rho k)) = g (R k) epsilon (rho k) := by
      have htransport (kl kr : K) (hl : kl = L k) (hr : kr = R k)
          (G : PartialDiffeomorph ThreeModel ThreeModel (M0 kl) (M0 kr) ∞)
          (hG : HEq G (F0 k))
          (hmem : g kl epsilon (rho k) ∈ G.source)
          (hpoint : G (g kl epsilon (rho k)) = g kr epsilon (rho k)) :
          g (L k) epsilon (rho k) ∈ (F0 k).source ∧
          F0 k (g (L k) epsilon (rho k)) = g (R k) epsilon (rho k) := by
        subst kl
        subst kr
        cases eq_of_heq hG
        exact ⟨hmem, hpoint⟩
      apply htransport _ _
        ((hleft (z k)).trans (congrArg L (z.symm_apply_apply k)))
        ((hright (z k)).trans (congrArg R (z.symm_apply_apply k))) (F (z k))
        ((hFeq (z k)).trans (congr_arg_heq F0 (z.symm_apply_apply k)))
      · simpa only [rho, hg] using (hf (z k)).1
      · simpa only [rho, hg] using (hf (z k)).2
    refine ⟨?_, ?_, ?_⟩
    · intro k
      have hk := hcompat (.inl k)
      have hmem : g (.inr (.inl k)) epsilon (rho (.inl k)) ∈ (Fn k).source :=
        hk.2 ▸ (Fn k).symm.map_source hk.1
      exact (hnewMap k hmem).trans
        ((congrArg (Fn k) hk.2).symm.trans ((Fn k).right_inv hk.1))
    · intro k
      have hk := hcompat (.inr (.inl k))
      exact (holdMap k hk.1).trans hk.2
    · have hk := hcompat (.inr (.inr 0))
      exact (hFTid _).symm.trans (heq_of_eq hk.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
