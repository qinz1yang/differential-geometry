import DifferentialGeometry.Topology.ThreeManifold.PairedBallLoop
import DifferentialGeometry.Topology.ThreeManifold.PairedBallMerge
import DifferentialGeometry.Topology.ThreeManifold.PairedBallEmpty
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteCongruence
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedCongruence
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
noncomputable section
open Set Metric

section

namespace DifferentialGeometry.Topology.PairedBallGluing

universe v w t
variable {V : Type v} {E : Type w} {A : Type t}
  (endpoint : E → Bool → V) (s : E)
  (assign : A → V) (L : V → List A)

private def loopLabels : Option {v // v ≠ endpoint s false} → List A
  | none => L (endpoint s false)
  | some v => L v.val

private def mergeLabels : Option {v // v ≠ endpoint s false ∧ v ≠ endpoint s true} → List A
  | none => L (endpoint s false) ++ L (endpoint s true)
  | some v => L v.val

private theorem mem_loopLabels
    (hL : ∀ v a, a ∈ L v ↔ assign a = v)
    (v : Option {v // v ≠ endpoint s false}) (a : A) :
    a ∈ loopLabels endpoint s L v ↔ loopVertex endpoint s (assign a) = v := by
  classical
  cases v with
  | none => simp only [loopLabels, hL, loopVertex]; split_ifs <;> simp_all
  | some v =>
    simp only [loopLabels, hL, loopVertex]
    by_cases h : assign a = endpoint s false
    · simp only [dif_pos h]
      constructor
      · intro ha
        exact (v.property (ha.symm.trans h)).elim
      · intro he
        exact (Option.some_ne_none _ he.symm).elim
    · simp only [dif_neg h, Option.some.injEq]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem mem_mergeLabels
    (hL : ∀ v a, a ∈ L v ↔ assign a = v)
    (v : Option {v // v ≠ endpoint s false ∧ v ≠ endpoint s true}) (a : A) :
    a ∈ mergeLabels endpoint s L v ↔ mergeVertex endpoint s (assign a) = v := by
  classical
  cases v with
  | none =>
    simp only [mergeLabels, List.mem_append, hL, mergeVertex]
    split_ifs <;> simp_all
  | some v =>
    simp only [mergeLabels, hL, mergeVertex]
    by_cases h : assign a = endpoint s false
    · simp only [dif_pos h]
      constructor
      · intro ha
        exact (v.property.1 (ha.symm.trans h)).elim
      · intro he
        exact (Option.some_ne_none _ he.symm).elim
    · simp only [dif_neg h]
      by_cases h' : assign a = endpoint s true
      · simp only [dif_pos h']
        constructor
        · intro ha
          exact (v.property.2 (ha.symm.trans h')).elim
        · intro he
          exact (Option.some_ne_none _ he.symm).elim
      · simp only [dif_neg h', Option.some.injEq]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem nodup_loopLabels (hL : ∀ v, (L v).Nodup)
    (v : Option {v // v ≠ endpoint s false}) : (loopLabels endpoint s L v).Nodup := by
  cases v <;> exact hL _

private theorem nodup_mergeLabels (hends : endpoint s false ≠ endpoint s true)
    (hL : ∀ v a, a ∈ L v ↔ assign a = v) (hn : ∀ v, (L v).Nodup)
    (v : Option {v // v ≠ endpoint s false ∧ v ≠ endpoint s true}) :
    (mergeLabels endpoint s L v).Nodup := by
  cases v with
  | some v => exact hn _
  | none =>
    apply (hn _).append (hn _)
    rw [List.disjoint_left]
    intro a ha hb
    exact hends ((hL _ a).mp ha |>.symm.trans ((hL _ a).mp hb))


end DifferentialGeometry.Topology.PairedBallGluing

end

section

namespace DifferentialGeometry.Topology

universe u v

private theorem nonempty_orientedDiffeomorph_connectedSum_append_replicate_succ
    {A : Type v} (original : A → ConnectedClosedOrientedManifold.{u} 3)
    (L : List A) (Z X : ConnectedClosedOrientedManifold.{u} 3) (b : ℕ)
    (hX : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X.toClosedOrientedManifold
      (finiteConnectedSum (L.map original ++ List.replicate b Z)).toClosedOrientedManifold)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Z).toClosedOrientedManifold
      (finiteConnectedSum (L.map original ++ List.replicate (b + 1)
          Z)).toClosedOrientedManifold) := by
  obtain ⟨F⟩ := connectedSumOrientedTransport_holds X
    (finiteConnectedSum (L.map original ++ List.replicate b Z)) Z Z hX
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  obtain ⟨G⟩ := finiteConnectedSum_append_orientedDiffeomorph
    (L.map original ++ List.replicate b Z) [Z]
  refine ⟨F.trans ?_⟩
  simpa only [finiteConnectedSum_singleton, List.replicate_succ', List.append_assoc]
    using G.symm

private theorem nonempty_orientedDiffeomorph_smoothConnectedSum_append_replicate
    {A : Type v} (original : A → ConnectedClosedOrientedManifold.{u} 3)
    (L K : List A) (Z X Y : ConnectedClosedOrientedManifold.{u} 3) (b c : ℕ)
    (p : OrientedBallChart X.toClosedOrientedManifold)
    (q : OrientedBallChart Y.toClosedOrientedManifold)
    (hX : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph X.toClosedOrientedManifold
      (finiteConnectedSum (L.map original ++ List.replicate b Z)).toClosedOrientedManifold))
    (hY : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y.toClosedOrientedManifold
      (finiteConnectedSum (K.map original ++ List.replicate c Z)).toClosedOrientedManifold)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum X Y p q
          boundaryAttachment).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (finiteConnectedSum ((L ++ K).map original ++ List.replicate (b + c)
          Z)).toClosedOrientedManifold) := by
  obtain ⟨F₀⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    p (orientedBallChart X) q (orientedBallChart Y) boundaryAttachment
  obtain ⟨F₁⟩ := connectedSumOrientedTransport_holds X
    (finiteConnectedSum (L.map original ++ List.replicate b Z)) Y
    (finiteConnectedSum (K.map original ++ List.replicate c Z)) hX hY
  obtain ⟨F₂⟩ := finiteConnectedSum_append_orientedDiffeomorph
    (L.map original ++ List.replicate b Z) (K.map original ++ List.replicate c Z)
  have hperm : List.Perm
      ((L.map original ++ List.replicate b Z) ++ (K.map original ++ List.replicate c Z))
      ((L ++ K).map original ++ List.replicate (b + c) Z) := by
    rw [List.map_append, List.replicate_add, List.append_assoc, List.append_assoc]
    exact List.Perm.append_left (L.map original)
      (List.perm_append_comm_assoc (List.replicate b Z) (K.map original) (List.replicate c Z))
  obtain ⟨F₃⟩ := finiteConnectedSum_perm_orientedDiffeomorph hperm
  exact ⟨((F₀.trans F₁).trans F₂.symm).trans F₃⟩


end DifferentialGeometry.Topology

end

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w t
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem remaining_card_lt {E : Type w} [Finite E] (s : E) :
    Nat.card {e // e ≠ s} < Nat.card E := by
  classical
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_lt (x := s) (by simp)

private theorem exists_finite_quotient_with_factor_lists {A : Type t}
    (original : A → ConnectedClosedOrientedManifold.{u} 3) :
    ∀ n, ∀ {V : Type v} {E : Type w}, [Finite V] → [Finite E] → Nat.card E = n →
      ∀ (N : V → ConnectedClosedOrientedManifold.{u} 3) (endpoint : E → Bool → V)
      (chart : (e : E) → (b : Bool) →
        OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
      (hdisj : Pairwise fun p q =>
        Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
          (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
      (assign : A → V) (L : V → List A) (k : V → ℕ),
      (∀ v a, a ∈ L v ↔ assign a = v) → (∀ v, (L v).Nodup) → (∀ v, L v ≠ []) →
      (∀ v, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (N v).toClosedOrientedManifold
        (finiteConnectedSum ((L v).map original ++
          List.replicate (k v) (sphereTwoTimesCircleLift.ulift.{0,
              u}))).toClosedOrientedManifold)) →
      ∃ (W : Type v) (_ : Finite W) (M : W → ConnectedClosedOrientedManifold.{u} 3)
        (assign' : A → W) (L' : W → List A) (k' : W → ℕ),
        (∀ w a, a ∈ L' w ↔ assign' a = w) ∧ (∀ w, (L' w).Nodup) ∧ (∀ w, L' w ≠ []) ∧
        (∀ w, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (M w).toClosedOrientedManifold
          (finiteConnectedSum ((L' w).map original ++
            List.replicate (k' w) (sphereTwoTimesCircleLift.ulift.{0,
                u}))).toClosedOrientedManifold)) ∧
        Nonempty (Quot (fun x y => ∃ e,
          seamRel N endpoint chart hdisj e boundaryAttachment x y) ≃ₜ (Σ w, (M w).Carrier)) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E hV hE hcard N endpoint chart hdisj assign L k hmem hnodup hnonempty hpres
    let := hV
    let := hE
    cases isEmpty_or_nonempty E with
    | inl he =>
      let := he
      exact ⟨V, hV, N, assign, L, k, hmem, hnodup, hnonempty, hpres,
        ⟨quotientHomeomorphOfIsEmpty N endpoint chart hdisj (fun _ => boundaryAttachment)⟩⟩
    | inr he =>
      let := he
      let s : E := Classical.choice he
      have hlt : Nat.card {e // e ≠ s} < n := hcard ▸ remaining_card_lt s
      by_cases hloop : endpoint s true = endpoint s false
      · obtain ⟨S, F, b, hb, hd, H, hfirst, hu, hH, J, hJ⟩ :=
          exists_quotient_homeomorph_loop N endpoint chart s hloop hdisj
            (fun _ => boundaryAttachment) rfl
        let N' := loopFactor N endpoint s
        let ep' := fun e t => (loopFlag N endpoint chart s b e t).fst
        let ch' := fun e t => (loopFlag N endpoint chart s b e t).snd
        let assign' := loopVertex endpoint s ∘ assign
        let L' := loopLabels endpoint s L
        let k' : Option {v // v ≠ endpoint s false} → ℕ
          | none => k (endpoint s false) + 1
          | some v => k v.val
        have hmem' : ∀ v a, a ∈ L' v ↔ assign' a = v :=
          mem_loopLabels endpoint s assign L hmem
        have hn' : ∀ v, (L' v).Nodup := nodup_loopLabels endpoint s L hnodup
        have hne' : ∀ v, L' v ≠ [] := by intro v; cases v <;> exact hnonempty _
        have hp' : ∀ v, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (N' v).toClosedOrientedManifold
            (finiteConnectedSum ((L' v).map original ++
              List.replicate (k' v) (sphereTwoTimesCircleLift.ulift.{0,
                  u}))).toClosedOrientedManifold) := by
          intro v
          cases v with
          | some v => exact hpres _
          | none =>
            obtain ⟨G⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
              (M := N (endpoint s false)) (M' := N (endpoint s false))
              (N := sphereTwoTimesCircleLift) (N' := sphereTwoTimesCircleLift.ulift.{0, u})
              (ClosedOrientedManifold.OrientedDiffeomorph.refl
                (N (endpoint s false)).toClosedOrientedManifold)
              (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
                sphereTwoTimesCircleLift.toClosedOrientedManifold)
            obtain ⟨K⟩ := nonempty_orientedDiffeomorph_connectedSum_append_replicate_succ
              original (L (endpoint s false)) (sphereTwoTimesCircleLift.ulift.{0, u})
              (N (endpoint s false)) (k (endpoint s false)) (hpres _)
            exact ⟨G.trans K⟩
        obtain ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'', ⟨K⟩⟩ :=
          ih _ hlt (V := Option {v // v ≠ endpoint s false}) (E := {e // e ≠ s}) rfl
            N' ep' ch' hd assign' L' k' hmem' hn' hne' hp'
        exact ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'', ⟨J.trans K⟩⟩
      · have hends : endpoint s false ≠ endpoint s true := Ne.symm hloop
        obtain ⟨b, hbL, hbR, hd, H, hfirst, hsecond, hu, hH, J, hJ⟩ :=
          exists_quotient_homeomorph_merge N endpoint chart s hdisj
            (fun _ => boundaryAttachment) hends
        let N' := mergeFactor N endpoint chart s boundaryAttachment
        let ep' := fun e t => (mergeFlag N endpoint chart s boundaryAttachment b e t).fst
        let ch' := fun e t => (mergeFlag N endpoint chart s boundaryAttachment b e t).snd
        let assign' := mergeVertex endpoint s ∘ assign
        let L' := mergeLabels endpoint s L
        let k' : Option {v // v ≠ endpoint s false ∧ v ≠ endpoint s true} → ℕ
          | none => k (endpoint s false) + k (endpoint s true)
          | some v => k v.val
        have hmem' : ∀ v a, a ∈ L' v ↔ assign' a = v :=
          mem_mergeLabels endpoint s assign L hmem
        have hn' : ∀ v, (L' v).Nodup := nodup_mergeLabels endpoint s assign L hends hmem hnodup
        have hne' : ∀ v, L' v ≠ [] := by
          intro v
          cases v with
          | some v => exact hnonempty _
          | none => exact fun h => hnonempty _ (List.append_eq_nil_iff.mp h).1
        have hp' : ∀ v, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (N' v).toClosedOrientedManifold
            (finiteConnectedSum ((L' v).map original ++
              List.replicate (k' v) (sphereTwoTimesCircleLift.ulift.{0,
                  u}))).toClosedOrientedManifold) := by
          intro v
          cases v with
          | some v => exact hpres _
          | none =>
            exact nonempty_orientedDiffeomorph_smoothConnectedSum_append_replicate
              original (L (endpoint s false)) (L (endpoint s true))
                  (sphereTwoTimesCircleLift.ulift.{0, u})
              (N (endpoint s false)) (N (endpoint s true)) (k (endpoint s false))
              (k (endpoint s true)) (chart s false) (chart s true) (hpres _) (hpres _)
        obtain ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'', ⟨K⟩⟩ :=
          ih _ hlt (V := Option {v // v ≠ endpoint s false ∧ v ≠ endpoint s true})
            (E := {e // e ≠ s}) rfl N' ep' ch' hd assign' L' k' hmem' hn' hne' hp'
        exact ⟨W, hW, M, assign'', L'', k'', hmem'', hn'', hne'', hp'', ⟨J.trans K⟩⟩

theorem exists_finite_connectedSum_quotient
    {V : Type v} {E : Type w} [Finite V] [Finite E]
    (N : V → ConnectedClosedOrientedManifold.{u} 3)
    (endpoint : E → Bool → V)
    (chart : (e : E) → (t : Bool) →
      OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2)) :
    ∃ (W : Type v) (_ : Finite W) (assign : V → W) (L : W → List V) (k : W → ℕ),
      (∀ w v, v ∈ L w ↔ assign v = w) ∧ (∀ w, (L w).Nodup) ∧ (∀ w, L w ≠ []) ∧
      Nonempty (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y) ≃ₜ
        (Σ w, (finiteConnectedSum ((L w).map N ++
          List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier)) := by
  classical
  have hpres (v : V) : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (N v).toClosedOrientedManifold
      (finiteConnectedSum (([v] : List V).map N ++
        List.replicate 0 (sphereTwoTimesCircleLift.ulift.{0, u}))).toClosedOrientedManifold) :=
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  obtain ⟨W, hW, M, assign, L, k, hm, hn, hne, hp, ⟨H⟩⟩ :=
    exists_finite_quotient_with_factor_lists N (Nat.card E) rfl N endpoint chart hdisj id
      (fun v => [v]) (fun _ => 0) (fun _ _ => List.mem_singleton) (fun _ => List.nodup_singleton _)
      (fun _ => List.cons_ne_nil _ _) hpres
  let F := fun w => Classical.choice (hp w)
  exact ⟨W, hW, assign, L, k, hm, hn, hne,
    ⟨H.trans (Homeomorph.sigmaCongrRight fun w => (F w).val.toHomeomorph)⟩⟩

theorem exists_connectedSum_quotient_of_preconnected
    {V : Type v} {E : Type w} [Finite V] [Finite E] [Nonempty V]
    (N : V → ConnectedClosedOrientedManifold.{u} 3)
    (endpoint : E → Bool → V)
    (chart : (e : E) → (t : Bool) →
      OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    [PreconnectedSpace (Quot (fun x y => ∃ e,
      seamRel N endpoint chart hdisj e boundaryAttachment x y))] :
    ∃ (L : List V) (k : ℕ), L.Nodup ∧ (∀ v, v ∈ L) ∧
      Nonempty (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e boundaryAttachment x y) ≃ₜ
        (finiteConnectedSum (L.map N ++
          List.replicate k (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier) := by
  classical
  obtain ⟨W, hW, assign, L, k, hm, hn, hne, ⟨H⟩⟩ :=
    exists_finite_connectedSum_quotient N endpoint chart hdisj
  let M := fun w => finiteConnectedSum ((L w).map N ++
    List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))
  have hpre : PreconnectedSpace (Σ w, (M w).Carrier) :=
    H.surjective.denseRange.preconnectedSpace H.continuous
  let := hpre
  have hf : IsLocallyConstant (Sigma.fst : (Σ w, (M w).Carrier) → W) :=
    fun S => isOpen_sigma_fst_preimage S
  have hw : Subsingleton W := ⟨fun x y => by
    let p := Classical.choice (inferInstance : Nonempty (M x).Carrier)
    let q := Classical.choice (inferInstance : Nonempty (M y).Carrier)
    exact hf.apply_eq_of_preconnectedSpace ⟨x, p⟩ ⟨y, q⟩⟩
  let := hw
  let w₀ := assign (Classical.choice (inferInstance : Nonempty V))
  let K : (Σ w, (M w).Carrier) ≃ₜ (M w₀).Carrier :=
    { toFun := fun x => (Subsingleton.elim x.fst w₀) ▸ x.snd
      invFun := fun x => ⟨w₀, x⟩
      left_inv := by
        intro x
        obtain ⟨w, x⟩ := x
        have h : w = w₀ := Subsingleton.elim _ _
        subst w
        rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_sigma fun w => by
        have h : w = w₀ := Subsingleton.elim _ _
        subst w
        exact continuous_id
      continuous_invFun := @continuous_sigmaMk W (fun w => (M w).Carrier)
        (fun w => (M w).topology) w₀ }
  exact ⟨L w₀, k w₀, hn _, fun v => (hm _ v).mpr (Subsingleton.elim _ _), ⟨H.trans K⟩⟩

end DifferentialGeometry.Topology.PairedBallGluing
