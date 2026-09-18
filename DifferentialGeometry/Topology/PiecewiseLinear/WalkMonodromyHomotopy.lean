import DifferentialGeometry.Topology.PiecewiseLinear.CocycleWalkLift

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Set SimpleGraph

def closedWalkPow {V : Type*} {G : SimpleGraph V} {u : V} (γ : G.Walk u u) :
    ℕ → G.Walk u u
  | 0 => Walk.nil
  | k + 1 => γ.append (closedWalkPow γ k)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

namespace SimplicialBoolCocycle

variable (ε : SimplicialBoolCocycle K)

theorem walkMonodromy_closedWalkPow {u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk u u) (k : ℕ) :
    ε.walkMonodromy (closedWalkPow γ k) = (k : ZMod 2) * ε.walkMonodromy γ := by
  induction k with
  | zero => rw [closedWalkPow, ε.walkMonodromy_nil, Nat.cast_zero, zero_mul]
  | succ k ih =>
      rw [closedWalkPow, ε.walkMonodromy_append, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_comm]

theorem walkMonodromy_conjugate {u v : K.vertices}
    (q : (SimplicialComplex.edgeGraph K).Walk u v)
    (r : (SimplicialComplex.edgeGraph K).Walk v v) :
    ε.walkMonodromy (q.append (r.append q.reverse)) = ε.walkMonodromy r := by
  rw [ε.walkMonodromy_append, ε.walkMonodromy_append, ε.walkMonodromy_reverse,
    add_comm (ε.walkMonodromy r), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

variable [FiniteDimensional ℝ E] [Finite K.faces]

open Classical in
theorem walkParity_eq_of_homotopic {u w : K.vertices}
    (p q : (SimplicialComplex.edgeGraph K).Walk u w)
    (hpq : (walkPath p).Homotopic (walkPath q)) :
    ε.walkParity p = ε.walkParity q := by
  obtain ⟨Γp, hΓp⟩ := ε.exists_walkLift p false
  obtain ⟨Γq, hΓq⟩ := ε.exists_walkLift q false
  have h0 : (walkPath p).toContinuousMap 0 =
      ε.toBoolCocycle.toFiberBundleCore.proj
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :=
    (walkPath p).source
  have h1 : (walkPath q).toContinuousMap 0 =
      ε.toBoolCocycle.toFiberBundleCore.proj
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :=
    (walkPath q).source
  have hliftp : Γp.toContinuousMap =
      ε.isCoveringMap.liftPath (walkPath p).toContinuousMap
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h0 :=
    (ε.isCoveringMap.eq_liftPath_iff' h0).mpr ⟨funext fun t => hΓp t, Γp.source⟩
  have hliftq : Γq.toContinuousMap =
      ε.isCoveringMap.liftPath (walkPath q).toContinuousMap
        (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h1 :=
    (ε.isCoveringMap.eq_liftPath_iff' h1).mpr ⟨funext fun t => hΓq t, Γq.source⟩
  have hsame := ε.isCoveringMap.liftPath_apply_one_eq_of_homotopicRel hpq
    (⟨vertexPoint K u, false⟩ : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) h0 h1
  have hval : Γp.toContinuousMap 1 = Γq.toContinuousMap 1 := by
    rw [hliftp, hliftq, hsame]
  have hend := Γp.target.symm.trans (hval.trans Γq.target)
  have hbool := Bundle.TotalSpace.mk_inj.mp hend
  rwa [Bool.false_xor, Bool.false_xor] at hbool

open Classical in
theorem walkMonodromy_eq_of_homotopic {u w : K.vertices}
    (p q : (SimplicialComplex.edgeGraph K).Walk u w)
    (hpq : (walkPath p).Homotopic (walkPath q)) :
    ε.walkMonodromy p = ε.walkMonodromy q := by
  rw [← ε.boolZMod2_walkParity p, ← ε.boolZMod2_walkParity q,
    ε.walkParity_eq_of_homotopic p q hpq]

open Classical in
theorem walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_pow {v₀ u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀)
    (p : (SimplicialComplex.edgeGraph K).Walk u u)
    (q : (SimplicialComplex.edgeGraph K).Walk u v₀) (k : ℕ)
    (hp : (walkPath p).Homotopic
      (walkPath (q.append ((closedWalkPow γ k).append q.reverse)))) :
    ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ := by
  have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [ε.walkMonodromy_eq_of_homotopic p _ hp, ε.walkMonodromy_conjugate,
    ε.walkMonodromy_closedWalkPow]
  rcases hx (k : ZMod 2) with hk | hk
  · exact Or.inl (by rw [hk, zero_mul])
  · exact Or.inr (by rw [hk, one_mul])

end SimplicialBoolCocycle

end DifferentialGeometry.Topology.PiecewiseLinear
