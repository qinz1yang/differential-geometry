import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.LoopSpace.BasedCircle

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vertex_mem_stdSimplexBoundary_two (i j : Fin 3) (hij : i ≠ j) :
    (Pi.single i 1 : Fin 3 → ℝ) ∈ stdSimplexBoundary 2 := by
  refine ⟨⟨fun k => ?_, ?_⟩, j, ?_⟩
  · rcases eq_or_ne i k with rfl | h
    · simp
    · simp [h]
  · simp
  · simp [hij]

theorem exists_ne_mem_of_isPLSphere_one {S : Set E} (hS : IsPLSphere 1 S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q := by
  obtain ⟨f, hbij, -, -⟩ := hS
  have h0 : (Pi.single (0 : Fin 3) (1 : ℝ)) ∈ stdSimplexBoundary 2 :=
    vertex_mem_stdSimplexBoundary_two 0 1 (by decide)
  have h1 : (Pi.single (1 : Fin 3) (1 : ℝ)) ∈ stdSimplexBoundary 2 :=
    vertex_mem_stdSimplexBoundary_two 1 0 (by decide)
  refine ⟨f _, hbij.mapsTo h0, f _, hbij.mapsTo h1, fun hcontra => ?_⟩
  have := hbij.injOn h0 h1 hcontra
  have hne : (Pi.single (0 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) ≠
      (Pi.single (1 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) := by
    intro h
    have hc := congrFun h 0
    simp at hc
  exact hne this

theorem nonempty_homeomorph_loopCircle_of_isPLSphere_one [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) : Nonempty (loopCircle ≃ₜ S) := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_ne_mem_of_isPLSphere_one hS
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hq hpq
  have hAS : A ⊆ S := by rw [← hunion]; exact subset_union_left
  have hBS : B ⊆ S := by rw [← hunion]; exact subset_union_right
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := hγ.2.1.continuousOn
  have hδcont : ContinuousOn δ (Icc (0 : ℝ) 1) := hδ.2.1.continuousOn
  have hγinj : InjOn γ (Icc (0 : ℝ) 1) := hγ.1.injOn
  have hδinj : InjOn δ (Icc (0 : ℝ) 1) := hδ.1.injOn
  have hγmem : ∀ t : unitInterval, γ (t : ℝ) ∈ S := fun t => hAS (hγ.1.mapsTo t.2)
  have hδmem : ∀ t : unitInterval, δ (1 - (t : ℝ)) ∈ S := fun t =>
    hBS (hδ.1.mapsTo ⟨by linarith [unitInterval.le_one t], by linarith [unitInterval.nonneg t]⟩)
  let P₁ : Path (⟨p, hp⟩ : S) ⟨q, hq⟩ :=
    { toFun := fun t => ⟨γ (t : ℝ), hγmem t⟩
      continuous_toFun :=
        Continuous.subtype_mk (hγcont.comp_continuous continuous_subtype_val fun t => t.2) _
      source' := Subtype.ext (by simpa using hγ0)
      target' := Subtype.ext (by simpa using hγ1) }
  let P₂ : Path (⟨q, hq⟩ : S) ⟨p, hp⟩ :=
    { toFun := fun t => ⟨δ (1 - (t : ℝ)), hδmem t⟩
      continuous_toFun :=
        Continuous.subtype_mk (hδcont.comp_continuous
          (continuous_const.sub continuous_subtype_val)
          fun t => by
            change (1 : ℝ) - (t : ℝ) ∈ Icc (0 : ℝ) 1
            exact ⟨by linarith [unitInterval.le_one t],
              by linarith [unitInterval.nonneg t]⟩) _
      source' := Subtype.ext (by simpa using hδ1)
      target' := Subtype.ext (by simpa using hδ0) }
  set loop : Path (⟨p, hp⟩ : S) ⟨p, hp⟩ := P₁.trans P₂ with hloopdef
  have hvals : ∀ t : unitInterval, (loop t : E) =
      if (t : ℝ) ≤ 1 / 2 then γ (2 * (t : ℝ)) else δ (2 - 2 * (t : ℝ)) := by
    intro t
    rw [hloopdef, Path.trans_apply]
    split_ifs with h
    · rfl
    · change δ (1 - (2 * (t : ℝ) - 1)) = δ (2 - 2 * (t : ℝ))
      congr 1
      ring
  set F : freeLoop S := pathToCircle loop with hFdef
  have hFval : ∀ t : unitInterval, ((F (t : loopCircle) : S) : E) =
      if (t : ℝ) ≤ 1 / 2 then γ (2 * (t : ℝ)) else δ (2 - 2 * (t : ℝ)) := by
    intro t
    rw [hFdef, pathToCircle_coe loop t]
    exact hvals t
  have hmemγ : ∀ t : unitInterval, (t : ℝ) ≤ 1 / 2 → 2 * (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
    fun t h => ⟨by linarith [unitInterval.nonneg t], by linarith⟩
  have hmemδ : ∀ t : unitInterval, ¬ (t : ℝ) ≤ 1 / 2 → 2 - 2 * (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
    fun t h => ⟨by linarith [unitInterval.le_one t], by linarith [not_le.mp h]⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hFval' : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ((F (r : loopCircle) : S) : E) =
      if r ≤ 1 / 2 then γ (2 * r) else δ (2 - 2 * r) := fun r hr => hFval ⟨r, hr⟩
  have hinj : Function.Injective F := by
    intro θ₁ θ₂ hθ
    obtain ⟨t₁, rfl⟩ := unitInterval_to_loopCircle_surjective θ₁
    obtain ⟨t₂, rfl⟩ := unitInterval_to_loopCircle_surjective θ₂
    have hv : ((F ((t₁ : ℝ) : loopCircle) : S) : E) = ((F ((t₂ : ℝ) : loopCircle) : S) : E) := by
      rw [hθ]
    rw [hFval t₁, hFval t₂] at hv
    by_cases hc1 : (t₁ : ℝ) ≤ 1 / 2 <;> by_cases hc2 : (t₂ : ℝ) ≤ 1 / 2
    · rw [if_pos hc1, if_pos hc2] at hv
      have h := hγinj (hmemγ t₁ hc1) (hmemγ t₂ hc2) hv
      exact congrArg _ (by linarith : (t₁ : ℝ) = (t₂ : ℝ))
    · rw [if_pos hc1, if_neg hc2] at hv
      have hmem : γ (2 * (t₁ : ℝ)) ∈ A ∩ B :=
        ⟨hγ.1.mapsTo (hmemγ t₁ hc1), hv ▸ hδ.1.mapsTo (hmemδ t₂ hc2)⟩
      rw [hinter] at hmem
      rcases hmem with hval | hval
      · have e1 : 2 * (t₁ : ℝ) = 0 :=
          hγinj (hmemγ t₁ hc1) hzero (by rw [hval, hγ0])
        have e2 : 2 - 2 * (t₂ : ℝ) = 0 :=
          hδinj (hmemδ t₂ hc2) hzero (by rw [← hv, hval, hδ0])
        have f1 : (t₁ : ℝ) = 0 := by linarith
        have f2 : (t₂ : ℝ) = 1 := by linarith
        change ((t₁ : ℝ) : loopCircle) = ((t₂ : ℝ) : loopCircle)
        rw [f1, f2]
        simp [AddCircle.coe_period]
      · exfalso
        have e2 : 2 - 2 * (t₂ : ℝ) = 1 :=
          hδinj (hmemδ t₂ hc2) hone (by rw [← hv, hval]; exact hδ1.symm)
        exact hc2 (by linarith)
    · rw [if_neg hc1, if_pos hc2] at hv
      have hmem : γ (2 * (t₂ : ℝ)) ∈ A ∩ B :=
        ⟨hγ.1.mapsTo (hmemγ t₂ hc2), hv ▸ hδ.1.mapsTo (hmemδ t₁ hc1)⟩
      rw [hinter] at hmem
      rcases hmem with hval | hval
      · have e1 : 2 * (t₂ : ℝ) = 0 :=
          hγinj (hmemγ t₂ hc2) hzero (by rw [hval, hγ0])
        have e2 : 2 - 2 * (t₁ : ℝ) = 0 :=
          hδinj (hmemδ t₁ hc1) hzero (by rw [hv, hval, hδ0])
        have f1 : (t₁ : ℝ) = 1 := by linarith
        have f2 : (t₂ : ℝ) = 0 := by linarith
        change ((t₁ : ℝ) : loopCircle) = ((t₂ : ℝ) : loopCircle)
        rw [f1, f2]
        simp [AddCircle.coe_period]
      · exfalso
        have e2 : 2 - 2 * (t₁ : ℝ) = 1 :=
          hδinj (hmemδ t₁ hc1) hone (by rw [hv, hval]; exact hδ1.symm)
        exact hc1 (by linarith)
    · rw [if_neg hc1, if_neg hc2] at hv
      have h := hδinj (hmemδ t₁ hc1) (hmemδ t₂ hc2) hv
      exact congrArg _ (by linarith : (t₁ : ℝ) = (t₂ : ℝ))
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    rw [← hunion] at hy
    rcases hy with hyA | hyB
    · obtain ⟨u, hu, hsy⟩ := hγ.1.surjOn hyA
      have ht : u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      refine ⟨((u / 2 : ℝ) : loopCircle), Subtype.ext ?_⟩
      rw [hFval' (u / 2) ht, if_pos (by linarith [hu.2] : u / 2 ≤ 1 / 2),
        show 2 * (u / 2) = u by ring]
      exact hsy
    · obtain ⟨u, hu, hsy⟩ := hδ.1.surjOn hyB
      have ht : 1 - u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      refine ⟨((1 - u / 2 : ℝ) : loopCircle), Subtype.ext ?_⟩
      rw [hFval' (1 - u / 2) ht]
      by_cases hcase : (1 : ℝ) - u / 2 ≤ 1 / 2
      · rw [if_pos hcase]
        have hu1 : u = 1 := by linarith [hu.2]
        rw [show 2 * (1 - u / 2) = 2 - u by ring, hu1]
        rw [show (2 : ℝ) - 1 = 1 by norm_num, hγ1, ← hδ1]
        rw [hu1] at hsy
        exact hsy
      · rw [if_neg hcase, show 2 - 2 * (1 - u / 2) = u by ring]
        exact hsy
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩) F.continuous⟩


end DifferentialGeometry.Topology.PiecewiseLinear
