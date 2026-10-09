/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ProtectedSubdivisionStarInj
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlockRecentre
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularSetOfCrossing

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_pos_doublePointSet_inter_subset {X : Type*} [MetricSpace X]
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : IsCompact S) {f : EuclideanSpace ℝ (Fin 2) → X}
    (hf : ContinuousOn f S) {κ : ℝ} (hκ : 0 < κ) {Q O : Set X} (hQ : IsClosed Q) (hO : IsOpen O)
    (hfQ : doublePointSet f S ∩ Q ⊆ O) :
    ∃ m : ℝ, 0 < m ∧ ∀ g : EuclideanSpace ℝ (Fin 2) → X, (∀ x ∈ S, dist (g x) (f x) < m) →
      UniformInjectivityScale S g κ → doublePointSet g S ∩ Q ⊆ O := by
  by_cases hQO : (Q \ O).Nonempty
  swap
  · refine ⟨1, one_pos, fun g _ _ y hy => ?_⟩
    by_contra hyO
    exact hQO ⟨y, hy.2, hyO⟩
  set P₀ : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (S ×ˢ S) ∩ {p | κ ≤ dist p.1 p.2}
  have hP₀c : IsCompact P₀ :=
    (hS.prod hS).inter_right (isClosed_le continuous_const continuous_dist)
  have hQOc : IsClosed (Q \ O) := hQ.sdiff hO
  have hF1 : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      f p.1) P₀ := hf.comp continuous_fst.continuousOn fun p hp => hp.1.1
  have hF2 : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      f p.2) P₀ := hf.comp continuous_snd.continuousOn fun p hp => hp.1.2
  have hF : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist (f p.1) (f p.2) + infDist (f p.1) (Q \ O)) P₀ :=
    (continuous_dist.comp_continuousOn (hF1.prodMk hF2)).add
      ((continuous_infDist_pt (Q \ O)).comp_continuousOn hF1)
  have hpos : ∀ p ∈ P₀, 0 < dist (f p.1) (f p.2) + infDist (f p.1) (Q \ O) := by
    intro p hp
    by_contra hle
    have h1 : 0 ≤ dist (f p.1) (f p.2) := dist_nonneg
    have h2 : 0 ≤ infDist (f p.1) (Q \ O) := infDist_nonneg
    have hd : dist (f p.1) (f p.2) = 0 := by linarith
    have hi : infDist (f p.1) (Q \ O) = 0 := by linarith
    have hmem : f p.1 ∈ Q \ O := by
      rw [← hQOc.closure_eq, mem_closure_iff_infDist_zero hQO]
      exact hi
    have hne : p.1 ≠ p.2 := by
      intro heq
      have h3 : κ ≤ dist p.1 p.2 := hp.2
      rw [heq, dist_self] at h3
      linarith
    exact hmem.2 (hfQ ⟨⟨p.1, hp.1.1, p.2, hp.1.2, hne, rfl, (dist_eq_zero.mp hd).symm⟩, hmem.1⟩)
  by_cases hne : P₀.Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := hP₀c.exists_isMinOn hne hF
    set m₁ := dist (f p₀.1) (f p₀.2) + infDist (f p₀.1) (Q \ O)
    have hm₁ : 0 < m₁ := hpos p₀ hp₀
    refine ⟨m₁ / 3, by positivity, fun g hg huis y hy => ?_⟩
    by_contra hyO
    obtain ⟨⟨x, hx, x', hx', hxx', hgx, hgx'⟩, hyQ⟩ := hy
    have hd : κ ≤ dist x x' := by
      by_contra hlt
      exact hxx' (huis x hx x' hx' (not_le.mp hlt) (hgx.trans hgx'.symm))
    have hpP : (x, x') ∈ P₀ := ⟨⟨hx, hx'⟩, hd⟩
    have h1 : m₁ ≤ dist (f x) (f x') + infDist (f x) (Q \ O) := isMinOn_iff.mp hmin _ hpP
    have h2 : infDist (f x) (Q \ O) ≤ dist (f x) y := infDist_le_dist_of_mem ⟨hyQ, hyO⟩
    have h3 : dist (f x) (f x') ≤ dist (f x) y + dist y (f x') := dist_triangle _ _ _
    have h4 := hg x hx
    have h5 := hg x' hx'
    rw [hgx, dist_comm] at h4
    rw [hgx', dist_comm] at h5
    rw [dist_comm y] at h3
    linarith
  · refine ⟨1, one_pos, fun g _ huis y hy => ?_⟩
    by_contra hyO
    obtain ⟨⟨x, hx, x', hx', hxx', hgx, hgx'⟩, -⟩ := hy
    have hd : κ ≤ dist x x' := by
      by_contra hlt
      exact hxx' (huis x hx x' hx' (not_le.mp hlt) (hgx.trans hgx'.symm))
    exact hne ⟨(x, x'), ⟨hx, hx'⟩, hd⟩

theorem IsPLHomeomorphOn.exists_pos_mem_of_dist_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p : E → ℝ × ℝ} {T : Set E} (hpl : IsPLHomeomorphOn p T (p '' T))
    {x₀ : E} (hx₀ : x₀ ∈ T) {G : Set E} (hG : IsOpen G) (hx₀G : x₀ ∈ G) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ T, dist (p x) (p x₀) < ρ → x ∈ G := by
  have hψ₀ : Function.invFunOn p T (p x₀) = x₀ := hpl.bijOn.invOn_invFunOn.1 hx₀
  have hψc : ContinuousWithinAt (Function.invFunOn p T) (p '' T) (p x₀) :=
    hpl.isPiecewiseAffineOn_invFunOn.continuousOn _ (mem_image_of_mem p hx₀)
  have hpre : Function.invFunOn p T ⁻¹' G ∈ 𝓝[p '' T] (p x₀) :=
    hψc.preimage_mem_nhdsWithin (by rw [hψ₀]; exact hG.mem_nhds hx₀G)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  refine ⟨ρ, hρ, fun x hx hd => ?_⟩
  have h1 : Function.invFunOn p T (p x) ∈ G := hball ⟨mem_ball.mpr hd, mem_image_of_mem p hx⟩
  rwa [hpl.bijOn.invOn_invFunOn.1 hx] at h1

section Ambient

variable {M : Type u} [TopologicalSpace M]

theorem IsStableCrossingBlock.exists_recentre_localized [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0) {y₀ : M}
    (hy₀ : y₀ ∈ doublePointSet f S) (hy₀in : y₀ ∈ innerChartBlock ec A r tlo)
    {Ω Kc : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω) (hKc : IsClosed Kc)
    (hKcΩ : Kc ⊆ Ω) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r₁ tlo₁ : ℝ) (a₁ b₁ : ℝ × ℝ → ℝ),
      0 < r₁ ∧ A' (ec y₀) = 0 ∧
      IsStableCrossingBlock f S ec ℓ BdM A' r₁ tlo₁ (SA ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁)
        (SB ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁) a₁ b₁ La Lb η ∧
      ((∀ x ∈ SA ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∈ Ω) ∨
        ∀ x ∈ SA ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∉ Kc) ∧
      ((∀ x ∈ SB ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∈ Ω) ∨
        ∀ x ∈ SB ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∉ Kc) := by
  obtain ⟨hr, -, -, -, -, -, -, hside, -, -, -, -, hplA, hplB, -, -, -, -, -, -⟩ := id h
  have htlo : tlo = -r ∨ tlo = 0 := hside.imp (fun h => h.1) (fun h => h.1)
  have htle : tlo ≤ 0 := by rcases htlo with ht | ht <;> linarith
  have hy₀B : y₀ ∈ chartBlock ec A r tlo := chartBlock_mono_of_half ec A hr.le htle hy₀in
  have hy₀s : y₀ ∈ ec.source := hy₀B.1
  obtain ⟨⟨xA, hxA, hfxA⟩, ⟨xB, hxB, hfxB⟩⟩ :=
    sheets_nonempty_of_isStableCrossingBlock h hy₀ hy₀B
  have hfxA' : f xA = y₀ := hfxA
  have hfxB' : f xB = y₀ := hfxB
  have hGsel : ∀ x₀ : EuclideanSpace ℝ (Fin 2), ∃ G : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen G ∧ x₀ ∈ G ∧ (G ⊆ Ω ∨ Disjoint G Kc) := by
    intro x₀
    by_cases hx₀ : x₀ ∈ Ω
    · exact ⟨Ω, hΩ, hx₀, Or.inl subset_rfl⟩
    · exact ⟨Kcᶜ, hKc.isOpen_compl, fun h => hx₀ (hKcΩ h), Or.inr disjoint_compl_left⟩
  obtain ⟨GA, hGAo, hxGA, hGA⟩ := hGsel xA
  obtain ⟨GB, hGBo, hxGB, hGB⟩ := hGsel xB
  obtain ⟨ρA, hρA, hρA'⟩ := hplA.exists_pos_mem_of_dist_lt hxA hGAo hxGA
  obtain ⟨ρB, hρB, hρB'⟩ := hplB.exists_pos_mem_of_dist_lt hxB hGBo hxGB
  have ht₀0 : tlo = 0 → 0 ≤ (A (ec y₀)).2.2 := by
    intro h0
    have h1 : tlo / 2 ≤ (A (ec y₀)).2.2 := hy₀in.2.2.2.1
    rw [h0, zero_div] at h1
    exact h1
  set ρ₃ : ℝ := if (A (ec y₀)).2.2 = 0 then 1 else |(A (ec y₀)).2.2| with hρ₃
  have hρ₃pos : 0 < ρ₃ := by
    rw [hρ₃]
    split_ifs with h0
    · exact one_pos
    · exact abs_pos.mpr h0
  set ρ : ℝ := min (min ρA ρB) ρ₃
  have hρpos : 0 < ρ := lt_min (lt_min hρA hρB) hρ₃pos
  have hAc : Continuous A := A.toAffineMap.continuous_of_finiteDimensional
  set O : Set M := ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' ball (A (ec y₀)) ρ)
  have hOo : IsOpen O := ec.isOpen_inter_preimage (isOpen_ball.preimage hAc)
  have hy₀O : y₀ ∈ O := ⟨hy₀s, mem_ball_self hρpos⟩
  set A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
    A.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-(A (ec y₀)))) with hA'def
  have hA'app : ∀ z, A' z = A z - A (ec y₀) := by
    intro z
    rw [hA'def, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, vadd_eq_add,
      neg_add_eq_sub]
  have hOpos : ∀ z ∈ O, tlo = 0 → (A (ec y₀)).2.2 ≠ 0 → 0 < (A (ec z)).2.2 := by
    intro z hz h0 hne
    have hd : dist (A (ec z)) (A (ec y₀)) < ρ := hz.2
    have h1 : |(A (ec z)).2.2 - (A (ec y₀)).2.2| < |(A (ec y₀)).2.2| := by
      have h2 : dist (A (ec z)).2.2 (A (ec y₀)).2.2 ≤ dist (A (ec z)) (A (ec y₀)) := by
        rw [Prod.dist_eq (x := A (ec z)), Prod.dist_eq (x := (A (ec z)).2)]
        exact (le_max_right _ _).trans (le_max_right _ _)
      rw [Real.dist_eq] at h2
      have h3 : ρ ≤ |(A (ec y₀)).2.2| := by
        have h5 : ρ₃ = |(A (ec y₀)).2.2| := by rw [hρ₃, ite_eq_right hne]
        rw [← h5]
        exact min_le_right _ _
      linarith
    have h4 : 0 < (A (ec y₀)).2.2 := lt_of_le_of_ne (ht₀0 h0) (Ne.symm hne)
    rw [abs_of_pos h4] at h1
    have := (abs_lt.mp h1).1
    linarith
  obtain ⟨r₁, tlo₁, a₁, b₁, hr₁, hB₁, hsubO⟩ :=
    IsStableCrossingBlock.exists_kink_recentre (ec' := ec) (ℓ' := ℓ) (A' := A') (α₁ := 0)
      (β₁ := 0) (κ := 0) h hBd hy₀ hy₀in (by norm_num) hOo hy₀O (fun z hz => ⟨hz.1, hz.1⟩)
      hOpos (by rw [hA'app, sub_self]) (fun z _ _ => by
        rw [hA'app]
        simp only [kinkOffset, kinkHeight, zero_mul, add_zero]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring)
      (fun h0 ht0 => by
        have hAℓ : ∀ z, (A z).2.2 = ℓ z := by
          rcases hside with ⟨ht', -⟩ | ⟨-, hz, -⟩
          · exfalso
            linarith
          · exact hz
        refine ⟨fun z => ?_, fun z _ => ?_⟩
        · rw [hA'app, Prod.snd_sub, Prod.snd_sub, ht0, sub_zero, hAℓ]
        · rw [hA'app, Prod.snd_sub, Prod.snd_sub, ht0, sub_zero])
  have hloc : ∀ x, f x ∈ chartBlock ec A' r₁ tlo₁ → dist (A (ec (f x))) (A (ec y₀)) < ρ :=
    fun x hx => (hsubO hx).2
  have hdistA : ∀ x, dist (A (ec (f x))) (A (ec y₀)) < ρ →
      dist (blockSheetProjA ec A f x) (blockSheetProjA ec A f xA) < ρA := by
    intro x hx
    have h1 : dist (blockSheetProjA ec A f x) (blockSheetProjA ec A f xA) ≤
        dist (A (ec (f x))) (A (ec y₀)) := by
      change dist ((A (ec (f x))).2.1, (A (ec (f x))).2.2)
        ((A (ec (f xA))).2.1, (A (ec (f xA))).2.2) ≤ _
      rw [hfxA', Prod.mk.eta, Prod.mk.eta, Prod.dist_eq (x := A (ec (f x)))]
      exact le_max_right _ _
    exact h1.trans_lt (hx.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hdistB : ∀ x, dist (A (ec (f x))) (A (ec y₀)) < ρ →
      dist (blockSheetProjB ec A f x) (blockSheetProjB ec A f xB) < ρB := by
    intro x hx
    have h1 : dist (blockSheetProjB ec A f x) (blockSheetProjB ec A f xB) ≤
        dist (A (ec (f x))) (A (ec y₀)) := by
      change dist ((A (ec (f x))).1, (A (ec (f x))).2.2)
        ((A (ec (f xB))).1, (A (ec (f xB))).2.2) ≤ _
      rw [hfxB', Prod.dist_eq, Prod.dist_eq (x := A (ec (f x))),
        Prod.dist_eq (x := (A (ec (f x))).2)]
      exact max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))
    exact h1.trans_lt (hx.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  refine ⟨A', r₁, tlo₁, a₁, b₁, hr₁, by rw [hA'app, sub_self], hB₁, ?_, ?_⟩
  · rcases hGA with hGA | hGA
    · exact Or.inl fun x hx => hGA (hρA' x hx.1 (hdistA x (hloc x hx.2)))
    · exact Or.inr fun x hx hxK =>
        Set.disjoint_left.mp hGA (hρA' x hx.1 (hdistA x (hloc x hx.2))) hxK
  · rcases hGB with hGB | hGB
    · exact Or.inl fun x hx => hGB (hρB' x hx.1 (hdistB x (hloc x hx.2)))
    · exact Or.inr fun x hx hxK =>
        Set.disjoint_left.mp hGB (hρB' x hx.1 (hdistB x (hloc x hx.2))) hxK

theorem IsStableCrossingBlock.exists_regional_perturbation [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0) {y₀ : M}
    (hy₀ : y₀ ∈ doublePointSet f S) (hy₀in : y₀ ∈ innerChartBlock ec A r tlo)
    {Ω Kc : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω) (hKc : IsClosed Kc)
    (hKcΩ : Kc ⊆ Ω) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ) (O : Set M), IsOpen O ∧
      y₀ ∈ O ∧ O ⊆ ec.source ∧ (∀ z ∈ O, 0 ≤ ℓ (ec z) → z ∈ innerChartBlock ec A' r' tlo') ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ (g : EuclideanSpace ℝ (Fin 2) → M)
          (δ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (lam : NNReal),
          (lam : ℝ) ≤ lam₀ → IsPiecewiseAffineOn δ univ → LipschitzWith lam δ →
          (∀ x ∈ S, g x ∈ ec.source → f x ∈ ec.source ∧ ‖ec (g x) - ec (f x)‖ ≤ ε₀) →
          (∀ x ∈ S, f x ∈ ec.source → 0 ≤ ℓ (ec (f x))) →
          (∀ x ∈ S, x ∈ Ω → g x ∈ ec.source ∧ ec (g x) = ec (f x) + δ x) →
          (∀ x ∈ S, x ∉ Kc → g x = f x) →
          (∀ x ∈ S, g x ∈ ec.source →
            0 ≤ ℓ (ec (g x)) ∧ (x ∈ frontier S ↔ ℓ (ec (g x)) = 0)) →
          ∃ (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ) (La' Lb' : ℝ),
            IsStableCrossingBlock g S ec ℓ BdM A' r' tlo' SA' SB' a' b' La' Lb' (η / 2) := by
  obtain ⟨hr, -, -, -, -, -, -, hside, hpre, -, -, -, -, -, -, -, -, -, -, -⟩ := id h
  have htlo : tlo = -r ∨ tlo = 0 := hside.imp (fun h => h.1) (fun h => h.1)
  have htle : tlo ≤ 0 := by rcases htlo with ht | ht <;> linarith
  have hy₀s : y₀ ∈ ec.source := (chartBlock_mono_of_half ec A hr.le htle hy₀in).1
  obtain ⟨A', r₁, tlo₁, a₁, b₁, hr₁, hA'0, hB₁, hlocA, hlocB⟩ :=
    h.exists_recentre_localized hBd hy₀ hy₀in hΩ hKc hKcΩ
  obtain ⟨r', hr', -, hinner, ε₀, hε₀, lam₀, hlam₀, hmain⟩ :=
    hB₁.exists_perturbation hy₀ hy₀s hA'0
  have hAℓ : tlo₁ = 0 → ∀ z, (A' z).2.2 = ℓ z := by
    intro h0
    obtain ⟨hr₁', -, -, -, -, -, -, hside₁, -⟩ := hB₁
    rcases hside₁ with ⟨ht, -⟩ | ⟨-, hz, -⟩
    · exfalso
      linarith
    · exact hz
  have hA'c : Continuous A' := A'.toAffineMap.continuous_of_finiteDimensional
  have hSAS : ∀ x ∈ SA, x ∈ S := fun x hx => by
    have h1 : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by
      rw [hpre]
      exact Or.inl hx
    exact h1.1
  have hSBS : ∀ x ∈ SB, x ∈ S := fun x hx => by
    have h1 : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by
      rw [hpre]
      exact Or.inr hx
    exact h1.1
  refine ⟨A', r', tlo₁ * (r' / r₁), ec.source ∩ ⇑ec ⁻¹' (⇑A' ⁻¹' ball 0 (r' / 2)),
    ec.isOpen_inter_preimage (isOpen_ball.preimage hA'c), ⟨hy₀s, ?_⟩, inter_subset_left, ?_,
    ε₀, hε₀, lam₀, hlam₀, ?_⟩
  · change A' (ec y₀) ∈ ball 0 (r' / 2)
    rw [hA'0]
    exact mem_ball_self (half_pos hr')
  · intro z hz hz0
    refine hinner z hz.1 (mem_ball_zero_iff.mp hz.2) fun h0 => ?_
    rw [hAℓ h0]
    exact hz0
  intro g δ lam hlam hδ hδL hclose hfC hgΩ hgK hg4
  have hsel : ∀ T₁ : Set (EuclideanSpace ℝ (Fin 2)),
      ((∀ x ∈ T₁, x ∈ Ω) ∨ ∀ x ∈ T₁, x ∉ Kc) → (∀ x ∈ T₁, x ∈ S ∧ f x ∈ ec.source) →
      ∃ δ₁ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3),
        IsPiecewiseAffineOn δ₁ univ ∧ LipschitzWith lam δ₁ ∧
          ∀ x ∈ T₁, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δ₁ x := by
    intro T₁ hT₁ hT₁S
    rcases hT₁ with hΩ₁ | hK₁
    · exact ⟨δ, hδ, hδL, fun x hx => hgΩ x (hT₁S x hx).1 (hΩ₁ x hx)⟩
    · refine ⟨fun _ => 0, isPiecewiseAffineOn_of_affine
        (AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) (0 : EuclideanSpace ℝ (Fin 3)))
        isOpen_univ, (LipschitzWith.const (0 : EuclideanSpace ℝ (Fin 3))).weaken zero_le,
        fun x hx => ?_⟩
      rw [hgK x (hT₁S x hx).1 (hK₁ x hx), add_zero]
      exact ⟨(hT₁S x hx).2, rfl⟩
  obtain ⟨δA, hδA, hδAL, hGA⟩ := hsel _ hlocA fun x hx => ⟨hSAS x hx.1, hx.2.1⟩
  obtain ⟨δB, hδB, hδBL, hGB⟩ := hsel _ hlocB fun x hx => ⟨hSBS x hx.1, hx.2.1⟩
  obtain ⟨a', b', La', Lb', hblk⟩ := hmain g δA δB lam hlam hδA hδAL hδB hδBL
    (fun x hx hxN => hclose x hx hxN.1) (fun _ => hfC) hGA hGB
    (fun _ x hx => by
      rcases hx with hx | hx
      · exact hg4 x (hSAS x hx.1) (hGA x hx).1
      · exact hg4 x (hSBS x hx.1) (hGB x hx).1)
  exact ⟨_, _, a', b', La', Lb', hblk⟩

end Ambient

theorem Finset.exists_pos_forall_le_of_pos {ι : Type*} (t : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ t, 0 < f i) : ∃ e : ℝ, 0 < e ∧ ∀ i ∈ t, e ≤ f i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | @insert j t hj ih =>
    obtain ⟨e, he, hle⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    refine ⟨min e (f j), lt_min he (hf j (Finset.mem_insert_self j t)), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle i hi)

section Ambient

variable {M : Type u} [TopologicalSpace M]

theorem hasStableCrossingBlocks_of_finset {ι : Type*} {g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q : Set M} {η : ℝ} (hη : 0 < η)
    (t : Finset ι) (A : ι → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ)) (r tlo : ι → ℝ)
    (SA SB : ι → Set (EuclideanSpace ℝ (Fin 2))) (a b : ι → ℝ × ℝ → ℝ) (La Lb : ι → ℝ)
    (hcov : doublePointSet g S ∩ Q ⊆ ⋃ i ∈ t, innerChartBlock ec (A i) (r i) (tlo i))
    (hblk : ∀ i ∈ t, IsStableCrossingBlock g S ec ℓ BdM (A i) (r i) (tlo i) (SA i) (SB i)
      (a i) (b i) (La i) (Lb i) η) :
    HasStableCrossingBlocks g S ec ℓ BdM Q η := by
  let e := t.equivFin
  let p : Fin t.card → ι := fun k => (e.symm k : ι)
  refine ⟨hη, t.card, fun k => A (p k), fun k => r (p k), fun k => tlo (p k),
    fun k => SA (p k), fun k => SB (p k), fun k => a (p k), fun k => b (p k),
    fun k => La (p k), fun k => Lb (p k), ?_, fun k => hblk (p k) (e.symm k).2⟩
  intro y hy
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hcov hy)
  refine mem_iUnion.mpr ⟨e ⟨i, hi⟩, ?_⟩
  have hpi : p (e ⟨i, hi⟩) = i := by simp [p]
  change y ∈ innerChartBlock ec (A (p (e ⟨i, hi⟩))) (r (p (e ⟨i, hi⟩))) (tlo (p (e ⟨i, hi⟩)))
  rw [hpi]
  exact hyi

end Ambient

open Classical in
theorem exists_vertex_displacement_lipschitz
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hRfin : R.faces.Finite) :
    ∃ (Vs : Finset (EuclideanSpace ℝ (Fin 2))) (Λ : ℝ), 0 ≤ Λ ∧ R.vertices ⊆ ↑Vs ∧
      ∀ (φ φ₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (τ : ℝ),
        (∀ v ∈ R.vertices, dist (φ v) (φ₀ v) < τ) →
        ∃ (δ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (lam : NNReal),
          IsPiecewiseAffineOn δ univ ∧ LipschitzWith lam δ ∧ (lam : ℝ) ≤ Λ * τ ∧
            ∀ x ∈ R.space, δ x = simplicialMap R φ x - simplicialMap R φ₀ x := by
  have : Finite R.faces := hRfin.to_subtype
  have hvfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  set Vs := hvfin.toFinset with hVs
  have hVsub : R.vertices ⊆ ↑Vs := by
    intro v hv
    rw [hVs, Set.Finite.coe_toFinset]
    exact hv
  choose bf kf hbpl hblip hbeq _ _ using fun v : EuclideanSpace ℝ (Fin 2) =>
    exists_piecewiseAffine_lipschitz_vertex_function R v isOpen_univ (subset_univ _)
  refine ⟨Vs, ∑ v ∈ Vs, (kf v : ℝ), Finset.sum_nonneg fun v _ => NNReal.coe_nonneg _, hVsub,
    fun φ φ₀ τ hφ => ?_⟩
  set c : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) := fun v => φ v - φ₀ v
  refine ⟨fun x => ∑ v ∈ Vs, bf v x • c v, ∑ v ∈ Vs, kf v * ‖c v‖₊, ?_, ?_, ?_, ?_⟩
  · refine IsPiecewiseAffineOn.sum Vs isOpen_univ fun v _ => ?_
    exact (hbpl v).affine_comp (LinearMap.smulRight LinearMap.id (c v)).toAffineMap
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, ← Finset.sum_sub_distrib]
    calc ‖∑ v ∈ Vs, (bf v x • c v - bf v y • c v)‖
        ≤ ∑ v ∈ Vs, ‖bf v x • c v - bf v y • c v‖ := norm_sum_le _ _
      _ = ∑ v ∈ Vs, |bf v x - bf v y| * ‖c v‖ := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ v ∈ Vs, (kf v * dist x y) * ‖c v‖ := by
          refine Finset.sum_le_sum fun v _ => ?_
          have h1 := (hblip v).dist_le_mul x y
          rw [Real.dist_eq] at h1
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ((∑ v ∈ Vs, kf v * ‖c v‖₊ : NNReal) : ℝ) * dist x y := by
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun v _ => ?_
          ring
  · push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun v hv => ?_
    refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
    have hvR : v ∈ R.vertices := by
      rw [hVs, Set.Finite.mem_toFinset] at hv
      exact hv
    have := hφ v hvR
    rw [dist_eq_norm] at this
    exact this.le
  · intro x hx
    change ∑ v ∈ Vs, bf v x • c v = simplicialMap R φ x - simplicialMap R φ₀ x
    rw [sum_vertex_functions_smul_eq_simplicialMap R Vs hVsub bf (fun v _ => hbeq v) c hx]
    exact simplicialMap_sub R φ φ₀ hx

end DifferentialGeometry.Topology.PiecewiseLinear
