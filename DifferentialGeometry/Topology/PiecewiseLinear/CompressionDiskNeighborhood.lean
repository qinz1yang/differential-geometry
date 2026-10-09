/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem mem_closure_sdiff_image_stdSimplexBoundary {q : (Fin 3 → ℝ) → E3} {D : Set E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {x : E3}
    (hx : x ∈ q '' stdSimplexBoundary 2) : x ∈ closure (D \ q '' stdSimplexBoundary 2) := by
  obtain ⟨b, hb, rfl⟩ := hx
  set c : Fin 3 → ℝ := fun _ => 1 / 3 with hcdef
  have hc : c ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    refine ⟨fun _ => by norm_num [hcdef], ?_⟩
    simp [hcdef]
  have hbS : b ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := hb.1
  have hseg : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (1 - t) • b + t • c ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2 := by
    intro t ht ht1
    refine ⟨(Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3)) hbS hc (by linarith) ht.le (by ring), ?_⟩
    rintro ⟨-, i, hi⟩
    have hbi : 0 ≤ b i := hbS.1 i
    have h1 : ((1 - t) • b + t • c) i = (1 - t) * b i + t * (1 / 3) := by
      simp [hcdef]
    rw [h1] at hi
    nlinarith
  have hcont : ContinuousWithinAt q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) b :=
    hq.isPiecewiseAffineOn.continuousOn b hbS
  have hline : Filter.Tendsto (fun t : ℝ => (1 - t) • b + t • c) (𝓝[>] 0) (𝓝 b) := by
    have hc' : Continuous (fun t : ℝ => (1 - t) • b + t • c) := by fun_prop
    have h0 : (fun t : ℝ => (1 - t) • b + t • c) 0 = b := by simp
    simpa [h0] using (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
  have hline' : Filter.Tendsto (fun t : ℝ => (1 - t) • b + t • c) (𝓝[>] 0)
      (𝓝[Convexity.StdSimplex.coordinateSet ℝ (Fin 3)] b) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hline, ?_⟩
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    exact (hseg t ht.1 ht.2).1
  have htend := hcont.tendsto.comp hline'
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have hmem := hseg t ht.1 ht.2
  refine ⟨hq.bijOn.mapsTo hmem.1, ?_⟩
  rintro ⟨b', hb', hbb'⟩
  have heq := hq.bijOn.injOn hb'.1 hmem.1 hbb'
  exact hmem.2 (heq ▸ hb')

theorem exists_isOpen_inter_inter_subset_of_hasPLCrossingAt {P S D : Set E3}
    (hP : IsPLBall 3 P) {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ P)
    (hDfr : D ∩ frontier P = q '' stdSimplexBoundary 2) (hDS : D ⊆ S)
    (hint : ∀ x ∈ D \ q '' stdSimplexBoundary 2, D ∈ 𝓝[S] x)
    (hcross : ∀ x ∈ q '' stdSimplexBoundary 2, HasPLCrossingAt (frontier P) S x)
    (hdisk : ∀ x ∈ q '' stdSimplexBoundary 2, ∀ N ∈ 𝓝 x,
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E3),
        0 < r ∧ ContinuousOn g (ball c r) ∧ InjOn g (ball c r) ∧
          MapsTo g (ball c r) (S ∩ N) ∧ g c = x) :
    ∃ U : Set E3, IsOpen U ∧ D ⊆ U ∧ U ∩ S ∩ P ⊆ D := by
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hDc : IsClosed D := (IsPLBall.isPolyhedron ⟨q, hq⟩).isClosed
  have hPreg : closure (interior P) = P := hP.closure_interior_of_finrank (by simp)
  have hDimg : q '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) = D := hq.image_eq
  have hlocal : ∀ x ∈ D, ∃ V : Set E3, IsOpen V ∧ x ∈ V ∧ V ∩ S ∩ P ⊆ D := by
    intro x hxD
    by_cases hxJ : x ∈ q '' stdSimplexBoundary 2
    · obtain ⟨V, φ, ρ, hV, hxV, hρ, hφ, hφx, hloc⟩ :=
        (hcross x hxJ).symm.exists_sideChart (hdisk x hxJ) hPc (by rw [hPreg]; exact hDP hxD)
      refine ⟨V, hV, hxV, ?_⟩
      set ψ := Function.invFunOn φ V with hψdef
      have hψφ : ∀ y ∈ V, ψ (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
      have hφψ : ∀ z ∈ ball (0 : ℝ × ℝ × ℝ) ρ, φ (ψ z) = z := fun z hz =>
        hφ.bijOn.invOn_invFunOn.2 hz
      have hψV : ∀ z ∈ ball (0 : ℝ × ℝ × ℝ) ρ, ψ z ∈ V := fun z hz => hφ.symm.bijOn.mapsTo hz
      have hψc : ContinuousOn ψ (ball (0 : ℝ × ℝ × ℝ) ρ) :=
        hφ.isPiecewiseAffineOn_invFunOn.continuousOn
      set H₀ : Set (ℝ × ℝ × ℝ) := ball 0 ρ ∩ {z | z.2.2 = 0 ∧ 0 < z.2.1} with hH₀def
      have hH₀conn : IsPreconnected H₀ := by
        refine (Convex.inter (convex_ball 0 ρ) ?_).isPreconnected
        intro a ha b hb s t hs ht hst
        change (s • a + t • b).2.2 = 0 ∧ 0 < (s • a + t • b).2.1
        refine ⟨?_, ?_⟩
        · simp [ha.1, hb.1]
        · have h1 : (s • a + t • b).2.1 = s * a.2.1 + t * b.2.1 := by simp
          rw [h1]
          rcases eq_or_lt_of_le hs with hs0 | hs0
          · subst hs0
            have ht1 : t = 1 := by linarith
            subst ht1
            simpa using hb.2
          · have := mul_pos hs0 ha.2
            nlinarith [mul_nonneg ht hb.2.le]
      set G : Set E3 := {y | ∀ᶠ y' in 𝓝 y, y' ∈ S → y' ∈ D} with hGdef
      have hGo : IsOpen G := isOpen_setOfPred_eventually_nhds
      have huo : IsOpen (φ '' (V ∩ G)) :=
        hφ.isOpen_image_of_isOpen isOpen_ball (hV.inter hGo) inter_subset_left
      have hvo : IsOpen (φ '' (V \ D)) :=
        hφ.isOpen_image_of_isOpen isOpen_ball (hV.sdiff hDc) sdiff_subset
      have hcover : H₀ ⊆ φ '' (V ∩ G) ∪ φ '' (V \ D) := by
        intro z hz
        have hyV := hψV z hz.1
        by_cases hyD : ψ z ∈ D
        · refine Or.inl ⟨ψ z, ⟨hyV, ?_⟩, hφψ z hz.1⟩
          have hyJ : ψ z ∉ q '' stdSimplexBoundary 2 := by
            intro hyJ
            rw [← hDfr] at hyJ
            have := ((hloc (ψ z) hyV).2.1).mp hyJ.2
            rw [hφψ z hz.1] at this
            exact absurd this (ne_of_gt hz.2.2)
          have hnhds := hint (ψ z) ⟨hyD, hyJ⟩
          obtain ⟨W, hW, hWD⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
          filter_upwards [hW] with y' hy' hy'S
          exact hWD ⟨hy', hy'S⟩
        · exact Or.inr ⟨ψ z, ⟨hyV, hyD⟩, hφψ z hz.1⟩
      have hdisj : H₀ ∩ (φ '' (V ∩ G) ∩ φ '' (V \ D)) = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr ?_
        rintro z ⟨hz, ⟨y, ⟨hyV, hyG⟩, rfl⟩, ⟨y', ⟨hy'V, hy'D⟩, hyy'⟩⟩
        have hyy : y' = y := hφ.bijOn.injOn hy'V hyV hyy'
        rw [hyy] at hy'D
        have hyS : y ∈ S := ((hloc y hyV).1).mpr hz.2.1
        exact hy'D (hyG.self_of_nhds hyS)
      have hne : (H₀ ∩ φ '' (V ∩ G)).Nonempty := by
        have hxcl := mem_closure_sdiff_image_stdSimplexBoundary hq hxJ
        obtain ⟨y, hyV, hyD, hyJ⟩ := mem_closure_iff.mp hxcl V hV hxV
        have hyP : y ∈ P := hDP hyD
        have hyfr : y ∉ frontier P := fun h => hyJ (by rw [← hDfr]; exact ⟨hyD, h⟩)
        have hyS : y ∈ S := hDS hyD
        have h1 := ((hloc y hyV).1).mp hyS
        have h2 : (φ y).2.1 ≠ 0 := fun h => hyfr (((hloc y hyV).2.1).mpr h)
        have h3 := ((hloc y hyV).2.2).mp hyP
        refine ⟨φ y, ⟨hφ.bijOn.mapsTo hyV, h1, lt_of_le_of_ne h3 (Ne.symm h2)⟩, y, ⟨hyV, ?_⟩,
          rfl⟩
        have hnhds := hint y ⟨hyD, hyJ⟩
        obtain ⟨W, hW, hWD⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
        filter_upwards [hW] with y' hy' hy'S
        exact hWD ⟨hy', hy'S⟩
      rcases isPreconnected_iff_subset_of_disjoint.mp hH₀conn _ _ huo hvo hcover hdisj with
        hsub | hsub
      · have hH₀D : ∀ z ∈ H₀, ψ z ∈ D := by
          intro z hz
          obtain ⟨y, ⟨hyV, hyG⟩, hyz⟩ := hsub hz
          have hyS : y ∈ S := ((hloc y hyV).1).mpr (by rw [hyz]; exact hz.2.1)
          have hyD : y ∈ D := hyG.self_of_nhds hyS
          rw [← hyz, hψφ y hyV]
          exact hyD
        rintro y ⟨⟨hyV, hyS⟩, hyP⟩
        have hz0 : (φ y).2.2 = 0 := ((hloc y hyV).1).mp hyS
        have hz1 : 0 ≤ (φ y).2.1 := ((hloc y hyV).2.2).mp hyP
        have hzball : φ y ∈ ball (0 : ℝ × ℝ × ℝ) ρ := hφ.bijOn.mapsTo hyV
        rcases eq_or_lt_of_le hz1 with h0 | hpos
        · have hcl : φ y ∈ closure H₀ := by
            have hcont : Continuous (fun t : ℝ => φ y + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) := by
              fun_prop
            have htend : Filter.Tendsto (fun t : ℝ => φ y + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)))
                (𝓝[>] 0) (𝓝 (φ y)) := by
              simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
            refine mem_closure_of_tendsto htend ?_
            filter_upwards [htend.eventually_mem (isOpen_ball.mem_nhds hzball),
              self_mem_nhdsWithin] with t htb ht
            refine ⟨htb, ?_, ?_⟩
            · simp [hz0]
            · have ht' : (0 : ℝ) < t := ht
              simp [← h0, ht']
          have hmem := (hψc.continuousAt (isOpen_ball.mem_nhds hzball)).continuousWithinAt
            |>.mem_closure_image hcl
          have hsubD : ψ '' H₀ ⊆ D := by
            rintro _ ⟨z, hz, rfl⟩
            exact hH₀D z hz
          have := closure_minimal hsubD hDc hmem
          rwa [hψφ y hyV] at this
        · have := hH₀D (φ y) ⟨hzball, hz0, hpos⟩
          rwa [hψφ y hyV] at this
      · obtain ⟨z, hz, hzu⟩ := hne
        obtain ⟨y, ⟨hyV, hyD⟩, hyz⟩ := hsub hz
        obtain ⟨y', ⟨hy'V, hy'G⟩, hy'z⟩ := hzu
        have hyy : y' = y := hφ.bijOn.injOn hy'V hyV (hy'z.trans hyz.symm)
        have hyS : y' ∈ S := ((hloc y' hy'V).1).mpr (by rw [hy'z]; exact hz.2.1)
        exact absurd (hyy ▸ hy'G.self_of_nhds hyS) hyD
    · obtain ⟨W, hW, hWD⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hint x ⟨hxD, hxJ⟩)
      obtain ⟨V, hVW, hV, hxV⟩ := _root_.mem_nhds_iff.mp hW
      exact ⟨V, hV, hxV, fun y hy => hWD ⟨hVW hy.1.1, hy.1.2⟩⟩
  choose! V hV hxV hVD using hlocal
  refine ⟨⋃ x ∈ D, V x, isOpen_biUnion fun x hx => hV x hx,
    fun x hx => mem_iUnion₂.mpr ⟨x, hx, hxV x hx⟩, ?_⟩
  rintro y ⟨⟨hyU, hyS⟩, hyP⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hyU
  exact hVD x hx ⟨⟨hyx, hyS⟩, hyP⟩

theorem exists_isOpen_inter_inter_subset_of_isPLSphere {P S D Sph O : Set E3}
    (hP : IsPLBall 3 P) {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ P)
    (hDfr : D ∩ frontier P = q '' stdSimplexBoundary 2) (hSph : IsPLSphere 2 Sph) (hDSph : D ⊆ Sph)
    (hO : IsOpen O) (hDO : D ⊆ O) (hOS : O ∩ S = O ∩ Sph)
    (hcross : ∀ x ∈ q '' stdSimplexBoundary 2, HasPLCrossingAt (frontier P) S x) :
    ∃ U : Set E3, IsOpen U ∧ D ⊆ U ∧ U ∩ S ∩ P ⊆ D := by
  have hDS : D ⊆ S := fun x hx => by
    have h : x ∈ O ∩ Sph := ⟨hDO hx, hDSph hx⟩
    rw [← hOS] at h
    exact h.2
  have hEc : IsClosed (closure (Sph \ D)) := isClosed_closure
  have hDE : D ∩ closure (Sph \ D) = q '' stdSimplexBoundary 2 :=
    hSph.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDSph
  refine exists_isOpen_inter_inter_subset_of_hasPLCrossingAt hP hq hDP hDfr hDS ?_ hcross ?_
  · rintro x ⟨hxD, hxJ⟩
    have hxE : x ∉ closure (Sph \ D) := fun h => hxJ (hDE ▸ ⟨hxD, h⟩)
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨O ∩ (closure (Sph \ D))ᶜ, (hO.inter hEc.isOpen_compl).mem_nhds ⟨hDO hxD, hxE⟩, ?_⟩
    rintro y ⟨⟨hyO, hyE⟩, hyS⟩
    have hySph : y ∈ O ∩ Sph := by
      rw [← hOS]
      exact ⟨hyO, hyS⟩
    by_contra hyD
    exact hyE (subset_closure ⟨hySph.2, hyD⟩)
  · intro x hxJ N hN
    have hxD : x ∈ D := by
      rw [← hDfr] at hxJ
      exact hxJ.1
    obtain ⟨W, hW, hxW, U, hU, ⟨e⟩⟩ := hSph.exists_isOpen_inter_homeomorph_of_two (hDSph hxD)
    have hNO : N ∩ O ∈ 𝓝 x := Filter.inter_mem hN (hO.mem_nhds (hDO hxD))
    obtain ⟨N', hN'sub, hN'o, hxN'⟩ := _root_.mem_nhds_iff.mp hNO
    set c : EuclideanSpace ℝ (Fin 2) := (e ⟨x, hxW, hDSph hxD⟩ : EuclideanSpace ℝ (Fin 2))
      with hcdef
    have hpre : IsOpen {v : U | ((e.symm v : ↥(W ∩ Sph)) : E3) ∈ N'} :=
      hN'o.preimage (continuous_subtype_val.comp e.symm.continuous)
    obtain ⟨V₀, hV₀, hV₀eq⟩ := isOpen_induced_iff.mp hpre
    have hcU : c ∈ U := (e ⟨x, hxW, hDSph hxD⟩).2
    have hcV₀ : c ∈ V₀ := by
      have hmem : (e ⟨x, hxW, hDSph hxD⟩ : U) ∈ {v : U | ((e.symm v : ↥(W ∩ Sph)) : E3) ∈ N'} := by
        change ((e.symm (e ⟨x, hxW, hDSph hxD⟩) : ↥(W ∩ Sph)) : E3) ∈ N'
        rw [e.symm_apply_apply]
        exact hxN'
      rw [← hV₀eq] at hmem
      exact hmem
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.inter hV₀) c ⟨hcU, hcV₀⟩
    classical
    let g : EuclideanSpace ℝ (Fin 2) → E3 := fun v =>
      if h : v ∈ U then ((e.symm ⟨v, h⟩ : ↥(W ∩ Sph)) : E3) else x
    have hgU : ∀ v (h : v ∈ U), g v = ((e.symm ⟨v, h⟩ : ↥(W ∩ Sph)) : E3) := fun v h => by
      simp only [g, dite_eq_left h]
    refine ⟨c, r, g, hr, ?_, ?_, ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have hsub : ball c r ⊆ U := fun v hv => (hball hv).1
      have heq : (ball c r).domRestrict g =
          fun v => ((e.symm (inclusion hsub v) : ↥(W ∩ Sph)) : E3) := by
        funext v
        exact hgU v.1 (hsub v.2)
      rw [heq]
      exact continuous_subtype_val.comp (e.symm.continuous.comp (continuous_inclusion hsub))
    · intro v hv v' hv' hvv
      have hvU := (hball hv).1
      have hv'U := (hball hv').1
      rw [hgU v hvU, hgU v' hv'U] at hvv
      have := e.symm.injective (Subtype.ext hvv)
      exact congrArg Subtype.val this
    · intro v hv
      have hvU := (hball hv).1
      have hvV₀ := (hball hv).2
      rw [hgU v hvU]
      have hmem : (⟨v, hvU⟩ : U) ∈ {v : U | ((e.symm v : ↥(W ∩ Sph)) : E3) ∈ N'} := by
        rw [← hV₀eq]
        exact hvV₀
      have hN' : ((e.symm ⟨v, hvU⟩ : ↥(W ∩ Sph)) : E3) ∈ N' := hmem
      have hSph' : ((e.symm ⟨v, hvU⟩ : ↥(W ∩ Sph)) : E3) ∈ Sph := (e.symm ⟨v, hvU⟩).2.2
      have hNO' := hN'sub hN'
      refine ⟨?_, hNO'.1⟩
      have h : ((e.symm ⟨v, hvU⟩ : ↥(W ∩ Sph)) : E3) ∈ O ∩ Sph := ⟨hNO'.2, hSph'⟩
      rw [← hOS] at h
      exact h.2
    · rw [hgU c hcU]
      have : (⟨c, hcU⟩ : U) = e ⟨x, hxW, hDSph hxD⟩ := rfl
      rw [this, e.symm_apply_apply]

end DifferentialGeometry.Topology.PiecewiseLinear
