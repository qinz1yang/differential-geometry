/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles
import DifferentialGeometry.Topology.PiecewiseLinear.CompressionDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLHomeomorphOn_comp_of_norm_eq {U : Set E3} {φ : E3 → ℝ × ℝ × ℝ} {ρ : ℝ}
    (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 ρ)) (L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ)
    (hL : ∀ z, ‖L z‖ = ‖z‖) : IsPLHomeomorphOn (fun y => L (φ y)) U (Metric.ball 0 ρ) := by
  have hball : (fun z => L z) '' Metric.ball (0 : ℝ × ℝ × ℝ) ρ = Metric.ball 0 ρ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_ball_zero_iff, hL]
      exact mem_ball_zero_iff.mp hz
    · intro z hz
      refine ⟨L.symm z, ?_, L.apply_symm_apply z⟩
      rw [mem_ball_zero_iff, ← hL, L.apply_symm_apply]
      exact mem_ball_zero_iff.mp hz
  have h := hφ.trans (isPLHomeomorphOn_linearEquiv L Metric.isOpen_ball)
  rw [hball] at h
  exact h

theorem side_of_frontier_plane_snd_snd {X U : Set E3} {x : E3} {φ : E3 → ℝ × ℝ × ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hxU : x ∈ U) (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 ρ))
    (hφx : φ x = 0) (hBU : ∀ y ∈ U, y ∈ frontier X ↔ (φ y).2.2 = 0) (hXc : IsClosed X)
    (hX : x ∈ closure (interior X)) :
    (∀ y ∈ U, y ∈ X ↔ 0 ≤ (φ y).2.2) ∨ ∀ y ∈ U, y ∈ X ↔ (φ y).2.2 ≤ 0 := by
  let S : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ :=
    { toFun := fun z => (z.1, z.2.2, z.2.1)
      invFun := fun z => (z.1, z.2.2, z.2.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hS : ∀ z, S z = (z.1, z.2.2, z.2.1) := fun _ => rfl
  have hSn : ∀ z, ‖S z‖ = ‖z‖ := fun z => by
    rw [hS, Prod.norm_def, Prod.norm_def, Prod.norm_def z, Prod.norm_def z.2, max_comm ‖z.2.2‖]
  have hφ' := isPLHomeomorphOn_comp_of_norm_eq hφ S hSn
  rcases side_of_frontier_plane hU hxU hφ' (by rw [hφx]; rfl)
    (fun y hy => by rw [hBU y hy, hS]) hXc hX with h | h
  · exact Or.inl fun y hy => by rw [h y hy, hS]
  · exact Or.inr fun y hy => by rw [h y hy, hS]

theorem exists_quadrantChart {P V D : Set E3} {q : (Fin 3 → ℝ) → E3} (hP : IsPLBall 3 P)
    (hV : IsPLBall 3 V) (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDV : D ⊆ frontier V) (hDP : D ∩ P = q '' stdSimplexBoundary 2) {p : E3}
    (hp : p ∈ q '' stdSimplexBoundary 2) (hcross : HasPLCrossingAt (frontier V) (frontier P) p) :
    ∃ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (r : ℝ), IsOpen U ∧ p ∈ U ∧ 0 < r ∧
      IsPLHomeomorphOn φ U (Metric.ball 0 r) ∧ φ p = 0 ∧ ∀ y ∈ U,
        (y ∈ frontier V ↔ (φ y).2.2 = 0) ∧ (y ∈ frontier P ↔ (φ y).2.1 = 0) ∧
        (y ∈ P ↔ 0 ≤ (φ y).2.1) ∧ (y ∈ V ↔ (φ y).2.2 ≤ 0) ∧
        (y ∈ D ↔ (φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) := by
  classical
  set J := q '' stdSimplexBoundary 2 with hJdef
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hΦ : IsPLSphere 2 (frontier V) := hV.isPLSphere_frontier
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hVc : IsClosed V := hV.isPolyhedron.isClosed
  have hPreg : closure (interior P) = P := hP.closure_interior_of_finrank (by simp)
  have hVreg : closure (interior V) = V := hV.closure_interior_of_finrank (by simp)
  have hpD : p ∈ D := hJD hp
  have hpP : p ∈ P := by
    have : p ∈ D ∩ P := by rw [hDP]; exact hp
    exact this.2
  have hpV : p ∈ V := hVc.frontier_subset (hDV hpD)
  obtain ⟨U, φ₀, ρ, hU, hpU, hρ, hφ₀, hφ₀p, hloc₀⟩ := hcross.exists_lineChart (hDV hpD)
    (hΦ.exists_isOpen_inter_homeomorph_of_two (hDV hpD)) hPc (by rw [hPreg]; exact hpP)
  obtain ⟨a, ha, hPa⟩ : ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ y ∈ U, y ∈ P ↔ 0 ≤ a * (φ₀ y).2.1 := by
    rcases side_of_frontier_plane hU hpU hφ₀ hφ₀p (fun y hy => (hloc₀ y hy).2) hPc
      (by rw [hPreg]; exact hpP) with h | h
    · exact ⟨1, Or.inl rfl, fun y hy => by rw [h y hy, one_mul]⟩
    · refine ⟨-1, Or.inr rfl, fun y hy => ?_⟩
      rw [h y hy]
      constructor <;> intro h' <;> linarith
  obtain ⟨b, hb, hVb⟩ : ∃ b : ℝ, (b = 1 ∨ b = -1) ∧ ∀ y ∈ U, y ∈ V ↔ b * (φ₀ y).2.2 ≤ 0 := by
    rcases side_of_frontier_plane_snd_snd hU hpU hφ₀ hφ₀p (fun y hy => (hloc₀ y hy).1) hVc
      (by rw [hVreg]; exact hpV) with h | h
    · refine ⟨-1, Or.inr rfl, fun y hy => ?_⟩
      rw [h y hy]
      constructor <;> intro h' <;> linarith
    · exact ⟨1, Or.inl rfl, fun y hy => by rw [h y hy, one_mul]⟩
  let L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ :=
    { toFun := fun z => (z.1, a * z.2.1, b * z.2.2)
      invFun := fun z => (z.1, a * z.2.1, b * z.2.2)
      map_add' := fun z w => by
        refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only [Prod.snd_add, Prod.fst_add] <;> ring
      map_smul' := fun c z => by
        refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only [Prod.smul_snd, Prod.smul_fst,
          smul_eq_mul, RingHom.id_apply] <;> ring
      left_inv := fun z => by
        refine Prod.ext rfl (Prod.ext ?_ ?_)
        · change a * (a * z.2.1) = z.2.1
          rcases ha with rfl | rfl <;> ring
        · change b * (b * z.2.2) = z.2.2
          rcases hb with rfl | rfl <;> ring
      right_inv := fun z => by
        refine Prod.ext rfl (Prod.ext ?_ ?_)
        · change a * (a * z.2.1) = z.2.1
          rcases ha with rfl | rfl <;> ring
        · change b * (b * z.2.2) = z.2.2
          rcases hb with rfl | rfl <;> ring }
  have hLz : ∀ z, L z = (z.1, a * z.2.1, b * z.2.2) := fun _ => rfl
  have habs : ∀ c : ℝ, (c = 1 ∨ c = -1) → ∀ t : ℝ, ‖c * t‖ = ‖t‖ := by
    intro c hc t
    rcases hc with rfl | rfl <;> simp
  have hLn : ∀ z, ‖L z‖ = ‖z‖ := fun z => by
    rw [hLz, Prod.norm_def, Prod.norm_def, Prod.norm_def z, Prod.norm_def z.2, habs a ha,
      habs b hb]
  set φ := fun y => L (φ₀ y) with hφdef
  have hφ : IsPLHomeomorphOn φ U (Metric.ball 0 ρ) := isPLHomeomorphOn_comp_of_norm_eq hφ₀ L hLn
  have hφ1 : ∀ y, (φ y).2.1 = a * (φ₀ y).2.1 := fun _ => rfl
  have hφ2 : ∀ y, (φ y).2.2 = b * (φ₀ y).2.2 := fun _ => rfl
  have hmul0 : ∀ c : ℝ, (c = 1 ∨ c = -1) → ∀ t : ℝ, c * t = 0 ↔ t = 0 := by
    intro c hc t
    rcases hc with rfl | rfl <;> constructor <;> intro h <;> linarith
  have hlocΦ : ∀ y ∈ U, y ∈ frontier V ↔ (φ y).2.2 = 0 := fun y hy => by
    rw [hφ2, hmul0 b hb, (hloc₀ y hy).1]
  have hlocS : ∀ y ∈ U, y ∈ frontier P ↔ (φ y).2.1 = 0 := fun y hy => by
    rw [hφ1, hmul0 a ha, (hloc₀ y hy).2]
  have hlocP : ∀ y ∈ U, y ∈ P ↔ 0 ≤ (φ y).2.1 := fun y hy => by rw [hφ1, hPa y hy]
  have hlocV : ∀ y ∈ U, y ∈ V ↔ (φ y).2.2 ≤ 0 := fun y hy => by rw [hφ2, hVb y hy]
  have hφp : φ p = 0 := by
    change L (φ₀ p) = 0
    rw [hφ₀p, map_zero]
  have hJfr : J ⊆ frontier P := by
    intro z hz
    have hzP : z ∈ P := by
      have : z ∈ D ∩ P := by rw [hDP]; exact hz
      exact this.2
    rw [hPc.frontier_eq]
    refine ⟨hzP, fun hzi => ?_⟩
    obtain ⟨w, hwP, hwD, hwJ⟩ := mem_closure_iff.mp
      (mem_closure_sdiff_image_stdSimplexBoundary hq hz) (interior P) isOpen_interior hzi
    exact hwJ (show w ∈ J by rw [← hDP]; exact ⟨hwD, interior_subset hwP⟩)
  have hDsub : ∀ y ∈ U, y ∈ D → (φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0 := by
    intro y hy hyD
    refine ⟨(hlocΦ y hy).mp (hDV hyD), ?_⟩
    by_contra hpos
    push Not at hpos
    have hyJ : y ∈ J := by
      rw [← hDP]
      exact ⟨hyD, (hlocP y hy).mpr hpos.le⟩
    have := (hlocS y hy).mp (hJfr hyJ)
    linarith
  have hDc : IsClosed D := (IsPLBall.isPolyhedron ⟨q, hq⟩).isClosed
  have hDint : ∀ x ∈ D \ J, ∀ᶠ y' in 𝓝 x, y' ∈ frontier V → y' ∈ D := by
    rintro x ⟨hxD, hxJ⟩
    have hDE : D ∩ closure (frontier V \ D) = J :=
      hΦ.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDV
    have hxE : x ∉ closure (frontier V \ D) := fun h => hxJ (hDE ▸ ⟨hxD, h⟩)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxE] with y' hy' hy'V
    by_contra hy'D
    exact hy' (subset_closure ⟨hy'V, hy'D⟩)
  set ψ := Function.invFunOn φ U with hψdef
  have hφψ : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, φ (ψ z) = z := fun z hz =>
    hφ.bijOn.invOn_invFunOn.2 hz
  have hψφ : ∀ y ∈ U, ψ (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
  have hψU : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, ψ z ∈ U := fun z hz =>
    hφ.bijOn.surjOn.mapsTo_invFunOn hz
  have hψc : ContinuousOn ψ (Metric.ball 0 ρ) := hφ.isPiecewiseAffineOn_invFunOn.continuousOn
  set H₀ : Set (ℝ × ℝ × ℝ) := Metric.ball 0 ρ ∩ {z | z.2.2 = 0 ∧ z.2.1 < 0} with hH₀def
  have hH₀conn : IsPreconnected H₀ := by
    refine (Convex.inter (convex_ball 0 ρ) ?_).isPreconnected
    intro a ha b hb s t hs ht hst
    change (s • a + t • b).2.2 = 0 ∧ (s • a + t • b).2.1 < 0
    refine ⟨?_, ?_⟩
    · simp [ha.1, hb.1]
    · have h1 : (s • a + t • b).2.1 = s * a.2.1 + t * b.2.1 := by simp
      rw [h1]
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · rw [← hs0] at hst ⊢
        have ht1 : t = 1 := by linarith
        rw [ht1]
        linarith [hb.2]
      · have h2 : s * a.2.1 < 0 := mul_neg_of_pos_of_neg hs0 ha.2
        have h3 : t * b.2.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hb.2.le
        linarith
  set G : Set E3 := {y | ∀ᶠ y' in 𝓝 y, y' ∈ frontier V → y' ∈ D} with hGdef
  have hGo : IsOpen G := isOpen_setOfPred_eventually_nhds
  have huo : IsOpen (φ '' (U ∩ G)) :=
    hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU.inter hGo) inter_subset_left
  have hvo : IsOpen (φ '' (U \ D)) :=
    hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU.sdiff hDc) sdiff_subset
  have hcover : H₀ ⊆ φ '' (U ∩ G) ∪ φ '' (U \ D) := by
    intro z hz
    have hyU := hψU z hz.1
    by_cases hyD : ψ z ∈ D
    · refine Or.inl ⟨ψ z, ⟨hyU, ?_⟩, hφψ z hz.1⟩
      have hyJ : ψ z ∉ J := by
        intro hyJ
        have := (hlocS (ψ z) hyU).mp (hJfr hyJ)
        rw [hφψ z hz.1] at this
        exact absurd this (ne_of_lt hz.2.2)
      exact hDint (ψ z) ⟨hyD, hyJ⟩
    · exact Or.inr ⟨ψ z, ⟨hyU, hyD⟩, hφψ z hz.1⟩
  have hdisj : H₀ ∩ (φ '' (U ∩ G) ∩ φ '' (U \ D)) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro z ⟨hz, ⟨y, ⟨hyU, hyG⟩, rfl⟩, ⟨y', ⟨hy'U, hy'D⟩, hyy'⟩⟩
    have hyy : y' = y := hφ.bijOn.injOn hy'U hyU hyy'
    rw [hyy] at hy'D
    have hyV : y ∈ frontier V := (hlocΦ y hyU).mpr hz.2.1
    exact hy'D (hyG.self_of_nhds hyV)
  have hne : (H₀ ∩ φ '' (U ∩ G)).Nonempty := by
    obtain ⟨y, hyU, hyD, hyJ⟩ := mem_closure_iff.mp
      (mem_closure_sdiff_image_stdSimplexBoundary hq hp) U hU hpU
    obtain ⟨h1, h2⟩ := hDsub y hyU hyD
    have h3 : (φ y).2.1 ≠ 0 := fun h => hyJ (show y ∈ J by
      rw [← hDP]
      exact ⟨hyD, (hlocP y hyU).mpr h.ge⟩)
    exact ⟨φ y, ⟨hφ.bijOn.mapsTo hyU, h1, lt_of_le_of_ne h2 h3⟩, y,
      ⟨hyU, hDint y ⟨hyD, hyJ⟩⟩, rfl⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp hH₀conn _ _ huo hvo hcover hdisj with
    hsub | hsub
  · have hH₀D : ∀ z ∈ H₀, ψ z ∈ D := by
      intro z hz
      obtain ⟨y, ⟨hyU, hyG⟩, hyz⟩ := hsub hz
      have hyV : y ∈ frontier V := (hlocΦ y hyU).mpr (by rw [hyz]; exact hz.2.1)
      rw [← hyz, hψφ y hyU]
      exact hyG.self_of_nhds hyV
    refine ⟨U, φ, ρ, hU, hpU, hρ, hφ, hφp, fun y hy => ⟨hlocΦ y hy, hlocS y hy, hlocP y hy,
      hlocV y hy, ⟨hDsub y hy, fun ⟨hz0, hz1⟩ => ?_⟩⟩⟩
    have hzball : φ y ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ := hφ.bijOn.mapsTo hy
    rcases eq_or_lt_of_le hz1 with h0 | hneg
    · have hcl : φ y ∈ closure H₀ := by
        have hcont : Continuous (fun t : ℝ => φ y + t • ((0 : ℝ), (-1 : ℝ), (0 : ℝ))) := by
          fun_prop
        have htend : Filter.Tendsto (fun t : ℝ => φ y + t • ((0 : ℝ), (-1 : ℝ), (0 : ℝ)))
            (𝓝[>] 0) (𝓝 (φ y)) := by
          simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
        refine mem_closure_of_tendsto htend ?_
        filter_upwards [htend.eventually_mem (Metric.isOpen_ball.mem_nhds hzball),
          self_mem_nhdsWithin] with t htb ht
        refine ⟨htb, ?_, ?_⟩
        · simp [hz0]
        · have ht' : (0 : ℝ) < t := ht
          simp [h0, ht']
      have hmem := (hψc.continuousAt (Metric.isOpen_ball.mem_nhds hzball)).continuousWithinAt
        |>.mem_closure_image hcl
      have hsubD : ψ '' H₀ ⊆ D := by
        rintro _ ⟨z, hz, rfl⟩
        exact hH₀D z hz
      have := closure_minimal hsubD hDc hmem
      rwa [hψφ y hy] at this
    · have := hH₀D (φ y) ⟨hzball, hz0, hneg⟩
      rwa [hψφ y hy] at this
  · obtain ⟨z, hz, hzu⟩ := hne
    obtain ⟨y, ⟨hyU, hyD⟩, hyz⟩ := hsub hz
    obtain ⟨y', ⟨hy'U, hy'G⟩, hy'z⟩ := hzu
    have hyy : y' = y := hφ.bijOn.injOn hy'U hyU (hy'z.trans hyz.symm)
    have hyV : y' ∈ frontier V := (hlocΦ y' hy'U).mpr (by rw [hy'z]; exact hz.2.1)
    exact absurd (hyy ▸ hy'G.self_of_nhds hyV) hyD

theorem IsPLHomeomorphOn.restrict_ball {U : Set E3} {φ : E3 → ℝ × ℝ × ℝ} {r r' : ℝ}
    (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 r)) (hU : IsOpen U) (hr' : r' ≤ r) :
    IsOpen (U ∩ φ ⁻¹' Metric.ball 0 r') ∧
      IsPLHomeomorphOn φ (U ∩ φ ⁻¹' Metric.ball 0 r') (Metric.ball 0 r') := by
  have hP₀ : IsOpen (U ∩ φ ⁻¹' Metric.ball 0 r') :=
    hφ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hsub : U ∩ φ ⁻¹' Metric.ball 0 r' ⊆ U := inter_subset_left
  have hballs : Metric.ball (0 : ℝ × ℝ × ℝ) r ∩ Metric.ball 0 r' = Metric.ball 0 r' :=
    inter_eq_right.mpr (Metric.ball_subset_ball hr')
  have himg : φ '' (U ∩ φ ⁻¹' Metric.ball 0 r') = Metric.ball (0 : ℝ × ℝ × ℝ) r' := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro z hz
      have hzr : z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r := Metric.ball_subset_ball hr' hz
      obtain ⟨x, hx, rfl⟩ := hφ.bijOn.surjOn hzr
      exact ⟨x, ⟨hx, hz⟩, rfl⟩
  have hinj : InjOn φ (U ∩ φ ⁻¹' Metric.ball 0 r') := hφ.bijOn.injOn.mono hsub
  have hb : BijOn φ (U ∩ φ ⁻¹' Metric.ball 0 r') (φ '' (U ∩ φ ⁻¹' Metric.ball 0 r')) :=
    hinj.bijOn_image
  rw [himg] at hb
  refine ⟨hP₀, hb, fun x hx => ?_, ?_⟩
  · have hw := (hφ.isPiecewiseAffineOn x (hsub hx)).inter_of_mem_nhds (hP₀.mem_nhds hx)
    rwa [inter_eq_right.mpr hsub] at hw
  · have hpa : IsPiecewiseAffineOn (Function.invFunOn φ U) (Metric.ball 0 r') := by
      intro y hy
      have h := (hφ.isPiecewiseAffineOn_invFunOn y
        (Metric.ball_subset_ball hr' hy)).inter_of_mem_nhds (Metric.isOpen_ball.mem_nhds hy)
      rwa [hballs] at h
    refine hpa.congr fun y hy => ?_
    rw [← himg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hinj.leftInvOn_invFunOn hx, hφ.bijOn.injOn.leftInvOn_invFunOn (hsub hx)]

theorem exists_sideCollar {P V D E E' F G : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hP : IsPLBall 3 P) (hV : IsPLBall 3 V) (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDV : D ⊆ frontier V) (hDP : D ∩ P = q '' stdSimplexBoundary 2)
    (hcross : ∀ p ∈ q '' stdSimplexBoundary 2, HasPLCrossingAt (frontier V) (frontier P) p)
    {qE : (Fin 3 → ℝ) → E3} (hqE : IsPLHomeomorphOn qE (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) E)
    (hqEJ : qE '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2)
    (hEE' : E ∪ E' = frontier P) (hEE'J : E ∩ E' = q '' stdSimplexBoundary 2)
    (hE'c : IsClosed E') (hF : IsClosed F) (hFD : Disjoint F D) (hG : IsOpen G)
    (hDG : q '' stdSimplexBoundary 2 ⊆ G) :
    ∃ (ρ : E3 × ℝ → E3) (A B : Set E3) (ε : ℝ),
      IsPLHomeomorphOn ρ ((q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) A ∧
      (∀ x ∈ q '' stdSimplexBoundary 2, ρ (x, 0) = x) ∧ A ⊆ E ∧ A ⊆ G ∧ IsPLBall 2 B ∧
      E = B ∪ A ∧ A ∩ B = ρ '' ((q '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}) ∧
      A ∩ D = q '' stdSimplexBoundary 2 ∧ A ∩ (frontier V ∪ F) ⊆ q '' stdSimplexBoundary 2 ∧
      (ε = 1 ∨ ε = -1) ∧ (∀ y ∈ A, y ∉ q '' stdSimplexBoundary 2 → (y ∈ V ↔ ε = -1)) ∧
      (∀ p ∈ q '' stdSimplexBoundary 2, ∃ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (r : ℝ),
        IsOpen U ∧ p ∈ U ∧ 0 < r ∧ IsPLHomeomorphOn φ U (Metric.ball 0 r) ∧ φ p = 0 ∧
        ∀ y ∈ U, (y ∈ D ∪ A ↔
          ((φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) ∨ ((φ y).2.1 = 0 ∧ 0 ≤ ε * (φ y).2.2)) ∧
          (y ∈ frontier P ∪ frontier V ∪ F ↔ (φ y).2.1 = 0 ∨ (φ y).2.2 = 0) ∧
          (y ∈ P ↔ 0 ≤ (φ y).2.1) ∧ (y ∈ V ↔ (φ y).2.2 ≤ 0)) ∧
      ∀ z ∈ (D ∪ ρ '' ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 (1 / 2))) \
        q '' stdSimplexBoundary 2, ∃ O : Set E3, IsOpen O ∧ z ∈ O ∧
          O ∩ (frontier P ∪ frontier V ∪ F) ⊆ D ∪ A := by
  classical
  set J := q '' stdSimplexBoundary 2 with hJdef
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hJF : ∀ x ∈ J, x ∉ F := fun x hx hxF => Set.disjoint_left.mp hFD hxF (hJD hx)
  have hJsph : IsPLSphere 1 J := hq.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hEc : IsClosed E := (IsPLBall.isPolyhedron ⟨qE, hqE⟩).isClosed
  have hES : E ⊆ frontier P := hEE' ▸ subset_union_left
  have hSP : frontier P ⊆ P := hPc.frontier_subset
  have hloc : ∀ p ∈ J, ∃ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (r : ℝ), IsOpen U ∧ p ∈ U ∧
      0 < r ∧ IsPLHomeomorphOn φ U (Metric.ball 0 r) ∧ φ p = 0 ∧ U ⊆ Fᶜ ∧ U ⊆ G ∧ ∀ y ∈ U,
        (y ∈ frontier V ↔ (φ y).2.2 = 0) ∧ (y ∈ frontier P ↔ (φ y).2.1 = 0) ∧
        (y ∈ P ↔ 0 ≤ (φ y).2.1) ∧ (y ∈ V ↔ (φ y).2.2 ≤ 0) ∧
        (y ∈ D ↔ (φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) := by
    intro p hp
    obtain ⟨U₀, φ, r₀, hU₀, hpU₀, hr₀, hφ₀, hφp, hq₀⟩ :=
      exists_quadrantChart hP hV hq hDV hDP hp (hcross p hp)
    have hopen : IsOpen (φ '' (U₀ ∩ (Fᶜ ∩ G))) :=
      hφ₀.isOpen_image_of_isOpen Metric.isOpen_ball (hU₀.inter (hF.isOpen_compl.inter hG))
        inter_subset_left
    have h0 : (0 : ℝ × ℝ × ℝ) ∈ φ '' (U₀ ∩ (Fᶜ ∩ G)) :=
      ⟨p, ⟨hpU₀, hJF p hp, hDG hp⟩, hφp⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
    have hr' : 0 < min r r₀ := lt_min hr hr₀
    obtain ⟨hUo, hφ'⟩ := hφ₀.restrict_ball hU₀ (min_le_right r r₀)
    have hsmall : ∀ y ∈ U₀ ∩ φ ⁻¹' Metric.ball 0 (min r r₀), y ∈ Fᶜ ∩ G := by
      intro y hy
      obtain ⟨y', ⟨hy'U, hy'FG⟩, hy'y⟩ :=
        hball (Metric.ball_subset_ball (min_le_left r r₀) hy.2)
      rw [hφ₀.bijOn.injOn hy'U hy.1 hy'y] at hy'FG
      exact hy'FG
    refine ⟨U₀ ∩ φ ⁻¹' Metric.ball 0 (min r r₀), φ, min r r₀, hUo,
      ⟨hpU₀, by rw [mem_preimage, hφp]; exact Metric.mem_ball_self hr'⟩, hr', hφ', hφp,
      fun y hy => (hsmall y hy).1, fun y hy => (hsmall y hy).2, fun y hy => hq₀ y hy.1⟩
  choose! Up φp rp hUp hpUp hrp hφpl hφpp hUpF hUpG hqp using hloc
  set Ocol := ⋃ p ∈ J, Up p with hOcoldef
  have hOcol : IsOpen Ocol := isOpen_biUnion fun p hp => hUp p hp
  have hJOcol : J ⊆ Ocol := fun p hp => mem_iUnion₂.mpr ⟨p, hp, hpUp p hp⟩
  have hOcolG : Ocol ⊆ G := iUnion₂_subset fun p hp => hUpG p hp
  have hOcolF : Ocol ⊆ Fᶜ := iUnion₂_subset fun p hp => hUpF p hp
  have hSPhi : ∀ y ∈ Ocol, y ∈ frontier P → y ∈ frontier V → y ∈ J := by
    intro y hy hyP hyV
    obtain ⟨p, hp, hyU⟩ := mem_iUnion₂.mp hy
    obtain ⟨h1, h2, h3, -, h5⟩ := hqp p hp y hyU
    have hw := h1.mp hyV
    have hv := h2.mp hyP
    have hyD : y ∈ D := h5.mpr ⟨hw, hv.le⟩
    rw [← hDP]
    exact ⟨hyD, h3.mpr hv.ge⟩
  have hUcol : E ∩ Ocol ∈ 𝓝ˢ[E] (qE '' stdSimplexBoundary 2) := by
    rw [hqEJ]
    exact mem_nhdsSetWithin.mpr ⟨Ocol, hOcol, hJOcol, fun y hy => ⟨hy.2, hy.1⟩⟩
  obtain ⟨A, B, ρ₀, -, hB, hAU, hEBA, hρ₀, hρ₀1, hAB, hAnhds, -⟩ :=
    hqE.exists_disk_boundary_collar hUcol
  rw [hqEJ] at hρ₀ hρ₀1 hAB hAnhds
  have hJpoly : IsPolyhedron (J ×ˢ Icc (0 : ℝ) 1) := hJsph.isPolyhedron.prod
    isHPolytope_Icc.isPolyhedron
  let aff : (E3 × ℝ) →ᵃ[ℝ] (E3 × ℝ) :=
    { toFun := fun w => (w.1, 1 - w.2)
      linear := (LinearMap.fst ℝ E3 ℝ).prod (-(LinearMap.snd ℝ E3 ℝ))
      map_vadd' := fun w v => by
        refine Prod.ext ?_ ?_
        · change v.1 + w.1 = v.1 + w.1
          rfl
        · change 1 - (v.2 + w.2) = -v.2 + (1 - w.2)
          ring }
  have hflip : IsPLHomeomorphOn (fun w : E3 × ℝ => (w.1, 1 - w.2)) (J ×ˢ Icc (0 : ℝ) 1)
      (J ×ˢ Icc (0 : ℝ) 1) := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJpoly
      (((isPiecewiseAffineOn_of_affine aff isOpen_univ).mono_of_isPolyhedron hJpoly
        (subset_univ _)).congr fun _ _ => rfl) ?_
    refine ⟨fun w hw => ⟨hw.1, by linarith [hw.2.2], by linarith [hw.2.1]⟩,
      fun w _ w' _ h => ?_, fun w hw => ⟨(w.1, 1 - w.2),
        ⟨hw.1, by linarith [hw.2.2], by linarith [hw.2.1]⟩, by simp⟩⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    exact Prod.ext h1 (by linarith)
  set ρ : E3 × ℝ → E3 := fun w => ρ₀ (w.1, 1 - w.2) with hρdef
  have hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) A := hflip.trans hρ₀
  have hρ0 : ∀ x ∈ J, ρ (x, 0) = x := fun x hx => by
    change ρ₀ (x, 1 - 0) = x
    rw [sub_zero]
    exact hρ₀1 x hx
  have hAB' : A ∩ B = ρ '' (J ×ˢ {(1 : ℝ)}) := by
    rw [hAB]
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      refine ⟨(x, 1), ⟨hx, rfl⟩, ?_⟩
      change ρ₀ (x, 1 - 1) = ρ₀ (x, t)
      rw [ht0, sub_self]
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht1 : t = 1 := ht
      refine ⟨(x, 0), ⟨hx, rfl⟩, ?_⟩
      change ρ₀ (x, 0) = ρ₀ (x, 1 - t)
      rw [ht1, sub_self]
  have hAE : A ⊆ E := fun y hy => (hAU hy).1
  have hAOcol : A ⊆ Ocol := fun y hy => (hAU hy).2
  have hJA : J ⊆ A := fun x hx => by
    rw [← hρ0 x hx]
    exact hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  have hAD : A ∩ D = J := by
    apply Subset.antisymm
    · rintro y ⟨hyA, hyD⟩
      rw [← hDP]
      exact ⟨hyD, hSP (hES (hAE hyA))⟩
    · exact fun x hx => ⟨hJA hx, hJD hx⟩
  have hAVF : A ∩ (frontier V ∪ F) ⊆ J := by
    rintro y ⟨hyA, hyV | hyF⟩
    · exact hSPhi y (hAOcol hyA) (hES (hAE hyA)) hyV
    · exact absurd hyF (hOcolF (hAOcol hyA))
  have hAne : ∀ y ∈ A, y ∉ J → ∃ x ∈ J, ∃ t ∈ Ioc (0 : ℝ) 1, y = ρ (x, t) := by
    intro y hy hyJ
    rw [← hρ.image_eq] at hy
    obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hy
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · have ht0 : t = 0 := h0.symm
      exact absurd (show ρ (x, t) ∈ J by rw [ht0, hρ0 x hx]; exact hx) hyJ
    · exact ⟨x, hx, t, ⟨h0, ht.2⟩, rfl⟩
  set Aop := ρ '' (J ×ˢ Ioc (0 : ℝ) 1) with hAopdef
  have hAopsub : Aop ⊆ A := image_mono (prod_mono Subset.rfl Ioc_subset_Icc_self) |>.trans
    hρ.image_eq.subset
  have hAopJ : ∀ y ∈ Aop, y ∉ J := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ hJ
    obtain ⟨x', hx', hx'e⟩ : ∃ x' ∈ J, ρ (x', 0) = ρ (x, t) := ⟨ρ (x, t), hJ, hρ0 _ hJ⟩
    have h := hρ.bijOn.injOn ⟨hx', le_rfl, zero_le_one⟩ ⟨hx, ht.1.le, ht.2⟩ hx'e
    have := congrArg Prod.snd h
    simp only at this
    linarith [ht.1]
  have hAopc : IsPreconnected Aop :=
    (hJsph.isConnected.isPreconnected.prod isPreconnected_Ioc).image _
      (hρ.isPiecewiseAffineOn.continuousOn.mono (prod_mono Subset.rfl Ioc_subset_Icc_self))
  have hAopfr : Disjoint Aop (frontier V) := Set.disjoint_left.mpr fun y hy hyV =>
    hAopJ y hy (hAVF ⟨hAopsub hy, Or.inl hyV⟩)
  obtain ⟨ε, hε, hεV⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ y ∈ A, y ∉ J → (y ∈ V ↔ ε = -1) := by
    by_cases hex : ∃ y ∈ Aop, y ∈ V
    · obtain ⟨y₀, hy₀, hy₀V⟩ := hex
      have hsub := IsPreconnected.subset_of_disjoint_frontier hAopc ⟨y₀, hy₀, hy₀V⟩ hAopfr
      refine ⟨-1, Or.inr rfl, fun y hy hyJ => ⟨fun _ => rfl, fun _ => ?_⟩⟩
      obtain ⟨x, hx, t, ht, rfl⟩ := hAne y hy hyJ
      exact hsub ⟨(x, t), ⟨hx, ht⟩, rfl⟩
    · push Not at hex
      refine ⟨1, Or.inl rfl, fun y hy hyJ => ⟨fun hyV => ?_, fun h => by norm_num at h⟩⟩
      obtain ⟨x, hx, t, ht, rfl⟩ := hAne y hy hyJ
      exact absurd hyV (hex _ ⟨(x, t), ⟨hx, ht⟩, rfl⟩)
  obtain ⟨OA, hOA, hJOA, hOAE⟩ := mem_nhdsSetWithin.mp hAnhds
  have hJV : J ⊆ frontier V := hJD.trans hDV
  have hBc : IsClosed B := hB.isPolyhedron.isClosed
  refine ⟨ρ, A, B, ε, hρ, hρ0, hAE, hAOcol.trans hOcolG, hB, hEBA, hAB', hAD, hAVF, hε, hεV,
    fun p hp => ?_, fun z hz => ?_⟩
  · have hU := hUp p hp
    have hpU := hpUp p hp
    have hφ := hφpl p hp
    have hφ0 := hφpp p hp
    have hopen : IsOpen (φp p '' (Up p ∩ OA)) :=
      hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU.inter hOA) inter_subset_left
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp hopen 0 ⟨p, ⟨hpU, hJOA hp⟩, hφ0⟩
    have hr' : 0 < min r₁ (rp p) := lt_min hr₁ (hrp p hp)
    obtain ⟨hU'o, hφ'⟩ := hφ.restrict_ball hU (min_le_right r₁ (rp p))
    set U' := Up p ∩ φp p ⁻¹' Metric.ball 0 (min r₁ (rp p)) with hU'def
    have hsmall : ∀ y ∈ U', y ∈ OA := by
      intro y hy
      obtain ⟨y', ⟨hy'U, hy'A⟩, hy'y⟩ :=
        hball₁ (Metric.ball_subset_ball (min_le_left r₁ (rp p)) hy.2)
      rw [hφ.bijOn.injOn hy'U hy.1 hy'y] at hy'A
      exact hy'A
    have hpU' : p ∈ U' := ⟨hpU, by rw [mem_preimage, hφ0]; exact Metric.mem_ball_self hr'⟩
    have hAside : ∀ y ∈ Up p, y ∈ A → y ∉ J → (φp p y).2.1 = 0 ∧ 0 < ε * (φp p y).2.2 := by
      intro y hyU hyA hyJ
      obtain ⟨h1, h2, -, h4, -⟩ := hqp p hp y hyU
      have hv : (φp p y).2.1 = 0 := h2.mp (hES (hAE hyA))
      have hVε := hεV y hyA hyJ
      have hw0 : (φp p y).2.2 ≠ 0 := fun hw => hyJ (hAVF ⟨hyA, Or.inl (h1.mpr hw)⟩)
      refine ⟨hv, ?_⟩
      rcases hε with hε1 | hε1
      · have hnV : y ∉ V := fun hyV => by
          have h := hVε.mp hyV
          rw [hε1] at h
          norm_num at h
        have hw : 0 < (φp p y).2.2 := lt_of_not_ge fun h => hnV (h4.mpr h)
        rw [hε1]
        linarith
      · have hyV : y ∈ V := hVε.mpr hε1
        have hw : (φp p y).2.2 < 0 := lt_of_le_of_ne (h4.mp hyV) hw0
        rw [hε1]
        linarith
    set ψ := Function.invFunOn (φp p) (Up p) with hψdef
    have hψc : ContinuousOn ψ (Metric.ball 0 (rp p)) := hφ.isPiecewiseAffineOn_invFunOn.continuousOn
    have hφψ : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (rp p), φp p (ψ z) = z := fun z hz =>
      hφ.bijOn.invOn_invFunOn.2 hz
    have hψφ : ∀ y ∈ Up p, ψ (φp p y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
    have hψU : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (rp p), ψ z ∈ Up p := fun z hz =>
      hφ.bijOn.surjOn.mapsTo_invFunOn hz
    have hrr : Metric.ball (0 : ℝ × ℝ × ℝ) (min r₁ (rp p)) ⊆ Metric.ball 0 (rp p) :=
      Metric.ball_subset_ball (min_le_right _ _)
    set H : Set (ℝ × ℝ × ℝ) := Metric.ball 0 (min r₁ (rp p)) ∩
      {z | z.2.1 = 0 ∧ 0 < ε * z.2.2} with hHdef
    have hHc : IsPreconnected H := by
      refine (Convex.inter (convex_ball 0 _) ?_).isPreconnected
      intro a ha b hb s t hs ht hst
      refine ⟨?_, ?_⟩
      · change s * a.2.1 + t * b.2.1 = 0
        rw [ha.1, hb.1]
        ring
      · change 0 < ε * (s * a.2.2 + t * b.2.2)
        have heq : ε * (s * a.2.2 + t * b.2.2) = s * (ε * a.2.2) + t * (ε * b.2.2) := by ring
        rw [heq]
        rcases eq_or_lt_of_le hs with hs0 | hs0
        · rw [← hs0] at hst ⊢
          have ht1 : t = 1 := by linarith
          rw [ht1]
          linarith [hb.2]
        · have h1 : 0 < s * (ε * a.2.2) := mul_pos hs0 ha.2
          have h2 : 0 ≤ t * (ε * b.2.2) := mul_nonneg ht hb.2.le
          linarith
    have hψH : ∀ z ∈ H, ψ z ∈ frontier P ∧ ψ z ∉ J := by
      intro z hz
      have hzr := hrr hz.1
      obtain ⟨h1, h2, -, -, -⟩ := hqp p hp (ψ z) (hψU z hzr)
      refine ⟨h2.mpr (by rw [hφψ z hzr]; exact hz.2.1), fun hJ => ?_⟩
      have hw := h1.mp (hJV hJ)
      rw [hφψ z hzr] at hw
      have := hz.2.2
      rw [hw, mul_zero] at this
      exact lt_irrefl 0 this
    have hsplitH : ψ '' H ⊆ E'ᶜ ∨ ψ '' H ⊆ Eᶜ := by
      refine isPreconnected_iff_subset_of_disjoint.mp
        (hHc.image ψ (hψc.mono fun z hz => hrr hz.1)) E'ᶜ Eᶜ hE'c.isOpen_compl
        hEc.isOpen_compl ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        by_cases h1 : ψ z ∈ E
        · exact Or.inl fun h2 => (hψH z hz).2 (by rw [← hEE'J]; exact ⟨h1, h2⟩)
        · exact Or.inr h1
      · refine eq_empty_iff_forall_notMem.mpr ?_
        rintro _ ⟨⟨z, hz, rfl⟩, h1, h2⟩
        have hS := (hψH z hz).1
        rw [← hEE'] at hS
        rcases hS with h | h
        · exact h2 h
        · exact h1 h
    have hHE : ψ '' H ⊆ E'ᶜ := by
      rcases hsplitH with h | h
      · exact h
      · exfalso
        have hcw : ContinuousWithinAt (fun t : ℝ => ρ (p, t)) (Icc (0 : ℝ) 1) 0 := by
          have hf : ContinuousWithinAt (fun t : ℝ => (p, t)) (Icc (0 : ℝ) 1) 0 :=
            (by fun_prop : Continuous fun t : ℝ => (p, t)).continuousWithinAt
          have hmaps : MapsTo (fun t : ℝ => (p, t)) (Icc (0 : ℝ) 1) (J ×ˢ Icc (0 : ℝ) 1) :=
            fun t ht => ⟨hp, ht⟩
          have h1 : ContinuousWithinAt ρ (J ×ˢ Icc (0 : ℝ) 1) ((fun t : ℝ => (p, t)) 0) :=
            hρ.isPiecewiseAffineOn.continuousOn _ ⟨hp, le_rfl, zero_le_one⟩
          exact ContinuousWithinAt.comp (f := fun t : ℝ => (p, t)) (x := 0) h1 hf hmaps
        obtain ⟨e, he, hOe⟩ := Metric.mem_nhds_iff.mp (hU'o.mem_nhds hpU')
        obtain ⟨δ, hδ, hδe⟩ := Metric.continuousWithinAt_iff.mp hcw e he
        set t₀ := min (δ / 2) 1 with ht₀def
        have ht₀pos : 0 < t₀ := lt_min (half_pos hδ) one_pos
        have ht₀1 : t₀ ≤ 1 := min_le_right _ _
        have ht₀δ : t₀ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
        have hmem := hδe (x := t₀) ⟨ht₀pos.le, ht₀1⟩ (by
          rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]
          exact ht₀δ)
        have hρp : ρ (p, 0) = p := hρ0 p hp
        rw [hρp] at hmem
        have hy₀U : ρ (p, t₀) ∈ U' := hOe hmem
        have hy₀A : ρ (p, t₀) ∈ A := hρ.bijOn.mapsTo ⟨hp, ht₀pos.le, ht₀1⟩
        have hy₀J : ρ (p, t₀) ∉ J := hAopJ _ ⟨(p, t₀), ⟨hp, ht₀pos, ht₀1⟩, rfl⟩
        obtain ⟨hv, hw⟩ := hAside _ hy₀U.1 hy₀A hy₀J
        have hz₀ : φp p (ρ (p, t₀)) ∈ H := ⟨hy₀U.2, hv, hw⟩
        have := h ⟨_, hz₀, hψφ _ hy₀U.1⟩
        exact this (hAE hy₀A)
    refine ⟨U', φp p, min r₁ (rp p), hU'o, hpU', hr', hφ', hφ0, fun y hy => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqp p hp y hy.1
    refine ⟨⟨fun hyDA => ?_, fun hbent => ?_⟩, ⟨fun hT => ?_, fun hT => ?_⟩, h3, h4⟩
    · rcases hyDA with hyD | hyA
      · exact Or.inl (h5.mp hyD)
      · by_cases hyJ : y ∈ J
        · have hw : (φp p y).2.2 = 0 := h1.mp (hJV hyJ)
          exact Or.inr ⟨h2.mp (hES (hAE hyA)), by rw [hw, mul_zero]⟩
        · obtain ⟨hv, hw⟩ := hAside y hy.1 hyA hyJ
          exact Or.inr ⟨hv, hw.le⟩
    · rcases hbent with hb | ⟨hv, hw⟩
      · exact Or.inl (h5.mpr hb)
      · rcases eq_or_lt_of_le hw with hw0 | hw0
        · have hw' : (φp p y).2.2 = 0 := by
            rcases hε with h | h <;> rw [h] at hw0 <;> linarith
          exact Or.inl (h5.mpr ⟨hw', hv.le⟩)
        · have hyH : φp p y ∈ H := ⟨hy.2, hv, hw0⟩
          have hyE' : y ∉ E' := by
            have := hHE ⟨_, hyH, hψφ y hy.1⟩
            exact this
          have hyS : y ∈ frontier P := h2.mpr hv
          rw [← hEE'] at hyS
          have hyE : y ∈ E := hyS.resolve_right hyE'
          exact Or.inr (hOAE ⟨hsmall y hy, hyE⟩)
    · rcases hT with (hyP | hyV) | hyF
      · exact Or.inl (h2.mp hyP)
      · exact Or.inr (h1.mp hyV)
      · exact absurd hyF (hUpF p hp hy.1)
    · rcases hT with hv | hw
      · exact Or.inl (Or.inl (h2.mpr hv))
      · exact Or.inl (Or.inr (h1.mpr hw))
  · obtain ⟨hzDA, hzJ⟩ := hz
    rcases hzDA with hzD | ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    · have hDE : D ∩ closure (frontier V \ D) = J :=
        hV.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDV
      refine ⟨(closure (frontier V \ D))ᶜ ∩ (frontier P ∪ F)ᶜ,
        isClosed_closure.isOpen_compl.inter (isClosed_frontier.union hF).isOpen_compl,
        ⟨fun h => hzJ (hDE ▸ ⟨hzD, h⟩), ?_⟩, ?_⟩
      · rintro (hzP | hzF)
        · exact hzJ (by rw [← hDP]; exact ⟨hzD, hSP hzP⟩)
        · exact Set.disjoint_left.mp hFD hzF hzD
      · rintro y ⟨⟨hy1, hy2⟩, hyT⟩
        rcases hyT with (hyP | hyV) | hyF
        · exact absurd (Or.inl hyP) hy2
        · by_contra hyD
          exact hy1 (subset_closure ⟨hyV, fun h => hyD (Or.inl h)⟩)
        · exact absurd (Or.inr hyF) hy2
    · have hzA : ρ (x, t) ∈ A := hρ.bijOn.mapsTo ⟨hx, ht.1, ht.2.trans (by norm_num)⟩
      refine ⟨(B ∪ E' ∪ frontier V ∪ F)ᶜ,
        (((hBc.union hE'c).union isClosed_frontier).union hF).isOpen_compl, ?_, ?_⟩
      · rintro (((hzB | hzE') | hzV) | hzF)
        · have hmem : ρ (x, t) ∈ A ∩ B := ⟨hzA, hzB⟩
          rw [hAB'] at hmem
          obtain ⟨⟨x', t'⟩, ⟨hx', ht'⟩, heq⟩ := hmem
          have ht'1 : t' = 1 := ht'
          have h := hρ.bijOn.injOn ⟨hx', by rw [ht'1]; exact ⟨zero_le_one, le_rfl⟩⟩
            ⟨hx, ht.1, ht.2.trans (by norm_num)⟩ heq
          have := congrArg Prod.snd h
          simp only at this
          linarith [ht.2]
        · exact hzJ (by rw [← hEE'J]; exact ⟨hAE hzA, hzE'⟩)
        · exact hzJ (hAVF ⟨hzA, Or.inl hzV⟩)
        · exact hzJ (hAVF ⟨hzA, Or.inr hzF⟩)
      · rintro y ⟨hyO, hyT⟩
        have hyB : y ∉ B := fun h => hyO (Or.inl (Or.inl (Or.inl h)))
        have hyE' : y ∉ E' := fun h => hyO (Or.inl (Or.inl (Or.inr h)))
        have hyV : y ∉ frontier V := fun h => hyO (Or.inl (Or.inr h))
        have hyF : y ∉ F := fun h => hyO (Or.inr h)
        rcases hyT with (hyP | hyV') | hyF'
        · rw [← hEE'] at hyP
          have hyE : y ∈ E := hyP.resolve_right hyE'
          rw [hEBA] at hyE
          exact Or.inr (hyE.resolve_left hyB)
        · exact absurd hyV' hyV
        · exact absurd hyF' hyF

end DifferentialGeometry.Topology.PiecewiseLinear
