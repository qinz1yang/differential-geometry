/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LocalManifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Chart

variable {E : Type*} [TopologicalSpace E]

theorem exists_ball_chart_of_homeomorph_isOpen {M : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (ψ : M ≃ₜ U) {y : E} (hy : y ∈ M) {N : Set E} (hN : N ∈ 𝓝[M] y) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
      0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
        MapsTo g (Metric.ball c r) (M ∩ N) ∧ g c = y := by
  classical
  let g : EuclideanSpace ℝ (Fin 2) → E := fun w =>
    if hw : w ∈ U then ((ψ.symm ⟨w, hw⟩ : M) : E) else y
  have hgU : ∀ w (hw : w ∈ U), g w = ((ψ.symm ⟨w, hw⟩ : M) : E) := fun w hw => dite_eq_left hw
  have hgc : ContinuousOn g U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : U.domRestrict g = fun w : U => ((ψ.symm w : M) : E) :=
      funext fun w => hgU w w.2
    rw [heq]
    exact continuous_subtype_val.comp ψ.symm.continuous
  have hcU : (ψ ⟨y, hy⟩ : EuclideanSpace ℝ (Fin 2)) ∈ U := (ψ ⟨y, hy⟩).2
  have hgcy : g (ψ ⟨y, hy⟩) = y := by
    rw [hgU _ hcU, Subtype.coe_eta, ψ.symm_apply_apply]
  obtain ⟨V, hV, hVN⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hN
  have hpre : U ∩ g ⁻¹' V ∈ 𝓝 (ψ ⟨y, hy⟩ : EuclideanSpace ℝ (Fin 2)) :=
    Filter.inter_mem (hU.mem_nhds hcU)
      ((hgc.continuousAt (hU.mem_nhds hcU)).preimage_mem_nhds (by rw [hgcy]; exact hV))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨_, r, g, hr, hgc.mono (hball.trans inter_subset_left), ?_, ?_, hgcy⟩
  · intro w hw w' hw' hww
    rw [hgU w (hball hw).1, hgU w' (hball hw').1] at hww
    exact congrArg Subtype.val (ψ.symm.injective (Subtype.ext hww))
  · intro w hw
    have hgw : g w ∈ M := by
      rw [hgU w (hball hw).1]
      exact (ψ.symm ⟨w, (hball hw).1⟩).2
    exact ⟨hgw, hVN ⟨(hball hw).2, hgw⟩⟩

theorem image_mem_nhdsWithin_of_homeomorph {M : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))}
    (ψ : M ≃ₜ U) {O : Set (EuclideanSpace ℝ (Fin 2))} (hO : IsOpen O)
    {g : EuclideanSpace ℝ (Fin 2) → E} (hg : ContinuousOn g O) (hgi : InjOn g O)
    (hgM : MapsTo g O M) {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ O) :
    g '' O ∈ 𝓝[M] (g z) := by
  let F : O → EuclideanSpace ℝ (Fin 2) := fun w =>
    (ψ ⟨g w, hgM w.2⟩ : EuclideanSpace ℝ (Fin 2))
  have hF : Continuous F :=
    continuous_subtype_val.comp (ψ.continuous.comp
      ((continuousOn_iff_continuous_domRestrict.mp hg).subtype_mk _))
  have hFi : Function.Injective F := fun w w' hww =>
    Subtype.ext (hgi w.2 w'.2 (congrArg Subtype.val (ψ.injective (Subtype.ext hww))))
  have hopen : IsOpen (range F) := isOpen_range_of_isOpen_of_continuous_injective_real
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) hO F hF hFi
  have hpre : IsOpen ((fun m : M => (ψ m : EuclideanSpace ℝ (Fin 2))) ⁻¹' range F) :=
    hopen.preimage (continuous_subtype_val.comp ψ.continuous)
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hpre
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨V, hV.mem_nhds ?_, ?_⟩
  · have hmem : (⟨g z, hgM hz⟩ : M) ∈
        (fun m : M => (ψ m : EuclideanSpace ℝ (Fin 2))) ⁻¹' range F := ⟨⟨z, hz⟩, rfl⟩
    rw [← hVeq] at hmem
    exact hmem
  · rintro x ⟨hxV, hxM⟩
    have hmem : (⟨x, hxM⟩ : M) ∈
        (fun m : M => (ψ m : EuclideanSpace ℝ (Fin 2))) ⁻¹' range F := by
      rw [← hVeq]
      exact hxV
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, w.2, congrArg Subtype.val (ψ.injective (Subtype.ext hw))⟩

theorem exists_ball_chart_of_inter_eq {M T W : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (ψ : M ≃ₜ U) (hW : IsOpen W) (hWT : W ∩ T = W ∩ M) {y : E} (hyW : y ∈ W)
    (hyT : y ∈ T) {N : Set E} (hN : N ∈ 𝓝[T] y) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
      0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
        MapsTo g (Metric.ball c r) (T ∩ N) ∧ g c = y := by
  have hyM : y ∈ M := by
    have h : y ∈ W ∩ T := ⟨hyW, hyT⟩
    rw [hWT] at h
    exact h.2
  have heq : 𝓝[T] y = 𝓝[M] y :=
    nhdsWithin_eq_nhdsWithin hyW hW (by rw [inter_comm T W, hWT, inter_comm W M])
  have hN' : N ∩ W ∈ 𝓝[M] y := by
    rw [← heq]
    exact Filter.inter_mem hN (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hyW))
  obtain ⟨c, r, g, hr, hgc, hgi, hgm, hgy⟩ := exists_ball_chart_of_homeomorph_isOpen hU ψ hyM hN'
  refine ⟨c, r, g, hr, hgc, hgi, fun w hw => ?_, hgy⟩
  obtain ⟨hwM, hwN, hwW⟩ := hgm hw
  have h : g w ∈ W ∩ M := ⟨hwW, hwM⟩
  rw [← hWT] at h
  exact ⟨h.2, hwN⟩

theorem image_mem_nhdsWithin_of_inter_eq {M T W : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))}
    (ψ : M ≃ₜ U) (hW : IsOpen W) (hWT : W ∩ T = W ∩ M) {O : Set (EuclideanSpace ℝ (Fin 2))}
    (hO : IsOpen O) {g : EuclideanSpace ℝ (Fin 2) → E} (hg : ContinuousOn g O)
    (hgi : InjOn g O) (hgT : MapsTo g O (T ∩ W)) {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ O) :
    g '' O ∈ 𝓝[T] (g z) := by
  have hgM : MapsTo g O M := fun w hw => by
    have h : g w ∈ W ∩ T := ⟨(hgT hw).2, (hgT hw).1⟩
    rw [hWT] at h
    exact h.2
  have heq : 𝓝[T] (g z) = 𝓝[M] (g z) :=
    nhdsWithin_eq_nhdsWithin (hgT hz).2 hW (by rw [inter_comm T W, hWT, inter_comm W M])
  rw [heq]
  exact image_mem_nhdsWithin_of_homeomorph ψ hO hg hgi hgM hz

end Chart

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem exists_mem_openSimplex_mem_of_mem {s : Finset E} (hs : s.Nonempty) {v : E}
    (hv : v ∈ s) {W : Set E} (hW : W ∈ 𝓝 v) : ∃ y ∈ openSimplex s, y ∈ W := by
  have hc := centroid_mem_openSimplex hs
  have hlim : Filter.Tendsto (fun r : ℝ => s.centroid ℝ id + r • (v - s.centroid ℝ id))
      (𝓝[<] 1) (𝓝 v) := by
    have hcont : Continuous fun r : ℝ => s.centroid ℝ id + r • (v - s.centroid ℝ id) := by
      fun_prop
    simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  obtain ⟨r, hrW, hr⟩ := ((hlim.eventually hW).and (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
  exact ⟨_, add_smul_sub_mem_openSimplex hc (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
    hr.1.le hr.2, hrW⟩

omit [FiniteDimensional ℝ E] in
theorem exists_segment_point_mem {a b : E} {W : Set E} (hW : W ∈ 𝓝 a) :
    ∃ t : ℝ, (1 - t) • a + t • b ∈ W ∧ t ∈ Ioo (0 : ℝ) 1 := by
  have hlim : Filter.Tendsto (fun t : ℝ => (1 - t) • a + t • b) (𝓝[>] 0) (𝓝 a) := by
    have hcont : Continuous fun t : ℝ => (1 - t) • a + t • b := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ((hlim.eventually hW).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists

open Classical in
theorem subset_or_subset_of_hinge_of_inter_eq (K : Geometry.SimplicialComplex ℝ E)
    {M W : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))} (ψ : M ≃ₜ U) (hW : IsOpen W)
    (hWK : W ∩ K.space = W ∩ M) {a b c₁ c₂ : E} (hab : a ≠ b) (hac₁ : a ≠ c₁) (hbc₁ : b ≠ c₁)
    (hac₂ : a ≠ c₂) (hbc₂ : b ≠ c₂) (hc : c₁ ≠ c₂) (h₁ : ({a, b, c₁} : Finset E) ∈ K.faces)
    (h₂ : ({a, b, c₂} : Finset E) ∈ K.faces) (haW : a ∈ W) {τ : Finset E} (hτ : τ ∈ K.faces)
    (habτ : ({a, b} : Finset E) ⊆ τ) :
    τ ⊆ {a, b, c₁} ∨ τ ⊆ {a, b, c₂} := by
  by_contra hne
  rw [not_or] at hne
  have hi₁ := affineIndependent_triple_of_mem_faces K hab hac₁ hbc₁ h₁
  have hi₂ := affineIndependent_triple_of_mem_faces K hab hac₂ hbc₂ h₂
  have hΦ₁ := (isPLHomeomorphOn_linearCombination_of_affineIndependent hi₁).bijOn
  have hΦ₂ := (isPLHomeomorphOn_linearCombination_of_affineIndependent hi₂).bijOn
  rw [range_vecCons_triple] at hΦ₁ hΦ₂
  let O : Set (EuclideanSpace ℝ (Fin 2)) := {p | 0 < p 0 ∧ p 0 + |p 1| < 1}
  have hc0 : Continuous fun p : EuclideanSpace ℝ (Fin 2) => p 0 := by fun_prop
  have hc1 : Continuous fun p : EuclideanSpace ℝ (Fin 2) => p 1 := by fun_prop
  have hO : IsOpen O :=
    (isOpen_lt continuous_const hc0).inter (isOpen_lt (hc0.add hc1.abs) continuous_const)
  let g : EuclideanSpace ℝ (Fin 2) → E := fun p =>
    (1 - p 0 - |p 1|) • a + p 0 • b + max (p 1) 0 • c₁ + max (-p 1) 0 • c₂
  have hgc : Continuous g := by fun_prop
  have hg₁ : ∀ p ∈ O, 0 ≤ p 1 → ![1 - p 0 - p 1, p 0, p 1] ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∧
      Fintype.linearCombination ℝ ![a, b, c₁] ![1 - p 0 - p 1, p 0, p 1] = g p := by
    intro p hp hp1
    have hp2 : p 0 + p 1 < 1 := by simpa [abs_of_nonneg hp1] using hp.2
    refine ⟨mem_stdSimplex_triple (by linarith) hp.1.le hp1 (by ring), ?_⟩
    rw [linearCombination_triple_apply]
    simp only [g, abs_of_nonneg hp1, max_eq_left hp1, max_eq_right (neg_nonpos.mpr hp1),
      zero_smul, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  have hg₂ : ∀ p ∈ O, p 1 ≤ 0 → ![1 - p 0 + p 1, p 0, -p 1] ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∧
      Fintype.linearCombination ℝ ![a, b, c₂] ![1 - p 0 + p 1, p 0, -p 1] = g p := by
    intro p hp hp1
    have hp2 : p 0 + -p 1 < 1 := by simpa [abs_of_nonpos hp1] using hp.2
    refine ⟨mem_stdSimplex_triple (by linarith) hp.1.le (neg_nonneg.mpr hp1) (by ring), ?_⟩
    rw [linearCombination_triple_apply]
    simp only [g, abs_of_nonpos hp1, max_eq_right hp1, max_eq_left (neg_nonneg.mpr hp1),
      zero_smul, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, sub_neg_eq_add]
  have hmem : ∀ p ∈ O, g p ∈ convexHull ℝ (↑({a, b, c₁} : Finset E) : Set E) ∨
      g p ∈ convexHull ℝ (↑({a, b, c₂} : Finset E) : Set E) := by
    intro p hp
    rcases le_total 0 (p 1) with hp1 | hp1
    · obtain ⟨hs, heq⟩ := hg₁ p hp hp1
      exact Or.inl (heq ▸ hΦ₁.mapsTo hs)
    · obtain ⟨hs, heq⟩ := hg₂ p hp hp1
      exact Or.inr (heq ▸ hΦ₂.mapsTo hs)
  have hgT : MapsTo g O K.space := fun p hp =>
    (hmem p hp).elim (fun h => K.convexHull_subset_space h₁ h)
      (fun h => K.convexHull_subset_space h₂ h)
  have hinter : (↑({a, b, c₁} : Finset E) : Set E) ∩ ↑({a, b, c₂} : Finset E) = {a, b} := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_inter_iff, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> simp_all
    · rintro (rfl | rfl) <;> simp
  have hflat : ∀ (c : E) (hi : AffineIndependent ℝ ![a, b, c]) (x : Fin 3 → ℝ),
      x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) → Fintype.linearCombination ℝ ![a, b, c] x ∈ segment ℝ a b →
      x 2 = 0 := by
    intro c hi x hx hseg
    obtain ⟨l, m, hl, hm, hlm, hz⟩ := hseg
    have hs : ![l, m, 0] ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := mem_stdSimplex_triple hl hm le_rfl (by
      rw [add_zero]; exact hlm)
    have heq := (isPLHomeomorphOn_linearCombination_of_affineIndependent hi).bijOn.injOn hs hx
      (by rw [linearCombination_triple_apply, ← hz]; simp)
    rw [← heq]
    rfl
  have hcross : ∀ p ∈ O, ∀ q ∈ O, 0 ≤ p 1 → q 1 ≤ 0 → g p = g q → p 1 = 0 ∧ q 1 = 0 := by
    intro p hp q hq hp1 hq1 hpq
    obtain ⟨hs₁, heq₁⟩ := hg₁ p hp hp1
    obtain ⟨hs₂, heq₂⟩ := hg₂ q hq hq1
    have hz : g p ∈ segment ℝ a b := by
      rw [← convexHull_pair, ← hinter]
      refine K.inter_subset_convexHull h₁ h₂ ⟨heq₁ ▸ hΦ₁.mapsTo hs₁, ?_⟩
      rw [hpq, ← heq₂]
      exact hΦ₂.mapsTo hs₂
    have e₁ := hflat c₁ hi₁ _ hs₁ (heq₁ ▸ hz)
    have e₂ := hflat c₂ hi₂ _ hs₂ (heq₂ ▸ hpq ▸ hz)
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at e₁ e₂
    exact ⟨e₁, neg_eq_zero.mp e₂⟩
  have hext : ∀ p q : EuclideanSpace ℝ (Fin 2), p 0 = q 0 → p 1 = q 1 → p = q := by
    intro p q h0 h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hgi : InjOn g O := by
    intro p hp q hq hpq
    have same₁ : 0 ≤ p 1 → 0 ≤ q 1 → p = q := by
      intro hp1 hq1
      obtain ⟨hs₁, heq₁⟩ := hg₁ p hp hp1
      obtain ⟨hs₂, heq₂⟩ := hg₁ q hq hq1
      have heq := hΦ₁.injOn hs₁ hs₂ (heq₁.trans (hpq.trans heq₂.symm))
      exact hext p q (by simpa using congrFun heq 1) (by simpa using congrFun heq 2)
    have same₂ : p 1 ≤ 0 → q 1 ≤ 0 → p = q := by
      intro hp1 hq1
      obtain ⟨hs₁, heq₁⟩ := hg₂ p hp hp1
      obtain ⟨hs₂, heq₂⟩ := hg₂ q hq hq1
      have heq := hΦ₂.injOn hs₁ hs₂ (heq₁.trans (hpq.trans heq₂.symm))
      exact hext p q (by simpa using congrFun heq 1) (by simpa using congrFun heq 2)
    rcases le_total 0 (p 1) with hp1 | hp1 <;> rcases le_total 0 (q 1) with hq1 | hq1
    · exact same₁ hp1 hq1
    · obtain ⟨e₁, e₂⟩ := hcross p hp q hq hp1 hq1 hpq
      exact same₁ hp1 e₂.ge
    · obtain ⟨e₁, e₂⟩ := hcross q hq p hp hq1 hp1 hpq.symm
      exact same₁ e₂.ge hq1
    · exact same₂ hp1 hq1
  obtain ⟨t, htW, ht⟩ := exists_segment_point_mem (b := b) (hW.mem_nhds haW)
  let p₀ : EuclideanSpace ℝ (Fin 2) := !₂[t, 0]
  have hp0 : p₀ 0 = t := by simp [p₀]
  have hp1 : p₀ 1 = 0 := by simp [p₀]
  have hgp₀ : g p₀ = (1 - t) • a + t • b := by
    simp only [g, hp0, hp1, abs_zero, sub_zero, max_self, neg_zero, zero_smul, add_zero]
  have hp₀ : p₀ ∈ O ∩ g ⁻¹' W := by
    refine ⟨⟨by rw [hp0]; exact ht.1, by rw [hp0, hp1, abs_zero, add_zero]; exact ht.2⟩, ?_⟩
    rw [mem_preimage, hgp₀]
    exact htW
  have hnhds := image_mem_nhdsWithin_of_inter_eq ψ hW hWK (hO.inter (hW.preimage hgc))
    hgc.continuousOn (hgi.mono inter_subset_left) (fun p hp => ⟨hgT hp.1, hp.2⟩) hp₀
  have hy : g p₀ ∈ convexHull ℝ (↑τ : Set E) := by
    rw [hgp₀]
    apply convexHull_mono (Finset.coe_subset.mpr habτ)
    rw [Finset.coe_pair, convexHull_pair]
    exact ⟨1 - t, t, by linarith [ht.2], ht.1.le, by ring, rfl⟩
  have hcl := convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hτ) hy
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
  obtain ⟨z, hzV, hzτ⟩ := mem_closure_iff_nhds.mp hcl V hV
  have hzK : z ∈ K.space := K.convexHull_subset_space hτ (openSimplex_subset_convexHull τ hzτ)
  obtain ⟨p, hp, rfl⟩ := hVsub ⟨hzV, hzK⟩
  rcases hmem p hp.1 with hz | hz
  · exact hne.1 (face_subset_of_mem_openSimplex_of_mem_convexHull K hτ h₁ hzτ hz)
  · exact hne.2 (face_subset_of_mem_openSimplex_of_mem_convexHull K hτ h₂ hzτ hz)

omit [FiniteDimensional ℝ E] in
open Classical in
theorem false_of_maximal_face_of_inter_eq (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {M W : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (ψ : M ≃ₜ U)
    (hW : IsOpen W) (hWK : W ∩ K.space = W ∩ M) {t : Finset E} (ht : t ∈ K.faces)
    (hcard : t.card ≤ 2) (hmax : ∀ σ ∈ K.faces, t ⊆ σ → σ = t) {y : E}
    (hyt : y ∈ openSimplex t) (hyW : y ∈ W) : False := by
  have htne := K.nonempty_of_mem_faces ht
  have hnhds := biUnion_convexHull_superset_mem_nhdsWithin K ht hyt
  have hN : (⋃ σ ∈ {σ ∈ K.faces | t ⊆ σ}, convexHull ℝ (σ : Set E)) =
      convexHull ℝ (t : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨σ, ⟨hσ, htσ⟩, hxσ⟩ := mem_iUnion₂.mp hx
      rwa [hmax σ hσ htσ] at hxσ
    · exact fun x hx => mem_iUnion₂.mpr ⟨t, ⟨ht, subset_rfl⟩, hx⟩
  rw [hN] at hnhds
  obtain ⟨c, r, h, hr, hhc, hhi, hhm, -⟩ := exists_ball_chart_of_inter_eq hU ψ hW hWK hyW
    (K.convexHull_subset_space ht (openSimplex_subset_convexHull t hyt)) hnhds
  have hcard' : t.card = 1 ∨ t.card = 2 := by
    have := Finset.card_pos.mpr htne
    omega
  rcases hcard' with h1 | h2
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    let c' : EuclideanSpace ℝ (Fin 2) := c + (r / 2) • EuclideanSpace.single 0 1
    have hc' : c' ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single,
        norm_one, mul_one, Real.norm_of_nonneg (by positivity)]
      linarith
    have hmem (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Metric.ball c r) : h z = a := by
      have := (hhm hz).2
      simpa using this
    have heq := hhi (Metric.mem_ball_self hr) hc' ((hmem c (Metric.mem_ball_self hr)).trans
      (hmem c' hc').symm)
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
    simp [c'] at this
    linarith
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℝ (b - a) (norm_ne_zero_iff.mpr hba)
    have hseg (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Metric.ball c r) :
        ∃ θ : ℝ, h z = a + θ • (b - a) := by
      have := (hhm hz).2
      rw [Finset.coe_pair, convexHull_pair, segment_eq_image'] at this
      obtain ⟨θ, -, hθ⟩ := this
      exact ⟨θ, hθ.symm⟩
    let F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => φ (h z - a) • EuclideanSpace.single 0 (1 : ℝ)
    have hF : ContinuousOn F (Metric.ball c r) :=
      ((φ.continuous.comp_continuousOn (hhc.sub continuousOn_const)).smul continuousOn_const)
    have hFi : InjOn F (Metric.ball c r) := by
      intro z hz z' hz' hzz
      have h0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) hzz
      simp only [F, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, ite_true,
        mul_one] at h0
      obtain ⟨θ, hθ⟩ := hseg z hz
      obtain ⟨θ', hθ'⟩ := hseg z' hz'
      rw [hθ, hθ', add_sub_cancel_left, add_sub_cancel_left, map_smul, map_smul, hφ,
        smul_eq_mul, smul_eq_mul] at h0
      have h0' : θ * ‖b - a‖ = θ' * ‖b - a‖ := by simpa using h0
      have hθθ : θ = θ' := mul_right_cancel₀ (norm_ne_zero_iff.mpr hba) h0'
      exact hhi hz hz' (by rw [hθ, hθ', hθθ])
    obtain ⟨z, -, hz⟩ := exists_mem_ball_apply_one_neg_of_injOn hr hF hFi (by simp [F])
    simp [F] at hz

omit [FiniteDimensional ℝ E] in
open Classical in
theorem exists_card_three_superset_of_inter_eq (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {M W : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (ψ : M ≃ₜ U) (hW : IsOpen W) (hWK : W ∩ K.space = W ∩ M) {v : E} (hvW : v ∈ W)
    (hcard : ∀ s ∈ K.faces, v ∈ s → s.card ≤ 3) {s : Finset E} (hs : s ∈ K.faces)
    (hvs : v ∈ s) : ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  induction hn : 3 - s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs3 : s.card = 3
    · exact ⟨s, hs, subset_rfl, hs3⟩
    by_cases hmax : ∀ σ ∈ K.faces, s ⊆ σ → σ = s
    · obtain ⟨y, hy, hyW⟩ :=
        exists_mem_openSimplex_mem_of_mem (K.nonempty_of_mem_faces hs) hvs (hW.mem_nhds hvW)
      exact (false_of_maximal_face_of_inter_eq K hU ψ hW hWK hs
        (by have := hcard s hs hvs; omega) hmax hy hyW).elim
    push Not at hmax
    obtain ⟨σ, hσ, hsσ, hne⟩ := hmax
    have hlt : s.card < σ.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsσ, fun h => hne h.symm⟩)
    obtain ⟨t, ht, hσt, htc⟩ :=
      ih (3 - σ.card) (by have := hcard σ hσ (hsσ hvs); omega) hσ (hsσ hvs) rfl
    exact ⟨t, ht, hsσ.trans hσt, htc⟩

open Classical in
theorem exists_second_triangle_of_inter_eq (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {M W : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (ψ : M ≃ₜ U) (hW : IsOpen W) (hWK : W ∩ K.space = W ∩ M) {a b c : E} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ht : ({a, b, c} : Finset E) ∈ K.faces) (haW : a ∈ W) :
    ∃ d, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ ({a, b, d} : Finset E) ∈ K.faces := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have he : ({a, b} : Finset E) ∈ K.faces := by
    refine K.down_closed ht (fun x hx => ?_) (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have hsub : ∀ σ ∈ K.faces, ({a, b} : Finset E) ⊆ σ → σ ⊆ {a, b, c} := by
    intro σ hσ habσ x hx
    by_contra hxn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxn
    have hface : ({a, b, x} : Finset E) ∈ K.faces := by
      refine K.down_closed hσ (fun y hy => ?_) (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact habσ (by simp)
      · exact habσ (by simp)
      · exact hx
    exact hno x hxn.1 hxn.2.1 hxn.2.2 hface
  obtain ⟨t, htW, htI⟩ := exists_segment_point_mem (b := b) (hW.mem_nhds haW)
  have hy : (1 - t) • a + t • b ∈ openSimplex ({a, b} : Finset E) := by
    refine ⟨fun x => if x = a then 1 - t else t, fun x _ => ?_, ?_, ?_⟩
    · dsimp only
      split_ifs
      · linarith [htI.2]
      · exact htI.1
    · rw [Finset.sum_pair hab]
      change (if a = a then 1 - t else t) + (if b = a then 1 - t else t) = 1
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hab)]
      ring
    · rw [Finset.sum_pair hab]
      change (if a = a then 1 - t else t) • a + (if b = a then 1 - t else t) • b =
        (1 - t) • a + t • b
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hab)]
  have hnhds := biUnion_convexHull_superset_mem_nhdsWithin K he hy
  have hN : (⋃ σ ∈ {σ ∈ K.faces | ({a, b} : Finset E) ⊆ σ}, convexHull ℝ (σ : Set E)) ⊆
      convexHull ℝ (↑({a, b, c} : Finset E) : Set E) := by
    intro x hx
    obtain ⟨σ, ⟨hσ, habσ⟩, hxσ⟩ := mem_iUnion₂.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr (hsub σ hσ habσ)) hxσ
  obtain ⟨c₀, r, h, hr, hhc, hhi, hhm, hhy⟩ := exists_ball_chart_of_inter_eq hU ψ hW hWK htW
    (K.convexHull_subset_space he (openSimplex_subset_convexHull _ hy))
    (Filter.mem_of_superset hnhds hN)
  have hi := affineIndependent_triple_of_mem_faces K hab hac hbc ht
  have hΦ := isPLHomeomorphOn_linearCombination_of_affineIndependent hi
  rw [range_vecCons_triple] at hΦ
  set Φ := Fintype.linearCombination ℝ ![a, b, c]
  set Ψ := Function.invFunOn Φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hΨc : ContinuousOn Ψ (convexHull ℝ (↑({a, b, c} : Finset E) : Set E)) :=
    hΦ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hΨm : MapsTo Ψ (convexHull ℝ (↑({a, b, c} : Finset E) : Set E)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
    fun x hx => hΦ.bijOn.surjOn.mapsTo_invFunOn hx
  have hΦΨ : ∀ x ∈ convexHull ℝ (↑({a, b, c} : Finset E) : Set E), Φ (Ψ x) = x :=
    fun x hx => hΦ.bijOn.invOn_invFunOn.2 hx
  have hk : ContinuousOn (fun z => Ψ (h z)) (Metric.ball c₀ r) :=
    hΨc.comp hhc (fun z hz => (hhm hz).2)
  let G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun z =>
    Ψ (h z) 1 • EuclideanSpace.single 0 (1 : ℝ) + Ψ (h z) 2 • EuclideanSpace.single 1 (1 : ℝ)
  have hG0 (z : EuclideanSpace ℝ (Fin 2)) : G z 0 = Ψ (h z) 1 := by simp [G]
  have hG1 (z : EuclideanSpace ℝ (Fin 2)) : G z 1 = Ψ (h z) 2 := by simp [G]
  have hGc : ContinuousOn G (Metric.ball c₀ r) :=
    (((continuous_apply 1).comp_continuousOn hk).smul continuousOn_const).add
      (((continuous_apply 2).comp_continuousOn hk).smul continuousOn_const)
  have hGi : InjOn G (Metric.ball c₀ r) := by
    intro z hz z' hz' hzz
    have e1 : Ψ (h z) 1 = Ψ (h z') 1 := by rw [← hG0, ← hG0, hzz]
    have e2 : Ψ (h z) 2 = Ψ (h z') 2 := by rw [← hG1, ← hG1, hzz]
    have hs := hΨm (hhm hz).2
    have hs' := hΨm (hhm hz').2
    have hsum := hs.2
    have hsum' := hs'.2
    simp only [Fin.sum_univ_three] at hsum hsum'
    have e0 : Ψ (h z) 0 = Ψ (h z') 0 := by linarith
    have heq : Ψ (h z) = Ψ (h z') := by
      funext i
      fin_cases i
      exacts [e0, e1, e2]
    apply hhi hz hz'
    rw [← hΦΨ _ (hhm hz).2, ← hΦΨ _ (hhm hz').2, heq]
  have hyΦ : Φ ![1 - t, t, 0] = (1 - t) • a + t • b := by
    rw [linearCombination_triple_apply]
    simp
  have hmid : ![1 - t, t, 0] ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    mem_stdSimplex_triple (by linarith [htI.2]) htI.1.le le_rfl (by ring)
  have hΨy : Ψ ((1 - t) • a + t • b) = ![1 - t, t, 0] := by
    rw [← hyΦ]
    exact hΦ.bijOn.invOn_invFunOn.1 hmid
  obtain ⟨z, hz, hzneg⟩ := exists_mem_ball_apply_one_neg_of_injOn hr hGc hGi
    (by rw [hG1, hhy, hΨy]; rfl)
  rw [hG1] at hzneg
  exact (hΨm (hhm hz).2).1 2 |>.not_gt hzneg

omit [FiniteDimensional ℝ E] in
open Classical in
theorem edgeGraph_geometricLink_connected_of_inter_eq (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {M W : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (ψ : M ≃ₜ U) (hW : IsOpen W) (hWK : W ∩ K.space = W ∩ M) {v w : E}
    (hv : ({v} : Finset E) ∈ K.faces) (hvW : v ∈ W) (hvw : v ≠ w)
    (hw : ({v, w} : Finset E) ∈ K.faces) :
    (SimplicialComplex.edgeGraph (SimplicialComplex.geometricLink K {v})).Connected := by
  set Lk := SimplicialComplex.geometricLink K {v}
  have hmemLk (s : Finset E) : s ∈ Lk.faces ↔ s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K.faces :=
    SimplicialComplex.mem_geometricLink_singleton K v s
  have hwLk : ({w} : Finset E) ∈ Lk.faces :=
    (hmemLk _).mpr ⟨by simp, by simpa using hvw, hw⟩
  have : Nonempty Lk.vertices := ⟨⟨w, hwLk⟩⟩
  refine ⟨fun a₀ b₀ => ?_⟩
  by_contra hnr
  let A : Set E := {x | ∃ hx : ({x} : Finset E) ∈ Lk.faces,
    (SimplicialComplex.edgeGraph Lk).Reachable a₀ ⟨x, hx⟩}
  have hA₀ : (a₀ : E) ∈ A := ⟨a₀.2, SimpleGraph.Reachable.refl _⟩
  have hB₀ : (b₀ : E) ∉ A := fun ⟨_, hr⟩ => hnr hr
  let Z (P : E → Prop) : Set E :=
    ⋃ σ ∈ {σ ∈ K.faces | v ∈ σ ∧ ∀ x ∈ σ, x ≠ v → P x}, convexHull ℝ (σ : Set E)
  have hclosed (P : E → Prop) : IsClosed (Z P) :=
    ((Set.toFinite K.faces).subset fun _ h => h.1).isClosed_biUnion
      fun σ _ => (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hlinkv : ∀ σ ∈ K.faces, v ∈ σ → ∀ x ∈ σ, x ≠ v → ({x} : Finset E) ∈ Lk.faces := by
    intro σ hσ hvσ x hx hxv
    refine (hmemLk _).mpr ⟨by simp, by simpa using hxv.symm, K.down_closed hσ ?_ (by simp)⟩
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    exacts [hvσ, hx]
  have hprop : ∀ σ ∈ K.faces, v ∈ σ → ∀ x ∈ σ, ∀ x' ∈ σ, x ≠ v → x' ≠ v → x ∈ A →
      x' ∈ A := by
    rintro σ hσ hvσ x hx x' hx' hxv hx'v ⟨hxL, hr⟩
    refine ⟨hlinkv σ hσ hvσ x' hx' hx'v, ?_⟩
    by_cases hxx : x = x'
    · subst hxx
      exact hr
    · have hadj : (SimplicialComplex.edgeGraph Lk).Adj ⟨x, hxL⟩
          ⟨x', hlinkv σ hσ hvσ x' hx' hx'v⟩ := by
        refine ⟨fun h => hxx (congrArg Subtype.val h), (hmemLk _).mpr ⟨by simp, ?_, ?_⟩⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hxv.symm, hx'v.symm⟩
        · refine K.down_closed hσ ?_ (by simp)
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          exacts [hvσ, hx, hx']
      exact hr.trans hadj.reachable
  have hcover : closedStar K v ⊆ Z (· ∈ A) ∪ Z (· ∉ A) := by
    intro z hz
    obtain ⟨σ, ⟨hσ, hvσ⟩, hzσ⟩ := mem_iUnion₂.mp hz
    have hvσ' : v ∈ σ := mem_of_mem_convexHull_of_singleton_mem K hv hσ hvσ
    by_cases hex : ∃ x ∈ σ, x ≠ v ∧ x ∈ A
    · obtain ⟨x, hx, hxv, hxA⟩ := hex
      exact Or.inl (mem_iUnion₂.mpr ⟨σ, ⟨hσ, hvσ', fun x' hx' hx'v =>
        hprop σ hσ hvσ' x hx x' hx' hxv hx'v hxA⟩, hzσ⟩)
    · simp only [not_exists, not_and] at hex
      exact Or.inr (mem_iUnion₂.mpr ⟨σ, ⟨hσ, hvσ', fun x hx hxv => hex x hx hxv⟩, hzσ⟩)
  have hinter : Z (· ∈ A) ∩ Z (· ∉ A) ⊆ {v} := by
    rintro z ⟨hzA, hzB⟩
    obtain ⟨σ, ⟨hσ, -, hσA⟩, hzσ⟩ := mem_iUnion₂.mp hzA
    obtain ⟨τ, ⟨hτ, -, hτB⟩, hzτ⟩ := mem_iUnion₂.mp hzB
    have h := K.inter_subset_convexHull hσ hτ ⟨hzσ, hzτ⟩
    have hsub : (↑σ : Set E) ∩ ↑τ ⊆ {v} := by
      rintro x ⟨hxσ, hxτ⟩
      by_contra hxv
      exact hτB x hxτ hxv (hσA x hxσ hxv)
    have h' := convexHull_mono hsub h
    rwa [convexHull_singleton] at h'
  obtain ⟨c, r, h, hr, hhc, hhi, hhm, hhv⟩ := exists_ball_chart_of_inter_eq hU ψ hW hWK hvW
    (K.convexHull_subset_space hv (by simp))
    (Filter.inter_mem (closedStar_mem_nhdsWithin K v)
      (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hvW)))
  have hW' := image_mem_nhdsWithin_of_inter_eq ψ hW hWK Metric.isOpen_ball hhc hhi
    (fun z hz => ⟨(hhm hz).1, (hhm hz).2.2⟩) (Metric.mem_ball_self hr)
  rw [hhv] at hW'
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW'
  have hray : ∀ x : E, ({v, x} : Finset E) ∈ K.faces → x ≠ v →
      ∃ z ∈ Metric.ball c r \ {c}, h z ∈ convexHull ℝ (↑({v, x} : Finset E) : Set E) := by
    intro x hx hxv
    have hlim : Filter.Tendsto (fun t : ℝ => v + t • (x - v)) (𝓝[>] 0) (𝓝 v) := by
      have hc : Continuous fun t : ℝ => v + t • (x - v) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨t, htV, ht0, ht1⟩ :=
      ((hlim.eventually hV).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have hseg : v + t • (x - v) ∈ convexHull ℝ (↑({v, x} : Finset E) : Set E) := by
      rw [Finset.coe_pair, convexHull_pair, segment_eq_image']
      exact ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
    obtain ⟨z, hz, hzt⟩ := hVsub ⟨htV, K.convexHull_subset_space hx hseg⟩
    refine ⟨z, ⟨hz, fun hzc => ?_⟩, hzt ▸ hseg⟩
    rw [mem_singleton_iff] at hzc
    rw [hzc, hhv] at hzt
    have h0 : t • (x - v) = 0 := by
      have := congrArg (· - v) hzt
      simpa using this.symm
    rcases smul_eq_zero.mp h0 with h0 | h0
    · exact ht0.ne' h0
    · exact hxv (sub_eq_zero.mp h0)
  have hedgeA : ∀ x : Lk.vertices, ({v, (x : E)} : Finset E) ∈ K.faces ∧ (x : E) ≠ v := by
    intro x
    obtain ⟨-, hvx, hins⟩ := (hmemLk _).mp x.2
    exact ⟨hins, fun h => hvx (by rw [h]; simp)⟩
  obtain ⟨za, hza, hza'⟩ := hray a₀ (hedgeA a₀).1 (hedgeA a₀).2
  obtain ⟨zb, hzb, hzb'⟩ := hray b₀ (hedgeA b₀).1 (hedgeA b₀).2
  have hZa : h za ∈ Z (· ∈ A) := by
    refine mem_iUnion₂.mpr ⟨_, ⟨(hedgeA a₀).1, by simp, fun x hx hxv => ?_⟩, hza'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (hxv rfl).elim
    · exact hA₀
  have hZb : h zb ∈ Z (· ∉ A) := by
    refine mem_iUnion₂.mpr ⟨_, ⟨(hedgeA b₀).1, by simp, fun x hx hxv => ?_⟩, hzb'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (hxv rfl).elim
    · exact hB₀
  have hpre := (isPreconnected_ball_sdiff_center c r).image h (hhc.mono sdiff_subset)
  obtain ⟨p, ⟨z, hz, rfl⟩, hpA, hpB⟩ := isPreconnected_closed_iff.mp hpre _ _
    (hclosed _) (hclosed _) (fun q ⟨z, hz, hzq⟩ => hzq ▸ hcover (hhm hz.1).2.1)
    ⟨_, ⟨za, hza, rfl⟩, hZa⟩ ⟨_, ⟨zb, hzb, rfl⟩, hZb⟩
  have hzv : h z = v := hinter ⟨hpA, hpB⟩
  exact hz.2 (hhi hz.1 (Metric.mem_ball_self hr) (hzv.trans hhv.symm))

open Classical in
theorem isPLSphere_one_geometricLink_of_homeomorph (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {M : Set E} {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (ψ : M ≃ₜ U) {v : E} (hv : ({v} : Finset E) ∈ K.faces)
    (hvM : ∀ᶠ y in 𝓝 v, y ∈ K.space ↔ y ∈ M) :
    IsPLSphere 1 (SimplicialComplex.geometricLink K {v}).space := by
  obtain ⟨W, hWp, hW, hvW⟩ := eventually_nhds_iff.mp hvM
  have hWK : W ∩ K.space = W ∩ M := by
    ext y
    exact ⟨fun hy => ⟨hy.1, (hWp y hy.1).mp hy.2⟩, fun hy => ⟨hy.1, (hWp y hy.1).mpr hy.2⟩⟩
  have hcard : ∀ s ∈ K.faces, v ∈ s → s.card ≤ 3 := by
    intro s hs hvs
    by_contra h4
    obtain ⟨σ, hσs, hσ3⟩ := Finset.exists_subset_card_eq
      (show 3 ≤ (s.erase v).card by rw [Finset.card_erase_of_mem hvs]; omega)
    obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp hσ3
    have hvσ : v ∉ ({b, c, d} : Finset E) := fun h => (Finset.mem_erase.mp (hσs h)).1 rfl
    have hτs : insert v ({b, c, d} : Finset E) ⊆ s :=
      Finset.insert_subset hvs (hσs.trans (Finset.erase_subset v s))
    have hτ := K.down_closed hs hτs (Finset.insert_nonempty _ _)
    have hτcard : (insert v ({b, c, d} : Finset E)).card = 4 := by
      rw [Finset.card_insert_of_notMem hvσ, hσ3]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvσ
    obtain ⟨hvb, hvc, hvd⟩ := hvσ
    have h₁ : ({v, b, c} : Finset E) ∈ K.faces := by
      refine K.down_closed hτ (fun x hx => ?_) (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    have h₂ : ({v, b, d} : Finset E) ∈ K.faces := by
      refine K.down_closed hτ (fun x hx => ?_) (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    rcases subset_or_subset_of_hinge_of_inter_eq K ψ hW hWK hvb hvc hbc hvd hbd hcd h₁ h₂ hvW hτ
      (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto) with h | h
    · have := Finset.card_le_card h
      have := Finset.card_le_three (a := v) (b := b) (c := c)
      omega
    · have := Finset.card_le_card h
      have := Finset.card_le_three (a := v) (b := b) (c := d)
      omega
  have hpure : ∀ {s : Finset E}, s ∈ K.faces → v ∈ s → ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 :=
    fun hs hvs => exists_card_three_superset_of_inter_eq K hU ψ hW hWK hvW hcard hs hvs
  have hedge : ∀ w : E, v ≠ w → ({v, w} : Finset E) ∈ K.faces → ∃ c₁ c₂, c₁ ≠ c₂ ∧
      {x | x ∉ ({v, w} : Finset E) ∧ insert x ({v, w} : Finset E) ∈ K.faces} = {c₁, c₂} := by
    intro w hvw he
    obtain ⟨t, ht, hvwt, ht3⟩ := hpure he (Finset.mem_insert_self v {w})
    have hdiff : (t \ {v, w}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hvwt, ht3, Finset.card_pair hvw]
    obtain ⟨c₁, hc₁⟩ := Finset.card_eq_one.mp hdiff
    have hc₁ab : c₁ ∉ ({v, w} : Finset E) :=
      (Finset.mem_sdiff.mp (hc₁ ▸ Finset.mem_singleton_self c₁)).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₁ab
    have htc : t = {v, w, c₁} := by
      rw [← Finset.sdiff_union_of_subset hvwt, hc₁]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [htc] at ht
    obtain ⟨c₂, hc₂a, hc₂b, hc₂c, h₂⟩ := exists_second_triangle_of_inter_eq K hU ψ hW hWK hvw
      (Ne.symm hc₁ab.1) (Ne.symm hc₁ab.2) ht hvW
    refine ⟨c₁, c₂, Ne.symm hc₂c, ?_⟩
    ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨⟨hxa, hxb⟩, hx⟩
      have hins : insert x ({v, w} : Finset E) = {v, w, x} := by
        ext y
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hins] at hx
      rcases subset_or_subset_of_hinge_of_inter_eq K ψ hW hWK hvw (Ne.symm hc₁ab.1)
        (Ne.symm hc₁ab.2) (Ne.symm hc₂a) (Ne.symm hc₂b) (Ne.symm hc₂c) ht h₂ hvW hx
        (fun y hy => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto) with h | h
      · have := h (by simp : x ∈ ({v, w, x} : Finset E))
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        tauto
      · have := h (by simp : x ∈ ({v, w, x} : Finset E))
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        tauto
    · rintro (rfl | rfl)
      · refine ⟨⟨hc₁ab.1, hc₁ab.2⟩, ?_⟩
        have hins : insert x ({v, w} : Finset E) = {v, w, x} := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rwa [hins]
      · refine ⟨⟨hc₂a, hc₂b⟩, ?_⟩
        have hins : insert x ({v, w} : Finset E) = {v, w, x} := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rwa [hins]
  set Lk := SimplicialComplex.geometricLink K {v}
  have hmemLk (s : Finset E) : s ∈ Lk.faces ↔ s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K.faces :=
    SimplicialComplex.mem_geometricLink_singleton K v s
  have hLk1 : IsCombinatorialManifold 1 Lk := by
    refine (isCombinatorialManifold_one_iff Lk).mpr ⟨fun s hs => ?_, fun w hw => ?_⟩
    · obtain ⟨-, hvs, hins⟩ := (hmemLk s).mp hs
      have := hcard _ hins (Finset.mem_insert_self v s)
      rw [Finset.card_insert_of_notMem hvs] at this
      omega
    · obtain ⟨-, hvw, hins⟩ := (hmemLk _).mp hw
      have hvw' : v ≠ w := fun h => hvw (by rw [h]; simp)
      obtain ⟨c₁, c₂, hc, hset⟩ := hedge w hvw' hins
      refine ⟨c₁, c₂, hc, ?_⟩
      rw [← hset]
      ext z
      simp only [mem_ofPred_eq, hmemLk, Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hzw, -, ⟨hvw₁, hvz⟩, hz⟩
        refine ⟨⟨fun h => hvz h.symm, hzw⟩, ?_⟩
        have hins' : insert z ({v, w} : Finset E) = insert v ({w, z} : Finset E) := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rwa [hins']
      · rintro ⟨⟨hzv, hzw⟩, hz⟩
        refine ⟨hzw, by simp, ⟨hvw', fun h => hzv h.symm⟩, ?_⟩
        have hins' : insert v ({w, z} : Finset E) = insert z ({v, w} : Finset E) := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rwa [hins']
  obtain ⟨t, ht, hvt, ht3⟩ := hpure hv (Finset.mem_singleton_self v)
  obtain ⟨w, hwt, hwv⟩ : ∃ w ∈ t, w ≠ v := by
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    have : t ⊆ {v} := fun x hx => Finset.mem_singleton.mpr (hno x hx)
    have := Finset.card_le_card this
    simp at this
    omega
  have hvw : ({v, w} : Finset E) ∈ K.faces := by
    refine K.down_closed ht (fun y hy => ?_) (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    exacts [hvt (Finset.mem_singleton_self _), hwt]
  exact isPLSphere_one_of_edgeGraph_connected Lk hLk1
    (edgeGraph_geometricLink_connected_of_inter_eq K hU ψ hW hWK hv hvW hwv.symm hvw)

open Classical in
theorem exists_isSubdivision_neighborhood_of_forall_geometricLink {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {C O : Set E} (hC : IsCompact C)
    (hCK : C ⊆ K.space) (hO : IsOpen O) (hCO : C ⊆ O)
    (hlink : ∀ J : Geometry.SimplicialComplex ℝ E, IsSubdivision J K → J.faces.Finite →
      ∀ v ∈ O, ({v} : Finset E) ∈ J.faces →
        IsPLSphere n (SimplicialComplex.geometricLink J {v}).space ∨
          IsPLBall n (SimplicialComplex.geometricLink J {v}).space) :
    ∃ K' L : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      L.faces ⊆ K'.faces ∧ IsCombinatorialManifoldWithBoundary (n + 1) L ∧ L.space ⊆ O ∧
        ∀ x ∈ C, L.space ∈ 𝓝[K.space] x := by
  classical
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_cthickening_subset_open hO hCO
  obtain ⟨N, hN⟩ := ((Set.toFinite K.faces).image fun s : Finset E => s.card).bddAbove
  have hcard : ∀ s ∈ K.faces, s.card ≤ N + 1 :=
    fun s hs => (hN (mem_image_of_mem _ hs)).trans (Nat.le_succ N)
  obtain ⟨J, hJ, hJfin, -, hdiam⟩ := exists_isSubdivision_diam_lt K hcard (half_pos hδ)
  have : Finite J.faces := hJfin.to_subtype
  let Q : Set E := {x | ∀ t ∈ J.faces, x ∈ convexHull ℝ (t : Set E) →
    convexHull ℝ (t : Set E) ⊆ O}
  let L := restrict J Q
  have hCL : C ⊆ L.space := by
    intro x hx
    have hxJ : x ∈ J.space := hJ.space_eq.symm ▸ hCK hx
    obtain ⟨s, hs, hxs⟩ := J.mem_space_iff.mp hxJ
    refine L.convexHull_subset_space ⟨hs, ?_⟩ hxs
    intro y hys t ht hyt z hzt
    apply hthick
    apply Metric.mem_cthickening_of_dist_le z x δ C hx
    have hzy : dist z y < δ / 2 :=
      (Metric.dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded hzt
        hyt).trans_lt (hdiam t ht)
    have hyx : dist y x < δ / 2 :=
      (Metric.dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded hys
        hxs).trans_lt (hdiam s hs)
    have hzx := dist_triangle z y x
    linarith
  have hloc : IsLocallyCombinatorialManifoldWithBoundary n J L.space := by
    rintro v hv ⟨s, hs, hvs, y, hys, hyL⟩
    have hyQ : y ∈ Q := restrict_space_subset J Q hyL
    exact hlink J hJ hJfin v (hyQ s hs hys (subset_convexHull ℝ _ (Finset.mem_coe.mpr hvs))) hv
  refine ⟨PiecewiseLinear.secondDerived J, PiecewiseLinear.derivedNeighborhood J L,
    (secondDerived_isSubdivision J).trans hJ, Set.toFinite _,
    derivedNeighborhood_faces_subset J L,
    IsLocallyCombinatorialManifoldWithBoundary.derivedNeighborhood L hloc, ?_, ?_⟩
  · apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst
    exact hs.2 (s.centroid_mem_convexHull (J.nonempty_of_mem_faces hs.1)) t ht hst
  · intro x hx
    rw [← hJ.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin (restrict_faces_subset J Q) (hCL hx)

end Complex

end DifferentialGeometry.Topology.PiecewiseLinear
