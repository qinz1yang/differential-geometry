/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Cone
import DifferentialGeometry.Topology.PiecewiseLinear.Derived
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.Star
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Chart

variable {E : Type*} [TopologicalSpace E] {T : Set E}

theorem mem_nhdsWithin_image_of_homeomorph_sphere_prod
    (ψ : T ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {O : Set (EuclideanSpace ℝ (Fin 2))} (hO : IsOpen O)
    {g : EuclideanSpace ℝ (Fin 2) → E}
    (hg : ContinuousOn g O) (hgi : InjOn g O) (hgT : MapsTo g O T)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ O) : g '' O ∈ 𝓝[T] (g z) := by
  let H := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
  let M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let e : H ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [H, Module.finrank_prod])
  let _ : ChartedSpace H M := inferInstanceAs
    (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) H := e.symm.toHomeomorph.chartedSpace
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) M :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin 2)) H M
  let F : O → M := fun w => ψ ⟨g w, hgT w.2⟩
  have hF : Continuous F :=
    ψ.continuous.comp ((continuousOn_iff_continuous_domRestrict.mp hg).subtype_mk _)
  have hFi : Function.Injective F := fun w w' h =>
    Subtype.ext (hgi w.2 w'.2 (congrArg Subtype.val (ψ.injective h)))
  have hopen : IsOpen (range F) := isOpen_range_of_isOpen_of_continuous_injective_real
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) hO F hF hFi
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp (hopen.preimage ψ.continuous)
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨U, hU.mem_nhds ?_, ?_⟩
  · have hmem : (⟨g z, hgT hz⟩ : T) ∈ ψ ⁻¹' range F := ⟨⟨z, hz⟩, rfl⟩
    rw [← hUeq] at hmem
    exact hmem
  · rintro x ⟨hxU, hxT⟩
    have hmem : (⟨x, hxT⟩ : T) ∈ ψ ⁻¹' range F := by
      rw [← hUeq]
      exact hxU
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, w.2, congrArg Subtype.val (ψ.injective hw)⟩

theorem exists_ball_chart_of_homeomorph_sphere_prod
    (ψ : T ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {y : E} (hy : y ∈ T) {N : Set (E)}
    (hN : N ∈ 𝓝[T] y) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (h : EuclideanSpace ℝ (Fin 2) → E),
      0 < r ∧ ContinuousOn h (Metric.ball c r) ∧ InjOn h (Metric.ball c r) ∧
        MapsTo h (Metric.ball c r) (T ∩ N) ∧ h c = y := by
  let H := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
  let M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let e : H ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [H, Module.finrank_prod])
  let _ : ChartedSpace H M := inferInstanceAs
    (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) H := e.symm.toHomeomorph.chartedSpace
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) M :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin 2)) H M
  let p : M := ψ ⟨y, hy⟩
  let φ := chartAt (EuclideanSpace ℝ (Fin 2)) p
  obtain ⟨U, hU, hUN⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hN
  have hcont : Continuous fun m : M => ((ψ.symm m : T) : E) :=
    continuous_subtype_val.comp ψ.symm.continuous
  have hV : {m : M | ((ψ.symm m : T) : E) ∈ U} ∈ 𝓝 p := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa [p] using hU
  have hpφ : p ∈ φ.source := mem_chart_source _ p
  have ht : φ.target ∈ 𝓝 (φ p) := φ.open_target.mem_nhds (φ.map_source hpφ)
  have hs : φ.symm ⁻¹' {m : M | ((ψ.symm m : T) : E) ∈ U} ∈
      𝓝 (φ p) := by
    apply (φ.continuousAt_symm (φ.map_source hpφ)).preimage_mem_nhds
    rw [φ.left_inv hpφ]
    exact hV
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hs)
  refine ⟨φ p, r, fun w => ((ψ.symm (φ.symm w) : T) : E), hr,
    hcont.comp_continuousOn (φ.continuousOn_symm.mono (hball.trans inter_subset_left)),
    ?_, ?_, ?_⟩
  · intro w hw w' hw' heq
    have h1 : φ.symm w = φ.symm w' := ψ.symm.injective (Subtype.ext heq)
    exact φ.symm.injOn (by rw [φ.symm_source]; exact (hball hw).1)
      (by rw [φ.symm_source]; exact (hball hw').1) h1
  · intro w hw
    exact ⟨(ψ.symm (φ.symm w)).2, hUN ⟨(hball hw).2, (ψ.symm (φ.symm w)).2⟩⟩
  · change ((ψ.symm (φ.symm (φ p)) : T) : E) = y
    rw [φ.left_inv hpφ]
    simp [p]

end Chart

theorem exists_mem_ball_apply_one_neg_of_injOn
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hG : ContinuousOn G (Metric.ball c r)) (hGi : InjOn G (Metric.ball c r))
    (hzero : G c 1 = 0) : ∃ z ∈ Metric.ball c r, G z 1 < 0 := by
  have hopen := invariance_of_domain_isOpen_image Metric.isOpen_ball hG hGi
  have hmem : G c ∈ G '' Metric.ball c r := ⟨c, Metric.mem_ball_self hr, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen _ hmem
  let q := G c - (ε / 2) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hq : q ∈ Metric.ball (G c) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : q - G c = -((ε / 2) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
      simp [q]
    rw [this, norm_neg, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg (by positivity)]
    linarith
  obtain ⟨z, hz, hzq⟩ := hεsub hq
  refine ⟨z, hz, ?_⟩
  rw [hzq]
  simp [q, hzero]
  linarith

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem affineIndependent_triple_of_mem_faces (K : Geometry.SimplicialComplex ℝ E)
    {a b c : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ({a, b, c} : Finset E) ∈ K.faces) : AffineIndependent ℝ ![a, b, c] := by
  have hK := K.indep h
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  have hinj : Function.Injective ![a, b, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  let f : Fin 3 ↪ ({a, b, c} : Finset E) :=
    ⟨fun i => ⟨![a, b, c] i, by fin_cases i <;> simp⟩, fun i j hij =>
      hinj (congrArg Subtype.val hij)⟩
  have heq : ((↑) : ({a, b, c} : Finset E) → E) ∘ f = ![a, b, c] := by
    funext i
    rfl
  rw [← heq]
  exact hK.comp_embedding f

omit [FiniteDimensional ℝ E] in
theorem linearCombination_triple_apply (a b c : E) (x : Fin 3 → ℝ) :
    Fintype.linearCombination ℝ ![a, b, c] x = x 0 • a + x 1 • b + x 2 • c := by
  simp [Fintype.linearCombination_apply, Fin.sum_univ_three]

theorem mem_stdSimplex_triple {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) : ![x, y, z] ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simpa
  · simpa [Fin.sum_univ_three] using hsum

open Classical in
theorem subset_or_subset_of_hinge (K : Geometry.SimplicialComplex ℝ E)
    (ψ : K.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {a b c₁ c₂ : E} (hab : a ≠ b) (hac₁ : a ≠ c₁) (hbc₁ : b ≠ c₁) (hac₂ : a ≠ c₂)
    (hbc₂ : b ≠ c₂) (hc : c₁ ≠ c₂) (h₁ : ({a, b, c₁} : Finset E) ∈ K.faces)
    (h₂ : ({a, b, c₂} : Finset E) ∈ K.faces) {τ : Finset E} (hτ : τ ∈ K.faces)
    (habτ : ({a, b} : Finset E) ⊆ τ) :
    τ ⊆ {a, b, c₁} ∨ τ ⊆ {a, b, c₂} := by
  by_contra hne
  rw [not_or] at hne
  have hi₁ := affineIndependent_triple_of_mem_faces K hab hac₁ hbc₁ h₁
  have hi₂ := affineIndependent_triple_of_mem_faces K hab hac₂ hbc₂ h₂
  have hΦ₁ := (isPLHomeomorphOn_linearCombination_of_affineIndependent hi₁).bijOn
  have hΦ₂ := (isPLHomeomorphOn_linearCombination_of_affineIndependent hi₂).bijOn
  have hrange (c : E) : range ![a, b, c] = ↑({a, b, c} : Finset E) := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
      mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  rw [hrange] at hΦ₁ hΦ₂
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
  let p₀ : EuclideanSpace ℝ (Fin 2) := !₂[1 / 2, 0]
  have hp₀ : p₀ ∈ O := by
    simp only [O, mem_ofPred_eq, p₀]
    norm_num
  have hnhds := mem_nhdsWithin_image_of_homeomorph_sphere_prod ψ hO hgc.continuousOn hgi hgT hp₀
  have hy : g p₀ ∈ convexHull ℝ (↑τ : Set E) := by
    apply convexHull_mono (Finset.coe_subset.mpr habτ)
    rw [Finset.coe_pair, convexHull_pair]
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp [g, p₀]
    norm_num
  have hcl := convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hτ) hy
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
  obtain ⟨z, hzU, hzτ⟩ := mem_closure_iff_nhds.mp hcl U hU
  have hzK : z ∈ K.space := K.convexHull_subset_space hτ (openSimplex_subset_convexHull τ hzτ)
  obtain ⟨p, hp, rfl⟩ := hUsub ⟨hzU, hzK⟩
  rcases hmem p hp with hz | hz
  · exact hne.1 (face_subset_of_mem_openSimplex_of_mem_convexHull K hτ h₁ hzτ hz)
  · exact hne.2 (face_subset_of_mem_openSimplex_of_mem_convexHull K hτ h₂ hzτ hz)

end Complex

theorem isPreconnected_ball_sdiff_center (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
    norm_num
  have heq : Metric.ball c r \ {c} =
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => c + q.2 • q.1) ''
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Ioo 0 r) := by
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      have hne : z - c ≠ 0 := sub_ne_zero.mpr hzc
      have hpos : 0 < ‖z - c‖ := norm_pos_iff.mpr hne
      refine ⟨(‖z - c‖⁻¹ • (z - c), ‖z - c‖), ⟨?_, hpos, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hpos.ne']
      · rw [← dist_eq_norm]
        exact hz
      · simp only
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
    · rintro ⟨⟨u, t⟩, ⟨hu, ht0, htr⟩, rfl⟩
      have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
          Real.norm_of_nonneg ht0.le]
        exact htr
      · intro h
        have h' : t • u = 0 := by
          have := congrArg (· - c) h
          simpa using this
        rcases smul_eq_zero.mp h' with h0 | h0
        · exact ht0.ne' h0
        · rw [h0, norm_zero] at hu1
          exact zero_ne_one hu1
  rw [heq]
  exact ((isConnected_sphere hrank 0 zero_le_one).isPreconnected.prod isPreconnected_Ioo).image
    _ (by fun_prop : Continuous fun q : EuclideanSpace ℝ (Fin 2) × ℝ => c + q.2 • q.1).continuousOn

section Complex2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem biUnion_convexHull_superset_mem_nhdsWithin
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {t : Finset E} (ht : t ∈ K.faces)
    {y : E} (hy : y ∈ openSimplex t) :
    (⋃ σ ∈ {σ ∈ K.faces | t ⊆ σ}, convexHull ℝ (σ : Set E)) ∈ 𝓝[K.space] y := by
  set B := ⋃ σ ∈ {σ ∈ K.faces | ¬ t ⊆ σ}, convexHull ℝ (σ : Set E)
  have hB : IsClosed B := ((Set.toFinite K.faces).subset fun _ h => h.1).isClosed_biUnion
    fun σ _ => (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hyB : y ∉ B := by
    intro hyB
    obtain ⟨σ, ⟨hσ, hnt⟩, hyσ⟩ := mem_iUnion₂.mp hyB
    exact hnt (face_subset_of_mem_openSimplex_of_mem_convexHull K ht hσ hy hyσ)
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨Bᶜ, hB.isOpen_compl.mem_nhds hyB, ?_⟩
  rintro x ⟨hxB, hxK⟩
  obtain ⟨σ, hσ, hxσ⟩ := K.mem_space_iff.mp hxK
  by_cases hts : t ⊆ σ
  · exact mem_iUnion₂.mpr ⟨σ, ⟨hσ, hts⟩, hxσ⟩
  · exact (hxB (mem_iUnion₂.mpr ⟨σ, ⟨hσ, hts⟩, hxσ⟩)).elim

omit [FiniteDimensional ℝ E] in
open Classical in
theorem mem_openSimplex_pair {a b : E} (hab : a ≠ b) :
    (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ openSimplex ({a, b} : Finset E) := by
  refine ⟨fun _ => 1 / 2, fun _ _ => by norm_num, ?_, ?_⟩
  · rw [Finset.sum_pair hab]
    norm_num
  · rw [Finset.sum_pair hab]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem false_of_maximal_face_of_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces]
    (ψ : K.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {t : Finset E} (ht : t ∈ K.faces) (hcard : t.card ≤ 2)
    (hmax : ∀ σ ∈ K.faces, t ⊆ σ → σ = t) : False := by
  have htne := K.nonempty_of_mem_faces ht
  have hnhds := biUnion_convexHull_superset_mem_nhdsWithin K ht
    (centroid_mem_openSimplex htne)
  have hN : (⋃ σ ∈ {σ ∈ K.faces | t ⊆ σ}, convexHull ℝ (σ : Set E)) =
      convexHull ℝ (t : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨σ, ⟨hσ, htσ⟩, hxσ⟩ := mem_iUnion₂.mp hx
      rwa [hmax σ hσ htσ] at hxσ
    · exact fun x hx => mem_iUnion₂.mpr ⟨t, ⟨ht, subset_rfl⟩, hx⟩
  rw [hN] at hnhds
  obtain ⟨c, r, h, hr, hhc, hhi, hhm, -⟩ := exists_ball_chart_of_homeomorph_sphere_prod ψ
    (K.convexHull_subset_space ht (openSimplex_subset_convexHull t
      (centroid_mem_openSimplex htne))) hnhds
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
theorem exists_card_three_superset_of_homeomorph (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces]
    (ψ : K.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    (hcard : ∀ s ∈ K.faces, s.card ≤ 3) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  induction hn : 3 - s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs3 : s.card = 3
    · exact ⟨s, hs, subset_rfl, hs3⟩
    by_cases hmax : ∀ σ ∈ K.faces, s ⊆ σ → σ = s
    · exact (false_of_maximal_face_of_card_le_two K ψ hs (by have := hcard s hs; omega)
        hmax).elim
    push Not at hmax
    obtain ⟨σ, hσ, hsσ, hne⟩ := hmax
    have hlt : s.card < σ.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsσ, fun h => hne h.symm⟩)
    obtain ⟨t, ht, hσt, htc⟩ := ih (3 - σ.card) (by have := hcard σ hσ; omega) hσ rfl
    exact ⟨t, ht, hsσ.trans hσt, htc⟩

end Complex2

section Complex3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
theorem range_vecCons_triple (a b c : E) : range ![a, b, c] = ↑({a, b, c} : Finset E) := by
  ext x
  simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
    mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

open Classical in
theorem exists_second_triangle_of_homeomorph (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces]
    (ψ : K.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {a b c : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset E) ∈ K.faces) :
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
  have hy := mem_openSimplex_pair hab
  have hnhds := biUnion_convexHull_superset_mem_nhdsWithin K he hy
  have hN : (⋃ σ ∈ {σ ∈ K.faces | ({a, b} : Finset E) ⊆ σ}, convexHull ℝ (σ : Set E)) ⊆
      convexHull ℝ (↑({a, b, c} : Finset E) : Set E) := by
    intro x hx
    obtain ⟨σ, ⟨hσ, habσ⟩, hxσ⟩ := mem_iUnion₂.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr (hsub σ hσ habσ)) hxσ
  obtain ⟨c₀, r, h, hr, hhc, hhi, hhm, hhy⟩ := exists_ball_chart_of_homeomorph_sphere_prod ψ
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
  have hyΦ : Φ ![1 / 2, 1 / 2, 0] = (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b := by
    rw [linearCombination_triple_apply]
    simp
  have hmid : ![1 / 2, 1 / 2, 0] ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    mem_stdSimplex_triple (by norm_num) (by norm_num) le_rfl (by norm_num)
  have hΨy : Ψ ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) = ![1 / 2, 1 / 2, 0] := by
    rw [← hyΦ]
    exact hΦ.bijOn.invOn_invFunOn.1 hmid
  obtain ⟨z, hz, hzneg⟩ := exists_mem_ball_apply_one_neg_of_injOn hr hGc hGi
    (by rw [hG1, hhy, hΨy]; rfl)
  rw [hG1] at hzneg
  exact (hΨm (hhm hz).2).1 2 |>.not_gt hzneg

omit [FiniteDimensional ℝ E] in
open Classical in
theorem edgeGraph_geometricLink_connected_of_homeomorph (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces]
    (ψ : K.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {v w : E} (hv : ({v} : Finset E) ∈ K.faces) (hvw : v ≠ w)
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
  obtain ⟨c, r, h, hr, hhc, hhi, hhm, hhv⟩ := exists_ball_chart_of_homeomorph_sphere_prod ψ
    (K.convexHull_subset_space hv (by simp)) (closedStar_mem_nhdsWithin K v)
  have hW := mem_nhdsWithin_image_of_homeomorph_sphere_prod ψ Metric.isOpen_ball hhc hhi
    (fun z hz => (hhm hz).1) (Metric.mem_ball_self hr)
  rw [hhv] at hW
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW
  have hray : ∀ x : E, ({v, x} : Finset E) ∈ K.faces → x ≠ v →
      ∃ z ∈ Metric.ball c r \ {c}, h z ∈ convexHull ℝ (↑({v, x} : Finset E) : Set E) := by
    intro x hx hxv
    have hlim : Filter.Tendsto (fun t : ℝ => v + t • (x - v)) (𝓝[>] 0) (𝓝 v) := by
      have hc : Continuous fun t : ℝ => v + t • (x - v) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨t, htU, ht0, ht1⟩ :=
      ((hlim.eventually hU).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have hseg : v + t • (x - v) ∈ convexHull ℝ (↑({v, x} : Finset E) : Set E) := by
      rw [Finset.coe_pair, convexHull_pair, segment_eq_image']
      exact ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
    obtain ⟨z, hz, hzt⟩ := hUsub ⟨htU, K.convexHull_subset_space hx hseg⟩
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
    (hclosed _) (hclosed _) (fun q ⟨z, hz, hzq⟩ => hzq ▸ hcover (hhm hz.1).2)
    ⟨_, ⟨za, hza, rfl⟩, hZa⟩ ⟨_, ⟨zb, hzb, rfl⟩, hZb⟩
  have hzv : h z = v := hinter ⟨hpA, hpB⟩
  exact hz.2 (hhi hz.1 (Metric.mem_ball_self hr) (hzv.trans hhv.symm))

open Classical in
theorem isCombinatorialManifold_two_of_homeomorph_sphere_prod
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (ψ : K.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    IsCombinatorialManifold 2 K := by
  have hcard : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    by_contra h4
    obtain ⟨σ, hσs, hσ4⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
    have hσ := K.down_closed hs hσs (Finset.card_pos.mp (by omega))
    have hσ4' := hσ4
    obtain ⟨d, τ, hdτ, rfl, hτ3⟩ := Finset.card_eq_succ.mp hσ4
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hτ3
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hdτ
    have h₁ : ({a, b, c} : Finset E) ∈ K.faces :=
      K.down_closed hσ (Finset.subset_insert _ _) (by simp)
    have h₂ : ({a, b, d} : Finset E) ∈ K.faces := by
      refine K.down_closed hσ (fun x hx => ?_) (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    rcases subset_or_subset_of_hinge K ψ hab hac hbc (Ne.symm hdτ.1) (Ne.symm hdτ.2.1)
      (Ne.symm hdτ.2.2) h₁ h₂ hσ (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto) with h | h
    · have := Finset.card_le_card h
      have := Finset.card_le_three (a := a) (b := b) (c := c)
      omega
    · have := Finset.card_le_card h
      have := Finset.card_le_three (a := a) (b := b) (c := d)
      omega
  have hpure : ∀ {s : Finset E}, s ∈ K.faces → ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 :=
    fun hs => exists_card_three_superset_of_homeomorph K ψ hcard hs
  have hedge : ∀ a b : E, a ≠ b → ({a, b} : Finset E) ∈ K.faces → ∃ c₁ c₂, c₁ ≠ c₂ ∧
      {x | x ∉ ({a, b} : Finset E) ∧ insert x ({a, b} : Finset E) ∈ K.faces} = {c₁, c₂} := by
    intro a b hab he
    obtain ⟨t, ht, habt, ht3⟩ := hpure he
    have hdiff : (t \ {a, b}).card = 1 := by
      rw [Finset.card_sdiff_of_subset habt, ht3, Finset.card_pair hab]
    obtain ⟨c₁, hc₁⟩ := Finset.card_eq_one.mp hdiff
    have hc₁t : c₁ ∈ t := (Finset.mem_sdiff.mp (hc₁ ▸ Finset.mem_singleton_self c₁)).1
    have hc₁ab : c₁ ∉ ({a, b} : Finset E) :=
      (Finset.mem_sdiff.mp (hc₁ ▸ Finset.mem_singleton_self c₁)).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₁ab
    have htc : t = {a, b, c₁} := by
      rw [← Finset.sdiff_union_of_subset habt, hc₁]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [htc] at ht
    obtain ⟨c₂, hc₂a, hc₂b, hc₂c, h₂⟩ := exists_second_triangle_of_homeomorph K ψ hab
      (Ne.symm hc₁ab.1) (Ne.symm hc₁ab.2) ht
    refine ⟨c₁, c₂, Ne.symm hc₂c, ?_⟩
    ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨⟨hxa, hxb⟩, hx⟩
      have hins : insert x ({a, b} : Finset E) = {a, b, x} := by
        ext y
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hins] at hx
      rcases subset_or_subset_of_hinge K ψ hab (Ne.symm hc₁ab.1) (Ne.symm hc₁ab.2)
        (Ne.symm hc₂a) (Ne.symm hc₂b) (Ne.symm hc₂c) ht h₂ hx (fun y hy => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto) with h | h
      · have := h (by simp : x ∈ ({a, b, x} : Finset E))
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        tauto
      · have := h (by simp : x ∈ ({a, b, x} : Finset E))
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        tauto
    · rintro (rfl | rfl)
      · refine ⟨⟨hc₁ab.1, hc₁ab.2⟩, ?_⟩
        have hins : insert x ({a, b} : Finset E) = {a, b, x} := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rwa [hins]
      · refine ⟨⟨hc₂a, hc₂b⟩, ?_⟩
        have hins : insert x ({a, b} : Finset E) = {a, b, x} := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rwa [hins]
  intro v hv
  set Lk := SimplicialComplex.geometricLink K {v}
  have hmemLk (s : Finset E) : s ∈ Lk.faces ↔ s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K.faces :=
    SimplicialComplex.mem_geometricLink_singleton K v s
  have hLk1 : IsCombinatorialManifold 1 Lk := by
    refine (isCombinatorialManifold_one_iff Lk).mpr ⟨fun s hs => ?_, fun w hw => ?_⟩
    · obtain ⟨-, hvs, hins⟩ := (hmemLk s).mp hs
      have := hcard _ hins
      rw [Finset.card_insert_of_notMem hvs] at this
      omega
    · obtain ⟨-, hvw, hins⟩ := (hmemLk _).mp hw
      have hvw' : v ≠ w := fun h => hvw (by rw [h]; simp)
      obtain ⟨c₁, c₂, hc, hset⟩ := hedge v w hvw' hins
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
  obtain ⟨t, ht, hvt, ht3⟩ := hpure hv
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
    (edgeGraph_geometricLink_connected_of_homeomorph K ψ hv hwv.symm hvw)

end Complex3

theorem IsPLTorus.exists_combinatorial_triangulation
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T) :
    ∃ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hLfin : L.faces.Finite),
      letI := hLfin.to_subtype
      IsCombinatorialManifold 2 L ∧ IsConnected L.space ∧ L.space = T := by
  obtain ⟨hpoly, ⟨ψ⟩⟩ := hT
  obtain ⟨L, hLfin, hLT⟩ := hpoly.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  subst hLT
  refine ⟨L, hLfin, isCombinatorialManifold_two_of_homeomorph_sphere_prod L ψ, ?_, rfl⟩
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
    norm_num
  have : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 zero_le_one)
  have hrange : range (fun p => ((ψ.symm p : L.space) : EuclideanSpace ℝ (Fin 3))) =
      L.space := by
    rw [← Function.comp_def, range_comp, ψ.symm.surjective.range_eq, image_univ,
      Subtype.range_val]
  rw [← hrange]
  exact isConnected_range (continuous_subtype_val.comp ψ.symm.continuous)

end DifferentialGeometry.Topology.PiecewiseLinear
