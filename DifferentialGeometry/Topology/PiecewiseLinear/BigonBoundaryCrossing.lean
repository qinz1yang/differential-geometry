/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCurveCrossingOnAt.of_openPartialHomeomorph
    {S A B S' A' B' : Set E} {x : E} (e : OpenPartialHomeomorph E E)
    (he : IsPiecewiseAffineOn e e.source) (hx : x ∈ e.source)
    (hcross : HasPLCurveCrossingOnAt S' A' B' (e x))
    (hS : ∀ᶠ y in 𝓝 x, y ∈ S ↔ e y ∈ S')
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔ e y ∈ A')
    (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ e y ∈ B') : HasPLCurveCrossingOnAt S A B x := by
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ,
    hlocal⟩ := hcross
  let k := e.trans (hφ.toOpenPartialHomeomorph hU hV)
  have hkpa : IsPiecewiseAffineOn k k.source := hφ.isPiecewiseAffineOn.comp he
  have hxk : x ∈ k.source := ⟨hx, hxU⟩
  refine ⟨k.source, k.target, k, T, P, Q, k.open_source, k.open_target, hxk,
    isPLHomeomorphOn_openPartialHomeomorph k hkpa, hφx, hT, hP, hQ, hPT, hQT, hPQ, ?_⟩
  filter_upwards [(e.continuousAt hx).tendsto.eventually hlocal, hS, hA, hB]
    with y hy hyS hyA hyB
  exact ⟨hyS.trans hy.1, hyA.trans hy.2.1, hyB.trans hy.2.2⟩

theorem HasPLCurveCrossingOnAt.image_chart_of_mem_maximalAtlas
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hc' : c' ∈ (plGroupoid 3).maximalAtlas M)
    {S A B : Set M} {x : M} (hx : x ∈ c.source) (hx' : x ∈ c'.source)
    (hcross : HasPLCurveCrossingOnAt (c' '' (S ∩ c'.source))
      (c' '' (A ∩ c'.source)) (c' '' (B ∩ c'.source)) (c' x)) :
    HasPLCurveCrossingOnAt (c '' (S ∩ c.source)) (c '' (A ∩ c.source))
      (c '' (B ∩ c.source)) (c x) := by
  let e := c.symm.trans c'
  have he : e ∈ plGroupoid 3 := StructureGroupoid.compatible_of_mem_maximalAtlas hc hc'
  have hepa : IsPiecewiseAffineOn e e.source := (mem_plGroupoid_iff.mp he).1
  have hsrc : ∀ z, z ∈ e.source ↔ z ∈ c.target ∧ c.symm z ∈ c'.source := fun z => by
    simp [e]
  have happ : ∀ z, e z = c' (c.symm z) := fun _ => rfl
  have hxe : c x ∈ e.source :=
    (hsrc _).mpr ⟨c.map_source hx, by rw [c.left_inv hx]; exact hx'⟩
  have hex : e (c x) = c' x := by rw [happ, c.left_inv hx]
  have hmem : ∀ (Z : Set M) {z}, z ∈ e.source →
      (z ∈ c '' (Z ∩ c.source) ↔ e z ∈ c' '' (Z ∩ c'.source)) := by
    intro Z z hz
    obtain ⟨hzt, hz'⟩ := (hsrc z).mp hz
    rw [happ]
    constructor
    · rintro ⟨a, ⟨haZ, has⟩, rfl⟩
      rw [c.left_inv has] at hz' ⊢
      exact ⟨a, ⟨haZ, hz'⟩, rfl⟩
    · rintro ⟨a, ⟨haZ, has'⟩, hae⟩
      have hae' : a = c.symm z := c'.injOn has' hz' hae
      refine ⟨a, ⟨haZ, ?_⟩, ?_⟩
      · rw [hae']
        exact c.map_target hzt
      · rw [hae']
        exact c.right_inv hzt
  refine HasPLCurveCrossingOnAt.of_openPartialHomeomorph e hepa hxe (hex ▸ hcross) ?_ ?_ ?_
  · filter_upwards [e.open_source.mem_nhds hxe] with z hz using hmem S hz
  · filter_upwards [e.open_source.mem_nhds hxe] with z hz using hmem A hz
  · filter_upwards [e.open_source.mem_nhds hxe] with z hz using hmem B hz

omit [FiniteDimensional ℝ E] in
private theorem exists_preconnected_diskInterior {D : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {x : E} (hx : x ∈ D)
    {O : Set E} (hO : O ∈ 𝓝 x) :
    ∃ L : Set E, L ⊆ O ∧ L ⊆ D \ q '' stdSimplexBoundary 2 ∧ IsPreconnected L ∧
      ∃ O' : Set E, IsOpen O' ∧ x ∈ O' ∧
        O' ∩ (D \ q '' stdSimplexBoundary 2) ⊆ L := by
  obtain ⟨b, hb, rfl⟩ := hq.bijOn.surjOn hx
  have hqc := hq.isPiecewiseAffineOn.continuousOn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hqc b hb).preimage_mem_nhdsWithin hO)
  obtain ⟨T, hT, hTeq⟩ := exists_isOpen_inter_image_eq_of_isCompact
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)) hqc hq.bijOn.injOn (Metric.isOpen_ball (x := b) (ε := r))
  have hsub : Metric.ball b r ∩ openSimplex (stdVertices 1) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    inter_subset_right.trans openSimplex_stdVertices_subset_stdSimplex
  refine ⟨q '' (Metric.ball b r ∩ openSimplex (stdVertices 1)), ?_, ?_, ?_, T, hT, ?_, ?_⟩
  · rintro _ ⟨z, ⟨hzr, hzo⟩, rfl⟩
    exact hball ⟨hzr, openSimplex_stdVertices_subset_stdSimplex hzo⟩
  · rw [← hq.image_openSimplex_stdVertices]
    exact image_mono inter_subset_right
  · exact ((convex_ball b r).inter (convex_openSimplex _)).isPreconnected.image q
      (hqc.mono hsub)
  · have hm : q b ∈ q '' (Metric.ball b r ∩ Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
      ⟨b, ⟨Metric.mem_ball_self hr, hb⟩, rfl⟩
    rw [← hTeq] at hm
    exact hm.1
  · rw [← hq.image_openSimplex_stdVertices]
    rintro _ ⟨hyT, z, hzo, rfl⟩
    have hzΔ : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := openSimplex_stdVertices_subset_stdSimplex hzo
    have hm : q z ∈ T ∩ q '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := ⟨hyT, z, hzΔ, rfl⟩
    rw [hTeq] at hm
    obtain ⟨w, ⟨hwr, hwΔ⟩, hwz⟩ := hm
    have hwz' : w = z := hq.bijOn.injOn hwΔ hzΔ hwz
    rw [hwz'] at hwr
    exact ⟨z, ⟨hwr, hzo⟩, rfl⟩

theorem HasPLCurveCrossingOnAt.eventually_mem_arc_iff {S A B C : Set E} {x : E}
    (hcross : HasPLCurveCrossingOnAt S A B x) {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) C) (hCB : C ⊆ B)
    (hx : x ∈ C \ {γ 0, γ 1}) : ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ B := by
  classical
  obtain ⟨U, V, φ, T, P, Q, hU, -, hxU, hφ, -, -, -, hQ, -, -, -, hlocal⟩ := hcross
  have hsmall : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (y ∈ B ↔ φ y ∈ Q) := by
    filter_upwards [hU.mem_nhds hxU, hlocal] with y hyU hy
    exact ⟨hyU, hy.2.2⟩
  obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hsmall
  have hQne : Q ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hQ
    omega
  obtain ⟨v, hvQ, hv0⟩ := Q.ne_bot_iff.mp hQne
  obtain ⟨ℓ, hℓv⟩ := Module.Projective.exists_dual_ne_zero ℝ hv0
  have hspan : Submodule.span ℝ {v} = Q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rwa [Submodule.span_singleton_le_iff_mem]
    · rw [finrank_span_singleton hv0, hQ]
  have hℓinj : InjOn ℓ (Q : Set E) := by
    intro y hy z hz hyz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan.symm ▸ Q.sub_mem hy hz)
    have haz : a * ℓ v = 0 := by
      simpa only [map_smul, smul_eq_mul, map_sub, hyz, sub_self] using congrArg ℓ ha
    have ha0 : a = 0 := (mul_eq_zero.mp haz).resolve_right hℓv
    apply sub_eq_zero.mp
    rw [← ha, ha0, zero_smul]
  obtain ⟨t, ht, htx⟩ := hγ.bijOn.surjOn hx.1
  have ht0 : t ≠ 0 := fun h => hx.2 (Or.inl (htx.symm.trans (congrArg γ h)))
  have ht1 : t ≠ 1 := fun h => hx.2 (Or.inr (htx.symm.trans (congrArg γ h)))
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
    lt_of_le_of_ne ht.2 ht1⟩
  let W := Ioo (0 : ℝ) 1 ∩ γ ⁻¹' O
  have hγc := hγ.isPiecewiseAffineOn.continuousOn
  have hW : IsOpen W := (hγc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo hO
  have htW : t ∈ W := ⟨htI, by change γ t ∈ O; rwa [htx]⟩
  have hγW : MapsTo γ W U := fun s hs => (hOO hs.2).1
  have hγQ : ∀ s ∈ W, φ (γ s) ∈ Q := fun s hs =>
    (hOO hs.2).2.mp (hCB (hγ.bijOn.mapsTo (Ioo_subset_Icc_self hs.1)))
  let f : E → ℝ := fun y => ℓ (φ y)
  have hfc : ContinuousOn f U := ℓ.continuous_of_finiteDimensional.comp_continuousOn
    hφ.isPiecewiseAffineOn.continuousOn
  have hcomp : ContinuousOn (f ∘ γ) W := hfc.comp
    (hγc.mono (inter_subset_left.trans Ioo_subset_Icc_self)) hγW
  have hinj : InjOn (f ∘ γ) W := by
    intro s hs r hr heq
    exact hγ.bijOn.injOn (Ioo_subset_Icc_self hs.1) (Ioo_subset_Icc_self hr.1)
      (hφ.bijOn.injOn (hγW hs) (hγW hr) (hℓinj (hγQ s hs) (hγQ r hr) heq))
  have himg : IsOpen ((f ∘ γ) '' W) :=
    invariance_of_domain_isOpen_image_of_finrank_eq rfl hW hcomp hinj
  have hN : IsOpen (O ∩ f ⁻¹' ((f ∘ γ) '' W)) :=
    (hfc.mono fun y hy => (hOO hy).1).isOpen_inter_preimage hO himg
  have hxN : x ∈ O ∩ f ⁻¹' ((f ∘ γ) '' W) := ⟨hxO, t, htW, congrArg f htx⟩
  filter_upwards [hN.mem_nhds hxN] with y hy
  refine ⟨fun hyC => hCB hyC, fun hyB => ?_⟩
  obtain ⟨s, hs, hsy⟩ := hy.2
  have hφeq : φ (γ s) = φ y := hℓinj (hγQ s hs) ((hOO hy.1).2.mp hyB) hsy
  have hγeq : γ s = y := hφ.bijOn.injOn (hγW hs) (hOO hy.1).1 hφeq
  exact hγeq ▸ hγ.bijOn.mapsTo (Ioo_subset_Icc_self hs.1)

theorem HasPLCurveCrossingOnAt.mem_closure_inter_diskInterior {S A B D : Set E} {x : E}
    (hcross : HasPLCurveCrossingOnAt S A B x) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDS : D ⊆ S)
    (hboundary : ∀ᶠ y in 𝓝 x, y ∈ q '' stdSimplexBoundary 2 ↔ y ∈ B) :
    x ∈ closure (A ∩ (D \ q '' stdSimplexBoundary 2)) := by
  classical
  by_contra hxcl
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ,
    hlocal⟩ := hcross
  have hxB : x ∈ B := (hlocal.self_of_nhds).2.2.mpr (hφx ▸ Q.zero_mem)
  have hxJ : x ∈ q '' stdSimplexBoundary 2 := hboundary.self_of_nhds.mpr hxB
  have hJD : q '' stdSimplexBoundary 2 ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩
    exact hq.bijOn.mapsTo hz.1
  have hsmall : ∀ᶠ y in 𝓝 x, y ∈ U ∧
      (y ∈ S ↔ φ y ∈ T) ∧ (y ∈ A ↔ φ y ∈ P) ∧ (y ∈ B ↔ φ y ∈ Q) ∧
      (y ∈ q '' stdSimplexBoundary 2 ↔ y ∈ B) ∧
      y ∉ A ∩ (D \ q '' stdSimplexBoundary 2) := by
    filter_upwards [hU.mem_nhds hxU, hlocal, hboundary,
      isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hyU hy hyJ hycl
    exact ⟨hyU, hy.1, hy.2.1, hy.2.2, hyJ, fun hyA => hycl (subset_closure hyA)⟩
  obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hsmall
  have hQne : Q ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hQ
    omega
  obtain ⟨v, hvQ, hv0⟩ := Q.ne_bot_iff.mp hQne
  have hvP : v ∉ P := by
    intro hvP
    have hv : v ∈ (P ⊓ Q : Submodule ℝ E) := ⟨hvP, hvQ⟩
    rw [hPQ] at hv
    exact hv0 hv
  obtain ⟨ℓ, hℓv, hPℓ⟩ := P.exists_le_ker_of_notMem hvP
  have hPK : P ≤ T ⊓ LinearMap.ker ℓ := le_inf hPT hPℓ
  have hKT : T ⊓ LinearMap.ker ℓ < T := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hv : v ∈ T ⊓ LinearMap.ker ℓ := heq.symm ▸ hQT hvQ
    exact hℓv hv.2
  have hker : P = T ⊓ LinearMap.ker ℓ := by
    apply Submodule.eq_of_le_of_finrank_eq hPK
    have hlo := Submodule.finrank_mono hPK
    have hhi := Submodule.finrank_lt_finrank_of_lt hKT
    omega
  let w := (ℓ v)⁻¹ • v
  have hwQ : w ∈ Q := Q.smul_mem _ hvQ
  have hℓw : ℓ w = 1 := by simp [w, hℓv]
  let f : E → ℝ := fun y => ℓ (φ y)
  have hfc : ContinuousOn f U := ℓ.continuous_of_finiteDimensional.comp_continuousOn
    hφ.isPiecewiseAffineOn.continuousOn
  obtain ⟨L, hLO, hLD, hLconn, O', hO', hxO', hO'L⟩ :=
    exists_preconnected_diskInterior hq (hJD hxJ) (hO.mem_nhds hxO)
  have hLU : L ⊆ U := fun y hy => (hOO (hLO hy)).1
  have hfne : ∀ y ∈ L, f y ≠ 0 := by
    intro y hy hfy
    have hyO := hOO (hLO hy)
    have hyT : φ y ∈ T := hyO.2.1.mp (hDS (hLD hy).1)
    have hyP : φ y ∈ P := hker.symm ▸ ⟨hyT, hfy⟩
    exact hyO.2.2.2.2.2 ⟨hyO.2.2.1.mpr hyP, hLD hy⟩
  have hside : (∀ y ∈ L, f y < 0) ∨ (∀ y ∈ L, 0 < f y) := by
    have hconn := hLconn.image f (hfc.mono hLU)
    have hcover : f '' L ⊆ Iio 0 ∪ Ioi 0 := by
      rintro _ ⟨y, hy, rfl⟩
      exact (lt_or_gt_of_ne (hfne y hy)).elim Or.inl Or.inr
    have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) := disjoint_left.mpr fun z hz hz' =>
      (not_lt_of_ge (show 0 ≤ z from le_of_lt hz')) hz
    exact (hconn.subset_or_subset isOpen_Iio isOpen_Ioi hdisj hcover).imp
      (fun h y hy => h ⟨y, hy, rfl⟩) (fun h y hy => h ⟨y, hy, rfl⟩)
  have hDcl : O' ∩ D ⊆ closure L := by
    intro y hy
    have hycl : y ∈ closure (O' ∩ (D \ q '' stdSimplexBoundary 2)) :=
      hO'.inter_closure ⟨hy.1, hq.closure_sdiff_image_stdSimplexBoundary.symm ▸ hy.2⟩
    exact closure_mono hO'L hycl
  let ψ := Function.invFunOn φ U
  have h0V : (0 : E) ∈ V := hφx ▸ hφ.bijOn.mapsTo hxU
  have hψ0 : ψ 0 = x := by
    rw [← hφx]
    exact hφ.bijOn.invOn_invFunOn.1 hxU
  have hψc : ContinuousAt ψ 0 := hφ.isPiecewiseAffineOn_invFunOn.continuousOn.continuousAt
    (hV.mem_nhds h0V)
  let g : ℝ → E := fun t => ψ (t • w)
  have hg0 : g 0 = x := by simp [g, hψ0]
  have hgc : ContinuousAt g 0 := by
    have hψc' : ContinuousAt ψ ((0 : ℝ) • w) := by simpa using hψc
    exact ContinuousAt.comp (f := fun t : ℝ => t • w) (g := ψ) hψc'
      (show ContinuousAt (fun t : ℝ => t • w) 0 by fun_prop)
  have hgn : ∀ᶠ t in 𝓝 (0 : ℝ), t • w ∈ V ∧ g t ∈ O ∩ O' := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), t • w ∈ V :=
      (by fun_prop : Continuous (fun t : ℝ => t • w)).continuousAt.preimage_mem_nhds
        (by simpa using hV.mem_nhds h0V)
    exact h1.and (hgc.preimage_mem_nhds (hg0.symm ▸ (hO.inter hO').mem_nhds ⟨hxO, hxO'⟩))
  obtain ⟨δ, hδ, hδg⟩ := Metric.mem_nhds_iff.mp hgn
  have hgt : ∀ t ∈ ball (0 : ℝ) δ, g t ∈ U ∩ closure L ∧ f (g t) = t := by
    intro t ht
    obtain ⟨htV, htO, htO'⟩ := hδg ht
    have hφg : φ (g t) = t • w := hφ.bijOn.invOn_invFunOn.2 htV
    have hdata := hOO htO
    have htB : g t ∈ B := hdata.2.2.2.1.mpr (hφg ▸ Q.smul_mem t hwQ)
    have htD : g t ∈ D := hJD (hdata.2.2.2.2.1.mpr htB)
    refine ⟨⟨hdata.1, hDcl ⟨htO', htD⟩⟩, ?_⟩
    change ℓ (φ (g t)) = t
    rw [hφg, map_smul, smul_eq_mul, hℓw, mul_one]
  have hpos : δ / 2 ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  have hneg : -(δ / 2) ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]
    linarith
  have hclosure : ∀ y ∈ U ∩ closure L, f y ∈ closure (f '' L) := by
    intro y hy
    exact (hfc.continuousAt (hU.mem_nhds hy.1)).continuousWithinAt.mem_closure_image hy.2
  rcases hside with hside | hside
  · have hle : f (g (δ / 2)) ≤ 0 := closure_minimal
      (by rintro z ⟨y, hy, rfl⟩; exact (hside y hy).le) isClosed_Iic
      (hclosure _ (hgt _ hpos).1)
    rw [(hgt _ hpos).2] at hle
    linarith
  · have hle : 0 ≤ f (g (-(δ / 2))) := closure_minimal
      (by rintro z ⟨y, hy, rfl⟩; exact (hside y hy).le) isClosed_Ici
      (hclosure _ (hgt _ hneg).1)
    rw [(hgt _ hneg).2] at hle
    linarith

theorem inter_subset_endpoints_of_disk_boundary_crossing {S A B C D F : Set E}
    {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDS : D ⊆ S) {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) C)
    (hCB : C ⊆ B) (hF : IsClosed F)
    (hFC : F ∩ C = {γ 0, γ 1}) (hJ : q '' stdSimplexBoundary 2 = F ∪ C)
    (hclean : Disjoint (D \ q '' stdSimplexBoundary 2) A)
    (hcross : ∀ x ∈ A ∩ C, HasPLCurveCrossingOnAt S A B x) :
    A ∩ C ⊆ {γ 0, γ 1} := by
  rintro x ⟨hxA, hxC⟩
  by_contra hxends
  have hxF : x ∉ F := fun hxF => hxends (hFC ▸ ⟨hxF, hxC⟩)
  have hc := hcross x ⟨hxA, hxC⟩
  have hCeq := hc.eventually_mem_arc_iff hγ hCB ⟨hxC, hxends⟩
  have hboundary : ∀ᶠ y in 𝓝 x, y ∈ q '' stdSimplexBoundary 2 ↔ y ∈ B := by
    filter_upwards [hF.isOpen_compl.mem_nhds hxF, hCeq] with y hyF hyC
    have hyF' : y ∉ F := hyF
    rw [hJ]
    simpa only [mem_union, hyF', false_or] using hyC
  have hcl := hc.mem_closure_inter_diskInterior hq hDS hboundary
  have hempty : A ∩ (D \ q '' stdSimplexBoundary 2) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hclean.symm
  rw [hempty, closure_empty] at hcl
  exact hcl

theorem inter_eq_endpoints_of_disk_boundary_crossing {S A B C D F : Set E}
    {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDS : D ⊆ S) {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) C)
    (hCB : C ⊆ B) (hF : IsClosed F) (hFA : F ⊆ A)
    (hFC : F ∩ C = {γ 0, γ 1}) (hJ : q '' stdSimplexBoundary 2 = F ∪ C)
    (hclean : Disjoint (D \ q '' stdSimplexBoundary 2) A)
    (hcross : ∀ x ∈ A ∩ C, HasPLCurveCrossingOnAt S A B x) :
    A ∩ C = {γ 0, γ 1} := by
  apply subset_antisymm
  · exact inter_subset_endpoints_of_disk_boundary_crossing hq hDS hγ hCB hF hFC hJ
      hclean hcross
  · intro x hxends
    have hxFC : x ∈ F ∩ C := hFC.symm ▸ hxends
    exact ⟨hFA hxFC.1, hxFC.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
