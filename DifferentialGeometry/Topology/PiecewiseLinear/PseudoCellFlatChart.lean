/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarGluing
import DifferentialGeometry.Topology.PiecewiseLinear.CollarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceInteriorFrontierOpen
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "P2" => EuclideanSpace ℝ (Fin 2)

theorem IsPLHomeomorphOn.notMem_image_stdSimplexBoundary_of_mem_nhdsWithin {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {M D : Set F}
    (hM : IsOpenTopologicalCell 2 M) {f : (Fin 3 → ℝ) → F}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {x : F} (hxM : x ∈ M)
    (hD : D ∈ 𝓝[M] x) : x ∉ f '' stdSimplexBoundary 2 := by
  classical
  rintro ⟨q, hq, hqx⟩
  obtain ⟨ψ⟩ := hM
  obtain ⟨c, ϱ, γ, hϱ, hγc, hγi, hγmaps, hγc0⟩ :=
    exists_ball_chart_of_homeomorph_isOpen Metric.isOpen_ball ψ hxM hD
  set g := Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) with hgdef
  have hg := hf.symm
  have hgf : ∀ p ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), g (f p) = p := fun p hp =>
    hf.bijOn.invOn_invFunOn.1 hp
  let proj : (Fin 3 → ℝ) → P2 := fun p => WithLp.toLp 2 fun i : Fin 2 => p (Fin.castSucc i)
  have hproj0 : ∀ p, proj p 0 = p 0 := fun p => rfl
  have hproj1 : ∀ p, proj p 1 = p 1 := fun p => rfl
  have hprojc : Continuous proj := by fun_prop
  have hσsum : ∀ p ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), p 0 + p 1 + p 2 = 1 := by
    intro p hp
    have := hp.2
    rwa [Fin.sum_univ_three] at this
  have hprojinj : InjOn proj (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := by
    intro p hp p' hp' h
    have h0 : p 0 = p' 0 := by rw [← hproj0 p, ← hproj0 p', h]
    have h1 : p 1 = p' 1 := by rw [← hproj1 p, ← hproj1 p', h]
    have h2 : p 2 = p' 2 := by linarith [hσsum p hp, hσsum p' hp']
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  let κ : P2 → P2 := fun w => proj (g (γ w))
  have hγD : MapsTo γ (Metric.ball c ϱ) D := fun w hw => (hγmaps hw).2
  have hgσ : MapsTo g D (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hg.bijOn.mapsTo
  have hκc : ContinuousOn κ (Metric.ball c ϱ) :=
    hprojc.comp_continuousOn (hg.isPiecewiseAffineOn.continuousOn.comp hγc hγD)
  have hκi : InjOn κ (Metric.ball c ϱ) := by
    intro w hw w' hw' h
    exact hγi hw hw' (hg.bijOn.injOn (hγD hw) (hγD hw') (hprojinj (hgσ (hγD hw))
      (hgσ (hγD hw')) h))
  have hopen := DifferentialGeometry.Topology.invariance_of_domain_isOpen_image
    Metric.isOpen_ball hκc hκi
  have hqσ : q ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := hq.1
  have hκcq : κ c = proj q := by
    change proj (g (γ c)) = proj q
    rw [hγc0, ← hqx, hgf q hqσ]
  have hsub : κ '' Metric.ball c ϱ ⊆ proj '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨g (γ w), hgσ (hγD hw), rfl⟩
  have hnear : ∀ v : P2, ∃ t : ℝ, 0 < t ∧ proj q + t • v ∈ κ '' Metric.ball c ϱ := by
    intro v
    have hmem : proj q ∈ κ '' Metric.ball c ϱ := ⟨c, Metric.mem_ball_self hϱ, hκcq⟩
    have htend : Filter.Tendsto (fun t : ℝ => proj q + t • v) (𝓝[>] 0) (𝓝 (proj q)) := by
      have h : Filter.Tendsto (fun t : ℝ => proj q + t • v) (𝓝 0) (𝓝 (proj q)) := by
        have h' : Filter.Tendsto (fun t : ℝ => proj q + t • v) (𝓝 0)
            (𝓝 (proj q + (0 : ℝ) • v)) :=
          tendsto_const_nhds.add (Filter.tendsto_id.smul_const v)
        rwa [zero_smul, add_zero] at h'
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, htpos⟩ :=
      ((htend.eventually (hopen.mem_nhds hmem)).and self_mem_nhdsWithin).exists
    exact ⟨t, htpos, ht⟩
  obtain ⟨hq0, i, hi⟩ := hq
  have hnonneg : ∀ p ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ∀ j, 0 ≤ p j := fun p hp j => hp.1 j
  fin_cases i
  · have hi' : q 0 = 0 := hi
    obtain ⟨t, ht, hmem⟩ := hnear (WithLp.toLp 2 ![-1, 0])
    obtain ⟨p, hp, hpe⟩ := hsub hmem
    have h0 := congrArg (fun z : P2 => z 0) hpe
    simp [hproj0] at h0
    have := hnonneg p hp 0
    linarith
  · have hi' : q 1 = 0 := hi
    obtain ⟨t, ht, hmem⟩ := hnear (WithLp.toLp 2 ![0, -1])
    obtain ⟨p, hp, hpe⟩ := hsub hmem
    have h1 := congrArg (fun z : P2 => z 1) hpe
    simp [hproj1] at h1
    have := hnonneg p hp 1
    linarith
  · have hi' : q 2 = 0 := hi
    obtain ⟨t, ht, hmem⟩ := hnear (WithLp.toLp 2 ![1, 1])
    obtain ⟨p, hp, hpe⟩ := hsub hmem
    have h0 := congrArg (fun z : P2 => z 0) hpe
    simp [hproj0] at h0
    have h1 := congrArg (fun z : P2 => z 1) hpe
    simp [hproj1] at h1
    have hq' := hσsum q hqσ
    have hp' := hσsum p hp
    have := hnonneg p hp 2
    linarith

theorem IsPseudoCell.exists_flatChart {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) {x : E3} (hx : x ∈ Eint) (hxP : x ≠ P) {O : Set E3}
    (hO : O ∈ 𝓝 x) :
    ∃ (U : Set E3) (V : Set (ℝ × ℝ × ℝ)) (φ : E3 → ℝ × ℝ × ℝ), IsOpen U ∧ IsOpen V ∧
      x ∈ U ∧ U ⊆ O ∧ IsPLHomeomorphOn φ U V ∧ ∀ y ∈ U, (y ∈ Ec ↔ (φ y).2.2 = 0) := by
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨L, hLfin, hL, hag⟩ := exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff
    (ι := Unit) {()} (M := fun _ => Eint) (Cc := fun _ => {x}) (P := fun _ => P)
    (fun _ _ => hpc.isOpenCell) (fun _ _ => hpc.regular)
    (fun i _ j _ hij => (hij (Subsingleton.elim i j)).elim)
    (fun _ _ => isCompact_singleton)
    (fun _ _ => singleton_subset_iff.mpr ⟨hx, hxP⟩)
  have : Finite L.faces := hLfin.to_subtype
  have hagx : ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ y ∈ Eint :=
    hag () (Finset.mem_singleton_self _) x (mem_singleton x)
  have hxL : x ∈ L.space := hagx.self_of_nhds.mpr hx
  have hxB : x ∉ (boundaryComplex 2 L).space := by
    intro hxB
    obtain ⟨R, hRL, hRfin, hxR⟩ := exists_isSubdivision_singleton_mem L hxL
    have : Finite R.faces := hRfin.to_subtype
    obtain ⟨ψ⟩ := hpc.isOpenCell
    have hsph := isPLSphere_one_geometricLink_of_homeomorph R Metric.isOpen_ball ψ hxR
      (by rw [hRL.space_eq]; exact hagx)
    have hball := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision (n := 1)
      L R hL hRL hxR).mpr hxB
    exact hball.not_isPLSphere hsph
  obtain ⟨W₀, hW₀p, hW₀, hxW₀⟩ := eventually_nhds_iff.mp hagx
  have hbdc : IsClosed Ebd := by
    obtain ⟨φ⟩ := hpc.isSphere
    exact (isCompact_iff_compactSpace.mpr φ.symm.compactSpace).isClosed
  have hxbd : x ∉ Ebd := fun h => Set.disjoint_left.mp hpc.disjointRim hx h
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  obtain ⟨T, hT, hTcard, hLT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space L).isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E3) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hLint : L.space ⊆ interior K.space := hLT.trans hint.symm.subset
  have hxKB : x ∉ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact fun h => h.2 (hLint hxL)
  have hKnhds : K.space ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (hLint hxL)
  have hU₀ : O ∩ W₀ ∩ Ebdᶜ ∈ 𝓝[K.space] x :=
    mem_nhdsWithin_of_mem_nhds (Filter.inter_mem (Filter.inter_mem hO (hW₀.mem_nhds hxW₀))
      (hbdc.isOpen_compl.mem_nhds hxbd))
  obtain ⟨C, hC, hCsub, hCnhds, hDQ, a, ha, b, hb, hdisj, hunion, hQa, hQb, hQab, hQint⟩ :=
    exists_isPLBall_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary hK hL
      (hLint.trans interior_subset) ⟨hxL, hxB⟩ hxKB hU₀
  set Qa := closure (connectedComponentIn (C \ L.space) a) with hQadef
  set Qb := closure (connectedComponentIn (C \ L.space) b) with hQbdef
  set DQ := C ∩ L.space with hDQdef
  have hCO : C ⊆ O := fun y hy => (hCsub hy).2.1.1
  have hCW : ∀ y ∈ C, (y ∈ L.space ↔ y ∈ Ec) := by
    intro y hy
    rw [hW₀p y (hCsub hy).2.1.2, hpc.carrierEq]
    exact ⟨Or.inl, fun h => h.resolve_right (hCsub hy).2.2⟩
  have hccsub : ∀ z : E3, connectedComponentIn (C \ L.space) z ⊆ C \ L.space := fun z =>
    connectedComponentIn_subset _ _
  have hDQfr : ∀ {Q Q' : Set E3} {z' : E3}, Q ∩ Q' = DQ →
      Q' = closure (connectedComponentIn (C \ L.space) z') → DQ ⊆ frontier Q := by
    intro Q Q' z' hQQ' hQ' y hy
    have hyQ : y ∈ Q := (hQQ'.symm ▸ hy : y ∈ Q ∩ Q').1
    have hyQ' : y ∈ Q' := (hQQ'.symm ▸ hy : y ∈ Q ∩ Q').2
    refine ⟨subset_closure hyQ, fun hyint => ?_⟩
    rw [hQ'] at hyQ'
    obtain ⟨z, hzU, hzcc⟩ := mem_closure_iff_nhds.mp hyQ' _ (mem_interior_iff_mem_nhds.mp hyint)
    have hzQ' : z ∈ Q' := hQ' ▸ subset_closure hzcc
    have hzD : z ∈ DQ := hQQ' ▸ ⟨hzU, hzQ'⟩
    exact (hccsub z' hzcc).2 hzD.2
  have hDQa : DQ ⊆ frontier Qa := hDQfr hQint rfl
  have hDQb : DQ ⊆ frontier Qb := hDQfr ((inter_comm Qb Qa).trans hQint) rfl
  have hDQpoly : IsPolyhedron DQ := hDQ.isPolyhedron
  have hcollar : ∀ Q : Set E3, IsPLBall 3 Q → DQ ⊆ frontier Q →
      ∃ ρ : E3 × ℝ → E3, IsPLHomeomorphOn ρ (DQ ×ˢ Icc (0 : ℝ) 1) (ρ '' (DQ ×ˢ Icc 0 1)) ∧
        ρ '' (DQ ×ˢ Icc 0 1) ⊆ Q ∧ ∀ y ∈ DQ, ρ (y, 0) = y := by
    intro Q hQ hDQQ
    obtain ⟨KQ, hKQfin, hKQ⟩ := hQ.isPolyhedron.exists_simplicialComplex
    have : Finite KQ.faces := hKQfin.to_subtype
    have hKQm : IsCombinatorialManifoldWithBoundary 3 KQ :=
      IsPLBall.isCombinatorialManifoldWithBoundary (n := 2) (by rw [hKQ]; exact hQ)
    obtain ⟨W, ρ, -, hWK, -, hρ, hbot, -, -⟩ := hKQm.exists_collar KQ
    have hfr : frontier KQ.space = (boundaryComplex 3 KQ).space :=
      frontier_space_eq_boundaryComplex_space_of_finrank hdim KQ hKQm
    have hDQB : DQ ⊆ (boundaryComplex 3 KQ).space := by
      rw [← hfr, hKQ]
      exact hDQQ
    have hsubset : DQ ×ˢ Icc (0 : ℝ) 1 ⊆ (boundaryComplex 3 KQ).space ×ˢ Icc 0 1 :=
      prod_mono hDQB subset_rfl
    refine ⟨ρ, hρ.restrict (hDQpoly.prod isHPolytope_Icc.isPolyhedron) hsubset, ?_,
      fun y hy => hbot y (hDQB hy)⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [← hKQ]
    exact hWK (hρ.bijOn.mapsTo (hsubset hz))
  obtain ⟨ρa, hρa, hAQa, hρa0⟩ := hcollar Qa hQa hDQa
  obtain ⟨ρb, hρb, hBQb, hρb0⟩ := hcollar Qb hQb hDQb
  have hAB : ρa '' (DQ ×ˢ Icc 0 1) ∩ ρb '' (DQ ×ˢ Icc 0 1) = DQ := by
    apply Subset.antisymm
    · rintro y ⟨hya, hyb⟩
      rw [← hQint]
      exact ⟨hAQa hya, hBQb hyb⟩
    · intro y hy
      exact ⟨⟨(y, 0), ⟨hy, by norm_num, by norm_num⟩, hρa0 y hy⟩,
        ⟨(y, 0), ⟨hy, by norm_num, by norm_num⟩, hρb0 y hy⟩⟩
  obtain ⟨ρ, hρ, hρ0, hρneg, hρpos⟩ :=
    exists_isPLHomeomorphOn_prod_Icc_of_collars hDQpoly hρa hρb hρa0 hρb0 hAB
  obtain ⟨f, hf⟩ := hDQ
  have hxC : x ∈ C := mem_of_mem_nhds (by
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hLint hxL))] at hCnhds)
  have hCn : C ∈ 𝓝 x := by
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hLint hxL))] at hCnhds
  have hxDQ : x ∈ DQ := ⟨hxC, hxL⟩
  have hDnhds : DQ ∈ 𝓝[Eint] x := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨C ∩ W₀, Filter.inter_mem hCn
      (hW₀.mem_nhds hxW₀), fun y hy => ⟨hy.1.1, (hW₀p y hy.1.2).mpr hy.2⟩⟩
  have hxnot := hf.notMem_image_stdSimplexBoundary_of_mem_nhdsWithin hpc.isOpenCell hx hDnhds
  set q₀ := Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x with hq₀def
  have hq₀σ : q₀ ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := hf.bijOn.surjOn.mapsTo_invFunOn hxDQ
  have hfq₀ : f q₀ = x := hf.bijOn.invOn_invFunOn.2 hxDQ
  have hq₀pos : ∀ i, 0 < q₀ i := by
    intro i
    refine lt_of_le_of_ne (hq₀σ.1 i) fun h => hxnot ⟨q₀, ⟨hq₀σ, i, h.symm⟩, hfq₀⟩
  have hσsum : ∀ p ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), p 0 + p 1 + p 2 = 1 := by
    intro p hp
    have := hp.2
    rwa [Fin.sum_univ_three] at this
  let κL : ((Fin 3 → ℝ) × ℝ) →ₗ[ℝ] ℝ × ℝ × ℝ :=
    ((LinearMap.proj 0).comp (LinearMap.fst ℝ _ ℝ)).prod
      (((LinearMap.proj 1).comp (LinearMap.fst ℝ _ ℝ)).prod (LinearMap.snd ℝ _ ℝ))
  have hκL : ∀ p : (Fin 3 → ℝ) × ℝ, κL p = (p.1 0, p.1 1, p.2) := fun p => rfl
  set σI := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 with hσIdef
  have hσIpoly : IsPolyhedron σI :=
    (isHPolytope_stdSimplex (Fin 3)).isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hκpl : IsPiecewiseAffineOn κL σI :=
    (isPiecewiseAffineOn_of_affine κL.toAffineMap isOpen_univ).mono_of_isPolyhedron hσIpoly
      (subset_univ _)
  have hκinj : InjOn κL σI := by
    intro p hp p' hp' h
    rw [hκL, hκL] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2⟩ := h
    have h3 : p.1 2 = p'.1 2 := by linarith [hσsum _ hp.1, hσsum _ hp'.1]
    refine Prod.ext (funext fun i => ?_) h2
    fin_cases i
    · exact h0
    · exact h1
    · exact h3
  set M := κL '' σI with hMdef
  have hκ : IsPLHomeomorphOn κL σI M :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hσIpoly hκpl ⟨mapsTo_image _ _, hκinj,
      fun _ hz => hz⟩
  let ι : ℝ × ℝ × ℝ → (Fin 3 → ℝ) × ℝ := fun z => (![z.1, z.2.1, 1 - z.1 - z.2.1], z.2.2)
  set Mo : Set (ℝ × ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2.1 ∧ z.1 + z.2.1 < 1 ∧ -1 < z.2.2 ∧
    z.2.2 < 1} with hModef
  have hMo : IsOpen Mo := by
    have c1 : Continuous fun z : ℝ × ℝ × ℝ => z.1 := continuous_fst
    have c2 : Continuous fun z : ℝ × ℝ × ℝ => z.2.1 := continuous_fst.comp continuous_snd
    have c3 : Continuous fun z : ℝ × ℝ × ℝ => z.2.2 := continuous_snd.comp continuous_snd
    exact (isOpen_lt continuous_const c1).inter ((isOpen_lt continuous_const c2).inter
      ((isOpen_lt (c1.add c2) continuous_const).inter ((isOpen_lt continuous_const c3).inter
        (isOpen_lt c3 continuous_const))))
  have hισ : ∀ z ∈ Mo, ι z ∈ σI := by
    rintro z ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨fun i => ?_, ?_⟩, h4.le, h5.le⟩
    · fin_cases i <;> simp [ι] <;> linarith
    · simp [ι, Fin.sum_univ_three]
  have hκι : ∀ z, κL (ι z) = z := fun z => by simp [hκL, ι]
  have hMoM : Mo ⊆ M := fun z hz => ⟨ι z, hισ z hz, hκι z⟩
  have hκinv : ∀ z ∈ Mo, Function.invFunOn κL σI z = ι z := by
    intro z hz
    exact hκinj (hκ.bijOn.surjOn.mapsTo_invFunOn (hMoM hz)) (hισ z hz)
      ((hκ.bijOn.invOn_invFunOn.2 (hMoM hz)).trans (hκι z).symm)
  have hId : IsPLHomeomorphOn (id : ℝ → ℝ) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) :=
    isPLHomeomorphOn_id_of_isHPolytope isHPolytope_Icc
  set G : ℝ × ℝ × ℝ → E3 := ρ ∘ Prod.map f id ∘ Function.invFunOn κL σI with hGdef
  have hG : IsPLHomeomorphOn G M (ρa '' (DQ ×ˢ Icc 0 1) ∪ ρb '' (DQ ×ˢ Icc 0 1)) :=
    (hκ.symm.trans (hf.prodMap hId)).trans hρ
  have hGMo : ∀ z ∈ Mo, G z = ρ (f (ι z).1, z.2.2) := by
    intro z hz
    simp only [hGdef, Function.comp_apply, hκinv z hz]
    rfl
  have hιq₀ : ι (q₀ 0, q₀ 1, 0) = (q₀, 0) := by
    refine Prod.ext (funext fun i => ?_) rfl
    fin_cases i
    · rfl
    · rfl
    · simp only [ι]
      have := hσsum q₀ hq₀σ
      simp
      linarith
  have hz₀ : (q₀ 0, q₀ 1, (0 : ℝ)) ∈ Mo := by
    refine ⟨hq₀pos 0, hq₀pos 1, ?_, by norm_num, by norm_num⟩
    have := hσsum q₀ hq₀σ
    have := hq₀pos 2
    simp only
    linarith
  have hGz₀ : G (q₀ 0, q₀ 1, 0) = x := by
    rw [hGMo _ hz₀, hιq₀]
    simp only
    rw [hfq₀, hρ0 x hxDQ]
  set U := G '' Mo with hUdef
  have hGc : ContinuousOn G Mo := hG.isPiecewiseAffineOn.continuousOn.mono hMoM
  have hGi : InjOn G Mo := hG.bijOn.injOn.mono hMoM
  have hU : IsOpen U :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image_of_finrank_eq (by simp)
      hMo hGc hGi
  set φ := Function.invFunOn G M with hφdef
  have hφG : ∀ z ∈ Mo, φ (G z) = z := fun z hz => hG.bijOn.invOn_invFunOn.1 (hMoM hz)
  have hUsub : U ⊆ ρa '' (DQ ×ˢ Icc 0 1) ∪ ρb '' (DQ ×ˢ Icc 0 1) :=
    image_subset_iff.mpr fun z hz => hG.bijOn.mapsTo (hMoM hz)
  have hφU : φ '' U = Mo := by
    ext z
    constructor
    · rintro ⟨_, ⟨z', hz', rfl⟩, rfl⟩
      rw [hφG z' hz']
      exact hz'
    · intro hz
      exact ⟨G z, ⟨z, hz, rfl⟩, hφG z hz⟩
  have hφ : IsPLHomeomorphOn φ U Mo := by
    have h := hG.symm.restrict_isOpen hU hUsub (by rw [hφU]; exact hMo)
    rwa [hφU] at h
  have hUC : U ⊆ C := fun y hy => by
    rcases hUsub hy with h | h
    · rw [← hQab]
      exact Or.inl (hAQa h)
    · rw [← hQab]
      exact Or.inr (hBQb h)
  refine ⟨U, Mo, φ, hU, hMo, ⟨_, hz₀, hGz₀⟩, hUC.trans hCO, hφ, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [hφG z hz, ← hCW _ (hUC ⟨z, hz, rfl⟩), hGMo z hz]
  have hqσ : (ι z).1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := (hισ z hz).1
  have hfD : f (ι z).1 ∈ DQ := hf.bijOn.mapsTo hqσ
  rcases lt_trichotomy z.2.2 0 with hneg | hzero | hpos
  · have hmem := hρneg (show (f (ι z).1, z.2.2) ∈ DQ ×ˢ Ico (-1 : ℝ) 0 from
      ⟨hfD, hz.2.2.2.1.le, hneg⟩)
    have hyC : ρ (f (ι z).1, z.2.2) ∈ C := by
      rw [← hQab]
      exact Or.inl (hAQa hmem.1)
    exact ⟨fun h => (hmem.2 ⟨hyC, h⟩).elim, fun h => absurd h hneg.ne⟩
  · rw [hzero, hρ0 _ hfD]
    exact ⟨fun _ => rfl, fun _ => hfD.2⟩
  · have hmem := hρpos (show (f (ι z).1, z.2.2) ∈ DQ ×ˢ Ioc (0 : ℝ) 1 from
      ⟨hfD, hpos, hz.2.2.2.2.le⟩)
    have hyC : ρ (f (ι z).1, z.2.2) ∈ C := by
      rw [← hQab]
      exact Or.inr (hBQb hmem.1)
    exact ⟨fun h => (hmem.2 ⟨hyC, h⟩).elim, fun h => absurd h hpos.ne'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
