/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellFlatChart
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_isPLHomeomorphOn_box {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ q : (Fin 3 → ℝ) → ℝ × ℝ, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Icc a b ×ˢ Icc c d) ∧
      q '' stdSimplexBoundary 2 = frontier (Icc a b ×ˢ Icc c d) := by
  classical
  have hC : IsHPolytope (Icc a b ×ˢ Icc c d) := isHPolytope_Icc.prod isHPolytope_Icc
  have hint : (interior (Icc a b ×ˢ Icc c d)).Nonempty := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨((a + b) / 2, (c + d) / 2), ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 1 + 1 := by simp
  have hball := hC.isPLBall hint
  rw [hdim] at hball
  obtain ⟨q, hq⟩ := hball
  obtain ⟨K, hKfin, hK⟩ := hC.isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have hKb : IsPLBall (1 + 1) K.space := by
    rw [hK]
    exact ⟨q, hq⟩
  have hKm : IsCombinatorialManifoldWithBoundary (1 + 1) K :=
    hKb.isCombinatorialManifoldWithBoundary
  refine ⟨q, hq, ?_⟩
  rw [hq.image_stdSimplexBoundary_eq_boundaryComplex (m := 1) K hK,
    ← frontier_space_eq_boundaryComplex_space_of_finrank (n := 1) hdim K hKm, hK]

noncomputable def planeEmbed : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ × ℝ :=
  (LinearMap.fst ℝ ℝ ℝ).prod ((LinearMap.snd ℝ ℝ ℝ).prod 0)

theorem planeEmbed_apply (w : ℝ × ℝ) : planeEmbed w = (w.1, w.2, 0) := rfl

theorem planeEmbed_injective : Function.Injective planeEmbed := fun w w' h => by
  rw [planeEmbed_apply, planeEmbed_apply] at h
  obtain ⟨h1, h23⟩ := Prod.mk.inj h
  obtain ⟨h2, -⟩ := Prod.mk.inj h23
  exact Prod.ext h1 h2

theorem isPLHomeomorphOn_planeEmbed {H : Set (ℝ × ℝ)} (hH : IsPolyhedron H) :
    IsPLHomeomorphOn planeEmbed H (planeEmbed '' H) := by
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hH
  · exact (isPiecewiseAffineOn_of_affine planeEmbed.toAffineMap
      isOpen_univ).mono_of_isPolyhedron hH (subset_univ _)
  · exact planeEmbed_injective.injOn.bijOn_image

theorem notMem_frontier_box {a b c d : ℝ} {w : ℝ × ℝ} (h1 : w.1 ∈ Ioo a b)
    (h2 : w.2 ∈ Ioo c d) : w ∉ frontier (Icc a b ×ˢ Icc c d) := by
  intro hw
  have hint : w ∈ interior (Icc a b ×ˢ Icc c d) := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨h1, h2⟩
  exact hw.2 hint

theorem IsPseudoCell.exists_localDisk {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) {y : E3} (hy : y ∈ Eint) (hyP : y ≠ P) {O : Set E3}
    (hO : O ∈ 𝓝 y) :
    ∃ (D W : Set E3) (q : (Fin 3 → ℝ) → E3), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ Ec ∩ O ∧ IsOpen W ∧ y ∈ W ∧ W ∩ Ec ⊆ D ∧ Disjoint W (q '' stdSimplexBoundary 2) := by
  obtain ⟨U, V, φ, hU, hV, hyU, hUO, hφ, hE⟩ := hpc.exists_flatChart hy hyP hO
  have hφV : ∀ z ∈ U, φ z ∈ V := fun z hz => hφ.bijOn.mapsTo hz
  have hgφ : ∀ z ∈ U, Function.invFunOn φ U (φ z) = z := fun z hz =>
    hφ.bijOn.invOn_invFunOn.1 hz
  have hφg : ∀ p ∈ V, φ (Function.invFunOn φ U p) = p := fun p hp =>
    hφ.bijOn.invOn_invFunOn.2 hp
  have hgU : ∀ p ∈ V, Function.invFunOn φ U p ∈ U := fun p hp => hφ.symm.bijOn.mapsTo hp
  have hyE : y ∈ Ec := by
    rw [hpc.carrierEq]
    exact Or.inl hy
  have hc3 : (φ y).2.2 = 0 := (hE y hyU).mp hyE
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV (φ y) (hφV y hyU)
  have hε : 0 < δ / 2 := half_pos hδ
  obtain ⟨q₂, hq₂, hq₂b⟩ := exists_isPLHomeomorphOn_box
    (a := (φ y).1 - δ / 2) (b := (φ y).1 + δ / 2) (c := (φ y).2.1 - δ / 2)
    (d := (φ y).2.1 + δ / 2) (by linarith) (by linarith)
  set Q₂ : Set (ℝ × ℝ) := Icc ((φ y).1 - δ / 2) ((φ y).1 + δ / 2) ×ˢ
    Icc ((φ y).2.1 - δ / 2) ((φ y).2.1 + δ / 2) with hQ₂def
  have hQ₂poly : IsPolyhedron Q₂ := (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hjV : planeEmbed '' Q₂ ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    apply hδV
    rw [Metric.mem_ball, planeEmbed_apply]
    have h1 : |w.1 - (φ y).1| ≤ δ / 2 :=
      abs_sub_le_iff.mpr ⟨by linarith [hw.1.2], by linarith [hw.1.1]⟩
    have h2 : |w.2 - (φ y).2.1| ≤ δ / 2 :=
      abs_sub_le_iff.mpr ⟨by linarith [hw.2.2], by linarith [hw.2.1]⟩
    have hdist : dist ((w.1, w.2, 0) : ℝ × ℝ × ℝ) (φ y) ≤ δ / 2 := by
      rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, hc3, sub_zero,
        abs_zero]
      exact max_le h1 (max_le h2 hε.le)
    linarith
  have hjpoly : IsPolyhedron (planeEmbed '' Q₂) := hQ₂poly.image_of_isPiecewiseAffineOn
    (isPLHomeomorphOn_planeEmbed hQ₂poly).isPiecewiseAffineOn planeEmbed_injective.injOn
  have hg := hφ.symm.restrict hjpoly hjV
  have hq := (hq₂.trans (isPLHomeomorphOn_planeEmbed hQ₂poly)).trans hg
  set g := Function.invFunOn φ U with hgdef
  set W : Set E3 := U ∩ φ ⁻¹' (Ioo ((φ y).1 - δ / 2) ((φ y).1 + δ / 2) ×ˢ
    (Ioo ((φ y).2.1 - δ / 2) ((φ y).2.1 + δ / 2) ×ˢ univ)) with hWdef
  have hWopen : IsOpen W := hφ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU
    (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_univ))
  refine ⟨g '' (planeEmbed '' Q₂), W, g ∘ planeEmbed ∘ q₂, ?_, ?_, hWopen, ?_, ?_, ?_⟩
  · exact hq
  · rintro _ ⟨p, hp, rfl⟩
    have hpV := hjV hp
    refine ⟨?_, hUO (hgU p hpV)⟩
    apply (hE _ (hgU p hpV)).mpr
    rw [hφg p hpV]
    obtain ⟨w, -, rfl⟩ := hp
    rfl
  · exact ⟨hyU, ⟨by constructor <;> linarith, by constructor <;> linarith, trivial⟩⟩
  · rintro z ⟨⟨hzU, hz1, hz2, -⟩, hzE⟩
    have hz3 : (φ z).2.2 = 0 := (hE z hzU).mp hzE
    refine ⟨planeEmbed ((φ z).1, (φ z).2.1), ⟨((φ z).1, (φ z).2.1),
      ⟨Ioo_subset_Icc_self hz1, Ioo_subset_Icc_self hz2⟩, rfl⟩, ?_⟩
    have hφz : planeEmbed ((φ z).1, (φ z).2.1) = φ z := by
      rw [planeEmbed_apply]
      exact Prod.ext rfl (Prod.ext rfl hz3.symm)
    rw [hφz]
    exact hgφ z hzU
  · refine Set.disjoint_left.mpr ?_
    rintro z ⟨hzU, hz1, hz2, -⟩ ⟨x, hx, rfl⟩
    have hq₂x : q₂ x ∈ frontier Q₂ := by
      rw [← hq₂b]
      exact ⟨x, hx, rfl⟩
    have hpV : planeEmbed (q₂ x) ∈ V := hjV ⟨q₂ x, hq₂.bijOn.mapsTo hx.1, rfl⟩
    have hφz : φ ((g ∘ planeEmbed ∘ q₂) x) = planeEmbed (q₂ x) := hφg _ hpV
    rw [hφz, planeEmbed_apply] at hz1 hz2
    exact notMem_frontier_box hz1 hz2 hq₂x

theorem mem_Icc_signed_iff {s c v : ℝ} (hs : s = 1 ∨ s = -1) (hc : 0 < c) :
    v ∈ Icc (min 0 (s * c)) (max 0 (s * c)) ↔ 0 ≤ s * v ∧ s * v ≤ c := by
  rcases hs with rfl | rfl
  · rw [one_mul, one_mul, min_eq_left hc.le, max_eq_right hc.le]
    exact Iff.rfl
  · rw [neg_one_mul, neg_one_mul, min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith

theorem mem_Ioo_signed_iff {s c v : ℝ} (hs : s = 1 ∨ s = -1) (hc : 0 < c) :
    v ∈ Ioo (min 0 (s * c)) (max 0 (s * c)) ↔ 0 < s * v ∧ s * v < c := by
  rcases hs with rfl | rfl
  · rw [one_mul, one_mul, min_eq_left hc.le, max_eq_right hc.le]
    exact Iff.rfl
  · rw [neg_one_mul, neg_one_mul, min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith

theorem dist_zero_lt_of_abs_lt {p : ℝ × ℝ × ℝ} {c : ℝ} (h1 : |p.1| < c) (h2 : |p.2.1| < c)
    (h3 : |p.2.2| < c) : dist p 0 < c := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
  exact max_lt h1 (max_lt h2 h3)

theorem mem_frontier_halfBox_iff {s ε : ℝ} (hs : s = 1 ∨ s = -1) (hε : 0 < ε) {w : ℝ × ℝ}
    (h1 : w.1 ∈ Ioo (-ε) ε) (h2 : w.2 ∈ Ioo (-ε) ε) :
    w ∈ frontier (Icc (-ε) ε ×ˢ Icc (min 0 (s * ε)) (max 0 (s * ε))) ↔ w.2 = 0 := by
  rw [frontier_prod_eq, closure_Icc, closure_Icc, frontier_Icc (a := -ε) (b := ε) (by linarith),
    frontier_Icc (a := min 0 (s * ε)) (b := max 0 (s * ε)) min_le_max]
  have hne1 : w.1 ≠ -ε := ne_of_gt h1.1
  have hne2 : w.1 ≠ ε := ne_of_lt h1.2
  rcases hs with rfl | rfl
  · rw [one_mul, min_eq_left hε.le, max_eq_right hε.le]
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, hne1, hne2, or_self,
      false_and, or_false]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · exact absurd h (ne_of_lt h2.2)
    · intro h0
      exact ⟨⟨h1.1.le, h1.2.le⟩, Or.inl h0⟩
  · rw [neg_one_mul, min_eq_right (by linarith), max_eq_left (by linarith)]
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, hne1, hne2, or_self,
      false_and, or_false]
    constructor
    · rintro ⟨-, h | h⟩
      · exact absurd h (ne_of_gt h2.1)
      · exact h
    · intro h0
      exact ⟨⟨h1.1.le, h1.2.le⟩, Or.inr h0⟩

section Side

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_sideDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) {y : E3} (hy : y ∈ Ec e ∩ frontier XK.space)
    {Sd : Set E3} (hSd : Sd = XK.space ∨ Sd = (interior XK.space)ᶜ)
    {M : Set E3} (hMc : IsClosed M) (hMSd : M ⊆ Sd)
    (hMint : ∀ᶠ z in 𝓝 y, z ∈ M → z ∉ frontier XK.space → M ∈ 𝓝 z)
    (hMy : y ∈ closure (M \ frontier XK.space)) {O : Set E3} (hO : O ∈ 𝓝 y) :
    ∃ (Dk W : Set E3) (q : (Fin 3 → ℝ) → E3), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Dk ∧
      Dk ⊆ Ec e ∩ M ∩ O ∧ IsOpen W ∧ y ∈ W ∧ W ∩ Ec e ∩ M ⊆ Dk ∧
      ∀ z ∈ W ∩ Dk, (z ∈ q '' stdSimplexBoundary 2 ↔ z ∈ frontier XK.space) := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hpc := hd.pseudoCell e he hcard
  obtain ⟨U, φ, ρ, hU, hyU, hρ, hφ, hφy, hloc⟩ := h2.exists_sideChart hd he hcard hy
  have hintX : ∀ z, z ∈ interior XK.space ↔ z ∈ XK.space ∧ z ∉ frontier XK.space := by
    intro z
    rw [frontier, hXc.closure_eq]
    constructor
    · intro hz
      exact ⟨interior_subset hz, fun h' => h'.2 hz⟩
    · rintro ⟨hz, hzf⟩
      by_contra hn
      exact hzf ⟨hz, hn⟩
  obtain ⟨s, hs, hsd⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ z ∈ U, (z ∈ Sd ↔ 0 ≤ s * (φ z).2.1) := by
    rcases hSd with rfl | rfl
    · exact ⟨1, Or.inl rfl, fun z hz => by rw [one_mul]; exact (hloc z hz).2.2⟩
    · refine ⟨-1, Or.inr rfl, fun z hz => ?_⟩
      rw [mem_compl_iff, hintX, (hloc z hz).2.2, (hloc z hz).2.1]
      constructor
      · intro h'
        by_contra hc
        have hp : 0 < (φ z).2.1 := by linarith [not_le.mp hc]
        exact h' ⟨hp.le, hp.ne'⟩
      · rintro h' ⟨hp0, hne⟩
        exact hne (by linarith)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hyint : y ∈ interior N' := h2.subsetInterior (hXc.frontier_subset hy.2)
  obtain ⟨VM, hVM, hVMo, hyVM⟩ := mem_nhds_iff.mp hMint
  set O'' : Set E3 := interior O ∩ interior N' ∩ VM ∩ U with hO''def
  have hO''o : IsOpen O'' := ((isOpen_interior.inter isOpen_interior).inter hVMo).inter hU
  have hyO'' : y ∈ O'' := ⟨⟨⟨mem_interior_iff_mem_nhds.mpr hO, hyint⟩, hyVM⟩, hyU⟩
  set g := Function.invFunOn φ U with hgdef
  have hg : IsPLHomeomorphOn g (Metric.ball 0 ρ) U := hφ.symm
  have hφg : ∀ p ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, φ (g p) = p := fun p hp =>
    hφ.bijOn.invOn_invFunOn.2 hp
  have hgφ : ∀ z ∈ U, g (φ z) = z := fun z hz => hφ.bijOn.invOn_invFunOn.1 hz
  have hgU : ∀ p ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, g p ∈ U := fun p hp => hg.bijOn.mapsTo hp
  have hg0 : g 0 = y := by
    rw [← hφy]
    exact hgφ y hyU
  have hgc : ContinuousOn g (Metric.ball 0 ρ) := hg.isPiecewiseAffineOn.continuousOn
  have hgca : ContinuousAt g 0 := hgc.continuousAt (Metric.ball_mem_nhds 0 hρ)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp
    (hgca.preimage_mem_nhds (hO''o.mem_nhds (hg0.symm ▸ hyO'')))
  set ε := min η ρ / 4 with hεdef
  have hε : 0 < ε := by positivity
  have hεη : 2 * ε < η := by
    have := min_le_left η ρ
    linarith
  have hερ : 2 * ε < ρ := by
    have := min_le_right η ρ
    linarith
  have hball : ∀ p : ℝ × ℝ × ℝ, |p.1| ≤ 3 / 2 * ε → |p.2.1| ≤ 3 / 2 * ε →
      |p.2.2| ≤ 3 / 2 * ε → p ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ ∧ g p ∈ O'' := by
    intro p h1 h2' h3
    have hd2 : dist p 0 < 2 * ε := dist_zero_lt_of_abs_lt (by linarith) (by linarith)
      (by linarith)
    exact ⟨Metric.mem_ball.mpr (by linarith), hηsub (Metric.mem_ball.mpr (by linarith))⟩
  have habs : ∀ b v : ℝ, 0 ≤ s * v → s * v ≤ b → |v| ≤ b := by
    intro b v h1 h2'
    rcases hs with rfl | rfl
    · rw [one_mul] at h1 h2'
      exact abs_le.mpr ⟨by linarith, h2'⟩
    · rw [neg_one_mul] at h1 h2'
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hslt : ∀ b v : ℝ, v ∈ Ioo (-b) b → s * v < b := by
    intro b v hv
    rcases hs with rfl | rfl
    · rw [one_mul]
      exact hv.2
    · rw [neg_one_mul]
      linarith [hv.1]
  have hmm : ∀ b : ℝ, 0 < b → min 0 (s * b) < max 0 (s * b) := by
    intro b hb
    rcases hs with rfl | rfl
    · rw [one_mul, min_eq_left hb.le, max_eq_right hb.le]
      exact hb
    · rw [neg_one_mul, min_eq_right (by linarith), max_eq_left (by linarith)]
      linarith
  obtain ⟨q₂, hq₂, hq₂b⟩ := exists_isPLHomeomorphOn_box (a := -ε) (b := ε) (by linarith)
    (hmm ε hε)
  set H₂ : Set (ℝ × ℝ) := Icc (-ε) ε ×ˢ Icc (min 0 (s * ε)) (max 0 (s * ε)) with hH₂def
  have hH₂poly : IsPolyhedron H₂ := (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hH₂v : ∀ w ∈ H₂, |w.1| ≤ ε ∧ 0 ≤ s * w.2 ∧ s * w.2 ≤ ε := fun w hw =>
    ⟨abs_le.mpr ⟨hw.1.1, hw.1.2⟩, (mem_Icc_signed_iff hs hε).mp hw.2⟩
  have hjball : ∀ w ∈ H₂,
      planeEmbed w ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ ∧ g (planeEmbed w) ∈ O'' := by
    intro w hw
    obtain ⟨h1, h2', h3⟩ := hH₂v w hw
    have hw2 := habs ε w.2 h2' h3
    rw [planeEmbed_apply]
    exact hball _ (by linarith) (by linarith) (by rw [abs_zero]; positivity)
  have hjsub : planeEmbed '' H₂ ⊆ Metric.ball (0 : ℝ × ℝ × ℝ) ρ := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hjball w hw).1
  have hjpoly : IsPolyhedron (planeEmbed '' H₂) := hH₂poly.image_of_isPiecewiseAffineOn
    (isPLHomeomorphOn_planeEmbed hH₂poly).isPiecewiseAffineOn planeEmbed_injective.injOn
  have hq := (hq₂.trans (isPLHomeomorphOn_planeEmbed hH₂poly)).trans (hg.restrict hjpoly hjsub)
  set c : ℝ := 3 / 2 * ε with hcdef
  have hc : 0 < c := by positivity
  set B : Set (ℝ × ℝ × ℝ) :=
    Ioo (-c) c ×ˢ (Ioo (min 0 (s * c)) (max 0 (s * c)) ×ˢ Ioo (-c) c) with hBdef
  have hBconv : Convex ℝ B := (convex_Ioo _ _).prod ((convex_Ioo _ _).prod (convex_Ioo _ _))
  have hBcl : closure B = Icc (-c) c ×ˢ (Icc (min 0 (s * c)) (max 0 (s * c)) ×ˢ Icc (-c) c) := by
    rw [closure_prod_eq, closure_prod_eq, closure_Ioo (neg_lt_self hc).ne,
      closure_Ioo (hmm c hc).ne]
  have hBclball : ∀ p ∈ closure B,
      p ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ ∧ g p ∈ O'' := by
    intro p hp
    rw [hBcl] at hp
    obtain ⟨h1, h2', h3⟩ := hp
    have hv := (mem_Icc_signed_iff hs hc).mp h2'
    exact hball p (abs_le.mpr ⟨h1.1, h1.2⟩) (habs c _ hv.1 hv.2) (abs_le.mpr ⟨h3.1, h3.2⟩)
  have hBball : B ⊆ Metric.ball (0 : ℝ × ℝ × ℝ) ρ := fun p hp =>
    (hBclball p (subset_closure hp)).1
  have hZpre : IsPreconnected (g '' B) := hBconv.isPreconnected.image g (hgc.mono hBball)
  have hZfr : ∀ z ∈ g '' B, z ∉ frontier XK.space ∧ z ∈ VM := by
    rintro _ ⟨p, hp, rfl⟩
    have hpb := hBball hp
    refine ⟨fun hfr => ?_, (hBclball p (subset_closure hp)).2.1.2⟩
    have h0 := ((hloc (g p) (hgU p hpb)).2.1).mp hfr
    rw [hφg p hpb] at h0
    have hpos := ((mem_Ioo_signed_iff hs hc).mp hp.2.1).1
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hcover : g '' B ⊆ interior M ∪ Mᶜ := by
    intro z hz
    by_cases hzM : z ∈ M
    · exact Or.inl (mem_interior_iff_mem_nhds.mpr (hVM (hZfr z hz).2 hzM (hZfr z hz).1))
    · exact Or.inr hzM
  have hne : (g '' B ∩ interior M).Nonempty := by
    set G : Set E3 := U ∩ φ ⁻¹' (Ioo (-c) c ×ˢ (Ioo (-c) c ×ˢ Ioo (-c) c)) with hGdef
    have hGo : IsOpen G := hφ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU
      (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo))
    have hyG : y ∈ G := by
      refine ⟨hyU, ?_⟩
      rw [mem_preimage, hφy]
      exact ⟨⟨neg_lt_zero.mpr hc, hc⟩, ⟨neg_lt_zero.mpr hc, hc⟩, ⟨neg_lt_zero.mpr hc, hc⟩⟩
    obtain ⟨z₀, hz₀G, hz₀M, hz₀fr⟩ := mem_closure_iff_nhds.mp hMy G (hGo.mem_nhds hyG)
    have hsign := (hsd z₀ hz₀G.1).mp (hMSd hz₀M)
    have hp2 : (φ z₀).2.1 ≠ 0 := fun h0 => hz₀fr (((hloc z₀ hz₀G.1).2.1).mpr h0)
    have hpos : 0 < s * (φ z₀).2.1 := lt_of_le_of_ne hsign (Ne.symm (mul_ne_zero hs0 hp2))
    have hB : φ z₀ ∈ B := ⟨hz₀G.2.1, (mem_Ioo_signed_iff hs hc).mpr
      ⟨hpos, hslt c _ hz₀G.2.2.1⟩, hz₀G.2.2.2⟩
    have hz₀Z : z₀ ∈ g '' B := ⟨φ z₀, hB, hgφ z₀ hz₀G.1⟩
    exact ⟨z₀, hz₀Z, mem_interior_iff_mem_nhds.mpr (hVM (hZfr _ hz₀Z).2 hz₀M hz₀fr)⟩
  have hZM : g '' B ⊆ interior M := hZpre.subset_left_of_subset_union isOpen_interior
    hMc.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hcover hne
  have hHcl : planeEmbed '' H₂ ⊆ closure B := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hBcl, planeEmbed_apply]
    obtain ⟨h1, h2', h3⟩ := hH₂v w hw
    refine ⟨⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩,
      (mem_Icc_signed_iff hs hc).mpr ⟨h2', by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hDM : g '' (planeEmbed '' H₂) ⊆ M := by
    have hcl : g '' closure B ⊆ closure (g '' B) :=
      (hgc.mono fun p hp => (hBclball p hp).1).image_closure
    rintro _ ⟨p, hp, rfl⟩
    exact closure_minimal (hZM.trans interior_subset) hMc (hcl ⟨p, hHcl hp, rfl⟩)
  set W : Set E3 := U ∩ φ ⁻¹' (Ioo (-ε) ε ×ˢ (Ioo (-ε) ε ×ˢ Ioo (-ε) ε)) with hWdef
  have hWo : IsOpen W := hφ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU
    (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo))
  have hyW : y ∈ W := by
    refine ⟨hyU, ?_⟩
    rw [mem_preimage, hφy]
    exact ⟨⟨neg_lt_zero.mpr hε, hε⟩, ⟨neg_lt_zero.mpr hε, hε⟩, ⟨neg_lt_zero.mpr hε, hε⟩⟩
  have hWO : ∀ z ∈ W, z ∈ O'' := by
    rintro z ⟨hzU, h1, h2', h3⟩
    have h := (hball (φ z) (abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩)
      (abs_le.mpr ⟨by linarith [h2'.1], by linarith [h2'.2]⟩)
      (abs_le.mpr ⟨by linarith [h3.1], by linarith [h3.2]⟩)).2
    rwa [hgφ z hzU] at h
  refine ⟨g '' (planeEmbed '' H₂), W, g ∘ planeEmbed ∘ q₂, hq, ?_, hWo, hyW, ?_, ?_⟩
  · intro z hz
    refine ⟨⟨?_, hDM hz⟩, ?_⟩
    · obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
      have hpb := (hjball w hw).1
      have hEint : g (planeEmbed w) ∈ Eint e := ((hloc _ (hgU _ hpb)).1).mpr (by
        rw [hφg _ hpb, planeEmbed_apply])
      rw [hpc.carrierEq]
      exact Or.inl hEint
    · obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
      exact interior_subset (hjball w hw).2.1.1.1
  · rintro z ⟨⟨hzW, hzE⟩, hzM⟩
    have hzO := hWO z hzW
    obtain ⟨hzU, h1, h2', h3⟩ := hzW
    have hzEint : z ∈ Eint e := by
      rw [hpc.carrierEq] at hzE
      rcases hzE with h' | h'
      · exact h'
      · exfalso
        have hbd : z ∈ Ec e ∩ frontier N' := by
          rw [hd.rimFrontier e he hcard]
          exact h'
        exact hbd.2.2 hzO.1.1.2
    have hz3 : (φ z).2.2 = 0 := ((hloc z hzU).1).mp hzEint
    have hsg := (hsd z hzU).mp (hMSd hzM)
    refine ⟨planeEmbed ((φ z).1, (φ z).2.1), ⟨((φ z).1, (φ z).2.1),
      ⟨⟨h1.1.le, h1.2.le⟩, (mem_Icc_signed_iff hs hε).mpr ⟨hsg, (hslt ε _ h2').le⟩⟩, rfl⟩, ?_⟩
    rw [show planeEmbed ((φ z).1, (φ z).2.1) = φ z from Prod.ext rfl (Prod.ext rfl hz3.symm)]
    exact hgφ z hzU
  · rintro z ⟨hzW, ⟨_, ⟨w, hw, rfl⟩, rfl⟩⟩
    obtain ⟨hzU, h1, h2', -⟩ := hzW
    have hpb := (hjball w hw).1
    have hφz : φ (g (planeEmbed w)) = planeEmbed w := hφg _ hpb
    rw [hφz, planeEmbed_apply] at h1 h2'
    have himg : (g ∘ planeEmbed ∘ q₂) '' stdSimplexBoundary 2 =
        g '' (planeEmbed '' frontier H₂) := by
      rw [← hq₂b, image_image, image_image]
      rfl
    have hfrH : frontier H₂ ⊆ H₂ :=
      (isHPolytope_Icc.prod isHPolytope_Icc).isCompact.isClosed.frontier_subset
    rw [himg, ((hloc _ hzU).2.1), hφz, planeEmbed_apply]
    constructor
    · rintro ⟨_, ⟨w', hw', rfl⟩, heq⟩
      have hpb' := (hjball w' (hfrH hw')).1
      have hww : planeEmbed w' = planeEmbed w := hg.bijOn.injOn hpb' hpb heq
      rw [planeEmbed_injective hww] at hw'
      exact (mem_frontier_halfBox_iff hs hε h1 h2').mp hw'
    · intro h0
      exact ⟨planeEmbed w, ⟨w, (mem_frontier_halfBox_iff hs hε h1 h2').mpr h0, rfl⟩, rfl⟩

end Side

end DifferentialGeometry.Topology.PiecewiseLinear
