/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Mathlib.Analysis.Convex.GaugeRescale

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section PlanarModel

variable {n : ℕ}

theorem dist_apply_le_dist (x y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    dist (x i) (y i) ≤ dist x y := by
  rw [EuclideanSpace.dist_eq]
  have hle : dist (x i) (y i) ^ 2 ≤ ∑ j, dist (x j) (y j) ^ 2 :=
    Finset.single_le_sum (f := fun j => dist (x j) (y j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc dist (x i) (y i) = Real.sqrt (dist (x i) (y i) ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ ≤ _ := Real.sqrt_le_sqrt hle

theorem continuous_euclideanApply (i : Fin n) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => x i :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    simpa using dist_apply_le_dist x y i).continuous

noncomputable def planarPoint (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1)

@[simp] theorem planarPoint_apply_zero (x : EuclideanSpace ℝ (Fin 2)) :
    planarPoint x 0 = x 0 := by
  simp [planarPoint, PiLp.add_apply]

@[simp] theorem planarPoint_apply_one (x : EuclideanSpace ℝ (Fin 2)) :
    planarPoint x 1 = x 1 := by
  simp [planarPoint, PiLp.add_apply]

@[simp] theorem planarPoint_apply_two (x : EuclideanSpace ℝ (Fin 2)) :
    planarPoint x 2 = 0 := by
  simp [planarPoint, PiLp.add_apply]

theorem planarPoint_smul_add_smul (s t : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    planarPoint (s • x + t • y) = s • planarPoint x + t • planarPoint y := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;>
    simp [PiLp.add_apply, PiLp.smul_apply, planarPoint_apply_zero, planarPoint_apply_one,
      planarPoint_apply_two]

theorem isometry_planarPoint : Isometry planarPoint := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp

theorem planarPoint_injective : Function.Injective planarPoint :=
  isometry_planarPoint.injective

theorem continuous_planarPoint : Continuous planarPoint :=
  isometry_planarPoint.continuous

theorem planarPoint_mem_iff (p : EuclideanSpace ℝ (Fin 3)) :
    p ∈ Set.range planarPoint ↔ p 2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact planarPoint_apply_two x
  · intro hp
    refine ⟨EuclideanSpace.single 0 (p 0) + EuclideanSpace.single 1 (p 1), PiLp.ext fun i => ?_⟩
    fin_cases i <;> simp [PiLp.add_apply, hp]

def rectTwo (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x 0 ∈ Icc a b ∧ x 1 ∈ Icc c d}

def openRectTwo (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x 0 ∈ Ioo a b ∧ x 1 ∈ Ioo c d}

variable {a b c d a' b' c' d' : ℝ}

theorem mem_rectTwo {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ rectTwo a b c d ↔ x 0 ∈ Icc a b ∧ x 1 ∈ Icc c d := Iff.rfl

theorem mem_openRectTwo {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ openRectTwo a b c d ↔ x 0 ∈ Ioo a b ∧ x 1 ∈ Ioo c d := Iff.rfl

theorem convex_rectTwo (a b c d : ℝ) : Convex ℝ (rectTwo a b c d) := by
  intro x hx y hy s t hs ht hst
  have key : ∀ lo hi u v : ℝ, lo ≤ u → u ≤ hi → lo ≤ v → v ≤ hi →
      lo ≤ s * u + t * v ∧ s * u + t * v ≤ hi := by
    intro lo hi u v h1 h2 h3 h4
    have e1 : s * lo ≤ s * u := mul_le_mul_of_nonneg_left h1 hs
    have e2 : t * lo ≤ t * v := mul_le_mul_of_nonneg_left h3 ht
    have e3 : s * lo + t * lo = lo := by rw [← add_mul, hst, one_mul]
    have f1 : s * u ≤ s * hi := mul_le_mul_of_nonneg_left h2 hs
    have f2 : t * v ≤ t * hi := mul_le_mul_of_nonneg_left h4 ht
    have f3 : s * hi + t * hi = hi := by rw [← add_mul, hst, one_mul]
    exact ⟨by linarith, by linarith⟩
  have h0 : (s • x + t • y) 0 = s * x 0 + t * y 0 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  have h1 : (s • x + t • y) 1 = s * x 1 + t * y 1 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  obtain ⟨⟨hx0, hx0'⟩, hx1, hx1'⟩ := hx
  obtain ⟨⟨hy0, hy0'⟩, hy1, hy1'⟩ := hy
  obtain ⟨k0, k0'⟩ := key a b (x 0) (y 0) hx0 hx0' hy0 hy0'
  obtain ⟨k1, k1'⟩ := key c d (x 1) (y 1) hx1 hx1' hy1 hy1'
  exact ⟨⟨by rw [h0]; exact k0, by rw [h0]; exact k0'⟩,
    ⟨by rw [h1]; exact k1, by rw [h1]; exact k1'⟩⟩

theorem isClosed_rectTwo (a b c d : ℝ) : IsClosed (rectTwo a b c d) := by
  have h0 : IsClosed ((fun x : EuclideanSpace ℝ (Fin 2) => x 0) ⁻¹' Icc a b) :=
    isClosed_Icc.preimage (continuous_euclideanApply 0)
  have h1 : IsClosed ((fun x : EuclideanSpace ℝ (Fin 2) => x 1) ⁻¹' Icc c d) :=
    isClosed_Icc.preimage (continuous_euclideanApply 1)
  exact h0.inter h1

theorem isOpen_openRectTwo (a b c d : ℝ) : IsOpen (openRectTwo a b c d) := by
  have h0 : IsOpen ((fun x : EuclideanSpace ℝ (Fin 2) => x 0) ⁻¹' Ioo a b) :=
    isOpen_Ioo.preimage (continuous_euclideanApply 0)
  have h1 : IsOpen ((fun x : EuclideanSpace ℝ (Fin 2) => x 1) ⁻¹' Ioo c d) :=
    isOpen_Ioo.preimage (continuous_euclideanApply 1)
  exact h0.inter h1

theorem openRectTwo_subset_interior_rectTwo (a b c d : ℝ) :
    openRectTwo a b c d ⊆ interior (rectTwo a b c d) :=
  interior_maximal (fun _ hx => ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩)
    (isOpen_openRectTwo a b c d)

theorem single_mem_interior_rectTwo {r : ℝ} (h1 : a < r) (h2 : r < b) (h3 : c < 0)
    (h4 : 0 < d) : EuclideanSpace.single (0 : Fin 2) r ∈ interior (rectTwo a b c d) := by
  refine openRectTwo_subset_interior_rectTwo a b c d ⟨?_, ?_⟩
  · change (EuclideanSpace.single (0 : Fin 2) r) 0 ∈ Ioo a b
    simpa using ⟨h1, h2⟩
  · change (EuclideanSpace.single (0 : Fin 2) r) 1 ∈ Ioo c d
    simpa using ⟨h3, h4⟩

theorem norm_le_of_abs_le {x : EuclideanSpace ℝ (Fin 2)} {M : ℝ} (h0 : |x 0| ≤ M)
    (h1 : |x 1| ≤ M) : ‖x‖ ≤ 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans h0
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hsq : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 ≤ (2 * M) ^ 2 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [abs_nonneg (x 0), abs_nonneg (x 1)]
  calc Real.sqrt (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2) ≤ Real.sqrt ((2 * M) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * M := Real.sqrt_sq (by linarith)

theorem isBounded_rectTwo (a b c d : ℝ) : Bornology.IsBounded (rectTwo a b c d) := by
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2)))
    (r := 2 * (|a| + |b| + |c| + |d|))).subset fun x hx => ?_
  obtain ⟨⟨hx0, hx0'⟩, hx1, hx1'⟩ := hx
  have h0 : |x 0| ≤ |a| + |b| + |c| + |d| := by
    rcases abs_cases (x 0) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      [nlinarith [le_abs_self b, abs_nonneg a, abs_nonneg c, abs_nonneg d];
       nlinarith [neg_abs_le a, abs_nonneg b, abs_nonneg c, abs_nonneg d]]
  have h1 : |x 1| ≤ |a| + |b| + |c| + |d| := by
    rcases abs_cases (x 1) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      [nlinarith [le_abs_self d, abs_nonneg a, abs_nonneg b, abs_nonneg c];
       nlinarith [neg_abs_le c, abs_nonneg a, abs_nonneg b, abs_nonneg d]]
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_le_of_abs_le h0 h1

theorem rectTwo_inter (a b c d a' b' c' d' : ℝ) :
    rectTwo a b c d ∩ rectTwo a' b' c' d' =
      rectTwo (max a a') (min b b') (max c c') (min d d') := by
  ext x
  simp only [mem_inter_iff, mem_rectTwo, mem_Icc, max_le_iff, le_min_iff]
  tauto

theorem rectTwo_eq_empty (hab : b < a) (c d : ℝ) : rectTwo a b c d = ∅ := by
  ext x
  simp only [mem_rectTwo, mem_Icc, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨h1, h2⟩
  linarith

end PlanarModel

section TopologicalCells

def IsTopologicalCellWithInterior (n : ℕ) {X : Type*} [TopologicalSpace X] (C I : Set X) :
    Prop :=
  ∃ φ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ C,
    I = Subtype.val '' (φ '' {q | ‖(q : EuclideanSpace ℝ (Fin n))‖ < 1})

theorem IsTopologicalCellWithInterior.isTopologicalCell {n : ℕ} {X : Type*} [TopologicalSpace X]
    {C I : Set X} (h : IsTopologicalCellWithInterior n C I) : IsTopologicalCell n C :=
  ⟨h.choose.symm⟩

variable {K : Set (EuclideanSpace ℝ (Fin 2))}

theorem isTopologicalCellWithInterior_planarImage (hconv : Convex ℝ K) (hcl : IsClosed K)
    (hb : Bornology.IsBounded K) (hne : (interior K).Nonempty) :
    IsTopologicalCellWithInterior 2 (planarPoint '' K) (planarPoint '' interior K) := by
  obtain ⟨e, hint, hclos, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hb
  rw [hcl.closure_eq] at hclos
  have hKe : e.symm '' Metric.closedBall 0 1 = K := by
    rw [← hclos]; exact e.toEquiv.symm_image_image K
  have hIe : e.symm '' Metric.ball 0 1 = interior K := by
    rw [← hint]; exact e.toEquiv.symm_image_image (interior K)
  set φ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ (planarPoint '' K) :=
    ((e.symm.image (Metric.closedBall 0 1)).trans (Homeomorph.setCongr hKe)).trans
      (isometry_planarPoint.isEmbedding.homeomorphImage K) with hφ
  have hval : ∀ q : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      (φ q : EuclideanSpace ℝ (Fin 3)) = planarPoint (e.symm (q : EuclideanSpace ℝ (Fin 2))) :=
    fun _ => rfl
  refine ⟨φ, ?_⟩
  rw [← hIe]
  ext p
  simp only [mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hznorm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hzmem : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hznorm.le
    exact ⟨φ ⟨z, hzmem⟩, ⟨⟨z, hzmem⟩, hznorm, rfl⟩, (hval ⟨z, hzmem⟩).symm⟩
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨e.symm (r : EuclideanSpace ℝ (Fin 2)),
      ⟨(r : EuclideanSpace ℝ (Fin 2)), ?_, rfl⟩, (hval r).symm⟩
    simpa [Metric.mem_ball, dist_zero_right] using hr

theorem isTopologicalCell_planarImage (hconv : Convex ℝ K) (hcl : IsClosed K)
    (hb : Bornology.IsBounded K) (hne : (interior K).Nonempty) :
    IsTopologicalCell 2 (planarPoint '' K) :=
  (isTopologicalCellWithInterior_planarImage hconv hcl hb hne).isTopologicalCell

theorem nonempty_homeomorph_planarImage_interior (hconv : Convex ℝ K)
    (hb : Bornology.IsBounded K) (hne : (interior K).Nonempty) :
    Nonempty ((planarPoint '' interior K) ≃ₜ
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  obtain ⟨e, hint, -, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hb
  exact ⟨((isometry_planarPoint.isEmbedding.homeomorphImage (interior K)).symm.trans
    (e.image (interior K))).trans (Homeomorph.setCongr hint)⟩

theorem nonempty_homeomorph_planarImage_frontier (hconv : Convex ℝ K)
    (hb : Bornology.IsBounded K) (hne : (interior K).Nonempty) :
    Nonempty ((planarPoint '' frontier K) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  obtain ⟨e, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hb
  exact ⟨((isometry_planarPoint.isEmbedding.homeomorphImage (frontier K)).symm.trans
    (e.image (frontier K))).trans (Homeomorph.setCongr hfr)⟩

end TopologicalCells

section Configuration

def revolutionOf (X : Set (EuclideanSpace ℝ (Fin 3))) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ∃ q ∈ X, q 2 = 0 ∧ 0 ≤ q 0 ∧ q 1 = p 1 ∧ q 0 ^ 2 = p 0 ^ 2 + p 2 ^ 2}

theorem revolutionOf_mono {X Y : Set (EuclideanSpace ℝ (Fin 3))} (h : X ⊆ Y) :
    revolutionOf X ⊆ revolutionOf Y := by
  rintro p ⟨q, hq, hrest⟩
  exact ⟨q, h hq, hrest⟩

structure IsPlanarCellChain (P : Fin 4 → EuclideanSpace ℝ (Fin 3))
    (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  halfPlane : ∀ j, ∀ p ∈ D j, p 2 = 0 ∧ 0 < p 0
  cell : ∀ j, IsTopologicalCellWithInterior 2 (D j) (Dint j)
  interiorSubset : ∀ j, Dint j ⊆ D j
  segmentSubset : ∀ j : Fin 3, segment ℝ (P j.castSucc) (P j.succ) ⊆ Dint j
  consecutiveNe : ∀ j : Fin 3, P j.castSucc ≠ P j.succ
  overlap : ∀ j : Fin 2, IsTopologicalCell 2 (D j.castSucc ∩ D j.succ)
  apart : D 0 ∩ D 2 = ∅

structure IsRevolvedTorusChain (P : Fin 4 → EuclideanSpace ℝ (Fin 3))
    (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  chain : IsPlanarCellChain P D Dint
  circleEq : ∀ j, J j = revolutionOf {P j}
  annulusEq : ∀ j : Fin 3, A j = revolutionOf (segment ℝ (P j.castSucc) (P j.succ))
  solidEq : ∀ j, S j = revolutionOf (D j)
  isSolidTorus : ∀ j, IsTopologicalSolidTorus (S j)
  boundaryEq : ∀ j, T j = frontier (S j)
  annulusSubset : ∀ j, A j ⊆ interior (S j)

structure IsCanonicalConfiguration (P : Fin 4 → EuclideanSpace ℝ (Fin 3))
    (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) (N : Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  base : IsRevolvedTorusChain P D Dint J A S T
  unionEq : N = ⋃ j, S j
  isEmbedding : Topology.IsEmbedding (N.domRestrict h)
  isPolyhedralSolidTorus : ∀ j, IsCombinatorialSolidTorus (S'' j)
  boundaryEq : ∀ j, T'' j = frontier (S'' j)
  annulusImageSubset : ∀ j, h '' A j ⊆ interior (S'' j)
  innerSubset : ∀ j, S'' j ⊆ interior (h '' S j)
  crossing : ∀ j : Fin 2, ∀ x ∈ T'' j.castSucc ∩ T'' j.succ,
    HasPLCrossingAt (T'' j.castSucc) (T'' j.succ) x
  polygons : ∀ j : Fin 2, ∃ (ι : Type) (_ : Finite ι) (G : ι → Set (EuclideanSpace ℝ (Fin 3))),
    (∀ i, IsPLSphere 1 (G i)) ∧ (Pairwise fun i i' => Disjoint (G i) (G i')) ∧
      T'' j.castSucc ∩ T'' j.succ = ⋃ i, G i

theorem IsRevolvedTorusChain.circle_subset_annulus {P : Fin 4 → EuclideanSpace ℝ (Fin 3)}
    {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3))}
    {A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsRevolvedTorusChain P D Dint J A S T) (j : Fin 3) (k : Fin 4)
    (hk : k = j.castSucc ∨ k = j.succ) : J k ⊆ A j := by
  rw [hc.circleEq, hc.annulusEq]
  refine revolutionOf_mono ?_
  rcases hk with rfl | rfl
  · simpa using left_mem_segment ℝ (P j.castSucc) (P j.succ)
  · simpa using right_mem_segment ℝ (P j.castSucc) (P j.succ)

theorem IsCanonicalConfiguration.image_circle_subset
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)} {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3))}
    {A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))} {N : Set (EuclideanSpace ℝ (Fin 3))}
    {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsCanonicalConfiguration P D Dint J A S T N h S'' T'') (j : Fin 3) (k : Fin 4)
    (hk : k = j.castSucc ∨ k = j.succ) : h '' J k ⊆ S'' j :=
  ((image_mono (hc.base.circle_subset_annulus j k hk)).trans
    (hc.annulusImageSubset j)).trans interior_subset

end Configuration

section Statements

def Moise311 : Prop :=
  ∀ (P : Fin 4 → EuclideanSpace ℝ (Fin 3)) (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) (N : Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
    IsRevolvedTorusChain P D Dint J A S T → N = ⋃ j, S j →
    Topology.IsEmbedding (N.domRestrict h) →
    ∃ S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)),
      IsCanonicalConfiguration P D Dint J A S T N h S'' T''

def Moise312 : Prop :=
  ∀ (P : Fin 4 → EuclideanSpace ℝ (Fin 3)) (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) (N : Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))),
    IsCanonicalConfiguration P D Dint J A S T N h S'' T'' →
    ∀ (j : Fin 3) (k : Fin 4), k = j.castSucc ∨ k = j.succ →
    ∀ hsub : h '' J k ⊆ S'' j, ∀ x : (h '' J k),
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(h '' J k, S'' j)) x)

def Moise313 : Prop :=
  ∀ (P : Fin 4 → EuclideanSpace ℝ (Fin 3)) (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) (N : Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))),
    IsCanonicalConfiguration P D Dint J A S T N h S'' T'' → S'' 0 ∩ S'' 2 = ∅

def Moise314 : Prop :=
  ∀ (P : Fin 4 → EuclideanSpace ℝ (Fin 3)) (D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))) (N : Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))),
    IsCanonicalConfiguration P D Dint J A S T N h S'' T'' →
    ∀ (j : Fin 2) (G : Set (EuclideanSpace ℝ (Fin 3))), IsPLSphere 1 G →
    G ⊆ T'' j.castSucc ∩ T'' j.succ →
    (∀ k : Fin 3, (k = j.castSucc ∨ k = j.succ) → ∀ hsub : G ⊆ S'' k, ∀ x : G,
        Function.Surjective (FundamentalGroup.map
          (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' k)) x)) ∨
      ∀ k : Fin 3, (k = j.castSucc ∨ k = j.succ) →
        ∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
          IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T'' k ∧
            G = r '' stdSimplexBoundary 2

end Statements

section Inhabitant

noncomputable def standardChainPoint (j : Fin 4) : EuclideanSpace ℝ (Fin 3) :=
  planarPoint (EuclideanSpace.single 0 (((j : ℕ) : ℝ) + 1))

noncomputable def standardChainRect (j : Fin 3) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectTwo (((j : ℕ) : ℝ) + 3 / 5) (((j : ℕ) : ℝ) + 12 / 5) (-1) 1

noncomputable def standardChainCell (j : Fin 3) : Set (EuclideanSpace ℝ (Fin 3)) :=
  planarPoint '' standardChainRect j

noncomputable def standardChainCellInterior (j : Fin 3) : Set (EuclideanSpace ℝ (Fin 3)) :=
  planarPoint '' interior (standardChainRect j)

theorem standardChainPoint_apply_zero (j : Fin 4) :
    standardChainPoint j 0 = ((j : ℕ) : ℝ) + 1 := by
  rw [standardChainPoint, planarPoint_apply_zero]
  simp

theorem interior_nonempty_standardChainRect (j : Fin 3) :
    (interior (standardChainRect j)).Nonempty := by
  have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  exact ⟨EuclideanSpace.single 0 (((j : ℕ) : ℝ) + 1),
    single_mem_interior_rectTwo (by linarith) (by linarith) (by norm_num) (by norm_num)⟩

theorem isPlanarCellChain_standard :
    IsPlanarCellChain standardChainPoint standardChainCell standardChainCellInterior := by
  have hconv : ∀ j : Fin 3, Convex ℝ (standardChainRect j) := fun _ => convex_rectTwo _ _ _ _
  have hcl : ∀ j : Fin 3, IsClosed (standardChainRect j) := fun _ => isClosed_rectTwo _ _ _ _
  have hb : ∀ j : Fin 3, Bornology.IsBounded (standardChainRect j) := fun _ =>
    isBounded_rectTwo _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro j p ⟨x, hx, rfl⟩
    refine ⟨planarPoint_apply_two x, ?_⟩
    have hx0 : ((j : ℕ) : ℝ) + 3 / 5 ≤ x 0 := hx.1.1
    have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [planarPoint_apply_zero]
    linarith
  · exact fun j => isTopologicalCellWithInterior_planarImage (hconv j) (hcl j) (hb j)
      (interior_nonempty_standardChainRect j)
  · exact fun j => image_mono interior_subset
  · intro j p hp
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hp
    have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcast : ((j.castSucc : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by rw [Fin.val_castSucc]
    have hsucc : ((j.succ : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by
      rw [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have hu : EuclideanSpace.single (0 : Fin 2) (((j.castSucc : ℕ) : ℝ) + 1) ∈
        interior (standardChainRect j) := by
      rw [standardChainRect, hcast]
      exact single_mem_interior_rectTwo (by linarith) (by linarith) (by norm_num) (by norm_num)
    have hv : EuclideanSpace.single (0 : Fin 2) (((j.succ : ℕ) : ℝ) + 1) ∈
        interior (standardChainRect j) := by
      rw [standardChainRect, hsucc]
      exact single_mem_interior_rectTwo (by linarith) (by linarith) (by norm_num) (by norm_num)
    refine ⟨s • EuclideanSpace.single (0 : Fin 2) (((j.castSucc : ℕ) : ℝ) + 1) +
      t • EuclideanSpace.single (0 : Fin 2) (((j.succ : ℕ) : ℝ) + 1),
      (hconv j).interior hu hv hs ht hst, ?_⟩
    simp only [standardChainPoint]
    rw [planarPoint_smul_add_smul]
  · intro j heq
    have hval : standardChainPoint j.castSucc 0 = standardChainPoint j.succ 0 := by rw [heq]
    rw [standardChainPoint_apply_zero, standardChainPoint_apply_zero] at hval
    have hcast : ((j.castSucc : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by rw [Fin.val_castSucc]
    have hsucc : ((j.succ : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by
      rw [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    rw [hcast, hsucc] at hval
    linarith
  · intro j
    have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcast : ((j.castSucc : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by rw [Fin.val_castSucc]
    have hsucc : ((j.succ : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by
      rw [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have hrect : standardChainRect j.castSucc ∩ standardChainRect j.succ =
        rectTwo (((j : ℕ) : ℝ) + 1 + 3 / 5) (((j : ℕ) : ℝ) + 12 / 5) (-1) 1 := by
      rw [standardChainRect, standardChainRect, hcast, hsucc, rectTwo_inter,
        max_eq_right (by linarith), min_eq_left (by linarith), max_self, min_self]
    rw [standardChainCell, standardChainCell, ← image_inter planarPoint_injective, hrect]
    refine isTopologicalCell_planarImage (convex_rectTwo _ _ _ _) (isClosed_rectTwo _ _ _ _)
      (isBounded_rectTwo _ _ _ _) ⟨EuclideanSpace.single 0 (((j : ℕ) : ℝ) + 2),
        single_mem_interior_rectTwo (by linarith) (by linarith) (by norm_num) (by norm_num)⟩
  · have h0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    have hrect : standardChainRect 0 ∩ standardChainRect 2 = ∅ := by
      rw [standardChainRect, standardChainRect, h0, h2, rectTwo_inter]
      refine rectTwo_eq_empty ?_ _ _
      norm_num
    rw [standardChainCell, standardChainCell, ← image_inter planarPoint_injective, hrect,
      image_empty]

end Inhabitant

end DifferentialGeometry.Topology.PiecewiseLinear
