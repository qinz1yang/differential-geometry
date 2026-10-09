/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTowerExistence
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImage
import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def momentPoint (N : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun i => t ^ (i.val + 1)

theorem momentPoint_injective {N : ℕ} (hN : 0 < N) : Function.Injective (momentPoint N) := by
  intro s t h
  have h0 : s ^ (0 + 1) = t ^ (0 + 1) :=
    congrArg (EuclideanSpace.projₗ (𝕜 := ℝ) (⟨0, hN⟩ : Fin N)) h
  simpa using h0

theorem affineIndependent_momentPoint {N : ℕ} {S : Finset (EuclideanSpace ℝ (Fin N))}
    (hS : (S : Set (EuclideanSpace ℝ (Fin N))) ⊆ range (momentPoint N))
    (hcard : S.card ≤ N + 1) : AffineIndependent ℝ ((↑) : S → EuclideanSpace ℝ (Fin N)) := by
  classical
  rw [affineIndependent_iff]
  intro s w hw0 hw1 e₀ he₀
  choose t ht using fun e : S => Set.mem_range.mp (hS e.2)
  have hpow : ∀ k ≤ N, ∑ e ∈ s, w e * t e ^ k = 0 := by
    intro k hk
    rcases k with _ | k
    · simpa using hw0
    · have h := congrArg (EuclideanSpace.projₗ (𝕜 := ℝ) (⟨k, by omega⟩ : Fin N)) hw1
      rw [map_sum, map_zero] at h
      refine (Finset.sum_congr rfl fun e _ => ?_).trans h
      rw [map_smul, smul_eq_mul]
      exact congrArg (w e * ·)
        (congrArg (EuclideanSpace.projₗ (𝕜 := ℝ) (⟨k, by omega⟩ : Fin N)) (ht e))
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℝ,
      Q = ∏ e ∈ s.erase e₀, (Polynomial.X - Polynomial.C (t e)) := ⟨_, rfl⟩
  have hdeg : Q.natDegree < N + 1 := by
    have h1 := Polynomial.natDegree_prod_le (s.erase e₀)
      fun e => Polynomial.X - Polynomial.C (t e)
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one] at h1
    have h2 := Finset.card_erase_lt_of_mem he₀
    have h3 : s.card ≤ S.card := (Finset.card_le_univ s).trans (Fintype.card_coe S).le
    rw [hQ]
    omega
  have hsum : ∑ e ∈ s, w e * Q.eval (t e) = 0 := by
    simp_rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k hk => ?_
    have h := hpow k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    calc ∑ e ∈ s, w e * (Q.coeff k * t e ^ k) = Q.coeff k * ∑ e ∈ s, w e * t e ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = 0 := by rw [h, mul_zero]
  have hzero : ∀ e ∈ s, e ≠ e₀ → Q.eval (t e) = 0 := by
    intro e he hne
    rw [hQ, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, he⟩) ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  have hne : Q.eval (t e₀) ≠ 0 := by
    rw [hQ, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun e he => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    intro h
    exact (Finset.mem_erase.mp he).1 (Subtype.ext (by rw [← ht e, ← ht e₀, h]))
  rw [Finset.sum_eq_single e₀ (fun e he hne' => by rw [hzero e he hne', mul_zero])
    (fun h => absurd he₀ h)] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right hne

def momentComplex (N : ℕ) (S : Set (Finset (EuclideanSpace ℝ (Fin N))))
    (hS : IsRelLowerSet S Finset.Nonempty)
    (hrange : ∀ s ∈ S, (s : Set (EuclideanSpace ℝ (Fin N))) ⊆ range (momentPoint N))
    (hcard : ∀ s ∈ S, 2 * s.card ≤ N + 1) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)) where
  faces := S
  isRelLowerSet_faces := hS
  indep hs := affineIndependent_momentPoint (hrange _ hs) (by have := hcard _ hs; omega)
  inter_subset_convexHull {s t} hs ht := by
    classical
    refine (AffineIndependent.convexHull_inter ?_ Finset.subset_union_left
      Finset.subset_union_right).symm.subset
    refine affineIndependent_momentPoint ?_ ?_
    · rw [Finset.coe_union]
      exact union_subset (hrange s hs) (hrange t ht)
    · have h1 := Finset.card_union_le s t
      have h2 := hcard s hs
      have h3 := hcard t ht
      omega

theorem exists_eqOn_of_eqOn_succ {α β : Type*} {S : ℕ → Set α} (hS : Monotone S)
    (f : ℕ → α → β) (hf : ∀ i, EqOn (f (i + 1)) (f i) (S i)) :
    ∃ g : α → β, ∀ i, EqOn g (f i) (S i) := by
  classical
  have hmono : ∀ i j, i ≤ j → EqOn (f j) (f i) (S i) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ j hij ih => exact fun x hx => (hf j (hS hij hx)).trans (ih hx)
  refine ⟨fun x => if h : ∃ i, x ∈ S i then f (Nat.find h) x else f 0 x, fun i x hx => ?_⟩
  have h : ∃ i, x ∈ S i := ⟨i, hx⟩
  exact (dite_eq_left h).trans (hmono _ _ (Nat.find_min' h hx) (Nat.find_spec h)).symm

theorem IsPiecewiseAffineWithinAt.of_subset_of_mem_nhdsWithin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s t : Set E} {x : E} (hf : IsPiecewiseAffineWithinAt f t x) (hts : t ⊆ s)
    (ht : t ∈ 𝓝[s] x) : IsPiecewiseAffineWithinAt f s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  refine ⟨ι, hι, C, A, fun i => ⟨(hC i).1, (hC i).2.1.trans hts, (hC i).2.2⟩, ?_⟩
  rw [nhdsWithin_restrict'' s ht, inter_eq_right.mpr hts]
  exact hCx

theorem simplicialMap_comp_eqOn {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [DecidableEq F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F) (φ : E → F)
    (ψ : F → G) (hφ : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    EqOn (fun x => simplicialMap L ψ (simplicialMap K φ x)) (simplicialMap K (ψ ∘ φ))
      K.space := by
  have haff : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] G,
      EqOn (fun x => simplicialMap L ψ (simplicialMap K φ x)) A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap K φ hs
    obtain ⟨B, hB⟩ := exists_affineMap_eqOn_simplicialMap L ψ (hφ s hs)
    refine ⟨B.comp A, fun x hx => ?_⟩
    change simplicialMap L ψ (simplicialMap K φ x) = B (A x)
    rw [← hA hx]
    exact hB (simplicialMap_mem_convexHull_image K φ hs hx)
  intro x hx
  refine (simplicialMap_eq_of_forall_affineOn K _ haff hx).symm.trans
    (simplicialMap_eqOn_of_eqOn_vertices K (fun v hv => ?_) hx)
  have hv' := hφ {v} hv
  rw [Finset.image_singleton] at hv'
  change simplicialMap L ψ (simplicialMap K φ v) = ψ (φ v)
  rw [simplicialMap_vertex K φ hv, simplicialMap_vertex L ψ hv']

namespace LocallyFinitePieceTower

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {U : Set X} (T : LocallyFinitePieceTower n X U)

theorem exists_injOn_nat_vertices (i : ℕ) :
    ∃ c : EuclideanSpace ℝ (Fin (T.piece i).ambientDim) → ℕ, InjOn c (T.core i).vertices :=
  Set.countable_iff_exists_injOn.mp
    ((T.core_faces_finite i).preimage Finset.singleton_injective.injOn).countable

noncomputable def vertexCode (i : ℕ) : EuclideanSpace ℝ (Fin (T.piece i).ambientDim) → ℕ :=
  Classical.choose (T.exists_injOn_nat_vertices i)

theorem injOn_vertexCode (i : ℕ) : InjOn (T.vertexCode i) (T.core i).vertices :=
  Classical.choose_spec (T.exists_injOn_nat_vertices i)

open Classical in
noncomputable def vertexParam (i : ℕ) : EuclideanSpace ℝ (Fin (T.piece i).ambientDim) → ℕ :=
  Nat.rec (motive := fun i => EuclideanSpace ℝ (Fin (T.piece i).ambientDim) → ℕ)
    (fun v => Nat.pair 0 (T.vertexCode 0 v))
    (fun i p w => if {w} ∈ (T.coreImage i).faces then p (T.embedInv i w)
      else Nat.pair (i + 1) (T.vertexCode (i + 1) w)) i

theorem vertexParam_zero (v : EuclideanSpace ℝ (Fin (T.piece 0).ambientDim)) :
    T.vertexParam 0 v = Nat.pair 0 (T.vertexCode 0 v) :=
  rfl

open Classical in
theorem vertexParam_succ (i : ℕ) (w : EuclideanSpace ℝ (Fin (T.piece (i + 1)).ambientDim)) :
    T.vertexParam (i + 1) w = if {w} ∈ (T.coreImage i).faces then
      T.vertexParam i (T.embedInv i w) else Nat.pair (i + 1) (T.vertexCode (i + 1) w) :=
  rfl

theorem unpair_vertexParam_fst_le (i : ℕ) :
    ∀ v : EuclideanSpace ℝ (Fin (T.piece i).ambientDim),
      (Nat.unpair (T.vertexParam i v)).1 ≤ i := by
  induction i with
  | zero =>
    intro v
    rw [vertexParam_zero, Nat.unpair_pair]
  | succ i ih =>
    intro w
    rw [vertexParam_succ]
    split_ifs
    · exact (ih _).trans (Nat.le_succ i)
    · rw [Nat.unpair_pair]

theorem injOn_vertexParam (i : ℕ) : InjOn (T.vertexParam i) (T.core i).vertices := by
  induction i with
  | zero =>
    intro v hv w hw h
    rw [vertexParam_zero, vertexParam_zero] at h
    exact T.injOn_vertexCode 0 hv hw (Nat.pair_eq_pair.mp h).2
  | succ i ih =>
    intro v hv w hw h
    rw [vertexParam_succ, vertexParam_succ] at h
    have hiso := T.embed_isGlueIso i
    by_cases hvA : {v} ∈ (T.coreImage i).faces <;> by_cases hwA : {w} ∈ (T.coreImage i).faces
    · rw [ite_eq_left hvA, ite_eq_left hwA] at h
      have hv' : T.embedInv i v ∈ (T.core i).vertices := hiso.symm.singleton_mem hvA
      have hw' : T.embedInv i w ∈ (T.core i).vertices := hiso.symm.singleton_mem hwA
      calc v = T.embed i (T.embedInv i v) :=
            (hiso.right _ hvA v (Finset.mem_singleton_self v)).symm
        _ = T.embed i (T.embedInv i w) := by rw [ih hv' hw' h]
        _ = w := hiso.right _ hwA w (Finset.mem_singleton_self w)
    · rw [ite_eq_left hvA, ite_eq_right hwA] at h
      have h1 := T.unpair_vertexParam_fst_le i (T.embedInv i v)
      rw [h, Nat.unpair_pair] at h1
      omega
    · rw [ite_eq_right hvA, ite_eq_left hwA] at h
      have h1 := T.unpair_vertexParam_fst_le i (T.embedInv i w)
      rw [← h, Nat.unpair_pair] at h1
      omega
    · rw [ite_eq_right hvA, ite_eq_right hwA] at h
      exact T.injOn_vertexCode (i + 1) hv hw (Nat.pair_eq_pair.mp h).2

theorem vertexParam_embed (i : ℕ) {v : EuclideanSpace ℝ (Fin (T.piece i).ambientDim)}
    (hv : {v} ∈ (T.core i).faces) : T.vertexParam (i + 1) (T.embed i v) = T.vertexParam i v := by
  rw [vertexParam_succ, ite_eq_left ((T.embed_isGlueIso i).singleton_mem hv),
    (T.embed_isGlueIso i).left _ hv v (Finset.mem_singleton_self v)]

noncomputable def vertexPos (i : ℕ) (v : EuclideanSpace ℝ (Fin (T.piece i).ambientDim)) :
    EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  momentPoint (2 * n + 1) (T.vertexParam i v)

theorem injOn_vertexPos (i : ℕ) : InjOn (T.vertexPos i) (T.core i).vertices :=
  fun _ hv _ hw h =>
    T.injOn_vertexParam i hv hw (Nat.cast_injective (momentPoint_injective (by omega) h))

theorem vertexPos_embed (i : ℕ) {v : EuclideanSpace ℝ (Fin (T.piece i).ambientDim)}
    (hv : {v} ∈ (T.core i).faces) : T.vertexPos (i + 1) (T.embed i v) = T.vertexPos i v :=
  congrArg (fun k : ℕ => momentPoint (2 * n + 1) k) (T.vertexParam_embed i hv)

variable (hcard : ∀ i, ∀ s ∈ (T.core i).faces, s.card ≤ n + 1)

noncomputable def limitComplex :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (2 * n + 1))) :=
  momentComplex (2 * n + 1) (⋃ i, simplicialImageFaces (T.core i) (T.vertexPos i))
    (by
      intro t ht
      obtain ⟨i, hi⟩ := mem_iUnion.mp ht
      obtain ⟨hne, hdown⟩ := simplicialImageFaces_isRelLowerSet (T.core i) (T.vertexPos i) hi
      exact ⟨hne, fun b hb hbne => mem_iUnion.mpr ⟨i, hdown hb hbne⟩⟩)
    (by
      intro t ht x hx
      obtain ⟨i, σ, -, rfl⟩ := mem_iUnion.mp ht
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨_, rfl⟩)
    (by
      intro t ht
      obtain ⟨i, σ, hσ, rfl⟩ := mem_iUnion.mp ht
      have h := (Finset.card_image_le (s := σ) (f := T.vertexPos i)).trans (hcard i σ hσ)
      omega)

theorem mem_limitComplex_faces_of_mem (i : ℕ)
    {σ : Finset (EuclideanSpace ℝ (Fin (T.piece i).ambientDim))} (hσ : σ ∈ (T.core i).faces) :
    σ.image (T.vertexPos i) ∈ (T.limitComplex hcard).faces :=
  mem_iUnion.mpr ⟨i, σ, hσ, rfl⟩

include hcard in
theorem injOn_simplicialMap_vertexPos (i : ℕ) :
    InjOn (simplicialMap (T.core i) (T.vertexPos i)) (T.core i).space := by
  have hψφ : ∀ s ∈ (T.core i).faces, ∀ v ∈ s,
      Function.invFunOn (T.vertexPos i) (T.core i).vertices (T.vertexPos i v) = v :=
    fun s hs v hv => (T.injOn_vertexPos i).leftInvOn_invFunOn
      ((T.core i).down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  intro x hx y hy hxy
  rw [← simplicialMap_simplicialMap (T.core i) (T.limitComplex hcard) (T.vertexPos i) _
      (fun s hs => T.mem_limitComplex_faces_of_mem hcard i hs) hψφ hx,
    ← simplicialMap_simplicialMap (T.core i) (T.limitComplex hcard) (T.vertexPos i) _
      (fun s hs => T.mem_limitComplex_faces_of_mem hcard i hs) hψφ hy, hxy]

include hcard in
theorem affineIndependent_image_vertexPos (i : ℕ) :
    ∀ σ ∈ (T.core i).faces, AffineIndependent ℝ
      ((↑) : {u // u ∈ σ.image (T.vertexPos i)} → EuclideanSpace ℝ (Fin (2 * n + 1))) :=
  fun _ hσ => (T.limitComplex hcard).indep (T.mem_limitComplex_faces_of_mem hcard i hσ)

noncomputable def levelComplex (i : ℕ) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (2 * n + 1))) :=
  simplicialImage (T.core i) (T.vertexPos i) (T.affineIndependent_image_vertexPos hcard i)
    (T.injOn_simplicialMap_vertexPos hcard i)

theorem mem_levelComplex_faces_iff (i : ℕ) {t : Finset (EuclideanSpace ℝ (Fin (2 * n + 1)))} :
    t ∈ (T.levelComplex hcard i).faces ↔ ∃ σ ∈ (T.core i).faces, t = σ.image (T.vertexPos i) :=
  Iff.rfl

theorem mem_limitComplex_faces_iff {t : Finset (EuclideanSpace ℝ (Fin (2 * n + 1)))} :
    t ∈ (T.limitComplex hcard).faces ↔ ∃ i, t ∈ (T.levelComplex hcard i).faces :=
  mem_iUnion

theorem levelComplex_faces_subset_limitComplex (i : ℕ) :
    (T.levelComplex hcard i).faces ⊆ (T.limitComplex hcard).faces :=
  fun _ ht => (T.mem_limitComplex_faces_iff hcard).mpr ⟨i, ht⟩

theorem levelComplex_space (i : ℕ) :
    (T.levelComplex hcard i).space =
      simplicialMap (T.core i) (T.vertexPos i) '' (T.core i).space :=
  simplicialImage_space _ _ _ _

theorem levelComplex_faces_finite (i : ℕ) : (T.levelComplex hcard i).faces.Finite := by
  have : Finite (T.core i).faces := (T.core_faces_finite i).to_subtype
  exact simplicialImage_faces_finite (T.core i) (T.vertexPos i)
    (T.affineIndependent_image_vertexPos hcard i) (T.injOn_simplicialMap_vertexPos hcard i)

theorem levelComplex_faces_subset_succ (i : ℕ) :
    (T.levelComplex hcard i).faces ⊆ (T.levelComplex hcard (i + 1)).faces := by
  intro t ht
  obtain ⟨σ, hσ, rfl⟩ := (T.mem_levelComplex_faces_iff hcard i).mp ht
  refine (T.mem_levelComplex_faces_iff hcard (i + 1)).mpr
    ⟨σ.image (T.embed i), T.coreImage_le i ((T.embed_isGlueIso i).image₁ σ hσ), ?_⟩
  rw [Finset.image_image]
  exact Finset.image_congr fun v hv => (T.vertexPos_embed i ((T.core i).down_closed hσ
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))).symm

theorem levelComplex_mono : Monotone fun i => (T.levelComplex hcard i).faces :=
  monotone_nat_of_le_succ (T.levelComplex_faces_subset_succ hcard)

theorem levelComplex_space_mono : Monotone fun i => (T.levelComplex hcard i).space :=
  fun _ _ hij => space_mono_of_faces_subset (T.levelComplex_mono hcard hij)

theorem mem_limitComplex_space {z : EuclideanSpace ℝ (Fin (2 * n + 1))} :
    z ∈ (T.limitComplex hcard).space ↔ ∃ i, z ∈ (T.levelComplex hcard i).space := by
  constructor
  · intro hz
    obtain ⟨s, hs, hzs⟩ := (T.limitComplex hcard).mem_space_iff.mp hz
    obtain ⟨i, hi⟩ := (T.mem_limitComplex_faces_iff hcard).mp hs
    exact ⟨i, (T.levelComplex hcard i).convexHull_subset_space hi hzs⟩
  · rintro ⟨i, hi⟩
    obtain ⟨s, hs, hzs⟩ := (T.levelComplex hcard i).mem_space_iff.mp hi
    exact (T.limitComplex hcard).convexHull_subset_space
      (T.levelComplex_faces_subset_limitComplex hcard i hs) hzs

theorem levelComplex_space_subset (i : ℕ) :
    (T.levelComplex hcard i).space ⊆ (T.limitComplex hcard).space :=
  fun _ hz => (T.mem_limitComplex_space hcard).mpr ⟨i, hz⟩

noncomputable def levelPiece (i : ℕ) :
    PLPieceIn (EuclideanSpace ℝ (Fin (2 * n + 1))) n X (T.coreSpace i) :=
  haveI : Finite (T.core i).faces := (T.core_faces_finite i).to_subtype
  ((T.piece i).piece.restrict (T.core i) (T.core_le i)).precomp (T.levelComplex hcard i)
    (T.levelComplex_faces_finite hcard i)
    (isPLHomeomorphOn_simplicialImage (T.core i) (T.vertexPos i)
      (T.affineIndependent_image_vertexPos hcard i) (T.injOn_simplicialMap_vertexPos hcard i)).symm

theorem levelPiece_complex (i : ℕ) : (T.levelPiece hcard i).complex = T.levelComplex hcard i :=
  rfl

theorem levelPiece_map (i : ℕ) :
    (T.levelPiece hcard i).map = (T.piece i).piece.map ∘
      Function.invFunOn (simplicialMap (T.core i) (T.vertexPos i)) (T.core i).space :=
  rfl

theorem levelPiece_map_simplicialMap (i : ℕ)
    {x : EuclideanSpace ℝ (Fin (T.piece i).ambientDim)} (hx : x ∈ (T.core i).space) :
    (T.levelPiece hcard i).map (simplicialMap (T.core i) (T.vertexPos i) x) =
      (T.piece i).piece.map x := by
  rw [levelPiece_map, Function.comp_apply,
    (T.injOn_simplicialMap_vertexPos hcard i).leftInvOn_invFunOn hx]

theorem levelPiece_map_eqOn_succ (i : ℕ) :
    EqOn (T.levelPiece hcard (i + 1)).map (T.levelPiece hcard i).map
      (T.levelComplex hcard i).space := by
  intro z hz
  rw [T.levelComplex_space hcard i] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hy : simplicialMap (T.core i) (T.embed i) x ∈ (T.core (i + 1)).space :=
    T.embed_mapsTo_core i hx
  have hcomp : simplicialMap (T.core (i + 1)) (T.vertexPos (i + 1))
      (simplicialMap (T.core i) (T.embed i) x) = simplicialMap (T.core i) (T.vertexPos i) x :=
    (simplicialMap_comp_eqOn (T.core i) (T.core (i + 1)) (T.embed i) (T.vertexPos (i + 1))
      (fun s hs => T.coreImage_le i ((T.embed_isGlueIso i).image₁ s hs)) hx).trans
      (simplicialMap_eqOn_of_eqOn_vertices (T.core i) (fun v hv => T.vertexPos_embed i hv) hx)
  calc (T.levelPiece hcard (i + 1)).map (simplicialMap (T.core i) (T.vertexPos i) x)
      = (T.levelPiece hcard (i + 1)).map (simplicialMap (T.core (i + 1)) (T.vertexPos (i + 1))
          (simplicialMap (T.core i) (T.embed i) x)) := by rw [hcomp]
    _ = (T.piece (i + 1)).piece.map (simplicialMap (T.core i) (T.embed i) x) :=
        T.levelPiece_map_simplicialMap hcard (i + 1) hy
    _ = (T.piece i).piece.map x := T.map_embed i x hx
    _ = (T.levelPiece hcard i).map (simplicialMap (T.core i) (T.vertexPos i) x) :=
        (T.levelPiece_map_simplicialMap hcard i hx).symm

theorem exists_limitMap : ∃ F : EuclideanSpace ℝ (Fin (2 * n + 1)) → X,
    ∀ i, EqOn F (T.levelPiece hcard i).map (T.levelComplex hcard i).space :=
  exists_eqOn_of_eqOn_succ (T.levelComplex_space_mono hcard)
    (fun i => (T.levelPiece hcard i).map) (T.levelPiece_map_eqOn_succ hcard)

noncomputable def limitMap : EuclideanSpace ℝ (Fin (2 * n + 1)) → X :=
  Classical.choose (T.exists_limitMap hcard)

theorem limitMap_eqOn (i : ℕ) :
    EqOn (T.limitMap hcard) (T.levelPiece hcard i).map (T.levelComplex hcard i).space :=
  Classical.choose_spec (T.exists_limitMap hcard) i

theorem continuousOn_limitMap_levelComplex (i : ℕ) :
    ContinuousOn (T.limitMap hcard) (T.levelComplex hcard i).space :=
  (T.levelPiece hcard i).continuousOn.congr (T.limitMap_eqOn hcard i)

theorem injOn_limitMap_levelComplex (i : ℕ) :
    InjOn (T.limitMap hcard) (T.levelComplex hcard i).space :=
  (T.levelPiece hcard i).bijOn.injOn.congr (T.limitMap_eqOn hcard i).symm

theorem image_limitMap_levelComplex (i : ℕ) :
    T.limitMap hcard '' (T.levelComplex hcard i).space = T.coreSpace i :=
  (Set.image_congr fun _ hz => T.limitMap_eqOn hcard i hz).trans
    (T.levelPiece hcard i).bijOn.image_eq

theorem limitMap_mem_coreSpace (i : ℕ) {z : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hz : z ∈ (T.levelComplex hcard i).space) : T.limitMap hcard z ∈ T.coreSpace i :=
  (T.image_limitMap_levelComplex hcard i).subset (mem_image_of_mem _ hz)

theorem mem_levelComplex_faces_of_mem_space (i : ℕ) {v : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hv : v ∈ (T.levelComplex hcard i).space)
    {σ : Finset (EuclideanSpace ℝ (Fin (2 * n + 1)))} (hσ : σ ∈ (T.limitComplex hcard).faces)
    (hvσ : v ∈ σ) : σ ∈ (T.levelComplex hcard (i + 2)).faces := by
  obtain ⟨m, hm⟩ := (T.mem_limitComplex_faces_iff hcard).mp hσ
  have hle : i + 2 ≤ max m (i + 2) := le_max_right m (i + 2)
  have hσj : σ ∈ (T.levelComplex hcard (max m (i + 2))).faces :=
    T.levelComplex_mono hcard (le_max_left m (i + 2)) hm
  have hvj : v ∈ (T.levelComplex hcard (max m (i + 2))).space :=
    T.levelComplex_space_mono hcard ((Nat.le_add_right i 2).trans hle) hv
  have hW : T.coreSpace (i + 2) ∈ 𝓝[U] (T.limitMap hcard v) :=
    T.core_space_mem_nhdsWithin (T.core_space_subset i (T.limitMap_mem_coreSpace hcard i hv))
  have hmaps : T.limitMap hcard '' (T.levelComplex hcard (max m (i + 2))).space ⊆ U := by
    rw [T.image_limitMap_levelComplex hcard]
    exact T.core_space_subset_union _
  have hpre : T.limitMap hcard ⁻¹' T.coreSpace (i + 2) ∈
      𝓝[(T.levelComplex hcard (max m (i + 2))).space] v :=
    (T.continuousOn_limitMap_levelComplex hcard _ v hvj).preimage_mem_nhdsWithin'
      (nhdsWithin_mono _ hmaps hW)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  have hσne : σ.Nonempty := ⟨v, hvσ⟩
  have hb : σ.centroid ℝ id ∈ openSimplex σ := centroid_mem_openSimplex hσne
  have hvhull : v ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hvσ)
  have hcts : Continuous fun r : ℝ => σ.centroid ℝ id + r • (v - σ.centroid ℝ id) := by
    fun_prop
  have hnear : ∀ᶠ r in 𝓝 (1 : ℝ),
      σ.centroid ℝ id + r • (v - σ.centroid ℝ id) ∈ Metric.ball v ε :=
    hcts.continuousAt.eventually_mem (by simpa using Metric.ball_mem_nhds v hε)
  obtain ⟨r, ⟨hr0, hr1⟩, hr⟩ :=
    ((show ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhdsLT one_pos).and
      (hnear.filter_mono nhdsWithin_le_nhds)).exists
  have hyopen : σ.centroid ℝ id + r • (v - σ.centroid ℝ id) ∈ openSimplex σ :=
    add_smul_sub_mem_openSimplex hb hvhull hr0.le hr1
  have hyj : σ.centroid ℝ id + r • (v - σ.centroid ℝ id) ∈
      (T.levelComplex hcard (max m (i + 2))).space :=
    (T.levelComplex hcard _).convexHull_subset_space hσj (openSimplex_subset_convexHull σ hyopen)
  have hFy : T.limitMap hcard (σ.centroid ℝ id + r • (v - σ.centroid ℝ id)) ∈
      T.limitMap hcard '' (T.levelComplex hcard (i + 2)).space := by
    rw [T.image_limitMap_levelComplex hcard]
    exact hball ⟨hr, hyj⟩
  obtain ⟨y', hy', hFy'⟩ := hFy
  have hyy : y' = σ.centroid ℝ id + r • (v - σ.centroid ℝ id) :=
    T.injOn_limitMap_levelComplex hcard _ (T.levelComplex_space_mono hcard hle hy') hyj hFy'
  rw [hyy] at hy'
  obtain ⟨τ, hτ, hyτ⟩ := (T.levelComplex hcard (i + 2)).mem_space_iff.mp hy'
  have hτj : τ ∈ (T.levelComplex hcard (max m (i + 2))).faces := T.levelComplex_mono hcard hle hτ
  exact (T.levelComplex hcard (i + 2)).down_closed hτ
    (face_subset_of_mem_openSimplex_of_mem_convexHull _ hσj hτj hyopen hyτ) hσne

theorem finite_setOf_mem_limitComplex_faces (v : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    {s | s ∈ (T.limitComplex hcard).faces ∧ v ∈ s}.Finite := by
  by_cases h : ∃ s ∈ (T.limitComplex hcard).faces, v ∈ s
  · obtain ⟨s₀, hs₀, hvs₀⟩ := h
    obtain ⟨m, hm⟩ := (T.mem_limitComplex_faces_iff hcard).mp hs₀
    have hvm : v ∈ (T.levelComplex hcard m).space :=
      (T.levelComplex hcard m).convexHull_subset_space hm
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr hvs₀))
    exact (T.levelComplex_faces_finite hcard (m + 2)).subset
      fun s hs => T.mem_levelComplex_faces_of_mem_space hcard m hvm hs.1 hs.2
  · exact Set.finite_empty.subset fun s hs => h ⟨s, hs.1, hs.2⟩

theorem locallyFinite_convexHull_limitComplex :
    LocallyFinite fun s : (T.limitComplex hcard).faces =>
      convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin (2 * n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (2 * n + 1)))) := by
  intro z
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : EuclideanSpace ℝ (Fin (2 * n + 1)) →ₗ[ℝ] ℝ,
      ∀ t : ℝ, ℓ (momentPoint (2 * n + 1) t) = t :=
    ⟨EuclideanSpace.projₗ (⟨0, by omega⟩ : Fin (2 * n + 1)), fun t => pow_one t⟩
  refine ⟨{y | ℓ y < ℓ z + 1}, (isOpen_lt (LinearMap.continuous_of_finiteDimensional ℓ)
    continuous_const).mem_nhds (lt_add_one (ℓ z)), ?_⟩
  refine (((Set.finite_Iio ⌈ℓ z + 1⌉₊).biUnion fun k _ =>
    T.finite_setOf_mem_limitComplex_faces hcard (momentPoint (2 * n + 1) k)).preimage
      Subtype.val_injective.injOn).subset ?_
  rintro ⟨s, hs⟩ ⟨y, hys, hyW⟩
  obtain ⟨v, hvs, hv⟩ : ∃ v ∈ s, ℓ v < ℓ z + 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    exact absurd (show ℓ z + 1 ≤ ℓ y from convexHull_min (fun v hv => hcon v hv)
      (convex_halfSpace_ge ℓ.isLinear (ℓ z + 1)) hys) (not_le.mpr hyW)
  obtain ⟨m, hm⟩ := (T.mem_limitComplex_faces_iff hcard).mp hs
  obtain ⟨σ, -, rfl⟩ := (T.mem_levelComplex_faces_iff hcard m).mp hm
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hvs
  refine mem_iUnion₂.mpr ⟨T.vertexParam m u, ?_, hs, hvs⟩
  rw [Set.mem_Iio, Nat.lt_ceil, ← hℓ (T.vertexParam m u)]
  exact hv

theorem levelComplex_space_mem_nhdsWithin (i : ℕ) {z : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hz : z ∈ (T.levelComplex hcard i).space) :
    (T.levelComplex hcard (i + 2)).space ∈ 𝓝[(T.limitComplex hcard).space] z := by
  have hev := (T.locallyFinite_convexHull_limitComplex hcard).eventually_subset
    (fun s => (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed) z
  obtain ⟨τ, hτ, hzτ⟩ := (T.levelComplex hcard i).mem_space_iff.mp hz
  refine mem_nhdsWithin_iff_eventually.mpr (hev.mono fun y hy hyK => ?_)
  obtain ⟨s, hs, hys⟩ := (T.limitComplex hcard).mem_space_iff.mp hyK
  have hzs : z ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))) := @hy ⟨s, hs⟩ hys
  have hinter := (T.limitComplex hcard).inter_subset_convexHull hs
    (T.levelComplex_faces_subset_limitComplex hcard i hτ) ⟨hzs, hzτ⟩
  obtain ⟨v, hvs, hvτ⟩ : ((s : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))) ∩ τ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, convexHull_empty] at hinter
    exact hinter
  have hvi : v ∈ (T.levelComplex hcard i).space :=
    (T.levelComplex hcard i).convexHull_subset_space hτ (subset_convexHull ℝ _ hvτ)
  exact (T.levelComplex hcard (i + 2)).convexHull_subset_space
    (T.mem_levelComplex_faces_of_mem_space hcard i hvi hs hvs) hys

theorem continuousOn_limitMap :
    ContinuousOn (T.limitMap hcard) (T.limitComplex hcard).space := by
  intro z hz
  obtain ⟨i, hi⟩ := (T.mem_limitComplex_space hcard).mp hz
  exact (T.continuousOn_limitMap_levelComplex hcard (i + 2) z
    (T.levelComplex_space_mono hcard (Nat.le_add_right i 2) hi)).mono_of_mem_nhdsWithin
    (T.levelComplex_space_mem_nhdsWithin hcard i hi)

theorem injOn_limitMap : InjOn (T.limitMap hcard) (T.limitComplex hcard).space := by
  intro z hz w hw h
  obtain ⟨i, hi⟩ := (T.mem_limitComplex_space hcard).mp hz
  obtain ⟨j, hj⟩ := (T.mem_limitComplex_space hcard).mp hw
  exact T.injOn_limitMap_levelComplex hcard (max i j)
    (T.levelComplex_space_mono hcard (le_max_left i j) hi)
    (T.levelComplex_space_mono hcard (le_max_right i j) hj) h

theorem bijOn_limitMap : BijOn (T.limitMap hcard) (T.limitComplex hcard).space U := by
  refine ⟨fun z hz => ?_, T.injOn_limitMap hcard, fun x hx => ?_⟩
  · obtain ⟨i, hi⟩ := (T.mem_limitComplex_space hcard).mp hz
    exact T.core_space_subset_union i (T.limitMap_mem_coreSpace hcard i hi)
  · obtain ⟨i, hi⟩ := T.exists_mem_core_space hx
    rw [← T.image_limitMap_levelComplex hcard i] at hi
    obtain ⟨z, hz, hzx⟩ := hi
    exact ⟨z, T.levelComplex_space_subset hcard i hz, hzx⟩

theorem invFunOn_limitMap_eq (i : ℕ) {x : X} (hx : x ∈ T.coreSpace i) :
    Function.invFunOn (T.limitMap hcard) (T.limitComplex hcard).space x =
      Function.invFunOn (T.levelPiece hcard i).map (T.levelComplex hcard i).space x := by
  have ha : Function.invFunOn (T.levelPiece hcard i).map (T.levelComplex hcard i).space x ∈
      (T.levelComplex hcard i).space :=
    (T.levelPiece hcard i).bijOn.surjOn.mapsTo_invFunOn hx
  have hFa : T.limitMap hcard
      (Function.invFunOn (T.levelPiece hcard i).map (T.levelComplex hcard i).space x) = x :=
    (T.limitMap_eqOn hcard i ha).trans ((T.levelPiece hcard i).bijOn.surjOn.rightInvOn_invFunOn hx)
  calc Function.invFunOn (T.limitMap hcard) (T.limitComplex hcard).space x
      = Function.invFunOn (T.limitMap hcard) (T.limitComplex hcard).space (T.limitMap hcard
          (Function.invFunOn (T.levelPiece hcard i).map (T.levelComplex hcard i).space x)) := by
        rw [hFa]
    _ = Function.invFunOn (T.levelPiece hcard i).map (T.levelComplex hcard i).space x :=
        (T.injOn_limitMap hcard).leftInvOn_invFunOn (T.levelComplex_space_subset hcard i ha)

theorem continuousOn_invFunOn_limitMap [T2Space X] :
    ContinuousOn (Function.invFunOn (T.limitMap hcard) (T.limitComplex hcard).space) U := by
  intro x hx
  obtain ⟨i, hi⟩ := T.exists_mem_core_space hx
  have hW : T.coreSpace (i + 2) ∈ 𝓝[U] x := T.core_space_mem_nhdsWithin (T.core_space_subset i hi)
  have hxW : x ∈ T.coreSpace (i + 2) := T.core_space_monotone (Nat.le_add_right i 2) hi
  have hc : ContinuousOn (Function.invFunOn (T.levelPiece hcard (i + 2)).map
      (T.levelComplex hcard (i + 2)).space) (T.coreSpace (i + 2)) := by
    have h := continuousOn_invFunOn_image_of_isCompact
      (T.levelPiece hcard (i + 2)).isPolyhedron_space.isCompact
      (T.levelPiece hcard (i + 2)).continuousOn (T.levelPiece hcard (i + 2)).bijOn.injOn
    rw [(T.levelPiece hcard (i + 2)).bijOn.image_eq, levelPiece_complex] at h
    exact h
  exact ((hc x hxW).congr (fun y hy => T.invFunOn_limitMap_eq hcard (i + 2) hy)
    (T.invFunOn_limitMap_eq hcard (i + 2) hxW)).mono_of_mem_nhdsWithin hW

theorem isEmbedding_limitMap [T2Space X] :
    IsEmbedding fun z : (T.limitComplex hcard).space => T.limitMap hcard z := by
  have hbij := T.bijOn_limitMap hcard
  have hg : Continuous fun z : (T.limitComplex hcard).space =>
      (⟨T.limitMap hcard z, hbij.mapsTo z.2⟩ : U) :=
    (continuousOn_iff_continuous_domRestrict.mp (T.continuousOn_limitMap hcard)).subtype_mk
      fun z => hbij.mapsTo z.2
  have hf : Continuous fun x : U => (⟨Function.invFunOn (T.limitMap hcard)
      (T.limitComplex hcard).space x, hbij.surjOn.mapsTo_invFunOn x.2⟩ :
        (T.limitComplex hcard).space) :=
    (continuousOn_iff_continuous_domRestrict.mp
      (T.continuousOn_invFunOn_limitMap hcard)).subtype_mk fun x => hbij.surjOn.mapsTo_invFunOn x.2
  have hleft : Function.LeftInverse (fun x : U => (⟨Function.invFunOn (T.limitMap hcard)
      (T.limitComplex hcard).space x, hbij.surjOn.mapsTo_invFunOn x.2⟩ :
        (T.limitComplex hcard).space))
      (fun z : (T.limitComplex hcard).space => (⟨T.limitMap hcard z, hbij.mapsTo z.2⟩ : U)) :=
    fun z => Subtype.ext (hbij.injOn.leftInvOn_invFunOn z.2)
  exact IsEmbedding.subtypeVal.comp (hleft.isEmbedding hf hg)

theorem isPiecewiseAffineOn_chart_limitMap : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ T.limitMap hcard)
      ((T.limitComplex hcard).space ∩ T.limitMap hcard ⁻¹' e.source) := by
  intro e he z hz
  obtain ⟨i, hi⟩ := (T.mem_limitComplex_space hcard).mp hz.1
  have hz2 : z ∈ (T.levelComplex hcard (i + 2)).space :=
    T.levelComplex_space_mono hcard (Nat.le_add_right i 2) hi
  have hP : IsPiecewiseAffineOn (e ∘ (T.levelPiece hcard (i + 2)).map)
      ((T.levelComplex hcard (i + 2)).space ∩ (T.levelPiece hcard (i + 2)).map ⁻¹' e.source) :=
    (T.levelPiece hcard (i + 2)).isPiecewiseAffineOn_chart e he
  have hze : z ∈ (T.levelPiece hcard (i + 2)).map ⁻¹' e.source := by
    rw [mem_preimage, ← T.limitMap_eqOn hcard (i + 2) hz2]
    exact hz.2
  have hset : (T.levelComplex hcard (i + 2)).space ∩
      (T.levelPiece hcard (i + 2)).map ⁻¹' e.source =
        ((T.limitComplex hcard).space ∩ T.limitMap hcard ⁻¹' e.source) ∩
          (T.levelComplex hcard (i + 2)).space := by
    ext y
    constructor
    · rintro ⟨hy, hye⟩
      refine ⟨⟨T.levelComplex_space_subset hcard (i + 2) hy, ?_⟩, hy⟩
      rw [mem_preimage, T.limitMap_eqOn hcard (i + 2) hy]
      exact hye
    · rintro ⟨⟨-, hye⟩, hy⟩
      refine ⟨hy, ?_⟩
      rw [mem_preimage, ← T.limitMap_eqOn hcard (i + 2) hy]
      exact hye
  have hPz := hP z ⟨hz2, hze⟩
  rw [hset] at hPz
  refine (hPz.congr (g := e ∘ T.limitMap hcard) fun y hy => ?_).of_subset_of_mem_nhdsWithin
    inter_subset_left (inter_mem self_mem_nhdsWithin (nhdsWithin_mono _ inter_subset_left
      (T.levelComplex_space_mem_nhdsWithin hcard i hi)))
  exact congrArg e (T.limitMap_eqOn hcard (i + 2) hy.2)

theorem isPiecewiseAffineOn_chart_symm_limitMap : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn
      (Function.invFunOn (T.limitMap hcard) (T.limitComplex hcard).space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' U) := by
  intro e he y hy
  obtain ⟨i, hi⟩ := T.exists_mem_core_space hy.2
  have hiW : e.symm y ∈ T.coreSpace (i + 2) := T.core_space_monotone (Nat.le_add_right i 2) hi
  have hP : IsPiecewiseAffineOn (Function.invFunOn (T.levelPiece hcard (i + 2)).map
      (T.levelComplex hcard (i + 2)).space ∘ e.symm) (e.target ∩ e.symm ⁻¹' T.coreSpace (i + 2)) :=
    (T.levelPiece hcard (i + 2)).isPiecewiseAffineOn_chart_symm e he
  have hW : T.coreSpace (i + 2) ∈ 𝓝[U] (e.symm y) :=
    T.core_space_mem_nhdsWithin (T.core_space_subset i hi)
  have hc : ContinuousWithinAt e.symm (e.target ∩ e.symm ⁻¹' U) y :=
    (e.continuousOn_symm y hy.1).mono inter_subset_left
  have hpre : e.symm ⁻¹' T.coreSpace (i + 2) ∈ 𝓝[e.target ∩ e.symm ⁻¹' U] y :=
    hc.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_subset_iff.mpr fun _ hy' => hy'.2) hW)
  refine ((hP y ⟨hy.1, hiW⟩).congr
    (g := Function.invFunOn (T.limitMap hcard) (T.limitComplex hcard).space ∘ e.symm)
    fun y' hy' => ?_).of_subset_of_mem_nhdsWithin
    (inter_subset_inter_right _ (preimage_mono (T.core_space_subset_union (i + 2))))
    (mem_of_superset (inter_mem self_mem_nhdsWithin hpre) fun y' hy' => ⟨hy'.1.1, hy'.2⟩)
  exact T.invFunOn_limitMap_eq hcard (i + 2) hy'.2

noncomputable def toLocallyFinitePLPieceIn [T2Space X] :
    LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin (2 * n + 1))) n X U where
  complex := T.limitComplex hcard
  locallyFinite :=
    (T.locallyFinite_convexHull_limitComplex hcard).preimage_continuous continuous_subtype_val
  map := T.limitMap hcard
  bijOn := T.bijOn_limitMap hcard
  continuousOn := T.continuousOn_limitMap hcard
  isEmbedding := T.isEmbedding_limitMap hcard
  isPiecewiseAffineOn_chart := T.isPiecewiseAffineOn_chart_limitMap hcard
  isPiecewiseAffineOn_chart_symm := T.isPiecewiseAffineOn_chart_symm_limitMap hcard

end LocallyFinitePieceTower

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}

theorem exists_locallyFinitePLPieceIn_of_isOpen [Nonempty M₁] [T2Space M₁]
    [SecondCountableTopology M₁] [HasGroupoid M₁ (plGroupoid 3)] (hU : IsOpen U) :
    ∃ N : ℕ, Nonempty (LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin N)) 3 M₁ U) := by
  obtain ⟨T, hT⟩ := exists_locallyFinitePieceTower_of_isOpen (m := 2) (X := M₁) hU
  refine ⟨2 * 3 + 1, ⟨T.toLocallyFinitePLPieceIn fun i s hs => ?_⟩⟩
  have : Finite (T.piece i).piece.complex.faces := (T.piece i).piece.finite_faces.to_subtype
  exact (hT i).card_le _ (T.core_le i hs)

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
