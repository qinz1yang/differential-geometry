/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

open Set Topology unitInterval

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isHPolytope_Icc {a b : ℝ} : IsHPolytope (Icc a b) := by
  refine ⟨isCompact_Icc, Fin 2, inferInstance, ![LinearMap.id, -LinearMap.id], ![b, -a], ?_⟩
  ext t
  constructor
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · simpa using h1
    · simpa using neg_le_neg h0
  · intro h
    have h1 := h 0
    have h0 := h 1
    simp only [Matrix.cons_val_zero, LinearMap.id_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one,
      LinearMap.neg_apply] at h1 h0
    exact ⟨by linarith, h1⟩

section PLPath

variable {S : Set E}

def IsPLPath {x y : S} (γ : Path x y) : Prop :=
  IsPiecewiseAffineOn (fun t : ℝ => ((γ.extend t : S) : E)) (Icc 0 1)

theorem IsPLPath.cast {x y x' y' : S} {γ : Path x y} (h : IsPLPath γ) (hx : x' = x)
    (hy : y' = y) : IsPLPath (γ.cast hx hy) :=
  h

theorem isPLPath_of_forall_eq {x y : S} (γ : Path x y) {z : E}
    (h : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ((γ.extend t : S) : E) = z) : IsPLPath γ :=
  (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.const ℝ ℝ z) isHPolytope_Icc).congr
    fun t ht => by rw [h t ht, AffineMap.const_apply]

def segmentPath (x y : S) (h : segment ℝ (x : E) y ⊆ S) : Path x y where
  toFun t := ⟨(1 - (t : ℝ)) • (x : E) + (t : ℝ) • (y : E),
    h ⟨1 - t, t, one_minus_nonneg t, nonneg t, sub_add_cancel 1 (t : ℝ), rfl⟩⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

theorem segmentPath_apply (x y : S) (h : segment ℝ (x : E) y ⊆ S) (t : I) :
    ((segmentPath x y h t : S) : E) = (1 - (t : ℝ)) • (x : E) + (t : ℝ) • (y : E) := rfl

theorem isPLPath_segmentPath (x y : S) (h : segment ℝ (x : E) y ⊆ S) :
    IsPLPath (segmentPath x y h) := by
  refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.lineMap (x : E) (y : E))
    isHPolytope_Icc).congr fun t ht => ?_
  rw [Path.extend_apply _ ht, segmentPath_apply, AffineMap.lineMap_apply_module]

theorem isPLPath_comp_affine {x y : S} {γ : Path x y} (h : IsPLPath γ) (A : ℝ →ᵃ[ℝ] ℝ)
    {a b : ℝ} (hab : A ⁻¹' Icc 0 1 = Icc a b) :
    IsPiecewiseAffineOn (fun t : ℝ => ((γ.extend (A t) : S) : E)) (Icc a b) := by
  have hcomp := h.comp (isPiecewiseAffineOn_of_affine A isOpen_univ)
  rw [univ_inter, hab] at hcomp
  exact hcomp.congr fun t _ => rfl

theorem IsPLPath.trans {x y z : S} {γ₁ : Path x y} {γ₂ : Path y z} (h₁ : IsPLPath γ₁)
    (h₂ : IsPLPath γ₂) : IsPLPath (γ₁.trans γ₂) := by
  have hl : IsPiecewiseAffineOn (fun t : ℝ => (((γ₁.trans γ₂).extend t : S) : E))
      (Icc 0 (1 / 2)) := by
    have hA : ∀ t : ℝ, AffineMap.lineMap (k := ℝ) (0 : ℝ) (2 : ℝ) t = 2 * t := fun t => by
      rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
      ring
    have hset : (AffineMap.lineMap (k := ℝ) (0 : ℝ) (2 : ℝ)) ⁻¹' Icc 0 1 = Icc 0 (1 / 2) := by
      ext t
      simp only [mem_preimage, mem_Icc, hA]
      constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
    refine (isPLPath_comp_affine h₁ _ hset).congr fun t ht => ?_
    change (((γ₁.trans γ₂).extend t : S) : E) = ((γ₁.extend (AffineMap.lineMap (k := ℝ) (0 : ℝ) 2 t)
        : S) : E)
    rw [hA, Path.extend_trans_of_le_half γ₁ γ₂ ht.2]
  have hr : IsPiecewiseAffineOn (fun t : ℝ => (((γ₁.trans γ₂).extend t : S) : E))
      (Icc (1 / 2) 1) := by
    have hA : ∀ t : ℝ, AffineMap.lineMap (k := ℝ) (-1 : ℝ) (1 : ℝ) t = 2 * t - 1 := fun t => by
      rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
      ring
    have hset : (AffineMap.lineMap (k := ℝ) (-1 : ℝ) (1 : ℝ)) ⁻¹' Icc 0 1 = Icc (1 / 2) 1 := by
      ext t
      simp only [mem_preimage, mem_Icc, hA]
      constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
    refine (isPLPath_comp_affine h₂ _ hset).congr fun t ht => ?_
    change (((γ₁.trans γ₂).extend t : S) : E) =
      ((γ₂.extend (AffineMap.lineMap (k := ℝ) (-1 : ℝ) 1 t) : S) : E)
    rw [hA, Path.extend_trans_of_half_le γ₁ γ₂ ht.1]
  have := hl.union_of_isClosed hr isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this

end PLPath

section Star

variable (K : Geometry.SimplicialComplex ℝ E)

theorem starConvex_closedStar {v : E} : StarConvex ℝ v (closedStar K v) :=
  starConvex_iUnion fun _ => starConvex_iUnion fun hs => (convex_convexHull ℝ _).starConvex hs.2

theorem mem_closedStar_of_singleton_mem {v : E} (hv : {v} ∈ K.faces) : v ∈ closedStar K v :=
  mem_biUnion (x := ({v} : Finset E))
    ⟨hv, subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v))⟩
    (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v)))

theorem segment_subset_closedStar {v z : E} (hz : z ∈ closedStar K v) :
    segment ℝ z v ⊆ closedStar K v := by
  obtain ⟨s, ⟨hs, hvs⟩, hzs⟩ := mem_iUnion₂.mp hz
  exact ((convex_convexHull ℝ _).segment_subset hzs hvs).trans fun w hw =>
    mem_biUnion (x := s) ⟨hs, hvs⟩ hw

theorem simplyConnectedSpace_closedStar {v : E} (hv : {v} ∈ K.faces) :
    SimplyConnectedSpace (closedStar K v) := by
  have : ContractibleSpace (closedStar K v) :=
    (starConvex_closedStar K).contractibleSpace ⟨v, mem_closedStar_of_singleton_mem K hv⟩
  infer_instance

theorem homotopic_of_forall_mem_closedStar {v : E} (hv : {v} ∈ K.faces) {x y : K.space}
    (α β : Path x y) (hα : ∀ t, (α t : E) ∈ closedStar K v)
    (hβ : ∀ t, (β t : E) ∈ closedStar K v) : α.Homotopic β := by
  have := simplyConnectedSpace_closedStar K hv
  have hαx : (x : E) ∈ closedStar K v := by simpa using hα 0
  have hαy : (y : E) ∈ closedStar K v := by simpa using hα 1
  let incl : C(closedStar K v, K.space) :=
    ⟨fun z => ⟨z, closedStar_subset_space K v z.2⟩, by fun_prop⟩
  let α' : Path (⟨x, hαx⟩ : closedStar K v) ⟨y, hαy⟩ :=
    { toFun := fun t => ⟨α t, hα t⟩
      continuous_toFun := (continuous_subtype_val.comp α.continuous).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  let β' : Path (⟨x, hαx⟩ : closedStar K v) ⟨y, hαy⟩ :=
    { toFun := fun t => ⟨β t, hβ t⟩
      continuous_toFun := (continuous_subtype_val.comp β.continuous).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  have h := (SimplyConnectedSpace.paths_homotopic α' β').map incl
  have e1 : α'.map incl.continuous = α := by
    ext t
    rfl
  have e2 : β'.map incl.continuous = β := by
    ext t
    rfl
  rw [e1, e2] at h
  exact h

end Star

section Truncate

variable {X : Type*} [TopologicalSpace X] {x y : X}

theorem truncateOfLE_apply (γ : Path x y) {a b : ℝ} (hab : a ≤ b) (s : I) :
    γ.truncateOfLE hab s = γ.extend (min (max s a) b) := rfl

theorem homotopic_truncateOfLE_trans (γ : Path x y) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) :
    ((γ.truncateOfLE hab).trans (γ.truncateOfLE hbc)).Homotopic
      (γ.truncateOfLE (hab.trans hbc)) := by
  let f : I → ℝ := fun s =>
    if (s : ℝ) ≤ 1 / 2 then min (max (2 * s) a) b else min (max (2 * s - 1) b) c
  let g : I → ℝ := fun s => min (max s a) c
  have hf : ∀ s : I, ((γ.truncateOfLE hab).trans (γ.truncateOfLE hbc)) s = γ.extend (f s) := by
    intro s
    rw [Path.trans_apply]
    simp only [f]
    split_ifs with h
    · rfl
    · rfl
  have hfcont : Continuous f := by
    refine Continuous.if_le
      (((continuous_const.mul continuous_subtype_val).max continuous_const).min continuous_const)
      ((((continuous_const.mul continuous_subtype_val).sub continuous_const).max
        continuous_const).min continuous_const)
      continuous_subtype_val continuous_const fun s hs => ?_
    have e1 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
    rw [hs, e1, sub_self, max_eq_left (by linarith), max_eq_right (by linarith),
      min_eq_right (by linarith), min_eq_left hbc]
  have hgcont : Continuous g :=
    (continuous_subtype_val.max continuous_const).min continuous_const
  have hf0 : f 0 = a := by
    simp only [f, Set.Icc.coe_zero, mul_zero, ite_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [max_eq_right ha, min_eq_left hab]
  have hf1 : f 1 = c := by
    simp only [f, Set.Icc.coe_one, mul_one, ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
    have e3 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [e3, max_eq_left (by linarith), min_eq_right hc]
  have hg0 : g 0 = a := by
    simp only [g, Set.Icc.coe_zero]
    rw [max_eq_right ha, min_eq_left (hab.trans hbc)]
  have hg1 : g 1 = c := by
    simp only [g, Set.Icc.coe_one]
    rw [max_eq_left (by linarith), min_eq_right hc]
  refine ⟨{ toFun := fun p => γ.extend ((1 - (p.1 : ℝ)) * f p.2 + (p.1 : ℝ) * g p.2)
            continuous_toFun := γ.continuous_extend.comp
              (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
                (hfcont.comp continuous_snd)).add
                ((continuous_subtype_val.comp continuous_fst).mul (hgcont.comp continuous_snd)))
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }⟩
  · change γ.extend ((1 - ((0 : I) : ℝ)) * f s + ((0 : I) : ℝ) * g s) = _
    rw [Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero, ← hf s]
    rfl
  · change γ.extend ((1 - ((1 : I) : ℝ)) * f s + ((1 : I) : ℝ) * g s) = _
    rw [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    rfl
  · rcases hs with rfl | rfl
    · change γ.extend ((1 - (t : ℝ)) * f 0 + (t : ℝ) * g 0) =
        ((γ.truncateOfLE hab).trans (γ.truncateOfLE hbc)) 0
      rw [hf 0, hf0, hg0]
      congr 1
      ring
    · change γ.extend ((1 - (t : ℝ)) * f 1 + (t : ℝ) * g 1) =
        ((γ.truncateOfLE hab).trans (γ.truncateOfLE hbc)) 1
      rw [hf 1, hf1, hg1]
      congr 1
      ring

end Truncate

section Main

theorem forall_mem_of_segmentPath {S : Set E} (x y : S) (h : segment ℝ (x : E) y ⊆ S) (t : I) :
    ((segmentPath x y h t : S) : E) ∈ segment ℝ (x : E) y :=
  ⟨1 - t, t, one_minus_nonneg t, nonneg t, sub_add_cancel 1 (t : ℝ), rfl⟩

omit [NormedSpace ℝ E] in
theorem forall_mem_trans {S : Set E} {x y z : S} (α : Path x y) (β : Path y z) {C : Set E}
    (hα : ∀ t, (α t : E) ∈ C) (hβ : ∀ t, (β t : E) ∈ C) (t : I) : ((α.trans β) t : E) ∈ C := by
  have hmem : (α.trans β) t ∈ range (α.trans β) := mem_range_self t
  rw [Path.trans_range] at hmem
  rcases hmem with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]
    exact hα u
  · rw [← hu]
    exact hβ u

variable (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]

theorem exists_isPLPath_homotopic {x y : K.space} (γ : Path x y) :
    ∃ γ' : Path x y, IsPLPath γ' ∧ γ.Homotopic γ' := by
  classical
  let U : {v // {v} ∈ K.faces} → Set I := fun v => γ ⁻¹' (Subtype.val ⁻¹' openStar K v)
  have hUopen : ∀ v, IsOpen (U v) := fun v =>
    (isOpen_preimage_openStar K v.1).preimage γ.continuous
  have hcover : (univ : Set I) ⊆ ⋃ v, U v := by
    intro t _
    obtain ⟨v, hv, hmem⟩ := exists_vertex_mem_openStar K (γ t).2
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, hmem⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hUopen hcover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N, hNpos, hNδ⟩ : ∃ N : ℕ, (0 : ℝ) < N ∧ 1 / (N : ℝ) < δ :=
    ⟨n + 1, by positivity, by push_cast; exact hn⟩
  have hti : ∀ i : ℕ, i ≤ N → (i : ℝ) / N ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨by positivity, by rw [div_le_one hNpos]; exact_mod_cast hi⟩
  have hsucc : ∀ i : ℕ, (i : ℝ) / N ≤ ((i + 1 : ℕ) : ℝ) / N := fun i => by
    apply div_le_div_of_nonneg_right _ hNpos.le
    push_cast
    linarith
  have hstar : ∀ i : ℕ, i < N → ∃ v, {v} ∈ K.faces ∧ ∀ t : ℝ,
      t ∈ Icc ((i : ℝ) / N) (((i + 1 : ℕ) : ℝ) / N) → (γ.extend t : E) ∈ openStar K v := by
    intro i hi
    obtain ⟨v, hv⟩ := hleb ⟨(i : ℝ) / N, hti i hi.le⟩ (mem_univ _)
    refine ⟨v.1, v.2, fun t ht => ?_⟩
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(hti i hi.le).1.trans ht.1, ht.2.trans (hti (i + 1) hi).2⟩
    have hball : (⟨t, ht01⟩ : I) ∈ Metric.ball (⟨(i : ℝ) / N, hti i hi.le⟩ : I) δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
      have hdiff : ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = 1 / N := by
        rw [← sub_div]
        push_cast
        ring
      linarith [ht.2]
    have hmem := hv hball
    rw [Path.extend_apply γ ht01]
    exact hmem
  choose! v hv hvstar using hstar
  have key : ∀ i : ℕ, ∀ hi : i ≤ N, ∃ β : Path (γ.extend 0) (γ.extend ((i : ℝ) / N)),
      IsPLPath β ∧ (γ.truncateOfLE (hti i hi).1).Homotopic β := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨γ.truncateOfLE (hti 0 hi).1, ?_, Path.Homotopic.refl _⟩
      refine isPLPath_of_forall_eq _ (z := (γ.extend 0 : E)) fun t ht => ?_
      rw [Path.extend_apply _ ht, truncateOfLE_apply]
      simp only [Nat.cast_zero, zero_div]
      rw [max_eq_left ht.1, min_eq_right ht.1]
    | succ i ih =>
      intro hi
      obtain ⟨β, hβpl, hβ⟩ := ih (Nat.le_of_succ_le hi)
      have hvi := hv i (Nat.lt_of_succ_le hi)
      have hvstari := hvstar i (Nat.lt_of_succ_le hi)
      have hwK : v i ∈ K.space := K.convexHull_subset_space hvi (subset_convexHull ℝ _ (by simp))
      have hclosed : ∀ t : ℝ, t ∈ Icc ((i : ℝ) / N) (((i + 1 : ℕ) : ℝ) / N) →
          (γ.extend t : E) ∈ closedStar K (v i) := fun t ht =>
        openStar_subset_closedStar K hvi (hvstari t ht)
      have hza : (γ.extend ((i : ℝ) / N) : E) ∈ closedStar K (v i) :=
        hclosed _ ⟨le_rfl, hsucc i⟩
      have hzb : (γ.extend (((i + 1 : ℕ) : ℝ) / N) : E) ∈ closedStar K (v i) :=
        hclosed _ ⟨hsucc i, le_rfl⟩
      have h₁ : segment ℝ ((γ.extend ((i : ℝ) / N) : K.space) : E) (v i) ⊆ K.space :=
        (segment_subset_closedStar K hza).trans (closedStar_subset_space K _)
      have h₂ : segment ℝ (v i) ((γ.extend (((i + 1 : ℕ) : ℝ) / N) : K.space) : E) ⊆ K.space := by
        rw [segment_symm]
        exact (segment_subset_closedStar K hzb).trans (closedStar_subset_space K _)
      let ρ : Path (γ.extend ((i : ℝ) / N)) (γ.extend (((i + 1 : ℕ) : ℝ) / N)) :=
        (segmentPath _ ⟨v i, hwK⟩ h₁).trans (segmentPath ⟨v i, hwK⟩ _ h₂)
      have hρpl : IsPLPath ρ := (isPLPath_segmentPath _ _ _).trans (isPLPath_segmentPath _ _ _)
      have hρ : ∀ t, (ρ t : E) ∈ closedStar K (v i) := by
        refine forall_mem_trans _ _ (fun t => ?_) fun t => ?_
        · exact segment_subset_closedStar K hza
            (forall_mem_of_segmentPath (γ.extend ((i : ℝ) / N)) ⟨v i, hwK⟩ h₁ t)
        · have hmem :=
            forall_mem_of_segmentPath ⟨v i, hwK⟩ (γ.extend (((i + 1 : ℕ) : ℝ) / N)) h₂ t
          rw [segment_symm] at hmem
          exact segment_subset_closedStar K hzb hmem
      have hτ : ∀ t, ((γ.truncateOfLE (hsucc i)) t : E) ∈ closedStar K (v i) := fun t => by
        rw [truncateOfLE_apply]
        refine hclosed _ ⟨?_, min_le_right _ _⟩
        exact le_min (le_max_right _ _) (hsucc i)
      have hτρ := homotopic_of_forall_mem_closedStar K hvi _ ρ hτ hρ
      have hsplit := homotopic_truncateOfLE_trans γ le_rfl (hti i (Nat.le_of_succ_le hi)).1
        (hsucc i) (hti (i + 1) hi).2
      refine ⟨β.trans ρ, hβpl.trans hρpl, ?_⟩
      exact hsplit.symm.trans (Path.Homotopic.hcomp hβ hτρ)
  obtain ⟨β, hβpl, hβ⟩ := key N le_rfl
  have hx : x = γ.extend 0 := γ.extend_zero.symm
  have hy : y = γ.extend ((N : ℝ) / N) := by
    rw [div_self hNpos.ne', γ.extend_one]
  refine ⟨β.cast hx hy, hβpl.cast hx hy, ?_⟩
  have hγ : (γ.truncateOfLE (hti N le_rfl).1).cast hx hy = γ := by
    ext t
    rw [Path.cast_coe, truncateOfLE_apply, div_self hNpos.ne', max_eq_left (nonneg t),
      min_eq_left (le_one t), γ.extend_extends' t]
  have h2 := hβ.pathCast hx hy
  rw [hγ] at h2
  exact h2

end Main

end DifferentialGeometry.Topology.PiecewiseLinear
