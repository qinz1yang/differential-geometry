import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedOriginalMap
import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockModel
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneData

/-!
# BCG03: the augmented reference-model table and its derivative image (lane BAUG-C, G1)

Blueprint 207B, BCG03 (`B:8960–9131`: "planes follow CFS27 on interior blocks and retain all
boundary blocks"); external draft 61 §1.4, §2.1, §2.5; dispositions D61-4, D61-5, D61-6. The
augmented target is `H^∂ = H_int ⊕ ⊕_b ℝ²_b = BlockSpace (ι ⊕ κ ↦ ℝ²)` in the `planeAxis`
encoding of BAUG-A (`boundaryAugmentedMap_BAUGA`). For a reference `a` with interior model
`Φ_a : E → H_int` (the active-family formula), interior pruning `K_a`, whole boundary list
`J_∂(a)` and the (BM) blocks `Φ^∂_{a,b} = R_a⁻¹𝓑(h_{a,b})` (`boundaryModel_BCG8b`):

* the continuous linear maps `pr_int` (`augIntProjCLM_BAUGC`), `ι_int` (`augIntInclCLM_BAUGC`)
  and the slot inclusions `augSlotCLM_BAUGC b`;
* the augmented pruning `K^∂ = ι_int K pr_int + (id − ι_int pr_int)` (`augmentedPrune_BAUGC`):
  `K^∂|_{H_∂} = id` (`augmentedPrune_apply_inr_BAUGC`, `augmentedPrune_slot_BAUGC`,
  `augmentedPrune_eq_self_of_proj_eq_zero_BAUGC`) — it keeps the WHOLE boundary part;
* the augmented model `Φ^∂_a = (Φ_a, (b ∈ J_∂(a) ? Φ^∂_{a,b} : 0)_b)` (`augmentedModel_BAUGC`,
  unlisted boundary blocks identically zero), its slot decomposition
  (`augmentedModel_eq_sum_BAUGC`) and `K^∂ ∘ Φ^∂ = Φ^∂[K ∘ Φ]` (`augmentedPrune_comp_model_BAUGC`);
* the derivative (`hasFDerivAt_augmentedModel_BAUGC`): `D Φ^∂ = ι_int DΦ + Σ_b slot_b DΦ^∂_{a,b}`
  (listed `b` only), hence for the plane `(P)` `L = im D(K^∂Φ^∂)(η(q))`:
  `pr_int ∘ D = D(KΦ)` (`augIntProj_comp_augDeriv_BAUGC`), slot `b` of `D w` is
  `planeBlockEmbed (DΦ^∂_{a,b} w)` or `0` (`augDeriv_apply_inr_BAUGC`);
* the boundary slot bound `‖(D(K^∂Φ^∂)(z) w)_b‖ ≤ 2P_*‖w‖` for a (BM) block with `‖A‖ ≤ 1`
  (`norm_augDeriv_inr_le_BAUGC`): the possibly large marker `R_a⁻¹` never enters;
* the degenerate case `J_∂(a) = ∅` (`augmentedModel_empty_BAUGC`,
  `range_augDeriv_empty_BAUGC`): the augmented model is `ι_int ∘ Φ` and the plane is
  `ι_int(L_int)` — the closed shape;
* norms: `norm_sq_eq_proj_add_slots_BAUGC`, `norm_le_proj_add_slot_BAUGC`,
  `norm_augIntProj_le_BAUGC`, `norm_augIntIncl_BAUGC`, `norm_augSlotCLM_apply_le_BAUGC`;
* consumer `bm_augmented_plane_BAUGC`: the plane map of the augmented (BM) model at a point, with
  BCG.0's `P_*` — interior part exact, boundary slots `≤ 2P_*‖w‖`, unlisted slots zero.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section CLM

variable {ι κ : Type*}

/-- `pr_{H_int}` as a continuous linear map. -/
def augIntProjCLM_BAUGC :
    BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²) :=
  ((PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => WithLp 2 (ℝ² × ℝ)).symm :
      (ι → WithLp 2 (ℝ² × ℝ)) →L[ℝ] BlockSpace (fun _ : ι => ℝ²)).comp
    ((ContinuousLinearMap.pi fun i : ι =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ))
          (Sum.inl i)).comp
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ) :
        BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] (ι ⊕ κ → WithLp 2 (ℝ² × ℝ))))

theorem augIntProjCLM_apply_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (i : ι) :
    augIntProjCLM_BAUGC x i = x (Sum.inl i) :=
  rfl

theorem augIntProjCLM_eq_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    augIntProjCLM_BAUGC x = augmentedInteriorProj_BAUGA x :=
  rfl

/-- `ι_int` as a continuous linear map. -/
def augIntInclCLM_BAUGC :
    BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
  ((PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)).symm :
      (ι ⊕ κ → WithLp 2 (ℝ² × ℝ)) →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)).comp
    ((ContinuousLinearMap.pi (φ := fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)) (Sum.elim
        (fun i : ι => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => WithLp 2 (ℝ² × ℝ)) i)
        (fun _ : κ => (0 : (ι → WithLp 2 (ℝ² × ℝ)) →L[ℝ] WithLp 2 (ℝ² × ℝ))))).comp
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => WithLp 2 (ℝ² × ℝ) :
        BlockSpace (fun _ : ι => ℝ²) →L[ℝ] (ι → WithLp 2 (ℝ² × ℝ))))

theorem augIntInclCLM_apply_inl_BAUGC (y : BlockSpace (fun _ : ι => ℝ²)) (i : ι) :
    (augIntInclCLM_BAUGC (κ := κ) y) (Sum.inl i) = y i :=
  rfl

theorem augIntInclCLM_apply_inr_BAUGC (y : BlockSpace (fun _ : ι => ℝ²)) (b : κ) :
    (augIntInclCLM_BAUGC (κ := κ) y) (Sum.inr b) = 0 :=
  rfl

theorem augIntInclCLM_eq_BAUGC (y : BlockSpace (fun _ : ι => ℝ²)) :
    augIntInclCLM_BAUGC (κ := κ) y = augmentedInteriorIncl_BAUGA y :=
  PiLp.ext fun t => by rcases t with i | b <;> rfl

theorem augIntProj_incl_BAUGC (y : BlockSpace (fun _ : ι => ℝ²)) :
    augIntProjCLM_BAUGC (augIntInclCLM_BAUGC (κ := κ) y) = y :=
  rfl

/-- `ι_int` is injective. -/
theorem augIntInclCLM_injective_BAUGC :
    Function.Injective (augIntInclCLM_BAUGC (ι := ι) (κ := κ)) := fun y y' h => by
  have := congrArg augIntProjCLM_BAUGC h
  rwa [augIntProj_incl_BAUGC, augIntProj_incl_BAUGC] at this

variable [DecidableEq κ]

/-- The slot inclusion of the boundary component `b`: `B ↦` the block-space vector whose slot `b`
is the plane encoding of `B`, every other slot zero. -/
def augSlotCLM_BAUGC (b : κ) : ℝ × ℝ →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
  ((PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)).symm :
      (ι ⊕ κ → WithLp 2 (ℝ² × ℝ)) →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)).comp
    (ContinuousLinearMap.pi (φ := fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)) (Sum.elim
      (fun _ : ι => (0 : ℝ × ℝ →L[ℝ] WithLp 2 (ℝ² × ℝ)))
      (fun b' : κ => if b' = b then planeBlockEmbed_BAUGA else 0)))

theorem augSlotCLM_apply_inl_BAUGC (b : κ) (B : ℝ × ℝ) (i : ι) :
    augSlotCLM_BAUGC (ι := ι) b B (Sum.inl i) = 0 :=
  rfl

theorem augSlotCLM_apply_inr_BAUGC (b b' : κ) (B : ℝ × ℝ) :
    augSlotCLM_BAUGC (ι := ι) b B (Sum.inr b') =
      if b' = b then planeBlockEmbed_BAUGA B else 0 := by
  change (if b' = b then planeBlockEmbed_BAUGA else 0) B = _
  split_ifs <;> rfl

theorem augSlotCLM_apply_self_BAUGC (b : κ) (B : ℝ × ℝ) :
    augSlotCLM_BAUGC (ι := ι) b B (Sum.inr b) = planeBlockEmbed_BAUGA B := by
  rw [augSlotCLM_apply_inr_BAUGC, ite_eq_left rfl]

theorem augSlotCLM_apply_ne_BAUGC {b b' : κ} (h : b' ≠ b) (B : ℝ × ℝ) :
    augSlotCLM_BAUGC (ι := ι) b B (Sum.inr b') = 0 := by
  rw [augSlotCLM_apply_inr_BAUGC, ite_eq_right h]

theorem augIntProj_slot_BAUGC (b : κ) (B : ℝ × ℝ) :
    augIntProjCLM_BAUGC (augSlotCLM_BAUGC (ι := ι) b B) = 0 :=
  rfl

end CLM

section SumApply

variable {ι κ : Type*} {α : Type*}

/-- A finite sum in the block space is computed slot by slot. -/
theorem blockSpace_sum_apply_BAUGC (s : Finset α) (f : α → BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (t : ι ⊕ κ) : (∑ a ∈ s, f a) t = ∑ a ∈ s, f a t :=
  map_sum (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)) t) f s

end SumApply

section Norms

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The plane encoding at most doubles the (sup) norm of `ℝ × ℝ`. -/
theorem norm_planeBlockEmbed_le_BAUGC (B : ℝ × ℝ) : ‖planeBlockEmbed_BAUGA B‖ ≤ 2 * ‖B‖ := by
  have h1 : ‖planeBlockEmbed_BAUGA B‖ ^ 2 = |B.1| ^ 2 + |B.2| ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, planeBlockEmbed_fst_BAUGA, planeBlockEmbed_snd_BAUGA,
      norm_planeAxis, Real.norm_eq_abs]
  have h2 : |B.1| ≤ ‖B‖ := by
    have := norm_fst_le B
    rwa [Real.norm_eq_abs] at this
  have h3 : |B.2| ≤ ‖B‖ := by
    have := norm_snd_le B
    rwa [Real.norm_eq_abs] at this
  have h4 : ‖planeBlockEmbed_BAUGA B‖ ^ 2 ≤ (2 * ‖B‖) ^ 2 := by
    rw [h1]
    nlinarith [abs_nonneg B.1, abs_nonneg B.2, norm_nonneg B]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

omit [DecidableEq κ] in
/-- A block-space vector with a single nonzero slot has the norm of that slot. -/
theorem norm_eq_of_single_slot_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (t₀ : ι ⊕ κ)
    (h : ∀ t, t ≠ t₀ → x t = 0) : ‖x‖ = ‖x t₀‖ := by
  rw [PiLp.norm_eq_of_L2, Finset.sum_eq_single t₀ (fun t _ ht => by rw [h t ht, norm_zero]; ring)
    (fun h0 => absurd (Finset.mem_univ t₀) h0), Real.sqrt_sq (norm_nonneg _)]

/-- `‖slot_b B‖ ≤ 2‖B‖`. -/
theorem norm_augSlotCLM_apply_le_BAUGC (b : κ) (B : ℝ × ℝ) :
    ‖augSlotCLM_BAUGC (ι := ι) b B‖ ≤ 2 * ‖B‖ := by
  rw [norm_eq_of_single_slot_BAUGC _ (Sum.inr b) fun t ht => ?_, augSlotCLM_apply_self_BAUGC]
  · exact norm_planeBlockEmbed_le_BAUGC B
  · rcases t with i | b'
    · rfl
    · exact augSlotCLM_apply_ne_BAUGC (fun hb => ht (by rw [hb])) B

omit [DecidableEq κ] in
/-- `‖x‖² = ‖pr_int x‖² + Σ_b ‖x_b‖²`. -/
theorem norm_sq_eq_proj_add_slots_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    ‖x‖ ^ 2 = ‖augIntProjCLM_BAUGC x‖ ^ 2 + ∑ b, ‖x (Sum.inr b)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  rfl

omit [DecidableEq κ] in
/-- With at most one nonzero boundary slot `b₀`: `‖x‖ ≤ ‖pr_int x‖ + ‖x_{b₀}‖`. -/
theorem norm_le_proj_add_slot_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b₀ : κ)
    (h : ∀ b, b ≠ b₀ → x (Sum.inr b) = 0) :
    ‖x‖ ≤ ‖augIntProjCLM_BAUGC x‖ + ‖x (Sum.inr b₀)‖ := by
  have hs : ∑ b, ‖x (Sum.inr b)‖ ^ 2 = ‖x (Sum.inr b₀)‖ ^ 2 :=
    Finset.sum_eq_single b₀ (fun b _ hb => by rw [h b hb, norm_zero]; ring)
      (fun h0 => absurd (Finset.mem_univ b₀) h0)
  have hsq : ‖x‖ ^ 2 ≤ (‖augIntProjCLM_BAUGC x‖ + ‖x (Sum.inr b₀)‖) ^ 2 := by
    rw [norm_sq_eq_proj_add_slots_BAUGC, hs]
    nlinarith [norm_nonneg (augIntProjCLM_BAUGC x), norm_nonneg (x (Sum.inr b₀))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

omit [DecidableEq κ] in
/-- With every boundary slot zero: `‖x‖ = ‖pr_int x‖`. -/
theorem norm_eq_proj_of_slots_zero_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (h : ∀ b, x (Sum.inr b) = 0) : ‖x‖ = ‖augIntProjCLM_BAUGC x‖ := by
  have hsq : ‖x‖ ^ 2 = ‖augIntProjCLM_BAUGC x‖ ^ 2 := by
    rw [norm_sq_eq_proj_add_slots_BAUGC, Finset.sum_eq_zero fun b _ => by rw [h b, norm_zero]; ring,
      add_zero]
  rw [← Real.sqrt_sq (norm_nonneg x), hsq, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq κ] in
/-- `pr_int` is `1`-Lipschitz: `‖pr_int x‖ ≤ ‖x‖`. -/
theorem norm_augIntProj_le_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    ‖augIntProjCLM_BAUGC x‖ ≤ ‖x‖ := by
  have hsq : ‖augIntProjCLM_BAUGC x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq_proj_add_slots_BAUGC]
    have : 0 ≤ ∑ b, ‖x (Sum.inr b)‖ ^ 2 := Finset.sum_nonneg fun b _ => sq_nonneg _
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

omit [DecidableEq κ] in
/-- `ι_int` is an isometry: `‖ι_int y‖ = ‖y‖`. -/
theorem norm_augIntIncl_BAUGC (y : BlockSpace (fun _ : ι => ℝ²)) :
    ‖augIntInclCLM_BAUGC (κ := κ) y‖ = ‖y‖ :=
  (norm_eq_proj_of_slots_zero_BAUGC _ fun b => augIntInclCLM_apply_inr_BAUGC y b).trans
    (by rw [augIntProj_incl_BAUGC])

end Norms

section Prune

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The augmented pruning** `K^∂ = ι_int K pr_int + (id − ι_int pr_int)`: CFS27's pruning on the
interior blocks, the identity on the WHOLE boundary part `H_∂` (draft 61 §2.1, D61-4). -/
def augmentedPrune_BAUGC
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²)) :
    BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
  augIntInclCLM_BAUGC.comp (Kint.comp augIntProjCLM_BAUGC) +
    (ContinuousLinearMap.id ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²)) -
      augIntInclCLM_BAUGC.comp augIntProjCLM_BAUGC)

variable (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))

theorem augmentedPrune_apply_inl_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (i : ι) :
    augmentedPrune_BAUGC Kint x (Sum.inl i) = Kint (augIntProjCLM_BAUGC x) i := by
  change Kint (augIntProjCLM_BAUGC x) i + (x (Sum.inl i) - x (Sum.inl i)) = _
  rw [sub_self, add_zero]

/-- **`K^∂|_{H_∂} = id`, slotwise**: every boundary slot is kept. -/
theorem augmentedPrune_apply_inr_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) :
    augmentedPrune_BAUGC Kint x (Sum.inr b) = x (Sum.inr b) := by
  change (0 : WithLp 2 (ℝ² × ℝ)) + (x (Sum.inr b) - 0) = _
  rw [sub_zero, zero_add]

theorem augIntProj_augmentedPrune_BAUGC (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    augIntProjCLM_BAUGC (augmentedPrune_BAUGC Kint x) = Kint (augIntProjCLM_BAUGC x) :=
  PiLp.ext fun i => augmentedPrune_apply_inl_BAUGC Kint x i

/-- **`K^∂|_{H_∂} = id`**: a vector of `H_∂ = ker pr_int` is fixed by the augmented pruning. -/
theorem augmentedPrune_eq_self_of_proj_eq_zero_BAUGC {x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)}
    (hx : augIntProjCLM_BAUGC x = 0) : augmentedPrune_BAUGC Kint x = x := by
  refine PiLp.ext fun t => ?_
  rcases t with i | b
  · rw [augmentedPrune_apply_inl_BAUGC, hx, map_zero]
    have := congrArg (fun y : BlockSpace (fun _ : ι => ℝ²) => y i) hx
    exact this.symm
  · exact augmentedPrune_apply_inr_BAUGC Kint x b

theorem augmentedPrune_incl_BAUGC (y : BlockSpace (fun _ : ι => ℝ²)) :
    augmentedPrune_BAUGC (κ := κ) Kint (augIntInclCLM_BAUGC y) =
      augIntInclCLM_BAUGC (Kint y) :=
  PiLp.ext fun t => by
    rcases t with i | b
    · rw [augmentedPrune_apply_inl_BAUGC, augIntProj_incl_BAUGC]
      rfl
    · rw [augmentedPrune_apply_inr_BAUGC]
      rfl

theorem augmentedPrune_slot_BAUGC [DecidableEq κ] (b : κ) (B : ℝ × ℝ) :
    augmentedPrune_BAUGC Kint (augSlotCLM_BAUGC (ι := ι) b B) = augSlotCLM_BAUGC b B :=
  augmentedPrune_eq_self_of_proj_eq_zero_BAUGC Kint (augIntProj_slot_BAUGC b B)

/-- The pruning acts on an augmented map through its interior part only. -/
theorem augmentedPrune_boundaryAugmentedMap_BAUGC {M : Type*}
    (Fint : M → BlockSpace (fun _ : ι => ℝ²)) (B : κ → M → ℝ × ℝ) (p : M) :
    augmentedPrune_BAUGC Kint (boundaryAugmentedMap_BAUGA Fint B p) =
      boundaryAugmentedMap_BAUGA (fun q => Kint (Fint q)) B p :=
  PiLp.ext fun t => by
    rcases t with i | b
    · rw [augmentedPrune_apply_inl_BAUGC]
      rfl
    · rw [augmentedPrune_apply_inr_BAUGC]
      rfl

end Prune

section Model

variable {ι κ E : Type*}

open Classical in
/-- The boundary blocks of a reference: the given block if `b` is listed, zero otherwise. -/
def augmentedBlocks_BAUGC (J : Set κ) (Φb : κ → E → ℝ × ℝ) (b : κ) (z : E) : ℝ × ℝ :=
  if b ∈ J then Φb b z else 0

theorem augmentedBlocks_of_mem_BAUGC {J : Set κ} (Φb : κ → E → ℝ × ℝ) {b : κ} (hb : b ∈ J) :
    augmentedBlocks_BAUGC J Φb b = Φb b :=
  funext fun _ => by rw [augmentedBlocks_BAUGC, ite_eq_left hb]

theorem augmentedBlocks_of_notMem_BAUGC {J : Set κ} (Φb : κ → E → ℝ × ℝ) {b : κ}
    (hb : b ∉ J) : augmentedBlocks_BAUGC J Φb b = 0 :=
  funext fun _ => by rw [augmentedBlocks_BAUGC, ite_eq_right hb]; rfl

/-- **The augmented reference model** (draft 61 §2.5, D61-5): the interior model `Φ_a` on the
interior slots, the (BM) block of every LISTED boundary component, zero on unlisted ones. -/
def augmentedModel_BAUGC (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ)
    (Φb : κ → E → ℝ × ℝ) : E → BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
  boundaryAugmentedMap_BAUGA Φint (augmentedBlocks_BAUGC J Φb)

theorem augmentedModel_apply_inl_BAUGC (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ)
    (Φb : κ → E → ℝ × ℝ) (z : E) (i : ι) :
    augmentedModel_BAUGC Φint J Φb z (Sum.inl i) = Φint z i :=
  rfl

theorem augmentedModel_apply_inr_BAUGC (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ)
    (Φb : κ → E → ℝ × ℝ) (z : E) (b : κ) :
    augmentedModel_BAUGC Φint J Φb z (Sum.inr b) =
      planeBlockEmbed_BAUGA (augmentedBlocks_BAUGC J Φb b z) :=
  rfl

theorem augIntProj_augmentedModel_BAUGC (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ)
    (Φb : κ → E → ℝ × ℝ) (z : E) :
    augIntProjCLM_BAUGC (augmentedModel_BAUGC Φint J Φb z) = Φint z :=
  rfl

variable [Fintype ι] [Fintype κ]

/-- `K^∂ ∘ Φ^∂ = Φ^∂[K ∘ Φ]`: the augmented pruned model is the augmented model of the pruned
interior model, with the SAME boundary blocks. -/
theorem augmentedPrune_comp_model_BAUGC
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ) (Φb : κ → E → ℝ × ℝ) :
    augmentedPrune_BAUGC Kint ∘ augmentedModel_BAUGC Φint J Φb =
      augmentedModel_BAUGC (Kint ∘ Φint) J Φb :=
  funext fun z => augmentedPrune_boundaryAugmentedMap_BAUGC Kint Φint _ z

variable [DecidableEq κ]

omit [Fintype ι] in
/-- **Slot decomposition**: `Φ^∂ = ι_int Φ + Σ_b slot_b(block_b)`. -/
theorem augmentedModel_eq_sum_BAUGC (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ)
    (Φb : κ → E → ℝ × ℝ) (z : E) :
    augmentedModel_BAUGC Φint J Φb z = augIntInclCLM_BAUGC (Φint z) +
      ∑ b, augSlotCLM_BAUGC b (augmentedBlocks_BAUGC J Φb b z) := by
  refine PiLp.ext fun t => ?_
  rw [PiLp.add_apply, blockSpace_sum_apply_BAUGC]
  rcases t with i | b
  · rw [augmentedModel_apply_inl_BAUGC, augIntInclCLM_apply_inl_BAUGC,
      Finset.sum_eq_zero fun b _ => augSlotCLM_apply_inl_BAUGC b _ i, add_zero]
  · rw [augmentedModel_apply_inr_BAUGC, augIntInclCLM_apply_inr_BAUGC, zero_add,
      Finset.sum_eq_single b (fun b' _ hb' => augSlotCLM_apply_ne_BAUGC (Ne.symm hb') _)
        (fun h0 => absurd (Finset.mem_univ b) h0), augSlotCLM_apply_self_BAUGC]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The (BM) blocks `Φ^∂_{a,b} = R⁻¹𝓑(c_b + R A_b(z − z₀))` of one reference. -/
def bmBlocks_BAUGC (c : κ → ℝ) (R : ℝ) (A : κ → E →L[ℝ] ℝ) (z₀ : E) : κ → E → ℝ × ℝ :=
  fun b => boundaryModel_BCG8b (c b) R (A b) z₀

open Classical in
/-- The derivative of the boundary blocks: `DΦ^∂_{a,b}` on listed `b`, zero otherwise. -/
def augmentedBlockDeriv_BAUGC (J : Set κ) (Db : κ → E →L[ℝ] ℝ × ℝ) (b : κ) : E →L[ℝ] ℝ × ℝ :=
  if b ∈ J then Db b else 0

/-- The derivative of the augmented model: `ι_int ∘ T_int + Σ_b slot_b ∘ T_b`. -/
def augDeriv_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²)) (Tb : κ → E →L[ℝ] ℝ × ℝ) :
    E →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
  augIntInclCLM_BAUGC (κ := κ).comp Tint + ∑ b, (augSlotCLM_BAUGC (ι := ι) b).comp (Tb b)

theorem augDeriv_apply_inl_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Tb : κ → E →L[ℝ] ℝ × ℝ) (w : E) (i : ι) :
    augDeriv_BAUGC Tint Tb w (Sum.inl i) = Tint w i := by
  rw [augDeriv_BAUGC, add_apply, PiLp.add_apply,
    sum_apply, blockSpace_sum_apply_BAUGC]
  rw [Finset.sum_eq_zero fun b _ => by
    rw [ContinuousLinearMap.comp_apply]; exact augSlotCLM_apply_inl_BAUGC b _ i, add_zero]
  rfl

/-- Slot `b` of the derivative is the plane encoding of `T_b`. -/
theorem augDeriv_apply_inr_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Tb : κ → E →L[ℝ] ℝ × ℝ) (w : E) (b : κ) :
    augDeriv_BAUGC Tint Tb w (Sum.inr b) = planeBlockEmbed_BAUGA (Tb b w) := by
  rw [augDeriv_BAUGC, add_apply, PiLp.add_apply,
    sum_apply, blockSpace_sum_apply_BAUGC,
    Finset.sum_eq_single b (fun b' _ hb' => by
      rw [ContinuousLinearMap.comp_apply]; exact augSlotCLM_apply_ne_BAUGC (Ne.symm hb') _)
      (fun h0 => absurd (Finset.mem_univ b) h0)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [augSlotCLM_apply_self_BAUGC]
  change (0 : WithLp 2 (ℝ² × ℝ)) + _ = _
  rw [zero_add]

/-- **`pr_int ∘ D = T_int`**: the interior part of the augmented derivative is the interior one. -/
theorem augIntProj_comp_augDeriv_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Tb : κ → E →L[ℝ] ℝ × ℝ) : augIntProjCLM_BAUGC.comp (augDeriv_BAUGC Tint Tb) = Tint :=
  ContinuousLinearMap.ext fun w => PiLp.ext fun i => augDeriv_apply_inl_BAUGC Tint Tb w i

/-- **The derivative of the augmented model** (`D Φ^∂ = ι_int DΦ + Σ_{b listed} slot_b DΦ^∂_b`). -/
theorem hasFDerivAt_augmentedModel_BAUGC {Φint : E → BlockSpace (fun _ : ι => ℝ²)} {J : Set κ}
    {Φb : κ → E → ℝ × ℝ} {z : E} {Dint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²)}
    (hint : HasFDerivAt Φint Dint z) {Db : κ → E →L[ℝ] ℝ × ℝ}
    (hb : ∀ b ∈ J, HasFDerivAt (Φb b) (Db b) z) :
    HasFDerivAt (augmentedModel_BAUGC Φint J Φb)
      (augDeriv_BAUGC Dint (augmentedBlockDeriv_BAUGC J Db)) z := by
  have hblock : ∀ b, HasFDerivAt (augmentedBlocks_BAUGC J Φb b)
      (augmentedBlockDeriv_BAUGC J Db b) z := by
    intro b
    by_cases hbJ : b ∈ J
    · rw [augmentedBlocks_of_mem_BAUGC Φb hbJ, augmentedBlockDeriv_BAUGC, ite_eq_left hbJ]
      exact hb b hbJ
    · rw [augmentedBlocks_of_notMem_BAUGC Φb hbJ, augmentedBlockDeriv_BAUGC, ite_eq_right hbJ]
      exact hasFDerivAt_const (0 : ℝ × ℝ) z
  have he : augmentedModel_BAUGC Φint J Φb = fun z => augIntInclCLM_BAUGC (Φint z) +
      ∑ b, augSlotCLM_BAUGC b (augmentedBlocks_BAUGC J Φb b z) :=
    funext (augmentedModel_eq_sum_BAUGC Φint J Φb)
  rw [he]
  exact (augIntInclCLM_BAUGC.hasFDerivAt.comp z hint).add
    (HasFDerivAt.fun_sum fun b _ => (augSlotCLM_BAUGC b).hasFDerivAt.comp z (hblock b))

/-- **The augmented pruned derivative** at a point where the pruned interior model and every
listed (BM) block are differentiable. -/
theorem fderiv_augmented_pruned_BAUGC
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    {Φint : E → BlockSpace (fun _ : ι => ℝ²)} {J : Set κ} {Φb : κ → E → ℝ × ℝ} {z : E}
    (hint : DifferentiableAt ℝ (Kint ∘ Φint) z) (hb : ∀ b ∈ J, DifferentiableAt ℝ (Φb b) z) :
    fderiv ℝ (augmentedPrune_BAUGC Kint ∘ augmentedModel_BAUGC Φint J Φb) z =
      augDeriv_BAUGC (fderiv ℝ (Kint ∘ Φint) z)
        (augmentedBlockDeriv_BAUGC J fun b => fderiv ℝ (Φb b) z) := by
  rw [augmentedPrune_comp_model_BAUGC]
  exact (hasFDerivAt_augmentedModel_BAUGC hint.hasFDerivAt
    fun b hbJ => (hb b hbJ).hasFDerivAt).fderiv

/-- **The (BM) slot bound**: for (BM) blocks with `R ≠ 0` and rows `‖A_b‖ ≤ 1`, every boundary slot
of the augmented derivative has `‖(D w)_b‖ ≤ 2P_*‖w‖` (zero on unlisted `b`); the marker `R⁻¹`
of the model never enters. -/
theorem norm_augDeriv_inr_le_BAUGC {P : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P)
    (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²)) (J : Set κ) (c : κ → ℝ) {R : ℝ} (hR : R ≠ 0)
    {A : κ → E →L[ℝ] ℝ} (hA : ∀ b ∈ J, ‖A b‖ ≤ 1) (z₀ z w : E) (b : κ) :
    ‖augDeriv_BAUGC Tint (augmentedBlockDeriv_BAUGC J fun b =>
        fderiv ℝ (bmBlocks_BAUGC c R A z₀ b) z) w (Sum.inr b)‖ ≤ 2 * P * ‖w‖ := by
  rw [augDeriv_apply_inr_BAUGC]
  have hP0 := nonneg_of_boundaryBlock_bound_BCG8b hP
  by_cases hbJ : b ∈ J
  · rw [augmentedBlockDeriv_BAUGC, ite_eq_left hbJ]
    refine (norm_planeBlockEmbed_le_BAUGC _).trans ?_
    have h1 := (fderiv ℝ (bmBlocks_BAUGC c R A z₀ b) z).le_opNorm w
    have h2 : ‖fderiv ℝ (bmBlocks_BAUGC c R A z₀ b) z‖ ≤ P :=
      norm_fderiv_boundaryModel_le_BCG8b hP (c b) hR (hA b hbJ) z₀ z
    have h3 : ‖fderiv ℝ (bmBlocks_BAUGC c R A z₀ b) z‖ * ‖w‖ ≤ P * ‖w‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
    linarith
  · rw [augmentedBlockDeriv_BAUGC, ite_eq_right hbJ, zero_apply, map_zero,
      norm_zero]
    positivity

omit [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **The degenerate case `J_∂(a) = ∅`**: the augmented model is `ι_int ∘ Φ` (the closed shape). -/
theorem augmentedModel_empty_BAUGC (Φint : E → BlockSpace (fun _ : ι => ℝ²))
    (Φb : κ → E → ℝ × ℝ) :
    augmentedModel_BAUGC Φint ∅ Φb = augIntInclCLM_BAUGC ∘ Φint :=
  funext fun z => by
    rw [augmentedModel_eq_sum_BAUGC,
      Finset.sum_eq_zero fun b _ => by
        rw [augmentedBlocks_of_notMem_BAUGC Φb (Set.notMem_empty b)]
        exact map_zero _,
      add_zero]
    rfl

/-- **The degenerate plane**: with `J_∂(a) = ∅` the augmented plane is `ι_int(L_int)`. -/
theorem range_augDeriv_empty_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Db : κ → E →L[ℝ] ℝ × ℝ) :
    LinearMap.range (augDeriv_BAUGC Tint (augmentedBlockDeriv_BAUGC ∅ Db) :
        E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) =
      (LinearMap.range (Tint : E →ₗ[ℝ] BlockSpace (fun _ : ι => ℝ²))).map
        (augIntInclCLM_BAUGC (κ := κ)).toLinearMap := by
  have he : augDeriv_BAUGC Tint (augmentedBlockDeriv_BAUGC ∅ Db) =
      augIntInclCLM_BAUGC.comp Tint := by
    rw [augDeriv_BAUGC, Finset.sum_eq_zero fun b _ => by
      rw [augmentedBlockDeriv_BAUGC, ite_eq_right (Set.notMem_empty b)]
      exact ContinuousLinearMap.comp_zero _, add_zero]
  rw [he]
  exact LinearMap.range_comp (Tint : E →ₗ[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (augIntInclCLM_BAUGC (κ := κ)).toLinearMap

omit [Fintype κ] [DecidableEq κ] in
/-- The (BM) blocks are differentiable everywhere (`R ≠ 0`). -/
theorem differentiableAt_bmBlocks_BAUGC (c : κ → ℝ) {R : ℝ} (hR : R ≠ 0) (A : κ → E →L[ℝ] ℝ)
    (z₀ z : E) (b : κ) : DifferentiableAt ℝ (bmBlocks_BAUGC c R A z₀ b) z :=
  (hasFDerivAt_boundaryModel_BCG8b (c b) hR (A b) z₀ z).differentiableAt

/-- **Consumer: the plane of the augmented (BM) model** (draft 61 (P) with D61-5). For a pruned
interior model differentiable at `z`, (BM) blocks with `R > 0` and rows `‖A_b‖ ≤ 1` on the list,
and BCG.0's constant `P_*`: the interior part of `D(K^∂Φ^∂)(z)` is exactly `D(KΦ)(z)`, every
boundary slot is bounded by `2P_*‖w‖`, and unlisted slots vanish. -/
theorem bm_augmented_plane_BAUGC {P : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P)
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    {Φint : E → BlockSpace (fun _ : ι => ℝ²)} (J : Set κ) (c : κ → ℝ) {R : ℝ} (hR : 0 < R)
    {A : κ → E →L[ℝ] ℝ} (hA : ∀ b ∈ J, ‖A b‖ ≤ 1) (z₀ : E) {z : E}
    (hint : DifferentiableAt ℝ (Kint ∘ Φint) z) :
    augIntProjCLM_BAUGC.comp
        (fderiv ℝ (augmentedPrune_BAUGC Kint ∘ augmentedModel_BAUGC Φint J
          (bmBlocks_BAUGC c R A z₀)) z) = fderiv ℝ (Kint ∘ Φint) z ∧
      ∀ (b : κ) (w : E),
        ‖fderiv ℝ (augmentedPrune_BAUGC Kint ∘ augmentedModel_BAUGC Φint J
          (bmBlocks_BAUGC c R A z₀)) z w (Sum.inr b)‖ ≤ 2 * P * ‖w‖ ∧
        (b ∉ J → fderiv ℝ (augmentedPrune_BAUGC Kint ∘ augmentedModel_BAUGC Φint J
          (bmBlocks_BAUGC c R A z₀)) z w (Sum.inr b) = 0) := by
  rw [fderiv_augmented_pruned_BAUGC Kint hint fun b _ =>
    differentiableAt_bmBlocks_BAUGC c hR.ne' A z₀ z b]
  refine ⟨augIntProj_comp_augDeriv_BAUGC _ _, fun b w => ⟨norm_augDeriv_inr_le_BAUGC hP _ J c
    hR.ne' hA z₀ z w b, fun hb => ?_⟩⟩
  rw [augDeriv_apply_inr_BAUGC, augmentedBlockDeriv_BAUGC, ite_eq_right hb, zero_apply, map_zero]

end Model

end DifferentialGeometry.Geometry.Collapse
