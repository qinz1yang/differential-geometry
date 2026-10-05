import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedCloudKernel
import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockProfile

/-!
# The transfer layer, generic part: port clauses ⟹ augmented spec fields (lane BAUG-C)

Step 0 of the transfer from the INTERIOR port tables (`PortTargets v3.1`,
`port_{circle,edge,slim}_interior_table_BAUGP`) to `BoundaryEnhancedPlaneSpecV3` (dry-run table in
`build-logs/resume/state-BAUG-C.md`): everything that does not mention the supply, stated for
abstract tag types `ι κ` (fast to elaborate; instantiated at `S.IntTag_BAUGA`,
`Fin S.packet.cusp.count` by the stage transfers).

* `bmConst_BAUGC`: BCG.0's profile constant `P_*` as a named number (`1 ≤ P_*`,
  `‖𝓑'‖, ‖𝓑''‖ ≤ P_*`), so that numeric premises of the producers can name it.
* (OWN) ⟹ `dimension`: a left inverse of a model is a left inverse of its derivative
  (`leftInverse_fderiv_BAUGC`); the augmented derivative is then injective
  (`augDeriv_injective_BAUGC`) and its range has dimension `dim E`
  (`finrank_range_augDeriv_BAUGC`).
* (Q) ⟹ `L_x ≤ Q_j^∂`: block-restriction invariance passes to derivatives
  (`clm_fderiv_of_fixed_BAUGC`) and to the augmented derivative with all boundary slots
  kept (`blockRestrict_disjSum_augDeriv_BAUGC`).
* (TG derivative) ⟹ `normal`: the normal component is at most the distance to any vector of the
  plane (`norm_orthogonal_starProjection_le_BAUGC`).
* (PP-int) / (SCL) / (SB-int) / (FM*-int) / (ZB*-int) ⟹ kernel clauses: the interior marker and
  whole-block functionals read only `T_int` (`blockMarkerCLM_inl_augDeriv_BAUGC`,
  `blockProjCLM_inl_augDeriv_BAUGC`, `range_augDeriv_le_ker_marker_BAUGC`,
  `range_augDeriv_le_ker_block_BAUGC`).
* consumer `augmented_plane_dimension_BAUGC`: the `dimension` field of an augmented pruned table
  from (OWN) and (Q).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ### BCG.0's profile constant -/

/-- **`P_*`** (BCG.0): one finite bound for `‖𝓑'‖∞` and `‖𝓑''‖∞` of the boundary block profile,
fixed once (`exists_boundaryBlock_derivative_bounds`). -/
def bmConst_BAUGC : ℝ :=
  Classical.choose exists_boundaryBlock_derivative_bounds

theorem one_le_bmConst_BAUGC : 1 ≤ bmConst_BAUGC :=
  (Classical.choose_spec exists_boundaryBlock_derivative_bounds).1

theorem norm_fderiv_boundaryBlock_le_bmConst_BAUGC (t : ℝ) :
    ‖fderiv ℝ boundaryBlock t‖ ≤ bmConst_BAUGC :=
  (Classical.choose_spec exists_boundaryBlock_derivative_bounds).2.1 t

theorem norm_fderiv_fderiv_boundaryBlock_le_bmConst_BAUGC (t : ℝ) :
    ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ bmConst_BAUGC :=
  (Classical.choose_spec exists_boundaryBlock_derivative_bounds).2.2 t

/-! ### (OWN) ⟹ dimension -/

section Own

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A left inverse of a model is a left inverse of its derivative**: `P ∘ Φ = id` with `P`
linear and `Φ` differentiable at `u` give `P ∘ DΦ(u) = id`. -/
theorem leftInverse_fderiv_BAUGC (P : F →L[ℝ] E) {Φ : E → F} (hP : ∀ u, P (Φ u) = u) {u : E}
    (hΦ : DifferentiableAt ℝ Φ u) (v : E) : P (fderiv ℝ Φ u v) = v := by
  have hcomp : (fun z => P (Φ z)) = id := funext hP
  have h := fderiv_comp u P.differentiableAt hΦ
  rw [ContinuousLinearMap.fderiv] at h
  have h2 : fderiv ℝ (fun z => P (Φ z)) u = ContinuousLinearMap.id ℝ E := by
    rw [hcomp]
    exact fderiv_id
  have h3 : (P.comp (fderiv ℝ Φ u)) v = v := by
    rw [← h]
    change fderiv ℝ (fun z => P (Φ z)) u v = v
    rw [h2]
    rfl
  exact h3

/-- **Invariance under a linear map passes to the derivative**: if `L ∘ Φ = Φ` (e.g. a block
restriction `π_s`) then `L (DΦ(u) v) = DΦ(u) v`. -/
theorem clm_fderiv_of_fixed_BAUGC (L : F →L[ℝ] F) {Φ : E → F} (hfix : ∀ u, L (Φ u) = Φ u) {u : E}
    (hΦ : DifferentiableAt ℝ Φ u) (v : E) : L (fderiv ℝ Φ u v) = fderiv ℝ Φ u v := by
  have h := L.hasFDerivAt.comp u hΦ.hasFDerivAt
  have hcomp : (L ∘ Φ) = Φ := funext hfix
  rw [hcomp] at h
  have h2 := h.fderiv
  calc L (fderiv ℝ Φ u v) = (L.comp (fderiv ℝ Φ u)) v := rfl
    _ = fderiv ℝ Φ u v := by rw [← h2]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **The augmented derivative is injective** when its interior part has a left inverse:
`Pc ∘ pr_int ∘ augDeriv = Pc ∘ T_int = id`. -/
theorem augDeriv_injective_BAUGC (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E)
    (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²)) (hPc : ∀ v, Pc (Tint v) = v)
    (Tb : κ → E →L[ℝ] ℝ × ℝ) : Function.Injective (augDeriv_BAUGC Tint Tb) := by
  intro v w h
  have hc := augIntProj_comp_augDeriv_BAUGC Tint Tb
  have hv : Pc (augIntProjCLM_BAUGC (augDeriv_BAUGC Tint Tb v)) = v := by
    rw [← ContinuousLinearMap.comp_apply augIntProjCLM_BAUGC, hc, hPc]
  have hw : Pc (augIntProjCLM_BAUGC (augDeriv_BAUGC Tint Tb w)) = w := by
    rw [← ContinuousLinearMap.comp_apply augIntProjCLM_BAUGC, hc, hPc]
  rw [← hv, ← hw, h]

/-- **`dim L = dim E`**: the range of an injective augmented derivative. -/
theorem finrank_range_augDeriv_BAUGC
    (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E) (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (hPc : ∀ v, Pc (Tint v) = v) (Tb : κ → E →L[ℝ] ℝ × ℝ) :
    Module.finrank ℝ (LinearMap.range (augDeriv_BAUGC Tint Tb :
      E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²))) = Module.finrank ℝ E :=
  LinearMap.finrank_range_of_inj (augDeriv_injective_BAUGC Pc Tint hPc Tb)

end Own

/-! ### (Q) ⟹ `L ≤ Q` -/

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι]
  [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **The augmented derivative stays in `Q^∂`**: if the interior part is `π_s`-invariant then the
augmented derivative is invariant under the restriction to `s ⊕ (all boundary slots)`. -/
theorem blockRestrict_disjSum_augDeriv_BAUGC (s : Finset ι)
    (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²)) (hfix : ∀ v, blockRestrict s (Tint v) = Tint v)
    (Tb : κ → E →L[ℝ] ℝ × ℝ) (v : E) :
    blockRestrict (s.disjSum Finset.univ) (augDeriv_BAUGC Tint Tb v) = augDeriv_BAUGC Tint Tb v := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  rcases t with i | b
  · by_cases hi : i ∈ s
    · rw [ite_eq_left (Finset.inl_mem_disjSum.mpr hi)]
    · rw [ite_eq_right (fun h => hi (Finset.inl_mem_disjSum.mp h)), augDeriv_apply_inl_BAUGC]
      have h := congrArg (fun z : BlockSpace (fun _ : ι => ℝ²) => z i) (hfix v)
      simp only [blockRestrict_apply, ite_eq_right hi] at h
      exact h
  · rw [ite_eq_left (Finset.inr_mem_disjSum.mpr (Finset.mem_univ b))]

end Restrict

/-! ### (TG derivative) ⟹ normal -/

section Normal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The normal component is at most the distance to the plane**: for `w ∈ K`,
`‖Kᗮ.starProjection y‖ ≤ ‖y − w‖`. -/
theorem norm_orthogonal_starProjection_le_BAUGC (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (y w : H) (hw : w ∈ K) : ‖Kᗮ.starProjection y‖ ≤ ‖y - w‖ := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, fun _ ⟨_, hz⟩ => hz ▸ norm_nonneg _⟩ (⟨w, hw⟩ : K)

end Normal

/-! ### Interior functionals read only the interior derivative -/

section Functionals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι]
  [Fintype κ] [DecidableEq κ]

/-- The marker of an interior tag of the augmented derivative is that of the interior one. -/
theorem blockMarkerCLM_inl_augDeriv_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Tb : κ → E →L[ℝ] ℝ × ℝ) (t : ι) (v : E) :
    blockMarkerCLM (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) (augDeriv_BAUGC Tint Tb v) =
      (Tint v t).snd := by
  rw [blockMarkerCLM_apply, augDeriv_apply_inl_BAUGC]

/-- The whole block of an interior tag of the augmented derivative is that of the interior one. -/
theorem blockProjCLM_inl_augDeriv_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Tb : κ → E →L[ℝ] ℝ × ℝ) (t : ι) (v : E) :
    blockProjCLM_PLN (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) (augDeriv_BAUGC Tint Tb v) =
      Tint v t := by
  rw [blockProjCLM_apply_PLN, augDeriv_apply_inl_BAUGC]

/-- **A vanishing interior marker derivative puts the plane in the marker kernel.** -/
theorem range_augDeriv_le_ker_marker_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Tb : κ → E →L[ℝ] ℝ × ℝ) (t : ι) (h : ∀ v, (Tint v t).snd = 0) :
    LinearMap.range (augDeriv_BAUGC Tint Tb : E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) ≤
      LinearMap.ker ((blockMarkerCLM (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) :
        BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] ℝ) : BlockSpace (fun _ : ι ⊕ κ => ℝ²) →ₗ[ℝ] ℝ) := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  change blockMarkerCLM (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) (augDeriv_BAUGC Tint Tb v) = 0
  rw [blockMarkerCLM_inl_augDeriv_BAUGC]
  exact h v

/-- **A vanishing interior block derivative puts the plane in the block kernel.** -/
theorem range_augDeriv_le_ker_block_BAUGC (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Tb : κ → E →L[ℝ] ℝ × ℝ) (t : ι) (h : ∀ v, Tint v t = 0) :
    LinearMap.range (augDeriv_BAUGC Tint Tb : E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) ≤
      LinearMap.ker ((blockProjCLM_PLN (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) :
        BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BlockSpace (fun _ : ι ⊕ κ => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  change blockProjCLM_PLN (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) (augDeriv_BAUGC Tint Tb v) = 0
  rw [blockProjCLM_inl_augDeriv_BAUGC]
  exact h v

end Functionals

/-! ### Consumer: the `dimension` field of an augmented pruned table -/

section Dimension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι]
  [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **Consumer (spec field `dimension`, generic)**: for the augmented pruned model
`K^∂(K_int) ∘ Φ^∂[Φ_int]` at `z`, if the pruned interior model has a linear left inverse (port
(OWN)) and is `π_s`-invariant (port (Q)), the plane `im D(K^∂Φ^∂)(z)` has dimension `dim E` and lies
in the stage space of the tags `s ⊕ (all boundary slots)`. -/
theorem augmented_plane_dimension_BAUGC
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ) (Φb : κ → E → ℝ × ℝ) {z : E}
    (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E) (hPc : ∀ u, Pc ((Kint ∘ Φint) u) = u)
    (s : Finset ι) (hQ : ∀ u, blockRestrict s ((Kint ∘ Φint) u) = (Kint ∘ Φint) u)
    (hint : DifferentiableAt ℝ (Kint ∘ Φint) z) (hb : ∀ b ∈ J, DifferentiableAt ℝ (Φb b) z) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (augmentedPrune_BAUGC Kint ∘
        augmentedModel_BAUGC Φint J Φb) z : E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²))) =
      Module.finrank ℝ E ∧
    ∀ w ∈ LinearMap.range (fderiv ℝ (augmentedPrune_BAUGC Kint ∘
        augmentedModel_BAUGC Φint J Φb) z : E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)),
      blockRestrict (s.disjSum Finset.univ) w = w := by
  rw [fderiv_augmented_pruned_BAUGC Kint hint hb]
  refine ⟨finrank_range_augDeriv_BAUGC Pc _ (leftInverse_fderiv_BAUGC Pc hPc hint) _, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact blockRestrict_disjSum_augDeriv_BAUGC s _
    (clm_fderiv_of_fixed_BAUGC (blockRestrict s) hQ hint) _ v

end Dimension

end DifferentialGeometry.Geometry.Collapse
