import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedOriginalMap

/-!
# BCG07 (Sat): the algebraic saturation exit of the cusp fronts (lane BCG7-COLLAR)

External draft 61 §5.3 and disposition D61-10: because every projection `π_j` of the boundary
adjustment chain keeps the whole boundary block space `H_∂` (`H_∂ ≤ Q_j^∂`), the block coordinates
`J_b` factor through `π_j`, hence for the cusp front `H_b = {v_b ≥ .9 ∧ u_b = 40 v_b}`,
`(u_b, v_b) = J_b ∘ E`,

  `p ∈ H_b, π_j E(q) = π_j E(p) ⟹ q ∈ H_b`        (Sat)

for EVERY map `E : W → H^∂` and every `q ∈ W` — no smoothness, no fibre connectedness (the
strengthening of the draft's "smooth `E`": smoothness is not used).

Encoding (lane BAUG-A, `BoundaryAugmentedOriginalMap`): `H^∂ = BlockSpace (ι ⊕ κ ↦ ℝ²)`, the slot of
the boundary component `b` carries `(planeAxis u_b, v_b)`.

* `mem_of_factor_BC7C`, `preimage_image_eq_of_factor_BC7C`: the abstract exit — if `J` factors
  through `π`, every set `{x | J (E x) ∈ S}` is `π ∘ E`-saturated (also for later factorizations
  such as the embedding `Θ₂`);
* `augmentedBoundarySubmodule_BC7C` (`H_∂`, the vectors with zero interior slots) and
  `augmentedBoundaryCoord_BC7C b` (`J_b`, read off the slot of `b`);
  `augmentedBoundaryCoord_boundaryAugmentedMap_BC7C`: `J_b ∘ F_∂ = F_{∂,b}` for BAUG-A's augmented
  map;
* `slot_eq_zero_of_mem_orthogonal_BC7C`, `slot_starProjection_BC7C`,
  `augmentedBoundaryCoord_starProjection_BC7C`: for every subspace `Q ≥ H_∂` the orthogonal
  projection onto `Q` keeps every boundary slot, hence `J_b ∘ π_Q = J_b`;
* `cuspFront_saturated_BC7C` (Sat), `cuspFront_preimage_image_BC7C` (the front is a union of
  whole fibres of `π_Q ∘ E`), `cuspMarkerSublevel_saturated_BC7C` (the same for the marker part
  `{v_b ≥ .9 ∧ u_b ≤ 40 v_b}` of the cusp core);
* consumer `boundaryOriginalMap_cuspFront_saturated_BC7C`: on the ACTUAL original augmented map
  `F_∂ = boundaryOriginalMap_BAUGA P Fint`, every point of `Safe_b` of height `40` lies in the front
  of `F_∂`, and every whole fibre of `π_Q ∘ F_∂` through it lies in the front.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

section Abstract

variable {W H Y Z : Type*}

/-- **(Sat), abstract**: if `J` factors through `π` (`π v = π w ⟹ J v = J w`), then for every
`E : W → H` and every `S ⊆ Z`, a point `q` with `π (E q) = π (E p)` and `J (E p) ∈ S` has
`J (E q) ∈ S`. -/
theorem mem_of_factor_BC7C (E : W → H) (π : H → Y) (J : H → Z)
    (hJ : ∀ v w, π v = π w → J v = J w) (S : Set Z) {p q : W} (hp : J (E p) ∈ S)
    (hpq : π (E q) = π (E p)) : J (E q) ∈ S := by
  rw [hJ _ _ hpq]
  exact hp

/-- **(Sat), as a set identity**: if `J` factors through `π`, the set `{x | J (E x) ∈ S}` is a
union of whole fibres of `π ∘ E`. -/
theorem preimage_image_eq_of_factor_BC7C (E : W → H) (π : H → Y) (J : H → Z)
    (hJ : ∀ v w, π v = π w → J v = J w) (S : Set Z) :
    (π ∘ E) ⁻¹' ((π ∘ E) '' {x | J (E x) ∈ S}) = {x | J (E x) ∈ S} := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro q ⟨p, hp, hpq⟩
  exact mem_of_factor_BC7C E π J hJ S hp hpq.symm

end Abstract

section Encoding

variable {ι κ : Type*}

/-- `H_∂`: the boundary block space of `H^∂ = BlockSpace (ι ⊕ κ ↦ ℝ²)`, the vectors whose interior
slots vanish. -/
def augmentedBoundarySubmodule_BC7C : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²)) where
  carrier := {x | ∀ i : ι, x (Sum.inl i) = 0}
  add_mem' := fun {x y} hx hy i => by simp [hx i, hy i]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c x hx i => by simp [hx i]

/-- `J_b = (u_b, v_b)`: the coordinates of the boundary block of `b`, read off the slot of `b` in
the plane encoding `(planeAxis u_b, v_b)`. -/
def augmentedBoundaryCoord_BC7C (b : κ) (x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) : ℝ × ℝ :=
  ((x (Sum.inr b)).fst 0, (x (Sum.inr b)).snd)

/-- `J_b ∘ F_∂ = F_{∂,b}`: on BAUG-A's augmented map the block coordinates of `b` are the boundary
block of `b`. -/
theorem augmentedBoundaryCoord_boundaryAugmentedMap_BC7C {M : Type*}
    (Fint : M → BlockSpace (fun _ : ι => ℝ²)) (B : κ → M → ℝ × ℝ) (p : M) (b : κ) :
    augmentedBoundaryCoord_BC7C b (boundaryAugmentedMap_BAUGA Fint B p) = B b p := by
  simp [augmentedBoundaryCoord_BC7C, boundaryAugmentedMap_boundary_block_BAUGA,
    planeBlockEmbed_apply_BAUGA, planeAxis_apply]

end Encoding

section Projection

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A vector orthogonal to `H_∂` has zero boundary slots. -/
theorem slot_eq_zero_of_mem_orthogonal_BC7C {w : BlockSpace (fun _ : ι ⊕ κ => ℝ²)}
    (hw : w ∈ (augmentedBoundarySubmodule_BC7C (ι := ι) (κ := κ))ᗮ) (b : κ) :
    w (Sum.inr b) = 0 := by
  classical
  let y : BlockSpace (fun _ : ι ⊕ κ => ℝ²) :=
    WithLp.toLp 2 (Pi.single (Sum.inr b) (w (Sum.inr b)))
  have hy : y ∈ augmentedBoundarySubmodule_BC7C (ι := ι) (κ := κ) := fun i => by
    simp [y]
  have h0 : ⟪y, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hy hw
  rw [PiLp.inner_apply, Finset.sum_eq_single (Sum.inr b)] at h0
  · simpa [y] using h0
  · intro t _ ht
    simp [y, Pi.single_eq_of_ne ht]
  · simp

/-- **The projections keep the boundary slots**: for a subspace `Q ≥ H_∂`, the orthogonal
projection onto `Q` does not change the slot of any boundary component. -/
theorem slot_starProjection_BC7C (Q : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²)))
    [Q.HasOrthogonalProjection] (hQ : augmentedBoundarySubmodule_BC7C ≤ Q)
    (v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) :
    Q.starProjection v (Sum.inr b) = v (Sum.inr b) := by
  have h := Submodule.orthogonal_le hQ (Q.sub_starProjection_mem_orthogonal v)
  have h0 := slot_eq_zero_of_mem_orthogonal_BC7C h b
  rw [PiLp.sub_apply, sub_eq_zero] at h0
  exact h0.symm

/-- **`J_b` factors through `π_Q`** for every `Q ≥ H_∂`: `J_b ∘ π_Q = J_b`. -/
theorem augmentedBoundaryCoord_starProjection_BC7C
    (Q : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) [Q.HasOrthogonalProjection]
    (hQ : augmentedBoundarySubmodule_BC7C ≤ Q) (b : κ) (v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    augmentedBoundaryCoord_BC7C b (Q.starProjection v) = augmentedBoundaryCoord_BC7C b v := by
  simp only [augmentedBoundaryCoord_BC7C, slot_starProjection_BC7C Q hQ v b]

/-- Equal projections onto `Q ≥ H_∂` have equal block coordinates. -/
theorem augmentedBoundaryCoord_eq_of_starProjection_eq_BC7C
    (Q : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) [Q.HasOrthogonalProjection]
    (hQ : augmentedBoundarySubmodule_BC7C ≤ Q) (b : κ) {v w : BlockSpace (fun _ : ι ⊕ κ => ℝ²)}
    (h : Q.starProjection v = Q.starProjection w) :
    augmentedBoundaryCoord_BC7C b v = augmentedBoundaryCoord_BC7C b w := by
  rw [← augmentedBoundaryCoord_starProjection_BC7C Q hQ b v, h,
    augmentedBoundaryCoord_starProjection_BC7C Q hQ b w]

variable {W : Type*}

/-- **(Sat) for the cusp front** (draft 61 §5.3): for EVERY map `E : W → H^∂`, every subspace
`Q ≥ H_∂` and every boundary component `b`, with `(u_b, v_b) = J_b ∘ E`: if `p` lies in the front
`H_b = {v_b ≥ .9 ∧ u_b = 40 v_b}` and `π_Q E(q) = π_Q E(p)` (`q` anywhere in `W`), then
`q ∈ H_b`. -/
theorem cuspFront_saturated_BC7C (Q : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²)))
    [Q.HasOrthogonalProjection] (hQ : augmentedBoundarySubmodule_BC7C ≤ Q)
    (E : W → BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) {p q : W}
    (hp : 9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (E p)).2 ∧
      (augmentedBoundaryCoord_BC7C b (E p)).1 = 40 * (augmentedBoundaryCoord_BC7C b (E p)).2)
    (hpq : Q.starProjection (E q) = Q.starProjection (E p)) :
    9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (E q)).2 ∧
      (augmentedBoundaryCoord_BC7C b (E q)).1 = 40 * (augmentedBoundaryCoord_BC7C b (E q)).2 := by
  rw [augmentedBoundaryCoord_eq_of_starProjection_eq_BC7C Q hQ b hpq]
  exact hp

/-- **The cusp front is a union of whole fibres** of `π_Q ∘ E` (every `Q ≥ H_∂`, every `E`). -/
theorem cuspFront_preimage_image_BC7C (Q : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²)))
    [Q.HasOrthogonalProjection] (hQ : augmentedBoundarySubmodule_BC7C ≤ Q)
    (E : W → BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) :
    (Q.starProjection ∘ E) ⁻¹' ((Q.starProjection ∘ E) ''
        {x | 9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (E x)).2 ∧
          (augmentedBoundaryCoord_BC7C b (E x)).1 =
            40 * (augmentedBoundaryCoord_BC7C b (E x)).2}) =
      {x | 9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (E x)).2 ∧
        (augmentedBoundaryCoord_BC7C b (E x)).1 =
          40 * (augmentedBoundaryCoord_BC7C b (E x)).2} :=
  preimage_image_eq_of_factor_BC7C E Q.starProjection (augmentedBoundaryCoord_BC7C b)
    (fun _ _ h => augmentedBoundaryCoord_eq_of_starProjection_eq_BC7C Q hQ b h)
    {z | 9 / 10 ≤ z.2 ∧ z.1 = 40 * z.2}

/-- **(Sat) for the marker part of the cusp core** `{v_b ≥ .9 ∧ u_b ≤ 40 v_b}` (every `Q ≥ H_∂`,
every `E`, `q` anywhere in `W`). -/
theorem cuspMarkerSublevel_saturated_BC7C (Q : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²)))
    [Q.HasOrthogonalProjection] (hQ : augmentedBoundarySubmodule_BC7C ≤ Q)
    (E : W → BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) {p q : W}
    (hp : 9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (E p)).2 ∧
      (augmentedBoundaryCoord_BC7C b (E p)).1 ≤ 40 * (augmentedBoundaryCoord_BC7C b (E p)).2)
    (hpq : Q.starProjection (E q) = Q.starProjection (E p)) :
    9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (E q)).2 ∧
      (augmentedBoundaryCoord_BC7C b (E q)).1 ≤ 40 * (augmentedBoundaryCoord_BC7C b (E q)).2 := by
  rw [augmentedBoundaryCoord_eq_of_starProjection_eq_BC7C Q hQ b hpq]
  exact hp

end Projection

section Consumer

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Geometry.Riemannian

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ} {ι : Type*} [Fintype ι]

/-- **Consumer: the front of the actual original augmented map.** For BAUG-A's
`F_∂ = boundaryOriginalMap_BAUGA P Fint` (actual collar blocks), every point `p` of `Safe_b` with
`η_b(p) = 40` lies in the cusp front of `F_∂` (`v_b = 1`, `u_b = 40`), and for every subspace
`Q ≥ H_∂`, every point `q` of `W` with `π_Q F_∂(q) = π_Q F_∂(p)` lies in that front. -/
theorem boundaryOriginalMap_cuspFront_saturated_BC7C (P : BoundaryCollarPacket W g K A w₀ ε)
    (Fint : W.Carrier → BlockSpace (fun _ : ι => ℝ²)) {b : Fin P.cusp.count} {p : W.Carrier}
    (hp : p ∈ P.safeBand_BAUGA b) (h40 : P.height b p = 40)
    (Q : Submodule ℝ (BlockSpace (fun _ : ι ⊕ Fin P.cusp.count => ℝ²)))
    [Q.HasOrthogonalProjection] (hQ : augmentedBoundarySubmodule_BC7C ≤ Q) :
    (9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint p)).2 ∧
      (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint p)).1 =
        40 * (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint p)).2) ∧
    ∀ q, Q.starProjection (boundaryOriginalMap_BAUGA P Fint q) =
        Q.starProjection (boundaryOriginalMap_BAUGA P Fint p) →
      9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint q)).2 ∧
        (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint q)).1 =
          40 * (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint q)).2 := by
  have hJ : augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint p) = (40, 1) := by
    rw [boundaryOriginalMap_BAUGA, augmentedBoundaryCoord_boundaryAugmentedMap_BC7C,
      P.block_eq_of_mem_safeBand_BAUGA b hp, h40]
  have hfront : 9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint p)).2 ∧
      (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint p)).1 =
        40 * (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint p)).2 := by
    rw [hJ]
    norm_num
  exact ⟨hfront, fun q hq => cuspFront_saturated_BC7C Q hQ _ b hfront hq⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
