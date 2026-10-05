import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersBase
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the adapted corner charts

Part B of the circle kind of the S³ inhabitant: the four corner charts of `C₁ = [1, 4]²`, adapted to
the actual rows (lead decision 02:45). The corner `(b, e)` (`circCornerEquiv`) is centred at
`(ψ, r) = (b ? 4 : 1, b xor e ? 4 : 1)`; its chart is

  `k_{b,e}(x, y) = (circCornerInv ψ b x, circCornerInv r (b xor e) y)`

on `rimBox 2`, i.e. the point whose `ψ`-slack is `x / 16` and whose `r`-slack is `y / 16`. Hence
the first label (`N` if `b`, else `S`) reads `−x / 16` and the second label (`T` if `b xor e`, else
`B`) reads `−y / 16` exactly; the other two defining functions are `< −1/8` on the chart; the
targets are pairwise disjoint; every double zero is a chart centre.

* `circPlaneChart σ σ'` — the chart in `ℝ × ℝ` coordinates `(ψ, r)` (source `rimBox 2`, target the
  points with small slacks), with the explicit inverse `16 • slack`;
* `circCornerChart b e` — composed with `(ψ, r) ↦ ℝ²` and the inverse of the open inclusion of the
  base `(1/2, 8)²`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem isOpen_rimBox_CIRCB (r : ℝ) : IsOpen (rimBox r) :=
  (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

/-! ## The chart in the coordinates `(ψ, r)` -/

/-- The corner chart in the coordinates `(ψ, r)`. -/
def circPlaneMap (σ σ' : Bool) (v : ℝ × ℝ) : ℝ × ℝ :=
  (circCornerInv false σ v.1, circCornerInv true σ' v.2)

/-- Its inverse: sixteen times the two slacks. -/
def circPlaneInv (σ σ' : Bool) (u : ℝ × ℝ) : ℝ × ℝ :=
  (16 * circSlack false σ u.1, 16 * circSlack true σ' u.2)

/-- The target: positive coordinates with slacks in `(−1/8, 1/8)`. -/
def circPlaneTarget (σ σ' : Bool) : Set (ℝ × ℝ) :=
  {u | 0 < u.1 ∧ 0 < u.2 ∧ |16 * circSlack false σ u.1| < 2 ∧ |16 * circSlack true σ' u.2| < 2}

theorem contDiffOn_circPlaneInv (σ σ' : Bool) :
    ContDiffOn ℝ ∞ (circPlaneInv σ σ') {u | 0 < u.1 ∧ 0 < u.2} := fun u hu =>
  ((contDiffAt_const.mul ((contDiffAt_circSlack false σ hu.1).comp u contDiffAt_fst)).prodMk
    (contDiffAt_const.mul
      ((contDiffAt_circSlack true σ' hu.2).comp u contDiffAt_snd))).contDiffWithinAt

theorem contDiffOn_circPlaneMap (σ σ' : Bool) : ContDiffOn ℝ ∞ (circPlaneMap σ σ') (rimBox 2) :=
  fun v hv => (((contDiffAt_circCornerInv false σ hv.1).comp v contDiffAt_fst).prodMk
    ((contDiffAt_circCornerInv true σ' hv.2).comp v contDiffAt_snd)).contDiffWithinAt

theorem isOpen_circPlaneTarget (σ σ' : Bool) : IsOpen (circPlaneTarget σ σ') := by
  have hQ : IsOpen {u : ℝ × ℝ | 0 < u.1 ∧ 0 < u.2} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
  have h := (contDiffOn_circPlaneInv σ σ').continuousOn.isOpen_inter_preimage hQ
    ((isOpen_Ioo (a := (-2 : ℝ)) (b := 2)).prod (isOpen_Ioo (a := (-2 : ℝ)) (b := 2)))
  convert h using 1
  ext u
  simp only [circPlaneTarget, circPlaneInv, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod,
    mem_Ioo, abs_lt]
  tauto

theorem sixteen_mul_one_div (s : ℝ) : 16 * (1 / 16 * s) = s := by
  ring

/-- **The plane corner chart** `(x, y) ↦ (ψ, r)` with slacks `(x / 16, y / 16)`. -/
def circPlaneChart (σ σ' : Bool) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun := circPlaneMap σ σ'
  invFun := circPlaneInv σ σ'
  source := rimBox 2
  target := circPlaneTarget σ σ'
  map_source' v hv := by
    refine ⟨circCornerInv_pos false σ hv.1, circCornerInv_pos true σ' hv.2, ?_, ?_⟩
    · change |16 * circSlack false σ (circCornerInv false σ v.1)| < 2
      rw [circSlack_circCornerInv false σ hv.1, sixteen_mul_one_div]
      exact hv.1
    · change |16 * circSlack true σ' (circCornerInv true σ' v.2)| < 2
      rw [circSlack_circCornerInv true σ' hv.2, sixteen_mul_one_div]
      exact hv.2
  map_target' u hu := ⟨hu.2.2.1, hu.2.2.2⟩
  left_inv' v hv := by
    change (16 * circSlack false σ (circCornerInv false σ v.1),
      16 * circSlack true σ' (circCornerInv true σ' v.2)) = v
    rw [circSlack_circCornerInv false σ hv.1, circSlack_circCornerInv true σ' hv.2,
      sixteen_mul_one_div, sixteen_mul_one_div]
  right_inv' u hu := by
    change (circCornerInv false σ (16 * circSlack false σ u.1),
      circCornerInv true σ' (16 * circSlack true σ' u.2)) = u
    rw [circCornerInv_circSlack false σ hu.1, circCornerInv_circSlack true σ' hu.2.1]
  open_source := isOpen_rimBox_CIRCB 2
  open_target := isOpen_circPlaneTarget σ σ'
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 (contDiffOn_circPlaneMap σ σ')
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2
    ((contDiffOn_circPlaneInv σ σ').mono fun _ hu => ⟨hu.1, hu.2.1⟩)

/-! ## Into the base `(1/2, 8)²` -/

/-- The base coordinates `(ψ, r) ↦ ℝ²` as a partial diffeomorphism. -/
def circEquivPD : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) E2 ∞ where
  toPartialEquiv := sphereCircleEquiv.symm.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := sphereCircleEquiv.symm.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := sphereCircleEquiv.contDiff.contMDiff.contMDiffOn

theorem circBase_nonempty : Nonempty sphereCircleBaseOpens :=
  ⟨⟨sphereCircleEquiv.symm (1, 1), sphereCircleEquiv_symm_mem ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩⟩⟩

/-- `(ψ, r) ↦` the base point, through the inverse of the open inclusion. -/
def circToBase : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) sphereCircleBaseOpens ∞ :=
  circEquivPD.trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 2) sphereCircleBaseOpens
      circBase_nonempty).symm

theorem circToBase_source :
    circToBase.source = sphereCircleEquiv.symm ⁻¹' sphereCircleBaseSet := by
  ext u
  change u ∈ univ ∩ sphereCircleEquiv.symm ⁻¹'
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 2) sphereCircleBaseOpens
      circBase_nonempty).target ↔ _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target, univ_inter]
  rfl

theorem circToBase_val {u : ℝ × ℝ} (hu : sphereCircleEquiv.symm u ∈ sphereCircleBaseSet) :
    (circToBase u).val = sphereCircleEquiv.symm u := by
  change ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 2)
    sphereCircleBaseOpens circBase_nonempty).symm (sphereCircleEquiv.symm u)).val = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hu]

theorem circToBase_symm (c : sphereCircleBaseOpens) :
    circToBase.symm c = sphereCircleEquiv c.val :=
  rfl

theorem mem_circToBase_target (c : sphereCircleBaseOpens) : c ∈ circToBase.target := by
  change c ∈ univ ∩ _ ⁻¹' univ
  simp

/-! ## The corner charts -/

/-- **The corner chart** of the corner `(b, e)`: `ψ`-side `b`, `r`-side `b xor e`. -/
def circCornerChart (b e : Bool) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) sphereCircleBaseOpens ∞ :=
  (circPlaneChart b (b ^^ e)).trans circToBase

theorem circPlaneMap_mem_base {σ σ' : Bool} {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    sphereCircleEquiv.symm (circPlaneMap σ σ' v) ∈ sphereCircleBaseSet :=
  sphereCircleEquiv_symm_mem (circCornerInv_mem_wide false σ hv.1)
    (circCornerInv_mem_wide true σ' hv.2)

theorem circCornerChart_source (b e : Bool) : (circCornerChart b e).source = rimBox 2 := by
  ext v
  change v ∈ rimBox 2 ∩ circPlaneMap b (b ^^ e) ⁻¹' circToBase.source ↔ _
  rw [circToBase_source]
  exact ⟨fun h => h.1, fun h => ⟨h, circPlaneMap_mem_base h⟩⟩

theorem circCornerChart_val (b e : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    (circCornerChart b e v).val = sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) v) :=
  circToBase_val (circPlaneMap_mem_base hv)

theorem circCoordL_circCornerChart (b e : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    circCoordL false (circCornerChart b e v).val = circCornerInv false b v.1 ∧
      circCoordL true (circCornerChart b e v).val = circCornerInv true (b ^^ e) v.2 := by
  rw [circCornerChart_val b e hv, circCoordL_symm, circCoordL_symm]
  exact ⟨rfl, rfl⟩

theorem mem_circCornerChart_target {b e : Bool} {c : sphereCircleBaseOpens} :
    c ∈ (circCornerChart b e).target ↔ sphereCircleEquiv c.val ∈ circPlaneTarget b (b ^^ e) := by
  change c ∈ circToBase.target ∩ circToBase.symm ⁻¹' circPlaneTarget b (b ^^ e) ↔ _
  rw [mem_inter_iff, mem_preimage, circToBase_symm]
  exact ⟨fun h => h.2, fun h => ⟨mem_circToBase_target c, h⟩⟩

theorem circCornerChart_symm (b e : Bool) (c : sphereCircleBaseOpens) :
    (circCornerChart b e).symm c = circPlaneInv b (b ^^ e) (sphereCircleEquiv c.val) :=
  rfl

/-! ## Corner index `Fin 4 ≃ (b, e)` -/

/-- The corner index `(b, e) ↦ 2 b + e`. -/
def circCornerEquiv : Bool × Bool ≃ Fin 4 where
  toFun p := ⟨(if p.1 then 2 else 0) + (if p.2 then 1 else 0), by
    rcases p with ⟨_ | _, _ | _⟩ <;> decide⟩
  invFun k := (decide (2 ≤ k.val), decide (k.val % 2 = 1))
  left_inv := by decide
  right_inv := by decide

/-- The corner charts indexed by `Fin 4`. -/
def circCorner (k : Fin 4) : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) sphereCircleBaseOpens ∞ :=
  circCornerChart (circCornerEquiv.symm k).1 (circCornerEquiv.symm k).2

/-- The first label of a corner: the `ψ`-face `(ψ, b)`. -/
def circCornerFirst (k : Fin 4) : Fin 4 :=
  circFaceEquiv (false, (circCornerEquiv.symm k).1)

/-- The second label of a corner: the `r`-face `(r, b xor e)`. -/
def circCornerSecond (k : Fin 4) : Fin 4 :=
  circFaceEquiv (true, (circCornerEquiv.symm k).1 ^^ (circCornerEquiv.symm k).2)

theorem circCorner_ne (k : Fin 4) : circCornerFirst k ≠ circCornerSecond k := by
  intro h
  have := congrArg Prod.fst (circFaceEquiv.injective h)
  exact Bool.false_ne_true this

theorem circCorner_source (k : Fin 4) : (circCorner k).source = rimBox 2 :=
  circCornerChart_source _ _

/-- The plane targets of two different corners are disjoint. -/
theorem circPlaneTarget_disjoint {σ₁ σ₁' σ₂ σ₂' : Bool} (h : (σ₁, σ₁') ≠ (σ₂, σ₂')) :
    Disjoint (circPlaneTarget σ₁ σ₁') (circPlaneTarget σ₂ σ₂') := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  have key : ∀ (a σ τ : Bool) (t : ℝ), 0 < t → |16 * circSlack a σ t| < 2 →
      |16 * circSlack a τ t| < 2 → σ = τ := by
    intro a σ τ t ht h1 h2
    by_contra hne
    have hτ : τ = !σ := by cases σ <;> cases τ <;> simp_all
    have h1' : |circSlack a σ t| < 1 / 8 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h1
      linarith
    have hgt := circSlack_other_gt a σ ht h1'
    rw [← hτ] at hgt
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h2
    linarith [le_abs_self (circSlack a τ t)]
  exact h (Prod.ext (key false σ₁ σ₂ u.1 hu.1 hu.2.2.1 hu'.2.2.1)
    (key true σ₁' σ₂' u.2 hu.2.1 hu.2.2.2 hu'.2.2.2))

theorem circCorner_disjoint : Pairwise fun k k' : Fin 4 =>
    Disjoint (circCorner k).target (circCorner k').target := by
  intro k k' hkk'
  refine Set.disjoint_left.2 fun c hc hc' => ?_
  rw [circCorner, mem_circCornerChart_target] at hc hc'
  have hne : ((circCornerEquiv.symm k).1, (circCornerEquiv.symm k).1 ^^ (circCornerEquiv.symm k).2)
      ≠ ((circCornerEquiv.symm k').1,
        (circCornerEquiv.symm k').1 ^^ (circCornerEquiv.symm k').2) := by
    intro h
    apply hkk'
    apply circCornerEquiv.symm.injective
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [h1] at h2
    have aux : ∀ b e e' : Bool, (b ^^ e) = (b ^^ e') → e = e' := by decide
    exact Prod.ext h1 (aux _ _ _ h2)
  exact Set.disjoint_left.1 (circPlaneTarget_disjoint hne) hc hc'

/-- **First label**: `−x / 16` on the chart. -/
theorem circCorner_first (k : Fin 4) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    circDefining (circCornerFirst k) (circCorner k v) = -(1 / 16 * v.1) := by
  rw [circCornerFirst, circDefining_face, circFaceFn, circCorner,
    (circCoordL_circCornerChart _ _ hv).1, circSlack_circCornerInv _ _ hv.1]

/-- **Second label**: `−y / 16` on the chart. -/
theorem circCorner_second (k : Fin 4) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    circDefining (circCornerSecond k) (circCorner k v) = -(1 / 16 * v.2) := by
  rw [circCornerSecond, circDefining_face, circFaceFn, circCorner,
    (circCoordL_circCornerChart _ _ hv).2, circSlack_circCornerInv _ _ hv.2]

/-- **The other two defining functions are negative** on the chart. -/
theorem circCorner_other (k : Fin 4) (l : Fin 4) (v : ℝ × ℝ) (hl : l ≠ circCornerFirst k)
    (hl' : l ≠ circCornerSecond k) (hv : v ∈ rimBox 2) : circDefining l (circCorner k v) < 0 := by
  have small : ∀ (a σ : Bool) (s : ℝ), |s| < 2 →
      1 < circSlack a (!σ) (circCornerInv a σ s) := fun a σ s hs =>
    circSlack_other_gt a σ (circCornerInv_pos a σ hs) (by
      rw [circSlack_circCornerInv a σ hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
      linarith)
  rw [← circFaceEquiv.apply_symm_apply l] at hl hl' ⊢
  rw [circDefining_face]
  rw [circCornerFirst, circFaceEquiv.injective.ne_iff] at hl
  rw [circCornerSecond, circFaceEquiv.injective.ne_iff] at hl'
  rw [circCorner]
  generalize circCornerEquiv.symm k = p at hl hl' ⊢
  generalize circFaceEquiv.symm l = q at hl hl' ⊢
  obtain ⟨b, e⟩ := p
  obtain ⟨a, σ⟩ := q
  dsimp only at hl hl' ⊢
  have hc := circCoordL_circCornerChart b e hv
  rw [circFaceFn, neg_lt_zero]
  have aux : ∀ σ τ : Bool, σ ≠ τ → σ = !τ := by decide
  cases a
  · have hσ : σ = !b := aux σ b (fun h => hl (by rw [h]))
    rw [hc.1, hσ]
    linarith [small false b v.1 hv.1]
  · have hσ : σ = !(b ^^ e) := aux σ _ (fun h => hl' (by rw [h]))
    rw [hc.2, hσ]
    linarith [small true (b ^^ e) v.2 hv.2]

/-- **Every double zero is a chart centre.** -/
theorem circCorner_center (c : sphereCircleBaseOpens) (l l' : Fin 4) (hne : l ≠ l')
    (h : circDefining l c = 0) (h' : circDefining l' c = 0) : ∃ k, c = circCorner k (0, 0) := by
  have hax := circDefining_axes_ne hne h h'
  have hz := circFaceFn_eq_zero_iff.1 h
  have hz' := circFaceFn_eq_zero_iff.1 h'
  -- the `ψ`-side `σ` and the `r`-side `τ` of the double zero
  obtain ⟨σ, τ, hσ, hτ⟩ : ∃ σ τ : Bool, circCoordL false c.val = circEndVal σ ∧
      circCoordL true c.val = circEndVal τ := by
    rcases ha : (circFaceEquiv.symm l).1 with _ | _ <;>
      rcases ha' : (circFaceEquiv.symm l').1 with _ | _ <;> rw [ha, ha'] at hax <;>
      rw [ha] at hz <;> rw [ha'] at hz'
    · exact absurd rfl hax
    · exact ⟨_, _, hz, hz'⟩
    · exact ⟨_, _, hz', hz⟩
    · exact absurd rfl hax
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ rimBox 2 := ⟨by norm_num, by norm_num⟩
  refine ⟨circCornerEquiv (σ, σ ^^ τ), Subtype.ext ?_⟩
  have hx : (σ ^^ (σ ^^ τ)) = τ := by cases σ <;> cases τ <;> rfl
  rw [circCorner, Equiv.symm_apply_apply, circCornerChart_val _ _ h0, circPlaneMap]
  dsimp only
  rw [hx, circCornerInv_zero, circCornerInv_zero, ← hσ, ← hτ]
  exact (sphereCircleEquiv.symm_apply_apply c.val).symm

end GC.GraphManifold.Assembly.FC39P0
