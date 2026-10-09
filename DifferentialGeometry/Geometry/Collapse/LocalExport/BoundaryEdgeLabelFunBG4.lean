import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeSlimCoverBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeZeroFaceFunBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCuspFaceFunBG4

/-!
# BCF02 G4, group G5b: the uniform face function of a label (lane S-BCF02-G4b)

The three families of face functions of G2--G4 (zero labels, cusp labels, the two interval
functions of every arc) are put in ONE uniform pointwise form, indexed by the label type
`Kc.EdgeFaceLabel_BIFc` of the relative edge restriction:

* `labelRemoved_BG4 Kc ℓ` (open): `int Z_k`, `int core_b`, `f₃⁻¹ γ_j((lo e, hi e))` with
  `(lo, hi) = (0, 2/3)` for the end `e = false` and `(1/3, 1)` for `e = true` (so that the two
  open sub-arcs of an arc cover `γ_j((0, 1))`; the extra zero at `2/3` resp. `1/3` lies over
  `int_{M₁} S`, outside `M₂`);
* `labelZero_BG4 Kc ℓ`: the zero face, the cusp front, `f₃⁻¹{γ_j lo, γ_j hi}`;
* **`exists_labelFun_BG4`**: a function `h` of the edge base, continuous on `B₂`, with, for every
  `p ∈ X₂`, `h (f₂ p) < 0 ⟺ p ∈ labelRemoved`, `h (f₂ p) = 0 ⟺ p ∈ labelZero`,
  `0 < h (f₂ p) ⟺ p ∉ labelRemoved ∪ labelZero`; smooth on an open set of `H` around each zero in
  `B₂`; smooth / regular / transverse after `f₂` at every zero in `X₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The lower parameter of the sub-arc of the slim-end label of end `e`. -/
def slimLabelLo_BG4 : Bool → ℝ
  | false => 0
  | true => 1 / 3

/-- The upper parameter of the sub-arc of the slim-end label of end `e`. -/
def slimLabelHi_BG4 : Bool → ℝ
  | false => 2 / 3
  | true => 1

theorem slimLabelLo_nonneg_BG4 (e : Bool) : 0 ≤ slimLabelLo_BG4 e := by
  cases e <;> norm_num [slimLabelLo_BG4]

theorem slimLabelLo_lt_Hi_BG4 (e : Bool) : slimLabelLo_BG4 e < slimLabelHi_BG4 e := by
  cases e <;> norm_num [slimLabelLo_BG4, slimLabelHi_BG4]

theorem slimLabelHi_le_one_BG4 (e : Bool) : slimLabelHi_BG4 e ≤ 1 := by
  cases e <;> norm_num [slimLabelHi_BG4]

/-- The two open sub-arcs `(0, 2/3)` and `(1/3, 1)` cover `(0, 1)`. -/
theorem Ioo_zero_one_subset_labels_BG4 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ e : Bool, t ∈ Ioo (slimLabelLo_BG4 e) (slimLabelHi_BG4 e) := by
  by_cases h : t < 2 / 3
  · exact ⟨false, by simpa [slimLabelLo_BG4, slimLabelHi_BG4] using ⟨ht.1, h⟩⟩
  · exact ⟨true, by
      simp only [slimLabelLo_BG4, slimLabelHi_BG4]
      exact ⟨by linarith, ht.2⟩⟩

/-- The sub-arc of a label lies inside `(0, 1)`. -/
theorem Ioo_label_subset_BG4 (e : Bool) {t : ℝ} (ht : t ∈ Ioo (slimLabelLo_BG4 e)
    (slimLabelHi_BG4 e)) : t ∈ Ioo (0 : ℝ) 1 := by
  cases e
  · simp only [slimLabelLo_BG4, slimLabelHi_BG4] at ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  · simp only [slimLabelLo_BG4, slimLabelHi_BG4] at ht
    exact ⟨by linarith [ht.1], ht.2⟩

/-- **From whole fibres to points** (pure logic): if `R` and `P` are disjoint and the signs of `h`
are the whole-fibre memberships, then, for a point `p` of the fibre, they are the point
memberships. -/
theorem pointwise_sign_of_fibre_BG4 {W' H' : Type*} {X : Set W'} {f : W' → H'} {R P : Set W'}
    (hRP : Disjoint R P) {h : ℝ} {y : H'} {p : W'} (hp : p ∈ X ∩ f ⁻¹' {y})
    (h1 : h < 0 ↔ X ∩ f ⁻¹' {y} ⊆ R) (h2 : h = 0 ↔ X ∩ f ⁻¹' {y} ⊆ P)
    (h3 : 0 < h ↔ X ∩ f ⁻¹' {y} ⊆ (R ∪ P)ᶜ) :
    (h < 0 ↔ p ∈ R) ∧ (h = 0 ↔ p ∈ P) ∧ (0 < h ↔ p ∉ R ∪ P) := by
  rcases lt_trichotomy h 0 with hlt | heq | hgt
  · have hpR : p ∈ R := h1.mp hlt hp
    refine ⟨⟨fun _ => hpR, fun _ => hlt⟩, ⟨fun h0 => absurd h0 hlt.ne, fun hpP => ?_⟩,
      ⟨fun hg => absurd hg hlt.not_gt, fun hn => absurd (Or.inl hpR) hn⟩⟩
    exact absurd hpP (Set.disjoint_left.mp hRP hpR)
  · have hpP : p ∈ P := h2.mp heq hp
    exact ⟨⟨fun hl => absurd heq hl.ne, fun hpR => absurd hpR (Set.disjoint_right.mp hRP hpP)⟩,
      ⟨fun _ => hpP, fun _ => heq⟩,
      ⟨fun hg => absurd heq hg.ne', fun hn => absurd (Or.inr hpP) hn⟩⟩
  · have hpn : p ∉ R ∪ P := h3.mp hgt hp
    exact ⟨⟨fun hl => absurd hl hgt.not_gt, fun hpR => absurd (Or.inl hpR) hpn⟩,
      ⟨fun h0 => absurd h0 hgt.ne', fun hpP => absurd (Or.inr hpP) hpn⟩,
      ⟨fun _ => hpn, fun _ => hgt⟩⟩

namespace BoundaryGaf02ChainE

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The removed open set of a label**: `int Z_k`, `int core_b`, `f₃⁻¹ γ_j((lo e, hi e))`. -/
def labelRemoved_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain} (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    Kc.EdgeFaceLabel_BIFc → Set W.Carrier
  | .inl k => interior (C.toChain.actualZeroDomain_BIFc k)
  | .inr (.inl i) => interior (C.toChain.cuspCore_BIF i)
  | .inr (.inr je) => {q | C.toChain.stageMap 2 q ∈
      Kc.arc je.1 '' Ioo (slimLabelLo_BG4 je.2) (slimLabelHi_BG4 je.2)}

/-- **The zero set of a label**: the zero face, the cusp front, `f₃⁻¹{γ_j lo, γ_j hi}`. -/
def labelZero_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain} (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    Kc.EdgeFaceLabel_BIFc → Set W.Carrier
  | .inl k => C.toChain.actualZeroFace_BIFc k
  | .inr (.inl i) => C.toChain.cuspFront_BIF i
  | .inr (.inr je) => {q | C.toChain.stageMap 2 q = Kc.arc je.1 (slimLabelLo_BG4 je.2) ∨
      C.toChain.stageMap 2 q = Kc.arc je.1 (slimLabelHi_BG4 je.2)}

/-- `f₃ = π₃ ∘ f₂` on the actual slot. -/
theorem stageMap_two_eq_proj_BG4 (p : W.Carrier) :
    C.toChain.stageMap 2 p =
      (actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 1 p) :=
  ((stageProj_one_two_V2_BAUGD S (C.toChain.E p)).1).symm

variable {C} in
/-- An arc over `[lo, hi]` is the open sub-arc together with its two end points. -/
theorem arc_Icc_iff_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs} {j : Fin Kc.arcCount} {ta tb : ℝ} (hab : ta ≤ tb)
    {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} :
    z ∈ Kc.arc j '' Icc ta tb ↔
      z ∈ Kc.arc j '' Ioo ta tb ∨ z = Kc.arc j ta ∨ z = Kc.arc j tb := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · exact Or.inr (Or.inl (by rw [h]))
    · rcases ht.2.eq_or_lt with h' | h'
      · exact Or.inr (Or.inr (by rw [h']))
      · exact Or.inl ⟨t, ⟨h, h'⟩, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | rfl | rfl)
    · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    · exact ⟨ta, ⟨le_rfl, hab⟩, rfl⟩
    · exact ⟨tb, ⟨hab, le_rfl⟩, rfl⟩

/-- **The uniform face function of a label** (see the module docstring). -/
theorem exists_labelFun_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (ℓ : Kc.EdgeFaceLabel_BIFc) :
    ∃ h : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ,
      ContinuousOn h (Bs.base 1) ∧
      (∀ p ∈ Bs.source 1,
        (h (C.toChain.stageMap 1 p) < 0 ↔ p ∈ C.labelRemoved_BG4 Kc ℓ) ∧
        (h (C.toChain.stageMap 1 p) = 0 ↔ p ∈ C.labelZero_BG4 Kc ℓ) ∧
        (0 < h (C.toChain.stageMap 1 p) ↔
          p ∉ C.labelRemoved_BG4 Kc ℓ ∪ C.labelZero_BG4 Kc ℓ)) ∧
      (∀ y ∈ Bs.base 1, h y = 0 → ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧ ContDiffOn ℝ ∞ h O) ∧
      (∀ p ∈ Bs.source 1, h (C.toChain.stageMap 1 p) = 0 →
        ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => h (C.toChain.stageMap 1 q)) p ∧
        mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0 ∧
        (C.toChain.heightRatio p = 4 * Δ →
          Surjective fun v : TangentSpace W.model p =>
            (mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p v,
              mvfderiv W.model C.toChain.heightRatio p v))) := by
  classical
  have himg : ∀ p ∈ Bs.source 1, C.toChain.stageMap 1 p ∈ Bs.base 1 := fun p hp =>
    Bs.image_eq 1 ▸ mem_image_of_mem _ hp
  rcases ℓ with k | i | je
  · obtain ⟨h, hc, hsgn, hG, hsm⟩ := C.exists_zeroFaceFun_BG4 WF Z k
    have hdisj : Disjoint (interior (C.toChain.actualZeroDomain_BIFc k))
        (C.toChain.actualZeroFace_BIFc k) := by
      rw [← Z.frontier_eq k]
      exact Set.disjoint_left.mpr fun x hx hxf => hxf.2 hx
    have hunion : interior (C.toChain.actualZeroDomain_BIFc k) ∪
        C.toChain.actualZeroFace_BIFc k = C.toChain.actualZeroDomain_BIFc k := by
      rw [← Z.frontier_eq k, ← closure_eq_interior_union_frontier,
        (Z.isCompact_domain k).isClosed.closure_eq]
    refine ⟨h, hc, fun p hp => ?_, hG, hsm⟩
    obtain ⟨h1, h2, h3⟩ := hsgn _ (himg p hp)
    rw [← hunion] at h3
    exact pointwise_sign_of_fibre_BG4 (X := Bs.source 1) (f := C.toChain.stageMap 1) hdisj
      ⟨hp, rfl⟩ h1 h2 h3
  · obtain ⟨h, hc, hsgn, hG, hsm⟩ := C.exists_cuspFaceFun_BG4 WF hrd hrd4 hrdc hprem hθ i
    have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
    have hF : frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i :=
      (hcomp i).relative_frontier_eq
    have hdisj : Disjoint (interior (C.toChain.cuspCore_BIF i)) (C.toChain.cuspFront_BIF i) := by
      rw [← hF]
      exact Set.disjoint_left.mpr fun x hx hxf => hxf.2 hx
    have hCc : IsClosed (C.toChain.cuspCore_BIF i) := (hcomp i).compact_core.isClosed
    have hunion : interior (C.toChain.cuspCore_BIF i) ∪ C.toChain.cuspFront_BIF i =
        C.toChain.cuspCore_BIF i := by
      rw [← hF, ← closure_eq_interior_union_frontier, hCc.closure_eq]
    refine ⟨h, hc, fun p hp => ?_, hG, hsm⟩
    obtain ⟨h1, h2, h3⟩ := hsgn _ (himg p hp)
    rw [← hunion] at h3
    exact pointwise_sign_of_fibre_BG4 (X := Bs.source 1) (f := C.toChain.stageMap 1) hdisj
      ⟨hp, rfl⟩ h1 h2 h3
  · obtain ⟨h, hc, hsgn, hG, hsm⟩ := C.exists_slimIntervalFun_BG4 WF Kc je.1
      (slimLabelLo_nonneg_BG4 je.2) (slimLabelLo_lt_Hi_BG4 je.2) (slimLabelHi_le_one_BG4 je.2)
    refine ⟨h, hc, fun p hp => ?_, hG, hsm⟩
    obtain ⟨h1, h2, h3⟩ := hsgn _ (himg p hp)
    rw [← C.stageMap_two_eq_proj_BG4 p] at h1 h2 h3
    refine ⟨h1, h2, ?_⟩
    rw [h3]
    change C.toChain.stageMap 2 p ∉ Kc.arc je.1 '' Icc (slimLabelLo_BG4 je.2)
      (slimLabelHi_BG4 je.2) ↔ ¬ (C.toChain.stageMap 2 p ∈ Kc.arc je.1 ''
        Ioo (slimLabelLo_BG4 je.2) (slimLabelHi_BG4 je.2) ∨
        C.toChain.stageMap 2 p = Kc.arc je.1 (slimLabelLo_BG4 je.2) ∨
        C.toChain.stageMap 2 p = Kc.arc je.1 (slimLabelHi_BG4 je.2))
    rw [arc_Icc_iff_BG4 (C := C) (Kc := Kc) (j := je.1) (slimLabelLo_lt_Hi_BG4 je.2).le]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
