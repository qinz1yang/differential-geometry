import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreCollarAvoidance

/-!
# FC42 packet "port shrink": a recorded shrink of the ports keeps the new zero level away

Review 42 §5.1–§5.2 and the lead disposition of item 5(a). V4 does not keep the new zero level
`Z_R = val '' proj⁻¹{rounding = 0}` of the circle region away from the CLOSURE of the external collar
targets: for `W = T² × [0, 3]` with ports `T² × [0, 1)`, `T² × (2, 3]` and circle region
`T² × [1, 2]`, the torus `T² × {1}` lies in the closure of a port. The assembly therefore works over
a RECORDED SHRINK `E.shrink δ` of the ports (the tree's `BoundaryTori.shrink`,
`Seifert/CollarGermAdapter.lean`: collars `(t, s) ↦ E.collar i (t, δ s)`, same torus maps and the same
boundary image).

* `CircleRegion.roundedLevel` (= `Z_R`): compact, inside `W.interior`, inside the rounded region, and
  equal to the zero level of `roundedFunction` on `domain`;
* `BoundaryTori.closure_shrink_target_subset`: the closure of a collar target shrunk to width `δ'`
  lies in the collar target shrunk to any larger width `δ ≤ 1`;
* `BoundaryTori.exists_shrink_closure_disjoint`: for a compact set inside the interior, some shrink
  has collar-target CLOSURES disjoint from it (from the tree's
  `BoundaryTori.exists_shrink_avoiding_compact`, `Closure/FibreCollarAvoidance.lean`);
* `DecompositionCertificate.shrinkPorts`: the transport of a V4 certificate to the shrunk ports — every
  field mentioning the ports only gets weaker, `face_external` is unchanged (same torus maps);
* `DecompositionCertificate.exists_shrinkPorts_buffer` (`ExternalBuffer` for `E.shrink δ`): for small
  `δ` the closures of the shrunk collar targets miss `Z_R`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
  Manifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## The new zero level `Z_R` -/

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- The new zero level `Z_R = val '' proj⁻¹{rounding = 0}` of the rounded circle region. -/
def roundedLevel : Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' {b | R.rounding b = 0})

theorem isCompact_roundedLevel : IsCompact R.roundedLevel := by
  have hK : IsCompact {b | R.rounding b = 0} :=
    R.rounded_compact.of_isClosed_subset
      (isClosed_eq R.rounding_smooth.continuous continuous_const) fun b hb => le_of_eq hb
  exact (R.isCompact_proj_preimage hK).image continuous_subtype_val

theorem roundedLevel_subset_rounded : R.roundedLevel ⊆ R.rounded :=
  image_mono fun _ hx => le_of_eq hx

theorem roundedLevel_subset_domain : R.roundedLevel ⊆ (R.domain : Set W.Carrier) :=
  R.roundedLevel_subset_rounded.trans R.rounded_subset_domain

theorem roundedLevel_subset_interior : R.roundedLevel ⊆ (W.interior : Set W.Carrier) :=
  R.roundedLevel_subset_rounded.trans R.rounded_subset_interior

theorem roundedLevel_eq : R.roundedLevel = {x | x ∈ R.domain ∧ R.roundedFunction x = 0} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (R.roundedFunction_apply y).trans hy⟩
  · rintro ⟨hx, h0⟩
    exact ⟨⟨x, hx⟩, (R.roundedFunction_apply ⟨x, hx⟩).symm.trans h0, rfl⟩

end CircleRegion

theorem halfSpaceOneLift_coord_eq_max (s : ℝ) : (halfSpaceOneLift s).1 0 = max s 0 :=
  rfl

end GC.GraphManifold.Assembly

/-! ## Closures of shrunk collar targets -/

namespace GC.GraphManifold.BoundaryTori

open GC.GraphManifold.Assembly

variable {C : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori C n)

/-- The closure of the collar target shrunk to width `δ'` lies in the collar target shrunk to any
larger width `δ ≤ 1`. -/
theorem closure_shrink_target_subset {δ' δ : ℝ} (hδ' : 0 < δ') (hδ'δ : δ' < δ) (hδ1 : δ ≤ 1)
    (i : Fin n) :
    closure ((E.shrink hδ' (hδ'δ.le.trans hδ1)).collar i).target ⊆
      ((E.shrink (hδ'.trans hδ'δ) hδ1).collar i).target := by
  have hδ : 0 < δ := hδ'.trans hδ'δ
  set c := E.collar i with hc
  have hsrc : c.source = halfCollarSource := E.source_eq i
  have hlift : ContinuousOn halfSpaceOneLift (Icc 0 δ') :=
    contMDiffOn_halfSpaceOneLift.continuousOn.mono Icc_subset_Ici_self
  let A : Set (Torus × EuclideanHalfSpace 1) := univ ×ˢ (halfSpaceOneLift '' Icc 0 δ')
  have hA : IsCompact A := isCompact_univ.prod (isCompact_Icc.image_of_continuousOn hlift)
  have hAsrc : A ⊆ c.source := by
    rintro ⟨t, _⟩ ⟨-, s, hs, rfl⟩
    rw [hsrc]
    change (halfSpaceOneLift s).1 0 < 1
    rw [halfSpaceOneLift_coord_eq_max, max_eq_left hs.1]
    exact hs.2.trans_lt (hδ'δ.trans_le hδ1)
  have hK : IsCompact (c '' A) := hA.image_of_continuousOn (c.contMDiffOn.continuousOn.mono hAsrc)
  -- the small target lies in `c '' A`
  have h1 : ((E.shrink hδ' (hδ'δ.le.trans hδ1)).collar i).target ⊆ c '' A := by
    intro y hy
    set S := (E.shrink hδ' (hδ'δ.le.trans hδ1)).collar i
    have hp : S.symm y ∈ S.source := S.map_target hy
    have hp' : (S.symm y).2.1 0 < 1 := by
      rw [show S.source = halfCollarSource from (E.shrink hδ' (hδ'δ.le.trans hδ1)).source_eq i]
        at hp
      exact hp
    have h0 : 0 ≤ (S.symm y).2.1 0 := (S.symm y).2.2
    refine ⟨((S.symm y).1, halfSpaceOneLift (δ' * (S.symm y).2.1 0)),
      ⟨mem_univ _, _, ⟨mul_nonneg hδ'.le h0, ?_⟩, rfl⟩, ?_⟩
    · nlinarith
    · conv_rhs => rw [← S.right_inv hy]
      rfl
  -- `c '' A` lies in the larger target
  have h2 : c '' A ⊆ ((E.shrink hδ hδ1).collar i).target := by
    rintro _ ⟨⟨t, _⟩, ⟨-, s, hs, rfl⟩, rfl⟩
    set L := (E.shrink hδ hδ1).collar i
    have hq : (t, halfSpaceOneLift (s / δ)) ∈ L.source := by
      rw [show L.source = halfCollarSource from (E.shrink hδ hδ1).source_eq i]
      change (halfSpaceOneLift (s / δ)).1 0 < 1
      rw [halfSpaceOneLift_coord_eq_max, max_eq_left (div_nonneg hs.1 hδ.le), div_lt_one hδ]
      exact hs.2.trans_lt hδ'δ
    have hval : L (t, halfSpaceOneLift (s / δ)) = c (t, halfSpaceOneLift s) := by
      change c (t, halfSpaceOneLift (δ * (halfSpaceOneLift (s / δ)).1 0)) = _
      rw [halfSpaceOneLift_coord_eq_max, max_eq_left (div_nonneg hs.1 hδ.le),
        mul_div_cancel₀ s hδ.ne']
    rw [← hval]
    exact L.map_source hq
  exact (closure_minimal h1 hK.isClosed).trans h2

/-- **External buffer.** For a compact set inside the interior, the collar-target closures of some
shrink of the ports avoid it. -/
theorem exists_shrink_closure_disjoint {K : Set C.Carrier} (hK : IsCompact K)
    (hKI : K ⊆ C.interior) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      ∀ i, Disjoint (closure ((E.shrink hδ hδ1).collar i).target) K := by
  obtain ⟨δ, hδ, hδ1, havoid⟩ := E.exists_shrink_avoiding_compact hK hKI
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hδ2δ : δ / 2 < δ := half_lt_self hδ
  refine ⟨δ / 2, hδ2, hδ2δ.le.trans hδ1, fun i => ?_⟩
  refine Disjoint.mono_left (E.closure_shrink_target_subset hδ2 hδ2δ hδ1 i) ?_
  rw [Set.disjoint_left]
  intro y hy hyK
  set L := (E.shrink hδ hδ1).collar i
  have hp : L.symm y ∈ L.source := L.map_target hy
  have hp' : L.symm y ∈ halfCollarSource := by
    rwa [show L.source = halfCollarSource from (E.shrink hδ hδ1).source_eq i] at hp
  apply havoid i (L.symm y) hp'
  have he : L (L.symm y) = y := L.right_inv hy
  convert hyK using 1

end GC.GraphManifold.BoundaryTori

namespace GC.GraphManifold.Assembly

/-! ## The certificate over the shrunk ports -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **Transport of a V4 certificate to shrunk ports.** All other data are unchanged; the port
fields only get weaker (smaller collar targets), and `face_external` is unchanged (same torus maps). -/
def shrinkPorts (D : DecompositionCertificate W E) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    DecompositionCertificate W (E.shrink hδ hδ1) :=
  { D with
    external_exhausted := by rw [BoundaryTori.shrink_image]; exact D.external_exhausted
    external_owned := fun i =>
      (shrinkHalfCollar_target_subset hδ (E.collar i)).trans (D.external_owned i)
    face_external := fun f i h => by
      rw [BoundaryTori.shrink_torusMap]
      exact D.face_external f i h
    external_region_disjoint := fun i =>
      (D.external_region_disjoint i).mono_left (shrinkHalfCollar_target_subset hδ (E.collar i))
    external_handle_disjoint := fun i h =>
      (D.external_handle_disjoint i h).mono_left (shrinkHalfCollar_target_subset hδ (E.collar i))
    external_edgeCircle_disjoint := fun i e =>
      (D.external_edgeCircle_disjoint i e).mono_left
        (shrinkHalfCollar_target_subset hδ (E.collar i))
    external_torusSeam_disjoint := fun i c =>
      (D.external_torusSeam_disjoint i c).mono_left
        (shrinkHalfCollar_target_subset hδ (E.collar i))
    external_sphereSeam_disjoint := fun i c =>
      (D.external_sphereSeam_disjoint i c).mono_left
        (shrinkHalfCollar_target_subset hδ (E.collar i))
    rim_external_disjoint := fun h b i =>
      (D.rim_external_disjoint h b i).mono_right (shrinkHalfCollar_target_subset hδ (E.collar i)) }

variable (D : DecompositionCertificate W E) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)

@[simp] theorem shrinkPorts_circ : (D.shrinkPorts hδ hδ1).circ = D.circ := rfl

@[simp] theorem shrinkPorts_vertexCount : (D.shrinkPorts hδ hδ1).vertexCount = D.vertexCount := rfl

@[simp] theorem shrinkPorts_handleCount : (D.shrinkPorts hδ hδ1).handleCount = D.handleCount := rfl

@[simp] theorem shrinkPorts_torusSeamCount :
    (D.shrinkPorts hδ hδ1).torusSeamCount = D.torusSeamCount := rfl

@[simp] theorem shrinkPorts_sphereSeamCount :
    (D.shrinkPorts hδ hδ1).sphereSeamCount = D.sphereSeamCount := rfl

theorem shrinkPorts_vertex (k : Fin D.vertexCount) : (D.shrinkPorts hδ hδ1).vertex k = D.vertex k :=
  rfl

theorem shrinkPorts_externalOwner (i : Fin n) :
    (D.shrinkPorts hδ hδ1).externalOwner i = D.externalOwner i :=
  rfl

/-- **`ExternalBuffer` for a shrink of the ports.** For some width `δ`, the closures of the shrunk
external collar targets miss the new zero level `Z_R` of the circle region. -/
theorem exists_shrinkPorts_buffer :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      ∀ i, Disjoint (closure ((E.shrink hδ hδ1).collar i).target)
        (D.shrinkPorts hδ hδ1).circ.roundedLevel :=
  E.exists_shrink_closure_disjoint D.circ.isCompact_roundedLevel
    D.circ.roundedLevel_subset_interior

end DecompositionCertificate

end GC.GraphManifold.Assembly
