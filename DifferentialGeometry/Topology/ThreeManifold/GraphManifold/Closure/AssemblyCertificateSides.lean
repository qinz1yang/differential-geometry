import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The FC39 certificate: seam sides and the protection of the operation supports

Structural lemmas on `DecompositionCertificate W E` (`AssemblyCertificate.lean`, V2 review item 3, D4):

* **Seam sides.** `torusSideSet c b` is the side set of torus seam `c` (the circle region for `none`,
  the vertex image for `some k`). Each signed half collar lies in its side set; for a `none` side the
  half collar lies in the circle region (`collar_mem_region_of_torusSide_eq_none`), for a `some k`
  side in the image of vertex `k`; the seam torus lies in both side sets; a seam with two `none`
  sides has its whole collar in the circle region. The same for sphere seams.
* **Protection.** The operation supports are the rim charts (rounding) and the sphere seam collars
  (sphere surgery); the protected sets are the external collars and the whole torus seam collars.
  Each operation support is disjoint from each protected set (`disjoint_operationSupport_protected`),
  and the external collars avoid the circle region, the handles, the circle-base edges and the torus
  seam collars.
* **Rounding supports.** The rounding support `circ.roundingSupport k` of a corner (the preimage of
  its corner chart target) is the target of the rim chart of the handle end with that corner
  (`roundingSupport_handleCorner`): the inclusion `⊆` uses that each fibre of the circle region is a
  connected circle (the trivialization) met by the rim chart target exactly in a compact circle.
  Hence every rounding support is protected as well (`disjoint_roundingSupport_*`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The union of the external collar targets of a port family. -/
def externalCollarSet {W : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori W n) : Set W.Carrier :=
  ⋃ i, (E.collar i).target

/-- The signed half collar of side `b` (`b = true`: `s ≤ 0`; `b = false`: `0 ≤ s`). -/
def signedHalfSource (b : Bool) : Set (Torus × ℝ) :=
  {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2}

theorem zero_mem_signedHalfSource (t : Torus) (b : Bool) : (t, (0 : ℝ)) ∈ signedHalfSource b := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  cases b <;> simp

theorem signedCollarSource_eq_union :
    signedCollarSource = signedHalfSource true ∪ signedHalfSource false := by
  ext p
  constructor
  · intro hp
    rcases le_total p.2 0 with h | h
    · exact Or.inl ⟨hp, by simpa using h⟩
    · exact Or.inr ⟨hp, by simpa using h⟩
  · rintro (h | h) <;> exact h.1

namespace CircleRegion

variable {W : CompactCarrier.{u}}

/-- The fibre of the circle region through a point of its domain is connected: through the
trivialization at its base point it is the image of a circle. -/
theorem isPreconnected_fibre (R : CircleRegion W) (y : R.domain) :
    IsPreconnected (Subtype.val '' (R.proj ⁻¹' {R.proj y})) := by
  have hb₀ : R.proj y ∈ R.neighborhood (R.proj y) := R.mem_neighborhood _
  have hm : Continuous fun θ : Circle =>
      (((R.trivialization (R.proj y)).symm (⟨R.proj y, hb₀⟩, θ) : _) : R.domain).val :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      ((R.trivialization _).symm.continuous.comp (continuous_const.prodMk continuous_id)))
  convert (isConnected_range hm).isPreconnected using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwU : w ∈ TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj y)) := by
      rw [TopologicalSpace.Opens.mem_comap, show R.proj w = R.proj y from hw]
      exact hb₀
    refine ⟨(R.trivialization (R.proj y) ⟨w, hwU⟩).2, ?_⟩
    have h1 : (R.trivialization (R.proj y) ⟨w, hwU⟩).1 = ⟨R.proj y, hb₀⟩ :=
      Subtype.ext ((R.projection_trivialization _ ⟨w, hwU⟩).trans hw)
    have h2 : R.trivialization (R.proj y) ⟨w, hwU⟩ =
        (⟨R.proj y, hb₀⟩, (R.trivialization (R.proj y) ⟨w, hwU⟩).2) :=
      Prod.ext h1 rfl
    change (((R.trivialization (R.proj y)).symm
      (⟨R.proj y, hb₀⟩, (R.trivialization (R.proj y) ⟨w, hwU⟩).2) : _) : R.domain).val = w.val
    rw [← h2, Diffeomorph.symm_apply_apply]
  · rintro ⟨θ, rfl⟩
    refine ⟨_, ?_, rfl⟩
    have h1 := R.projection_trivialization (R.proj y)
      ((R.trivialization (R.proj y)).symm (⟨R.proj y, hb₀⟩, θ))
    rw [Diffeomorph.apply_symm_apply] at h1
    exact h1.symm

/-- A partial diffeomorphism `Φ` from `Circle × (ℝ × ℝ)` into `W` lying over a chart `χ` of the
base (`proj ∘ Φ = χ ∘ snd`, with source `χ.source` in the second factor) has as target the whole
preimage of `χ.target`: each fibre over `χ.target` is connected and meets `Φ.target` in the compact
circle `Φ (Circle × {v})`. -/
theorem preimage_target_subset_target (R : CircleRegion W)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) R.Base ∞)
    (Φ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    (hsource : ∀ p, p ∈ Φ.source ↔ p.2 ∈ χ.source)
    (hproj : ∀ p, p ∈ Φ.source → ∃ hx : Φ p ∈ R.domain, R.proj ⟨Φ p, hx⟩ = χ p.2) :
    Subtype.val '' (R.proj ⁻¹' χ.target) ⊆ Φ.target := by
  rintro _ ⟨y, hy, rfl⟩
  have hvs : χ.symm (R.proj y) ∈ χ.source := χ.map_target hy
  have hχv : χ (χ.symm (R.proj y)) = R.proj y := χ.right_inv hy
  have hsrc : ∀ θ : Circle, (θ, χ.symm (R.proj y)) ∈ Φ.source := fun θ => (hsource _).2 hvs
  have hg : Continuous fun θ : Circle => Φ (θ, χ.symm (R.proj y)) :=
    Φ.contMDiffOn.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) hsrc
  -- the target meets the fibre exactly in the circle `range g`
  have hFT : Subtype.val '' (R.proj ⁻¹' {R.proj y}) ∩ Φ.target ⊆
      range fun θ : Circle => Φ (θ, χ.symm (R.proj y)) := by
    rintro z ⟨⟨w, hw, rfl⟩, hz⟩
    have hp := Φ.map_target hz
    have hpz : Φ (Φ.symm w.val) = w.val := Φ.right_inv hz
    obtain ⟨hx, hpr⟩ := hproj _ hp
    have hwx : (⟨Φ (Φ.symm w.val), hx⟩ : R.domain) = w := Subtype.ext hpz
    have hpr' : R.proj w = χ (Φ.symm w.val).2 := (congrArg R.proj hwx).symm.trans hpr
    have heq : (Φ.symm w.val).2 = χ.symm (R.proj y) :=
      χ.injOn ((hsource _).1 hp) hvs ((hpr'.symm.trans (hw : R.proj w = R.proj y)).trans hχv.symm)
    refine ⟨(Φ.symm w.val).1, ?_⟩
    change Φ ((Φ.symm w.val).1, χ.symm (R.proj y)) = w.val
    rw [← heq]
    exact hpz
  have hgT : (range fun θ : Circle => Φ (θ, χ.symm (R.proj y))) ⊆ Φ.target := by
    rintro _ ⟨θ, rfl⟩
    exact Φ.map_source (hsrc θ)
  have hg1 : Φ (1, χ.symm (R.proj y)) ∈ Subtype.val '' (R.proj ⁻¹' {R.proj y}) := by
    obtain ⟨hx, hpr⟩ := hproj _ (hsrc 1)
    refine ⟨⟨_, hx⟩, ?_, rfl⟩
    change R.proj ⟨_, hx⟩ = R.proj y
    rw [hpr, hχv]
  by_contra hyT
  obtain ⟨z, hzF, hz⟩ := R.isPreconnected_fibre y Φ.target
    (range fun θ : Circle => Φ (θ, χ.symm (R.proj y)))ᶜ Φ.open_target
    (isCompact_range hg).isClosed.isOpen_compl (fun z _ => by
      by_cases hzt : z ∈ Φ.target
      · exact Or.inl hzt
      · exact Or.inr fun hzg => hzt (hgT hzg))
    ⟨_, hg1, hgT ⟨1, rfl⟩⟩ ⟨y.val, ⟨y, rfl, rfl⟩, fun hyg => hyT (hgT hyg)⟩
  exact hz.2 (hFT ⟨hzF, hz.1⟩)

end CircleRegion

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-! ## Torus seam sides -/

/-- The side set of torus seam `c` on side `b`: the circle region for `none`, the image of the vertex
for `some k`. -/
def torusSideSet (c : Fin D.torusSeamCount) (b : Bool) : Set W.Carrier :=
  (D.torusSide c b).elim D.circ.region fun k => (D.vertex k).image

theorem torusSideSet_of_eq_none {c : Fin D.torusSeamCount} {b : Bool}
    (h : D.torusSide c b = none) : D.torusSideSet c b = D.circ.region := by
  simp [torusSideSet, h]

theorem torusSideSet_of_eq_some {c : Fin D.torusSeamCount} {b : Bool} {k : Fin D.vertexCount}
    (h : D.torusSide c b = some k) : D.torusSideSet c b = (D.vertex k).image := by
  simp [torusSideSet, h]

theorem collar_mem_torusSideSet_true (c : Fin D.torusSeamCount) (t : Torus) {s : ℝ}
    (hs₁ : -1 < s) (hs₀ : s ≤ 0) : (D.torusSeam c).collar (t, s) ∈ D.torusSideSet c true :=
  D.torusSide_neg c t s hs₁ hs₀

theorem collar_mem_torusSideSet_false (c : Fin D.torusSeamCount) (t : Torus) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s < 1) : (D.torusSeam c).collar (t, s) ∈ D.torusSideSet c false :=
  D.torusSide_pos c t s hs₀ hs₁

/-- Each signed half collar of a torus seam lies in its side set. -/
theorem image_signedHalfSource_subset (c : Fin D.torusSeamCount) (b : Bool) :
    (D.torusSeam c).collar '' signedHalfSource b ⊆ D.torusSideSet c b := by
  rintro _ ⟨p, ⟨⟨hp₁, hp₂⟩, hpb⟩, rfl⟩
  cases b
  · exact D.collar_mem_torusSideSet_false c p.1 hpb hp₂
  · exact D.collar_mem_torusSideSet_true c p.1 hp₁ hpb

/-- **`none` side.** A torus seam side labelled `none` has its half collar in the circle region. -/
theorem collar_mem_region_of_torusSide_eq_none {c : Fin D.torusSeamCount} {b : Bool}
    (hc : D.torusSide c b = none) {p : Torus × ℝ} (hp : p ∈ signedHalfSource b) :
    (D.torusSeam c).collar p ∈ D.circ.region := by
  rw [← D.torusSideSet_of_eq_none hc]
  exact D.image_signedHalfSource_subset c b (mem_image_of_mem _ hp)

/-- A torus seam side labelled `some k` has its half collar in the image of vertex `k`. -/
theorem collar_mem_vertex_of_torusSide_eq_some {c : Fin D.torusSeamCount} {b : Bool}
    {k : Fin D.vertexCount} (hc : D.torusSide c b = some k) {p : Torus × ℝ}
    (hp : p ∈ signedHalfSource b) : (D.torusSeam c).collar p ∈ (D.vertex k).image := by
  rw [← D.torusSideSet_of_eq_some hc]
  exact D.image_signedHalfSource_subset c b (mem_image_of_mem _ hp)

/-- The seam torus lies in both side sets. -/
theorem seamTorus_subset_torusSideSet (c : Fin D.torusSeamCount) (b : Bool) :
    range (fun t => (D.torusSeam c).collar (t, 0)) ⊆ D.torusSideSet c b := by
  rintro _ ⟨t, rfl⟩
  exact D.image_signedHalfSource_subset c b (mem_image_of_mem _ (zero_mem_signedHalfSource t b))

/-- A torus seam with two `none` sides lies, with its whole collar, in the circle region. -/
theorem collar_target_subset_region {c : Fin D.torusSeamCount} (htrue : D.torusSide c true = none)
    (hfalse : D.torusSide c false = none) : (D.torusSeam c).collar.target ⊆ D.circ.region := by
  rw [← (D.torusSeam c).collar.toPartialEquiv.image_source_eq_target, (D.torusSeam c).source_eq,
    signedCollarSource_eq_union, image_union]
  rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
  · exact D.collar_mem_region_of_torusSide_eq_none htrue hp
  · exact D.collar_mem_region_of_torusSide_eq_none hfalse hp

/-! ## Sphere seam sides -/

/-- The sphere seam sphere lies in both side vertices. -/
theorem sphereSeam_zero_mem (c : Fin D.sphereSeamCount) (b : Bool) (z : ClosureSphere.{u}) :
    (D.sphereSeam c).collar (z, 0) ∈ (D.vertex (D.sphereSide c b)).image := by
  cases b
  · exact D.sphereSide_pos c z 0 le_rfl zero_lt_one
  · exact D.sphereSide_neg c z 0 le_rfl (by norm_num)

/-- The sphere seam sphere lies in the intersection of its two side vertices. -/
theorem sphereSeam_sphere_subset_inter (c : Fin D.sphereSeamCount) :
    range (fun z => (D.sphereSeam c).collar (z, 0)) ⊆
      (D.vertex (D.sphereSide c true)).image ∩ (D.vertex (D.sphereSide c false)).image := by
  rintro _ ⟨z, rfl⟩
  exact ⟨D.sphereSeam_zero_mem c true z, D.sphereSeam_zero_mem c false z⟩

/-! ## Operation supports and protected sets -/

/-- The rounding support: the union of the rim chart targets. -/
def rimSupport : Set W.Carrier :=
  ⋃ (h : Fin D.handleCount) (b : Bool), (D.rimChart h b).target

/-- The sphere surgery support: the union of the sphere seam collar targets. -/
def sphereSupport : Set W.Carrier :=
  ⋃ c, (D.sphereSeam c).collar.target

/-- The union of the whole torus seam collar targets. -/
def torusCollarSet : Set W.Carrier :=
  ⋃ c, (D.torusSeam c).collar.target

theorem disjoint_rimSupport_externalCollarSet : Disjoint D.rimSupport (externalCollarSet E) :=
  disjoint_iUnion_left.2 fun h => disjoint_iUnion_left.2 fun b => disjoint_iUnion_right.2 fun i =>
    D.rim_external_disjoint h b i

theorem disjoint_rimSupport_torusCollarSet : Disjoint D.rimSupport D.torusCollarSet :=
  disjoint_iUnion_left.2 fun h => disjoint_iUnion_left.2 fun b => disjoint_iUnion_right.2 fun c =>
    D.rim_torusSeam_disjoint h b c

theorem disjoint_rimSupport_sphereSupport : Disjoint D.rimSupport D.sphereSupport :=
  disjoint_iUnion_left.2 fun h => disjoint_iUnion_left.2 fun b => disjoint_iUnion_right.2 fun c =>
    D.rim_sphereSeam_disjoint h b c

theorem disjoint_sphereSupport_externalCollarSet :
    Disjoint D.sphereSupport (externalCollarSet E) :=
  disjoint_iUnion_left.2 fun c => disjoint_iUnion_right.2 fun i =>
    (D.external_sphereSeam_disjoint i c).symm

theorem disjoint_sphereSupport_torusCollarSet : Disjoint D.sphereSupport D.torusCollarSet :=
  disjoint_iUnion_left.2 fun c => disjoint_iUnion_right.2 fun d => D.sphere_torus_seam_disjoint c d

theorem disjoint_externalCollarSet_torusCollarSet :
    Disjoint (externalCollarSet E) D.torusCollarSet :=
  disjoint_iUnion_left.2 fun i => disjoint_iUnion_right.2 fun c => D.external_torusSeam_disjoint i c

/-- **Protection.** Every operation support (rounding = rim charts, sphere surgery = sphere seam
collars) is disjoint from every protected set (external collars and whole torus seam collars). -/
theorem disjoint_operationSupport_protected :
    Disjoint (D.rimSupport ∪ D.sphereSupport) (externalCollarSet E ∪ D.torusCollarSet) :=
  disjoint_union_left.2
    ⟨disjoint_union_right.2 ⟨D.disjoint_rimSupport_externalCollarSet,
        D.disjoint_rimSupport_torusCollarSet⟩,
      disjoint_union_right.2 ⟨D.disjoint_sphereSupport_externalCollarSet,
        D.disjoint_sphereSupport_torusCollarSet⟩⟩

theorem disjoint_externalCollarSet_region : Disjoint (externalCollarSet E) D.circ.region :=
  disjoint_iUnion_left.2 fun i => D.external_region_disjoint i

theorem disjoint_externalCollarSet_handles :
    Disjoint (externalCollarSet E) (⋃ h, range (D.handle h).map) :=
  disjoint_iUnion_left.2 fun i => disjoint_iUnion_right.2 fun h => D.external_handle_disjoint i h

theorem disjoint_externalCollarSet_edgeCircles :
    Disjoint (externalCollarSet E) (⋃ e, range (D.edgeCircle e).piece.map) :=
  disjoint_iUnion_left.2 fun i => disjoint_iUnion_right.2 fun e =>
    D.external_edgeCircle_disjoint i e

theorem disjoint_sphereSupport_region : Disjoint D.sphereSupport D.circ.region :=
  disjoint_iUnion_left.2 fun c => D.sphereSeam_region_disjoint c

theorem disjoint_sphereSupport_handles :
    Disjoint D.sphereSupport (⋃ h, range (D.handle h).map) :=
  disjoint_iUnion_left.2 fun c => disjoint_iUnion_right.2 fun h => D.sphereSeam_handle_disjoint c h

/-! ## Rounding supports are rim chart targets -/

theorem rimChart_target_subset_roundingSupport (h : Fin D.handleCount) (b : Bool) :
    (D.rimChart h b).target ⊆ D.circ.roundingSupport (D.handleCorner h b) := by
  intro z hz
  have hp := (D.rimChart h b).map_target hz
  have hpz : D.rimChart h b ((D.rimChart h b).symm z) = z := (D.rimChart h b).right_inv hz
  obtain ⟨hx, hproj⟩ := D.rim_proj h b _ hp
  refine ⟨⟨_, hx⟩, ?_, hpz⟩
  change D.circ.proj ⟨_, hx⟩ ∈ (D.circ.cornerChart (D.handleCorner h b)).target
  rw [hproj]
  apply (D.circ.cornerChart (D.handleCorner h b)).map_source
  rw [D.circ.cornerChart_source]
  exact D.rim_source h b |>.1 hp

/-- **Rounding support = rim chart target.** -/
theorem roundingSupport_handleCorner (h : Fin D.handleCount) (b : Bool) :
    D.circ.roundingSupport (D.handleCorner h b) = (D.rimChart h b).target := by
  refine Subset.antisymm ?_ (D.rimChart_target_subset_roundingSupport h b)
  refine D.circ.preimage_target_subset_target _ _ (fun p => ?_) (D.rim_proj h b)
  rw [D.circ.cornerChart_source]
  exact D.rim_source h b

/-- Every corner's rounding support is the target of the rim chart of its handle end. -/
theorem exists_roundingSupport_eq_rimChart_target (k : Fin D.circ.cornerCount) :
    ∃ h b, D.handleCorner h b = k ∧ D.circ.roundingSupport k = (D.rimChart h b).target := by
  obtain ⟨⟨h, b⟩, hk⟩ := D.handleCorner_bijective.2 k
  exact ⟨h, b, hk, hk ▸ D.roundingSupport_handleCorner h b⟩

theorem iUnion_roundingSupport : (⋃ k, D.circ.roundingSupport k) = D.rimSupport := by
  apply Subset.antisymm
  · refine iUnion_subset fun k => ?_
    obtain ⟨h, b, -, hk⟩ := D.exists_roundingSupport_eq_rimChart_target k
    rw [hk]
    exact subset_iUnion₂ (s := fun h b => (D.rimChart h b).target) h b
  · refine iUnion₂_subset fun h b => ?_
    rw [← D.roundingSupport_handleCorner h b]
    exact subset_iUnion (fun k => D.circ.roundingSupport k) _

theorem roundingSupport_subset_rimSupport (k : Fin D.circ.cornerCount) :
    D.circ.roundingSupport k ⊆ D.rimSupport :=
  D.iUnion_roundingSupport ▸ subset_iUnion (fun k => D.circ.roundingSupport k) k

/-- **Protection of the rounding supports** from the external collars. -/
theorem disjoint_roundingSupport_externalCollarSet (k : Fin D.circ.cornerCount) :
    Disjoint (D.circ.roundingSupport k) (externalCollarSet E) :=
  D.disjoint_rimSupport_externalCollarSet.mono_left (D.roundingSupport_subset_rimSupport k)

/-- **Protection of the rounding supports** from the whole torus seam collars. -/
theorem disjoint_roundingSupport_torusCollarSet (k : Fin D.circ.cornerCount) :
    Disjoint (D.circ.roundingSupport k) D.torusCollarSet :=
  D.disjoint_rimSupport_torusCollarSet.mono_left (D.roundingSupport_subset_rimSupport k)

/-- The rounding supports avoid the sphere surgery supports. -/
theorem disjoint_roundingSupport_sphereSupport (k : Fin D.circ.cornerCount) :
    Disjoint (D.circ.roundingSupport k) D.sphereSupport :=
  D.disjoint_rimSupport_sphereSupport.mono_left (D.roundingSupport_subset_rimSupport k)

end DecompositionCertificate

end GC.GraphManifold.Assembly
