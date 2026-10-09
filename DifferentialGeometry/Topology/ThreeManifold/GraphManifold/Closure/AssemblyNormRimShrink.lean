import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormCircleShrink
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormMeasure
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimQuadrantProducer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateFaces

/-!
# FC42 normalization, packet N1 (d): support preparation of a certificate

Lane ASM-NRM (frozen text `build-logs/scratch/ASM-NRM/Targets.lean`, section N1 (d); review 40
§1.5 steps 2–3, dispositions item 1: "an internal sphere does NOT automatically avoid rim chart
targets — shrink rim / corner charts and re-choose the common rounding first; never shorten the
collars of `E`").

`DecompositionCertificate.shrinkRims D ε` (`0 < ε ≤ 1/2`): the rim charts `χ' = χ ∘ (id × ε •)`
and the circle region `D.circ.shrink ε` (corner charts `cornerChart ∘ (ε •)`, scales `ε λ`, the
blended rounding); every other field — vertices, handles, edge circles, seams, faces, arcs, loops,
owners, ports `E` — is unchanged, definitionally. Hence:

* the counts, the measure `μ` and the cornered region are unchanged (`badVertexCount_shrinkRims`,
  `sphereMeasure_shrinkRims`, `region_shrinkRims`);
* the rim chart targets shrink: `shrinkRims_rimChart_target` (`χ '' {p.2 ∈ rimBox (2 ε)}`);
* the rim-product clause is transported (`RimProduct.shrinkRims`: `ρ (ε ·)`, `τ (ε ·)`, same `A`
  and `a`);
* **main** `exists_shrinkRims_disjoint`: a compact set avoiding every rim circle avoids every
  rim chart target of `D.shrinkRims ε` for some `ε` (on the compact `χ⁻¹ K ∩ (Circle × changeBox)`
  the sup-norm of the box coordinate has a positive minimum);
* `disjoint_rimCircle_of_subset_interior`: ambient interior points of a vertex image inside
  `W.interior` avoid every rim circle (own boundary image: the G1 criterion; other vertices: interior
  density and `vertex_disjoint`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-! ## The shrunk rim charts -/

/-- The shrunk rim chart `χ ∘ (id × ε •)`. -/
def shrinkRimChart (ε : ℝ) (hε : 0 < ε) (h : Fin D.handleCount) (b : Bool) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞ :=
  (rimScaling ε hε).trans (D.rimChart h b)

theorem shrinkRimChart_apply (ε : ℝ) (hε : 0 < ε) (h : Fin D.handleCount) (b : Bool)
    (p : Circle × (ℝ × ℝ)) : D.shrinkRimChart ε hε h b p = D.rimChart h b (p.1, ε • p.2) :=
  rfl

theorem rimChart_mem_source (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p.2 ∈ rimBox 2) : p ∈ (D.rimChart h b).source :=
  (D.rim_source h b).mpr hp

variable {D} {ε : ℝ} {hε : 0 < ε}

theorem shrinkRimChart_source (hε1 : ε ≤ 1 / 2) (h : Fin D.handleCount) (b : Bool)
    {p : Circle × (ℝ × ℝ)} : p ∈ (D.shrinkRimChart ε hε h b).source ↔ p.2 ∈ rimBox 2 := by
  change p ∈ (rimScaling ε hε).source ∩ rimScaleMap ε ⁻¹' (D.rimChart h b).source ↔ _
  rw [mem_inter_iff, rimScaling_source, mem_preimage, D.rim_source h b]
  exact ⟨fun hp => hp.1, fun hp => ⟨hp, smul_mem_rimBox hε (by linarith) hp⟩⟩

theorem shrinkRimChart_target_subset (h : Fin D.handleCount) (b : Bool) :
    (D.shrinkRimChart ε hε h b).target ⊆ (D.rimChart h b).target :=
  fun _ hx => hx.1

theorem shrinkRimChart_target (hε1 : ε ≤ 1 / 2) (h : Fin D.handleCount) (b : Bool) :
    (D.shrinkRimChart ε hε h b).target = D.rimChart h b '' {p | p.2 ∈ rimBox (2 * ε)} := by
  ext x
  change x ∈ (D.rimChart h b).target ∩ (D.rimChart h b).symm ⁻¹' (rimScaling ε hε).target ↔ _
  constructor
  · rintro ⟨hx, hxs⟩
    exact ⟨_, hxs, (D.rimChart h b).right_inv hx⟩
  · rintro ⟨p, hp, rfl⟩
    have hp2 : p ∈ (D.rimChart h b).source := D.rimChart_mem_source h b (rimBox_mono (by linarith) hp)
    refine ⟨(D.rimChart h b).map_source hp2, ?_⟩
    have hinv : (D.rimChart h b).symm (D.rimChart h b p) = p := (D.rimChart h b).left_inv hp2
    change (D.rimChart h b).symm (D.rimChart h b p) ∈ (rimScaling ε hε).target
    rw [hinv]
    exact hp

/-! ## The rim fields of the shrunk certificate -/

variable (hε1 : ε ≤ 1 / 2)
include hε1

theorem shrink_mem_source {h : Fin D.handleCount} {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (D.shrinkRimChart ε hε h b).source) : (p.1, ε • p.2) ∈ (D.rimChart h b).source :=
  D.rimChart_mem_source h b (smul_mem_rimBox hε (by linarith)
    ((shrinkRimChart_source hε1 h b).mp hp))

theorem shrink_rim_proj (h : Fin D.handleCount) (b : Bool) (p : Circle × (ℝ × ℝ))
    (hp : p ∈ (D.shrinkRimChart ε hε h b).source) :
    ∃ hx : D.shrinkRimChart ε hε h b p ∈ (D.circ.shrink ε hε hε1).domain,
      (D.circ.shrink ε hε hε1).proj ⟨D.shrinkRimChart ε hε h b p, hx⟩ =
        (D.circ.shrink ε hε hε1).cornerChart (D.handleCorner h b) p.2 := by
  obtain ⟨hx, hproj⟩ := D.rim_proj h b _ (shrink_mem_source hε1 hp)
  exact ⟨hx, hproj⟩

theorem shrink_rim_vertex (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (D.shrinkRimChart ε hε h b).source) :
    D.shrinkRimChart ε hε h b p ∈ (D.vertex (D.handleEnd h b)).image ↔ p.2.2 ≤ 0 := by
  rw [shrinkRimChart_apply, D.rim_vertex h b (shrink_mem_source hε1 hp)]
  simp only [Prod.smul_snd, smul_eq_mul]
  exact ⟨fun h => nonpos_of_mul_nonpos_right h hε |>.trans le_rfl,
    fun h => mul_nonpos_of_nonneg_of_nonpos hε.le h⟩

theorem shrink_rim_handle (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (D.shrinkRimChart ε hε h b).source) :
    D.shrinkRimChart ε hε h b p ∈ range (D.handle h).map ↔ (0 ≤ p.2.2 ∧ p.2.1 ≤ 0) := by
  rw [shrinkRimChart_apply, D.rim_handle h b (shrink_mem_source hε1 hp)]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [mul_nonneg_iff_of_pos_left hε]
  exact and_congr_right fun _ =>
    ⟨fun h => nonpos_of_mul_nonpos_right h hε, fun h => mul_nonpos_of_nonneg_of_nonpos hε.le h⟩

theorem shrink_rim_region (h : Fin D.handleCount) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (D.shrinkRimChart ε hε h b).source) :
    D.shrinkRimChart ε hε h b p ∈ (D.circ.shrink ε hε hε1).region ↔ (0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := by
  rw [CircleRegion.region_shrink, shrinkRimChart_apply, D.rim_region h b (shrink_mem_source hε1 hp)]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [mul_nonneg_iff_of_pos_left hε, mul_nonneg_iff_of_pos_left hε]

omit hε1 in
theorem shrink_rim_label (h : Fin D.handleCount) (b : Bool) :
    D.shrinkRimChart ε hε h b '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => (D.handle h).map (x, iccEnd b)) '' diskRim := by
  rw [← D.rim_label h b]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(p.1, ε • p.2), ?_, rfl⟩
    change ε • p.2 = (0, 0)
    rw [show p.2 = (0, 0) from hp]
    simp
  · rintro ⟨⟨θ, v⟩, hp, rfl⟩
    refine ⟨(θ, v), hp, ?_⟩
    change v = (0, 0) at hp
    subst hp
    rw [shrinkRimChart_apply]
    simp

omit hε1 in
theorem shrink_rim_disjoint (h : Fin D.handleCount) (b : Bool) (h' : Fin D.handleCount) (b' : Bool)
    (hne : (h, b) ≠ (h', b')) :
    Disjoint (D.shrinkRimChart ε hε h b).target (D.shrinkRimChart ε hε h' b').target :=
  (D.rim_disjoint h b h' b' hne).mono (shrinkRimChart_target_subset h b)
    (shrinkRimChart_target_subset h' b')

omit hε1 in
theorem shrink_arcBase_end (j : Fin D.arcFaceCount) (e : Bool) :
    D.arcBase j (iccEnd e) =
      D.circ.cornerChart (D.handleCorner (D.arcEnd j e).1 (D.arcEnd j e).2) (ε • ((0, 0) : ℝ × ℝ)) := by
  rw [D.arcBase_end j e]
  simp

omit hε1

variable (D)

/-! ## The shrunk certificate -/

/-- **N1. Support preparation** (review 40 §1.5; review 44 §4, binding form). WHAT CHANGES: the
rim charts `χ' = χ ∘ (id × ε •)`, the corner charts `cornerChart ∘ (ε •)` (one COMMON linear scaling
of both coordinates), the corner scales `ε λ`, and the common rounding function (the blend
`shrinkRounding ε`), hence the rounded region `circ.rounded` (only inside the compact change sets
`cornerChart k '' changeBox`, `rounded_shrinkRims_diff`) and every rounded union built from it.
WHAT DOES NOT CHANGE (definitionally): vertices, handles, edge circles, torus and sphere seams,
faces, face kinds and models, arcs, loops, owners, handle ends, the ports `E` (collars untouched),
the base, domain, projection, trivializations, defining functions and the cornered region. Every V4
field is re-proved; `RimProduct` is transported by `RimProduct.shrinkRims`. -/
def shrinkRims (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) : DecompositionCertificate W E :=
  { D with
    circ := D.circ.shrink ε hε hε1
    rimChart := D.shrinkRimChart ε hε
    arcBase_end := shrink_arcBase_end (D := D) (ε := ε)
    rim_source := shrinkRimChart_source hε1
    rim_proj := shrink_rim_proj hε1
    rim_vertex := shrink_rim_vertex hε1
    rim_handle := shrink_rim_handle hε1
    rim_region := shrink_rim_region hε1
    rim_label := shrink_rim_label (D := D) (hε := hε)
    rim_disjoint := shrink_rim_disjoint
    rim_external_disjoint := fun h b i =>
      (D.rim_external_disjoint h b i).mono_left (shrinkRimChart_target_subset h b)
    rim_torusSeam_disjoint := fun h b c =>
      (D.rim_torusSeam_disjoint h b c).mono_left (shrinkRimChart_target_subset h b)
    rim_sphereSeam_disjoint := fun h b c =>
      (D.rim_sphereSeam_disjoint h b c).mono_left (shrinkRimChart_target_subset h b) }

variable (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)

theorem shrinkRims_vertex : (D.shrinkRims ε hε hε1).vertex = D.vertex := rfl

theorem shrinkRims_handle : (D.shrinkRims ε hε hε1).handle = D.handle := rfl

theorem shrinkRims_sphereSeam : (D.shrinkRims ε hε hε1).sphereSeam = D.sphereSeam := rfl

theorem shrinkRims_torusSeam : (D.shrinkRims ε hε hε1).torusSeam = D.torusSeam := rfl

theorem shrinkRims_face : (D.shrinkRims ε hε hε1).face = D.face := rfl

theorem shrinkRims_circ : (D.shrinkRims ε hε hε1).circ = D.circ.shrink ε hε hε1 := rfl

theorem shrinkRims_rimChart_apply (h : Fin D.handleCount) (b : Bool) (p : Circle × (ℝ × ℝ)) :
    (D.shrinkRims ε hε hε1).rimChart h b p = D.rimChart h b (p.1, ε • p.2) :=
  rfl

theorem shrinkRims_rimChart_target (h : Fin D.handleCount) (b : Bool) :
    ((D.shrinkRims ε hε hε1).rimChart h b).target =
      D.rimChart h b '' {p | p.2 ∈ rimBox (2 * ε)} :=
  shrinkRimChart_target hε1 h b

theorem shrinkRims_rimChart_target_subset (h : Fin D.handleCount) (b : Bool) :
    ((D.shrinkRims ε hε hε1).rimChart h b).target ⊆ (D.rimChart h b).target :=
  shrinkRimChart_target_subset h b

theorem region_shrinkRims : (D.shrinkRims ε hε hε1).circ.region = D.circ.region :=
  rfl

theorem badVertexCount_shrinkRims :
    (D.shrinkRims ε hε hε1).badVertexCount = D.badVertexCount :=
  rfl

theorem badVertexSet_shrinkRims : (D.shrinkRims ε hε hε1).badVertexSet = D.badVertexSet :=
  rfl

theorem sphereMeasure_shrinkRims :
    (D.shrinkRims ε hε hε1).sphereMeasure = D.sphereMeasure :=
  rfl

/-- **What changes in the rounded region**: nothing off the preimages of the compact change sets
`cornerChart k '' changeBox`. -/
theorem rounded_shrinkRims_diff :
    (D.shrinkRims ε hε hε1).circ.rounded \
        Subtype.val '' (D.circ.proj ⁻¹' ⋃ k, D.circ.cornerChart k '' changeBox) =
      D.circ.rounded \ Subtype.val '' (D.circ.proj ⁻¹' ⋃ k, D.circ.cornerChart k '' changeBox) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hnot⟩
    have hy' : D.circ.proj y ∉ ⋃ k, D.circ.cornerChart k '' changeBox := fun h => hnot ⟨y, h, rfl⟩
    refine ⟨⟨y, ?_, rfl⟩, hnot⟩
    change D.circ.rounding (D.circ.proj y) ≤ 0
    rw [← D.circ.shrinkRounding_eq_of_not_mem ε hy']
    exact hy
  · rintro ⟨⟨y, hy, rfl⟩, hnot⟩
    have hy' : D.circ.proj y ∉ ⋃ k, D.circ.cornerChart k '' changeBox := fun h => hnot ⟨y, h, rfl⟩
    refine ⟨⟨y, ?_, rfl⟩, hnot⟩
    change D.circ.shrinkRounding ε (D.circ.proj y) ≤ 0
    rw [D.circ.shrinkRounding_eq_of_not_mem ε hy']
    exact hy

variable {D} in
/-- **N1. `RimProduct` is transported** (`ρ' = ρ (ε ·)`, `τ' = τ (ε ·)`, same `A` and `a`). -/
theorem RimProduct.shrinkRims (hD : D.RimProduct) : (D.shrinkRims ε hε hε1).RimProduct := by
  intro h b
  obtain ⟨a, ha, ha', A, ρ, τ, hρ, hτ, hρ0, hτ0, hρd, hτd, heq⟩ := hD h b
  have hε1' : ε ≤ 1 := by linarith
  refine ⟨a, ha, ha', A, fun x => ρ (ε * x), fun y => τ (ε * y),
    hρ.comp (contDiff_const.mul contDiff_id), hτ.comp (contDiff_const.mul contDiff_id),
    by simpa using hρ0, by simpa using hτ0, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : ε * x ∈ Ioc (-a) 0 :=
      ⟨by nlinarith [hx.1, hx.2], mul_nonpos_of_nonneg_of_nonpos hε.le hx.2⟩
    refine ⟨(hρd _ hx').1, ?_⟩
    rw [deriv_comp_mul_left, smul_eq_mul]
    exact mul_pos hε (hρd _ hx').2
  · intro y hy
    have hy' : ε * y ∈ Ico 0 a := ⟨mul_nonneg hε.le hy.1, by nlinarith [hy.1, hy.2]⟩
    rw [deriv_comp_mul_left, smul_eq_mul]
    exact mul_pos hε (hτd _ hy')
  · intro θ x y w t hx hx' hy hy' hw ht
    change D.rimChart h b (θ, ε • (x, y)) = (D.handle h).map (w, t)
    rw [show ε • (x, y) = (ε * x, ε * y) by simp]
    exact heq θ (ε * x) (ε * y) w t (by nlinarith) (mul_nonpos_of_nonneg_of_nonpos hε.le hx')
      (mul_nonneg hε.le hy) (by nlinarith) hw ht

/-! ## N1 main: shrinking off a compact set -/

/-- For one rim chart: a compact set avoiding the rim circle avoids the shrunk targets for all
small `ε`. -/
theorem eventually_disjoint_rimChart_image (h : Fin D.handleCount) (b : Bool) {K : Set W.Carrier}
    (hK : IsCompact K) (hrim : Disjoint K (D.rimChart h b '' {p | p.2 = (0, 0)})) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Disjoint (D.rimChart h b '' {p | p.2 ∈ rimBox (2 * ε)}) K := by
  set χ := D.rimChart h b
  let S : Set (Circle × (ℝ × ℝ)) := {p | p.2 ∈ changeBox}
  have hSc : IsCompact S := by
    have : S = univ ×ˢ changeBox := by ext p; simp [S]
    rw [this]
    exact isCompact_univ.prod isCompact_changeBox
  have hSsrc : S ⊆ χ.source := fun p hp => D.rimChart_mem_source h b (changeBox_subset_rimBox_two hp)
  have hχS : ContinuousOn χ S := χ.contMDiffOn.continuousOn.mono hSsrc
  let T : Set (Circle × (ℝ × ℝ)) := S ∩ χ ⁻¹' K
  have hTc : IsCompact T :=
    hSc.of_isClosed_subset (hχS.preimage_isClosed_of_isClosed hSc.isClosed hK.isClosed)
      inter_subset_left
  -- the sup-norm of the box coordinate is positive on `T`
  let F : Circle × (ℝ × ℝ) → ℝ := fun p => max |p.2.1| |p.2.2|
  have hF : Continuous F :=
    (continuous_abs.comp (continuous_fst.comp continuous_snd)).max
      (continuous_abs.comp (continuous_snd.comp continuous_snd))
  have hFpos : ∀ p ∈ T, 0 < F p := by
    intro p hp
    by_contra hle
    rw [not_lt] at hle
    have h1 : p.2.1 = 0 := abs_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hle) (abs_nonneg _))
    have h2 : p.2.2 = 0 := abs_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hle) (abs_nonneg _))
    have hp0 : p.2 = (0, 0) := Prod.ext h1 h2
    exact Set.disjoint_left.mp hrim hp.2 ⟨p, hp0, rfl⟩
  obtain ⟨m, hm, hmT⟩ : ∃ m : ℝ, 0 < m ∧ ∀ p ∈ T, m ≤ F p := by
    rcases T.eq_empty_or_nonempty with hT | hT
    · exact ⟨1, one_pos, fun p hp => by rw [hT] at hp; exact hp.elim⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hTc.exists_isMinOn hT hF.continuousOn
      exact ⟨F p₀, hFpos p₀ hp₀, fun p hp => hmin hp⟩
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min (3 / 4) (m / 2) :=
    nhdsWithin_le_nhds (eventually_lt_nhds (lt_min (by norm_num) (half_pos hm)))
  filter_upwards [hlt, self_mem_nhdsWithin] with ε hε hεpos
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ hpK
  have hε1 := (lt_min_iff.mp hε).1
  have hε2 := (lt_min_iff.mp hε).2
  have hpS : p ∈ S := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hFp := hmT p ⟨hpS, hpK⟩
  have : F p < 2 * ε := max_lt hp.1 hp.2
  linarith

/-- **N1, main.** A compact set avoiding every rim circle avoids every rim chart target after a
small enough shrink. -/
theorem exists_shrinkRims_disjoint {K : Set W.Carrier} (hK : IsCompact K)
    (hrim : ∀ h b, Disjoint K (D.rimChart h b '' {p | p.2 = (0, 0)})) :
    ∃ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2), ∀ h b,
      Disjoint ((D.shrinkRims ε hε hε1).rimChart h b).target K := by
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hb : Fin D.handleCount × Bool,
      Disjoint (D.rimChart hb.1 hb.2 '' {p | p.2 ∈ rimBox (2 * ε)}) K :=
    Filter.eventually_all.mpr fun hb => D.eventually_disjoint_rimChart_image hb.1 hb.2 hK (hrim _ _)
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 / 2 :=
    nhdsWithin_le_nhds (eventually_le_nhds (by norm_num))
  obtain ⟨ε, hεall, hε1, hεpos⟩ := (hall.and (hle.and self_mem_nhdsWithin)).exists
  refine ⟨ε, hεpos, hε1, fun h b => ?_⟩
  exact (hεall (h, b)).mono_left (D.shrinkRims_rimChart_target ε hεpos hε1 h b).le

/-- **N1, consumer form of the rim-circle hypothesis**: a set of ambient interior points of a
vertex image inside `W.interior` avoids every rim circle. -/
theorem disjoint_rimCircle_of_subset_interior {k : Fin D.vertexCount} {K : Set W.Carrier}
    (hK : K ⊆ interior (D.vertex k).image ∩ W.interior) (h : Fin D.handleCount) (b : Bool) :
    Disjoint K (D.rimChart h b '' {p | p.2 = (0, 0)}) := by
  rw [D.rim_label h b, Set.disjoint_left]
  rintro x hxK ⟨y, hy, rfl⟩
  have hxint := (hK hxK).1
  have hxW := (hK hxK).2
  have hxE : (D.handle h).map (y, iccEnd b) ∈ (D.handle h).endDisk b := ⟨y, rfl⟩
  have hxB : (D.handle h).map (y, iccEnd b) ∈ (D.vertex (D.handleEnd h b)).boundaryImage := by
    have := D.face_subset_boundaryImage (D.handleFace h b) (D.handleEnd_face h b hxE)
    rwa [D.handleFace_owner] at this
  by_cases hk : D.handleEnd h b = k
  · rw [hk] at hxB
    exact Vertex.boundaryImage_inter_interior_subset _ ⟨hxB, hxint⟩ hxW
  · -- a point of another vertex image inside the open `interior (image k)`
    obtain ⟨q, hq, hqx⟩ := hxB
    obtain ⟨z, hz1, hz2⟩ := exists_mem_inter_interior_range (by simp)
      (D.vertex (D.handleEnd h b)).piece.smooth (D.vertex (D.handleEnd h b)).piece.mfderiv_bijective
      isOpen_interior (x := q) (by rw [hqx]; exact hxint)
    rw [← Vertex.image_eq_range_piece] at hz2
    exact Set.disjoint_left.mp (D.vertex_disjoint (Ne.symm hk)) hz1 hz2

end DecompositionCertificate

end GC.GraphManifold.Assembly
