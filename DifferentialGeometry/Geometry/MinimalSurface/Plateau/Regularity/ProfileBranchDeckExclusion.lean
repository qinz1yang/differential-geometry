/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.HarmonicMap.BranchedDeckGerms
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.RegularValueNoCoincidentGerms

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

/-- Coincident germs of the actual disk extension at two interior points remain
coincident after restricting the same disk to an open preimage. No rank
hypothesis or change of disk is needed for this neighborhood transport. -/
theorem coincidentGermPairs_restrictPreimage_of_interior_disk_germs
    {M : Type*} [TopologicalSpace M]
    (q : C(closedDisk, M)) {V : Set M} (hV : IsOpen (q ⁻¹' V))
    (x y : closedDisk)
    (hx : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1)
    (hy : (y : ℂ) ∈ Metric.ball (0 : ℂ) 1)
    (hxV : q x ∈ V) (hyV : q y ∈ V)
    (hne : x ≠ y) (hxy : q x = q y)
    (hgerm : Filter.map (diskExtension q) (𝓝 (x : ℂ)) =
      Filter.map (diskExtension q) (𝓝 (y : ℂ))) :
    ((⟨x, hxV⟩ : q ⁻¹' V), (⟨y, hyV⟩ : q ⁻¹' V)) ∈
      coincidentGermPairs (V.restrictPreimage (q : closedDisk → M)) := by
  let R : Set closedDisk := q ⁻¹' V
  let qr := V.restrictPreimage (q : closedDisk → M)
  have hR : IsOpen R := hV
  have hsource (z : R) :
      Filter.map (Subtype.val : R → closedDisk) (𝓝 z) = 𝓝 z.val :=
    hR.isOpenEmbedding_subtypeVal.map_nhds_eq z
  have hmap (z : R) :
      Filter.map (Subtype.val : V → M) (Filter.map qr (𝓝 z)) =
        Filter.map q (𝓝 z.val) := by
    rw [Filter.map_map]
    change Filter.map ((q : closedDisk → M) ∘ (Subtype.val : R → closedDisk))
      (𝓝 z) = Filter.map q (𝓝 z.val)
    rw [← Filter.map_map, hsource]
  have hrestriction : diskExtension q ∘ (Subtype.val : closedDisk → ℂ) =
      (q : closedDisk → M) := funext (diskExtension_coe q)
  have hdisk (z : closedDisk) (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
      Filter.map q (𝓝 z) = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
    calc
      Filter.map q (𝓝 z) =
          Filter.map (diskExtension q ∘ (Subtype.val : closedDisk → ℂ)) (𝓝 z) :=
        congrArg (fun f : closedDisk → M => Filter.map f (𝓝 z)) hrestriction.symm
      _ = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
        rw [← Filter.map_map, map_nhds_subtype_val]
        rw [nhdsWithin_eq_nhds.2
          (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
            Metric.ball_subset_closedBall)]
  have hfull (z : R) (hz : (z.val : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
      Filter.map (Subtype.val : V → M) (Filter.map qr (𝓝 z)) =
        Filter.map (diskExtension q) (𝓝 (z.val : ℂ)) :=
    (hmap z).trans (hdisk z.val hz)
  refine ⟨fun h => hne (congrArg Subtype.val h), Subtype.ext hxy, ?_⟩
  apply Filter.map_injective (Subtype.val_injective : Function.Injective (Subtype.val : V → M))
  exact (hfull ⟨x, hxV⟩ hx).trans (hgerm.trans (hfull ⟨y, hyV⟩ hy).symm)

/-- A punctured coordinate disk contains a point outside any supplied finite
set of actual closed-disk source points. -/
private theorem exists_coordinate_outside_finite
    (e : OpenPartialHomeomorph ℂ ℂ) (h0 : (0 : ℂ) ∈ e.target)
    (D : Set closedDisk) (hD : D.Finite) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℂ, 0 < ‖w‖ ∧ ‖w‖ < ε ∧ w ∈ e.target ∧
      ∀ z : closedDisk, (z : ℂ) = e.symm w → z ∉ D := by
  classical
  let A : Set ℂ := insert 0 ((fun z : closedDisk => e (z : ℂ)) '' D)
  have hA : A.Finite := (hD.image (fun z : closedDisk => e (z : ℂ))).insert 0
  have hnear : e.target ∩ Metric.ball (0 : ℂ) ε ∈ 𝓝 (0 : ℂ) :=
    inter_mem (e.open_target.mem_nhds h0) (Metric.ball_mem_nhds 0 hε)
  have hinfinite : (e.target ∩ Metric.ball (0 : ℂ) ε).Infinite :=
    infinite_of_mem_nhds (0 : ℂ) hnear
  obtain ⟨w, hw, hwnot⟩ := hinfinite.exists_notMem_finite hA
  have hw0 : w ≠ 0 := by
    intro h
    apply hwnot
    exact Set.mem_insert_iff.mpr (Or.inl h)
  refine ⟨w, norm_pos_iff.mpr hw0,
    by simpa only [Metric.mem_ball, dist_zero_right] using hw.2, hw.1, ?_⟩
  intro z hz hzD
  apply hwnot
  apply Set.mem_insert_of_mem
  refine ⟨z, hzD, ?_⟩
  change e (z : ℂ) = w
  rw [hz, e.right_inv hw.1]

/-- A nontrivial deck-height zero germ would give two coincident regular image
germs outside the finite removed fibers of the same disk. Thus an empty
coincident-germ relation on that restriction rules out the zero germ. -/
theorem IsMorreyDisk.not_branched_height_zero_germ_of_finite_restriction
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) (S : Set M)
    (hfinite : (q ⁻¹' S).Finite)
    (hno : coincidentGermPairs ((Sᶜ).restrictPreimage (q : closedDisk → M)) = ∅)
    {a : ℂ} (m : ℕ) (b : Fin (Module.finrank ℝ E) → ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hae : a ∈ e.source) (hea : e a = 0)
    (heinterior : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (hechart : ∀ z ∈ e.source,
      diskExtension q z ∈ (chartAt E (diskExtension q a)).source) :
    let U : ℂ → M := diskExtension q
    let p := U a
    let GramQ := chartGramBilin g p p
    let P := chartLeadingPlaneProjection g p p b
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := P ∘ X
    (∀ z ∈ e.source, z ≠ a → (fderiv ℝ F z).IsInvertible) →
    (∀ w ∈ e.target,
      F (e.symm w) = F a + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) →
    ∀ (N : E) (lift : ℂ → E),
      (∀ v : E, v = lift (P v) + (GramQ N v) • N) →
      let H : ℂ → ℝ := fun w => GramQ N (X (e.symm w) - X a)
      ∀ ζ : ℂ, ζ ^ (m + 1) = 1 → ζ ≠ 1 →
        ¬ (∀ᶠ w in 𝓝 (0 : ℂ), H w - H (ζ * w) = 0) := by
  intro U p GramQ P X F hreg hpower N lift hsplit H ζ hζpower hζne hzero
  obtain ⟨ε, hε, hgerms⟩ :=
    hq.coincident_regular_germs_of_branched_height_zero_germ
      m b e hae hea heinterior hechart hreg hpower N lift hsplit ζ hζpower hζne hzero
  have h0target : (0 : ℂ) ∈ e.target := by
    rw [← hea]
    exact e.map_source hae
  obtain ⟨w, hwpos, hwε, _hwt, hwavoid⟩ :=
    exists_coordinate_outside_finite e h0target (q ⁻¹' S) hfinite ε hε
  obtain ⟨hx, hy, hne, _hrankx, _hranky, hxy, hgerm⟩ := hgerms w hwpos hwε
  let x : closedDisk := ⟨e.symm w, Metric.ball_subset_closedBall hx⟩
  let y : closedDisk := ⟨e.symm (ζ * w), Metric.ball_subset_closedBall hy⟩
  have hxV : q x ∈ Sᶜ := hwavoid x rfl
  have hvalue : q x = q y :=
    (diskExtension_coe q x).symm.trans (hxy.trans (diskExtension_coe q y))
  have hyV : q y ∈ Sᶜ := hvalue ▸ hxV
  have hdistinct : x ≠ y := fun h => hne (congrArg Subtype.val h)
  have hopen : IsOpen (q ⁻¹' Sᶜ) := hfinite.isClosed.isOpen_compl
  have hpair := coincidentGermPairs_restrictPreimage_of_interior_disk_germs
    q hopen x y hx hy hxV hyV hdistinct hvalue hgerm
  rw [hno] at hpair
  exact hpair

end DifferentialGeometry.Geometry

namespace DiskRegularity.ConsumerAudit

/-- On the literal completed-domain profile disk, every nontrivial deck-height
difference in an actual branched leading-projection coordinate has nonzero
germ. The finite exceptional fibers and exclusion of coincident regular germs
are derived from the profile hypotheses for the same disk and extension. -/
theorem profile_branched_height_not_zero_germ
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (hd3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hbase : ∀ x : M, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, 0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric g hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ (γU θ : M) = 0) →
      ∀ (Q : ℂ → U), SmoothDiskExtension (E := E) q Q →
      ∀ {z₀ : ℂ} (m : ℕ) (b : Fin (Module.finrank ℝ E) → ℂ)
        (e : OpenPartialHomeomorph ℂ ℂ),
        z₀ ∈ e.source → e z₀ = 0 →
        e.source ⊆ Metric.ball (0 : ℂ) 1 →
        (∀ z ∈ e.source,
          diskExtension q z ∈ (chartAt E (diskExtension q z₀)).source) →
        let u : ℂ → U := diskExtension q
        let p := u z₀
        let GramQ := chartGramBilin G p p
        let P := chartLeadingPlaneProjection G p p b
        let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (u z)
        let F : ℂ → ℂ := P ∘ X
        (∀ z ∈ e.source, z ≠ z₀ → (fderiv ℝ F z).IsInvertible) →
        (∀ w ∈ e.target,
          F (e.symm w) = F z₀ + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) →
        ∀ (N : E) (lift : ℂ → E),
          (∀ v : E, v = lift (P v) + (GramQ N v) • N) →
          let H : ℂ → ℝ := fun w => GramQ N (X (e.symm w) - X z₀)
          ∀ ζ : ℂ, ζ ^ (m + 1) = 1 → ζ ≠ 1 →
            ¬ (∀ᶠ w in 𝓝 (0 : ℂ), H w - H (ζ * w) = 0) := by
  classical
  dsimp only
  intro γU q hγ hq hγzero Q hQ z₀ m b e hae hea heinterior hechart
  let B : Set closedDisk := {z | ¬ Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)}
  have hprofile := profile_regular_value_restriction_no_coincident_germs
    hd3 g a ha ρ hρ hbase hcontact γU q hγ hq hγzero Q hQ
  exact hq.not_branched_height_zero_germ_of_finite_restriction
    (q '' B) hprofile.1 hprofile.2.2 m b e hae hea heinterior hechart

end DiskRegularity.ConsumerAudit
