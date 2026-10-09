import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceCountRowApplications
import DifferentialGeometry.Topology.Surface.Recognition.SolidTorusSphereFaceBIF

/-!
# A bundle-form inhabitant of FC40 (`fc40_row_RWS`): the sphere with two polar caps

Lane S-CLEAN (suffix `_SCL`). Blueprint `master207B.tex`, FC40 (B:7457–7463).

`fc40_row_RWS` takes its circle-bundle surface in BUNDLE form (`B ⊆ Y` compact, `π : B → C` locally
trivial with fibre `Circle` over a smooth one-manifold with boundary `C`); the earlier inhabitant
`solidTorusSphereFace_BIF` is only a KERNEL-form `EmbeddedFacePartition_BCF` (annulus
parametrization `S¹ × [0,1] → band`, no projection). This file builds the bundle form on the same
geometry:

* `Y = S²` (`SphereTwo`), `A = ⋃ᵢ capParam_BIF i (D²)` the two closed polar caps `{∓z ≥ 1/2}`,
  `B = {|z| ≤ 1/2}` the equatorial band, `C = [0, 1]`;
* `bandHomeo_SCL : S¹ × [0,1] ≃ₜ B` (the band parametrization, a continuous bijection from a
  compact space to a Hausdorff space), `bandTriv_SCL : B ≃ₜ [0,1] × Circle`, and the projection
  `bandProj_SCL = (bandTriv_SCL ·).1`, globally trivial hence locally trivial
  (`localTrivialization_of_homeomorph_prod_SCL`);
* `capParam_cover_SCL`, `capParam_inter_band_SCL`, `capParam_boundary_SCL`: the three set
  equations of `fc40_row_RWS` (`A ∪ B = Y`, `A ∩ B = ∂A`, `∂A = π⁻¹(∂C)` with `∂[0,1] = {0, 1}`).

Consumers: `fc40_sphere_band_card_SCL` (`d = 2` for the inhabitant, from `fc40_row_RWS`) and
`fc40_sphere_band_unique_SCL` (the band bundle `π : B → [0,1]` admits NO disk family with a
different number of disks: any finite family satisfying the row's hypotheses against this `B`, `π`
has exactly two members — the row applied at an arbitrary index type, not only at `Fin 2`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

local instance factZeroLtOne_SCL : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A homeomorphism `Θ : B ≃ₜ C × F` makes `b ↦ (Θ b).1` a (globally, hence) locally trivial
bundle with fibre `F`, in the form of `fc40_row_RWS`. -/
theorem localTrivialization_of_homeomorph_prod_SCL {B C F : Type*} [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace F] (Θ : B ≃ₜ C × F) :
    ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : (fun b => (Θ b).1) ⁻¹' U ≃ₜ U × F,
      ∀ x : (fun b => (Θ b).1) ⁻¹' U, ((e x).1 : C) = (Θ x.1).1 := fun c => by
  refine ⟨univ, Filter.univ_mem, (Homeomorph.setCongr (preimage_univ (f := fun b => (Θ b).1))).trans
    ((Homeomorph.Set.univ B).trans (Θ.trans
      ((Homeomorph.Set.univ C).symm.prodCongr (Homeomorph.refl F)))), fun x => rfl⟩

/-- The point of the band `{|z| ≤ 1/2}` parametrized by `q`. -/
def bandPoint_SCL (q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1) : (sphereBand_BIF : Set SphereTwo) :=
  ⟨bandParam_BIF q, by rw [← range_bandParam_BIF]; exact mem_range_self q⟩

theorem continuous_bandPoint_SCL : Continuous bandPoint_SCL :=
  continuous_bandParam_BIF.subtype_mk _

theorem bijective_bandPoint_SCL : Bijective bandPoint_SCL :=
  ⟨fun a b h => injective_bandParam_BIF (congrArg Subtype.val h), fun p => by
    have hp : p.1 ∈ range bandParam_BIF := by
      rw [range_bandParam_BIF]
      exact p.2
    obtain ⟨q, hq⟩ := hp
    exact ⟨q, Subtype.ext hq⟩⟩

/-- **The band parametrization is a homeomorphism** `S¹ × [0,1] ≃ₜ {|z| ≤ 1/2}`. -/
def bandHomeo_SCL : sphere (0 : E2) 1 × Icc (0 : ℝ) 1 ≃ₜ (sphereBand_BIF : Set SphereTwo) :=
  (continuous_bandPoint_SCL).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective bandPoint_SCL bijective_bandPoint_SCL)

theorem bandHomeo_apply_SCL (q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1) :
    bandHomeo_SCL q = bandPoint_SCL q := rfl

/-- The band as a trivial circle bundle over `[0,1]`: `B ≃ₜ [0,1] × Circle`. -/
def bandTriv_SCL : (sphereBand_BIF : Set SphereTwo) ≃ₜ Icc (0 : ℝ) 1 × Circle :=
  bandHomeo_SCL.symm.trans (Homeomorph.prodComm _ _ |>.trans
    ((Homeomorph.refl _).prodCongr sphereTwoCircleHomeomorph_RWS))

/-- The bundle projection `π : B → [0,1]` (the band parameter `t = z + 1/2`). -/
def bandProj_SCL (b : (sphereBand_BIF : Set SphereTwo)) : Icc (0 : ℝ) 1 :=
  (bandTriv_SCL b).1

theorem continuous_bandProj_SCL : Continuous bandProj_SCL :=
  continuous_fst.comp bandTriv_SCL.continuous

theorem bandProj_bandPoint_SCL (q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1) :
    bandProj_SCL (bandPoint_SCL q) = q.2 := by
  change (bandTriv_SCL (bandHomeo_SCL q)).1 = q.2
  simp [bandTriv_SCL]

/-- **The band is a locally trivial circle bundle over `[0,1]`.** -/
theorem bandProj_locallyTrivial_SCL :
    ∀ c : Icc (0 : ℝ) 1, ∃ U ∈ 𝓝 c, ∃ e : bandProj_SCL ⁻¹' U ≃ₜ U × Circle,
      ∀ x : bandProj_SCL ⁻¹' U, ((e x).1 : Icc (0 : ℝ) 1) = bandProj_SCL x.1 :=
  localTrivialization_of_homeomorph_prod_SCL bandTriv_SCL

theorem isCompact_sphereBand_SCL : IsCompact (sphereBand_BIF : Set SphereTwo) := by
  rw [← range_bandParam_BIF]
  exact isCompact_range continuous_bandParam_BIF

/-- The caps are pairwise disjoint. -/
theorem capParam_disjoint_SCL : Pairwise (Disjoint on fun i : Fin 2 => range (capParam_BIF i)) := by
  intro i j hij
  have h : Disjoint (sphereCap_BIF i) (sphereCap_BIF j) :=
    solidTorusSphereFace_BIF.disk_disjoint hij
  simpa only [Function.onFun, range_capParam_BIF] using h

/-- `A ∪ B = Y`. -/
theorem capParam_cover_SCL :
    (⋃ i : Fin 2, range (capParam_BIF i)) ∪ sphereBand_BIF = univ := by
  have h := solidTorusSphereFace_BIF.cover
  simpa only [solidTorusSphereFace_BIF, iUnion_const, range_capParam_BIF] using h

/-- `A ∩ B = ∂A`. -/
theorem capParam_inter_band_SCL :
    (⋃ i : Fin 2, range (capParam_BIF i)) ∩ sphereBand_BIF =
      ⋃ i : Fin 2, capParam_BIF i '' diskSphere 2 := by
  rw [iUnion_inter]
  refine iUnion_congr fun i => ?_
  rw [range_capParam_BIF, capParam_diskSphere_BIF]

/-- `∂A = π⁻¹(∂C)` for `C = [0,1]`, `∂C = {0, 1}`. -/
theorem capParam_boundary_SCL :
    ⋃ i : Fin 2, capParam_BIF i '' diskSphere 2 =
      Subtype.val '' (bandProj_SCL ⁻¹' (𝓡∂ 1).boundary (Icc (0 : ℝ) 1)) := by
  ext p
  simp only [mem_iUnion, capParam_diskSphere_BIF, cap_inter_band_eq_BIF]
  rw [boundary_Icc]
  constructor
  · rintro ⟨i, q, hq, rfl⟩
    refine ⟨bandPoint_SCL q, ?_, rfl⟩
    rw [mem_preimage, bandProj_bandPoint_SCL]
    rcases capEndT_cases_BIF i with h | h
    · left
      exact Subtype.ext (hq.trans h)
    · right
      exact Subtype.ext (hq.trans h)
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨q, rfl⟩ := bijective_bandPoint_SCL.2 b
    rw [mem_preimage, bandProj_bandPoint_SCL] at hb
    rcases hb with h | h
    · refine ⟨0, q, ?_, rfl⟩
      have h0 : (q.2 : ℝ) = 0 := congrArg Subtype.val h
      show (q.2 : ℝ) = capEndT_BIF 0
      rw [h0]
      norm_num [capEndT_BIF, capSign_BIF]
    · refine ⟨1, q, ?_, rfl⟩
      have h1 : (q.2 : ℝ) = 1 := congrArg Subtype.val (mem_singleton_iff.mp h)
      show (q.2 : ℝ) = capEndT_BIF 1
      rw [h1]
      norm_num [capEndT_BIF, capSign_BIF]

/-- **Consumer (the inhabitant)**: `d = 2` for the bundle-form sphere face, from `fc40_row_RWS`. -/
theorem fc40_sphere_band_card_SCL : Fintype.card (Fin 2) = 2 :=
  (fc40_row_RWS (C := Icc (0 : ℝ) 1) capParam_BIF continuous_capParam_BIF
    injective_capParam_BIF capParam_disjoint_SCL sphereBand_BIF isCompact_sphereBand_SCL
    bandProj_SCL continuous_bandProj_SCL bandProj_locallyTrivial_SCL capParam_cover_SCL
    capParam_inter_band_SCL capParam_boundary_SCL).1 ⟨Homeomorph.refl _⟩

/-- **Consumer (uniqueness)**: against the band bundle `π : B → [0,1]`, EVERY finite family of
closed disks satisfying the hypotheses of FC40 has exactly two members (the row at an arbitrary
index type). -/
theorem fc40_sphere_band_unique_SCL {ι : Type*} [Fintype ι] (h : ι → Disk 2 → SphereTwo)
    (hh : ∀ i, Continuous (h i)) (hinj : ∀ i, Injective (h i))
    (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (hcover : (⋃ i, range (h i)) ∪ sphereBand_BIF = univ)
    (hAB : (⋃ i, range (h i)) ∩ sphereBand_BIF = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 =
      Subtype.val '' (bandProj_SCL ⁻¹' (𝓡∂ 1).boundary (Icc (0 : ℝ) 1))) :
    Fintype.card ι = 2 :=
  (fc40_row_RWS (C := Icc (0 : ℝ) 1) h hh hinj hdisj sphereBand_BIF isCompact_sphereBand_SCL
    bandProj_SCL continuous_bandProj_SCL bandProj_locallyTrivial_SCL hcover hAB hbd).1
    ⟨Homeomorph.refl _⟩

end DifferentialGeometry.Topology.Surface
