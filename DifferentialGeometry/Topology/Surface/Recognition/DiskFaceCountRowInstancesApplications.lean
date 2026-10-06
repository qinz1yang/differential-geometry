import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceCountRowInstances

/-!
# Consumer of the bundle-form FC40 inhabitant

Lane S-CLEAN (suffix `_SCL`). `sphere_band_two_disks_SCL`: against the band bundle
`bandProj_SCL : B → [0,1]` of `DiskFaceCountRowInstances`, any finite family of closed disks
satisfying the FC40 hypotheses consists of exactly two disks `h i`, `h j` (`i ≠ j`), and
`S² = h i (D²) ∪ h j (D²) ∪ B` — the form in which BCF03's sphere branch consumes the row
(`fc40_sphere_two_disks_SRF`), now at a concrete non-vacuous `Y`, `B`, `π`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

local instance factZeroLtOneApp_SCL : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

/-- Any disk family satisfying FC40 against the band bundle has exactly two disks `h i`, `h j`
and `S² = h i (D²) ∪ h j (D²) ∪ B`. -/
theorem sphere_band_two_disks_SCL {ι : Type*} [Fintype ι] (h : ι → Disk 2 → SphereTwo)
    (hh : ∀ i, Continuous (h i)) (hinj : ∀ i, Injective (h i))
    (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (hcover : (⋃ i, range (h i)) ∪ sphereBand_BIF = univ)
    (hAB : (⋃ i, range (h i)) ∩ sphereBand_BIF = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 =
      Subtype.val '' (bandProj_SCL ⁻¹' (𝓡∂ 1).boundary (Icc (0 : ℝ) 1))) :
    ∃ i j : ι, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
      range (h i) ∪ range (h j) ∪ sphereBand_BIF = univ :=
  fc40_sphere_two_disks_SRF (C := Icc (0 : ℝ) 1) (Homeomorph.refl SphereTwo) h hh hinj hdisj
    sphereBand_BIF isCompact_sphereBand_SCL bandProj_SCL continuous_bandProj_SCL
    bandProj_locallyTrivial_SCL hcover hAB hbd

/-- The concrete two-cap family is such a family: instantiating the consumer at the inhabitant
returns `i ≠ j` in `Fin 2` covering `Fin 2`. -/
theorem capParam_two_disks_SCL :
    ∃ i j : Fin 2, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
      range (capParam_BIF i) ∪ range (capParam_BIF j) ∪ sphereBand_BIF = univ :=
  sphere_band_two_disks_SCL capParam_BIF continuous_capParam_BIF injective_capParam_BIF
    capParam_disjoint_SCL capParam_cover_SCL capParam_inter_band_SCL capParam_boundary_SCL

end DifferentialGeometry.Topology.Surface
