import DifferentialGeometry.Topology.Surface.Recognition.DiskRimBaseBCF
import DifferentialGeometry.Topology.Surface.Recognition.PartitionOfBaseCurveBCF

/-!
# A torus component of `∂M₂` meets no horizontal disk (lane S-BCF03b; BCF03 G7 `hdisk`, FC40)

Kernel of the cusp branch of BCF03: let `Y` be a connected component of `Bd = ∂M₂` homeomorphic to
a torus and `P` an `EmbeddedFacePartition_BCF` of `Y` whose pieces cover `Y ∩ R_c`. FC40
(`diskCount_eq_zero_of_torus`) gives no disk, so `Y ⊆ R_c`; a point of `Y ∩ X₂` would put its whole
edge disk `D` in `Y ⊆ R_c`, hence in `P_e ∩ R_c = V_e ⊆ {T = c}`, contradicting that only the rim
of `D` lies at the level `c` (the centre of the disk does not).

* `subset_remainder_of_diskCount_zero_BCF`: no disk ⟹ `Y ⊆ R_c`;
* `component_inter_source_eq_empty_of_torus_BCF`: **`Y ∩ X₂ = ∅`** (the input `hdisk` of the cusp
  dichotomy, proved from the partition of the torus component).
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

section NoDisk

variable {Wt H : Type*} [TopologicalSpace Wt] {fib₁ : H → Set Wt} {f₂ : Wt → H} {T : Wt → ℝ}
  {c : ℝ} {X₂ Bd Rc : Set Wt}

/-- No disk in a partition of `Y` whose pieces cover `Y ∩ Rc` forces `Y ⊆ Rc`. -/
theorem subset_remainder_of_diskCount_zero_BCF {Y : Set Wt}
    (P : EmbeddedFacePartition_BCF ↥Y) (h0 : P.diskCount = 0)
    (hpieces : Subtype.val '' (⋃ j, P.piece j) = Y ∩ Rc) : Y ⊆ Rc := by
  intro y hy
  have hc : (⟨y, hy⟩ : Y) ∈ (⋃ i, P.disk i) ∪ (⋃ j, P.piece j) := P.cover ▸ mem_univ _
  rcases hc with hc | hc
  · obtain ⟨i, -⟩ := mem_iUnion.mp hc
    exact (Fin.elim0 (h0 ▸ i))
  · have : y ∈ Subtype.val '' (⋃ j, P.piece j) := ⟨⟨y, hy⟩, hc, rfl⟩
    rw [hpieces] at this
    exact this.2


/-- **A torus component of `∂M₂` meets no horizontal disk** (`hdisk`): `Y ∩ X₂ = ∅`, from the
partition of `Y` (FC40 for the torus count), the whole edge disks `≃ ClosedCell 2` and
`P_e ∩ R_c ⊆ {T = c}`. -/
theorem component_inter_source_eq_empty_of_torus_BCF
    (hfib₁ : ∀ y, fib₁ y = X₂ ∩ f₂ ⁻¹' {y})
    (hHe : ∀ p ∈ Bd ∩ X₂, ∀ q ∈ X₂, f₂ q = f₂ p → q ∈ Bd ∩ X₂)
    (hdisk : ∀ p ∈ Bd ∩ X₂, ∃ ed : fib₁ (f₂ p) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = rim_BCF fib₁ T c (f₂ p))
    (hPeRc : ∀ p ∈ Bd ∩ X₂, p ∈ Rc → T p = c) {x : Wt}
    (φ : ↥(connectedComponentIn Bd x) ≃ₜ Circle × Circle)
    (P : EmbeddedFacePartition_BCF ↥(connectedComponentIn Bd x))
    (hpieces : Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn Bd x ∩ Rc) :
    connectedComponentIn Bd x ∩ X₂ = ∅ := by
  have hYR : connectedComponentIn Bd x ⊆ Rc := subset_remainder_of_diskCount_zero_BCF P
    (P.diskCount_eq_zero_of_torus φ) hpieces
  refine eq_empty_of_forall_notMem fun q hq => ?_
  have hqBd : q ∈ Bd := connectedComponentIn_subset Bd x hq.1
  have hqHe : q ∈ Bd ∩ X₂ := ⟨hqBd, hq.2⟩
  have hqD : q ∈ fib₁ (f₂ q) := by
    rw [hfib₁]
    exact ⟨hq.2, rfl⟩
  have hy : f₂ q ∈ f₂ '' (Bd ∩ X₂) := ⟨q, hqHe, rfl⟩
  have hDHe : fib₁ (f₂ q) ⊆ Bd ∩ X₂ := by
    intro z hz
    rw [hfib₁] at hz
    exact hHe q hqHe z hz.1 hz.2
  have hDY : fib₁ (f₂ q) ⊆ connectedComponentIn Bd x :=
    subset_component_of_meets_BCF (isPreconnected_edgeDisk_BCF hdisk hy)
      (fun z hz => (hDHe hz).1) hqD hq.1
  obtain ⟨ed, hed⟩ := hdisk q hqHe
  let c₀ : ClosedCell 2 := ⟨0, by simp⟩
  have hz : ((ed.symm c₀ : fib₁ (f₂ q)) : Wt) ∈ rim_BCF fib₁ T c (f₂ q) :=
    ⟨(ed.symm c₀).2, hPeRc _ (hDHe (ed.symm c₀).2) (hYR (hDY (ed.symm c₀).2))⟩
  rw [← hed] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  have hww : w = ed.symm c₀ := Subtype.ext hwz
  have h1 : ‖((ed w : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ = 1 := hw
  rw [hww, ed.apply_symm_apply] at h1
  simp [c₀] at h1

end NoDisk

end DifferentialGeometry.Topology.Surface
