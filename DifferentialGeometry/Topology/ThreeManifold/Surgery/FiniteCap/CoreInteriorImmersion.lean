import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreAmbientSmooth
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreAmbientCoordinates

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold IsManifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev ImmInteriorE2 := EuclideanSpace ℝ (Fin 2)
private abbrev ImmInteriorIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev ImmInteriorIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev ImmInteriorIH := ModelProd ImmInteriorE2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph ImmInteriorIC I ∞ (f i))

include hs in
theorem cutCore_ambientInclusion_isImmersionAt_interior (x : coreInteriorDomain f) :
    let : ChartedSpace ImmInteriorIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    IsImmersionAtOfComplement Unit ImmInteriorIR I ∞ (Subtype.val : cutCore f → M)
      (coreInteriorInclusion f x) := by
  let : ChartedSpace ImmInteriorIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold ImmInteriorIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let a := (coreInteriorModelDiffeomorph I hdim (chartAt H x x)).2 - 1
  let ψ := coreAmbientNormalizingHomeomorph I hdim a 1 (by norm_num)
  let ψ₀ := coreAmbientNormalizingHomeomorph I hdim 0 1 (by norm_num)
  let c := cutCoreInteriorHalfChart I hdim f x
  let d := (chartAt H x.val).transHomeomorph (ψ.symm.trans ψ₀)
  have hd : d ∈ maximalAtlas I ∞ M := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact ((coreAmbientNormalizingHomeomorph_contMDiff I hdim 0 1 (by norm_num)).comp
        (coreAmbientNormalizingHomeomorph_symm_contMDiff I hdim a 1 (by norm_num))).comp_contMDiffOn
          (contMDiffOn_chart (I := I) (n := ∞) (x := x.val))
    · exact (contMDiffOn_chart_symm (I := I) (n := ∞) (x := x.val)).comp
        (((coreAmbientNormalizingHomeomorph_contMDiff I hdim a 1 (by norm_num)).comp
          (coreAmbientNormalizingHomeomorph_symm_contMDiff I hdim 0 1 (by norm_num))).contMDiffOn)
        (fun _ hz => hz)
  have hc : c ∈ maximalAtlas ImmInteriorIR ∞ (cutCore f) := subset_maximalAtlas (Or.inl ⟨x, rfl⟩)
  let L := (ContinuousLinearEquiv.prodUnique ℝ (ImmInteriorE2 × EuclideanSpace ℝ (Fin 1)) Unit).trans
    (coreBoundaryAmbientLinearEquiv hdim)
  apply IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt L c d
    (cutCoreInteriorHalfChart_mem I hdim f x) (mem_chart_source H x.val) hc hd
  intro z hz
  have hzcore : ImmInteriorIR.symm z ∈ c.target := by
    exact hz.2
  have hzold := hzcore
  rw [cutCoreInteriorHalfChart_target_original] at hzold
  have hchart := (chartAt H x).right_inv hzold.2
  change I (d ((c.extend ImmInteriorIR).symm z).val) = L (z, 0)
  change I (ψ₀ (ψ.symm (chartAt H x.val ((c.symm (ImmInteriorIR.symm z)).val)))) = L (z, 0)
  dsimp only [c]
  rw [cutCoreInteriorHalfChart_symm_original]
  change I (ψ₀ (ψ.symm (chartAt H x ((chartAt H x).symm
    ((coreInteriorModelDiffeomorph I hdim).symm
      ((ImmInteriorIR.symm z).1, (ImmInteriorIR.symm z).2.val 0 + a)))))) = L (z, 0)
  rw [hchart]
  have hψ : ψ.symm ((coreInteriorModelDiffeomorph I hdim).symm
      ((ImmInteriorIR.symm z).1, (ImmInteriorIR.symm z).2.val 0 + a)) =
        ((ImmInteriorIR.symm z).1, (ImmInteriorIR.symm z).2.val 0) := by
    apply ψ.injective
    rw [ψ.apply_symm_apply]
    change (coreInteriorModelDiffeomorph I hdim).symm
      ((ImmInteriorIR.symm z).1, (ImmInteriorIR.symm z).2.val 0 + a) =
        (coreInteriorModelDiffeomorph I hdim).symm
          ((ImmInteriorIR.symm z).1, a + 1 * (ImmInteriorIR.symm z).2.val 0)
    simp only [one_mul, add_comm]
  rw [hψ]
  have hext := coreAmbientNormalizingHomeomorph_extend I hdim 0 1 (by norm_num)
    (((ImmInteriorIR.symm z).1, (ImmInteriorIR.symm z).2.val 0) : ModelProd ImmInteriorE2 ℝ)
  change I (ψ₀ ((ImmInteriorIR.symm z).1, (ImmInteriorIR.symm z).2.val 0)) = L (z, 0)
  rw [hext]
  simp only [one_mul, zero_add]
  have hzcoords : ((ImmInteriorIR.symm z).1, (ImmInteriorIR.symm z).2.val 0) =
      (z.1, z.2 0) :=
    congrArg (fun v : ImmInteriorE2 × EuclideanSpace ℝ (Fin 1) => (v.1, v.2 0))
      (ImmInteriorIR.right_inv (by rw [← ImmInteriorIR.target_eq]; exact hz.1))
  rw [hzcoords]
  rfl
end DifferentialGeometry.Topology.ThreeManifold.Surgery
