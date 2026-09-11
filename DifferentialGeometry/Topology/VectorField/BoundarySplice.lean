import DifferentialGeometry.Topology.VectorField.IndexComparison
import DifferentialGeometry.Topology.VectorField.IndexSumZeroGerm
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I ∞ M]


def affineSection (V W : ∀ x : M, TangentSpace I x) (t : ℝ) (x : M) : TangentSpace I x :=
  (1 - t) • V x + t • W x

omit [T2Space M] [CompactSpace M] in
private theorem contMDiff_affineSection
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M))) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, affineSection I V W q.1 q.2⟩ : TangentBundle I M)) := by
  intro q
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, ?_⟩
  let e := trivializationAt (EuclideanSpace ℝ (Fin (d + 1))) (TangentSpace I) q.2
  have hv := (contMDiffAt_section q.2).mp (hV q.2)
  have hw := (contMDiffAt_section q.2).mp (hW q.2)
  have hs : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) ∞
      (fun z : ℝ × M => (1 - z.1) • (e ⟨z.2, V z.2⟩).2 + z.1 • (e ⟨z.2, W z.2⟩).2) q :=
    ((contMDiffAt_const.sub contMDiffAt_fst).smul (hv.comp q contMDiffAt_snd)).add
      (contMDiffAt_fst.smul (hw.comp q contMDiffAt_snd))
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ q.2))] with z hz
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ z.2 hz]
  simp only [affineSection, map_add, map_smul]
  congr 1

omit [T2Space M] [CompactSpace M] in
theorem exists_open_affineSection_ne_zero
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)))
    {B : Set M} (hn : ∀ x ∈ B, ∀ t : unitInterval, affineSection I V W t x ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ B ⊆ U ∧
      ∀ x ∈ U, ∀ t : unitInterval, affineSection I V W t x ≠ 0 := by
  let Z := {q : unitInterval × M | affineSection I V W q.1 q.2 = 0}
  have hc : Continuous (fun q : unitInterval × M =>
      (⟨q.2, affineSection I V W q.1 q.2⟩ : TangentBundle I M)) :=
    (contMDiff_affineSection I V W hV hW).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hZ : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_eventually]
    intro q hq
    let e := trivializationAt (EuclideanSpace ℝ (Fin (d + 1))) (TangentSpace I) q.2
    have he := mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin (d + 1))) (TangentSpace I) q.2
    have hcoord := (FiberBundle.continuousAt_totalSpace _ _).mp (hc.continuousAt (x := q)) |>.2
    have hncoord : (e ⟨q.2, affineSection I V W q.1 q.2⟩).2 ≠ 0 := by
      rw [e.apply_eq_prod_continuousLinearEquivAt ℝ q.2 he]
      exact (e.continuousLinearEquivAt ℝ q.2 he).map_ne_zero_iff.mpr hq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he),
      hcoord.eventually_ne hncoord] with z hz hnz
    intro hzero
    apply hnz
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ z.2 hz]
    change e.continuousLinearEquivAt ℝ z.2 hz (affineSection I V W z.1 z.2) = 0
    rw [hzero, map_zero]
  refine ⟨(Prod.snd '' Z)ᶜ, (isClosedMap_snd_of_compactSpace Z hZ).isOpen_compl, ?_, ?_⟩
  · intro x hx
    rintro ⟨q, hq, rfl⟩
    exact hn q.2 hx q.1 hq
  · intro x hx t hz
    exact hx ⟨(t, x), hz, rfl⟩

theorem exists_boundary_splice_preserving_zero_germs
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)))
    {B : Set M} (hB : IsClosed B)
    (hn : ∀ x ∈ B, ∀ t : unitInterval, affineSection I V W t x ≠ 0) :
    ∃ (G : ∀ x : M, TangentSpace I x),
      ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) ∧
      (∀ x ∈ B, G =ᶠ[𝓝 x] W) ∧ {x | G x = 0} = {x | V x = 0} ∧
      (∀ x, V x = 0 → G =ᶠ[𝓝 x] V) := by
  obtain ⟨U, hU, hBU, hUn⟩ := exists_open_affineSection_ne_zero I V W hV hW hn
  obtain ⟨ρ, hρzero, hρone, hρrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    I hU.isClosed_compl hB (disjoint_compl_left_iff.mpr hBU) (n := (⊤ : ℕ∞))
  let G := fun x => affineSection I V W (ρ x) x
  have hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) :=
    ((contMDiff_const.sub ρ.contMDiff).smul_section hV).add_section (ρ.contMDiff.smul_section hW)
  have hVoutside : ∀ x, V x = 0 → x ∉ U := by
    intro x hz hx
    exact hUn x hx 0 (by simpa [affineSection] using hz)
  have hGoutside : ∀ x, G x = 0 → x ∉ U := by
    intro x hz hx
    exact hUn x hx ⟨ρ x, hρrange x⟩ hz
  have hzeroGerm : ∀ x ∉ U, G =ᶠ[𝓝 x] V := by
    intro x hx
    filter_upwards [hρzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [G, affineSection, hy, sub_zero, one_smul, zero_smul, add_zero]
    rfl
  refine ⟨G, hG, ?_, ?_, fun x hx => hzeroGerm x (hVoutside x hx)⟩
  · intro x hx
    filter_upwards [hρone.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [G, affineSection, hy, sub_self, zero_smul, one_smul, zero_add]
    rfl
  · ext x
    constructor
    · intro hz
      exact (hzeroGerm x (hGoutside x hz)).self_of_nhds.symm.trans hz
    · intro hz
      exact (hzeroGerm x (hVoutside x hz)).self_of_nhds.trans hz

theorem interiorIndexSum_eq_of_boundary_affine_ne_zero
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)))
    (hVfinite : {x | V x = 0}.Finite)
    (hVisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVint : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (hWfinite : {x | W x = 0}.Finite)
    (hWisolated : ∀ x, W x = 0 → HasContinuousIsolatedZero I W x)
    (hWint : ∀ x, W x = 0 → I.IsInteriorPoint x)
    (hboundary : ∀ x, ¬I.IsInteriorPoint x →
      ∀ t : unitInterval, affineSection I V W t x ≠ 0) :
    interiorIndexSum I V hVfinite hVisolated hVint =
      interiorIndexSum I W hWfinite hWisolated hWint := by
  obtain ⟨G, hG, hGb, hz, hgerm⟩ := exists_boundary_splice_preserving_zero_germs I V W hV hW
    (I.isOpen_interior (n := ∞) (by simp)).isClosed_compl hboundary
  have hGfinite : {x | G x = 0}.Finite := hz ▸ hVfinite
  have hGzero (x : M) (hx : G x = 0) : V x = 0 := by
    exact (congrArg (fun s : Set M => x ∈ s) hz).mp hx
  have hGiso (x : M) (hx : G x = 0) : HasContinuousIsolatedZero I G x :=
    (hVisolated x (hGzero x hx)).congr (hgerm x (hGzero x hx)).symm
  have hGint (x : M) (hx : G x = 0) : I.IsInteriorPoint x := hVint x (hGzero x hx)
  have he := interiorIndexSum_eq_of_zero_germ I G V hGfinite hGiso hGint
    hVfinite hVisolated hVint hz (fun x hx => hgerm x (hGzero x hx))
  exact he.symm.trans (interiorIndexSum_eq_of_boundary_germ I G W hG hW
    hGfinite hGiso hGint hWfinite hWisolated hWint hGb)

end DifferentialGeometry.VectorField
