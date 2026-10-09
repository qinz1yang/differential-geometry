import DifferentialGeometry.Topology.Manifold.RegularZero.ManifoldAtlas

/-!
# Tangent spaces of manifold regular-zero fibres

The inclusion has injective differential, and its image is precisely the kernel of the original
map's vector-valued manifold derivative. Both statements use the actual regular-zero atlas.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Manifold.RegularZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {m : ℕ∞ω} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem injective_mfderiv_manifold_val (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) (z : {x : M // t x = 0}) :
    letI := manifoldChartedSpace hm t ht hreg
    Injective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
      (Subtype.val : {x : M // t x = 0} → M) z) := by
  let _ := manifoldChartedSpace hm t ht hreg
  let _ := manifold_isManifold hm t ht hreg
  let : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  let P := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  let : IsManifold 𝓘(ℝ, P) 1 {x : M // t x = 0} :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  let Φ := manifoldCoordinates hm t ht hreg z
  let ψ : M → P := fun x => (Φ x).2
  have hz : z.val ∈ Φ.source := (manifoldCoordinates_spec hm t ht hreg z).1
  have hψ : MDifferentiableAt I 𝓘(ℝ, P) ψ z.val :=
    (contDiff_snd.contMDiff.contMDiffAt.comp z.val
      (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hz))).mdifferentiableAt hm
  have hi := (contMDiff_manifold_val hm t ht hreg z).mdifferentiableAt hm
  have he : mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) (extChartAt 𝓘(ℝ, P) z) z =
      (mfderiv I 𝓘(ℝ, P) ψ z.val).comp
        (mfderiv 𝓘(ℝ, P) I (Subtype.val : {x : M // t x = 0} → M) z) :=
    mfderiv_comp z hψ hi
  rw [mfderiv_extChartAt_self] at he
  intro v w hvw
  have hh := congrArg (mfderiv I 𝓘(ℝ, P) ψ z.val) hvw
  change ((mfderiv I 𝓘(ℝ, P) ψ z.val).comp
    (mfderiv 𝓘(ℝ, P) I (Subtype.val : {x : M // t x = 0} → M) z)) v =
    ((mfderiv I 𝓘(ℝ, P) ψ z.val).comp
    (mfderiv 𝓘(ℝ, P) I (Subtype.val : {x : M // t x = 0} → M) z)) w at hh
  rw [← he] at hh
  change v = w at hh
  exact hh

theorem range_mfderiv_manifold_val (hm : m ≠ 0) (t : M → F)
    (ht : ContMDiff I 𝓘(ℝ, F) m t)
    (hreg : ∀ x, t x = 0 → Surjective (mvfderiv I t x)) (z : {x : M // t x = 0}) :
    letI := manifoldChartedSpace hm t ht hreg
    LinearMap.range (mfderiv
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
      (Subtype.val : {x : M // t x = 0} → M) z).toLinearMap =
      LinearMap.ker (mvfderiv I t z.val).toLinearMap := by
  let _ := manifoldChartedSpace hm t ht hreg
  let P := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  let L := mfderiv 𝓘(ℝ, P) I (Subtype.val : {x : M // t x = 0} → M) z
  have hi := (contMDiff_manifold_val hm t ht hreg z).mdifferentiableAt hm
  have hd := mvfderiv_comp z ((ht z.val).mdifferentiableAt hm) hi
  have hzero : (t ∘ (Subtype.val : {x : M // t x = 0} → M)) = fun _x => 0 :=
    funext fun x => x.property
  rw [hzero, mvfderiv_const] at hd
  have hle : L.toLinearMap.range ≤ (mvfderiv I t z.val).ker := by
    rintro v ⟨w, rfl⟩
    exact (DFunLike.congr_fun hd w).symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj
    (injective_mfderiv_manifold_val hm t ht hreg z)]
  have hdim := (mvfderiv I t z.val).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hreg z.val z.property), finrank_top] at hdim
  change Module.finrank ℝ P = _
  rw [Module.finrank_fin_fun]
  change Module.finrank ℝ F + Module.finrank ℝ (mvfderiv I t z.val).toLinearMap.ker =
    Module.finrank ℝ E at hdim
  omega

end DifferentialGeometry.Manifold.RegularZero
