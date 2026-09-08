import Mathlib.Analysis.CStarAlgebra.Basic
import DifferentialGeometry.Analysis.ODE.HamiltonIvey
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.SelfAdjointRegion
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree
open Set Filter
open scoped Topology NNReal Matrix.Norms.Elementwise
open DifferentialGeometry.Analysis.ODE

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private def selfAdjointMatrixMap (b : OrthonormalBasis (Fin 3) ℝ W) :
    selfAdjoint (W →L[ℝ] W) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  { toFun := fun A => LinearMap.toMatrix b.toBasis b.toBasis (A : W →L[ℝ] W).toLinearMap
    map_add' := by intros; simp
    map_smul' := by intros; simp }

private theorem selfAdjointMatrixMap_continuous (b : OrthonormalBasis (Fin 3) ℝ W) :
    Continuous (selfAdjointMatrixMap b) := by
  change Continuous (fun A : selfAdjoint (W →L[ℝ] W) =>
    LinearMap.toMatrix b.toBasis b.toBasis (A : W →L[ℝ] W).toLinearMap)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simpa only [LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply] using!
    (continuous_const.inner (continuous_subtype_val.clm_apply continuous_const) :
      Continuous (fun A : selfAdjoint (W →L[ℝ] W) =>
        inner ℝ (b i) ((A : W →L[ℝ] W) (b j))))

private theorem selfAdjointMatrixMap_reaction (b : OrthonormalBasis (Fin 3) ℝ W)
    (A : selfAdjoint (W →L[ℝ] W)) :
    selfAdjointMatrixMap b (curvatureOperatorReactionSelfAdjoint3 A) =
      curvatureOperatorReaction3 (selfAdjointMatrixMap b A) := by
  change LinearMap.toMatrix b.toBasis b.toBasis
      (curvatureOperatorReactionEndomorphism3 (A : W →L[ℝ] W).toLinearMap) = _
  exact curvatureOperatorReactionEndomorphism3_toMatrix b.toBasis _

private theorem selfAdjointMatrixMap_region (b : OrthonormalBasis (Fin 3) ℝ W) (A : selfAdjoint (W →L[ℝ] W)) :
    A ∈ hamiltonIveyRegion (W := W) 1 ↔
      selfAdjointMatrixMap b A ∈ hamiltonIveyConvexMatrixRegion 1 0 := by
  exact mem_hamiltonIveyRegion_iff_toMatrix b (K := 1) (by norm_num) A


private theorem mem_posTangentConeAt_smul_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {x v : E} {c : ℝ} (hc : 0 ≤ c)
    (hv : v ∈ posTangentConeAt C x) : c • v ∈ posTangentConeAt C x := by
  rcases exists_fun_of_mem_tangentConeAt hv with ⟨ι, l, hl, d, e, he₀, heC, hde⟩
  let c' : ℝ≥0 := ⟨c, hc⟩
  refine mem_tangentConeAt_of_seq l (fun n => c' * d n) e he₀ heC ?_
  apply Tendsto.congr' _ (hde.const_smul c)
  filter_upwards with n
  change c • (d n : ℝ) • e n = ((c' * d n : ℝ≥0) : ℝ) • e n
  rw [NNReal.coe_mul, smul_smul]
  congr 1

private theorem nonnegative_time_multiple_hamiltonIvey_matrix
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hanonneg : ∀ t, 0 ≤ a t) :
    IsForwardInvariantForODE
      (fun t A => a t • (A + curvatureOperatorReaction3 A))
      (hamiltonIveyConvexMatrixRegion 1 0) := by
  apply nagumo_isForwardInvariantForODE_of_contDiff
    (isClosed_hamiltonIveyConvexMatrixRegion (K := 1) (by norm_num))
    (convex_hamiltonIveyConvexMatrixRegion (K := 1) (by norm_num) (by norm_num))
  · intro t A hA
    apply mem_posTangentConeAt_smul_nonneg (hanonneg t)
    simpa only [one_smul] using!
      smul_add_curvatureOperatorReaction3_mem_posTangentConeAt (K := 1) (by norm_num) hA
  · change ContDiff ℝ 1 (Function.uncurry (fun t A => a t • (A + curvatureOperatorReaction3 A)))
    have hQ : ContDiff ℝ 1 curvatureOperatorReaction3 :=
      contDiff_curvatureOperatorReaction3.of_le (by norm_num)
    exact (ha.comp contDiff_fst).smul (contDiff_snd.add (hQ.comp contDiff_snd))

theorem isForwardInvariantForODE_hamiltonIveyRegion_smul
    (hdim : Module.finrank ℝ W = 3)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hanonneg : ∀ t, 0 ≤ a t) :
    IsForwardInvariantForODE
      (fun t A => a t • (A + curvatureOperatorReactionSelfAdjoint3 A))
      (hamiltonIveyRegion (W := W) 1) := by
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  let L : selfAdjoint (W →L[ℝ] W) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    { toLinearMap := selfAdjointMatrixMap b
      cont := selfAdjointMatrixMap_continuous b }
  have hL : ∀ t ∈ (univ : Set ℝ), ∀ A : selfAdjoint (W →L[ℝ] W),
      L (a t • (A + curvatureOperatorReactionSelfAdjoint3 A)) =
        a t • (L A + curvatureOperatorReaction3 (L A)) := by
    intro t _ A
    rw [map_smul, map_add]
    congr 2
    exact selfAdjointMatrixMap_reaction b A
  have hset : hamiltonIveyRegion (W := W) 1 =
      L ⁻¹' hamiltonIveyConvexMatrixRegion 1 0 := by
    ext A
    exact selfAdjointMatrixMap_region b A
  intro t u htu γ hγ hinit
  have hmat := (isForwardInvariantForODEOn_univ.mpr
      (nonnegative_time_multiple_hamiltonIvey_matrix ha hanonneg)).preimage L hL
      t u htu (subset_univ _) γ hγ
      ((hset ▸ hinit))
  intro s hs
  have hm := hmat hs
  exact (selfAdjointMatrixMap_region b (γ s)).mpr hm



theorem isForwardInvariantForODE_hamiltonIveyRegion_normalized
    (hdim : Module.finrank ℝ W = 3) :
    IsForwardInvariantForODE
      (fun _ A => A + curvatureOperatorReactionSelfAdjoint3 A)
      (hamiltonIveyRegion (W := W) 1) := by
  simpa only [one_smul] using
    (isForwardInvariantForODE_hamiltonIveyRegion_smul (W := W) hdim
      (a := fun _ : ℝ => 1) contDiff_const (fun _ => by norm_num))


end DifferentialGeometry.Geometry.Curvature.DimensionThree
