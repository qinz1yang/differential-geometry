# Full AC75 independent acceptance

Five public theorems, one definition and two private helpers in three leaves add16 owned declarations, including8 generated declarations. The339-module gate checks1473 declarations in3174 jobs. All new closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent; nine requested reports check the actual declarations and regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves remain unchanged. The inherited AreaUpperBarrier warning is outside these closures. The blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

One agent implemented the elementary whole-KL conversion and factor quasi-inverse kernel. Root read the complete proof, including the OWN factor coverage and preservation of the full closed-ball values. A second agent implemented the full original-sequence transfer. Root and the first agent independently read its complete proof; the first agent developed and compiled a nontrivial same-Q/full-sequence regression. Final review imports the actual production leaves, not copied theorem bodies.

The factor construction is actual, not an assumed approximate inverse: h gives error3e on8R, H transports its target, and the actual g quasi-inverse has error4e on4R. Composition at2R has error14e. Its values remain in g's ORIGINAL8R domain; the inverse estimate is<e there. Coverage in the whole-KL conversion uses the radial lower bound to put the actual source witness inside the OPEN tau inverse ball, even though the map is defined globally. The generic kernel requires only metric spaces, including the shared factor.

In the sequence transfer both original maps apply at the SAME original source point. Their radial bounds establish the factor-domain membership before any conditional control is used. Both full controls use exactly f_i(x), and the global exact identity uses the given Q/H on that point. Restricting and enlarging g/h preserves values. The product perturbation inequality improves the blueprint2e+4rho estimate to2e+2rho; e=rho=tau/1000 still satisfies the stated budget. The stronger public theorem retains SAME Q and strict source-ball error; its corollary uses the identity Euclidean map. No further subsequence, geometric hypothesis, map continuity or factor completeness is introduced.

The kernel regression uses shared E=Ioi(-100), proves it incomplete, takes two incomplete source factors, inclusion approximations, and a nontrivial factor-swap isometry. At tau1/2 and e1/1000 the returned whole-factor map is within e of the swap on the FULL closed radius8 ball and carries its own coverage witnesses for every target of radius<3/2.

The full sequence regression uses X=R2 times R, basepoint(0,2), the identity rank2 map, a rank1 map with Q first coordinate-v_1, and a nontrivial residual factor swap. All common/factor approximations and full controls are constructed directly, on radii i+1 with errors1/[100(i+1)]. For every fixed tau in(0,1), both public APIs return eventual compatibility on this ORIGINAL sequence and an actual whole-factor map retaining the fixed Q and strict error. The original Euclidean orientation is checked by an exact formula.

Sources are the full frozen AC75 statement/proof and KL4.17 actual proof, with retained corrections and the documented strict/equal-rank convention. Full AC75 is complete. Uniform geometric compatibility remains AC76's separate acceptance. Chapters3-4 are not declared complete; blueprint207 and migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.SplittingCompatibilityTransfer
import DifferentialGeometry.Analysis.InnerProductSpace.OrthonormalProductCoordinates
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GCAC75KernelReview

open GC.MetricGeometry Set Metric

private abbrev E := Ioi (-100 : ℝ)
private def o : E := ⟨0, by norm_num⟩
private abbrev X := WithLp 2 (E × E)
private abbrev A := WithLp 2 (ℝ × E)
private def p : X := WithLp.toLp 2 (o, o)
private def a : A := WithLp.toLp 2 (0, o)
private def gMap (x : X) : A := WithLp.toLp 2 (x.fst.val, x.snd)

private theorem gMap_isometry : Isometry gMap := by
  apply Isometry.of_dist_eq
  intro x y
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  simp only [gMap, WithLp.prod_dist_sq_eq_add_sq, WithLp.toLp_fst, WithLp.toLp_snd,
    Subtype.dist_eq]

private def h : PointedBallApprox o (0 : ℝ) (8 * ((1 / 2 : ℝ)⁻¹ + 2)) (1 / 1000) where
  error_pos := by norm_num
  error_lt_radius := by norm_num
  toFun x := x.val.val
  basepoint := rfl
  distortion x y := by
    change |dist x.val.val y.val.val - dist x.val.val y.val.val| < (1 / 1000 : ℝ)
    norm_num
  coverage y hy := by
    have hr : 8 * ((1 / 2 : ℝ)⁻¹ + 2) = 32 := by norm_num
    rw [hr] at hy
    have ha : |y| ≤ 32 - (1 / 1000 : ℝ) := by simpa only [Real.dist_eq, sub_zero] using hy
    have hm : (-100 : ℝ) < y := by linarith [(abs_le.mp ha).1]
    refine ⟨⟨⟨y, hm⟩, ?_⟩, ?_⟩
    · rw [hr]
      change dist y 0 ≤ (32 : ℝ)
      linarith
    · change dist y y < (1 / 1000 : ℝ)
      norm_num

private def g : PointedBallApprox p a (8 * ((1 / 2 : ℝ)⁻¹ + 2)) (1 / 1000) where
  error_pos := by norm_num
  error_lt_radius := by norm_num
  toFun x := gMap x.val
  basepoint := rfl
  distortion x y := by rw [gMap_isometry.dist_eq, sub_self, abs_zero]; norm_num
  coverage y hy := by
    have hr : 8 * ((1 / 2 : ℝ)⁻¹ + 2) = 32 := by norm_num
    rw [hr] at hy
    have hs := (WithLp.dist_fst_le y a).trans hy
    change |y.fst - 0| ≤ 32 - (1 / 1000 : ℝ) at hs
    rw [sub_zero] at hs
    have hm : (-100 : ℝ) < y.fst := by linarith [(abs_le.mp hs).1]
    let x : X := WithLp.toLp 2 (⟨y.fst, hm⟩, y.snd)
    have he : gMap x = y := rfl
    have hb : gMap p = a := rfl
    have hd : dist x p = dist y a := by rw [← gMap_isometry.dist_eq, he, hb]
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [hd, hr]
      linarith
    · change dist y (gMap x) < (1 / 1000 : ℝ)
      rw [he, dist_self]
      norm_num

private theorem shared_factor_not_complete : ¬ CompleteSpace E := by
  intro hc
  let := hc
  have hs : IsClosed (Ioi (-100 : ℝ)) := by
    simpa only [Subtype.range_val] using
      (isometry_subtype_coe (s := Ioi (-100 : ℝ))).isUniformInducing.isComplete_range.isClosed
  have hb : (-100 : ℝ) ∈ closure (Ioi (-100 : ℝ)) := by
    rw [closure_Ioi]
    exact (show (-100 : ℝ) ≤ -100 from le_rfl)
  have hh := hs.closure_subset hb
  exact (lt_irrefl (-100 : ℝ)) hh

private theorem actual_whole_factor_approximation :
    ∃ F : KleinerLottApprox p p (1 / 2 : ℝ),
      (∀ x : BallCarrier p 8,
        dist (F.toFun x.val) ((IsometryEquiv.withLpProdComm 2 E E) x.val) < 1 / 1000) ∧
      ∀ y : X, dist y p < 3 / 2 →
        ∃ x ∈ ball p 2, dist y (F.toFun x) < 1 := by
  let H : WithLp 2 (E × ℝ) ≃ᵢ A := IsometryEquiv.withLpProdComm 2 E ℝ
  obtain ⟨F, hF⟩ := exists_factor_transfer_kleinerLott_approximation
    (u := o) g h H rfl (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num)
  refine ⟨F, ?_, ?_⟩
  · intro x
    have hx : dist x.val p ≤ 2 * ((1 / 2 : ℝ)⁻¹ + 2) := by norm_num; exact x.property
    obtain ⟨hFx, herr⟩ := hF ⟨x.val, hx⟩
    have hy : dist x.val.snd o ≤ 8 * ((1 / 2 : ℝ)⁻¹ + 2) := by
      have hs := (WithLp.dist_snd_le x.val p).trans x.property
      change dist x.val.snd o ≤ 8 at hs
      norm_num
      linarith
    have hd := herr hFx hy
    change dist (gMap (F.toFun x.val))
      (gMap ((IsometryEquiv.withLpProdComm 2 E E) x.val)) < (1 / 1000 : ℝ) at hd
    rwa [gMap_isometry.dist_eq] at hd
  · intro y hy
    have hh := F.coverage_witness y (by norm_num; exact hy)
    simpa [p] using hh

#print axioms shared_factor_not_complete
#print axioms actual_whole_factor_approximation

end GCAC75KernelReview

#lint- only unusedArguments simpNF synTaut

namespace GCAC75TransferReview

open GC.MetricGeometry Set Filter Metric
open scoped Topology

private abbrev E₁ := EuclideanSpace ℝ (Fin 1)
private abbrev E₂ := EuclideanSpace ℝ (Fin 2)
private abbrev A := WithLp 2 (ℝ × E₁)
private abbrev X := WithLp 2 (E₂ × ℝ)
private noncomputable def p : X := WithLp.toLp 2 (0, 2)
private noncomputable def a : A := WithLp.toLp 2 (2, 0)
private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem errors_pos (i : ℕ) : 0 < errors i := by dsimp [errors]; positivity
private theorem errors_small (i : ℕ) : errors i < 1 ∧ errors i < radius i := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors, radius]
  constructor <;> linarith
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100

private def identityApprox {T : Type*} [MetricSpace T] (o : T) (i : ℕ) :
    PointedBallApprox o o (radius i) (errors i) where
  error_pos := errors_pos i
  error_lt_radius := (errors_small i).2
  toFun x := x.val
  basepoint := rfl
  distortion x y := by norm_num; exact errors_pos i
  coverage y hy := by
    refine ⟨⟨y, by linarith [errors_pos i]⟩, ?_⟩
    simpa only [dist_self] using errors_pos i

private theorem reversed_axis_orthonormal :
    Orthonormal ℝ (fun _ : Fin 1 => (PiLp.single 2 (1 : Fin 2) (-1) : E₂)) := by
  rw [orthonormal_iff_ite]
  intro i l
  have hil : i = l := Subsingleton.elim _ _
  subst l
  simp only [ite_true]
  rw [EuclideanSpace.inner_single_left]
  norm_num

private theorem full_sequence_reversed_coordinate_transfer :
    ∃ Q : E₂ ≃ₗᵢ[ℝ] WithLp 2 (E₁ × E₁),
    ∃ φ : ∀ i, KleinerLottApprox p (WithLp.toLp 2 ((0 : E₁), a)) (errors i),
    ∃ ψ : ∀ i, KleinerLottApprox p (WithLp.toLp 2 ((0 : E₂), (2 : ℝ))) (errors i),
      (∀ v, (Q v).fst 0 = -v 1) ∧
      (∀ i x, (ψ i).toFun x = x) ∧
      (∀ i x, (φ i).toFun x = WithLp.toLp 2 ((Q x.fst).fst,
        WithLp.toLp 2 (x.snd, (Q x.fst).snd))) ∧
      ∀ τ : ℝ, 0 < τ → τ < 1 → ∀ᶠ i in atTop,
        SplittingCompatible (φ i) (ψ i) τ ∧
        ∃ F : KleinerLottApprox (WithLp.toLp 2 ((0 : E₁), (2 : ℝ))) a τ,
          ∀ x ∈ ball p τ⁻¹,
            dist (WithLp.toLp 2 ((Q ((ψ i).toFun x).fst).fst,
              F.toFun (WithLp.toLp 2 ((Q ((ψ i).toFun x).fst).snd, ((ψ i).toFun x).snd))))
              ((φ i).toFun x) < τ := by
  obtain ⟨Q, hQ⟩ := reversed_axis_orthonormal.exists_euclidean_product_coordinates
    (by decide : 1 ≤ 2)
  let H : WithLp 2 (E₁ × ℝ) ≃ᵢ A := IsometryEquiv.withLpProdComm 2 E₁ ℝ
  let eA : X ≃ᵢ WithLp 2 (E₁ × A) :=
    ((IsometryEquiv.withLpProdCongr 2 Q.toIsometryEquiv (IsometryEquiv.refl ℝ)).trans
      (IsometryEquiv.withLpProdAssoc 2 E₁ E₁ ℝ)).trans
        (IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl E₁) H)
  let eB := IsometryEquiv.refl X
  have heA : eA p = WithLp.toLp 2 ((0 : E₁), a) := by
    simp [eA, p, a, H]
    exact ⟨rfl, rfl⟩
  let φ (i : ℕ) := eA.toKleinerLottApprox heA (errors_pos i) (errors_small i).1
  let ψ (i : ℕ) := eB.toKleinerLottApprox (show eB p = WithLp.toLp 2 ((0 : E₂), (2 : ℝ)) from rfl)
    (errors_pos i) (errors_small i).1
  have hcontrol : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ radius i ∧ ∀ x : BallCarrier p (radius i), dist x.val p ≤ S →
        (dist ((φ i).toFun x.val).snd a ≤ radius i ∧
          ∀ hx : dist ((φ i).toFun x.val).snd a ≤ radius i,
            dist (WithLp.toLp 2 (((φ i).toFun x.val).fst,
              (identityApprox a i).toFun ⟨((φ i).toFun x.val).snd, hx⟩))
              (eA ((identityApprox p i).toFun x)) < ζ) ∧
        (dist ((ψ i).toFun x.val).snd (2 : ℝ) ≤ radius i ∧
          ∀ hx : dist ((ψ i).toFun x.val).snd (2 : ℝ) ≤ radius i,
            dist (WithLp.toLp 2 (((ψ i).toFun x.val).fst,
              (identityApprox (2 : ℝ) i).toFun ⟨((ψ i).toFun x.val).snd, hx⟩))
              (eB ((identityApprox p i).toFun x)) < ζ) := by
    intro S ζ hζ
    filter_upwards [radius_top.eventually (eventually_ge_atTop S)] with i hi
    refine ⟨hi, fun x hx => ?_⟩
    constructor
    · refine ⟨?_, fun _ => ?_⟩
      · have hh := WithLp.dist_snd_le (eA x.val) (eA p)
        rw [eA.dist_eq, heA] at hh
        exact hh.trans (hx.trans hi)
      · change dist (eA x.val) (eA x.val) < ζ
        simpa only [dist_self] using hζ
    · refine ⟨?_, fun _ => ?_⟩
      · exact (WithLp.dist_snd_le x.val p).trans (hx.trans hi)
      · change dist x.val x.val < ζ
        simpa only [dist_self] using hζ
  refine ⟨Q, φ, ψ, ?_, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  · intro v
    rw [hQ]
    simp [EuclideanSpace.inner_single_right]
  · intro τ hτ hτone
    have hmap := eventually_exists_compatibility_map_of_full_product_convergence
      φ ψ errors_zero errors_zero (identityApprox p) (identityApprox a) (identityApprox (2 : ℝ))
      radius_top errors_zero radius_top errors_zero eA eB hcontrol Q H rfl
      (fun _ => rfl) hτ hτone
    have hcompatible := eventually_splittingCompatible_of_full_product_convergence
      φ ψ errors_zero errors_zero (identityApprox p) (identityApprox a) (identityApprox (2 : ℝ))
      radius_top errors_zero radius_top errors_zero eA eB hcontrol Q H rfl
      (fun _ => rfl) hτ hτone (by decide : 1 ≤ 2)
    exact hcompatible.and hmap

#print axioms full_sequence_reversed_coordinate_transfer

end GCAC75TransferReview

#lint- only unusedArguments simpNF synTaut

#print axioms GC.MetricGeometry.PointedBallApprox.toKleinerLottOfSmallError
#print axioms GC.MetricGeometry.PointedBallApprox.toKleinerLottOfSmallError_apply
#print axioms GC.MetricGeometry.exists_factor_transfer_approximation
#print axioms GC.MetricGeometry.exists_factor_transfer_kleinerLott_approximation
#print axioms GC.MetricGeometry.eventually_exists_compatibility_map_of_full_product_convergence
#print axioms GC.MetricGeometry.eventually_splittingCompatible_of_full_product_convergence
```
