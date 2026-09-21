import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakLaplacian.HolderRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence.Local
import DifferentialGeometry.Analysis.Schauder.Holder.QuadraticSource
import DifferentialGeometry.Analysis.Schauder.Holder.IteratedDerivative
import DifferentialGeometry.Analysis.Schauder.Holder.Localization
import DifferentialGeometry.Analysis.Elliptic.Euclidean.SemilinearRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Analysis.Schauder
open scoped Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_contDiffOn_two_of_quadratic_weak_system
    {z : V → F} {R : ℝ} (hR : 0 < R)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hz1 : ContDiffOn ℝ 1 z (ball (0 : V) R))
    {G : ι → V → V} (hGeq : ∀ i, G i =ᵐ[volume.restrict (ball (0 : V) R)] (hz i).weakGrad)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hHolder : ∀ i, ∀ x ∈ ball (0 : V) R, ∀ y ∈ ball (0 : V) R,
      ‖G i x - G i y‖ ≤ C i * ‖x - y‖ ^ (α : ℝ))
    {U : Set F} (hU : IsOpen U) (hzU : MapsTo z (ball (0 : V) R) U)
    (A : ι → ι → ι → F → ℝ) (hA : ∀ k i j, ContDiffOn ℝ 1 (A k i j) U)
    (hdiv : ∀ k, DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin d, ∑ i, ∑ l,
      A k i l (z x) * (hz i).weakGrad x j * (hz l).weakGrad x j))
        (hz k).weakGrad (ball (0 : V) R)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ContDiffOn ℝ 2 z (ball (0 : V) r) ∧
      ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 2 z) (ball (0 : V) r) := by
  classical
  let ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have hρR : ρ < R := half_lt_self hR
  have hclosed : closedBall (0 : V) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hball : ball (0 : V) ρ ⊆ ball 0 R := ball_subset_closedBall.trans hclosed
  obtain ⟨Kz, hzH⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact
    (isCompact_closedBall (0 : V) ρ) (convex_closedBall _ _) (hz1.mono hclosed) hα1.le
  have hzH' : HolderOnWith Kz α z (closedBall (0 : V) ρ) := HolderWith.restrict_iff.mp hzH
  let CG (i : ι) : ℝ≥0 := ⟨C i, hC i⟩
  have hGH (i : ι) (j : Fin d) : HolderOnWith (CG i) α (fun x => G i x j)
      (closedBall (0 : V) ρ) := by
    intro x hx y hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]
    have hcoe : (CG i : ℝ≥0∞) = ENNReal.ofReal (C i) := ENNReal.ofReal_coe_nnreal.symm
    rw [hcoe, ← ENNReal.ofReal_mul (hC i)]
    apply ENNReal.ofReal_le_ofReal
    have hn := PiLp.norm_apply_le (G i x - G i y) j
    simpa only [Real.dist_eq, dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
      hn.trans (hHolder i x (hclosed hx) y (hclosed hy))
  let Fk (k : ι) (x : V) := -(∑ j : Fin d, ∑ i, ∑ l,
    A k i l (z x) * G i x j * G l x j)
  have hFH (k : ι) : ∃ K : ℝ≥0, HolderOnWith K α (Fk k) (closedBall (0 : V) ρ) := by
    obtain ⟨K, hK⟩ := exists_holderOnWith_quadratic_sum_of_contDiffOn_coefficients
      (isCompact_closedBall (0 : V) ρ) hU hα hzH' (hzU.mono_left hclosed) (hA k) hGH
    refine ⟨K, ?_⟩
    intro x hx y hy
    simpa only [Fk, edist_neg_neg] using hK x hx y hy
  choose KF hKF using hFH
  have hFLp (k : ι) : MemLp (Fk k) 2 (volume.restrict (ball (0 : V) ρ)) := by
    let : IsFiniteMeasure (volume.restrict (ball (0 : V) ρ)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hc := (hKF k).continuousOn hα
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) ρ).exists_bound_of_continuousOn hc
    apply MemLp.of_bound
      ((hc.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) B
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hB x (ball_subset_closedBall hx)
  let hzρ (i : ι) := (hz i).restrict isOpen_ball hball
  have hGρ (i : ι) : G i =ᵐ[volume.restrict (ball (0 : V) ρ)] (hzρ i).weakGrad :=
    ae_restrict_of_ae_restrict_of_subset hball (hGeq i)
  have hdivF (k : ι) : DeGiorgi.HasWeakDiv (Fk k) (hzρ k).weakGrad (ball (0 : V) ρ) := by
    apply ((hdiv k).restrict hball).congr_ae _ EventuallyEq.rfl
    filter_upwards [ae_all_iff.mpr hGρ] with x hx
    simp only [Fk, hx]
    rfl
  have hzHs (k : ι) : ∃ K : ℝ≥0, HolderOnWith K α (fun x => z x k) (closedBall (0 : V) ρ) := by
    have hzk : ContDiffOn ℝ 1 (fun x => z x k) (closedBall (0 : V) ρ) :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn (hz1.mono hclosed)
    obtain ⟨K, hK⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact
      (isCompact_closedBall (0 : V) ρ) (convex_closedBall _ _) hzk hα1.le
    exact ⟨K, HolderWith.restrict_iff.mp hK⟩
  choose Ku hKu using hzHs
  have hsub : closedBall (0 : V) (ρ / 2) ⊆ ball 0 ρ := closedBall_subset_ball (half_lt_self hρ)
  have hsubc : closedBall (0 : V) (ρ / 2) ⊆ closedBall 0 ρ := hsub.trans ball_subset_closedBall
  have hresult (k : ι) : ∃ K : ℝ≥0, ContDiffOn ℝ 2 (fun x => z x k) (ball (0 : V) (ρ / 4)) ∧
      HolderOnWith K α (iteratedFDeriv ℝ 2 (fun x => z x k)) (ball (0 : V) (ρ / 4)) := by
    have h := exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_ball
      isOpen_ball (hzρ k) (hFLp k) (hdivF k) (hGρ k) (half_pos hρ) hsub hα hα1
      ((hKu k).mono hsubc) ((hKF k).mono hsubc) (fun j => (hGH k j).mono hsubc)
    simpa only [show ρ / 2 / 2 = ρ / 4 by ring] using h
  choose K hK2 hKH using hresult
  have hz2 : ContDiffOn ℝ 2 z (ball (0 : V) (ρ / 4)) := contDiffOn_piLp' 2 hK2
  obtain ⟨KH, hHess⟩ := exists_holderOnWith_iteratedFDeriv_of_components isOpen_ball hz2
    (fun k => ⟨K k, hKH k⟩)
  exact ⟨ρ / 4, by positivity, by dsimp only [ρ]; linarith, hz2, KH, hHess⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Analysis.Schauder
open scoped Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem contDiffOn_quadratic_firstJet_source
    {U : Set F} (A : ι → ι → ι → F → ℝ)
    (hA : ∀ k i j, ContDiffOn ℝ ∞ (A k i j) U) :
    ContDiffOn ℝ ∞ (fun q : V × F × (V →L[ℝ] F) =>
      (WithLp.toLp 2 (fun k => -(∑ j : Fin d, ∑ i, ∑ l,
        A k i l q.2.1 * (q.2.2 (EuclideanSpace.single j 1)) i *
          (q.2.2 (EuclideanSpace.single j 1)) l)) : F)) (univ ×ˢ U ×ˢ univ) := by
  apply contDiffOn_piLp' 2
  intro k
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro j hj
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro l hl
  have hcoeff : ContDiffOn ℝ ∞ (fun q : V × F × (V →L[ℝ] F) => A k i l q.2.1)
      (univ ×ˢ U ×ˢ univ) :=
    (hA k i l).comp (contDiffOn_fst.comp contDiffOn_snd (mapsTo_univ _ _))
      (fun q hq => hq.2.1)
  have hcol (a : ι) : ContDiff ℝ ∞ (fun q : V × F × (V →L[ℝ] F) =>
      (q.2.2 (EuclideanSpace.single j 1)) a) :=
    (contDiff_piLp_apply (p := 2) (i := a)).comp
      ((contDiff_snd.comp contDiff_snd).clm_apply contDiff_const)
  exact (hcoeff.mul (hcol i).contDiffOn).mul (hcol l).contDiffOn

theorem exists_contDiffOn_of_quadratic_weak_system
    {z : V → F} {R : ℝ} (hR : 0 < R)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hz1 : ContDiffOn ℝ 1 z (ball (0 : V) R))
    {G : ι → V → V} (hGeq : ∀ i, G i =ᵐ[volume.restrict (ball (0 : V) R)] (hz i).weakGrad)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hHolder : ∀ i, ∀ x ∈ ball (0 : V) R, ∀ y ∈ ball (0 : V) R,
      ‖G i x - G i y‖ ≤ C i * ‖x - y‖ ^ (α : ℝ))
    {U : Set F} (hU : IsOpen U) (hzU : MapsTo z (ball (0 : V) R) U)
    (A : ι → ι → ι → F → ℝ) (hA : ∀ k i j, ContDiffOn ℝ ∞ (A k i j) U)
    (hdiv : ∀ k, DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin d, ∑ i, ∑ l,
      A k i l (z x) * (hz i).weakGrad x j * (hz l).weakGrad x j))
        (hz k).weakGrad (ball (0 : V) R)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ContDiffOn ℝ ∞ z (ball (0 : V) r) := by
  obtain ⟨r₀, hr₀, hr₀R, hz2, K, hHess⟩ := exists_contDiffOn_two_of_quadratic_weak_system
    hR hz hz1 hGeq hα hα1 C hC hHolder hU hzU A (fun k i j => (hA k i j).of_le (by simp)) hdiv
  let r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hrr₀ : r < r₀ := half_lt_self hr₀
  have hrR : r < R := hrr₀.trans hr₀R
  have hsub : ball (0 : V) r ⊆ ball 0 R := ball_subset_ball hrR.le
  have hsub₀ : ball (0 : V) r ⊆ ball 0 r₀ := ball_subset_ball hrr₀.le
  let S (q : V × F × (V →L[ℝ] F)) : F := WithLp.toLp 2 (fun k => -(∑ j : Fin d,
    ∑ i, ∑ l, A k i l q.2.1 * (q.2.2 (EuclideanSpace.single j 1)) i *
      (q.2.2 (EuclideanSpace.single j 1)) l))
  let T : Set (V × F × (V →L[ℝ] F)) := univ ×ˢ U ×ˢ univ
  have hT : IsOpen T := isOpen_univ.prod (hU.prod isOpen_univ)
  have hzT : MapsTo (fun x => (x, z x, fderiv ℝ z x)) (ball (0 : V) r) T :=
    fun x hx => ⟨mem_univ _, hzU (hsub hx), mem_univ _⟩
  have hpartial (k : ι) : (hz k).weakGrad =ᵐ[volume.restrict (ball (0 : V) r)]
      DeGiorgi.smoothGradField (fun x => z x k) := by
    have hzk : ContDiffOn ℝ 1 (fun x => z x k) (ball (0 : V) R) :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn hz1
    exact (hz k).weakGrad_ae_eq_smoothGradField_on_ball (by norm_num) isOpen_ball hzk
      (closedBall_subset_ball hrR)
  have hcolumn (k : ι) (x : V) (hx : x ∈ ball (0 : V) r) (j : Fin d) :
      DeGiorgi.smoothGradField (fun y => z y k) x j =
        (fderiv ℝ z x (EuclideanSpace.single j 1)) k := by
    let L : F →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) k
    have hd := L.hasFDerivAt.comp x
      ((hz1.contDiffAt (isOpen_ball.mem_nhds (hsub hx))).differentiableAt (by simp)).hasFDerivAt
    change fderiv ℝ (L ∘ z) x (EuclideanSpace.single j 1) = _
    rw [hd.fderiv]
    rfl
  have hdivS (k : ι) : DeGiorgi.HasWeakDiv (fun x => S (x, z x, fderiv ℝ z x) k)
      (DeGiorgi.smoothGradField (fun x => z x k)) (ball (0 : V) r) := by
    apply ((hdiv k).restrict hsub).congr_ae _ (hpartial k)
    filter_upwards [ae_all_iff.mpr hpartial, ae_restrict_mem measurableSet_ball] with x hx hxB
    change -(∑ j : Fin d, ∑ i, ∑ l,
      A k i l (z x) * (hz i).weakGrad x j * (hz l).weakGrad x j) = S (x, z x, fderiv ℝ z x) k
    simp only [S, hx, hcolumn _ x hxB]
  refine ⟨r, hr, hrR, ?_⟩
  exact contDiffOn_of_semilinear_weak_laplacian (hz2.mono hsub₀) hα hα1 (hHess.mono hsub₀)
    hT hzT (contDiffOn_quadratic_firstJet_source A hA) hdivS

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
