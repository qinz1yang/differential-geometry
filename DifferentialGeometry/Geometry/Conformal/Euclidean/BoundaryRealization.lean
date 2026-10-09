/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Conformal.Euclidean.Liouville
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.MobiusTransformations
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

open DifferentialGeometry.ProjectiveOrthogonalGroup
open Matrix
open scoped Topology

namespace DifferentialGeometry.LiouvilleBoundary

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.MobiusBoundary
open DifferentialGeometry.LiouvilleRigidity

variable {m : ℕ}

noncomputable def eucEquiv : ES m ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ

theorem eucEquiv_apply_coord (u : ES m) (i : Fin m) : eucEquiv u i = u i := rfl

theorem eucEquiv_symm_apply_coord (x : Fin m → ℝ) (i : Fin m) :
    (eucEquiv.symm x : ES m) i = x i := rfl

theorem dotB_eq_inner (x y : Fin m → ℝ) :
    @inner ℝ (ES m) _ (eucEquiv.symm x) (eucEquiv.symm y) = dotB x y := by
  rw [PiLp.inner_apply]
  simp [dotB, eucEquiv_symm_apply_coord, RCLike.inner_apply, mul_comm]

noncomputable def transLinear (li : ES m →ₗᵢ[ℝ] ES m) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  eucEquiv.toLinearEquiv.toLinearMap ∘ₗ li.toLinearMap
    ∘ₗ eucEquiv.symm.toLinearEquiv.toLinearMap

theorem transLinear_apply (li : ES m →ₗᵢ[ℝ] ES m) (x : Fin m → ℝ) :
    transLinear li x = eucEquiv (li (eucEquiv.symm x)) := rfl

theorem transLinear_dotB (li : ES m →ₗᵢ[ℝ] ES m) (x y : Fin m → ℝ) :
    dotB (transLinear li x) (transLinear li y) = dotB x y := by
  have happ : ∀ w : Fin m → ℝ, eucEquiv.symm (transLinear li w) = li (eucEquiv.symm w) := by
    intro w
    change eucEquiv.symm (eucEquiv (li (eucEquiv.symm w))) = _
    rw [eucEquiv.symm_apply_apply]
  rw [← dotB_eq_inner, happ, happ, li.inner_map_map, dotB_eq_inner]

theorem dotB_single_single (i j : Fin m) :
    dotB (Pi.single i (1:ℝ)) (Pi.single j 1) = if i = j then 1 else 0 := by
  unfold dotB
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]; norm_num
    · intro k _ hk; rw [Pi.single_eq_of_ne hk]; norm_num
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst hki
      rw [Pi.single_eq_same, Pi.single_eq_of_ne h]; norm_num
    · rw [Pi.single_eq_of_ne hki]; norm_num

noncomputable def conformalMatrix (li : ES m →ₗᵢ[ℝ] ES m) : Matrix (Fin m) (Fin m) ℝ :=
  LinearMap.toMatrix' (transLinear li)

theorem conformalMatrix_orthogonal (li : ES m →ₗᵢ[ℝ] ES m) :
    (conformalMatrix li)ᵀ * (conformalMatrix li) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, conformalMatrix,
    LinearMap.toMatrix'_apply]
  rw [show (∑ k : Fin m, transLinear li (Pi.single i 1) k * transLinear li (Pi.single j 1) k)
      = dotB (transLinear li (Pi.single i 1)) (transLinear li (Pi.single j 1)) from rfl]
  rw [transLinear_dotB, dotB_single_single]

theorem transLinear_eq_mulVec (li : ES m →ₗᵢ[ℝ] ES m) (z : Fin m → ℝ) :
    transLinear li z = conformalMatrix li *ᵥ z := by
  rw [conformalMatrix, LinearMap.toMatrix'_mulVec]

theorem realizedByPo_similarity_of_isConformalMap {L : ES m →L[ℝ] ES m}
    (hL : IsConformalMap L) (t : ES m) :
    RealizedByPo (fun z : Fin m → ℝ => eucEquiv (L (eucEquiv.symm z) + t)) := by
  obtain ⟨c, hc0, li, hLeq⟩ := hL
  have hA : (conformalMatrix li)ᵀ * (conformalMatrix li) = 1 := conformalMatrix_orthogonal li
  have hpt : ∀ z : Fin m → ℝ,
      eucEquiv (L (eucEquiv.symm z) + t) = c • (conformalMatrix li *ᵥ z) + eucEquiv t := by
    intro z
    have hLz : L (eucEquiv.symm z) = c • li (eucEquiv.symm z) := by
      rw [hLeq]
      change c • li.toContinuousLinearMap (eucEquiv.symm z) = c • li (eucEquiv.symm z)
      rw [li.coe_toContinuousLinearMap]
    rw [hLz, map_add, map_smul, ← transLinear_apply, transLinear_eq_mulVec]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hAneg : ((-conformalMatrix li)ᵀ) * (-conformalMatrix li) = 1 := by
      rw [Matrix.transpose_neg, neg_mul_neg]; exact hA
    refine RealizedByPo.congr (fun z => ?_)
      (realizedByPo_similarity hAneg (-c) (by linarith) (eucEquiv t))
    rw [hpt, Matrix.neg_mulVec]
    rw [show (-c) • (-(conformalMatrix li *ᵥ z)) = c • (conformalMatrix li *ᵥ z) from by
      rw [smul_neg, neg_smul, neg_neg]]
  · refine RealizedByPo.congr (fun z => ?_)
      (realizedByPo_similarity hA c hpos (eucEquiv t))
    rw [hpt]

theorem norm_sq_eq_normSq (u : ES m) : ‖u‖^2 = normSq (eucEquiv u) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  unfold normSq
  apply Finset.sum_congr rfl
  intro i _
  rw [eucEquiv_apply_coord, Real.norm_eq_abs, sq_abs]

theorem eucEquiv_inversion (x₀ : ES m) (z : Fin m → ℝ) :
    eucEquiv (DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm z))
      = inversionAbout (eucEquiv x₀) z := by
  have hw : eucEquiv (eucEquiv.symm z) = z := eucEquiv.apply_symm_apply z
  have hnorm : ‖eucEquiv.symm z - x₀‖^2 = normSq (z - eucEquiv x₀) := by
    rw [norm_sq_eq_normSq, map_sub, hw]
  unfold DifferentialGeometry.LiouvilleMobius.inversion inversionAbout
  rw [map_add, map_smul, map_sub, hw, hnorm, add_comm]

theorem eucEquiv_symm_inversionAbout (x₀ : ES m) (z : Fin m → ℝ) :
    eucEquiv.symm (inversionAbout (eucEquiv x₀) z)
      = DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm z) := by
  have h := eucEquiv_inversion x₀ z
  rw [← h, eucEquiv.symm_apply_apply]

theorem realizedByPo_conformal_inversion {L : ES m →L[ℝ] ES m}
    (hL : IsConformalMap L) (t x₀ : ES m) (z : Fin m → ℝ) (hz : z ≠ eucEquiv x₀) :
    ∃ g : PO (m+1) 1, (poBoundaryMulAction (Nat.le_add_left 1 m)).smul g (horo z)
      = horo (eucEquiv (L (DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm z)) + t)) := by
  obtain ⟨c, hc0, li, hLeq⟩ := hL
  have hA : (conformalMatrix li)ᵀ * (conformalMatrix li) = 1 := conformalMatrix_orthogonal li
  have hpt : ∀ zz : Fin m → ℝ,
      eucEquiv (L (DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm zz)) + t)
        = c • (conformalMatrix li *ᵥ inversionAbout (eucEquiv x₀) zz) + eucEquiv t := by
    intro zz
    have hLz : L (DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm zz))
        = c • li (DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm zz)) := by
      rw [hLeq]
      change c • li.toContinuousLinearMap _ = c • li _
      rw [li.coe_toContinuousLinearMap]
    rw [hLz, map_add, map_smul]
    have hinv : eucEquiv (li (DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm zz)))
        = conformalMatrix li *ᵥ inversionAbout (eucEquiv x₀) zz := by
      have h1 : eucEquiv (li (DifferentialGeometry.LiouvilleMobius.inversion x₀ (eucEquiv.symm zz)))
          = transLinear li (inversionAbout (eucEquiv x₀) zz) := by
        rw [transLinear_apply, eucEquiv_symm_inversionAbout]
      rw [h1, transLinear_eq_mulVec]
    rw [hinv]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hAneg : ((-conformalMatrix li)ᵀ) * (-conformalMatrix li) = 1 := by
      rw [Matrix.transpose_neg, neg_mul_neg]; exact hA
    have hmain := realizedByPo_similarity_comp_inversion hAneg (-c) (by linarith)
      (eucEquiv t) (eucEquiv x₀) z hz
    have hrewrite : (-c) • ((-conformalMatrix li) *ᵥ inversionAbout (eucEquiv x₀) z) + eucEquiv t
        = c • (conformalMatrix li *ᵥ inversionAbout (eucEquiv x₀) z) + eucEquiv t := by
      rw [Matrix.neg_mulVec, smul_neg, neg_smul, neg_neg]
    exact ⟨_, hmain.trans (congrArg horo (hrewrite.trans (hpt z).symm))⟩
  · have hmain := realizedByPo_similarity_comp_inversion hA c hpos (eucEquiv t)
      (eucEquiv x₀) z hz
    exact ⟨_, hmain.trans (congrArg horo (hpt z).symm)⟩

theorem eq_po_smul_of_continuous_on_horo {F : (Fin m → ℝ) → (Fin m → ℝ)}
    (hF : RealizedByPo F) {φ : BoundaryH (m + 1) → BoundaryH (m + 1)}
    (hφ : Continuous φ) (hm : 1 ≤ m)
    (h : ∀ x : Fin m → ℝ, φ (horo x) = horo (F x)) :
    ∃ g : PO (m+1) 1, ∀ v : BoundaryH (m+1),
      φ v = (poBoundaryMulAction (Nat.le_add_left 1 m)).smul g v := by
  obtain ⟨g, hgF⟩ := hF
  obtain ⟨ψ, hψ⟩ :=
    DifferentialGeometry.BoundaryTopology.po_boundary_homeomorph (Nat.le_add_left 1 m) g
  refine ⟨g, fun v => ?_⟩
  have hagree : ∀ x : Fin m → ℝ, φ (horo x) = ψ (horo x) := fun x =>
    calc φ (horo x) = horo (F x) := h x
      _ = (poBoundaryMulAction (Nat.le_add_left 1 m)).smul g (horo x) := (hgF x).symm
      _ = ψ (horo x) := (hψ (horo x)).symm
  have hAll : ∀ v : BoundaryH (m+1), φ v = ψ v :=
    DifferentialGeometry.MobiusBoundary.eq_on_boundary_of_eq_on_horo hφ ψ.continuous hm hagree
  rw [hAll v, hψ v]

noncomputable def boundaryHCongr {a b : ℕ} (h : a = b) : BoundaryH a ≃ₜ BoundaryH b := by
  subst h
  exact Homeomorph.refl _

noncomputable def poCongr {a b : ℕ} (h : a = b) : PO a 1 ≃* PO b 1 := by
  subst h
  exact MulEquiv.refl _

theorem boundaryHCongr_smul {a b : ℕ} (h : a = b) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (g : PO a 1) (v : BoundaryH a) :
    boundaryHCongr h ((poBoundaryMulAction ha).smul g v)
      = (poBoundaryMulAction hb).smul (poCongr h g) (boundaryHCongr h v) := by
  subst h
  rfl

theorem isSimilarity_global_of_contDiff_conformal {F : ES m → ES m} (hm : 3 ≤ m)
    (hF : ContDiff ℝ 3 F) (hconf : ∀ x, IsConformalMap (fderiv ℝ F x)) :
    ∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m, ∀ z, F z = L z + t := by
  have hconfU : ∀ x ∈ (Set.univ : Set (ES m)), IsConformalMap (fderiv ℝ F x) :=
    fun x _ => hconf x
  obtain hs | hi := LiouvilleMobius.mobius_classification_on_domain hm hF
    isOpen_univ hconfU isPreconnected_univ (Set.mem_univ (0 : ES m))
  · obtain ⟨L, hL, t, ht⟩ := hs
    exact ⟨L, hL, t, fun z => ht z (Set.mem_univ z)⟩
  · obtain ⟨L, hL, t, x₀, hFx⟩ := hi
    obtain ⟨c, hc0, li, hLeq⟩ := hL
    have hcabs : (0 : ℝ) < |c| := abs_pos.mpr hc0
    have hnormL : ∀ w : ES m, ‖L w‖ = |c| * ‖w‖ := by
      intro w
      have hw : L w = c • li w := by
        rw [hLeq]
        rfl
      rw [hw, norm_smul, li.norm_map, Real.norm_eq_abs]
    have hbdd : ∀ᶠ z in 𝓝 x₀, ‖F z‖ ≤ ‖F x₀‖ + 1 := by
      have hcn : ContinuousAt (fun z => ‖F z‖) x₀ :=
        (continuous_norm.comp hF.continuous).continuousAt
      have hmem : Set.Iio (‖F x₀‖ + 1) ∈ 𝓝 ‖F x₀‖ := Iio_mem_nhds (by linarith)
      filter_upwards [hcn hmem] with z hz using le_of_lt hz
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hbdd
    have hm1 : 1 ≤ m := by omega
    set e : ES m := stdBasis m ⟨0, hm1⟩ with he_def
    have he : ‖e‖ = 1 := (stdBasis m).orthonormal.1 _
    set M : ℝ := ‖F x₀‖ + 1 + ‖t‖ + |c| * ‖x₀‖ with hM_def
    have hM : (0 : ℝ) < M := by positivity
    set K : ℝ := |c| / (2 * (M + 1)) with hK_def
    have hK : (0 : ℝ) < K := by positivity
    set s : ℝ := min (ε / 2) K with hs_def
    have hs_pos : (0 : ℝ) < s := lt_min (by linarith) hK
    have hs_lt_ε : s < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsK : s ≤ K := min_le_right _ _
    have hK2 : (2 * (M + 1)) * K = |c| := by
      have hne : (2 * (M + 1)) ≠ 0 := ne_of_gt (by positivity)
      rw [hK_def]; field_simp
    have hcs' : (2 * (M + 1)) * s ≤ |c| := by
      calc (2 * (M + 1)) * s ≤ (2 * (M + 1)) * K :=
            mul_le_mul_of_nonneg_left hsK (by positivity)
        _ = |c| := hK2
    have hcs : 2 * (M + 1) ≤ |c| * s⁻¹ := by
      have hs0 : s ≠ 0 := ne_of_gt hs_pos
      calc 2 * (M + 1) = (2 * (M + 1)) * s * s⁻¹ := by field_simp
        _ ≤ |c| * s⁻¹ :=
            mul_le_mul_of_nonneg_right hcs' (by positivity)
    have he_ne : e ≠ 0 := by
      intro h0; rw [h0, norm_zero] at he; norm_num at he
    set z : ES m := x₀ + s • e with hz_def
    have hz_sub : z - x₀ = s • e := by rw [hz_def, add_sub_cancel_left]
    have hz_ne : z ≠ x₀ := by
      intro hzz
      have h1 : s • e = 0 := by
        have h2 := congrArg (· - x₀) hzz
        rw [hz_def, add_sub_cancel_left, sub_self] at h2
        exact h2
      exact smul_ne_zero (ne_of_gt hs_pos) he_ne h1
    have hnorm_z : ‖z - x₀‖ = s := by
      rw [hz_sub, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hs_pos]
    have hdist : dist z x₀ = s := by rw [dist_eq_norm, hnorm_z]
    have hzF : F z = L (LiouvilleMobius.inversion x₀ z) + t := hFx z (Set.mem_univ z)
    have hnorm_inv : ‖LiouvilleMobius.inversion x₀ z - x₀‖ = s⁻¹ := by
      rw [LiouvilleMobius.norm_inversion_sub_center hz_ne, hnorm_z]
    have hnorm_Fz : |c| * s⁻¹ - |c| * ‖x₀‖ - ‖t‖ ≤ ‖F z‖ := by
      rw [hzF]
      have h1 : ‖L (LiouvilleMobius.inversion x₀ z)‖ - ‖t‖
          ≤ ‖L (LiouvilleMobius.inversion x₀ z) + t‖ := by
        have h := norm_sub_le (L (LiouvilleMobius.inversion x₀ z) + t) t
        rw [add_sub_cancel_right] at h
        linarith
      have h2 : ‖LiouvilleMobius.inversion x₀ z‖ ≥ s⁻¹ - ‖x₀‖ := by
        have h := norm_sub_le (LiouvilleMobius.inversion x₀ z) x₀
        rw [hnorm_inv] at h
        linarith
      rw [hnormL] at h1
      have h3 : |c| * (s⁻¹ - ‖x₀‖) ≤ |c| * ‖LiouvilleMobius.inversion x₀ z‖ :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hcabs)
      linarith
    have hball_z : ‖F z‖ ≤ ‖F x₀‖ + 1 := hball (by rw [hdist]; exact hs_lt_ε)
    have hnn1 : (0:ℝ) ≤ ‖F x₀‖ := norm_nonneg _
    have hnn2 : (0:ℝ) ≤ ‖t‖ := norm_nonneg _
    have hnn3 : (0:ℝ) ≤ |c| * ‖x₀‖ := by positivity
    linarith

theorem mobius_boundary_of_contDiff_conformal {m : ℕ} (hm : 3 ≤ m)
    (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (F : ES m → ES m) (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x, IsConformalMap (fderiv ℝ F x))
    (hφF : ∀ x : Fin m → ℝ, φ (horo x) = horo (eucEquiv (F (eucEquiv.symm x)))) :
    ∃ g : PO (m+1) 1, ∀ v : BoundaryH (m+1),
      φ v = (poBoundaryMulAction (Nat.le_add_left 1 m)).smul g v := by
  obtain ⟨L, hL, t, ht⟩ := isSimilarity_global_of_contDiff_conformal hm hF hconf
  have hG : ∀ z : Fin m → ℝ,
      eucEquiv (F (eucEquiv.symm z)) = eucEquiv (L (eucEquiv.symm z) + t) :=
    fun z => congrArg eucEquiv (ht (eucEquiv.symm z))
  have hRF : RealizedByPo (fun z : Fin m → ℝ => eucEquiv (L (eucEquiv.symm z) + t)) :=
    realizedByPo_similarity_of_isConformalMap hL t
  have hφG : ∀ x : Fin m → ℝ,
      φ (horo x)
        = horo ((fun z : Fin m → ℝ => eucEquiv (L (eucEquiv.symm z) + t)) x) := by
    intro x
    rw [hφF x, hG x]
  exact eq_po_smul_of_continuous_on_horo hRF φ.continuous (by omega) hφG

theorem mobius_boundary_of_smoothConformal_dim {n : ℕ} (hn : 4 ≤ n)
    (φ : BoundaryH n ≃ₜ BoundaryH n)
    (F : ES (n - 1) → ES (n - 1)) (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x, IsConformalMap (fderiv ℝ F x))
    (hφF : ∀ x : Fin (n-1) → ℝ,
      φ ((boundaryHCongr (by omega : (n-1)+1 = n)) (horo x))
        = (boundaryHCongr (by omega : (n-1)+1 = n))
            (horo (eucEquiv (F (eucEquiv.symm x))))) :
    ∃ g : PO n 1, ∀ v : BoundaryH n,
      φ v = (poBoundaryMulAction (by omega : 1 ≤ n)).smul g v := by
  set hnm : (n - 1) + 1 = n := by omega
  set e := boundaryHCongr hnm with he_def
  set φ' : BoundaryH ((n-1)+1) ≃ₜ BoundaryH ((n-1)+1) := e.trans (φ.trans e.symm)
    with hφ'_def
  have hφF' : ∀ x : Fin (n-1) → ℝ,
      φ' (horo x) = horo (eucEquiv (F (eucEquiv.symm x))) := by
    intro x
    have h1 : φ' (horo x) = e.symm (φ (e (horo x))) := rfl
    rw [h1, hφF x, Homeomorph.symm_apply_apply]
  obtain ⟨g', hg'⟩ :=
    mobius_boundary_of_contDiff_conformal (m := n - 1) (by omega) φ' F hF hconf hφF'
  refine ⟨poCongr hnm g', fun v => ?_⟩
  have h2 : φ v = e (φ' (e.symm v)) := by
    have hdef : φ' (e.symm v) = e.symm (φ v) := by
      have h1 : φ' (e.symm v) = e.symm (φ (e (e.symm v))) := rfl
      rw [h1, Homeomorph.apply_symm_apply]
    rw [hdef, Homeomorph.apply_symm_apply]
  have h3 : φ v
      = e ((poBoundaryMulAction (Nat.le_add_left 1 (n-1))).smul g' (e.symm v)) := by
    rw [h2, hg' (e.symm v)]
  rw [h3,
    boundaryHCongr_smul hnm (Nat.le_add_left 1 (n-1)) (by omega : 1 ≤ n) g' (e.symm v),
    Homeomorph.apply_symm_apply]

end DifferentialGeometry.LiouvilleBoundary
