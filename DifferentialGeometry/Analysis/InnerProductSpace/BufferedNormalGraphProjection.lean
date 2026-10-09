import DifferentialGeometry.Analysis.Calculus.Inverse.ContractionGraph
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraph
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphStationarity
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphRemainder

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis
section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_contDiffOn_unique_nearest_buffered_normal_graph
    (L : Submodule ℝ H) [FiniteDimensional ℝ L]
    (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContDiffOn ℝ (m + 1 : ℕ) g (ball 0 (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t)) :
    ∃ P : H → H, ContDiffOn ℝ m P (ball o R) ∧
      ∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun y => dist z y) W (P z) ∧
        ∀ y ∈ W, IsMinOn (fun w => dist z w) W y → y = P z := by
  classical
  let u : H → L := fun z => L.orthogonalProjectionOnto (z - o)
  let v : H → Lᗮ := fun z => Lᗮ.orthogonalProjectionOnto (z - o)
  let V : Set (H × L) := ball o (2 * R) ×ˢ ball 0 (2 * R)
  let q : H × L → L := fun p => u p.1 + p.2
  let e : H × L → L := fun p =>
    (ContinuousLinearMap.adjoint (fderiv ℝ g (q p))) (g (q p) - v p.1)
  let J : (L →L[ℝ] Lᗮ) →L[ℝ] (Lᗮ →L[ℝ] L) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hu : ContDiff ℝ m u :=
    L.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hv : ContDiff ℝ m v :=
    Lᗮ.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hq : ContDiff ℝ m q := (hu.comp contDiff_fst).add contDiff_snd
  have hmaps : MapsTo q V (ball (0 : L) (4 * R)) := by
    intro p hp
    have h1 : ‖u p.1‖ < 2 * R :=
      (L.norm_orthogonalProjectionOnto_apply_le (p.1 - o)).trans_lt
        (by simpa only [mem_ball, dist_eq_norm] using hp.1)
    have h2 : ‖p.2‖ < 2 * R := by simpa only [mem_ball, dist_zero_right] using hp.2
    rw [mem_ball, dist_zero_right]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hdg : ContDiffOn ℝ m (fderiv ℝ g) (ball (0 : L) (4 * R)) :=
    hg.fderiv_of_isOpen isOpen_ball (by simp)
  have hgm : ContDiffOn ℝ m g (ball (0 : L) (4 * R)) := hg.of_le (by simp)
  have he : ContDiffOn ℝ m e V :=
    (J.contDiff.comp_contDiffOn (hdg.comp hq.contDiffOn hmaps)).clm_apply
      ((hgm.comp hq.contDiffOn hmaps).sub (hv.comp contDiff_fst).contDiffOn)
  have hmn : (m : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiff (t : L) (ht : t ∈ ball (0 : L) (4 * R)) :
      DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (fderiv ℝ g) t := by
    exact ⟨(hgm.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt hmn,
      (hdg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt hmn⟩
  have hcylinder : ball o R ×ˢ closedBall (0 : L) R ⊆ V := by
    intro p hp
    constructor
    · change dist p.1 o < 2 * R
      have hh : dist p.1 o < R := hp.1
      linarith
    · change dist p.2 0 < 2 * R
      have hh : dist p.2 0 ≤ R := hp.2
      linarith
  have hscaled (z : H) (hz : z ∈ ball o R) (n : L)
      (hn : n ∈ closedBall (0 : L) R) :
      ‖e (z, n)‖ ≤ R / 4 ∧ ‖fderiv ℝ (fun w : L => e (z, w)) n‖ ≤ 1 / 2 := by
    have hp : (z, n) ∈ V := hcylinder ⟨hz, hn⟩
    have ht : q (z, n) ∈ ball (0 : L) (4 * R) := hmaps hp
    have hvnorm : ‖v z‖ ≤ R :=
      (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z - o)).trans
        (by simpa only [mem_ball, dist_eq_norm] using (show dist z o < R from hz).le)
    have hh := normal_graph_remainder_small_of_scaled_bounds g (u z + n) (v z) R a hR ha
      (hdiff _ ht).1 (hdiff _ ht).2 (hvalue _ ht) (hfirst _ ht) (hsecond _ ht) hvnorm
    refine ⟨hh.1, ?_⟩
    change ‖fderiv ℝ (fun w : L =>
      (ContinuousLinearMap.adjoint (fderiv ℝ g (u z + w))) (g (u z + w) - v z)) n‖ ≤ _
    rw [fderiv_comp_add_left (f := fun t : L =>
      (ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v z)) (u z)]
    exact hh.2
  obtain ⟨h, hh, hroot, hunique⟩ := exists_contDiffOn_contraction_graph hmn isOpen_ball
    (isOpen_ball.prod isOpen_ball) hR hcylinder he
    (fun z hz n hn => (hscaled z hz n hn).1)
    (fun z hz n hn => (hscaled z hz n hn).2)
  let T : H → L := fun z => u z + h z
  let P : H → H := fun z => o + orthogonalCoordinateSum L (T z, g (T z))
  have hT : ContDiffOn ℝ m T (ball o R) := hu.contDiffOn.add hh
  have hTmem (z : H) (hz : z ∈ ball o R) : T z ∈ ball (0 : L) (4 * R) := by
    have hunorm : ‖u z‖ < R :=
      (L.norm_orthogonalProjectionOnto_apply_le (z - o)).trans_lt
        (by simpa only [mem_ball, dist_eq_norm] using hz)
    have hhnorm := (hroot z hz).1
    rw [mem_ball, dist_zero_right]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hP : ContDiffOn ℝ m P (ball o R) :=
    contDiffOn_const.add ((orthogonalCoordinateSum L).contDiff.comp_contDiffOn
      (hT.prodMk (hgm.comp hT hTmem)))
  have huz (z : H) : o + orthogonalCoordinateSum L (u z, v z) = z := by
    change o + (L.starProjection (z - o) + Lᗮ.starProjection (z - o)) = z
    rw [L.starProjection_add_starProjection_orthogonal]
    abel
  have hidentify (z : H) (hz : z ∈ ball o R) (y : H) (hy : y ∈ W)
      (hmin : IsMinOn (fun w => dist z w) W y) : y = P z := by
    obtain ⟨_, _, t, ht, hyrep⟩ := minimizer_mem_buffered_normal_graph L o g W R a
      hR ha hvalue hgraph hsheet z y hz hy hmin
    have ht4 : t ∈ ball (0 : L) (4 * R) := by
      have ht' : dist t 0 < 5 * R / 2 := ht
      change dist t 0 < 4 * R
      linarith
    have hmgraph : IsMinOn (fun w => dist (o + orthogonalCoordinateSum L (u z, v z)) w)
        W (o + orthogonalCoordinateSum L (t, g t)) := by
      rw [huz, ← hyrep]
      exact hmin
    have hstation := normal_equation_of_isMinOn_normal_graph L o g
      (ball 0 (4 * R)) W (u z) t (v z) (isOpen_ball.mem_nhds ht4)
      (hdiff t ht4).1 hgraph hmgraph
    have hvnorm : ‖v z‖ ≤ R :=
      (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z - o)).trans
        (by simpa only [mem_ball, dist_eq_norm] using (show dist z o < R from hz).le)
    have hsmall := (normal_graph_remainder_small_of_scaled_bounds g t (v z) R a hR ha
      (hdiff t ht4).1 (hdiff t ht4).2 (hvalue t ht4) (hfirst t ht4) (hsecond t ht4) hvnorm).1
    have hnsmall : ‖t - u z‖ ≤ R / 4 := by
      have heq : t - u z = -(ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v z) :=
        eq_neg_of_add_eq_zero_left hstation
      rw [heq, norm_neg]
      exact hsmall
    have hnmem : t - u z ∈ closedBall (0 : L) R := by
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hcorrect : u z + (t - u z) = t := by abel
    have hzero : (t - u z) + e (z, t - u z) = 0 := by
      simpa only [e, q, hcorrect] using hstation
    have hn := (hunique z hz (t - u z) hnmem).mp hzero
    have htT : t = T z := by
      dsimp [T]
      rw [← hn]
      abel
    simpa only [P, htT] using hyrep
  refine ⟨P, hP, ?_⟩
  intro z hz
  obtain ⟨t, ht, hy, hmin⟩ := exists_nearest_on_buffered_normal_graph L o g W R a hR ha
    hg.continuousOn hvalue hgraph hsheet z hz
  have heq := hidentify z hz _ hy hmin
  refine ⟨?_, ?_, fun y hy hmin => hidentify z hz y hy hmin⟩
  · rwa [← heq]
  · rwa [← heq]

end
end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis
section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_smooth_unique_nearest_buffered_normal_graph
    (L : Submodule ℝ H) [FiniteDimensional ℝ L]
    (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContDiffOn ℝ ∞ g (ball 0 (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t)) :
    ∃ P : H → H, ContDiffOn ℝ ∞ P (ball o R) ∧
      ∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun y => dist z y) W (P z) ∧
        ∀ y ∈ W, IsMinOn (fun w => dist z w) W y → y = P z := by
  obtain ⟨P, _, hmin⟩ := exists_contDiffOn_unique_nearest_buffered_normal_graph
    L o g W R a 1 le_rfl hR ha (hg.of_le (by simp)) hvalue hfirst hsecond hgraph hsheet
  refine ⟨P, contDiffOn_infty.mpr ?_, hmin⟩
  intro m
  obtain ⟨Pm, hPm, hminm⟩ := exists_contDiffOn_unique_nearest_buffered_normal_graph
    L o g W R a (max m 1) (le_max_right _ _) hR ha (hg.of_le (by simp))
    hvalue hfirst hsecond hgraph hsheet
  have hm : ContDiffOn ℝ m Pm (ball o R) :=
    hPm.of_le (by exact_mod_cast Nat.le_max_left m 1)
  apply hm.congr
  intro z hz
  exact ((hmin z hz).2.2 (Pm z) (hminm z hz).1 (hminm z hz).2.1).symm

end
end DifferentialGeometry.Analysis
