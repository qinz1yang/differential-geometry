import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraph
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphStationarity
import DifferentialGeometry.Analysis.InnerProductSpace.NormalEquationMapDerivative
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphMapDerivative

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_fderiv_nearest_map_sub_starProjection_le
    (L : Submodule ℝ H) [CompleteSpace L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (W : Set H) (P : H → H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContDiffOn ℝ 2 g (ball 0 (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t))
    (hnearest : ∀ y ∈ ball o R, P y ∈ W ∧ IsMinOn (fun w => dist y w) W (P y))
    (z : H) (hz : z ∈ ball o R) (hP : DifferentiableAt ℝ P z) :
    ‖fderiv ℝ P z - L.starProjection‖ ≤ 7 * a := by
  let T : H → L := fun y => L.orthogonalProjectionOnto (P y-o)
  let u : H → L := fun y => L.orthogonalProjectionOnto (y-o)
  let v : H → Lᗮ := fun y => Lᗮ.orthogonalProjectionOnto (y-o)
  have hrepresentation (y : H) (hy : y ∈ ball o R) :
      T y ∈ ball (0 : L) (4*R) ∧ P y=o+orthogonalCoordinateSum L (T y,g (T y)) := by
    obtain ⟨_,_,t,ht,heq⟩ := minimizer_mem_buffered_normal_graph L o g W R a hR ha
      hvalue hgraph hsheet y (P y) hy (hnearest y hy).1 (hnearest y hy).2
    have htT : T y=t := by
      have hsub : P y-o=(t : H)+(g t : H) := by
        rw [heq]
        change (o+((t : H)+(g t : H)))-o=_
        abel
      change L.orthogonalProjectionOnto (P y-o)=t
      rw [hsub,map_add,L.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g t).property,add_zero]
    have ht4 : t ∈ ball (0 : L) (4*R) := by
      have hh : dist t 0 < 5*R/2 := ht
      change dist t 0 < 4*R
      linarith
    exact ⟨htT.symm ▸ ht4, by simpa only [htT] using heq⟩
  have hdg : ContDiffOn ℝ 1 (fderiv ℝ g) (ball (0 : L) (4*R)) :=
    hg.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdiff (t : L) (ht : t ∈ ball (0 : L) (4*R)) :
      DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (fderiv ℝ g) t := by
    exact ⟨(hg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by norm_num),
      (hdg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by norm_num)⟩
  have hstation (y : H) (hy : y ∈ ball o R) :
      T y-u y+(ContinuousLinearMap.adjoint (fderiv ℝ g (T y))) (g (T y)-v y)=0 := by
    have hsplit : o+orthogonalCoordinateSum L (u y,v y)=y := by
      change o+(L.starProjection (y-o)+Lᗮ.starProjection (y-o))=y
      rw [L.starProjection_add_starProjection_orthogonal]
      abel
    have hmin : IsMinOn (fun w => dist (o+orthogonalCoordinateSum L (u y,v y)) w)
        W (o+orthogonalCoordinateSum L (T y,g (T y))) := by
      rw [hsplit,← (hrepresentation y hy).2]
      exact (hnearest y hy).2
    exact normal_equation_of_isMinOn_normal_graph L o g (ball 0 (4*R)) W
      (u y) (T y) (v y) (isOpen_ball.mem_nhds (hrepresentation y hy).1)
      (hdiff _ (hrepresentation y hy).1).1 hgraph hmin
  have hT : DifferentiableAt ℝ T z :=
    L.orthogonalProjectionOnto.differentiableAt.comp z (hP.sub_const o)
  have ht := (hrepresentation z hz).1
  have hvnorm : ‖Lᗮ.orthogonalProjectionOnto (z-o)‖ ≤ R :=
    (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z-o)).trans
      (by simpa only [dist_eq_norm] using (show dist z o < R from hz).le)
  have hevent : ∀ᶠ y in 𝓝 z,
      T y-L.orthogonalProjectionOnto (y-o)+
        (ContinuousLinearMap.adjoint (fderiv ℝ g (T y)))
          (g (T y)-Lᗮ.orthogonalProjectionOnto (y-o))=0 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact hstation y hy
  have htan := norm_fderiv_tangent_map_sub_projection_le_of_normal_equation L o g T z R a
    hR ha hT (hdiff _ ht).1 (hdiff _ ht).2 (hvalue _ ht) (hfirst _ ht)
    (hsecond _ ht) hvnorm hevent
  have hPeq : P =ᶠ[𝓝 z] (fun y => o+orthogonalCoordinateSum L (T y,g (T y))) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact (hrepresentation y hy).2
  have hmap := norm_fderiv_normal_graph_map_sub_starProjection_le L o g T z (hdiff _ ht).1 hT
  rw [hPeq.fderiv_eq (𝕜 := ℝ)]
  apply hmap.trans
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hfirst _ ht)
  have hprod : ‖fderiv ℝ g (T z)‖*(1+‖fderiv ℝ T z-L.orthogonalProjectionOnto‖) ≤
      a*(1+5*a) := by
    exact mul_le_mul (hfirst _ ht) (add_le_add (le_refl (1 : ℝ)) htan)
      (by positivity) ha0
  have haa : a*a ≤ a/100 := by nlinarith [mul_le_mul_of_nonneg_left ha ha0]
  nlinarith

end DifferentialGeometry.Analysis
