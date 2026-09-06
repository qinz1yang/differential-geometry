import DifferentialGeometry.Geometry.Comparison.Volume.Radial.Gronwall
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Radial.Frame
import DifferentialGeometry.Geometry.Exponential.Smoothness.Framed
import DifferentialGeometry.Geometry.Exponential.Variation.Radial

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace VolumeComparison

open CovariantDerivativeAlong Exponential Variation Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem radialJacobiField_ne_zero_of_curvature_bound
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K R Vb : ℝ}
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hcoef : Real.sqrt (Module.finrank ℝ E) * R * Vb ^ 2 ≤ K)
    (hw : w ≠ 0)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    radialJacobiField (I := I) g p x w 1 ≠ 0 := by
  classical
  have hVb : 0 ≤ Vb :=
    (Real.sqrt_nonneg _).trans (hV (1 / 2) (by constructor <;> norm_num))
  have hR : 0 ≤ R :=
    (Real.sqrt_nonneg _).trans (hRm (1 / 2) (by constructor <;> norm_num))
  have hK : 0 ≤ K :=
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR) (sq_nonneg Vb)).trans hcoef
  have hcoef' : Real.sqrt ((Fintype.card
      (Fin 1 → Fin (Module.finrank ℝ E)) : ℝ)) * R * Vb ^ 2 ≤ K := by
    simpa only [Fintype.card_fun, Fintype.card_fin, pow_one] using hcoef
  have hdom (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := smul_mem_expDomain hx ht
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    let _ : Subsingleton E := Module.finrank_zero_iff.1 hzero
    exact hw (Subsingleton.elim w 0)
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t := by
    intro t ht
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s : ℝ => s • x) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    have hexp := contMDiffAt_expMap (I := I) g p (hdom t ht)
    exact (hexp.comp t hline).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  obtain ⟨F, hFdiff, hpar, hON⟩ :=
    exists_parallel_orthonormal_frame_expMap_smul (I := I) g p x zero_le_one
      (hdom 1 ⟨zero_le_one, le_rfl⟩)
  have hcard : ∀ t : ℝ, Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)) :=
    fun _ => (Fintype.card_fin _).trans rfl
  have hreg : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) t) t ∧
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun u => covDerivAlong (I := I) g
              (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) u) t) t := by
    intro t ht
    exact ⟨differentiableAt_chartRep_radialJacobiField (I := I) g p x w (hdom t ht),
      differentiableAt_chartRep_covDerivAlong_radialJacobiField
        (I := I) g p x w (hdom t ht)⟩
  have hJac : ∀ t ∈ Ioo (0 : ℝ) 1,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t := by
    intro t ht
    exact isJacobiAt_radialJacobiField (I := I) g p x w (hdom t ⟨ht.1.le, ht.2.le⟩)
  have hbasis : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
          (TangentSpace I (radialCurve (I := I) g p x t)),
        ∀ i j,
          g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
            if i = j then (1 : ℝ) else 0 := by
    intro t _ht
    exact DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
      (I := I) g (radialCurve (I := I) g p x t)
  choose basis hBasisON using hbasis
  have hcurv := by
    refine curv_sq_of_rm04_velocity_Ioo (I := I) g p x w hK hVb basis
      (fun t ht i j => hBasisON t ht i j) hV ?_
    intro t ht
    set C : ℝ :=
      Real.sqrt ((Fintype.card (Fin 1 → Fin (Module.finrank ℝ E)) : ℝ))
    have hC : 0 ≤ C := Real.sqrt_nonneg _
    have hV2 : 0 ≤ Vb ^ 2 := sq_nonneg Vb
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hRm t ht) hC) hV2).trans hcoef'
  have hD2 :
      covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g
          (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) 0 = 0 := by
    apply d2_zero_of_jacobian0 (I := I) g p x w
    exact isJacobiAt_radialJacobiField_zero (I := I) g p x w
  have hODE := ode_Ico_of_Ioo_d2 (I := I) g p x w hJac hcurv hD2
  have hDJ0 : covDerivAlong (I := I) g
      (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) 0 =
        (show TangentSpace I (radialCurve (I := I) g p x 0) from w) := by
    change (covDerivAlong (I := I) g
      (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) 0 : E) = w
    exact covDerivAlong_radialJacobiField_zero (I := I) g p x w
  have hs : 0 < Real.sqrt (g.inner p w w) :=
    Real.sqrt_pos.2 (g.pos p w hw)
  have hsmall' :
      gronwallBound 0 (max K 1)
          (K * ((1 : ℝ) * Real.sqrt (g.inner p w w))) 1 <
        (1 : ℝ) * Real.sqrt (g.inner p w w) := by
    have hscaled := mul_lt_mul_of_pos_left hsmall hs
    have herr :
        gronwallBound 0 (max K 1)
            (K * ((1 : ℝ) * Real.sqrt (g.inner p w w))) 1 =
          Real.sqrt (g.inner p w w) * gronwallBound 0 (max K 1) K 1 := by
      have heps : K * ((1 : ℝ) * Real.sqrt (g.inner p w w)) =
          Real.sqrt (g.inner p w w) * K := by ring
      rw [heps, gronwallBound_zero_mul_eps]
    rw [herr]
    simpa only [one_mul, mul_one] using hscaled
  have hγ0 : radialCurve (I := I) g p x 0 = p := by
    simp only [radialCurve, zero_smul]
    exact expMap_zero (I := I) g p
  apply covGronwall_ne_zero_at (I := I) g
    (radialCurve (I := I) g p x) hγ hcard F
    (radialJacobiField (I := I) g p x w) hK zero_lt_one
    hpar hON hFdiff (fun t ht => (hreg t ht).1)
    (fun t ht => (hreg t ht).2) hODE
    (radialJacobiField_zero (I := I) g p x w) hDJ0
  rw [hγ0]
  exact hsmall'

end VolumeComparison

namespace Exponential

open VolumeComparison Variation

theorem injective_mfderiv_expMap_of_curvature_bound
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K R Vb : ℝ}
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hcoef : Real.sqrt (Module.finrank ℝ E) * R * Vb ^ 2 ≤ K)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) I
        (fun u : E => expMap (I := I) g p
          (show TangentSpace I p from u)) x) := by
  rw [injective_iff_map_eq_zero]
  intro w hzero
  by_contra hw
  have hne := radialJacobiField_ne_zero_of_curvature_bound (I := I) g p x w hx
    hV hRm hcoef hw hsmall
  exact hne ((radialJacobiField_one (I := I) g p x w hx).trans hzero)

end Exponential

end Normed

namespace NormalCoordinates

open VolumeComparison Exponential Variation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem injective_mfderiv_framedExpMap_of_curvature_bound
    (g : SmoothRiemannianMetric I M) (p : M) (z : E)
    {K R Vb : ℝ}
    (hz : normalFrame (I := I) (E := E) g p z ∈ expDomain (I := I) g p)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)) ≤ Vb)
    (hRm : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t))) ≤ R)
    (hcoef : Real.sqrt (Module.finrank ℝ E) * R * Vb ^ 2 ≤ K)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) I (framedExpMap (I := I) (E := E) g p) z) := by
  have hinj := injective_mfderiv_expMap_of_curvature_bound (I := I) g p
    (normalFrame (I := I) (E := E) g p z) hz hV hRm hcoef hsmall
  rw [mfderiv_framedExpMap (I := I) g p hz]
  exact hinj.comp (normalFrame (I := I) (E := E) g p).injective

theorem isLocalDiffeomorphOn_framedExpMap_of_curvature_bound
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set E}
    (hU : IsOpen U) {K R Vb : ℝ}
    (hdom : ∀ z ∈ U, normalFrame (I := I) (E := E) g p z ∈ expDomain (I := I) g p)
    (hV : ∀ z ∈ U, ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)) ≤ Vb)
    (hRm : ∀ z ∈ U, ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t))) ≤ R)
    (hcoef : Real.sqrt (Module.finrank ℝ E) * R * Vb ^ 2 ≤ K)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap (I := I) (E := E) g p) U := by
  apply isLocalDiffeomorphOn_framedExpMap (I := I) g p hU hdom
  intro z hz
  exact injective_mfderiv_framedExpMap_of_curvature_bound (I := I) g p z (hdom z hz)
    (hV z hz) (hRm z hz) hcoef hsmall

end NormalCoordinates

end DifferentialGeometry.Geometry.Riemannian
