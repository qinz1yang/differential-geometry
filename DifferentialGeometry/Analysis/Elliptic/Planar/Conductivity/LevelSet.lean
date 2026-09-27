import DifferentialGeometry.Topology.LocalHomeomorph.Fiber
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.Noncritical

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem isLocalHomeomorphOn_pair_of_conductivity_stream
    {Ω : Set V} (hΩ : IsOpen Ω) {A : V → Matrix (Fin 2) (Fin 2) ℝ} {v s : V → ℝ}
    (hv : ContDiffOn ℝ 1 v Ω) (hs : ContDiffOn ℝ 1 s Ω)
    (hpos : ∀ x ∈ Ω, (A x).PosDef)
    (hstream : ∀ x ∈ Ω, HasFDerivAt s
      (planarFluxForm (fun y => DeGiorgi.matMulE (A y) (DeGiorgi.smoothGradField v y)) x) x)
    (hn : ∀ x ∈ Ω, fderiv ℝ v x ≠ 0) :
    IsLocalHomeomorphOn (fun x => (v x, s x)) Ω := by
  intro x hx
  let L := Complex.orthonormalBasisOneI.repr
  let z := L.symm x
  have hLz : L z = x := L.apply_symm_apply x
  have hzx : Complex.orthonormalBasisOneI.repr z ∈ Ω := by change L z ∈ Ω; rwa [hLz]
  obtain ⟨e, hez, _, _, _, heq⟩ := exists_localInverse_of_conductivity_stream one_ne_zero hΩ
    hv hs hzx (hpos _ hzx) (hstream _ hzx)
    (fun hg => hn _ hzx (DeGiorgi.smoothGradField_eq_zero_iff.mp hg))
  let F := L.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (e.trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph)
  have hxF : x ∈ F.source := ⟨mem_univ _, hez, mem_univ _⟩
  refine ⟨F, hxF, ?_⟩
  funext y
  change (v y, s y) = Complex.equivRealProdCLM (e (L.symm y))
  rw [heq]
  change (v y, s y) = Complex.equivRealProdCLM
    ((v (L (L.symm y)) : ℂ) + (s (L (L.symm y)) : ℂ) * Complex.I)
  rw [L.apply_symm_apply]
  apply Prod.ext <;> simp

end DifferentialGeometry.Analysis

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)


section General

variable {d : ℕ} [NeZero d]
local notation "Vd" => EuclideanSpace ℝ (Fin d)

theorem IsSolution.contDiffOn_of_continuousOn_ae_eq
    {Ω : Set Vd} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {u v : Vd → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm d (univ : Set Vd))
    (hAB : EqOn A.a B.a Ω) (hv : ContinuousOn v Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    ContDiffOn ℝ ∞ v Ω := by
  obtain ⟨w, hw, huw⟩ := hu.exists_contDiffOn_ae_eq hΩ B hAB
  exact hw.congr (Measure.eqOn_open_of_ae_eq (huv.symm.trans huw) hΩ hv hw.continuousOn)

end General

private theorem smooth_stream_of_continuous_representative
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff 2 Ω} {u v s : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a Ω) (hv : ContinuousOn v Ω) (huv : u =ᵐ[volume.restrict Ω] v)
    (hstream : ∀ x ∈ Ω, HasFDerivAt s (planarFluxForm
      (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) : ContDiffOn ℝ ∞ s Ω := by
  have hvs := hu.contDiffOn_of_continuousOn_ae_eq hΩ B hAB hv huv
  have hflux := contDiffOn_matMulE_smoothGradField (n := ∞) hΩ
    (fun i j => (B.smooth_a i j).contDiffOn.congr
      (fun x hx => congrFun (congrFun (hAB hx) i) j))
    (by simpa only [ENat.coe_top_add_one] using hvs)
  have hω : ContDiffOn ℝ ∞ (planarFluxForm
      (fun y => matMulE (A.a y) (smoothGradField v y))) Ω :=
    (((contDiff_piLp_apply (p := 2) (i := (1 : Fin 2))).comp_contDiffOn hflux).neg.smul_const
      (EuclideanSpace.proj 0 : V →L[ℝ] ℝ)).add
      (((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).comp_contDiffOn hflux).smul_const
        (EuclideanSpace.proj 1 : V →L[ℝ] ℝ))
  apply (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mpr
  exact ⟨fun x hx => (hstream x hx).differentiableAt.differentiableWithinAt,
    hω.congr (fun x hx => (hstream x hx).fderiv)⟩

theorem IsSolution.isLocalHomeomorph_stream_on_level
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0)
    (hstream : ∀ x ∈ Metric.ball (0 : V) R,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x)
    (c : ℝ) :
    IsLocalHomeomorph (fun x : {x : V // x ∈ Metric.ball (0 : V) R ∧ v x = c} => s x) := by
  have hv := hu.contDiffOn_of_continuousOn_ae_eq Metric.isOpen_ball B hAB
    (hc.mono Metric.ball_subset_closedBall) huv
  have hs := smooth_stream_of_continuous_representative Metric.isOpen_ball hu B hAB
    (hc.mono Metric.ball_subset_closedBall) huv hstream
  apply IsLocalHomeomorphOn.snd_fiber Metric.isOpen_ball
    (isLocalHomeomorphOn_pair_of_conductivity_stream Metric.isOpen_ball
      (hv.of_le (by norm_cast)) (hs.of_le (by norm_cast)) ?_ hstream
      (hu.fderiv_ne_zero_of_coordinate_boundary hR B hAB hdet hc huv hbd)) c
  intro x hx
  rw [hAB hx]
  exact B.posDef (mem_univ x)

end DeGiorgi

end

end
