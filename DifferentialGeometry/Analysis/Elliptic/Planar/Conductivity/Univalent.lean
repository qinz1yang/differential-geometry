import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.LevelSet
import DifferentialGeometry.Topology.LevelSet.Disk.CoordinateRange
import DifferentialGeometry.Topology.LevelSet.Disk.Regular
import DifferentialGeometry.Topology.LocalHomeomorph.Real

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Topology

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem IsSolution.injOn_pair_of_coordinate_boundary_stream
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0)
    (hstream : ∀ x ∈ Metric.ball (0 : V) R,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    InjOn (fun x => (v x, s x)) (Metric.ball (0 : V) R) := by
  have hv := hu.contDiffOn_of_continuousOn_ae_eq Metric.isOpen_ball B hAB
    (hc.mono Metric.ball_subset_closedBall) huv
  have hn := hu.fderiv_ne_zero_of_coordinate_boundary hR B hAB hdet hc huv hbd
  have hrange := mapsTo_Ioo_of_noncritical_coordinate_boundary hc 0 hbd hn
  intro x hx y hy hxy
  have hvxy : v x = v y := congrArg Prod.fst hxy
  have hsxy : s x = s y := congrArg Prod.snd hxy
  let L := {z : V // z ∈ Metric.ball (0 : V) R ∧ v z = v x}
  have hconn := isConnected_level_of_noncritical_disk_coordinate hR hc hbd
    (hv.of_le (by norm_cast)) hn (hrange hx)
  let : PreconnectedSpace L := isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  have hlocal : IsLocalHomeomorph (fun z : L => s z) :=
    hu.isLocalHomeomorph_stream_on_level hR B hAB hdet hc huv hbd hstream (v x)
  have heq : (⟨x, hx, rfl⟩ : L) = ⟨y, hy, hvxy.symm⟩ :=
    hlocal.injective_of_preconnected_real hsxy
  exact congrArg Subtype.val heq

theorem IsSolution.injOn_complex_stream_of_coordinate_boundary
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0)
    (hstream : ∀ x ∈ Metric.ball (0 : V) R,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    InjOn (fun z => (v (Complex.orthonormalBasisOneI.repr z) : ℂ) +
      (s (Complex.orthonormalBasisOneI.repr z) : ℂ) * Complex.I) (Metric.ball (0 : ℂ) R) := by
  have hinj := hu.injOn_pair_of_coordinate_boundary_stream hR B hAB hdet hc huv hbd hstream
  intro z hz w hw hzw
  apply Complex.orthonormalBasisOneI.repr.injective
  apply hinj (by simpa using hz) (by simpa using hw)
  apply Prod.ext
  · have hh := congrArg Complex.re hzw
    simpa using hh
  · have hh := congrArg Complex.im hzw
    simpa using hh


theorem IsSolution.injOn_complex_stream_of_coordinate_trace
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (ht : MemH01 (fun x => u x - x 0) (Metric.ball (0 : V) R))
    (hv : ContinuousOn v (Metric.ball (0 : V) r))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) r)] v)
    (hs : ∀ x ∈ Metric.ball (0 : V) r,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    InjOn (fun z => (v (Complex.orthonormalBasisOneI.repr z) : ℂ) +
      (s (Complex.orthonormalBasisOneI.repr z) : ℂ) * Complex.I) (Metric.ball (0 : ℂ) r) := by
  obtain ⟨v₁, s₁, _, _, hc, huv₁, hveq, hseq, hbd, hds⟩ :=
    hu.exists_dirichlet_stream_boundary_extension hr hrR B hAB 0 ht hv huv hs
  have hinj := hu.injOn_complex_stream_of_coordinate_boundary (hr.trans_le hrR) B hAB hdet
    hc huv₁ hbd hds
  intro x hx y hy hxy
  have hxV : Complex.orthonormalBasisOneI.repr x ∈ Metric.ball (0 : V) r := by simpa using hx
  have hyV : Complex.orthonormalBasisOneI.repr y ∈ Metric.ball (0 : V) r := by simpa using hy
  apply hinj (Metric.ball_subset_ball hrR hx) (Metric.ball_subset_ball hrR hy)
  change (v₁ (Complex.orthonormalBasisOneI.repr x) : ℂ) +
    (s₁ (Complex.orthonormalBasisOneI.repr x) : ℂ) * Complex.I =
      (v₁ (Complex.orthonormalBasisOneI.repr y) : ℂ) +
        (s₁ (Complex.orthonormalBasisOneI.repr y) : ℂ) * Complex.I
  rw [hveq hxV, hseq hxV, hveq hyV, hseq hyV]
  exact hxy

end DeGiorgi

end

end
