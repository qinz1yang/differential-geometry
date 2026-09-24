import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.JointMetricExtensionRegularity
import DifferentialGeometry.Analysis.Calculus.Inverse.MatrixSmoothness
import DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import DifferentialGeometry.Analysis.Matrix.PositiveRankOneField


noncomputable section

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem contDiffAt_gSeqExt_chartDensity_mul_chartInvGram
    (Φ : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : ℕ) (a : P.M) (q : ℝ × E) (hqt : q.1 ∈ X.D.regular)
    (hqtarget : q.2 ∈ (extChartAt I a).target)
    (hqgrow : (extChartAt I a).symm q.2 ∈ bf.grow k) :
    ContDiffAt ℝ ∞
      (fun z : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
        chartDensityOnE (gSeqExt Φ R bf hsrc htgt k z.1) a z.2 *
          chartInvGramOnE (gSeqExt Φ R bf hsrc htgt k z.1) a i j z.2) q := by
  let G : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun z i j => chartGramOnE (gSeqExt Φ R bf hsrc htgt k z.1) a i j z.2
  have hG : ContDiffAt ℝ ∞ G q := by
    apply contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
    exact contDiffAt_gSeqExt_chartGramOnE_of_solution Φ k
      (sourceFlow Φ k (hsrc k) (htgt k))
      (isSolutionOn_sourceFlow Φ k (hsrc k) (htgt k))
      (fun _ _ _ _ => rfl) a i j q hqt hqtarget hqgrow
  have hdet : (G q).det ≠ 0 :=
    (chartGramMatrix_det_pos (gSeqExt Φ R bf hsrc htgt k q.1) a
      (extChartAt_symm_mem_trivializationAt_baseSet a hqtarget)).ne'
  apply contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
  have hQ : ContDiffAt ℝ ∞
      (fun A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
        Real.sqrt A.det * A⁻¹ i j) (G q) :=
    ((Matrix.contDiff_det (𝕜 := ℝ) (n := ∞)).contDiffAt.sqrt hdet).mul
      (DifferentialGeometry.Analysis.contDiffAt_inv_of_entries id
        (fun k l => contDiff_pi.mp (contDiff_pi.mp contDiff_id k) l) hdet i j)
  exact hQ.comp q hG

theorem exists_contDiffOn_gSeqExt_positive_rank_one_decomposition_one_sub
    (Φ : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : ℕ) (a : P.M) (q : ℝ × E) (hqt : 1 - q.1 ∈ X.D.regular)
    (hqtarget : q.2 ∈ (extChartAt I a).target)
    (hqgrow : (extChartAt I a).symm q.2 ∈ bf.grow k) (r : ℕ) :
    ∃ (N : ℕ) (v : Fin N → E) (w : Fin N → ℝ × E → ℝ) (U : Set (ℝ × E)),
      IsOpen U ∧ q ∈ U ∧
      U ⊆ {z | 1 - z.1 ∈ X.D.regular ∧ z.2 ∈ (extChartAt I a).target} ∧
      (∀ l, ContDiffOn ℝ r (w l) U) ∧
      (∀ z ∈ U, ∀ l, 0 < w l z) ∧
      ∀ z ∈ U, ∀ i j : Fin (Module.finrank ℝ E),
        chartDensityOnE (gSeqExt Φ R bf hsrc htgt k (1 - z.1)) a z.2 *
          chartInvGramOnE (gSeqExt Φ R bf hsrc htgt k (1 - z.1)) a i j z.2 =
          ∑ l, w l z * (chartModelBasis E).repr (v l) i *
            (chartModelBasis E).repr (v l) j := by
  classical
  let C : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun z i j => chartDensityOnE (gSeqExt Φ R bf hsrc htgt k (1 - z.1)) a z.2 *
      chartInvGramOnE (gSeqExt Φ R bf hsrc htgt k (1 - z.1)) a i j z.2
  have hC : ContDiffAt ℝ ∞ C q :=
    (contDiffAt_gSeqExt_chartDensity_mul_chartInvGram Φ R bf hsrc htgt k a
      (1 - q.1, q.2) hqt hqtarget hqgrow).comp q
      ((contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd)
  have hpos (z : ℝ × E) (hz : z.2 ∈ (extChartAt I a).target) : (C z).PosDef := by
    exact (chartInvGramOnE_posDef (gSeqExt Φ R bf hsrc htgt k (1 - z.1)) a hz).smul
      (chartDensity_pos (gSeqExt Φ R bf hsrc htgt k (1 - z.1)) a
        (extChartAt_symm_mem_trivializationAt_baseSet a hz))
  have hsymm : ∀ᶠ z in 𝓝 q, (C z).IsSymm := by
    filter_upwards [(continuous_snd.tendsto q).eventually
      ((isOpen_extChartAt_target a).mem_nhds hqtarget)] with z hz
    exact Matrix.isHermitian_iff_isSymm.mp (hpos z hz).isHermitian
  obtain ⟨N, v, w, U, hU, hqU, hw, hwp, hrep⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_positive_rank_one_decomposition (n := r)
      (hC.of_le (by exact_mod_cast le_top)) hsymm (hpos q hqtarget)
  let V : Set (ℝ × E) :=
    {z | 1 - z.1 ∈ X.D.regular ∧ z.2 ∈ (extChartAt I a).target}
  have hV : IsOpen V :=
    (X.D.regular_isOpen.preimage (continuous_const.sub continuous_fst)).inter
      ((isOpen_extChartAt_target a).preimage continuous_snd)
  refine ⟨N, fun l => (chartModelBasis E).equivFun.symm (v l), w, U ∩ V,
    hU.inter hV, ⟨hqU, hqt, hqtarget⟩, inter_subset_right, ?_, ?_, ?_⟩
  · intro l
    exact (hw l).mono inter_subset_left
  · intro z hz l
    exact hwp z hz.1 l
  · intro z hz i j
    simpa only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hrep z hz.1 i j

end DifferentialGeometry.CheegerGromovCompactness
