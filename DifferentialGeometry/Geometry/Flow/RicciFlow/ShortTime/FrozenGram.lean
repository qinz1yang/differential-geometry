import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSPD
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoefficients

/-!
# Frozen inverse-Gram coordinate equivalences

At every active partition-of-unity chart point, the low-regularity coefficient
package supplies one uniformly positive inverse-Gram matrix.  This file turns
that concrete matrix into the positive-square-root coordinate equivalence used
by the Euclidean frozen heat operator, with constants depending only on the
two ellipticity numbers in `LowRegCoeff`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped ContDiff Manifold Topology BigOperators RealInnerProductSpace
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

private lemma frozenGram_quad
    (g : SmoothRiemannianMetric I M) (alpha b : M)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    ⟪x, Matrix.toEuclideanCLM
      (chartInvGramMatrix (I := I) g alpha b) x⟫_ℝ =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g alpha b i j * x i * x j := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The frozen inverse-Gram matrix at every active low-regularity chart point
is positive definite. -/
theorem frozenGram_posDef {index : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : index → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D)
    (alpha : M) (hAlpha : alpha ∈ chartAtlasPOU_finset (I := I) (M := M))
    (k : index) (b : M)
    (hb : b ∈ tsupport
      ((chartAtlasPOU I M alpha : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    (chartInvGramMatrix (I := I) (gSeq k) alpha b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · unfold chartInvGramMatrix
    exact (chartGramMatrix_isHermitian (I := I) (gSeq k) alpha b).inv
  · intro xi hxi
    have hEll := (hD.elliptic alpha hAlpha k b hb xi).1
    have hExists : ∃ i, xi i ≠ 0 := by
      contrapose! hxi
      exact funext hxi
    obtain ⟨i, hi⟩ := hExists
    have hSum : 0 < ∑ j : Fin (Module.finrank ℝ E), xi j ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg (xi j))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hLeft :
        0 < D.ellMin * ∑ j : Fin (Module.finrank ℝ E), xi j ^ 2 :=
      mul_pos hD.ellMin_pos hSum
    refine hLeft.trans_le ?_
    calc
      D.ellMin * ∑ j : Fin (Module.finrank ℝ E), xi j ^ 2 ≤
          ∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) (gSeq k) alpha b p q * xi p * xi q := hEll
      _ = star xi ⋝ᵥ
          chartInvGramMatrix (I := I) (gSeq k) alpha b *ᵥ xi := by
        symmetry
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        ring

/-- Intrinsic low-regularity ellipticity rewritten as the Euclidean quadratic
form bounds consumed by `spdSqrtEquiv`. -/
theorem frozenGram_bounds {index : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : index → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D)
    (alpha : M) (hAlpha : alpha ∈ chartAtlasPOU_finset (I := I) (M := M))
    (k : index) (b : M)
    (hb : b ∈ tsupport
      ((chartAtlasPOU I M alpha : C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    D.ellMin * ‖x‖ ^ 2 ≤
        ⟪x, Matrix.toEuclideanCLM
          (chartInvGramMatrix (I := I) (gSeq k) alpha b) x⟫_ℝ ∧
      ⟪x, Matrix.toEuclideanCLM
          (chartInvGramMatrix (I := I) (gSeq k) alpha b) x⟫_ℝ ≤
        D.ellMax * ‖x‖ ^ 2 := by
  have hEll := hD.elliptic alpha hAlpha k b hb (fun i => x i)
  constructor
  · rw [EuclideanSpace.real_norm_sq_eq,
      frozenGram_quad (I := I) (gSeq k) alpha b x]
    exact hEll.1
  · rw [EuclideanSpace.real_norm_sq_eq,
      frozenGram_quad (I := I) (gSeq k) alpha b x]
    exact hEll.2

/-- Positive-square-root coordinates for one frozen active inverse-Gram
matrix.  The global unknown remains a metric path; this is only a local
coordinate equivalence used inside its canonical chart gauge. -/
def frozenGramEquiv {index : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : index → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D)
    (alpha : M) (hAlpha : alpha ∈ chartAtlasPOU_finset (I := I) (M := M))
    (k : index) (b : M)
    (hb : b ∈ tsupport
      ((chartAtlasPOU I M alpha : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  spdSqrtEquiv (chartInvGramMatrix (I := I) (gSeq k) alpha b)
    (frozenGram_posDef (I := I) gBase gSeq D hD alpha hAlpha k b hb)

/-- Exact frozen-principal factorization. -/
theorem frozenGram_comp {index : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : index → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D)
    (alpha : M) (hAlpha : alpha ∈ chartAtlasPOU_finset (I := I) (M := M))
    (k : index) (b : M)
    (hb : b ∈ tsupport
      ((chartAtlasPOU I M alpha : C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    frozenGramEquiv (I := I) gBase gSeq D hD alpha hAlpha k b hb
        (frozenGramEquiv (I := I) gBase gSeq D hD alpha hAlpha k b hb x) =
      Matrix.toEuclideanCLM
        (chartInvGramMatrix (I := I) (gSeq k) alpha b) x := by
  exact spdSqrt_comp _ _ x

/-- Uniform operator-norm bound for all active frozen coordinate maps. -/
theorem frozenGram_norm_le {index : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : index → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D)
    (alpha : M) (hAlpha : alpha ∈ chartAtlasPOU_finset (I := I) (M := M))
    (k : index) (b : M)
    (hb : b ∈ tsupport
      ((chartAtlasPOU I M alpha : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    ‖(frozenGramEquiv (I := I) gBase gSeq D hD alpha hAlpha k b hb :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ≤ √D.ellMax := by
  apply spdSqrt_norm_le _ _ hD.ellMax_pos.le
  intro x
  exact (frozenGram_bounds (I := I) gBase gSeq D hD alpha hAlpha k b hb x).2

/-- Uniform inverse operator-norm bound for all active frozen coordinate
maps. -/
theorem frozenGram_inv_le {index : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : index → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D)
    (alpha : M) (hAlpha : alpha ∈ chartAtlasPOU_finset (I := I) (M := M))
    (k : index) (b : M)
    (hb : b ∈ tsupport
      ((chartAtlasPOU I M alpha : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    ‖((frozenGramEquiv (I := I) gBase gSeq D hD alpha hAlpha k b hb).symm :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ≤ (√D.ellMin)⁻¹ := by
  apply spdSqrt_inv_le _ _ hD.ellMin_pos
  intro x
  exact (frozenGram_bounds (I := I) gBase gSeq D hD alpha hAlpha k b hb x).1

end DifferentialGeometry.PDE.RicciFlow
