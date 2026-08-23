import DifferentialGeometry.Geometry.Comparison.Variation.JacobiGram
import DifferentialGeometry.Geometry.Exponential.EndpointShape
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold Matrix
open scoped Topology Manifold ContDiff Matrix

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

def velJacFrame
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x) :
    Option (Fin d) →
      ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm x u t)
  | none => fun t => curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) t
  | some i => fun t => intrinsicJacobi (I := I) g hEnorm x u (w i) t

@[simp] theorem velJacFrame_none
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x) :
    velJacFrame (I := I) g hEnorm x u w none =
      fun t => curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) t :=
  rfl

@[simp] theorem velJacFrame_some
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x)
    (i : Fin d) :
    velJacFrame (I := I) g hEnorm x u w (some i) =
      fun t => intrinsicJacobi (I := I) g hEnorm x u (w i) t :=
  rfl

theorem velJac_gram_split
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x)
    (hperp : ∀ i, g.inner x u (w i) = 0) :
    (curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
        (velJacFrame (I := I) g hEnorm x u w) 1).det
      = g.inner x u u *
        (curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) 1).det := by
  classical
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u with hγ
  set vel : TangentSpace I (γ 1) := curveVelocity (I := I) γ 1 with hvel
  set T : Matrix (Fin d) (Fin d) ℝ :=
    curveGram (I := I) g γ (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) 1
      with hT
  have hdiag : g.inner (γ 1) vel vel = g.inner x u u := by
    simpa only [hvel, curveVelocity, hγ] using
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x u 1
  have hcross : ∀ i, g.inner (γ 1) vel
      (intrinsicJacobi (I := I) g hEnorm x u (w i) 1) = 0 := by
    intro i
    have hp := intrinsicJacobi_perp (I := I) g hEnorm x u (w i)
    rw [hperp i] at hp
    simpa only [hvel, hγ, curveVelocity, intrinsicVelocityLift] using hp
  let e : Option (Fin d) ≃ Fin d ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit (Fin d)
  let D : Matrix PUnit.{1} PUnit.{1} ℝ := Matrix.of fun _ _ => g.inner x u u
  have hblock :
      Matrix.reindex e e
          (curveGram (I := I) g γ (velJacFrame (I := I) g hEnorm x u w) 1) =
        Matrix.fromBlocks T 0 0 D := by
    ext a b
    rcases a with i | a
    · rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inl, Matrix.fromBlocks_apply₁₁,
          curveGram, Matrix.of_apply, velJacFrame_some, hT]
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inl,
          Equiv.optionEquivSumPUnit_symm_inr, Matrix.fromBlocks_apply₁₂,
          curveGram, Matrix.of_apply, velJacFrame_some, velJacFrame_none]
        rw [g.symm]
        exact hcross i
    · cases a
      rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr,
          Equiv.optionEquivSumPUnit_symm_inl, Matrix.fromBlocks_apply₂₁,
          curveGram, Matrix.of_apply, velJacFrame_some, velJacFrame_none]
        exact hcross j
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr, Matrix.fromBlocks_apply₂₂,
          curveGram, Matrix.of_apply, velJacFrame_none, D]
        exact hdiag
  have hreindexDet :
      (Matrix.reindex e e
          (curveGram (I := I) g γ (velJacFrame (I := I) g hEnorm x u w) 1)).det =
        (curveGram (I := I) g γ (velJacFrame (I := I) g hEnorm x u w) 1).det :=
    Matrix.det_reindex_self e _
  have hDdet : D.det = g.inner x u u := by
    rw [Matrix.det_unique]; rfl
  have hdet :
      (curveGram (I := I) g γ (velJacFrame (I := I) g hEnorm x u w) 1).det =
        T.det * D.det := by
    rw [← hreindexDet, hblock, Matrix.det_fromBlocks_zero₂₁]
  rw [hdet, hDdet, hT, mul_comm]

theorem velJac_density_split
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x)
    (hperp : ∀ i, g.inner x u (w i) = 0) :
    curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
        (velJacFrame (I := I) g hEnorm x u w) 1
      = Real.sqrt (g.inner x u u) *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) 1 := by
  have hnn : 0 ≤ g.inner x u u := by
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu]
    · exact (g.pos x u hu).le
  rw [curveDensity, curveDensity, velJac_gram_split (I := I) g hEnorm x u w hperp,
    Real.sqrt_mul hnn]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] in
theorem curveGram_recomb
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V V' : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) (C : Matrix ι ι ℝ)
    (h : ∀ i, V' i t = ∑ k, C k i • V k t) :
    curveGram (I := I) g γ V' t = Cᵀ * curveGram (I := I) g γ V t * C := by
  ext i j
  have hexp :
      g.inner (γ t) (V' i t) (V' j t)
        = ∑ k, ∑ l, C k i * C l j * g.inner (γ t) (V k t) (V l t) := by
    rw [h i, h j]
    have hL : g.inner (γ t) (∑ k, C k i • V k t)
          = ∑ k, C k i • g.inner (γ t) (V k t) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => ContinuousLinearMap.map_smul _ _ _
    rw [hL, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.smul_apply]
    have hR : g.inner (γ t) (V k t) (∑ l, C l j • V l t)
          = ∑ l, C l j * g.inner (γ t) (V k t) (V l t) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [curveGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] in
theorem curveDensity_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : κ → ∀ t, TangentSpace I (γ t)) (t : ℝ) (e : ι ≃ κ) :
    curveDensity (I := I) g γ (fun i => V (e i)) t
      = curveDensity (I := I) g γ V t := by
  rw [curveDensity, curveDensity]
  congr 1
  have hsub : curveGram (I := I) g γ (fun i => V (e i)) t
      = (curveGram (I := I) g γ V t).submatrix e e := by
    ext i j; simp only [curveGram, Matrix.of_apply, Matrix.submatrix_apply]
  rw [hsub, Matrix.det_submatrix_equiv_self]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] in
theorem curveDensity_recomb
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V V' : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ) (C : Matrix ι ι ℝ)
    (h : ∀ i, V' i t = ∑ k, C k i • V k t) :
    curveDensity (I := I) g γ V' t = |C.det| * curveDensity (I := I) g γ V t := by
  rw [curveDensity, curveDensity, curveGram_recomb (I := I) g γ V V' t C h,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show C.det * (curveGram (I := I) g γ V t).det * C.det
        = C.det ^ 2 * (curveGram (I := I) g γ V t).det from by ring,
    Real.sqrt_mul (sq_nonneg C.det), Real.sqrt_sq_eq_abs]

theorem jacDens_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) (u : TangentSpace I x)
    (B B' : Module.Basis ι ℝ (TangentSpace I x)) :
    curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
        (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B' i) t) 1 =
      |B.det B'| *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B i) t) 1 := by
  classical
  let C : Matrix ι ι ℝ := B.toMatrix B'
  let L :=
    mfderiv 𝓘(ℝ, E) I
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b))
      (show E from u)
  have hcoord (i : ι) : B' i = ∑ k, C k i • B k := by
    simpa only [C, Module.Basis.toMatrix_apply] using (B.sum_repr (B' i)).symm
  have hcol (w : TangentSpace I x) :
      intrinsicJacobi (I := I) g hEnorm x u w 1 =
        L (show E from w) := by
    exact intrinsic_jacobi_one (I := I) g hEnorm x u w
  have hjac (i : ι) :
      intrinsicJacobi (I := I) g hEnorm x u (B' i) 1 =
        ∑ k, C k i • intrinsicJacobi (I := I) g hEnorm x u (B k) 1 := by
    rw [hcol, hcoord i]
    change
      L (∑ k, C k i • (show E from B k)) =
        ∑ k, C k i • intrinsicJacobi (I := I) g hEnorm x u (B k) 1
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    calc
      L (C k i • (show E from B k)) =
          C k i • L (show E from B k) := L.map_smul _ _
      _ = C k i • intrinsicJacobi (I := I) g hEnorm x u (B k) 1 := by
        rw [hcol]
        rfl
  simpa only [C, Module.Basis.det_apply] using
    curveDensity_recomb (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x u)
      (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B i) t)
      (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B' i) t)
      1 C hjac

theorem transDens_scale
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) (u : TangentSpace I x) {d : ℕ}
    (w : Fin d → TangentSpace I x) (t : ℝ) :
    curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x u)
        (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) t =
      |t| ^ d *
        curveDensity (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm x (t • u))
          (fun i => intrinsicJacobi (I := I) g hEnorm x (t • u) (w i)) 1 := by
  let L :=
    mfderiv 𝓘(ℝ, E) I
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b))
      (t • (show E from u))
  have hcol (v : TangentSpace I x) :
      (intrinsicJacobi (I := I) g hEnorm x u v t : E) =
        t • (intrinsicJacobi (I := I) g hEnorm x (t • u) v 1 : E) := by
    have hat :
        (intrinsicJacobi (I := I) g hEnorm x u v t : E) =
          (L (t • (show E from v)) : E) := by
      exact intrinsic_jacobi_at (I := I) g hEnorm x
        (show E from u) (show E from v) t
    have hmap :
        (L (t • (show E from v)) : E) =
          t • (L (show E from v) : E) := by
      exact L.map_smul _ _
    have hone :
        (intrinsicJacobi (I := I) g hEnorm x (t • u) v 1 : E) =
          (L (show E from v) : E) := by
      exact intrinsic_jacobi_one (I := I) g hEnorm x
        (t • (show E from u)) (show E from v)
    exact hat.trans (hmap.trans (congrArg (fun z : E => t • z) hone.symm))
  have hgram :
      curveGram (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) t =
        (t ^ 2) •
          curveGram (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x (t • u))
            (fun i => intrinsicJacobi (I := I) g hEnorm x (t • u) (w i)) 1 := by
    ext i j
    simp only [curveGram, Matrix.of_apply, Matrix.smul_apply]
    rw [intrinsicGeodesic_smul (I := I) g hEnorm x u t]
    change
      g.inner
          (intrinsicGeodesic (I := I) g hEnorm x u t)
          (intrinsicJacobi (I := I) g hEnorm x u (w i) t)
          (intrinsicJacobi (I := I) g hEnorm x u (w j) t) =
        t ^ 2 *
          g.inner
            (intrinsicGeodesic (I := I) g hEnorm x u t)
            (intrinsicJacobi (I := I) g hEnorm x (t • u) (w i) 1)
            (intrinsicJacobi (I := I) g hEnorm x (t • u) (w j) 1)
    rw [hcol, hcol]
    let β : E →L[ℝ] E →L[ℝ] ℝ :=
      g.inner (intrinsicGeodesic (I := I) g hEnorm x u t)
    let X : E :=
      (intrinsicJacobi (I := I) g hEnorm x (t • u) (w i) 1 : E)
    let Y : E :=
      (intrinsicJacobi (I := I) g hEnorm x (t • u) (w j) 1 : E)
    change β (t • X) (t • Y) = t ^ 2 * β X Y
    have hleft : β (t • X) (t • Y) = t * β X (t • Y) := by
      have h := congrArg (fun A : E →L[ℝ] ℝ => A (t • Y)) (β.map_smul t X)
      simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
    have hright : β X (t • Y) = t * β X Y := by
      simpa only [smul_eq_mul] using (β X).map_smul t Y
    rw [hleft, hright, pow_two]
    ring
  rw [curveDensity, curveDensity, hgram, Matrix.det_smul, Fintype.card_fin]
  have hpow : (t ^ 2) ^ d = (t ^ d) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow, Real.sqrt_mul (sq_nonneg (t ^ d)), Real.sqrt_sq_eq_abs, abs_pow]

theorem radialJac_eq_vel
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) :
    intrinsicJacobi (I := I) g hEnorm x u u 1
      = curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) 1 := by
  set φ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u with hφ
  have hrepar : (fun r : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + r • u) 1)
      = fun r : ℝ => φ (1 + r) := by
    funext r
    have hsmul : u + r • u = (1 + r) • u := by rw [add_smul, one_smul]
    rw [hsmul, intrinsicGeodesic_smul (I := I) g hEnorm x u (1 + r)]
  have hφ_mdiff1 : MDifferentiableAt 𝓘(ℝ, ℝ) I φ 1 :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm x u).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by norm_num)
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => 1 + r) 0
      (ContinuousLinearMap.id ℝ ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    simpa using ((hasFDerivAt_id (0 : ℝ)).const_add (1 : ℝ))
  have hφ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I φ (1 + (0 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I φ 1) := by
    rw [add_zero]; exact hφ_mdiff1.hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun r : ℝ => φ (1 + r)) 0
      ((mfderiv 𝓘(ℝ, ℝ) I φ 1).comp (ContinuousLinearMap.id ℝ ℝ)) :=
    hφ_at.comp 0 hshift
  have hJ : HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun r : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + r • u) 1) 0
      ((mfderiv 𝓘(ℝ, ℝ) I φ 1).comp (ContinuousLinearMap.id ℝ ℝ)) := by
    rw [hrepar]; exact hcomp
  change mfderiv 𝓘(ℝ, ℝ) I
      (fun r : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + r • u) 1) 0 1
    = mfderiv 𝓘(ℝ, ℝ) I φ 1 1
  rw [hJ.mfderiv]
  rfl

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
