import DifferentialGeometry.Geometry.Comparison.Volume.BishopIntrinsicDeriv
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Field.Smoothness
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open CovariantDerivativeAlong Exponential Geodesic Variation BonnetMyers

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]


variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem segRadial_deriv_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (b : Real)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hb : (b • u : TangentSpace I p) ∈ SegmentInt (I := I) g hEnorm p)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i)
    let J := fun t ↦ normalChartDensity (I := I) g p 0 *
      curveDensity (I := I) g γ V t
    ∀ t ∈ Ioo (0 : Real) b,
      HasDerivAt J
          (normalChartDensity (I := I) g p 0 *
            (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t)) t ∧
        deriv J t ≤ ((Module.finrank Real E - 1 : Nat) : Real) / t * J t ∧
        expJacobianDensity (I := I) g hEnorm p ((t • u) : E) *
            t ^ (Module.finrank Real E - 1) = J t := by
  classical
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let V := fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i)
  let J := fun t ↦ normalChartDensity (I := I) g p 0 *
    curveDensity (I := I) g γ V t
  dsimp only
  intro t ht
  have hbpos : 0 < b := ht.1.trans ht.2
  have hno : ∀ s ∈ Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p ((s • u : TangentSpace I p) : E) := by
    intro s hs
    have hs0 : 0 ≤ s / b := div_nonneg hs.1.le hbpos.le
    have hs1 : s / b ≤ 1 := (div_le_one hbpos).mpr hs.2.le
    have hscaled := segmentInt_smul (I := I) g hEnorm hb hs0 hs1
    have hsSeg : (s • u : TangentSpace I p) ∈ SegmentInt (I := I) g hEnorm p := by
      simpa only [smul_smul, div_mul_cancel₀ s hbpos.ne'] using hscaled
    exact segmentInt_no_conj (I := I) g hEnorm hsSeg
  have hden :=
    intrDen_deriv_le (I := I) g hEnorm p u b hd hu v hON hperp hno hRic
  have hdenAt := hden t ht
  have hJ : HasDerivAt J
      (normalChartDensity (I := I) g p 0 *
        (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t)) t := by
    simpa only [J, γ, V] using
      hdenAt.1.const_mul (normalChartDensity (I := I) g p 0)
  have hc : 0 ≤ normalChartDensity (I := I) g p 0 := Real.sqrt_nonneg _
  have hvalue :
      normalChartDensity (I := I) g p 0 *
          (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t) ≤
        ((Module.finrank Real E - 1 : Nat) : Real) / t * J t := by
    calc
      normalChartDensity (I := I) g p 0 *
            (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t)
          ≤ normalChartDensity (I := I) g p 0 *
              (((Module.finrank Real E - 1 : Nat) : Real) / t *
                curveDensity (I := I) g γ V t) :=
            mul_le_mul_of_nonneg_left hdenAt.2 hc
      _ = ((Module.finrank Real E - 1 : Nat) : Real) / t * J t := by
        simp only [J]
        ring
  have hderiv :
      deriv J t ≤ ((Module.finrank Real E - 1 : Nat) : Real) / t * J t := by
    rw [hJ.deriv]
    exact hvalue
  have hu0 : u ≠ 0 := by
    intro huz
    subst u
    have hfalse : (0 : Real) < 0 := by
      simpa only [map_zero, zero_apply] using hu
    exact (lt_irrefl 0) hfalse
  have hexp := expJac_radial (I := I) g hEnorm p hu0 v hON hperp t ht.1
  refine ⟨hJ, hderiv, ?_⟩
  simpa only [J, γ, V] using hexp

theorem radialDensity_deriv_le_of_segmentInt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (b : Real)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hseg : ∀ t ∈ Set.Ioo (0 : Real) b,
      (t • u : TangentSpace I p) ∈ SegmentInt (I := I) g hEnorm p)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i)
    let J := fun t ↦ normalChartDensity (I := I) g p 0 *
      curveDensity (I := I) g γ V t
    ∀ t ∈ Set.Ioo (0 : Real) b,
      HasDerivAt J
          (normalChartDensity (I := I) g p 0 *
            (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t)) t ∧
        deriv J t ≤ ((Module.finrank Real E - 1 : Nat) : Real) / t * J t ∧
        expJacobianDensity (I := I) g hEnorm p ((t • u) : E) *
            t ^ (Module.finrank Real E - 1) = J t := by
  intro γ V J t ht
  let c : Real := (t + b) / 2
  have htc : t < c := by
    dsimp only [c]
    linarith [ht.2]
  have hcb : c < b := by
    dsimp only [c]
    linarith [ht.2]
  have hc0 : 0 < c := ht.1.trans htc
  have hcseg : (c • u : TangentSpace I p) ∈ SegmentInt (I := I) g hEnorm p :=
    hseg c ⟨hc0, hcb⟩
  simpa only [γ, V, J] using
    segRadial_deriv_le (I := I) g hEnorm p u c hd hu v hON hperp
      hcseg hRic t ⟨ht.1, htc⟩

omit [ConnectedSpace M] in
theorem radialDensity_absolutelyContinuousOnInterval_of_segmentInt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) {a b : Real}
    (ha : 0 < a) (hab : a ≤ b) (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hseg : ∀ t ∈ Set.Icc a b,
      (t • u : TangentSpace I p) ∈ SegmentInt (I := I) g hEnorm p) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i)
    let J := fun t ↦ normalChartDensity (I := I) g p 0 *
      curveDensity (I := I) g γ V t
    AbsolutelyContinuousOnInterval J a b := by
  classical
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let V := fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i)
  let J := fun t ↦ normalChartDensity (I := I) g p 0 *
    curveDensity (I := I) g γ V t
  dsimp only
  have hV (i : Fin (Module.finrank Real E - 1)) :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun t : Real => TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _)) (γ t) (V i t)) := by
    let F : Real → Real → M := fun s t =>
      intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from (u : E) + s • (v i : E)) t
    have hvar : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
        (fun q : Real × Real => F q.1 q.2) := by
      change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
        (fun q : Real × Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from (u : E) + q.1 • (v i : E)) q.2)
      exact intrinsicVar_smooth (I := I) g hEnorm p (u : E) (v i : E)
    have hfield := varField_smooth (I := I) F hvar
    have hbase : (fun t : Real => F 0 t) = γ := by
      funext t
      simp only [F, γ, zero_smul, add_zero]
    have hJac :
        (fun t : Real => mfderiv 𝓘(Real, Real) I (fun s : Real => F s t) 0 1) =
          V i := by
      funext t
      rfl
    refine hfield.congr fun t => ?_
    rw [congrFun hbase t, ← congrFun hJac t]
    rfl
  have hentry (i j : Fin (Module.finrank Real E - 1)) :
      ContDiff Real ∞ (fun t : Real => g.inner (γ t) (V i t) (V j t)) := by
    let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hinner := ContMDiff.inner_bundle (F := E) (B := M)
      (E := (TangentSpace I : M → Type _)) (b := γ) (v := V i) (w := V j)
        (hV i) (hV j)
    rw [← contMDiff_iff_contDiff]
    exact hinner.congr fun _ => rfl
  have hdet : ContDiff Real ∞
      (fun t : Real => (curveGram (I := I) g γ V t).det) := by
    simp_rw [curveGram, Matrix.det_apply', Matrix.of_apply]
    refine ContDiff.sum fun σ _ => ?_
    exact contDiff_const.mul (contDiff_prod fun i _ => hentry (σ i) i)
  have hvLI : LinearIndependent Real v := by
    simpa only using linIndep_of_ortho (I := I) g p (fun i ↦ (v i : E)) hON
  have hdetPos : ∀ t ∈ Set.Icc a b,
      0 < (curveGram (I := I) g γ V t).det := by
    intro t ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    have hLI : LinearIndependent Real fun i ↦ V i t := by
      simpa only [V] using intrJacobi_li (I := I) g hEnorm p u v hvLI ht0
        (segmentInt_no_conj (I := I) g hEnorm (hseg t ht))
    have hgram := curveGram_det_pos (I := I) g γ V t hLI
    exact pos_of_mul_pos_left (mul_pos hgram hu) hu.le
  have hcurve : ContDiffOn Real 1
      (curveDensity (I := I) g γ V) (Set.Icc a b) := by
    change ContDiffOn Real 1
      (fun t => Real.sqrt (curveGram (I := I) g γ V t).det) (Set.Icc a b)
    apply (hdet.of_le (by norm_num)).contDiffOn.sqrt
    intro t ht
    exact (hdetPos t ht).ne'
  have hJ : ContDiffOn Real 1 J (Set.Icc a b) :=
    contDiffOn_const.mul hcurve
  obtain ⟨K, hK⟩ :=
    hJ.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  have hKu : LipschitzOnWith K J (Set.uIcc a b) := by
    simpa only [uIcc_of_le hab] using hK
  exact hKu.absolutelyContinuousOnInterval

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
