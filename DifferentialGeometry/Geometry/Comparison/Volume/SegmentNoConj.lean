import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Comparison.HalfSqDistGrad
import DifferentialGeometry.Geometry.Comparison.Variation.MinimalGeodesicNoConjugate

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem segDom_no_conj
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {x : M} {v : TangentSpace I x}
    (hv : v ∈ SegDom (I := I) g hEnorm x)
    (hv0 : v ≠ 0) :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      ¬ IsConjVec (I := I) g hEnorm x
        ((t • v : TangentSpace I x) : E) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  classical
  let L : ℝ := Real.sqrt (g.inner x v v)
  let u : TangentSpace I x := L⁻¹ • v
  have hL_pos : 0 < L := by
    exact Real.sqrt_pos.mpr (g.pos x v hv0)
  have hL_ne : L ≠ 0 := hL_pos.ne'
  have hinner : g.inner x v v = L ^ 2 := by
    have h := Real.sq_sqrt (gInner_self_nonneg (I := I) g x v)
    simpa only [L] using h.symm
  have hu_unit : g.inner x u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self (I := I) g x, hinner]
    field_simp [hL_ne]
  have hscale : L • u = v := by
    dsimp only [u]
    rw [smul_smul]
    field_simp [hL_ne]
    simp
  have hscaleE : L • (u : E) = (v : E) :=
    congrArg (fun w : TangentSpace I x => (w : E)) hscale
  have hcurve_end :
      intrinsicGeodesic (I := I) g hEnorm x u L =
        expMapIntrinsic (I := I) g hEnorm x v := by
    calc
      intrinsicGeodesic (I := I) g hEnorm x u L =
          intrinsicGeodesic (I := I) g hEnorm x (L • u) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x u L).symm
      _ = intrinsicGeodesic (I := I) g hEnorm x v 1 := by rw [hscale]
      _ = expMapIntrinsic (I := I) g hEnorm x v := rfl
  have hLdist :
      L = (riemannianEDist I x
        (expMapIntrinsic (I := I) g hEnorm x v)).toReal := by
    simpa only [L] using
      (mem_segDom (I := I) (g := g) (hEnorm := hEnorm)).mp hv
  have hmin :
      ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
        η 0 = x →
        η L = intrinsicGeodesic (I := I) g hEnorm x u L →
        arcLength (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x u) 0 L ≤
          arcLength (I := I) g η 0 L := by
    intro η hη hη0 hηL
    have hη_end :
        η L = expMapIntrinsic (I := I) g hEnorm x v :=
      hηL.trans hcurve_end
    have hη_nonneg : 0 ≤ arcLength (I := I) g η 0 L := by
      unfold arcLength
      exact intervalIntegral.integral_nonneg hL_pos.le
        (fun _ _ => Real.sqrt_nonneg _)
    have hed :=
      riemannianEDist_le_arcLength
        (I := I) g hL_pos.le hη
        (fun s _ => hEnorm (η s) _)
    have hreal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hL_le : L ≤ arcLength (I := I) g η 0 L := by
      rw [hη0, hη_end, ENNReal.toReal_ofReal hη_nonneg] at hreal
      calc
        L = (riemannianEDist I x
              (expMapIntrinsic (I := I) g hEnorm x v)).toReal := hLdist
        _ ≤ arcLength (I := I) g η 0 L := hreal
    rw [arcLength_radial (I := I) g hEnorm x u 0 L,
      hu_unit, Real.sqrt_one, sub_zero, mul_one]
    exact hL_le
  intro t ht
  have hc : t * L ∈ Ioo (0 : ℝ) L :=
    ⟨mul_pos ht.1 hL_pos,
      (mul_lt_iff_lt_one_left hL_pos).mpr ht.2⟩
  have hno :=
    not_conj_of_min_len
      (I := I) g hEnorm x (u : E)
      hu_unit L hL_pos hmin hc
  have hvec :
      (t * L) • (u : E) = t • (v : E) := by
    calc
      (t * L) • (u : E) = t • (L • (u : E)) := by module
      _ = t • (v : E) :=
        congrArg (fun w : E => t • w) hscaleE
  intro hconj
  apply hno
  exact hvec.symm ▸ hconj

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
