import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import Mathlib.Topology.Sequences

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem unit_initial_subsegment_edist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (a L : ℝ) (ha : 0 < a) (hL : 0 ≤ L) (hLa : L ≤ a)
    (hmin : (riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p u a)).toReal = a) :
    riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p u L) =
      ENNReal.ofReal L := by
  let v : TangentSpace I p := a • u
  have hexp : expMapIntrinsic (I := I) g hEnorm p v =
      intrinsicGeodesic (I := I) g hEnorm p u a :=
    intrinsicGeodesic_smul (I := I) g hEnorm p u a
  have hlen : Real.sqrt (g.inner p v v) = a := by
    dsimp only [v]
    rw [sqrt_gInner_smul_self (I := I) g p ha.le, hu, Real.sqrt_one, mul_one]
  have hfin : riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p u a) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hmin
    linarith
  have hratio : L / a ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hL ha.le, (div_le_one ha).2 hLa⟩
  have h := minSegment_edist (I := I) g hEnorm v hexp hlen hmin.symm hfin hratio
  have hparam : intrinsicGeodesic (I := I) g hEnorm p v (L / a) =
      intrinsicGeodesic (I := I) g hEnorm p u L := by
    calc
      _ = intrinsicGeodesic (I := I) g hEnorm p u (a * (L / a)) :=
        intrinsicGeo_smul_apply (I := I) g hEnorm p u a (L / a)
      _ = _ := by rw [mul_div_cancel₀ L ha.ne']
  rw [hparam, div_mul_cancel₀ L ha.ne'] at h
  exact h

theorem minimizing_ray_of_tendsto_unit_vectors
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : ℕ → TangentSpace I p) (d : ℕ → ℝ) (u : TangentSpace I p)
    (hunit : ∀ n, g.inner p (v n) (v n) = 1)
    (hdpos : ∀ n, 0 < d n)
    (hmin : ∀ n, (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v n) (d n))).toReal = d n)
    (hd : Tendsto d atTop atTop) (hv : Tendsto v atTop (𝓝 u)) :
    ∀ L : ℝ, 0 ≤ L → riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p u L) = ENNReal.ofReal L := by
  intro L hL
  have hc : Continuous (fun w : TangentSpace I p =>
      riemannianEDist I p (expMapIntrinsic (I := I) g hEnorm p (L • w))) := by
    have h := (continuous_riemannianEDist_to (I := I) p).comp
      ((expMapIntrinsic_continuous (I := I) g hEnorm p).comp
        (continuous_const_smul L : Continuous (fun w : TangentSpace I p => L • w)))
    simpa only [Function.comp_def, riemannianEDist_comm] using h
  have hevent : ∀ᶠ n in atTop,
      riemannianEDist I p (expMapIntrinsic (I := I) g hEnorm p (L • v n)) =
        ENNReal.ofReal L := by
    filter_upwards [hd (eventually_ge_atTop L)] with n hn
    simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using
      unit_initial_subsegment_edist (I := I) g hEnorm p (v n) (hunit n)
        (d n) L (hdpos n) hL hn (hmin n)
  have hconst : Tendsto (fun n =>
      riemannianEDist I p (expMapIntrinsic (I := I) g hEnorm p (L • v n)))
      atTop (𝓝 (ENNReal.ofReal L)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)
  have h := tendsto_nhds_unique ((hc.tendsto u).comp hv) hconst
  simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using h

theorem exists_minimizing_ray_subsequence
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : ℕ → TangentSpace I p) (d : ℕ → ℝ)
    (hunit : ∀ n, g.inner p (v n) (v n) = 1)
    (hdpos : ∀ n, 0 < d n)
    (hmin : ∀ n, (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v n) (d n))).toReal = d n)
    (hd : Tendsto d atTop atTop) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (v ∘ phi) atTop (𝓝 u) ∧
        ∀ L : ℝ, 0 ≤ L → riemannianEDist I p
          (intrinsicGeodesic (I := I) g hEnorm p u L) = ENNReal.ofReal L := by
  obtain ⟨u, hu, phi, hphi, hlim⟩ :=
    (gUnitSphere_isCompact (I := I) g p).tendsto_subseq hunit
  refine ⟨u, hu, phi, hphi, hlim, ?_⟩
  exact minimizing_ray_of_tendsto_unit_vectors (I := I) g hEnorm p (v ∘ phi) (d ∘ phi) u
    (fun n => hunit (phi n)) (fun n => hdpos (phi n)) (fun n => hmin (phi n))
    (hd.comp hphi.tendsto_atTop) hlim

end DifferentialGeometry.Geometry.Comparison.Toponogov

end
