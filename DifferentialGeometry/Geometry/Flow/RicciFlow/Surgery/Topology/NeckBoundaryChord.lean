import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SphereChordConnector
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Topology.Manifold.OpenSubtype

noncomputable section

open Bundle Manifold MeasureTheory Set
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

namespace NormalizedNeck

def boundaryPoint (N : NormalizedNeck g δ k) (y : Sphere 2) : M :=
  N.chart ⟨(y, 0), by
    have hp := inv_pos.mpr N.delta_pos
    constructor <;> linarith⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem boundaryPoint_smooth (N : NormalizedNeck g δ k) :
    ContMDiff (𝓡 2) ThreeModel ∞ N.boundaryPoint := by
  let ι : Sphere 2 → neckBuffer δ := fun y => ⟨(y, 0), by
    have hp := inv_pos.mpr N.delta_pos
    constructor <;> linarith⟩
  have hi : ContMDiff (𝓡 2) NeckCylinderModel ∞ ι :=
    (ContMDiff.subtypeVal_comp_iff (neckBuffer δ) ι).mp
      (contMDiff_id.prodMk contMDiff_const)
  exact N.chart_smooth.contMDiff.comp hi

omit [T2Space M] [SigmaCompactSpace M] in
/-- A connector lies on the actual central sphere and has terminal metric length
bounded by the Euclidean chord of its labels. -/
theorem exists_boundary_curve (N : NormalizedNeck g δ k) (y z : Sphere 2) :
    ∃ σ : ℝ → Sphere 2,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ σ ∧ σ 0 = y ∧ σ 1 = z ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (N.boundaryPoint ∘ σ) ∧
      metricPathELength g (N.boundaryPoint ∘ σ) 0 1 ≤
        ENNReal.ofReal (Real.pi / Real.sqrt N.scale * ‖(y : ThreeSpace) - z‖) := by
  obtain ⟨L, σ, hL, hchord, hσ, hσ0, hσ1, hspeed⟩ :=
    Perelman.KappaSolutions.sphere2_exists_chord_controlled_curve y z
  let β : ℝ → neckBuffer δ := fun t => ⟨(σ t, 0), by
    have hp := inv_pos.mpr N.delta_pos
    constructor <;> linarith⟩
  have hβ : ContMDiff 𝓘(ℝ, ℝ) NeckCylinderModel ∞ β :=
    (ContMDiff.subtypeVal_comp_iff (neckBuffer δ) β).mp
      (hσ.prodMk contMDiff_const)
  have hΓ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (N.boundaryPoint ∘ σ) :=
    N.boundaryPoint_smooth.comp hσ
  have hder (t : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1 : EuclideanSpace ℝ (Fin 2) × ℝ) =
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1, 0) := by
    have hsub := mfderiv_comp_apply t
      ((contMDiff_subtype_val (I := NeckCylinderModel) (U := neckBuffer δ)
        (n := ∞)).mdifferentiableAt (x := β t) (by decide))
      (hβ.mdifferentiableAt (x := t) (by decide)) (1 : ℝ)
    rw [mfderiv_subtype_val_apply] at hsub
    have hprod := mfderiv_prodMk (hσ.mdifferentiableAt (x := t) (by decide))
      (mdifferentiableAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ)))
    have hpair := congrArg
      (fun D : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) => D 1) hprod
    change (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel
        (fun t => (σ t, (0 : ℝ))) t 1 : EuclideanSpace ℝ (Fin 2) × ℝ) =
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1,
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => (0 : ℝ)) t 1) at hpair
    have heq := hsub.symm.trans hpair
    simpa only [mfderiv_const, zero_apply] using! heq
  have href (t : ℝ) :
      (roundCylinderMetric.restrictOpen (neckBuffer δ)).inner (β t)
        (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1)
        (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1) = 2 * L ^ 2 := by
    change roundCylinderMetric.inner (β t).val
      (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1)
      (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1) = _
    erw [roundCylinderMetric_eq_geometry, Geometry.Metric.roundCylinderMetric_inner]
    change 2 * inner ℝ
        (dIncl (n := 2) (σ t) (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1).1)
        (dIncl (n := 2) (σ t) (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1).1) +
      (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1).2 *
        (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1).2 = _
    rw [hder t]
    change 2 * inner ℝ
        (dIncl (n := 2) (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1))
        (dIncl (n := 2) (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1)) + 0 * 0 = _
    rw [← roundMetric_inner, hspeed t]
    ring
  have hΓder (t : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) ThreeModel (N.boundaryPoint ∘ σ) t 1 =
        mfderiv NeckCylinderModel ThreeModel N.chart (β t)
          (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1) :=
    mfderiv_comp_apply t
      (N.chart_smooth.contMDiff.mdifferentiableAt (x := β t) (by decide))
      (hβ.mdifferentiableAt (x := t) (by decide)) (1 : ℝ)
  have hterminal (t : ℝ) :
      Real.sqrt (g.inner ((N.boundaryPoint ∘ σ) t)
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (N.boundaryPoint ∘ σ) t 1)
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (N.boundaryPoint ∘ σ) t 1)) ≤
      2 * L / Real.sqrt N.scale := by
    have hcore : β t ∈ neckClosedTest δ := by
      have hp := inv_pos.mpr N.delta_pos
      change -δ⁻¹ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ δ⁻¹
      constructor <;> linarith
    have herr := metricDerivNorm_lt_of_sup_lt (isCompact_neckClosedTest δ)
      (Nat.zero_le k) N.normalizedMetric
      (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) N.closeness hcore
    have hb := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) N.normalizedMetric (β t)
      herr.le (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel β t 1)).2
    rw [href t, N.normalized_inner, ← hΓder t] at hb
    change N.scale * g.inner ((N.boundaryPoint ∘ σ) t)
      (mfderiv 𝓘(ℝ, ℝ) ThreeModel (N.boundaryPoint ∘ σ) t 1)
      (mfderiv 𝓘(ℝ, ℝ) ThreeModel (N.boundaryPoint ∘ σ) t 1) ≤
        (1 + δ) * (2 * L ^ 2) at hb
    have hupper : g.inner ((N.boundaryPoint ∘ σ) t)
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (N.boundaryPoint ∘ σ) t 1)
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (N.boundaryPoint ∘ σ) t 1) ≤
        (2 * L / Real.sqrt N.scale) ^ 2 := by
      have heq : N.scale * (2 * L / Real.sqrt N.scale) ^ 2 = 4 * L ^ 2 := by
        rw [div_pow, Real.sq_sqrt N.scale_pos.le]
        field_simp [N.scale_pos.ne']; ring
      apply (mul_le_mul_iff_right₀ N.scale_pos).mp
      rw [heq]
      have hδ := mul_nonneg (sub_nonneg.mpr N.delta_lt_one.le) (sq_nonneg L)
      nlinarith
    exact (Real.sqrt_le_sqrt hupper).trans_eq
      (Real.sqrt_sq (div_nonneg (mul_nonneg (by norm_num) hL.1) (Real.sqrt_nonneg _)))
  have hlength : metricPathELength g (N.boundaryPoint ∘ σ) 0 1 ≤
      ENNReal.ofReal (2 * L / Real.sqrt N.scale) := by
    rw [metricPathELength_eq]
    calc
      _ ≤ ∫⁻ _t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * L / Real.sqrt N.scale) :=
        setLIntegral_mono' measurableSet_Ioo fun t _ => ENNReal.ofReal_le_ofReal (hterminal t)
      _ = _ := by rw [setLIntegral_const, Real.volume_Ioo]; norm_num
  refine ⟨σ, hσ, hσ0, hσ1, hΓ, hlength.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  apply (div_le_iff₀ (Real.sqrt_pos.mpr N.scale_pos)).mpr
  have heq : Real.pi / Real.sqrt N.scale * ‖(y : ThreeSpace) - z‖ *
      Real.sqrt N.scale = Real.pi * ‖(y : ThreeSpace) - z‖ := by
    field_simp [(Real.sqrt_pos.mpr N.scale_pos).ne']
  rw [heq]
  linarith

omit [T2Space M] [SigmaCompactSpace M] in
theorem edist_boundaryPoint_le_chord (N : NormalizedNeck g δ k) (y z : Sphere 2) :
    riemannianEDistOf g (N.boundaryPoint y) (N.boundaryPoint z) ≤
      ENNReal.ofReal (Real.pi / Real.sqrt N.scale * ‖(y : ThreeSpace) - z‖) := by
  obtain ⟨σ, _, h0, h1, hγ, hlength⟩ := N.exists_boundary_curve y z
  let : RiemannianBundle (TangentSpace ThreeModel : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hb := Manifold.riemannianEDist_le_pathELength
    (hγ.of_le (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).contMDiffOn
    (show (N.boundaryPoint ∘ σ) 0 = N.boundaryPoint y by rw [Function.comp_apply, h0])
    (show (N.boundaryPoint ∘ σ) 1 = N.boundaryPoint z by rw [Function.comp_apply, h1])
    (by norm_num : (0 : ℝ) ≤ 1)
  exact hb.trans hlength

end NormalizedNeck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
