import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeBallChartDictionary
import DifferentialGeometry.Topology.Ehresmann.Interval
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.ThreeManifold.MarkedBallTubeProducer

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
local instance closedCellChartedSpaceThree :
    ChartedSpace (EuclideanHalfSpace 3)
      (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
local instance closedCellIsManifoldThree :
    IsManifold (𝓡∂ 3) ∞ (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

theorem neckPoint_apply_last (u : Sphere 2) (t : ℝ) : neckPoint u t (Fin.last 3) = t / 4 := by
  rw [neckPoint, WithLp.ofLp_toLp]
  simp only [snocR_last]

theorem neckPoint_apply_castSucc (u : Sphere 2) (t : ℝ) (i : Fin 3) :
    neckPoint u t i.castSucc = Real.sqrt (1 - (t / 4) ^ 2) * (u : ThreeSpace) i := by
  rw [neckPoint, WithLp.ofLp_toLp]
  simp only [snocR_castSucc]

theorem neckPoint_zero (u : Sphere 2) :
    neckPoint u 0 = WithLp.toLp 2 (snocR (fun i : Fin 3 => (u : ThreeSpace) i) 0) := by
  rw [neckPoint]
  norm_num

theorem collarHeight_eq_four_mul_neckPoint (u : Sphere 2) (t : ℝ) :
    t = 4 * neckPoint u t (Fin.last 3) := by
  rw [neckPoint_apply_last]
  ring

theorem standardNeckCapPointAmbient_apply_last (side : Bool) (v : ThreeBall) :
    standardNeckCapPointAmbient side (v : ThreeSpace) (Fin.last 3) =
      (if side then -standardNeckCapCAmbient (v : ThreeSpace)
        else standardNeckCapCAmbient (v : ThreeSpace)) := by
  rw [standardNeckCapPointAmbient, WithLp.ofLp_toLp]
  simp only [snocR_last]

theorem standardNeckCapPointAmbient_apply_castSucc (side : Bool) (v : ThreeBall) (i : Fin 3) :
    standardNeckCapPointAmbient side (v : ThreeSpace) i.castSucc =
      (standardNeckCapUAmbient (v : ThreeSpace)).ofLp i := by
  rw [standardNeckCapPointAmbient, WithLp.ofLp_toLp]
  simp only [snocR_castSucc]

abbrev PuncturedClosedCell : Type :=
  {x : DifferentialGeometry.Topology.ClosedCell 3 // (x : ThreeSpace) ≠ 0}

def collarHeight (r : Icc (0 : ℝ) 1) : Icc (-2 : ℝ) 2 :=
  ⟨4 * (r : ℝ) - 2, by
    obtain ⟨h0, h1⟩ := r.2
    constructor <;> linarith⟩

private theorem norm_sphere_eq_one (u : Sphere 2) : ‖(u : ThreeSpace)‖ = 1 := by
  have h := u.2
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  exact h

private theorem norm_ne_zero_of_punctured (x : PuncturedClosedCell) :
    ‖(x.1 : ThreeSpace)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2

private theorem norm_inv_smul_punctured (x : PuncturedClosedCell) :
    ‖(‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace)‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_of_punctured x)]

private theorem smul_inv_norm_punctured (x : PuncturedClosedCell) :
    ‖(x.1 : ThreeSpace)‖ • ((‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace)) =
      (x.1 : ThreeSpace) := by
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_of_punctured x), one_smul]

private def puncturedSpherePoint (x : PuncturedClosedCell) : Sphere 2 :=
  ⟨(‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_inv_smul_punctured x⟩

private def puncturedHeight (x : PuncturedClosedCell) : Icc (-2 : ℝ) 2 :=
  ⟨4 * ‖(x.1 : ThreeSpace)‖ - 2, by
    have h0 : 0 < ‖(x.1 : ThreeSpace)‖ := norm_pos_iff.mpr x.2
    have h1 : ‖(x.1 : ThreeSpace)‖ ≤ 1 := x.1.2
    constructor <;> linarith⟩

private def puncturedOf (v : ThreeSpace) (hv : ‖v‖ ≤ 1) (hv0 : v ≠ 0) :
    PuncturedClosedCell :=
  ⟨⟨v, hv⟩, hv0⟩

private theorem coe_puncturedOf (v : ThreeSpace) (hv : ‖v‖ ≤ 1) (hv0 : v ≠ 0) :
    ((puncturedOf v hv hv0).1 : ThreeSpace) = v := rfl

def collarPolarCoordinates (x : PuncturedClosedCell) : Sphere 2 × Icc (0 : ℝ) 1 :=
  (puncturedSpherePoint x,
    ⟨‖(x.1 : ThreeSpace)‖, Set.mem_Icc.mpr ⟨norm_nonneg _, x.1.2⟩⟩)

private theorem coe_puncturedSpherePoint (x : PuncturedClosedCell) :
    ((puncturedSpherePoint x : Sphere 2) : ThreeSpace) =
      (‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace) := rfl

private theorem coe_collarPolarCoordinates_snd (x : PuncturedClosedCell) :
    ((collarPolarCoordinates x).2 : ℝ) = ‖(x.1 : ThreeSpace)‖ := rfl

def collarFilling (x : PuncturedClosedCell) : TubeDomain :=
  (puncturedSpherePoint x, puncturedHeight x)

theorem collarFilling_fst (x : PuncturedClosedCell) :
    ((collarFilling x).1 : ThreeSpace) = (‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace) :=
  rfl

theorem collarFilling_snd (x : PuncturedClosedCell) :
    ((collarFilling x).2 : ℝ) = 4 * ‖(x.1 : ThreeSpace)‖ - 2 := rfl

private theorem continuous_puncturedValue :
    Continuous fun x : PuncturedClosedCell => (x.1 : ThreeSpace) :=
  continuous_subtype_val.comp continuous_subtype_val

private theorem continuous_puncturedNorm :
    Continuous fun x : PuncturedClosedCell => ‖(x.1 : ThreeSpace)‖ :=
  continuous_norm.comp continuous_puncturedValue

private theorem continuous_puncturedDirection :
    Continuous fun x : PuncturedClosedCell =>
      (‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace) :=
  (continuous_puncturedNorm.inv₀ (fun x => norm_ne_zero_of_punctured x)).smul
    continuous_puncturedValue

theorem continuous_collarPolarCoordinates : Continuous collarPolarCoordinates :=
  Continuous.prodMk (Continuous.subtype_mk continuous_puncturedDirection _)
    (Continuous.subtype_mk continuous_puncturedNorm _)

theorem continuous_collarFilling : Continuous collarFilling :=
  Continuous.prodMk (Continuous.subtype_mk continuous_puncturedDirection _)
    (Continuous.subtype_mk (continuous_const.mul continuous_puncturedNorm |>.sub
      continuous_const) _)

theorem injective_collarPolarCoordinates : Function.Injective collarPolarCoordinates := by
  intro x y h
  have hdir : (‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace) =
      (‖(y.1 : ThreeSpace)‖)⁻¹ • (y.1 : ThreeSpace) := by
    have h1 := congrArg (fun z : Sphere 2 × Icc (0 : ℝ) 1 => (z.1 : ThreeSpace)) h
    simpa only [collarPolarCoordinates, puncturedSpherePoint] using h1
  have hnorm : ‖(x.1 : ThreeSpace)‖ = ‖(y.1 : ThreeSpace)‖ := by
    have h2 := congrArg (fun z : Sphere 2 × Icc (0 : ℝ) 1 => (z.2 : ℝ)) h
    simpa only [collarPolarCoordinates] using h2
  have hval : (x.1 : ThreeSpace) = (y.1 : ThreeSpace) := by
    calc (x.1 : ThreeSpace)
        = ‖(x.1 : ThreeSpace)‖ • ((‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace)) :=
          (smul_inv_norm_punctured x).symm
      _ = ‖(y.1 : ThreeSpace)‖ •
          ((‖(y.1 : ThreeSpace)‖)⁻¹ • (y.1 : ThreeSpace)) := by
          rw [hdir, hnorm]
      _ = (y.1 : ThreeSpace) := smul_inv_norm_punctured y
  exact Subtype.ext (Subtype.ext hval)

theorem injective_collarFilling : Function.Injective collarFilling := by
  intro x y h
  have hdir : (‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace) =
      (‖(y.1 : ThreeSpace)‖)⁻¹ • (y.1 : ThreeSpace) := by
    have h1 := congrArg (fun z : TubeDomain => (z.1 : ThreeSpace)) h
    simpa only [collarFilling, puncturedSpherePoint] using h1
  have hnorm : ‖(x.1 : ThreeSpace)‖ = ‖(y.1 : ThreeSpace)‖ := by
    have h2 := congrArg (fun z : TubeDomain => (z.2 : ℝ)) h
    simp only [collarFilling_snd] at h2
    linarith
  have hval : (x.1 : ThreeSpace) = (y.1 : ThreeSpace) := by
    calc (x.1 : ThreeSpace)
        = ‖(x.1 : ThreeSpace)‖ • ((‖(x.1 : ThreeSpace)‖)⁻¹ • (x.1 : ThreeSpace)) :=
          (smul_inv_norm_punctured x).symm
      _ = ‖(y.1 : ThreeSpace)‖ •
          ((‖(y.1 : ThreeSpace)‖)⁻¹ • (y.1 : ThreeSpace)) := by
          rw [hdir, hnorm]
      _ = (y.1 : ThreeSpace) := smul_inv_norm_punctured y
  exact Subtype.ext (Subtype.ext hval)

theorem range_collarPolarCoordinates :
    range collarPolarCoordinates = {z : Sphere 2 × Icc (0 : ℝ) 1 | 0 < (z.2 : ℝ)} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [collarPolarCoordinates]
    exact norm_pos_iff.mpr x.2
  · intro hz
    set r : ℝ := (z.2 : ℝ) with hr
    have hrpos : 0 < r := hz
    have hrle : r ≤ 1 := by rw [hr]; exact z.2.2.2
    have hnorm : ‖r • (z.1 : ThreeSpace)‖ = r := by
      rw [norm_smul, Real.norm_of_nonneg hrpos.le, norm_sphere_eq_one z.1, mul_one]
    have hv0 : r • (z.1 : ThreeSpace) ≠ 0 := by
      rw [← norm_ne_zero_iff, hnorm]
      exact hrpos.ne'
    refine ⟨puncturedOf (r • (z.1 : ThreeSpace)) (by rw [hnorm]; exact hrle) hv0, ?_⟩
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      rw [show (collarPolarCoordinates (puncturedOf (r • (z.1 : ThreeSpace))
          (by rw [hnorm]; exact hrle) hv0)).1 =
          puncturedSpherePoint (puncturedOf (r • (z.1 : ThreeSpace))
            (by rw [hnorm]; exact hrle) hv0) from rfl]
      rw [coe_puncturedSpherePoint]
      have hcoe : ((puncturedOf (r • (z.1 : ThreeSpace))
          (by rw [hnorm]; exact hrle) hv0).1 : ThreeSpace) = r • (z.1 : ThreeSpace) := rfl
      rw [hcoe, hnorm, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    · refine Subtype.ext ?_
      rw [coe_collarPolarCoordinates_snd]
      have hcoe : ((puncturedOf (r • (z.1 : ThreeSpace))
          (by rw [hnorm]; exact hrle) hv0).1 : ThreeSpace) = r • (z.1 : ThreeSpace) := rfl
      rw [hcoe, hnorm, hr]

theorem range_collarFilling :
    range collarFilling = {z : TubeDomain | (z.2 : ℝ) ∈ Ioc (-2 : ℝ) 2} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have h0 : 0 < ‖(x.1 : ThreeSpace)‖ := norm_pos_iff.mpr x.2
    have h1 : ‖(x.1 : ThreeSpace)‖ ≤ 1 := x.1.2
    change ((collarFilling x).2 : ℝ) ∈ Ioc (-2 : ℝ) 2
    rw [collarFilling_snd]
    constructor <;> linarith
  · intro hz
    obtain ⟨hzlo, hzhi⟩ := hz
    set r : ℝ := ((z.2 : ℝ) + 2) / 4 with hr
    have hrpos : 0 < r := by rw [hr]; linarith
    have hrle : r ≤ 1 := by rw [hr]; linarith
    have hnorm : ‖r • (z.1 : ThreeSpace)‖ = r := by
      rw [norm_smul, Real.norm_of_nonneg hrpos.le, norm_sphere_eq_one z.1, mul_one]
    have hv0 : r • (z.1 : ThreeSpace) ≠ 0 := by
      rw [← norm_ne_zero_iff, hnorm]
      exact hrpos.ne'
    refine ⟨puncturedOf (r • (z.1 : ThreeSpace)) (by rw [hnorm]; exact hrle) hv0, ?_⟩
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      rw [collarFilling_fst]
      have hcoe : ((puncturedOf (r • (z.1 : ThreeSpace))
          (by rw [hnorm]; exact hrle) hv0).1 : ThreeSpace) = r • (z.1 : ThreeSpace) := rfl
      rw [hcoe, hnorm, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    · refine Subtype.ext ?_
      rw [collarFilling_snd]
      have hcoe : ((puncturedOf (r • (z.1 : ThreeSpace))
          (by rw [hnorm]; exact hrle) hv0).1 : ThreeSpace) = r • (z.1 : ThreeSpace) := rfl
      rw [hcoe, hnorm, hr]
      ring

theorem innerEnd_not_mem_range_collarFilling (u : Sphere 2) :
    (u, (⟨-2, by norm_num⟩ : Icc (-2 : ℝ) 2)) ∉ range collarFilling := by
  rw [range_collarFilling]
  exact fun h => absurd h.1 (by norm_num)

def collarFillingModel : Sphere 2 × Icc (0 : ℝ) 1 → TubeDomain :=
  ⇑((Diffeomorph.refl (𝓡 2) (Sphere 2) ∞).prodCongr
    (DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph (-2) 2))

theorem collarFillingModel_apply (z : Sphere 2 × Icc (0 : ℝ) 1) :
    collarFillingModel z = (z.1, collarHeight z.2) := by
  rw [collarFillingModel, Diffeomorph.coe_prodCongr, Prod.map]
  refine Prod.ext rfl (Subtype.ext ?_)
  rw [collarHeight, DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph_apply]
  ring

theorem isSmoothEmbedding_collarFillingModel :
    IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
      collarFillingModel := by
  have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    (I := (𝓡 2).prod (𝓡∂ 1)) (J := (𝓡 2).prod (𝓡∂ 1))
    (id : Sphere 2 × Icc (0 : ℝ) 1 → Sphere 2 × Icc (0 : ℝ) 1)
    (IsSmoothEmbedding.id : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1))
      ((𝓡 2).prod (𝓡∂ 1)) ∞
        (id : Sphere 2 × Icc (0 : ℝ) 1 → Sphere 2 × Icc (0 : ℝ) 1))
    ((Diffeomorph.refl (𝓡 2) (Sphere 2) ∞).prodCongr
      (DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph (-2) 2))
  simpa [collarFillingModel, Function.comp_def] using h

private def collarModelPunctured : TopologicalSpace.Opens (Sphere 2 × Icc (0 : ℝ) 1) :=
  ⟨{z : Sphere 2 × Icc (0 : ℝ) 1 | 0 < (z.2 : ℝ)},
    isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)⟩

theorem isSmoothEmbedding_collarFillingModel_restrictOpen :
    IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (collarFillingModel ∘ (Subtype.val : ↥collarModelPunctured →
        Sphere 2 × Icc (0 : ℝ) 1)) := by
  have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    (I := (𝓡 2).prod (𝓡∂ 1)) (J := (𝓡 2).prod (𝓡∂ 1))
    (Subtype.val : ↥collarModelPunctured → Sphere 2 × Icc (0 : ℝ) 1)
    (IsSmoothEmbedding.of_opens collarModelPunctured)
    ((Diffeomorph.refl (𝓡 2) (Sphere 2) ∞).prodCongr
      (DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph (-2) 2))
  simpa [collarFillingModel, Function.comp_def] using h

theorem range_collarFillingModel : range collarFillingModel = univ := by
  ext z
  refine ⟨fun _ => mem_univ z, fun _ => ?_⟩
  obtain ⟨h0, h1⟩ := z.2.2
  refine ⟨(z.1, ⟨((z.2 : ℝ) + 2) / 4, by constructor <;> linarith⟩), ?_⟩
  rw [collarFillingModel_apply]
  refine Prod.ext rfl (Subtype.ext ?_)
  rw [collarHeight]
  ring

theorem collarFilling_eq_collarFillingModel_comp :
    collarFilling = collarFillingModel ∘ collarPolarCoordinates := by
  funext x
  rw [Function.comp_apply, collarFillingModel_apply, collarFilling, collarPolarCoordinates,
    puncturedSpherePoint, puncturedHeight, collarHeight]

private def sphereToPunctured (z : Sphere 2) : PuncturedClosedCell :=
  ⟨DifferentialGeometry.Topology.sphereToClosedCell z, by
    intro h
    have h1 : (z : ThreeSpace) = 0 := h
    have h2 : ‖(z : ThreeSpace)‖ = 1 := norm_sphere_eq_one z
    rw [h1, norm_zero] at h2
    exact one_ne_zero h2.symm⟩

theorem collarFilling_sphereToClosedCell (z : Sphere 2) :
    collarFilling (sphereToPunctured z) = (z, ⟨2, by norm_num⟩) := by
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    rw [collarFilling_fst]
    have hcoe : ((sphereToPunctured z).1 : ThreeSpace) = (z : ThreeSpace) := rfl
    rw [hcoe, norm_sphere_eq_one z, inv_one, one_smul]
  · refine Subtype.ext ?_
    rw [collarFilling_snd]
    have hcoe : ((sphereToPunctured z).1 : ThreeSpace) = (z : ThreeSpace) := rfl
    rw [hcoe, norm_sphere_eq_one z]
    norm_num

theorem range_collarFilling_sphereToClosedCell :
    range (fun z : Sphere 2 => collarFilling (sphereToPunctured z)) =
      {z : TubeDomain | (z.2 : ℝ) = 2} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change ((collarFilling (sphereToPunctured w)).2 : ℝ) = 2
    rw [collarFilling_sphereToClosedCell]
  · intro hz
    refine ⟨z.1, ?_⟩
    change collarFilling (sphereToPunctured z.1) = z
    rw [collarFilling_sphereToClosedCell]
    exact Prod.ext rfl (Subtype.ext hz.symm)

private def collarSpherePoint (u : ThreeSpace) (hu : ‖u‖ = 1) : Sphere 2 :=
  ⟨u, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hu⟩

private def rayBase : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩

private def rayParam (n : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨1 / (n + 1), by
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · positivity
    · rw [div_le_one h1]
      linarith⟩

private theorem rayParam_pos (n : ℕ) : 0 < (rayParam n : ℝ) := by
  rw [show (rayParam n : ℝ) = 1 / (n + 1) from rfl]
  positivity

private theorem tendsto_rayParam : Tendsto rayParam atTop (𝓝 rayBase) := by
  rw [tendsto_subtype_rng]
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [rayParam, rayBase] using h

private def rayPoint (u : ThreeSpace) (hu : ‖u‖ = 1) (n : ℕ) :
    DifferentialGeometry.Topology.ClosedCell 3 :=
  ⟨(rayParam n : ℝ) • u, by
    rw [norm_smul, Real.norm_of_nonneg (rayParam n).2.1, hu, mul_one]
    exact (rayParam n).2.2⟩

private theorem norm_rayPoint (u : ThreeSpace) (hu : ‖u‖ = 1) (n : ℕ) :
    ‖((rayPoint u hu n : DifferentialGeometry.Topology.ClosedCell 3) : ThreeSpace)‖ =
      (rayParam n : ℝ) := by
  rw [show ((rayPoint u hu n : DifferentialGeometry.Topology.ClosedCell 3) : ThreeSpace) =
      (rayParam n : ℝ) • u from rfl,
    norm_smul, Real.norm_of_nonneg (rayParam n).2.1, hu, mul_one]

private def rayPunctured (u : ThreeSpace) (hu : ‖u‖ = 1) (n : ℕ) : PuncturedClosedCell :=
  puncturedOf ((rayParam n : ℝ) • u)
    (by
      rw [norm_smul, Real.norm_of_nonneg (rayParam n).2.1, hu, mul_one]
      exact (rayParam n).2.2)
    (by
      rw [← norm_ne_zero_iff, norm_smul, Real.norm_of_nonneg (rayParam n).2.1, hu, mul_one]
      exact (rayParam_pos n).ne')

private theorem tendsto_rayPoint (u : ThreeSpace) (hu : ‖u‖ = 1) :
    Tendsto (rayPoint u hu) atTop (𝓝 (DifferentialGeometry.Topology.closedCellCenter 3)) := by
  rw [tendsto_subtype_rng]
  have h : Tendsto (fun n : ℕ => (rayParam n : ℝ)) atTop (𝓝 0) :=
    (tendsto_subtype_rng (f := rayParam)).mp tendsto_rayParam
  rw [show (DifferentialGeometry.Topology.closedCellCenter 3 : ThreeSpace) = 0 from rfl]
  simpa [rayPoint] using h.smul_const u

private theorem collarFilling_rayPunctured (u : ThreeSpace) (hu : ‖u‖ = 1) (n : ℕ) :
    collarFilling (rayPunctured u hu n) =
      (collarSpherePoint u hu, collarHeight (rayParam n)) := by
  have hnorm : ‖(rayParam n : ℝ) • u‖ = (rayParam n : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (rayParam n).2.1, hu, mul_one]
  have hcoe : ((rayPunctured u hu n).1 : ThreeSpace) = (rayParam n : ℝ) • u := rfl
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    rw [collarFilling_fst, hcoe, hnorm, smul_smul, inv_mul_cancel₀ (rayParam_pos n).ne', one_smul]
    rfl
  · refine Subtype.ext ?_
    rw [collarFilling_snd, hcoe, hnorm, collarHeight]

theorem not_continuous_extension_collarFilling
    (F : DifferentialGeometry.Topology.ClosedCell 3 → TubeDomain) (hF : Continuous F)
    (hagree : ∀ x : PuncturedClosedCell, F x.1 = collarFilling x) : False := by
  have hkey : ∀ u : Sphere 2,
      F (DifferentialGeometry.Topology.closedCellCenter 3) = (u, collarHeight rayBase) := by
    intro u
    have hu : ‖(u : ThreeSpace)‖ = 1 := norm_sphere_eq_one u
    have hray : Tendsto (fun n : ℕ => rayPoint (u : ThreeSpace) hu n) atTop
        (𝓝 (DifferentialGeometry.Topology.closedCellCenter 3)) := tendsto_rayPoint _ hu
    have hlimF : Tendsto (fun n : ℕ => F (rayPoint (u : ThreeSpace) hu n)) atTop
        (𝓝 (F (DifferentialGeometry.Topology.closedCellCenter 3))) :=
      hF.continuousAt.tendsto.comp hray
    have hcont : Continuous fun r : Icc (0 : ℝ) 1 =>
        (collarSpherePoint (u : ThreeSpace) hu, collarHeight r) :=
      Continuous.prodMk continuous_const (Continuous.subtype_mk (by fun_prop) _)
    have hlim : Tendsto (fun n : ℕ => collarFilling (rayPunctured (u : ThreeSpace) hu n))
        atTop (𝓝 (collarSpherePoint (u : ThreeSpace) hu, collarHeight rayBase)) :=
      Filter.Tendsto.congr' (Eventually.of_forall fun n =>
          (collarFilling_rayPunctured (u : ThreeSpace) hu n).symm)
        ((hcont.continuousAt (x := rayBase)).tendsto.comp tendsto_rayParam)
    have hlimF' : Tendsto (fun n : ℕ => collarFilling (rayPunctured (u : ThreeSpace) hu n))
        atTop (𝓝 (F (DifferentialGeometry.Topology.closedCellCenter 3))) :=
      Filter.Tendsto.congr' (Eventually.of_forall fun n =>
        hagree (rayPunctured (u : ThreeSpace) hu n)) hlimF
    have huniq := tendsto_nhds_unique hlimF' hlim
    rw [show collarSpherePoint (u : ThreeSpace) hu = u from Subtype.ext rfl] at huniq
    exact huniq
  have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∈
      Metric.sphere (0 : ThreeSpace) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num
  have hmem' : (-(EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) ∈
      Metric.sphere (0 : ThreeSpace) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg, PiLp.norm_single]
    norm_num
  have hne : (⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), hmem⟩ : Sphere 2) ≠
      ⟨-(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)), hmem'⟩ := by
    intro h
    have hv := congrArg (fun z : Sphere 2 => (z : ThreeSpace)) h
    have h0 := congrArg (fun v : ThreeSpace => v 0) hv
    simp only [PiLp.single_eq_same] at h0
    norm_num at h0
  have hEq := (hkey ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), hmem⟩).symm.trans
    (hkey ⟨-(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)), hmem'⟩)
  exact hne (Prod.ext_iff.mp hEq).1

def ClosedCellBoundaryBijectionFree : Prop :=
  ¬ ∃ φ : DifferentialGeometry.Topology.ClosedCell 3 → Sphere 2,
      Continuous φ ∧ Function.Bijective (φ ∘ DifferentialGeometry.Topology.sphereToClosedCell)

theorem exists_boundaryBijection_of_boundarySliceCorrespondence
    (e : DifferentialGeometry.Topology.ClosedCell 3 → TubeDomain) (he : Continuous e)
    {b : Icc (-2 : ℝ) 2}
    (hbd : ∀ z : Sphere 2, e (DifferentialGeometry.Topology.sphereToClosedCell z) = (z, b)) :
    ∃ φ : DifferentialGeometry.Topology.ClosedCell 3 → Sphere 2,
      Continuous φ ∧
        Function.Bijective (φ ∘ DifferentialGeometry.Topology.sphereToClosedCell) := by
  refine ⟨fun x => (e x).1, continuous_fst.comp he, ?_, ?_⟩
  · intro z z' h
    simp only [Function.comp_apply] at h
    rw [hbd z, hbd z'] at h
    exact h
  · intro w
    exact ⟨w, by simp only [Function.comp_apply, hbd w]⟩

theorem not_exists_smoothEmbedding_of_boundarySliceCorrespondence
    (h : ClosedCellBoundaryBijectionFree) :
    ¬ ∃ (e : DifferentialGeometry.Topology.ClosedCell 3 → TubeDomain) (b : Icc (-2 : ℝ) 2),
        IsSmoothEmbedding (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞ e ∧
          ∀ z : Sphere 2, e (DifferentialGeometry.Topology.sphereToClosedCell z) = (z, b) := by
  rintro ⟨e, b, he, hbd⟩
  exact h (exists_boundaryBijection_of_boundarySliceCorrespondence e he.contMDiff.continuous hbd)

theorem nonempty_markedBall_of_collarFillingEmbedding
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (T : DifferentialGeometry.Topology.SphericalTubeSystem M) (a : T.Index)
    (e : DifferentialGeometry.Topology.ClosedCell 3 → TubeDomain)
    (he : IsSmoothEmbedding (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞ e) :
    Nonempty (DifferentialGeometry.Topology.MarkedBall M) :=
  ⟨DifferentialGeometry.Topology.MarkedBall.ofBallEmbedding
    (fun x => T.tube a (e x))
    (IsSmoothEmbedding.comp_of_smoothBoundary (T.smooth a) he)⟩

theorem isSmoothEmbedding_id_collarModel :
    IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (id : TubeDomain → TubeDomain) :=
  IsSmoothEmbedding.id

theorem range_collarFilling_ne_univ : range collarFilling ≠ univ := by
  intro h
  have hmem := innerEnd_not_mem_range_collarFilling
    (collarSpherePoint (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (by
      rw [PiLp.norm_single]; norm_num))
  rw [h] at hmem
  exact hmem (mem_univ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
