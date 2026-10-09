import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.TangentCone.Real
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskDivergence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCoordinates
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskTensionTrace
import DifferentialGeometry.Geometry.Measure.Area.Positivity
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationGerm
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.HalfSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.HalfSpaceContinuousBoundary

set_option autoImplicit false

noncomputable section

open Set Filter Bundle _root_.Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Topology ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry.ImmersedDiskDivergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def gramA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) : ℝ :=
  g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)

def gramB (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) : ℝ :=
  g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I)

def gramC (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) : ℝ :=
  g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)

/-- The area-weighted trace in the original, possibly nonconformal, frame. -/
def immersedSectionDivergence (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)) (z : ℂ) : ℝ :=
  (gramC g U z * g.inner (U z)
      (sourceSectionCovariantDerivative g U W z 1) (diskMapPartial U z 1) +
    gramA g U z * g.inner (U z)
      (sourceSectionCovariantDerivative g U W z Complex.I) (diskMapPartial U z Complex.I) -
    gramB g U z * (g.inner (U z)
      (sourceSectionCovariantDerivative g U W z 1) (diskMapPartial U z Complex.I) +
      g.inner (U z) (sourceSectionCovariantDerivative g U W z Complex.I)
        (diskMapPartial U z 1))) / riemannianAreaDensity g U z

def fluxOne (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)) (z : ℂ) : ℝ :=
  gramC g U z / riemannianAreaDensity g U z *
      g.inner (U z) (W z) (diskMapPartial U z 1) -
    gramB g U z / riemannianAreaDensity g U z *
      g.inner (U z) (W z) (diskMapPartial U z Complex.I)

def fluxI (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)) (z : ℂ) : ℝ :=
  gramA g U z / riemannianAreaDensity g U z *
      g.inner (U z) (W z) (diskMapPartial U z Complex.I) -
    gramB g U z / riemannianAreaDensity g U z *
      g.inner (U z) (W z) (diskMapPartial U z 1)

omit [FiniteDimensional ℝ E] in
private theorem smooth_gram (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContDiffOn ℝ ∞ (gramA g U) s ∧ ContDiffOn ℝ ∞ (gramB g U) s ∧
      ContDiffOn ℝ ∞ (gramC g U) s := by
  have hp := contMDiffOn_source_partial hs hU (m := ∞) (by simp)
  exact ⟨contDiffOn_sourceSectionPairing g hU (hp 1) (hp 1),
    contDiffOn_sourceSectionPairing g hU (hp 1) (hp Complex.I),
    contDiffOn_sourceSectionPairing g hU (hp Complex.I) (hp Complex.I)⟩

omit [FiniteDimensional ℝ E] in
private theorem smooth_density (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hi : ∀ z ∈ s, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ContDiffOn ℝ ∞ (riemannianAreaDensity g U) s := by
  obtain ⟨hA, hB, hC⟩ := smooth_gram g hs hU
  exact ((hA.mul hC).sub (hB.pow 2)).sqrt (fun z hz =>
    ne_of_gt (Real.sqrt_pos.mp (riemannianAreaDensity_pos_of_injective_mfderiv g (hi z hz))))

private theorem covariantPartial_add_right
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v a b : ℂ) :
    diskMapCovariantPartial g U z v (a + b) =
      diskMapCovariantPartial g U z v a + diskMapCovariantPartial g U z v b := by
  let line : ℝ → ℂ := fun t => z + t • v
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hlz : line 0 ∈ s := by simpa only [line, zero_smul, add_zero] using hz
  have hsec (w : ℂ) :=
    ((contMDiffOn_source_partial hs hU (m := ∞) (by simp) w _ hlz).contMDiffAt
      (hs.mem_nhds hlz)).comp 0 hl.contMDiff.contMDiffAt
  have hd (w : ℂ) : DifferentiableAt ℝ
      (chartRepAt (U ∘ line) (fun t => diskMapPartial U (line t) w) 0) 0 :=
    (contDiffAt_chartRepAt_of_section (hsec w)).differentiableAt (by simp)
  unfold diskMapCovariantPartial
  have heq : (fun t : ℝ => diskMapPartial (E := E) U (z + t • v) (a + b)) =
      (fun t => diskMapPartial U (z + t • v) a + diskMapPartial U (z + t • v) b) := by
    funext t
    exact map_add (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z + t • v)) a b
  rw [heq]
  exact covDerivAlong_add g (U ∘ line) _ _ 0 (hd a) (hd b)

private theorem inner_secondFundamentalForm_eq_covariantPartial
    (N : TopologicalSpace.Opens ℂ) (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (z : N) (W : TangentSpace 𝓘(ℝ, E) (U z))
    (hW : ∀ a : ℂ, g.inner (U z) W (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z a) = 0)
    (v w : ℂ) :
    g.inner (U z) W (secondFundamentalFormAmbientAt gN g (fun q : N => U q) z v w) =
      g.inner (U z) W (diskMapCovariantPartial g U z v w) := by
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hadd := covariantPartial_add_right g N.isOpen hUon z.property
  have hsym := diskMapCovariantPartial_symm g N.isOpen hUon z.property
  have hII := secondFundamentalFormAmbientAt_symmetric gN g
    (hU.contMDiffAt (x := z) |>.of_le (by simp))
  have hd := inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial N gN g U hU z W hW
  have hsum := hd (v + w)
  rw [hadd, hsym (v + w) v, hsym (v + w) w,
    hadd, hadd, hsym w v] at hsum
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  let H : ℂ → ℂ → E := diskMapCovariantPartial g U z
  have hQ : Q w v = Q v w := hII w v
  have hdv : G W (Q v v) = G W (H v v) := hd v
  have hdw : G W (Q w w) = G W (H w w) := hd w
  change G W (Q (v + w) (v + w)) =
    G W (H v v + H v w + (H v w + H w w)) at hsum
  simp only [map_add, _root_.add_apply, hQ, hdv, hdw] at hsum
  change G W (Q v w) = G W (H v w)
  linarith only [hsum]

private theorem scalar_normal_cancellation
    (A B C J X Y Z T P Q : ℝ) (hJ : J ≠ 0) (hJsq : J ^ 2 = A * C - B ^ 2) :
    let Jx := (C * X + A * T - B * (Y + Z)) / J
    let Jy := (C * Z + A * Q - B * (T + P)) / J
    let L := ((T - P) * J - C * Jx + B * Jy) / J ^ 2
    let R := ((Z - Y) * J - A * Jy + B * Jx) / J ^ 2
    (C * X + A * P - 2 * B * Z) / J + A * L + B * R = 0 ∧
      (C * Y + A * Q - 2 * B * T) / J + B * L + C * R = 0 := by
  dsimp only
  constructor
  · calc
      _ = (C * X + A * T - B * (Y + Z)) *
          (J ^ 2 - (A * C - B ^ 2)) / J ^ 3 := by field_simp [hJ]; ring
      _ = 0 := by rw [hJsq]; ring
  · calc
      _ = (C * Z + A * Q - B * (T + P)) *
          (J ^ 2 - (A * C - B ^ 2)) / J ^ 3 := by field_simp [hJ]; ring
      _ = 0 := by rw [hJsq]; ring

def correctionOne (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) : ℝ :=
  fderiv ℝ (fun q => gramC g U q / riemannianAreaDensity g U q) z 1 -
    fderiv ℝ (fun q => gramB g U q / riemannianAreaDensity g U q) z Complex.I

def correctionI (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) : ℝ :=
  fderiv ℝ (fun q => gramA g U q / riemannianAreaDensity g U q) z Complex.I -
    fderiv ℝ (fun q => gramB g U q / riemannianAreaDensity g U q) z 1

def meanDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) :
    TangentSpace 𝓘(ℝ, E) (U z) :=
  (gramC g U z / riemannianAreaDensity g U z) • diskMapCovariantPartial g U z 1 1 +
    (gramA g U z / riemannianAreaDensity g U z) •
      diskMapCovariantPartial g U z Complex.I Complex.I -
    (2 * gramB g U z / riemannianAreaDensity g U z) •
      diskMapCovariantPartial g U z 1 Complex.I +
    correctionOne g U z • diskMapPartial U z 1 +
    correctionI g U z • diskMapPartial U z Complex.I

private theorem directional_div {f h : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (hh0 : h z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun q => f q / h q) z v =
      (fderiv ℝ f z v * h z - f z * fderiv ℝ h z v) / (h z) ^ 2 := by
  let line : ℝ → ℂ := fun t => z + t • v
  have hl : HasDerivAt line v 0 := by
    simpa only [line, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hl0 : z = line 0 := by simp [line]
  have hd := (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl hl0).div
    (hh.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl hl0) (by simpa only [Function.comp_apply, ← hl0] using hh0)
  have hquot : DifferentiableAt ℝ (fun q => f q / h q) z := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      hf.fun_mul ((differentiableAt_inv hh0).comp z hh)
  have hd' := hquot.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl hl0
  simpa only [Function.comp_apply, ← hl0] using hd'.unique hd

omit [FiniteDimensional ℝ E] in
private theorem directional_density (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s)
    (hi : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) (v : ℂ) :
    fderiv ℝ (riemannianAreaDensity g U) z v =
      (gramC g U z * fderiv ℝ (gramA g U) z v +
        gramA g U z * fderiv ℝ (gramC g U) z v -
        2 * gramB g U z * fderiv ℝ (gramB g U) z v) /
          (2 * riemannianAreaDensity g U z) := by
  obtain ⟨hA, hB, hC⟩ := smooth_gram g hs hU
  have dA := ((hA z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have dB := ((hB z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have dC := ((hC z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have hd := ((dA.hasFDerivAt.mul dC.hasFDerivAt).sub (dB.hasFDerivAt.pow 2)).sqrt
    (ne_of_gt (Real.sqrt_pos.mp (riemannianAreaDensity_pos_of_injective_mfderiv g hi)))
  have heq := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hd.fderiv
  change fderiv ℝ (riemannianAreaDensity g U) z v = _ at heq
  rw [heq]
  simp only [_root_.smul_apply, _root_.add_apply,
    _root_.sub_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  change (1 / (2 * riemannianAreaDensity g U z)) *
    (gramA g U z * fderiv ℝ (gramC g U) z v +
      gramC g U z * fderiv ℝ (gramA g U) z v -
      (2 * gramB g U z) * fderiv ℝ (gramB g U) z v) = _
  ring

private theorem meanDensity_normal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hi : ∀ z ∈ s, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {z : ℂ} (hz : z ∈ s) :
    ∀ v : ℂ, g.inner (U z) (meanDensity g U z) (diskMapPartial U z v) = 0 := by
  let A := gramA g U z
  let B := gramB g U z
  let C := gramC g U z
  let J := riemannianAreaDensity g U z
  let P := diskMapPartial (E := E) U z
  let H := diskMapCovariantPartial g U z
  let X := g.inner (U z) (H 1 1) (P 1)
  let Y := g.inner (U z) (H 1 1) (P Complex.I)
  let Z := g.inner (U z) (H 1 Complex.I) (P 1)
  let T := g.inner (U z) (H 1 Complex.I) (P Complex.I)
  let V := g.inner (U z) (H Complex.I Complex.I) (P 1)
  let Q := g.inner (U z) (H Complex.I Complex.I) (P Complex.I)
  have hJ : J ≠ 0 := ne_of_gt (riemannianAreaDensity_pos_of_injective_mfderiv g (hi z hz))
  have hJsq : J ^ 2 = A * C - B ^ 2 := tangentTwoJacobian_sq g (P 1) (P Complex.I)
  obtain ⟨hA, hB, hC⟩ := smooth_gram g hs hU
  have hJsmooth := smooth_density g hs hU hi
  have dA := ((hA z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have dB := ((hB z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have dC := ((hC z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have dJ := ((hJsmooth z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have hsym := diskMapCovariantPartial_symm g hs hU hz Complex.I 1
  have hAx : fderiv ℝ (gramA g U) z 1 = 2 * X := by
    change fderiv ℝ (fun q => g.inner (U q)
      (diskMapPartial U q 1) (diskMapPartial U q 1)) z _ = _
    rw [fderiv_diskMapMetricPairing g hs hU hz, g.symm (U z) (P 1)]
    change X + X = 2 * X
    ring
  have hAy : fderiv ℝ (gramA g U) z Complex.I = 2 * Z := by
    change fderiv ℝ (fun q => g.inner (U q)
      (diskMapPartial U q 1) (diskMapPartial U q 1)) z _ = _
    rw [fderiv_diskMapMetricPairing g hs hU hz, hsym,
      g.symm (U z) (P 1)]
    change Z + Z = 2 * Z
    ring
  have hBx : fderiv ℝ (gramB g U) z 1 = Y + Z := by
    change fderiv ℝ (fun q => g.inner (U q)
      (diskMapPartial U q 1) (diskMapPartial U q Complex.I)) z _ = _
    rw [fderiv_diskMapMetricPairing g hs hU hz, g.symm (U z) (P 1)]
  have hBy : fderiv ℝ (gramB g U) z Complex.I = T + V := by
    change fderiv ℝ (fun q => g.inner (U q)
      (diskMapPartial U q 1) (diskMapPartial U q Complex.I)) z _ = _
    rw [fderiv_diskMapMetricPairing g hs hU hz, hsym,
      g.symm (U z) (P 1)]
  have hCx : fderiv ℝ (gramC g U) z 1 = 2 * T := by
    change fderiv ℝ (fun q => g.inner (U q)
      (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)) z _ = _
    rw [fderiv_diskMapMetricPairing g hs hU hz, g.symm (U z) (P Complex.I)]
    change T + T = 2 * T
    ring
  have hCy : fderiv ℝ (gramC g U) z Complex.I = 2 * Q := by
    change fderiv ℝ (fun q => g.inner (U q)
      (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)) z _ = _
    rw [fderiv_diskMapMetricPairing g hs hU hz, g.symm (U z) (P Complex.I)]
    change Q + Q = 2 * Q
    ring
  have hJx : fderiv ℝ (riemannianAreaDensity g U) z 1 =
      (C * X + A * T - B * (Y + Z)) / J := by
    rw [directional_density g hs hU hz (hi z hz), hAx, hBx, hCx]
    change (C * (2 * X) + A * (2 * T) - 2 * B * (Y + Z)) / (2 * J) = _
    ring
  have hJy : fderiv ℝ (riemannianAreaDensity g U) z Complex.I =
      (C * Z + A * Q - B * (T + V)) / J := by
    rw [directional_density g hs hU hz (hi z hz), hAy, hBy, hCy]
    change (C * (2 * Z) + A * (2 * Q) - 2 * B * (T + V)) / (2 * J) = _
    ring
  let Jx := (C * X + A * T - B * (Y + Z)) / J
  let Jy := (C * Z + A * Q - B * (T + V)) / J
  have hL : correctionOne g U z = ((T - V) * J - C * Jx + B * Jy) / J ^ 2 := by
    rw [correctionOne, directional_div dC dJ hJ, directional_div dB dJ hJ,
      hCx, hBy, hJx, hJy]
    change ((2 * T) * J - C * Jx) / J ^ 2 - ((T + V) * J - B * Jy) / J ^ 2 = _
    ring
  have hR : correctionI g U z = ((Z - Y) * J - A * Jy + B * Jx) / J ^ 2 := by
    rw [correctionI, directional_div dA dJ hJ, directional_div dB dJ hJ,
      hAy, hBx, hJx, hJy]
    change ((2 * Z) * J - A * Jy) / J ^ 2 - ((Y + Z) * J - B * Jx) / J ^ 2 = _
    ring
  have hcancel := scalar_normal_cancellation A B C J X Y Z T V Q hJ hJsq
  have h1 : g.inner (U z) (meanDensity g U z) (P 1) = 0 := by
    simp only [meanDensity, map_add, map_sub, map_smul, _root_.add_apply,
      _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
    rw [g.symm (U z) (P Complex.I) (P 1), hL, hR]
    change C / J * X + A / J * V - (2 * B / J) * Z +
      (((T - V) * J - C * Jx + B * Jy) / J ^ 2) * A +
      (((Z - Y) * J - A * Jy + B * Jx) / J ^ 2) * B = 0
    calc
      _ = (C * X + A * V - 2 * B * Z) / J +
          A * (((T - V) * J - C * Jx + B * Jy) / J ^ 2) +
          B * (((Z - Y) * J - A * Jy + B * Jx) / J ^ 2) := by ring
      _ = 0 := hcancel.1
  have hI : g.inner (U z) (meanDensity g U z) (P Complex.I) = 0 := by
    simp only [meanDensity, map_add, map_sub, map_smul, _root_.add_apply,
      _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
    rw [hL, hR]
    change C / J * Y + A / J * Q - (2 * B / J) * T +
      (((T - V) * J - C * Jx + B * Jy) / J ^ 2) * B +
      (((Z - Y) * J - A * Jy + B * Jx) / J ^ 2) * C = 0
    calc
      _ = (C * Y + A * Q - 2 * B * T) / J +
          B * (((T - V) * J - C * Jx + B * Jy) / J ^ 2) +
          C * (((Z - Y) * J - A * Jy + B * Jx) / J ^ 2) := by ring
      _ = 0 := hcancel.2
  intro v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  rw [hv]
  let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  have hd1 : G (meanDensity g U z) (D 1) = 0 := h1
  have hdI : G (meanDensity g U z) (D Complex.I) = 0 := hI
  change G (meanDensity g U z) (D (v.re • (1 : ℂ) + v.im • Complex.I)) = 0
  simp only [map_add, map_smul, smul_eq_mul, hd1, hdI, mul_zero, add_zero]

def inducedMeanTrace (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q)) (z : N) :
    TangentSpace 𝓘(ℝ, E) (U z) :=
  let gN := g.pullback (fun q : N => U q) hU hi
  let II := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  (gramA g U z * gramC g U z - gramB g U z ^ 2)⁻¹ •
    (gramC g U z • II (1 : ℂ) (1 : ℂ) + gramA g U z • II Complex.I Complex.I -
      (2 * gramB g U z) • II (1 : ℂ) Complex.I)

private theorem meanDensity_eq_zero_of_inducedMeanTrace_eq_zero
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (z : N) (hmean : inducedMeanTrace N g U hU hi z = 0) :
    meanDensity g U z = 0 := by
  let gN := g.pullback (fun q : N => U q) hU hi
  let II := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hion : ∀ q ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q) := by
    intro q hq
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) ⟨q, hq⟩ :
        ℂ →L[ℝ] E) = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
      DifferentialGeometry.mfderiv_restrict_open U N ⟨q, hq⟩
    exact (congrArg (fun L : ℂ →L[ℝ] E => Function.Injective L) hdf).mp (hi ⟨q, hq⟩)
  have hJ : 0 < riemannianAreaDensity g U z :=
    riemannianAreaDensity_pos_of_injective_mfderiv g (hion z z.property)
  have hdet : gramA g U z * gramC g U z - gramB g U z ^ 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mp hJ)
  have hS : gramC g U z • II (1 : ℂ) (1 : ℂ) + gramA g U z • II Complex.I Complex.I -
      (2 * gramB g U z) • II (1 : ℂ) Complex.I = 0 := by
    exact (smul_eq_zero.mp hmean).resolve_left (inv_ne_zero hdet)
  have hnormal := meanDensity_normal g N.isOpen hUon hion z.property
  have hpair := inner_secondFundamentalForm_eq_covariantPartial
    N gN g U hU z (meanDensity g U z) hnormal
  have hSinner := congrArg (g.inner (U z) (meanDensity g U z)) hS
  simp only [map_add, map_sub, map_smul, map_zero, smul_eq_mul] at hSinner
  have hzero : g.inner (U z) (meanDensity g U z) (meanDensity g U z) = 0 := by
    change g.inner (U z) (meanDensity g U z)
      ((gramC g U z / riemannianAreaDensity g U z) • diskMapCovariantPartial g U z 1 1 +
        (gramA g U z / riemannianAreaDensity g U z) •
          diskMapCovariantPartial g U z Complex.I Complex.I -
        (2 * gramB g U z / riemannianAreaDensity g U z) •
          diskMapCovariantPartial g U z 1 Complex.I +
        correctionOne g U z • diskMapPartial U z 1 +
        correctionI g U z • diskMapPartial U z Complex.I) = 0
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hnormal, mul_zero, add_zero]
    rw [← hpair 1 1, ← hpair Complex.I Complex.I, ← hpair 1 Complex.I]
    change gramC g U z / riemannianAreaDensity g U z *
        g.inner (U z) (meanDensity g U z) (II (1 : ℂ) (1 : ℂ)) +
      gramA g U z / riemannianAreaDensity g U z *
        g.inner (U z) (meanDensity g U z) (II Complex.I Complex.I) -
      (2 * gramB g U z / riemannianAreaDensity g U z) *
        g.inner (U z) (meanDensity g U z) (II (1 : ℂ) Complex.I) = 0
    calc
      _ = (gramC g U z * g.inner (U z) (meanDensity g U z) (II (1 : ℂ) (1 : ℂ)) +
          gramA g U z * g.inner (U z) (meanDensity g U z) (II Complex.I Complex.I) -
          2 * gramB g U z * g.inner (U z) (meanDensity g U z) (II (1 : ℂ) Complex.I)) /
            riemannianAreaDensity g U z := by ring
      _ = 0 := by rw [hSinner]; simp
  by_contra hn
  exact (ne_of_gt (g.pos (U z) (meanDensity g U z) hn)) hzero

omit [FiniteDimensional ℝ E] in
private theorem smooth_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hi : ∀ z ∈ s, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s) :
    ContDiffOn ℝ ∞ (fluxOne g U W) s ∧ ContDiffOn ℝ ∞ (fluxI g U W) s := by
  obtain ⟨hA, hB, hC⟩ := smooth_gram g hs hU
  have hJ := smooth_density g hs hU hi
  have hJ0 : ∀ z ∈ s, riemannianAreaDensity g U z ≠ 0 :=
    fun z hz => ne_of_gt (riemannianAreaDensity_pos_of_injective_mfderiv g (hi z hz))
  have hp := contDiffOn_sourceSectionPairing g hU hW
    (contMDiffOn_source_partial hs hU (by simp) 1)
  have hq := contDiffOn_sourceSectionPairing g hU hW
    (contMDiffOn_source_partial hs hU (by simp) Complex.I)
  exact ⟨((hC.div hJ hJ0).mul hp).sub ((hB.div hJ hJ0).mul hq),
    ((hA.div hJ hJ0).mul hq).sub ((hB.div hJ hJ0).mul hp)⟩

private theorem complexDivergence_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hi : ∀ z ∈ s, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s)
    {z : ℂ} (hz : z ∈ s) :
    complexDivergence (fluxOne g U W) (fluxI g U W) z =
      immersedSectionDivergence g U W z + g.inner (U z) (W z) (meanDensity g U z) := by
  obtain ⟨hA, hB, hC⟩ := smooth_gram g hs hU
  have hJ := smooth_density g hs hU hi
  have hJ0 : ∀ q ∈ s, riemannianAreaDensity g U q ≠ 0 :=
    fun q hq => ne_of_gt (riemannianAreaDensity_pos_of_injective_mfderiv g (hi q hq))
  have dA := (((hA.div hJ hJ0) z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have dB := (((hB.div hJ hJ0) z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have dC := (((hC.div hJ hJ0) z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have h1 := contMDiffOn_source_partial hs hU (m := ∞) (by simp) 1
  have hI := contMDiffOn_source_partial hs hU (m := ∞) (by simp) Complex.I
  have dp := (((contDiffOn_sourceSectionPairing g hU hW h1) z hz).contDiffAt
    (hs.mem_nhds hz)).differentiableAt (by simp)
  have dq := (((contDiffOn_sourceSectionPairing g hU hW hI) z hz).contDiffAt
    (hs.mem_nhds hz)).differentiableAt (by simp)
  unfold complexDivergence fluxOne fluxI
  erw [fderiv_fun_sub (dC.mul dp) (dB.mul dq), fderiv_fun_sub (dA.mul dq) (dB.mul dp),
    fderiv_fun_mul dC dp, fderiv_fun_mul dB dq,
    fderiv_fun_mul dA dq, fderiv_fun_mul dB dp]
  simp only [_root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  erw [fderiv_sourceSectionPairing g hs hU hW h1 hz 1,
    fderiv_sourceSectionPairing g hs hU hW hI hz 1,
    fderiv_sourceSectionPairing g hs hU hW hI hz Complex.I,
    fderiv_sourceSectionPairing g hs hU hW h1 hz Complex.I]
  change _ = immersedSectionDivergence g U W z + g.inner (U z) (W z)
    (meanDensity g U z)
  simp only [immersedSectionDivergence, meanDensity, correctionOne, correctionI,
    map_add, map_sub, map_smul, smul_eq_mul]
  have hsym := diskMapCovariantPartial_symm g hs hU hz Complex.I 1
  change sourceSectionCovariantDerivative g U
      (fun q => diskMapPartial U q 1) z Complex.I =
    sourceSectionCovariantDerivative g U
      (fun q => diskMapPartial U q Complex.I) z 1 at hsym
  simp only [diskMapCovariantPartial, sourceSectionCovariantDerivative, diskMapPartial] at hsym ⊢
  rw [hsym]
  simp only [Pi.div_def]
  simp only [div_eq_mul_inv]
  ring

/-- On the actual minimal immersion, the divergence of its inverse-Gram flux
equals the area-weighted ambient derivative trace. This identity is local and
does not impose boundary regularity or zero boundary flux. -/
theorem complexDivergence_flux_eq_immersedSectionDivergence_of_mean_zero
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) (N : Set ℂ))
    (z : N) (hmean : inducedMeanTrace N g U hU hi z = 0) :
    complexDivergence (fluxOne g U W) (fluxI g U W) z =
      immersedSectionDivergence g U W z := by
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hion : ∀ q ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q) := by
    intro q hq
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) ⟨q, hq⟩ :
        ℂ →L[ℝ] E) = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
      DifferentialGeometry.mfderiv_restrict_open U N ⟨q, hq⟩
    exact (congrArg (fun L : ℂ →L[ℝ] E => Function.Injective L) hdf).mp (hi ⟨q, hq⟩)
  rw [complexDivergence_flux g N.isOpen hUon hion hW z.property,
    meanDensity_eq_zero_of_inducedMeanTrace_eq_zero N g U hU hi z hmean,
    map_zero, add_zero]

private theorem integral_immersedSectionDivergence_of_meanDensity_zero
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hD : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) 1, meanDensity g U z = 0)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) (N : Set ℂ))
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1, W z = 0) :
    IntegrableOn (immersedSectionDivergence g U W) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, immersedSectionDivergence g U W z) = 0 := by
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hion : ∀ q ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q) := by
    intro q hq
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) ⟨q, hq⟩ :
        ℂ →L[ℝ] E) = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
      DifferentialGeometry.mfderiv_restrict_open U N ⟨q, hq⟩
    exact (congrArg (fun L : ℂ →L[ℝ] E => Function.Injective L) hdf).mp (hi ⟨q, hq⟩)
  obtain ⟨hF, hG⟩ := smooth_flux g N.isOpen hUon hion hW
  have heq : immersedSectionDivergence g U W =ᵐ[volume.restrict (Metric.closedBall 0 1)]
      complexDivergence (fluxOne g U W) (fluxI g U W) := by
    filter_upwards [ae_disk_interior] with z hz
    have hzN := hD (Metric.ball_subset_closedBall hz)
    rw [complexDivergence_flux g N.isOpen hUon hion hW hzN, hmean z hz,
      map_zero, add_zero]
  refine ⟨?_, ?_⟩
  · exact (((contDiffOn_complexDivergence N.isOpen hF hG).continuousOn.mono hD).integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).congr heq.symm
  · rw [integral_congr_ae heq,
      integral_complexDivergence_closedBall_of_open N.isOpen hF hG (by norm_num : (0 : ℝ) < 1) hD]
    have hb (θ : ℝ) : W (Complex.polarCoord.symm (1, θ)) = 0 := by
      apply hboundary
      simp [Complex.polarCoord_symm_apply]
    have hzero : (fun θ : ℝ => (1 : ℝ) *
        (fluxOne g U W (Complex.polarCoord.symm (1, θ)) * Real.cos θ +
          fluxI g U W (Complex.polarCoord.symm (1, θ)) * Real.sin θ)) = fun _ => 0 := by
      funext θ
      simp only [fluxOne, fluxI, hb θ, map_zero, _root_.zero_apply,
        mul_zero, sub_zero, zero_mul, add_zero]
    rw [hzero, intervalIntegral.integral_zero]

/-- Fixed boundary sections have zero integrated area-weighted divergence on a
minimal immersed disk, in its original parametrization.  The mean vector uses
the canonical pullback metric and the actual inverse Gram matrix. -/
theorem integral_immersedSectionDivergence_eq_zero
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hD : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hmean : ∀ z : N, (z : ℂ) ∈ Metric.ball 0 1 → inducedMeanTrace N g U hU hi z = 0)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) (N : Set ℂ))
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1, W z = 0) :
    IntegrableOn (immersedSectionDivergence g U W) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, immersedSectionDivergence g U W z) = 0 := by
  apply integral_immersedSectionDivergence_of_meanDensity_zero N g U hU hi hD _ hW hboundary
  intro z hz
  let p : N := ⟨z, hD (Metric.ball_subset_closedBall hz)⟩
  exact meanDensity_eq_zero_of_inducedMeanTrace_eq_zero N g U hU hi p (hmean p hz)

abbrev diskInterior : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The mean vector may be supplied on the canonical open disk itself.  The
larger neighborhood is used only to control the actual flux through the outer
boundary; no second-fundamental-form restriction identity is assumed. -/
theorem integral_immersedSectionDivergence_eq_zero_of_interior_mean
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hD : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hUD : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : diskInterior => U q))
    (hiD : ∀ q : diskInterior, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : diskInterior => U p) q))
    (hmean : ∀ z : diskInterior, inducedMeanTrace diskInterior g U hUD hiD z = 0)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) (N : Set ℂ))
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1, W z = 0) :
    IntegrableOn (immersedSectionDivergence g U W) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, immersedSectionDivergence g U W z) = 0 := by
  apply integral_immersedSectionDivergence_of_meanDensity_zero N g U hU hi hD _ hW hboundary
  intro z hz
  exact meanDensity_eq_zero_of_inducedMeanTrace_eq_zero diskInterior g U hUD hiD
    ⟨z, hz⟩ (hmean ⟨z, hz⟩)

/-- Actual covariant acceleration of the time tracks of the same variation. -/
def actualTimeAcceleration
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (F : ℝ × ℂ → M) (z : ℂ) :
    TangentSpace 𝓘(ℝ, E) (F (0, z)) :=
  covDerivAlong g (fun t => F (t, z))
    (fun t => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => F (r, z)) t (1 : ℝ)) 0

/-- Fixed time tracks at the boundary remove the actual acceleration term in
the second area variation, without conformality of the original disk. -/
theorem integral_actual_acceleration_eq_zero
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (F : ℝ × ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => F (0, q)))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => F (0, p)) q))
    (hD : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hmean : ∀ z : N, (z : ℂ) ∈ Metric.ball 0 1 →
      inducedMeanTrace N g (fun q => F (0, q)) hU hi z = 0)
    (hacc : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (F (0, z)) (actualTimeAcceleration g F z)) (N : Set ℂ))
    (hfix : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      (fun t => F (t, z)) =ᶠ[𝓝 (0 : ℝ)] fun _ => F (0, z)) :
    IntegrableOn (immersedSectionDivergence g (fun q => F (0, q))
      (actualTimeAcceleration g F)) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        immersedSectionDivergence g (fun q => F (0, q)) (actualTimeAcceleration g F) z) = 0 := by
  apply integral_immersedSectionDivergence_eq_zero N g (fun q => F (0, q)) hU hi hD hmean hacc
  intro z hz
  exact centralVariationAcceleration_eq_zero_of_eventually_constant g
    (fun t (_ : ℝ) => F (t, z)) 0 (F (0, z)) (hfix z hz)

/-- The original-parametrization acceleration cancellation consumes the mean
vector on the same canonical disk interior as the actual stationarity producer. -/
theorem integral_actual_acceleration_eq_zero_of_interior_mean
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (F : ℝ × ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => F (0, q)))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => F (0, p)) q))
    (hD : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hUD : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : diskInterior => F (0, q)))
    (hiD : ∀ q : diskInterior, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : diskInterior => F (0, p)) q))
    (hmean : ∀ z : diskInterior,
      inducedMeanTrace diskInterior g (fun q => F (0, q)) hUD hiD z = 0)
    (hacc : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (F (0, z)) (actualTimeAcceleration g F z)) (N : Set ℂ))
    (hfix : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      (fun t => F (t, z)) =ᶠ[𝓝 (0 : ℝ)] fun _ => F (0, z)) :
    IntegrableOn (immersedSectionDivergence g (fun q => F (0, q))
      (actualTimeAcceleration g F)) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        immersedSectionDivergence g (fun q => F (0, q)) (actualTimeAcceleration g F) z) = 0 := by
  apply integral_immersedSectionDivergence_eq_zero_of_interior_mean N g
    (fun q => F (0, q)) hU hi hD hUD hiD hmean hacc
  intro z hz
  exact centralVariationAcceleration_eq_zero_of_eventually_constant g
    (fun t (_ : ℝ) => F (t, z)) 0 (F (0, z)) (hfix z hz)

end DifferentialGeometry.Geometry.ImmersedDiskDivergence

namespace DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within

open Set Filter Bundle _root_.Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped _root_.Topology ContDiff _root_.Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def partialWithin (U : ℂ → M) (S : Set ℂ) (z v : ℂ) :
    TangentSpace 𝓘(ℝ, E) (U z) := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z v

def gramWithin (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (S : Set ℂ) (z v w : ℂ) : ℝ :=
  g.inner (U z) (partialWithin (E := E) U S z v) (partialWithin (E := E) U S z w)

def densityWithin (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (S : Set ℂ) (z : ℂ) : ℝ :=
  tangentTwoJacobian g (partialWithin (E := E) U S z 1) (partialWithin (E := E) U S z Complex.I)

def ambientPartialWithin (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (S : Set ℂ) (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (z v : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  (leviCivitaConnectionOfMetric g) Y (U z) (partialWithin (E := E) U S z v)

/-- The extension uses first derivatives of the sheet and the actual ambient
Levi-Civita derivative of the supplied field, not boundary second derivatives. -/
def ambientDivergenceWithin (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (S : Set ℂ) (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p) (z : ℂ) : ℝ :=
  (gramWithin g U S z Complex.I Complex.I * g.inner (U z)
      (ambientPartialWithin g U S Y z 1) (partialWithin (E := E) U S z 1) +
    gramWithin g U S z 1 1 * g.inner (U z)
      (ambientPartialWithin g U S Y z Complex.I) (partialWithin (E := E) U S z Complex.I) -
    gramWithin g U S z 1 Complex.I * (g.inner (U z)
      (ambientPartialWithin g U S Y z 1) (partialWithin (E := E) U S z Complex.I) +
      g.inner (U z) (ambientPartialWithin g U S Y z Complex.I)
        (partialWithin (E := E) U S z 1))) / densityWithin g U S z

def stressWithin (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (S : Set ℂ) (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (z : ℂ) : ℝ × ℝ :=
  (gramWithin g U S z Complex.I Complex.I / densityWithin g U S z *
      g.inner (U z) (Y (U z)) (partialWithin (E := E) U S z 1) -
    gramWithin g U S z 1 Complex.I / densityWithin g U S z *
      g.inner (U z) (Y (U z)) (partialWithin (E := E) U S z Complex.I),
   gramWithin g U S z 1 1 / densityWithin g U S z *
      g.inner (U z) (Y (U z)) (partialWithin (E := E) U S z Complex.I) -
    gramWithin g U S z 1 Complex.I / densityWithin g U S z *
      g.inner (U z) (Y (U z)) (partialWithin (E := E) U S z 1))

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem partialWithin_contMDiff_zero {U : ℂ → M} {S : Set ℂ}
    (hS : UniqueMDiffOn 𝓘(ℝ, ℂ) S)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U S) (v : ℂ) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 0
      (fun z => TotalSpace.mk' E (U z) (partialWithin (E := E) U S z v)) S := by
  have ht := hU.contMDiffOn_tangentMapWithin (m := 0) (by simp) hS
  have hv : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 0
      (fun z => (TotalSpace.mk' ℂ z v : TangentBundle 𝓘(ℝ, ℂ) ℂ)) := by
    intro z
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 0 (fun _ : ℂ => v) z)
  exact (ht.comp hv.contMDiffOn (fun z hz => hz)).congr (fun _ _ => rfl)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem pairing_contDiff_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {S : Set ℂ}
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 0 U S)
    {W Z : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 0
      (fun z => TotalSpace.mk' E (U z) (W z)) S)
    (hZ : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 0
      (fun z => TotalSpace.mk' E (U z) (Z z)) S) :
    ContDiffOn ℝ 0 (fun z => g.inner (U z) (W z) (Z z)) S := by
  intro z hz
  have h : ContMDiffWithinAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 0
      (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U q)
        (g.inner (U q) (W q) (Z q))) S z := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact (g.contMDiff.contMDiffAt.of_le (by simp)).comp_contMDiffWithinAt z (hU z hz)
    · exact hW z hz
    · exact hZ z hz
  exact (contMDiffWithinAt_totalSpace.mp h).2.contDiffWithinAt

omit [FiniteDimensional ℝ E] [T2Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem densityWithin_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {S : Set ℂ} {z : ℂ}
    (hi : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z)) :
    0 < densityWithin g U S z := by
  have hli : LinearIndependent ℝ ![(partialWithin (E := E) U S z 1), (partialWithin (E := E) U S z Complex.I)] := by
    convert Complex.basisOneI.linearIndependent.map'
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z).toLinearMap
        (LinearMap.ker_eq_bot.mpr hi) using 1
    ext i
    fin_cases i <;> simp [partialWithin, Complex.coe_basisOneI] <;> rfl
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  change 0 < twoJacobian (partialWithin (E := E) U S z 1) (partialWithin (E := E) U S z Complex.I)
  rw [twoJacobian_eq_sqrt_det_gram]
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hli).det_pos

omit [T2Space M] in
/-- Actual stress and actual first-order ambient divergence are continuous
on a one-sided C¹ immersed source. `UniqueMDiffOn` holds for the closed half-plane.
No extension of second derivatives or of the second fundamental form is used. -/
theorem continuousOn_stress_and_ambientDivergenceWithin
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) {S : Set ℂ}
    (hS : UniqueMDiffOn 𝓘(ℝ, ℂ) S)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U S)
    (hi : ∀ z ∈ S, Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z))
    (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p (Y p))) :
    ContinuousOn (stressWithin g U S Y) S ∧
      ContinuousOn (ambientDivergenceWithin g U S Y) S := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hU0 := hU.of_le (by simp : (0 : WithTop ℕ∞) ≤ 1)
  have hT := partialWithin_contMDiff_zero hS hU
  have hDY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p => (⟨p, (leviCivitaConnectionOfMetric g) Y p⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun p => TangentSpace 𝓘(ℝ, E) p →L[ℝ] TangentSpace 𝓘(ℝ, E) p))) := by
    rw [← contMDiffOn_univ]
    exact (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g
      isOpen_univ).contMDiff (by simpa using hY.contMDiffOn)
  have hN (v : ℂ) : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 0
      (fun z => TotalSpace.mk' E (U z) (ambientPartialWithin g U S Y z v)) S :=
    ((hDY.of_le (by simp)).comp_contMDiffOn hU0).clm_bundle_apply (hT v)
  have hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 0
      (fun z => TotalSpace.mk' E (U z) (Y (U z))) S :=
    (hY.of_le (by simp)).comp_contMDiffOn hU0
  have hG (v w : ℂ) : ContinuousOn (fun z => gramWithin g U S z v w) S :=
    (pairing_contDiff_zero g hU0 (hT v) (hT w)).continuousOn
  have hP (v : ℂ) : ContinuousOn (fun z => g.inner (U z) (Y (U z))
      (partialWithin (E := E) U S z v)) S :=
    (pairing_contDiff_zero g hU0 hW (hT v)).continuousOn
  have hQ (v w : ℂ) : ContinuousOn (fun z => g.inner (U z)
      (ambientPartialWithin g U S Y z v) (partialWithin (E := E) U S z w)) S :=
    (pairing_contDiff_zero g hU0 (hN v) (hT w)).continuousOn
  have hJ : ContinuousOn (densityWithin g U S) S :=
    (((hG 1 1).mul (hG Complex.I Complex.I)).sub ((hG 1 Complex.I).pow 2)).sqrt
  have hJ0 : ∀ z ∈ S, densityWithin g U S z ≠ 0 :=
    fun z hz => ne_of_gt (densityWithin_pos g (hi z hz))
  refine ⟨?_, ?_⟩
  · exact ((((hG Complex.I Complex.I).div hJ hJ0).mul (hP 1)).sub
      (((hG 1 Complex.I).div hJ hJ0).mul (hP Complex.I))).prodMk
      ((((hG 1 1).div hJ hJ0).mul (hP Complex.I)).sub
        (((hG 1 Complex.I).div hJ hJ0).mul (hP 1)))
  · exact ((((hG Complex.I Complex.I).mul (hQ 1 1)).add
      ((hG 1 1).mul (hQ Complex.I Complex.I))).sub
        ((hG 1 Complex.I).mul ((hQ 1 Complex.I).add (hQ Complex.I 1)))).div hJ hJ0

private theorem sourceSectionCovariantDerivative_ambient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z)
    (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p (Y p))) (v : ℂ) :
    sourceSectionCovariantDerivative g U (fun q => Y (U q)) z v =
      (leviCivitaConnectionOfMetric g) Y (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) := by
  let line : ℝ → ℂ := fun t => z + t • v
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t => U (line t)) 0 :=
    (show ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U (line 0) by simpa [line] using hU).comp 0
      (hl.contMDiff.contMDiffAt.of_le (by simp))
  have hX : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun p => TotalSpace.mk' E p (Y p)) (U (line 0)) :=
    hY.mdifferentiable (by simp) (U (line 0))
  have hvel : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => U (line t)) 0 (1 : ℝ) : E) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v :=
    source_mfderiv_line (I := 𝓘(ℝ, E)) (r := U)
      (hU.mdifferentiableAt (by simp)) v
  have hchain :
      (covDerivAlong (I := 𝓘(ℝ, E)) g (fun t => U (line t))
        (fun t => Y (U (line t))) 0 : E) =
      (leviCivitaConnectionOfMetric g) Y (U (line 0))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => U (line t)) 0 (1 : ℝ)) :=
    covDerivAlong_eq_leviCivita_of_eventuallyEq (I := 𝓘(ℝ, E))
      (X := Y) (V := fun t => Y (U (line t)))
      g (fun t => U (line t)) 0 hγ hX (Eventually.of_forall (fun _ => rfl))
  change (covDerivAlong (I := 𝓘(ℝ, E)) g (fun t => U (line t))
    (fun t => Y (U (line t))) 0 : E) = _
  rw [hchain, hvel]
  let A : M → E →L[ℝ] E := fun p => (leviCivitaConnectionOfMetric g) Y p
  change A (U (line 0)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) =
    A (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v)
  have hline0 : line 0 = z := by simp only [line, zero_smul, add_zero]
  rw [hline0]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The same within-defined stress is smooth on every actual smooth immersed
interior patch. This supplies the interior C¹ input to the seam-limit theorem. -/
theorem contDiffOn_stressWithin_of_smooth_interior
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) {S : Set ℂ} (hNS : (N : Set ℂ) ⊆ interior S)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p (Y p))) :
    ContDiffOn ℝ ∞ (stressWithin g U S Y) (N : Set ℂ) := by
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hion : ∀ q ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q) := by
    intro q hq
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) ⟨q, hq⟩ :
        ℂ →L[ℝ] E) = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
      DifferentialGeometry.mfderiv_restrict_open U N ⟨q, hq⟩
    exact (congrArg (fun L : ℂ →L[ℝ] E => Function.Injective L) hdf).mp (hi ⟨q, hq⟩)
  have hflux := DifferentialGeometry.Geometry.ImmersedDiskDivergence.smooth_flux g N.isOpen hUon hion
    (hY.comp_contMDiffOn hUon)
  refine (hflux.1.prodMk hflux.2).congr ?_
  intro q hq
  have hw (v : ℂ) : partialWithin (E := E) U S q v = diskMapPartial U q v := by
    exact congrArg (fun L : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U q) => L v)
      (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) (f := U)
        (mem_interior_iff_mem_nhds.mp (hNS hq)))
  simp only [stressWithin, gramWithin, densityWithin, hw,
    DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxOne, DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxI,
    DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramA, DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramB,
    DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramC, riemannianAreaDensity, diskMapPartial]

/-- The genuine continuous first-order expression equals the actual interior
stress divergence when the same induced immersion has zero mean trace. -/
theorem complexDivergence_eq_ambientDivergenceWithin_of_mean_zero
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) {S : Set ℂ} (hNS : (N : Set ℂ) ⊆ interior S)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p (Y p)))
    (z : N) (hmean : DifferentialGeometry.Geometry.ImmersedDiskDivergence.inducedMeanTrace N g U hU hi z = 0) :
    DifferentialGeometry.Analysis.complexDivergence
      (fun q => (stressWithin g U S Y q).1) (fun q => (stressWithin g U S Y q).2) z =
      ambientDivergenceWithin g U S Y z := by
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hW := hY.comp_contMDiffOn hUon
  have hw (q : ℂ) (hq : q ∈ N) (v : ℂ) :
      partialWithin (E := E) U S q v = diskMapPartial U q v := by
    exact congrArg (fun L : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U q) => L v)
      (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) (f := U)
        (mem_interior_iff_mem_nhds.mp (hNS hq)))
  have hnear (k : ℝ × ℝ → ℝ) :
      (fun q => k (stressWithin g U S Y q)) =ᶠ[𝓝 (z : ℂ)]
      (fun q => k (DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxOne g U (fun p => Y (U p)) q,
        DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxI g U (fun p => Y (U p)) q)) := by
    filter_upwards [N.isOpen.mem_nhds z.property] with q hq
    simp only [stressWithin, gramWithin, densityWithin, hw q hq,
      DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxOne, DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxI,
      DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramA, DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramB,
      DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramC, riemannianAreaDensity, diskMapPartial]
  have hdiv := DifferentialGeometry.Geometry.ImmersedDiskDivergence.complexDivergence_flux_eq_immersedSectionDivergence_of_mean_zero
    N g U hU hi hW z hmean
  unfold DifferentialGeometry.Analysis.complexDivergence
  rw [(hnear Prod.fst).fderiv_eq, (hnear Prod.snd).fderiv_eq]
  change DifferentialGeometry.Analysis.complexDivergence
    (DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxOne g U (fun p => Y (U p)))
    (DifferentialGeometry.Geometry.ImmersedDiskDivergence.fluxI g U (fun p => Y (U p))) z = _
  rw [hdiv]
  have hzU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z :=
    (hUon.contMDiffAt (N.isOpen.mem_nhds z.property)).of_le (by simp)
  simp only [DifferentialGeometry.Geometry.ImmersedDiskDivergence.immersedSectionDivergence,
    ambientDivergenceWithin, gramWithin, densityWithin, ambientPartialWithin, hw z z.property,
    sourceSectionCovariantDerivative_ambient g hzU Y hY,
    DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramA, DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramB,
    DifferentialGeometry.Geometry.ImmersedDiskDivergence.gramC, riemannianAreaDensity, diskMapPartial]

end DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk

open Set Filter Bundle _root_.Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open scoped _root_.Topology ContDiff _root_.Manifold

abbrev upperClosed : Set ℂ := {z | 0 ≤ z.im}
abbrev upperOpen : Set ℂ := {z | 0 < z.im}

private theorem trace_pair_eq_diagonal (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    LinearMap.trace ℝ (ℝ × ℝ) L.toLinearMap =
      (L (1, 0)).1 + (L (0, 1)).2 := by
  have hL : L.toLinearMap =
      ((LinearMap.fst ℝ ℝ ℝ).comp L.toLinearMap).smulRight (1, 0) +
      ((LinearMap.snd ℝ ℝ ℝ).comp L.toLinearMap).smulRight (0, 1) := by
    apply LinearMap.ext
    intro p
    apply Prod.ext <;> simp
  rw [hL, map_add, LinearMap.trace_smulRight, LinearMap.trace_smulRight]
  rfl

/-- Exact trace transport for the literal coordinate map `(s,n) ↦ s+nI`. -/
theorem trace_fderiv_comp_equivRealProd
    {β : ℂ → ℝ × ℝ} {p : ℝ × ℝ}
    (hβ : DifferentiableAt ℝ β (Complex.equivRealProdCLM.symm p)) :
    LinearMap.trace ℝ (ℝ × ℝ)
        (fderiv ℝ (β ∘ Complex.equivRealProdCLM.symm) p).toLinearMap =
      DifferentialGeometry.Analysis.complexDivergence
        (fun z => (β z).1) (fun z => (β z).2) (Complex.equivRealProdCLM.symm p) := by
  rw [(hβ.hasFDerivAt.comp p Complex.equivRealProdCLM.symm.hasFDerivAt).fderiv,
    trace_pair_eq_diagonal]
  unfold DifferentialGeometry.Analysis.complexDivergence
  rw [hβ.hasFDerivAt.fst.fderiv, hβ.hasFDerivAt.snd.fderiv]
  change ((fderiv ℝ β (Complex.equivRealProdCLM.symm p))
      (Complex.equivRealProdCLM.symm (1, 0))).1 +
      ((fderiv ℝ β (Complex.equivRealProdCLM.symm p))
        (Complex.equivRealProdCLM.symm (0, 1))).2 =
    ((fderiv ℝ β (Complex.equivRealProdCLM.symm p)) (1 : ℂ)).1 +
      ((fderiv ℝ β (Complex.equivRealProdCLM.symm p)) Complex.I).2
  have h1 : Complex.equivRealProdCLM.symm (1, 0) = (1 : ℂ) := by
    simp [Complex.equivRealProdCLM_symm_apply]
  have hI : Complex.equivRealProdCLM.symm (0, 1) = Complex.I := by
    simp [Complex.equivRealProdCLM_symm_apply]
  rw [h1, hI]

/-- Lebesgue measure transport is exactly the complex volume-preserving real-pair
coordinate equivalence, with no extra factor. -/
theorem integral_upper_eq_real_pair (D : ℂ → ℝ) :
    (∫ z in upperOpen, D z) =
      ∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), D (Complex.equivRealProdCLM.symm p) := by
  have he := Complex.volume_preserving_equiv_real_prod.symm
  have hr := he.restrict_preimage (s := upperOpen)
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hi := hr.integral_comp' D
  have hs : Complex.measurableEquivRealProd.symm ⁻¹' upperOpen =
      (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    ext p
    simp [upperOpen]
  have hmap : (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) =
      Complex.equivRealProdCLM.symm := by
    funext p
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply]
  rw [hs, hmap] at hi
  exact hi.symm

/-- Complex-coordinate form of the genuine C¹ seam-limit identity. The actual
trace and measure transports are proved, not assumed as inputs. -/
theorem integral_complex_divergence_extension_eq_boundary
    (β : ℂ → ℝ × ℝ) (D : ℂ → ℝ)
    (hβ : ContinuousOn β upperClosed)
    (hβdiff : ContDiffOn ℝ 1 β upperOpen) (hβcs : HasCompactSupport β)
    (hDcont : ContinuousOn D upperClosed)
    (hD : ∀ z ∈ upperOpen, D z = DifferentialGeometry.Analysis.complexDivergence
      (fun q => (β q).1) (fun q => (β q).2) z) :
    (∫ z in upperOpen, D z) = -∫ s : ℝ, (β (s : ℂ)).2 := by
  let e := Complex.equivRealProdCLM.symm
  have hclosed : MapsTo e ((univ : Set ℝ) ×ˢ Ici 0) upperClosed := fun _ h => h.2
  have hopen : MapsTo e ((univ : Set ℝ) ×ˢ Ioi 0) upperOpen := fun _ h => h.2
  have hβr := hβ.comp e.continuous.continuousOn hclosed
  have hβrd := hβdiff.comp e.contDiff.contDiffOn hopen
  have hβrc := hβcs.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have hDr := hDcont.comp e.continuous.continuousOn hclosed
  have hDr_eq (p : ℝ × ℝ) (hp : 0 < p.2) :
      (D ∘ e) p = LinearMap.trace ℝ (ℝ × ℝ) (fderiv ℝ (β ∘ e) p).toLinearMap := by
    have hp' : e p ∈ upperOpen := hp
    rw [trace_fderiv_comp_equivRealProd
      ((hβdiff.differentiableOn one_ne_zero (e p) hp').differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hp'))]
    exact hD _ hp'
  have h := DifferentialGeometry.Analysis.integral_divergence_eq_neg_boundary_of_continuous_extension
    (β ∘ e) (D ∘ e) hβr hβrd hβrc hDr hDr_eq
  rw [integral_upper_eq_real_pair]
  simpa only [Function.comp_apply, e, Complex.equivRealProdCLM_symm_apply,
    Complex.ofReal_zero, zero_mul, add_zero] using h

/-- Source localization, rather than compact target support, supplies compact
support of the stress. No continuity is needed for this support statement. -/
theorem hasCompactSupport_ball_indicator {F : Type*} [Zero F]
    (f : ℂ → F) (p : ℂ) (r : ℝ) : HasCompactSupport ((Metric.ball p r).indicator f) := by
  classical
  apply (isCompact_closedBall p r).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra hnot
  have hnb : z ∉ Metric.ball p r := fun h => hnot (Metric.ball_subset_closedBall h)
  exact hz (indicator_of_notMem hnb f)

private theorem continuousOn_ball_indicator {F : Type*}
    [TopologicalSpace F] [Zero F] {f : ℂ → F} {S : Set ℂ} {p : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (S ∩ Metric.closedBall p r))
    (hzero : ∀ z ∈ S ∩ Metric.sphere p r, f z = 0) :
    ContinuousOn ((Metric.ball p r).indicator f) S := by
  classical
  change ContinuousOn ((Metric.ball p r).piecewise f (fun _ => 0)) S
  apply ContinuousOn.piecewise
  · intro z hz
    exact hzero z ⟨hz.1, by simpa only [frontier_ball p hr.ne'] using hz.2⟩
  · simpa only [closure_ball p hr.ne'] using hf
  · exact continuousOn_const

private theorem indicator_eventually_zero_of_collar {F : Type*} [Zero F]
    {f : ℂ → F} {S : Set ℂ} {p q : ℂ} {r : ℝ}
    (hqS : S ∈ 𝓝 q)
    (hf : f =ᶠ[𝓝[S ∩ Metric.closedBall p r] q] (fun _ => 0)) :
    (Metric.ball p r).indicator f =ᶠ[𝓝 q] (fun _ => 0) := by
  classical
  have hf' : ∀ᶠ z in 𝓝 q, z ∈ S ∩ Metric.closedBall p r → f z = 0 :=
    eventually_inf_principal.mp hf
  filter_upwards [hf', hqS] with z hz hzS
  by_cases hzb : z ∈ Metric.ball p r
  · rw [indicator_of_mem hzb, hz ⟨hzS, Metric.ball_subset_closedBall hzb⟩]
  · exact indicator_of_notMem hzb f

private theorem contDiffOn_ball_indicator_of_collar
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {S : Set ℂ} {p : ℂ} {r : ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f (S ∩ Metric.ball p r))
    (hcollar : ∀ q ∈ S ∩ Metric.sphere p r,
      f =ᶠ[𝓝[S ∩ Metric.closedBall p r] q] (fun _ => 0)) :
    ContDiffOn ℝ 1 ((Metric.ball p r).indicator f) S := by
  classical
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hqb : q ∈ Metric.ball p r
  · have heq : (Metric.ball p r).indicator f =ᶠ[𝓝 q] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hqb] with z hz
      exact indicator_of_mem hz f
    exact ((hf q ⟨hq, hqb⟩).contDiffAt
      ((hS.inter Metric.isOpen_ball).mem_nhds ⟨hq, hqb⟩)).congr_of_eventuallyEq heq
  · have heq : (Metric.ball p r).indicator f =ᶠ[𝓝 q] (fun _ => 0) := by
      by_cases hqc : q ∈ Metric.closedBall p r
      · have hqs : q ∈ Metric.sphere p r := by
          rw [Metric.mem_sphere]
          exact le_antisymm (Metric.mem_closedBall.mp hqc)
            (not_lt.mp (fun h => hqb (Metric.mem_ball.mpr h)))
        exact indicator_eventually_zero_of_collar (hS.mem_nhds hq)
          (hcollar q ⟨hq, hqs⟩)
      · filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hqc] with z hz
        exact indicator_of_notMem (fun h => hz (Metric.ball_subset_closedBall h)) f
    exact contDiffAt_const.congr_of_eventuallyEq heq

private theorem complexDivergence_congr_eventually
    {β γ : ℂ → ℝ × ℝ} {z : ℂ} (h : β =ᶠ[𝓝 z] γ) :
    DifferentialGeometry.Analysis.complexDivergence (fun q => (β q).1)
      (fun q => (β q).2) z =
    DifferentialGeometry.Analysis.complexDivergence (fun q => (γ q).1)
      (fun q => (γ q).2) z := by
  unfold DifferentialGeometry.Analysis.complexDivergence
  have hfst : (fun q => (β q).1) =ᶠ[𝓝 z] (fun q => (γ q).1) := h.fun_comp Prod.fst
  have hsnd : (fun q => (β q).2) =ᶠ[𝓝 z] (fun q => (γ q).2) := h.fun_comp Prod.snd
  rw [hfst.fderiv_eq, hsnd.fderiv_eq]

/-- A local half-disk suffices. The stress is extended by zero across its
artificial circular boundary using the actual zero collar; it need not be
defined by an immersion on the rest of the half-plane. -/
theorem integral_local_complex_divergence_extension_eq_boundary
    (p : ℂ) {r : ℝ} (hr : 0 < r) (β : ℂ → ℝ × ℝ) (D : ℂ → ℝ)
    (hβ : ContinuousOn β (upperClosed ∩ Metric.closedBall p r))
    (hβdiff : ContDiffOn ℝ 1 β (upperOpen ∩ Metric.ball p r))
    (hβzero : ∀ q ∈ upperClosed ∩ Metric.sphere p r, β q = 0)
    (hβcollar : ∀ q ∈ upperOpen ∩ Metric.sphere p r,
      β =ᶠ[𝓝[upperClosed ∩ Metric.closedBall p r] q] (fun _ => 0))
    (hDcont : ContinuousOn D (upperClosed ∩ Metric.closedBall p r))
    (hDzero : ∀ q ∈ upperClosed ∩ Metric.sphere p r, D q = 0)
    (hD : ∀ z ∈ upperOpen ∩ Metric.ball p r,
      D z = DifferentialGeometry.Analysis.complexDivergence
        (fun q => (β q).1) (fun q => (β q).2) z) :
    (∫ z in upperOpen ∩ Metric.ball p r, D z) =
      -∫ s : ℝ, ((Metric.ball p r).indicator β (s : ℂ)).2 := by
  classical
  let β₀ := (Metric.ball p r).indicator β
  let D₀ := (Metric.ball p r).indicator D
  have hopen : IsOpen upperOpen := isOpen_lt continuous_const Complex.continuous_im
  have hcollar : ∀ q ∈ upperOpen ∩ Metric.sphere p r,
      β =ᶠ[𝓝[upperOpen ∩ Metric.closedBall p r] q] (fun _ => 0) := by
    intro q hq
    exact (hβcollar q hq).filter_mono (nhdsWithin_mono q
      (fun z hz => ⟨(show 0 < z.im from hz.1).le, hz.2⟩))
  have hβ₀ : ContinuousOn β₀ upperClosed := continuousOn_ball_indicator hr hβ hβzero
  have hβ₀d : ContDiffOn ℝ 1 β₀ upperOpen :=
    contDiffOn_ball_indicator_of_collar hopen hβdiff hcollar
  have hD₀ : ContinuousOn D₀ upperClosed := continuousOn_ball_indicator hr hDcont hDzero
  have hD₀eq : ∀ z ∈ upperOpen, D₀ z =
      DifferentialGeometry.Analysis.complexDivergence
        (fun q => (β₀ q).1) (fun q => (β₀ q).2) z := by
    intro z hz
    by_cases hzb : z ∈ Metric.ball p r
    · have heq : β₀ =ᶠ[𝓝 z] β := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with q hq
        exact indicator_of_mem hq β
      rw [complexDivergence_congr_eventually heq]
      exact (indicator_of_mem hzb D).trans (hD z ⟨hz, hzb⟩)
    · have heq : β₀ =ᶠ[𝓝 z] (fun _ => 0) := by
        by_cases hzc : z ∈ Metric.closedBall p r
        · have hzs : z ∈ Metric.sphere p r := by
            rw [Metric.mem_sphere]
            exact le_antisymm (Metric.mem_closedBall.mp hzc)
              (not_lt.mp (fun h => hzb (Metric.mem_ball.mpr h)))
          exact indicator_eventually_zero_of_collar (hopen.mem_nhds hz)
            (hcollar z ⟨hz, hzs⟩)
        · filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hzc] with q hq
          exact indicator_of_notMem (fun h => hq (Metric.ball_subset_closedBall h)) β
      rw [complexDivergence_congr_eventually heq]
      simp only [D₀, indicator_of_notMem hzb,
        DifferentialGeometry.Analysis.complexDivergence, Prod.fst_zero, Prod.snd_zero,
        fderiv_const_apply, _root_.zero_apply, add_zero]
  have h := integral_complex_divergence_extension_eq_boundary β₀ D₀ hβ₀ hβ₀d
    (hasCompactSupport_ball_indicator β p r) hD₀ hD₀eq
  rwa [show (∫ z in upperOpen, D₀ z) =
      ∫ z in upperOpen ∩ Metric.ball p r, D z from
    setIntegral_indicator Metric.isOpen_ball.measurableSet] at h

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [T2Space M] in
private theorem ambientDerivative_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    {x : M} (hx : x ∉ tsupport Y) : (leviCivitaConnectionOfMetric g) Y x = 0 := by
  have h := (leviCivitaConnectionOfMetric g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hY.mdifferentiable (by simp) x) (mdifferentiableAt_zeroSection ..) univ_mem
    (notMem_tsupport_iff_eventuallyEq.mp hx)
  change (leviCivitaConnectionOfMetric g) Y x =
    (leviCivitaConnectionOfMetric g) (0 : ∀ p : M, TangentSpace 𝓘(ℝ, E) p) x at h
  rw [(leviCivitaConnectionOfMetric g).zero] at h
  exact h

omit [T2Space M] in
/-- The actual target support avoidance supplied by the cutoff construction
forces both stress and the first-order divergence expression to vanish on a
source collar. It does not assume any second boundary derivative. -/
theorem stress_and_divergence_zero_on_source_collar
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (S : Set ℂ)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    {q : ℂ} (hU : ContinuousWithinAt U S q) (hq : U q ∉ tsupport Y) :
    (stressWithin g U S Y =ᶠ[𝓝[S] q] (fun _ => 0)) ∧
      (ambientDivergenceWithin g U S Y =ᶠ[𝓝[S] q] (fun _ => 0)) := by
  have hpre : ∀ᶠ z in 𝓝[S] q, U z ∉ tsupport Y :=
    hU ((isClosed_tsupport Y).isOpen_compl.mem_nhds hq)
  constructor
  · filter_upwards [hpre] with z hz
    have hg0 (v : TangentSpace 𝓘(ℝ, E) (U z)) :
        g.inner (U z) (Y (U z)) v = 0 := by
      let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
      change G (Y (U z)) v = 0
      rw [image_eq_zero_of_notMem_tsupport hz, map_zero]
      rfl
    simp only [stressWithin, hg0, mul_zero, sub_self, Prod.mk_zero_zero]
  · filter_upwards [hpre] with z hz
    have hDY := ambientDerivative_eq_zero_off_tsupport g Y hY hz
    simp only [ambientDivergenceWithin, ambientPartialWithin, hDY,
      _root_.zero_apply, map_zero, mul_zero, add_zero, sub_self, zero_div]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Gram stress equals actual conormal flux per seam arclength, and reversing
the inward conormal produces exactly the outward sign in the half-plane formula. -/
theorem gram_stress_eq_inward_and_outward_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (T N V : TangentSpace 𝓘(ℝ, E) x) (hT : T ≠ 0)
    (hdet : 0 < g.inner x T T * g.inner x N N - (g.inner x T N) ^ 2) :
    let a := g.inner x T T
    let b := g.inner x T N
    let J := Real.sqrt (a * g.inner x N N - b ^ 2)
    let ν := (Real.sqrt a * J)⁻¹ • (a • N - b • T)
    (a * g.inner x V N - b * g.inner x V T) / J = Real.sqrt a * g.inner x V ν ∧
      -((a * g.inner x V N - b * g.inner x V T) / J) =
        Real.sqrt a * g.inner x V (-ν) := by
  dsimp only
  have ha : Real.sqrt (g.inner x T T) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (g.pos x T hT))
  have hJ : Real.sqrt (g.inner x T T * g.inner x N N - g.inner x T N ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hdet)
  have hin : (g.inner x T T * g.inner x V N - g.inner x T N * g.inner x V T) /
      Real.sqrt (g.inner x T T * g.inner x N N - g.inner x T N ^ 2) =
      Real.sqrt (g.inner x T T) * g.inner x V
        ((Real.sqrt (g.inner x T T) *
          Real.sqrt (g.inner x T T * g.inner x N N - g.inner x T N ^ 2))⁻¹ •
            (g.inner x T T • N - g.inner x T N • T)) := by
    simp only [map_smul, map_sub, smul_eq_mul]
    field_simp [ha, hJ]
  refine ⟨hin, ?_⟩
  rw [hin, map_neg, mul_neg]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The Gram formula is a genuine unit conormal: it is perpendicular to the
seam tangent and has positive pairing with the inward coordinate derivative. -/
theorem gram_inward_conormal_geometry
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (T N : TangentSpace 𝓘(ℝ, E) x) (hT : T ≠ 0)
    (hdet : 0 < g.inner x T T * g.inner x N N - (g.inner x T N) ^ 2) :
    let a := g.inner x T T
    let b := g.inner x T N
    let J := Real.sqrt (a * g.inner x N N - b ^ 2)
    let ν := (Real.sqrt a * J)⁻¹ • (a • N - b • T)
    g.inner x ν ν = 1 ∧ g.inner x ν T = 0 ∧ 0 < g.inner x ν N := by
  let a := g.inner x T T
  let b := g.inner x T N
  let Δ := a * g.inner x N N - b ^ 2
  let d := Real.sqrt a * Real.sqrt Δ
  let Q := a • N - b • T
  have ha : 0 < a := g.pos x T hT
  have hΔ : 0 < Δ := hdet
  have hd : 0 < d := mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hΔ)
  have hd2 : d ^ 2 = a * Δ := by
    dsimp only [d]
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hΔ.le]
  have hNT : g.inner x N T = b := g.symm x N T
  have hQT : g.inner x Q T = 0 := by
    simp only [Q, map_sub, map_smul, _root_.sub_apply,
      _root_.smul_apply, smul_eq_mul, hNT]
    change a * b - b * a = 0
    ring
  have hQN : g.inner x Q N = Δ := by
    simp only [Q, map_sub, map_smul, _root_.sub_apply,
      _root_.smul_apply, smul_eq_mul]
    change a * g.inner x N N - b * b = Δ
    dsimp [Δ]
    ring
  have hQQ : g.inner x Q Q = a * Δ := by
    change g.inner x Q (a • N - b • T) = a * Δ
    rw [map_sub, map_smul, map_smul, hQN, hQT]
    simp only [smul_eq_mul, mul_zero, sub_zero]
  change g.inner x (d⁻¹ • Q) (d⁻¹ • Q) = 1 ∧
    g.inner x (d⁻¹ • Q) T = 0 ∧ 0 < g.inner x (d⁻¹ • Q) N
  have hscale (v : TangentSpace 𝓘(ℝ, E) x) :
      g.inner x (d⁻¹ • Q) v = d⁻¹ * g.inner x Q v := by
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hscale, map_smul, smul_eq_mul, hQQ, ← hd2]
    field_simp [hd.ne']
  · rw [hscale, hQT, mul_zero]
  · rw [hscale, hQN]
    exact mul_pos (inv_pos.mpr hd) hΔ

/-- The inward conormal determined by the actual one-sided disk differential.
The positive imaginary coordinate is the inward coordinate. -/
def inwardConormalWithin (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (S : Set ℂ) (z : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  (Real.sqrt (gramWithin g U S z 1 1) * densityWithin g U S z)⁻¹ •
    (gramWithin g U S z 1 1 • partialWithin U S z Complex.I -
      gramWithin g U S z 1 Complex.I • partialWithin U S z 1)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
private theorem partialWithin_one_ne_zero {U : ℂ → M} {S : Set ℂ} {z : ℂ}
    (hi : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z)) :
    partialWithin (E := E) U S z 1 ≠ 0 := by
  intro h
  let L : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z
  have hL : Function.Injective L := hi
  apply one_ne_zero (α := ℂ)
  apply hL
  rw [map_zero]
  exact h

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Unit length, tangential orthogonality and inward orientation are derived
from the actual rank-two differential, without an assumed conormal law. -/
theorem inwardConormalWithin_geometry
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {S : Set ℂ} {z : ℂ}
    (hi : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z)) :
    g.inner (U z) (inwardConormalWithin g U S z) (inwardConormalWithin g U S z) = 1 ∧
      g.inner (U z) (inwardConormalWithin g U S z) (partialWithin U S z 1) = 0 ∧
      0 < g.inner (U z) (inwardConormalWithin g U S z) (partialWithin U S z Complex.I) := by
  have hdet := Real.sqrt_pos.mp (DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within.densityWithin_pos g hi)
  exact gram_inward_conormal_geometry g (U z) (partialWithin U S z 1)
    (partialWithin U S z Complex.I) (partialWithin_one_ne_zero hi) hdet

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The actual second stress component has the precise seam-arclength factor. -/
theorem stressWithin_snd_eq_seamSpeed_inner_inwardConormal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {S : Set ℂ} {z : ℂ}
    (hi : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z))
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) :
    (stressWithin g U S Y z).2 = Real.sqrt (gramWithin g U S z 1 1) *
      g.inner (U z) (Y (U z)) (inwardConormalWithin g U S z) := by
  have hdet := Real.sqrt_pos.mp (DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within.densityWithin_pos g hi)
  have h := (gram_stress_eq_inward_and_outward_flux g (U z)
    (partialWithin U S z 1) (partialWithin U S z Complex.I) (Y (U z))
      (partialWithin_one_ne_zero hi) hdet).1
  change (gramWithin g U S z 1 1 *
      g.inner (U z) (Y (U z)) (partialWithin (E := E) U S z Complex.I) -
      gramWithin g U S z 1 Complex.I *
        g.inner (U z) (Y (U z)) (partialWithin (E := E) U S z 1)) /
      densityWithin g U S z =
    Real.sqrt (gramWithin g U S z 1 1) *
      g.inner (U z) (Y (U z)) (inwardConormalWithin g U S z) at h
  rw [← h]
  dsimp only [stressWithin]
  ring

omit [T2Space M] in
/-- Only continuity of the actual conormal pairing is needed by the strict
seam-flux argument. It follows from one-sided C¹ sheet data and a smooth
ambient field; the conormal itself is not presumed to extend smoothly. -/
theorem continuousOn_inner_inwardConormalWithin
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) {S : Set ℂ}
    (hS : UniqueMDiffOn 𝓘(ℝ, ℂ) S)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U S)
    (hi : ∀ z ∈ S, Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U S z))
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x))) :
    ContinuousOn (fun z => g.inner (U z) (Y (U z)) (inwardConormalWithin g U S z)) S := by
  have hT := DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within.partialWithin_contMDiff_zero hS hU (1 : ℂ)
  have ha : ContinuousOn (fun z => gramWithin g U S z 1 1) S :=
    (DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within.pairing_contDiff_zero g
      (hU.of_le (by simp)) hT hT).continuousOn
  have hρ : ∀ z ∈ S, Real.sqrt (gramWithin g U S z 1 1) ≠ 0 := by
    intro z hz
    exact (Real.sqrt_pos.mpr (g.pos (U z) _ (partialWithin_one_ne_zero (hi z hz)))).ne'
  have hc := ((continuousOn_stress_and_ambientDivergenceWithin g U hS hU hi Y hY).1.snd).div
    ha.sqrt hρ
  apply hc.congr
  intro z hz
  change g.inner (U z) (Y (U z)) (inwardConormalWithin g U S z) =
    (stressWithin g U S Y z).2 / Real.sqrt (gramWithin g U S z 1 1)
  rw [stressWithin_snd_eq_seamSpeed_inner_inwardConormal g (hi z hz) Y]
  field_simp [hρ z hz]

abbrev closedHalfDisk (p r : ℝ) : Set ℂ :=
  upperClosed ∩ Metric.closedBall (p : ℂ) r

def openHalfDisk (p r : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨upperOpen ∩ Metric.ball (p : ℂ) r,
    (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball⟩

private theorem openHalfDisk_subset_interior (p r : ℝ) :
    (openHalfDisk p r : Set ℂ) ⊆ interior (closedHalfDisk p r) := by
  intro z hz
  apply mem_interior_iff_mem_nhds.mpr
  exact mem_of_superset ((openHalfDisk p r).isOpen.mem_nhds hz)
    (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)

private theorem uniqueMDiffOn_closedHalfDisk (p : ℝ) {r : ℝ} (hr : 0 < r) :
    UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk p r) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex ((convex_halfSpace_im_ge 0).inter (convex_closedBall (p : ℂ) r))
  refine ⟨(p : ℂ) + (r / 2 : ℂ) * Complex.I, openHalfDisk_subset_interior p r ?_⟩
  constructor
  · change 0 < ((p : ℂ) + (r / 2 : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.div_ofNat_re, Complex.ofReal_re, zero_add]
    positivity
  · rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos hr]
    linarith

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
private theorem injective_restrict_of_closedHalfDisk
    {U : ℂ → M} {p r : ℝ}
    (hi : ∀ z ∈ closedHalfDisk p r,
      Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (closedHalfDisk p r) z))
    (z : openHalfDisk p r) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      (fun q : openHalfDisk p r => U q) z) := by
  rw [DifferentialGeometry.mfderiv_restrict_open]
  have hS : closedHalfDisk p r ∈ 𝓝 (z : ℂ) :=
    mem_interior_iff_mem_nhds.mp (openHalfDisk_subset_interior p r z.property)
  rw [← mfderivWithin_of_mem_nhds hS]
  exact hi z (mem_of_mem_nhds hS)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The circle cutoff converts the actual localized boundary stress to the
closed seam interval used by the strict flux lemma. Its endpoints contribute
zero pointwise, and the outward conormal is the negative inward conormal. -/
theorem boundary_stress_integral_eq_outward_conormal_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (p r : ℝ)
    (hi : ∀ z ∈ closedHalfDisk p r,
      Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (closedHalfDisk p r) z))
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (havoid : ∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, U q ∉ tsupport Y) :
    (-∫ s : ℝ, ((Metric.ball (p : ℂ) r).indicator
      (stressWithin g U (closedHalfDisk p r) Y) (s : ℂ)).2) =
    ∫ s : ℝ, (Icc (p - r) (p + r)).indicator
      (fun s => Real.sqrt (gramWithin g U (closedHalfDisk p r) (s : ℂ) 1 1) *
        g.inner (U (s : ℂ)) (Y (U (s : ℂ)))
          (-inwardConormalWithin g U (closedHalfDisk p r) (s : ℂ))) s := by
  classical
  have hclosed (s : ℝ) : (s : ℂ) ∈ Metric.closedBall (p : ℂ) r ↔
      s ∈ Icc (p - r) (p + r) := by
    rw [Metric.mem_closedBall, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hpoint (s : ℝ) :
      -((Metric.ball (p : ℂ) r).indicator
        (stressWithin g U (closedHalfDisk p r) Y) (s : ℂ)).2 =
      (Icc (p - r) (p + r)).indicator
        (fun s => Real.sqrt (gramWithin g U (closedHalfDisk p r) (s : ℂ) 1 1) *
          g.inner (U (s : ℂ)) (Y (U (s : ℂ)))
            (-inwardConormalWithin g U (closedHalfDisk p r) (s : ℂ))) s := by
    by_cases hb : (s : ℂ) ∈ Metric.ball (p : ℂ) r
    · have hc := Metric.ball_subset_closedBall hb
      have hS : (s : ℂ) ∈ closedHalfDisk p r := ⟨by simp [upperClosed], hc⟩
      rw [indicator_of_mem hb, indicator_of_mem ((hclosed s).mp hc),
        stressWithin_snd_eq_seamSpeed_inner_inwardConormal g (hi _ hS) Y,
        map_neg, mul_neg]
    · rw [indicator_of_notMem hb]
      by_cases hs : s ∈ Icc (p - r) (p + r)
      · have hc := (hclosed s).mpr hs
        have hcircle : (s : ℂ) ∈ Metric.sphere (p : ℂ) r := by
          rw [Metric.mem_sphere]
          exact le_antisymm (Metric.mem_closedBall.mp hc)
            (not_lt.mp (fun h => hb (Metric.mem_ball.mpr h)))
        have hYzero : Y (U (s : ℂ)) = 0 :=
          image_eq_zero_of_notMem_tsupport (havoid _ ⟨by simp [upperClosed], hcircle⟩)
        simp only [indicator_of_mem hs, hYzero, map_zero,
          _root_.zero_apply, mul_zero, Prod.snd_zero, neg_zero]
      · simp only [indicator_of_notMem hs, Prod.snd_zero, neg_zero]
  rw [← integral_neg]
  exact integral_congr_ae (Eventually.of_forall hpoint)

/-- The local immersed half-sheet supplies the actual divergence integral.
Only first derivatives are required up to the seam; smoothness and zero mean
trace are required on the open half-disk. The source zero collar is derived
from the actual ambient support avoidance on the circular boundary. -/
theorem integral_actual_halfdisk_ambient_divergence_eq_outward_conormal_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (p : ℝ) {r : ℝ} (hr : 0 < r)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U (closedHalfDisk p r))
    (hi : ∀ z ∈ closedHalfDisk p r,
      Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (closedHalfDisk p r) z))
    (hUinterior : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (fun z : openHalfDisk p r => U z))
    (hmean : ∀ z : openHalfDisk p r,
      DifferentialGeometry.Geometry.ImmersedDiskDivergence.inducedMeanTrace (openHalfDisk p r) g U
        hUinterior (injective_restrict_of_closedHalfDisk hi) z = 0)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (havoid : ∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, U q ∉ tsupport Y) :
    (∫ z in (openHalfDisk p r : Set ℂ),
        ambientDivergenceWithin g U (closedHalfDisk p r) Y z) =
      ∫ s : ℝ, (Icc (p - r) (p + r)).indicator
        (fun s => Real.sqrt (gramWithin g U (closedHalfDisk p r) (s : ℂ) 1 1) *
          g.inner (U (s : ℂ)) (Y (U (s : ℂ)))
            (-inwardConormalWithin g U (closedHalfDisk p r) (s : ℂ))) s := by
  rw [← boundary_stress_integral_eq_outward_conormal_flux g U p r hi Y havoid]
  let S := closedHalfDisk p r
  let β := stressWithin g U S Y
  let D := ambientDivergenceWithin g U S Y
  have hc := continuousOn_stress_and_ambientDivergenceWithin g U
    (uniqueMDiffOn_closedHalfDisk p hr) hU hi Y hY
  have hcircle (q : ℂ) (hq : q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r) :
      β q = 0 ∧ D q = 0 := by
    have hqS : q ∈ S := ⟨hq.1, Metric.sphere_subset_closedBall hq.2⟩
    have hcollar := stress_and_divergence_zero_on_source_collar g U S Y hY
      (hU.continuousOn q hqS) (havoid q hq)
    exact ⟨hcollar.1.eq_of_nhdsWithin hqS, hcollar.2.eq_of_nhdsWithin hqS⟩
  apply integral_local_complex_divergence_extension_eq_boundary (p : ℂ) hr β D hc.1
  · exact (contDiffOn_stressWithin_of_smooth_interior (openHalfDisk p r) g U
      (openHalfDisk_subset_interior p r) hUinterior
      (injective_restrict_of_closedHalfDisk hi) Y hY).of_le (by simp)
  · exact fun q hq => (hcircle q hq).1
  · intro q hq
    have hqS : q ∈ S := ⟨(show 0 < q.im from hq.1).le, Metric.sphere_subset_closedBall hq.2⟩
    exact (stress_and_divergence_zero_on_source_collar g U S Y hY
      (hU.continuousOn q hqS) (havoid q ⟨(show 0 < q.im from hq.1).le, hq.2⟩)).1
  · exact hc.2
  · exact fun q hq => (hcircle q hq).2
  · intro z hz
    exact (complexDivergence_eq_ambientDivergenceWithin_of_mean_zero
      (openHalfDisk p r) g U (openHalfDisk_subset_interior p r) hUinterior
        (injective_restrict_of_closedHalfDisk hi) Y hY ⟨z, hz⟩ (hmean ⟨z, hz⟩)).symm

end DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
