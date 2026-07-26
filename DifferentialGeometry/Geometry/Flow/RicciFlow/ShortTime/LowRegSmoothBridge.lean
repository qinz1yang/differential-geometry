import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDenseSolve

/-!
# Low-regularity smooth forcing bridge

The dense lower-regularity nonlinearity agrees with the genuine smooth
Ricci--DeTurck nonlinearity on its smooth core.  Consequently, whenever a
smooth representative family is pinned to the maximal-regularity solution on
the original time interval, the forcing identity transfers on that same
interval; no post-solution time shrink is used here.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- Symmetrizing a smooth `H3` state representative preserves its lower
`H2` state-ball bound. -/
theorem symm_h2_of_state
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ 3 by norm_num)
      (smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S)‖ ≤ R) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ)
      (symmS (I := I) (M := M) g₀ S)‖ ≤ R := by
  calc
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ)
        (symmS (I := I) (M := M) g₀ S)‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) S‖ :=
      norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (2 : ℝ) S
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ 3 by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S)‖ := by
      rw [tensorHsInclusion_smoothCcToTensorHs]
    _ ≤ R := hS

/-- A continuous genuine core nonlinearity is recovered exactly by its dense
extension at every point of the smooth core.  `lowreg_partial_sol` exports the
required core continuity for its concrete `Nfun`. -/
theorem lowRegN_on_core
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (x : smoothCore (I := I) (M := M) g₀ R) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal x.1 =
      coreN (I := I) (M := M) g₀ g_bg hδ hreal x := by
  simpa only [lowRegN] using
    (smoothCore_dense (I := I) (M := M) g₀ hR).extend_eq hcore x

/-- On a directly supplied smooth state representative, `lowRegN` is the
order-one spectral embedding of the genuine smooth Ricci--DeTurck remainder. -/
theorem lowRegN_on_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ 3 by norm_num)
      (smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S)‖ ≤ R) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S, hS⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀ S) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hS)) := by
  let u : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S, hS⟩
  let x : smoothCore (I := I) (M := M) g₀ R := ⟨u, ⟨S, rfl⟩⟩
  have hrep : coreRep g₀ x = S := by
    apply smoothHs_inj (I := I) (M := M) g₀ (3 : ℝ)
    rw [coreRep_spec]
    rfl
  have hx := lowRegN_on_core (I := I) (M := M) g₀ g_bg hR hδ hreal hcore x
  unfold coreN at hx
  rw [hrep] at hx
  simpa only [u, x] using hx

/-- If a smooth representative family is pinned to the lower-regularity
maximal-regularity field, its forcing is the genuine smooth Ricci--DeTurck
forcing almost everywhere on the original time interval `T`. -/
theorem lowReg_force_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)) T)
    (hstate : ∀ᵐ t ∂(timeMeasure T),
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t)))
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (hpin : ∀ᵐ t ∂(timeMeasure T),
      smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) (F t) = field t)
    (hball : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ 3 by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) (F t))‖ ≤ R) :
    gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))) := by
  filter_upwards [hforce, hstate, hpin] with t htforce htstate htpin
  let uF : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) (F t), hball t⟩
  have hlift : aeSetLift
      (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t = uF := by
    apply Subtype.ext
    simp only [aeSetLift, dif_pos htstate, uF]
    exact htpin.symm
  rw [htforce, hlift]
  simpa only [uF] using
    lowRegN_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore (F t) (hball t)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
