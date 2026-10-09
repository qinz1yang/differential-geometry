import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskNormalTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskTensionSmoothness
import Mathlib.Topology.VectorBundle.Hom

/-! # Continuity of the original disk's normal scalar trace

The metric is the actual induced metric of the same complex immersion. Local
ambient trivializations establish continuity without a global tangent frame or
an extension of the normal section beyond its original open source.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem continuous_restricted_diskMapCovariantPartial
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (v w : ℂ) :
    Continuous (fun q : N =>
      (⟨U q, diskMapCovariantPartial g U q v w⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp
      (hU.contMDiffAt (x := (⟨z, hz⟩ : N)))).contMDiffWithinAt
  apply continuous_iff_continuousAt.mpr
  intro q₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hU.continuous.continuousAt, ?_⟩
  let α : M := U q₀
  let s : Set ℂ := (N : Set ℂ) ∩ U ⁻¹' (chartAt E α).source
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) α
  have hs : IsOpen s :=
    hUon.continuousOn.isOpen_inter_preimage N.isOpen (chartAt E α).open_source
  have hq₀ : (q₀ : ℂ) ∈ s := ⟨q₀.property, mem_chart_source E (U q₀)⟩
  have hUs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s := hUon.mono inter_subset_left
  have hsrc : ∀ z ∈ s, U z ∈ (chartAt E α).source := fun _ hz => hz.2
  have hc : ContDiffAt ℝ ∞
      (fun z : ℂ => e.continuousLinearMapAt ℝ (U z)
        (diskMapCovariantPartial g U z v w)) q₀ :=
    (contDiffOn_diskMapCovariantPartial_trivAt g hs hUs hsrc v w).contDiffAt
      (hs.mem_nhds hq₀)
  have hcN : ContinuousAt
      (fun q : N => e.continuousLinearMapAt ℝ (U q)
        (diskMapCovariantPartial g U q v w)) q₀ :=
    hc.continuousAt.comp continuous_subtype_val.continuousAt
  change ContinuousAt
    (fun q : N => (e (⟨U q, diskMapCovariantPartial g U q v w⟩ :
      TangentBundle 𝓘(ℝ, E) M)).2) q₀
  refine hcN.congr_of_eventuallyEq ?_
  have hpre : ∀ᶠ q : N in 𝓝 q₀, U q ∈ (chartAt E α).source :=
    hU.continuous.continuousAt
      ((chartAt E α).open_source.mem_nhds (mem_chart_source E (U q₀)))
  filter_upwards [hpre] with q hq
  have hb : U q ∈ e.baseSet := by
    change U q ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact hq
  exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hb
    (diskMapCovariantPartial g U q v w)).symm

/-- The unnormalized normal scalar trace is continuous for the same original
immersion and its induced metric. Bundle continuity of the genuine normal
section suffices; no unit length, conformality or global frame is assumed. -/
theorem continuous_normal_scalar_secondFundamentalForm_disk_trace
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : Continuous
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hnormal : ∀ (q : N) (v : ℂ),
      g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0) :
    let f : N → M := fun q => U q
    let gN := g.pullback f hU hi
    let H : N → ℝ := fun q =>
      let II := secondFundamentalFormAmbientAt gN g f q
      let A := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)
      let B := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)
      let C := g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)
      (C * g.inner (U q) (ν q) (II (1 : ℂ) (1 : ℂ)) +
          A * g.inner (U q) (ν q) (II Complex.I Complex.I) -
          2 * B * g.inner (U q) (ν q) (II (1 : ℂ) Complex.I)) /
        (A * C - B ^ 2)
    Continuous H := by
  let f : N → M := fun q => U q
  let gN := g.pullback f hU hi
  let Q (q : N) : ℂ →L[ℝ] ℂ →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g f q
  let A : N → ℝ := fun q =>
    g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)
  let B : N → ℝ := fun q =>
    g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)
  let C : N → ℝ := fun q =>
    g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)
  let P : ℂ → N → ℝ := fun v q =>
    g.inner (U q) (ν q) (diskMapCovariantPartial g U q v v)
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp
      (hU.contMDiffAt (x := (⟨z, hz⟩ : N)))).contMDiffWithinAt
  have hcoef (v w : ℂ) : Continuous
      (fun q : N => g.inner (U q) (diskMapPartial U q v) (diskMapPartial U q w)) :=
    (contDiffOn_diskMapMetricPairing g N.isOpen hUon v w).continuousOn.comp_continuous
      continuous_subtype_val (fun q => q.property)
  have hA : Continuous A := hcoef 1 1
  have hB : Continuous B := hcoef 1 Complex.I
  have hC : Continuous C := hcoef Complex.I Complex.I
  have hP (v : ℂ) : Continuous (P v) := by
    have hpartial := continuous_restricted_diskMapCovariantPartial N g U hU v v
    have hpair : Continuous
        (fun q : N => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U q)
          (g.inner (U q) (ν q) (diskMapCovariantPartial g U q v v))) :=
      Continuous.clm_bundle_apply₂
        (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (E₁ := fun x : M => TangentSpace 𝓘(ℝ, E) x)
        (E₂ := fun x : M => TangentSpace 𝓘(ℝ, E) x)
        (E₃ := Bundle.Trivial M ℝ) (b := fun q : N => U q)
        (ψ := fun q => g.inner (U q)) (v := ν)
        (w := fun q => diskMapCovariantPartial g U q v v)
        (g.contMDiff.continuous.comp hU.continuous) hν hpartial
    apply continuous_iff_continuousAt.mpr
    intro q
    have h := hpair.continuousAt (x := q)
    rw [FiberBundle.continuousAt_totalSpace] at h
    exact h.2
  have hdf (q : N) :
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q : ℂ →L[ℝ] E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
    DifferentialGeometry.mfderiv_restrict_open U N q
  have hnormalU (q : N) (v : ℂ) :
      g.inner (U q) (ν q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q v) = 0 :=
    (congrArg (fun L : ℂ →L[ℝ] E => g.inner (U q) (ν q) (L v)) (hdf q)).symm.trans
      (hnormal q v)
  have hdiag (q : N) (v : ℂ) :
      g.inner (U q) (ν q) (Q q v v) = P v q :=
    inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial
      N gN g U hU q (ν q) (hnormalU q) v
  have hdiagfun (v : ℂ) : (fun q : N => g.inner (U q) (ν q) (Q q v v)) = P v :=
    funext (fun q => hdiag q v)
  have hdiagc (v : ℂ) : Continuous (fun q : N => g.inner (U q) (ν q) (Q q v v)) := by
    rw [hdiagfun v]
    exact hP v
  have hpol (q : N) : 2 * g.inner (U q) (ν q) (Q q (1 : ℂ) Complex.I) =
      P (1 + Complex.I) q - P 1 q - P Complex.I q := by
    let ℓ : E →L[ℝ] ℝ := g.inner (U q) (ν q)
    change 2 * ℓ (Q q (1 : ℂ) Complex.I) =
      P (1 + Complex.I) q - P 1 q - P Complex.I q
    have hsymm : Q q Complex.I (1 : ℂ) = Q q (1 : ℂ) Complex.I :=
      secondFundamentalFormAmbientAt_symmetric gN g
        ((hU.contMDiffAt (x := q)).of_le (by simp)) Complex.I (1 : ℂ)
    have hQdiag (v : ℂ) : ℓ (Q q v v) = P v q := hdiag q v
    have h := hQdiag (1 + Complex.I)
    simp only [map_add, _root_.add_apply, hsymm] at h
    rw [hQdiag (1 : ℂ), hQdiag Complex.I] at h
    linarith only [h]
  have hmixed : (fun q : N => g.inner (U q) (ν q) (Q q (1 : ℂ) Complex.I)) =
      fun q => (P (1 + Complex.I) q - P 1 q - P Complex.I q) / 2 := by
    funext q
    let ℓ : E →L[ℝ] ℝ := g.inner (U q) (ν q)
    change ℓ (Q q (1 : ℂ) Complex.I) =
      (P (1 + Complex.I) q - P 1 q - P Complex.I q) / 2
    have h : 2 * ℓ (Q q (1 : ℂ) Complex.I) =
        P (1 + Complex.I) q - P 1 q - P Complex.I q := hpol q
    linarith only [h]
  have hmixedc : Continuous
      (fun q : N => g.inner (U q) (ν q) (Q q (1 : ℂ) Complex.I)) := by
    rw [hmixed]
    exact (((hP (1 + Complex.I)).sub (hP 1)).sub (hP Complex.I)).div_const 2
  have hdet (q : N) : 0 < A q * C q - B q ^ 2 := by
    have hinj : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q) := by
      rw [← hdf q]
      exact hi q
    exact Real.sqrt_pos.mp (riemannianAreaDensity_pos_of_injective_mfderiv g hinj)
  change Continuous (fun q : N =>
    (C q * g.inner (U q) (ν q) (Q q (1 : ℂ) (1 : ℂ)) +
        A q * g.inner (U q) (ν q) (Q q Complex.I Complex.I) -
        2 * B q * g.inner (U q) (ν q) (Q q (1 : ℂ) Complex.I)) /
      (A q * C q - B q ^ 2))
  exact (((hC.mul (hdiagc 1)).add (hA.mul (hdiagc Complex.I))).sub
    ((continuous_const.mul hB).mul hmixedc)).div
      ((hA.mul hC).sub (hB.pow 2)) (fun q => ne_of_gt (hdet q))

end DifferentialGeometry.Geometry
