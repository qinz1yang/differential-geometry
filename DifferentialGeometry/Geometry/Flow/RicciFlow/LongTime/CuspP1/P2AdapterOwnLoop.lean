import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterOwnGeodesic
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# P2A-13 (step 1): the transported prescribed meridian is a smooth embedded loop
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

open GC.LongTime

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

namespace PrescribedCuspMeridianTop_CPQ

theorem slice_mem_domain_P2A (M : PrescribedCuspMeridianTop_CPQ cores) (t : ℝ)
    (ht : M.exterior.start ≤ t) (x : Torus) :
    (M.exterior.truncation M.model).cuspMap M.port (x, halfZero) ∈
      cores.domain M.model t := by
  have h1 := (M.exterior.truncation M.model).cusp_zero M.port x
  refine cores.advertised_ball M.model t (M.exterior.after_cores.trans ht) ?_
  refine M.exterior.in_ball M.model t ht ?_
  rw [h1]
  exact ⟨_, rfl⟩

/-- The boundary-slice curve in the half-collar. -/
def sliceCurve_P2A (M : PrescribedCuspMeridianTop_CPQ cores) : ℝ → CuspHalfSpace :=
  fun s => (loopLift M.loop s, halfZero)

/-- The lifted curve in the hyperbolic model. -/
def modelCurve_P2A (M : PrescribedCuspMeridianTop_CPQ cores) : ℝ → (cores.model M.model).Carrier :=
  fun s => (M.exterior.truncation M.model).cuspMap M.port (M.sliceCurve_P2A s)

theorem sliceCurve_contMDiff_P2A (M : PrescribedCuspMeridianTop_CPQ cores) :
    ContMDiff 𝓘(ℝ, ℝ) halfCollarModel ∞ M.sliceCurve_P2A :=
  M.smooth.prodMk contMDiff_const

theorem modelCurve_contMDiff_P2A (M : PrescribedCuspMeridianTop_CPQ cores) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ M.modelCurve_P2A :=
  ((M.exterior.truncation M.model).cuspEmbedding M.port).contMDiff.comp M.sliceCurve_contMDiff_P2A

theorem modelCurve_mfderiv_ne_zero_P2A (M : PrescribedCuspMeridianTop_CPQ cores) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 3) M.modelCurve_P2A s (1 : ℝ) ≠ 0 := by
  have hv : mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s (1 : ℝ) ≠ 0 :=
    loop_velocity_ne_zero_P2A _ M.loop M.embedded M.geodesic s
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel M.sliceCurve_P2A s :=
    (M.sliceCurve_contMDiff_P2A s).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt halfCollarModel (𝓡 3)
      ((M.exterior.truncation M.model).cuspMap M.port) (M.sliceCurve_P2A s) :=
    (((M.exterior.truncation M.model).cuspEmbedding M.port).contMDiff
      (M.sliceCurve_P2A s)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp s hf hc
  have hprod : mfderiv 𝓘(ℝ, ℝ) halfCollarModel M.sliceCurve_P2A s =
      (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s).prod
        (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) (fun _ : ℝ => halfZero) s) :=
    mfderiv_prodMk ((M.smooth s).mdifferentiableAt (by simp)) mdifferentiableAt_const
  have hne : mfderiv 𝓘(ℝ, ℝ) halfCollarModel M.sliceCurve_P2A s (1 : ℝ) ≠ 0 := by
    intro h
    rw [hprod] at h
    exact hv (congrArg Prod.fst h)
  have hinj := ((M.exterior.truncation M.model).cuspEmbedding M.port).isImmersion.mfderiv_injective
    (by simp) (M.sliceCurve_P2A s)
  have : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) M.modelCurve_P2A s (1 : ℝ) =
      mfderiv halfCollarModel (𝓡 3) ((M.exterior.truncation M.model).cuspMap M.port)
        (M.sliceCurve_P2A s) (mfderiv 𝓘(ℝ, ℝ) halfCollarModel M.sliceCurve_P2A s (1 : ℝ)) := by
    have := congrArg (fun L => L (1 : ℝ)) hcomp
    exact this
  rw [this]
  intro h0
  exact hne (hinj (h0.trans (map_zero _).symm))

/-- Step 1 (IMS03): the transported prescribed meridian `M.transported t ht` is a smooth embedded
loop in the sense of `IsSmoothEmbeddedLoop` (smooth, topologically embedded, nowhere-vanishing
velocity). -/
theorem transported_isSmoothEmbeddedLoop_P2A (M : PrescribedCuspMeridianTop_CPQ cores) (t : ℝ)
    (ht : M.exterior.start ≤ t) :
    IsSmoothEmbeddedLoop (E := ThreeSpace) (M.transported t ht) := by
  have hst := M.exterior.after_cores.trans ht
  let T := M.exterior.truncation M.model
  let ψ : cores.domain M.model t → (postStage F.observation t).Carrier :=
    fun x => cores.map M.model t hst x
  have hψ := cores.embedding M.model t hst
  let Aup : Torus → cores.domain M.model t := fun x =>
    ⟨T.cuspMap M.port (x, halfZero), M.slice_mem_domain_P2A t ht x⟩
  let a : ℝ → cores.domain M.model t := fun s => Aup (loopLift M.loop s)
  have hfun : (fun s : ℝ => M.transported t ht (s : loopCircle)) = ψ ∘ a := by
    funext s
    exact M.prescribed t ht (s : loopCircle)
  have ha : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ a :=
    (contMDiff_subtypeVal_comp_iff (I := 𝓘(ℝ, ℝ)) (J := 𝓡 3) (n := ∞)
      (cores.domain M.model t) a).mp M.modelCurve_contMDiff_P2A
  have hAemb : Topology.IsEmbedding Aup := by
    have hcont : Continuous Aup :=
      Continuous.subtype_mk ((T.cuspEmbedding M.port).isEmbedding.continuous.comp
        (continuous_id.prodMk continuous_const)) _
    have hval : Topology.IsEmbedding (Subtype.val ∘ Aup) :=
      (T.cuspEmbedding M.port).isEmbedding.comp (isEmbedding_prodMkLeft halfZero)
    exact (Topology.IsEmbedding.of_comp_iff (Topology.IsEmbedding.subtypeVal)).mp hval
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hψ.contMDiff.comp ha
  · have : (M.transported t ht) = ψ ∘ Aup ∘ M.loop := by
      funext x
      exact M.prescribed t ht x
    rw [this]
    exact hψ.isEmbedding.comp (hAemb.comp M.embedded)
  · intro s
    rw [hfun]
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) a s := (ha s).mdifferentiableAt (by simp)
    have hψd : MDifferentiableAt (𝓡 3) (𝓡 3) ψ (a s) :=
      (hψ.contMDiff (a s)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp s hψd hdiff
    have hinj := hψ.isImmersion.mfderiv_injective (by simp) (a s)
    have hsub : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) a s = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) M.modelCurve_P2A s :=
      (mfderiv_subtypeVal_comp (I := 𝓘(ℝ, ℝ)) (J := 𝓡 3) (cores.domain M.model t) a s).symm
    have h1 := M.modelCurve_mfderiv_ne_zero_P2A s
    have h2 : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) a s (1 : ℝ) ≠ 0 := by rw [hsub]; exact h1
    have e : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (ψ ∘ a) s (1 : ℝ) =
        mfderiv (𝓡 3) (𝓡 3) ψ (a s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) a s (1 : ℝ)) :=
      congrArg (fun L => L (1 : ℝ)) hcomp
    intro h0
    exact h2 (hinj (e.symm.trans (h0.trans (map_zero _).symm)))

end PrescribedCuspMeridianTop_CPQ

end GC.LongTime.CuspP1
