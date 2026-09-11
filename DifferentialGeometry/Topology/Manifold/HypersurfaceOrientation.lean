import Mathlib.Geometry.Manifold.Instances.Real
import DifferentialGeometry.Topology.Manifold.BoundaryOrientationVariation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback

set_option autoImplicit false
noncomputable section
open Set Function Filter Module Manifold TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private def surfaceBasis : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
private def surfaceIndex : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M] [IsManifold (𝓡 2) ∞ M]

private def surfaceDerivative (f : M → E3) (p : M) : E2 →L[ℝ] E3 :=
  mfderiv (𝓡 2) (𝓡 3) f p

def hypersurfaceNormalFrame (f N : M → E3) (p : M) : (ℝ × E2) →L[ℝ] E3 :=
  (ContinuousLinearMap.fst ℝ ℝ E2).smulRight (N p) +
    (surfaceDerivative f p).comp (ContinuousLinearMap.snd ℝ ℝ E2)

omit [IsManifold (𝓡 2) ∞ M] in
theorem hypersurfaceNormalFrame_apply (f N : M → E3) (p : M) (v : ℝ × E2) :
    let D : E2 →L[ℝ] E3 := mfderiv (𝓡 2) (𝓡 3) f p
    hypersurfaceNormalFrame f N p v = v.1 • N p + D v.2 := rfl

def hypersurfaceNormalFrameEquiv (f N : M → E3)
    (h : ∀ p, Bijective (hypersurfaceNormalFrame f N p)) (p : M) : (ℝ × E2) ≃L[ℝ] E3 :=
  (LinearEquiv.ofBijective (hypersurfaceNormalFrame f N p).toLinearMap (h p)).toContinuousLinearEquiv

private theorem derivative_in_chart (f : M → E3) (p x : M) (hx : x ∈ (chartAt E2 p).source) :
    inTangentCoordinates (𝓡 2) (𝓡 3) id f (fun y => (surfaceDerivative f y)) p x =
      (surfaceDerivative f x).comp
        ((preferredChartTangentEquiv (𝓡 2) p x hx).symm : E2 →L[ℝ] E2) := by
  have hy : f x ∈ (chartAt E3 (f p)).source := Set.mem_univ _
  have h := inTangentCoordinates_eq_mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3)
    (f := id) (g := f) (ϕ := mfderiv (𝓡 2) (𝓡 3) f) hx hy
  have hc : (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (f p)) (f x) : E3 →L[ℝ] E3) = ContinuousLinearMap.id ℝ E3 := by
    rw [extChartAt_model_space_eq_id]
    change (mfderiv (𝓡 3) (𝓡 3) (id : E3 → E3) (f x) : E3 →L[ℝ] E3) = _
    rw [mfderiv_id]
    rfl
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : E2 →L[ℝ] E3 => A v) h
  change inTangentCoordinates (𝓡 2) (𝓡 3) id f (fun y => (surfaceDerivative f y)) p x v =
    (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (f p)) (f x) : E3 →L[ℝ] E3)
      ((surfaceDerivative f x)
        (mfderivWithin (𝓡 2) (𝓡 2) (extChartAt (𝓡 2) p).symm (range (𝓡 2)) (extChartAt (𝓡 2) p x) v)) at hv
  rw [hc] at hv
  exact hv.trans (congrArg (surfaceDerivative f x)
    (preferredChartTangentEquiv_symm_apply (𝓡 2) p x hx v).symm)

private theorem derivative_in_chart_continuousAt (f : M → E3)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (p : M) :
    ContinuousAt (fun x : (chartAt E2 p).source =>
      (surfaceDerivative f x.val).comp
        ((preferredChartTangentEquiv (𝓡 2) p x.val x.property).symm : E2 →L[ℝ] E2))
      (⟨p, mem_chart_source E2 p⟩ : (chartAt E2 p).source) := by
  have h : ContinuousAt (inTangentCoordinates (𝓡 2) (𝓡 3) id f (fun y => (surfaceDerivative f y)) p) p :=
    (hf.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have he : (fun x : (chartAt E2 p).source =>
      (surfaceDerivative f x.val).comp
        ((preferredChartTangentEquiv (𝓡 2) p x.val x.property).symm : E2 →L[ℝ] E2)) =
      (fun x : (chartAt E2 p).source => inTangentCoordinates (𝓡 2) (𝓡 3) id f (fun y => (surfaceDerivative f y)) p x.val) := by
    funext x
    exact (derivative_in_chart f p x.val x.property).symm
  rw [he]
  exact h.comp (continuous_subtype_val.continuousAt
    (x := (⟨p, mem_chart_source E2 p⟩ : (chartAt E2 p).source)))

private def normalFrameInChart (f N : M → E3)
    (h : ∀ p, Bijective (hypersurfaceNormalFrame f N p)) (p : M) (x : (chartAt E2 p).source) :
    (ℝ × E2) ≃L[ℝ] E3 :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (preferredChartTangentEquiv (𝓡 2) p x.val x.property).symm).trans
      (hypersurfaceNormalFrameEquiv f N h x.val)

private theorem normalFrameInChart_continuousAt (f N : M → E3)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hN : Continuous N)
    (h : ∀ p, Bijective (hypersurfaceNormalFrame f N p)) (p : M) :
    ContinuousAt (fun x : (chartAt E2 p).source => (normalFrameInChart f N h p x : (ℝ × E2) →L[ℝ] E3))
      (⟨p, mem_chart_source E2 p⟩ : (chartAt E2 p).source) := by
  have he : (fun x : (chartAt E2 p).source => (normalFrameInChart f N h p x : (ℝ × E2) →L[ℝ] E3)) =
      (fun x : (chartAt E2 p).source =>
        (ContinuousLinearMap.fst ℝ ℝ E2).smulRight (N x.val) +
        ((surfaceDerivative f x.val).comp
          ((preferredChartTangentEquiv (𝓡 2) p x.val x.property).symm : E2 →L[ℝ] E2)).comp
            (ContinuousLinearMap.snd ℝ ℝ E2)) := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact (((ContinuousLinearMap.smulRightL ℝ (ℝ × E2) E3 (ContinuousLinearMap.fst ℝ ℝ E2)).continuous.continuousAt).comp
    (hN.comp continuous_subtype_val).continuousAt).add
    ((derivative_in_chart_continuousAt f hf p).clm_comp continuousAt_const)

private def hypersurfaceOrientationField (f N : M → E3)
    (h : ∀ p, Bijective (hypersurfaceNormalFrame f N p)) (o : Orientation ℝ E3 (Fin 3))
    (p : M) : Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) :=
  Orientation.reindex ℝ E2 surfaceIndex
    (normalFirstOrientation (hypersurfaceNormalFrameEquiv f N h p).toLinearEquiv surfaceBasis o)

private theorem hypersurface_chart_representation (f N : M → E3)
    (h : ∀ p, Bijective (hypersurfaceNormalFrame f N p)) (o : Orientation ℝ E3 (Fin 3))
    (p : M) (x : (chartAt E2 p).source) :
    Orientation.map _ (preferredChartTangentEquiv (𝓡 2) p x.val x.property).toLinearEquiv
      (hypersurfaceOrientationField f N h o x.val) =
      Orientation.reindex ℝ E2 surfaceIndex
        (normalFirstOrientation (normalFrameInChart f N h p x).toLinearEquiv surfaceBasis o) := by
  have hchange := normalFirstOrientation_change_boundary
    (hypersurfaceNormalFrameEquiv f N h x.val).toLinearEquiv
    (preferredChartTangentEquiv (𝓡 2) p x.val x.property).symm.toLinearEquiv surfaceBasis surfaceBasis o
  have hm : ∀ (A : E2 ≃ₗ[ℝ] E2) (q : Orientation ℝ E2 (Fin 2)),
      Orientation.map (Fin (Module.finrank ℝ E2)) A (Orientation.reindex ℝ E2 surfaceIndex q) =
        Orientation.reindex ℝ E2 surfaceIndex (Orientation.map (Fin 2) A q) := by
    intro A q
    induction q using Module.Ray.ind
    rfl
  rw [hypersurfaceOrientationField, hm]
  exact congrArg (Orientation.reindex ℝ E2 surfaceIndex) hchange.symm

def hypersurfaceSmoothOrientation (f N : M → E3)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hN : Continuous N)
    (h : ∀ p, Bijective (hypersurfaceNormalFrame f N p)) (o : Orientation ℝ E3 (Fin 3)) :
    SmoothOrientation (𝓡 2) M := by
  apply smoothOrientationOfLocalRepresentations (𝓡 2) (hypersurfaceOrientationField f N h o)
  intro p
  let S : Opens M := ⟨(chartAt E2 p).source, (chartAt E2 p).open_source⟩
  let pS : S := ⟨p, mem_chart_source E2 p⟩
  let g : S → Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) := fun x =>
    Orientation.map _ (preferredChartTangentEquiv (𝓡 2) p x.val x.property).toLinearEquiv
      (hypersurfaceOrientationField f N h o x.val)
  have hg : ∀ᶠ x in 𝓝 pS, g x = g pS := by
    have he := normalFirstOrientation_eventually_eq (normalFrameInChart f N h p) surfaceBasis pS
      (normalFrameInChart_continuousAt f N hf hN h p) o
    filter_upwards [he] with x hx
    exact (hypersurface_chart_representation f N h o p x).trans
      ((congrArg (Orientation.reindex ℝ E2 surfaceIndex) hx).trans
        (hypersurface_chart_representation f N h o p pS).symm)
  obtain ⟨U, hU, hp, hloc⟩ := locallyConstant_neighborhood_of_eventually_eq S pS g hg
  exact ⟨U, hU, hp, hloc⟩

theorem hypersurfaceSmoothOrientation_apply (f N : M → E3)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hN : Continuous N)
    (h : ∀ p, Bijective (hypersurfaceNormalFrame f N p)) (o : Orientation ℝ E3 (Fin 3)) (p : M) :
    (hypersurfaceSmoothOrientation f N hf hN h o).val p =
      Orientation.reindex ℝ E2 surfaceIndex
        (normalFirstOrientation (hypersurfaceNormalFrameEquiv f N h p).toLinearEquiv surfaceBasis o) := rfl
end DifferentialGeometry.Topology.Manifold
