import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Metric.RadialTranslation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def endTranslationDomain (s : ℝ) : Opens E3 :=
  ⟨{x | transitionEnd < ‖x‖ ∧ transitionEnd < ‖x‖ + s},
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_const (continuous_norm.add continuous_const))⟩

@[simp] theorem mem_endTranslationDomain (s : ℝ) (x : E3) :
    x ∈ endTranslationDomain s ↔
      transitionEnd < ‖x‖ ∧ transitionEnd < ‖x‖ + s := Iff.rfl

theorem endTranslationDomain_subset_source (s : ℝ) :
    (endTranslationDomain s : Set E3) ⊆ (radialTranslationDiffeomorph s).source := by
  intro x hx
  change max 0 (-s) < ‖x‖
  apply max_lt
  · exact transitionEnd_pos.trans hx.1
  · linarith [transitionEnd_pos, hx.2]

theorem endTranslationDiffeomorph_norm (s : ℝ) (x : E3)
    (hx : x ∈ endTranslationDomain s) :
    ‖radialTranslationDiffeomorph s x‖ = ‖x‖ + s :=
  norm_radialTranslation s (endTranslationDomain_subset_source s hx)

theorem endTranslationDiffeomorph_metric_inner (s : ℝ) (x : E3)
    (hx : x ∈ endTranslationDomain s) (v w : E3) :
    metric.inner x v w =
      metric.inner (radialTranslationDiffeomorph s x)
        (mfderiv (𝓡 3) (𝓡 3) (radialTranslationDiffeomorph s) x v)
        (mfderiv (𝓡 3) (𝓡 3) (radialTranslationDiffeomorph s) x w) := by
  have hy : transitionEnd ≤ ‖radialTranslation s x‖ := by
    rw [norm_radialTranslation s (endTranslationDomain_subset_source s hx)]
    exact hx.2.le
  change metric.inner x v w =
    metric.inner (radialTranslation s x)
      (mfderiv (𝓡 3) (𝓡 3) (radialTranslation s) x v)
      (mfderiv (𝓡 3) (𝓡 3) (radialTranslation s) x w)
  rw [mfderiv_eq_fderiv]
  calc
    _ = radialBilinearField (fun _ => Real.sqrt 2) x v w :=
      metric_inner_cylindrical hx.1.le v w
    _ = radialBilinearField (fun _ => Real.sqrt 2) (radialTranslation s x)
        (fderiv ℝ (radialTranslation s) x v) (fderiv ℝ (radialTranslation s) x w) :=
      (radialBilinearField_radialTranslation s (Real.sqrt 2)
        (endTranslationDomain_subset_source s hx) v w).symm
    _ = _ := (metric_inner_cylindrical hy _ _).symm

def endTranslationImage (s : ℝ) : Opens E3 :=
  ⟨(radialTranslationDiffeomorph s : E3 → E3) '' (endTranslationDomain s : Set E3),
    image_opens_isOpen _ (endTranslationDomain_subset_source s)⟩

def endTranslation (s : ℝ) :
    endTranslationDomain s ≃ₘ⟮𝓡 3, 𝓡 3⟯ endTranslationImage s :=
  PartialDiffeomorph.toOpensDiffeo (radialTranslationDiffeomorph s)
    (endTranslationDomain_subset_source s)

@[simp] theorem endTranslation_apply (s : ℝ) (x : endTranslationDomain s) :
    (endTranslation s x : E3) = radialTranslationDiffeomorph s (x : E3) := rfl

theorem endTranslation_mfderiv (s : ℝ) (x : endTranslationDomain s)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x v =
      mfderiv (𝓡 3) (𝓡 3) (radialTranslationDiffeomorph s) (x : E3) v :=
  PartialDiffeomorph.mfderiv_toOpensDiffeo _
    (endTranslationDomain_subset_source s) x v

theorem endTranslation_metric_inner (s : ℝ) (x : endTranslationDomain s)
    (v w : TangentSpace (𝓡 3) x) :
    metric.inner (x : E3) v w =
      metric.inner (endTranslation s x : E3)
        (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x v)
        (mfderiv (𝓡 3) (𝓡 3) (endTranslation s) x w) := by
  rw [endTranslation_mfderiv, endTranslation_mfderiv, endTranslation_apply]
  exact endTranslationDiffeomorph_metric_inner s x x.property v w

theorem endTranslation_norm (s : ℝ) (x : endTranslationDomain s) :
    ‖(endTranslation s x : E3)‖ = ‖(x : E3)‖ + s :=
  endTranslationDiffeomorph_norm s x x.property

theorem endTranslationImage_subset_end (s : ℝ) :
    (endTranslationImage s : Set E3) ⊆ {x | transitionEnd < ‖x‖} := by
  rintro y ⟨x, hx, rfl⟩
  change transitionEnd < ‖radialTranslationDiffeomorph s x‖
  rw [endTranslationDiffeomorph_norm s x hx]
  exact hx.2

theorem mem_endTranslationDomain_to_fixed_radius {x : E3} (hx : transitionEnd < ‖x‖) :
    x ∈ endTranslationDomain (transitionEnd + 2 - ‖x‖) := by
  exact ⟨hx, by linarith⟩

theorem endTranslationDiffeomorph_norm_to_fixed_radius {x : E3}
    (hx : transitionEnd < ‖x‖) :
    ‖radialTranslationDiffeomorph (transitionEnd + 2 - ‖x‖) x‖ = transitionEnd + 2 := by
  rw [endTranslationDiffeomorph_norm _ _ (mem_endTranslationDomain_to_fixed_radius hx)]
  ring

end DifferentialGeometry.PDE.RicciFlow.StandardCap
