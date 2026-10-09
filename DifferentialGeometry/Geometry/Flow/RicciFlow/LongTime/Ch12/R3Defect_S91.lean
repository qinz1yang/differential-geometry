import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RicciNormDefect_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DuhamelWindow_S57

set_option autoImplicit false

noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem defectJet0_apply_S91 {D : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := M) D)
    (h : SmoothRiemannianMetric (𝓡 3) M) (r : ℝ) (x : M) (slots : Fin 2 → TangentSpace (𝓡 3) x) :
    defectJet_S57 S h 0 r x slots =
      (S.base.metric r).inner x (slots 0) (slots 1) +
        2 * r * ricciTensor (S.base.metric r) x (slots 0) (slots 1) := by
  have e1 : CheegerGromovCompactness.metricCovDeriv (I := 𝓡 3) (S.base.metric r) h 0 x slots =
      (S.base.metric r).inner x (slots 0) (slots 1) := by
    simp [CheegerGromovCompactness.metricCovDeriv, Tensor0SBundle.metricTensorField]
  have e2 : nablaRicReal (I := 𝓡 3) (fun _ s => S.base.metric s) h 0 0 r x slots =
      ricciTensor (S.base.metric r) x (slots 0) (slots 1) := by
    rw [← metricRicciAt_apply_eq_ricciTensor]
    unfold nablaRicReal ricCovTower
    have hv : vec2 (slots 0) (slots 1) = slots := by
      funext a; fin_cases a <;> rfl
    rw [hv]
    change ((CovariantDerivative.ricciSection (I := 𝓡 3) (M := M)
      (leviCivitaConnectionOfMetric (S.base.metric r)) _ x).domDomCongr (acEquiv 0)) slots = _
    rw [CovariantDerivative.ricciSection_apply]
    rfl
  have e3 : defectJet_S57 S h 0 r x slots = CheegerGromovCompactness.metricCovDeriv (I := 𝓡 3) (S.base.metric r) h 0 x slots +
      (2 * r) * nablaRicReal (I := 𝓡 3) (fun _ s => S.base.metric s) h 0 0 r x slots := rfl
  rw [e3, e1, e2]

/-- polarisation: a symmetric `B` with `|B(w,w)| ≤ c h(w,w)` has `|B(e_i,e_j)| ≤ c` on an `h`-orthonormal basis. -/
theorem abs_basis_le_of_quad_S91 {V : Type*} [AddCommGroup V] [Module ℝ V] (B hh : V → V → ℝ)
    (hBs : ∀ v w, B v w = B w v) (hhs : ∀ v w, hh v w = hh w v)
    (hBa : ∀ u v w, B (u + v) w = B u w + B v w) (hBa' : ∀ u v w, B u (v + w) = B u v + B u w)
    (hBn : ∀ u v w, B (u - v) w = B u w - B v w) (hBn' : ∀ u v w, B u (v - w) = B u v - B u w)
    (hha : ∀ u v w, hh (u + v) w = hh u w + hh v w) (hha' : ∀ u v w, hh u (v + w) = hh u v + hh u w)
    (hhn : ∀ u v w, hh (u - v) w = hh u w - hh v w) (hhn' : ∀ u v w, hh u (v - w) = hh u v - hh u w)
    {c : ℝ} (hq : ∀ w, |B w w| ≤ c * hh w w) (a b : V) (haa : hh a a = 1) (hbb : hh b b = 1)
    (hab : hh a b = 0) : |B a b| ≤ c := by
  have hba : hh b a = 0 := by rw [hhs, hab]
  have gp : hh (a + b) (a + b) = 2 := by rw [hha, hha', hha']; simp [haa, hbb, hab, hba]; norm_num
  have gm : hh (a - b) (a - b) = 2 := by rw [hhn, hhn', hhn']; simp [haa, hbb, hab, hba]; norm_num
  have bp : B (a + b) (a + b) = B a a + 2 * B a b + B b b := by
    rw [hBa, hBa', hBa', hBs b a]; ring
  have bm : B (a - b) (a - b) = B a a - 2 * B a b + B b b := by
    rw [hBn, hBn', hBn', hBs b a]; ring
  have h1 := hq (a + b)
  have h2 := hq (a - b)
  have h3 := hq a
  have h4 := hq b
  rw [gp, bp] at h1
  rw [gm, bm] at h2
  rw [haa] at h3
  rw [hbb] at h4
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

end GC.LongTime.Ch12
