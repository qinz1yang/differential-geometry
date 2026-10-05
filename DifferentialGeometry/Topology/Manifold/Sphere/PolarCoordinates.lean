import DifferentialGeometry.Topology.Manifold.SphereDirection
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Set Metric Manifold Module
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

def spherePolarChart (v : sphere (0 : E) 1) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (sphere (0 : E) 1 × ℝ) E ∞ where
  toFun q := q.2 • (q.1 : E)
  invFun x := (sphereDirection v x, ‖x‖)
  source := {q | 0 < q.2}
  target := {0}ᶜ
  map_source' q hq := smul_ne_zero hq.ne' (ne_zero_of_mem_unit_sphere q.1)
  map_target' x hx := norm_pos_iff.mpr hx
  left_inv' q hq := by
    have hq' : 0 < q.2 := hq
    apply Prod.ext
    · exact sphereDirection_pos_smul v q.1 hq
    · simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hq', norm_eq_of_mem_sphere, mul_one]
  right_inv' x hx := norm_smul_sphereDirection v hx
  open_source := isOpen_lt continuous_const continuous_snd
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun :=
    (contMDiff_snd.smul (contMDiff_coe_sphere.comp contMDiff_fst)).contMDiffOn
  contMDiffOn_invFun := (contMDiffOn_sphereDirection v).prodMk
    (fun x hx => (contDiffAt_norm ℝ hx).contMDiffAt.contMDiffWithinAt)

@[simp] theorem spherePolarChart_apply (v : sphere (0 : E) 1) (p : sphere (0 : E) 1 × ℝ) :
    spherePolarChart (n := n) v p = p.2 • (p.1 : E) := rfl

@[simp] theorem spherePolarChart_symm_apply (v : sphere (0 : E) 1) (x : E) :
    (spherePolarChart (n := n) v).symm x = (sphereDirection v x, ‖x‖) := rfl

@[simp] theorem spherePolarChart_source (v : sphere (0 : E) 1) :
    (spherePolarChart (n := n) v).source = {p | 0 < p.2} := rfl

@[simp] theorem spherePolarChart_target (v : sphere (0 : E) 1) :
    (spherePolarChart (n := n) v).target = {0}ᶜ := rfl

theorem isLocalDiffeomorphAt_sphere_smul (q : sphere (0 : E) 1 × ℝ) (hq : 0 < q.2) :
    IsLocalDiffeomorphAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : sphere (0 : E) 1 × ℝ => p.2 • (p.1 : E)) q :=
  (spherePolarChart q.1).isLocalDiffeomorphAt _ _ ∞ hq

theorem isLocalDiffeomorphAt_chart_sphere_smul
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph 𝓘(ℝ, E) I E N ∞)
    (q : sphere (0 : E) 1 × ℝ) (hq : 0 < q.2) (hc : q.2 • (q.1 : E) ∈ c.source) :
    IsLocalDiffeomorphAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : sphere (0 : E) 1 × ℝ => c (p.2 • (p.1 : E))) q :=
  (isLocalDiffeomorphAt_sphere_smul q hq).comp I N (c.isLocalDiffeomorphAt _ _ ∞ hc)

end DifferentialGeometry.Topology.Manifold
