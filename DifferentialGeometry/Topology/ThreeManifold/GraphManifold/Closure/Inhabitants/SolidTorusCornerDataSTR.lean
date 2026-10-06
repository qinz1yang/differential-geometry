import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRimsConsumerSTR
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerLocalJN74

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7b part 1: the local data of the corner facts

The descended face equation `b(t) = 4 t (1 - t)` (`bE_STR`; `b' = ±4` at the endpoints `t = 0, 1`),
the open patch `P = {‖q‖² > 9/10, |Re q - κ| < 1/100}` of the circle base (it contains both rim base
points, and over it the cutoff is `1`, so that the ball ratio is `λ₁ (κ - u) = 4 t (1 - t)`,
`four_t_STR`), the open set `N` of the circle domain over `P` (inside the edge source and the
residual buffer), and the descent data `Tb = 15/16 - ‖q‖²`, `hb = ratioP`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_CornerDataSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CornerDataSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## The descended equation on the edge base -/

/-- The descended face equation `b(t) = 4 t (1 - t)`. -/
def bE_STR (c : rows_STR.edge.Base) : ℝ := 4 * coordE_STR c * (1 - coordE_STR c)

def bAmb_STR (w : EuclideanSpace ℝ (Fin 1)) : ℝ := 4 * w 0 * (1 - w 0)

theorem bE_eq_STR (c : rows_STR.edge.Base) : bE_STR c = bAmb_STR c.val := rfl

theorem contDiff_bAmb_STR : ContDiff ℝ ∞ bAmb_STR := by
  have hL : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 1) => w 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
  exact (contDiff_const.mul hL).mul (contDiff_const.sub hL)

theorem contMDiff_bE_STR : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ bE_STR :=
  contDiff_bAmb_STR.contMDiff.comp contMDiff_subtype_val

theorem mfderiv_edge_STR {g : EuclideanSpace ℝ (Fin 1) → ℝ}
    {g' : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ} (c : rows_STR.edge.Base) (v : EuclideanSpace ℝ (Fin 1))
    (hv : v = c.val) (hg : HasFDerivAt g g' v) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun y : rows_STR.edge.Base => g y.val) c = g' := by
  have h1 := DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) g
    (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))) ⟨c.val, trivial⟩
  have h2 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) g v = g' := by
    rw [mfderiv_eq_fderiv]
    exact hg.fderiv
  subst hv
  exact h1.trans h2

theorem mfderiv_bE_ne_STR (e : rows_STR.edge.EdgeEnd) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) bE_STR e.1 ≠ 0 := by
  have hτ := edgeEnd_val_STR e
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 1)
  let v : EuclideanSpace ℝ (Fin 1) := e.1.val
  have hL : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 1) => w 0) L v := L.hasFDerivAt
  have hd := (hL.const_mul (4 : ℝ)).mul (hL.const_sub (1 : ℝ))
  have hm := mfderiv_edge_STR (g := bAmb_STR) e.1 v rfl hd
  intro h
  have hz : ((4 * v 0) • -L + (1 - v 0) • (4 : ℝ) • L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) =
      0 := hm.symm.trans h
  have h2 := DFunLike.congr_fun hz (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  have hv0 : coordE_STR e.1 = v 0 := rfl
  rw [hv0] at hτ
  have h3 : 4 * (1 - 2 * v 0) = 0 := by
    simp [L] at h2
    linarith
  rcases hτ with hv | hv <;> (rw [hv] at h3; norm_num at h3)

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
