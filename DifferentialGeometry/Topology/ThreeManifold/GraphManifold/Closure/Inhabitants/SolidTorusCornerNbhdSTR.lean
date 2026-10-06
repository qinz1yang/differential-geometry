import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCornerDataSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7b part 2: the patch, the neighbourhood and the descent data

The patch `patch_STR = {‖q‖² > 9/10, |Re q - 4/5| < 1/100}` of the circle base and
`N_STR = proj⁻¹(patch)` in the circle domain. On `N_STR` the point lies in the edge source, the
cutoff of the ball ratio is `1` and so `ratioL = 4 t (1 - t)` (`ratioL_eq_b_STR`); the descent data
of an endpoint is `Tb = 15/16 - ‖q‖²`, `hb = ratioP(q)` (`descent_STR`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_CornerNbhdSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CornerNbhdSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-- The open patch of the circle base around the rim circle `‖q‖² = 15/16`, `u = κ`. -/
def patch_STR : TopologicalSpace.Opens rows_STR.circle.Base :=
  ⟨{c | 9 / 10 < ‖vOf_STR c‖ ^ 2 ∧ |reL_STR (vOf_STR c) - 4 / 5| < 1 / 100},
    by
    have h1 : Continuous fun c : rows_STR.circle.Base => ‖vOf_STR c‖ ^ 2 :=
      (continuous_norm.comp contMDiff_vOf_STR.continuous).pow 2
    have h2 : Continuous fun c : rows_STR.circle.Base => |reL_STR (vOf_STR c) - 4 / 5| :=
      continuous_abs.comp ((reL_STR.continuous.comp contMDiff_vOf_STR.continuous).sub
        continuous_const)
    exact (isOpen_lt continuous_const h1).inter (isOpen_lt h2 continuous_const)⟩

/-- The neighbourhood of the rim fibres in the circle domain. -/
def nbhd_STR : Set rows_STR.circle.domain := rows_STR.circle.proj ⁻¹' (patch_STR : Set _)

theorem nbhd_open_STR : IsOpen nbhd_STR :=
  patch_STR.isOpen.preimage rows_STR.circle.proj.continuous

theorem second_proj_STR (x : rows_STR.circle.domain) :
    sphereSecond x.val.val = qOfBase_STR (rows_STR.circle.proj x).1 :=
  (mem_fibre_STR.1 (⟨x, rfl, rfl⟩ : x.val ∈ rows_STR.circle.fibre (rows_STR.circle.proj x))).2

theorem nbhd_facts_STR (x : rows_STR.circle.domain) (hx : x ∈ nbhd_STR) :
    9 / 10 < ‖sphereSecond x.val.val‖ ^ 2 ∧ |(sphereSecond x.val.val).re - 4 / 5| < 1 / 100 := by
  have h1 : 9 / 10 < ‖vOf_STR (rows_STR.circle.proj x)‖ ^ 2 := hx.1
  have h2 : |reL_STR (vOf_STR (rows_STR.circle.proj x)) - 4 / 5| < 1 / 100 := hx.2
  rw [second_proj_STR x]
  rw [norm_q_sq_STR, ← re_q_STR] at *
  exact ⟨h1, h2⟩

theorem nbhd_edgeParent_STR (x : rows_STR.circle.domain) (hx : x ∈ nbhd_STR) :
    x.val ∈ edgeParent_STR := by
  obtain ⟨h1, h2⟩ := nbhd_facts_STR x hx
  have hn := norm_sphereFirst_sq_add x.val.val
  refine ⟨by linarith, ?_⟩
  have h3 := (abs_lt.1 h2).2
  by_contra hcon
  have h4 := not_lt.1 hcon
  have h5 := norm_nonneg (sphereSecond x.val.val)
  nlinarith

theorem nbhd_edgeSource_STR (x : rows_STR.circle.domain) (hx : x ∈ nbhd_STR) :
    x.val ∈ rows_STR.edge.source :=
  (stageGeometry_STR ballZeroDomainsL_STR).edge.mem_restrictParent_of
    (nbhd_edgeParent_STR x hx) trivial

theorem nbhd_height_STR (x : rows_STR.circle.domain) (hx : x ∈ nbhd_STR) :
    X135Radial.height x.val < -(4 / 5 : ℝ) := by
  obtain ⟨h1, -⟩ := nbhd_facts_STR x hx
  have h := norm_second_sq_STR x.val
  linarith

/-- On the neighbourhood the ball ratio is `4 t (1 - t)`. -/
theorem ratioL_eq_b_STR (x : rows_STR.circle.domain) (hx : x ∈ nbhd_STR) :
    ratioL_STR x.val = 4 * tOf_STR (sphereSecond x.val.val) *
      (1 - tOf_STR (sphereSecond x.val.val)) := by
  obtain ⟨h1, h2⟩ := nbhd_facts_STR x hx
  have hy := nbhd_edgeParent_STR x hx
  have hk := kap_lt_norm_of_edgeParent_STR hy
  have hre : (sphereSecond x.val.val).re < ‖sphereSecond x.val.val‖ := hy.2
  have hcut : cut_STR (sphereSecond x.val.val) = 1 :=
    cut_eq_one_STR (by have := (abs_lt.1 h2).2; norm_num [kap_STR]; linarith) (by linarith)
  change lamMix_STR (sphereSecond x.val.val) * ((4 / 5 : ℝ) - (sphereSecond x.val.val).re) = _
  rw [lam1_eq_of_cut_STR hcut]
  exact (four_t_STR hk hre).symm

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
