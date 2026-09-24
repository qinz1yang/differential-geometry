import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamChart
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.InteriorChart
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped Manifold ContDiff Topology

universe u v w

namespace DifferentialGeometry.Topology
namespace ConnectedSumQuotient

abbrev csModel : Type := EuclideanSpace ℝ (Fin 3)
abbrev csSphere : Type := Metric.sphere (0 : csModel) 1

instance instNonemptySeam : Nonempty Seam := by
  have hnorm : ‖(spherePoint (n := 3) (by norm_num) : csModel)‖ = 1 :=
    norm_spherePoint (n := 3) (by norm_num)
  exact ⟨⟨(spherePoint (n := 3) (by norm_num) : csModel), by
    rw [SeamShell]
    exact ⟨by linarith, by linarith⟩⟩⟩

theorem isOpenEmbedding_subtype_val_seam : IsOpenEmbedding (Subtype.val : Seam → csModel) :=
  isOpen_seamShell.isOpenEmbedding_subtypeVal

def seamShellChart : OpenPartialHomeomorph Seam csModel :=
  isOpenEmbedding_subtype_val_seam.toOpenPartialHomeomorph Subtype.val

theorem seamShellChart_apply (x : Seam) : seamShellChart x = (x : csModel) :=
  congrFun (IsOpenEmbedding.toOpenPartialHomeomorph_apply Subtype.val
    isOpenEmbedding_subtype_val_seam) x

theorem seamShellChart_source : seamShellChart.source = univ :=
  IsOpenEmbedding.toOpenPartialHomeomorph_source Subtype.val isOpenEmbedding_subtype_val_seam

theorem seamShellChart_target : seamShellChart.target = SeamShell := by
  rw [seamShellChart, IsOpenEmbedding.toOpenPartialHomeomorph_target]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩


private local instance : Fact (Module.finrank ℝ csModel = 2 + 1) := ⟨by simp⟩

theorem contMDiffAt_unitVecFun_self (x : csModel) (hx : x ≠ 0) :
    ContMDiffAt 𝓘(ℝ, csModel) (𝓡 2) ∞ (fun y : csModel => unitVecFun y) x := by
  set U : TopologicalSpace.Opens csModel := ⟨{y | y ≠ 0}, isOpen_ne⟩ with hU
  have hbase : ContMDiff 𝓘(ℝ, csModel) 𝓘(ℝ, csModel) ∞
      (fun y : U => (‖(y : csModel)‖)⁻¹ • (y : csModel)) := by
    intro y
    exact (contMDiffAt_subtype_iff (U := U) (f := fun z : csModel => (‖z‖)⁻¹ • z)
      (x := y)).mpr (contMDiffAt_iff_contDiffAt.mpr
      (((contDiffAt_norm ℝ y.2).inv (norm_ne_zero_iff.mpr y.2)).smul
        (contDiffAt_id (x := (y : csModel)))))
  have hmem : ∀ y : U, (‖(y : csModel)‖)⁻¹ • (y : csModel) ∈ Metric.sphere (0 : csModel) 1 := by
    intro y
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr y.2)]
  have hsphere := hbase.codRestrict_sphere (n := 2) hmem
  have heq : (Set.codRestrict (fun y : U => (‖(y : csModel)‖)⁻¹ • (y : csModel))
        (Metric.sphere (0 : csModel) 1) hmem :
        U → csSphere) = fun y : U => unitVecFun (y : csModel) := by
    funext y
    rw [unitVecFun_of_ne y.2]
    rfl
  have h1 : ContMDiff 𝓘(ℝ, csModel) (𝓡 2) ∞ (fun y : U => unitVecFun (y : csModel)) := by
    rw [← heq]
    exact hsphere
  exact contMDiffAt_subtype_iff.mp (h1.contMDiffAt (x := (⟨x, hx⟩ : U)))

theorem contMDiffOn_sphereReflectCoe (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    ContMDiffOn 𝓘(ℝ, csModel) 𝓘(ℝ, csModel) ∞
      (fun x : csModel => ((a (unitVecFun x) : csSphere) : csModel)) {x | x ≠ 0} := by
  intro x hx
  have h1 : ContMDiffAt 𝓘(ℝ, csModel) (𝓡 2) ∞ (fun y : csModel => a (unitVecFun y)) x :=
    ContMDiffAt.comp x a.contMDiff.contMDiffAt (contMDiffAt_unitVecFun_self x hx)
  have h2 : ContMDiffAt 𝓘(ℝ, csModel) 𝓘(ℝ, csModel) ∞
      (fun y : csModel => ((a (unitVecFun y) : csSphere) : csModel)) x :=
    ContMDiffAt.comp x (contMDiff_coe_sphere (n := 2)).contMDiffAt h1
  exact h2.contMDiffWithinAt

theorem contDiffOn_reflectMap (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    ContDiffOn ℝ ∞ (reflectMap (a.toHomeomorph)) {x : csModel | x ≠ 0} := by
  refine contMDiffOn_iff_contDiffOn.mp ?_
  intro x hx
  have hcoeff : ContMDiffWithinAt 𝓘(ℝ, csModel) 𝓘(ℝ, ℝ) ∞ (fun y : csModel => 2 - ‖y‖)
      {x : csModel | x ≠ 0} x :=
    (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.sub (contDiffAt_norm ℝ hx))).contMDiffWithinAt
  have hbody := contMDiffOn_sphereReflectCoe a x hx
  exact hcoeff.smul hbody

theorem contDiffOn_reflectMapInv (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    ContDiffOn ℝ ∞ (reflectMapInv (a.toHomeomorph)) {x : csModel | x ≠ 0} := by
  have h := contDiffOn_reflectMap a.symm
  have heq : reflectMapInv (a.toHomeomorph) = reflectMap (a.symm.toHomeomorph) := by
    funext x
    simp [reflectMap, reflectMapInv]
  rw [heq]
  exact h


variable {M : Type*} [TopologicalSpace M] [ChartedSpace csModel M] [IsManifold (𝓡 3) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace csModel N] [IsManifold (𝓡 3) ∞ N]
  [T2Space M] [T2Space N]
  (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
  (a : csSphere ≃ₜ csSphere)

abbrev CSIndex := {f : OpenPartialHomeomorph M csModel // f ∈ atlas csModel M} ⊕
  ({g : OpenPartialHomeomorph N csModel // g ∈ atlas csModel N} ⊕ Unit)

def seamChartX : OpenPartialHomeomorph (ConnectedSumQuotient c d a) csModel :=
  ((isOpenEmbedding_seamMap c d a).toOpenPartialHomeomorph
    (seamMap c d a)).symm.trans seamShellChart

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamChartX_source :
    (seamChartX c d a).source = Set.range (seamMap c d a) := by
  rw [seamChartX, OpenPartialHomeomorph.trans_source, seamShellChart_source, preimage_univ,
    inter_univ, OpenPartialHomeomorph.symm_source]
  exact IsOpenEmbedding.toOpenPartialHomeomorph_target (seamMap c d a)
    (isOpenEmbedding_seamMap c d a)

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamShellChart_inv (x : Seam) :
    ((isOpenEmbedding_seamMap c d a).toOpenPartialHomeomorph (seamMap c d a)).symm
      (seamMap c d a x) = x := by
  rw [← congrFun (IsOpenEmbedding.toOpenPartialHomeomorph_apply (seamMap c d a)
    (isOpenEmbedding_seamMap c d a)) x]
  exact OpenPartialHomeomorph.left_inv _ (Set.mem_univ x)

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamChartX_apply_seamMap (x : Seam) :
    seamChartX c d a (seamMap c d a x) = (x : csModel) := by
  simp only [seamChartX, OpenPartialHomeomorph.trans_apply]
  rw [seamShellChart_inv c d a x, seamShellChart_apply]

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamChartX_symm_apply (x : Seam) :
    (seamChartX c d a).symm (x : csModel) = seamMap c d a x := by
  rw [← seamChartX_apply_seamMap c d a x]
  exact OpenPartialHomeomorph.left_inv _ (by
    rw [seamChartX_source]
    exact Set.mem_range_self x)

def csChart (k : CSIndex (M := M) (N := N)) :
    OpenPartialHomeomorph (ConnectedSumQuotient c d a) csModel :=
  match k with
  | .inl f => (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f.1).symm
  | .inr (.inl g) => (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g.1).symm
  | .inr (.inr _) => seamChartX c d a

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem csChart_inr_inr : csChart c d a (.inr (.inr ())) = seamChartX c d a := rfl

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem csChart_inl (f : {f : OpenPartialHomeomorph M csModel // f ∈ atlas csModel M}) :
    csChart c d a (.inl f) =
      (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f.1).symm := rfl

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem csChart_inr_inl (g : {g : OpenPartialHomeomorph N csModel // g ∈ atlas csModel N}) :
    csChart c d a (.inr (.inl g)) =
      (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g.1).symm := rfl

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem csChart_covers (x : ConnectedSumQuotient c d a) :
    ∃ k : CSIndex (M := M) (N := N), x ∈ (csChart c d a k).source := by
  rcases jointly_surjective c d a x with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · rcases BallChart.interior_boundary_cover c p with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · refine ⟨Sum.inl ⟨chartAt csModel (y : M), chart_mem_atlas csModel (y : M)⟩, ?_⟩
      simpa only [csChart, OpenPartialHomeomorph.symm_source] using
        mem_leftChart_target_of_mem_source c d a (by norm_num : 0 < (3 : ℕ))
          (chartAt csModel (y : M)) (mem_chart_source csModel (y : M))
    · refine ⟨Sum.inr (Sum.inr ()), ?_⟩
      rw [csChart_inr_inr, seamChartX_source]
      have hz : (z : csModel) ∈ SeamShell := by
        rw [SeamShell]
        have h1 : ‖(z : csModel)‖ = 1 := norm_coe_sphere z
        exact ⟨by linarith, by linarith⟩
      refine ⟨⟨(z : csModel), hz⟩, ?_⟩
      rw [seamMap_eq_inl_chart c d a ⟨(z : csModel), hz⟩ (by
        rw [norm_coe_sphere z])]
      refine congrArg (inl c d a) (Subtype.ext ?_)
      rw [BallChart.boundaryMap_val]
  · rcases BallChart.interior_boundary_cover d q with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · refine ⟨Sum.inr (Sum.inl ⟨chartAt csModel (y : N), chart_mem_atlas csModel (y : N)⟩), ?_⟩
      simpa only [csChart, OpenPartialHomeomorph.symm_source] using
        mem_rightChart_target_of_mem_source c d a (by norm_num : 0 < (3 : ℕ))
          (chartAt csModel (y : N)) (mem_chart_source csModel (y : N))
    · refine ⟨Sum.inr (Sum.inr ()), ?_⟩
      rw [csChart_inr_inr, seamChartX_source]
      have hz : (a.symm z : csModel) ∈ SeamShell := by
        rw [SeamShell]
        have h1 : ‖(a.symm z : csModel)‖ = 1 := norm_coe_sphere (a.symm z)
        exact ⟨by linarith, by linarith⟩
      refine ⟨⟨(a.symm z : csModel), hz⟩, ?_⟩
      have hnorm : ‖((⟨(a.symm z : csModel), hz⟩ : Seam) : csModel)‖ = 1 :=
        norm_coe_sphere (a.symm z)
      have hdir : seamDir (⟨(a.symm z : csModel), hz⟩ : Seam) = a.symm z := by
        apply Subtype.ext
        rw [coe_seamDir_eq, norm_coe_sphere (a.symm z)]
        simp
      rw [seamMap_of_one_le c d a _ (le_of_eq hnorm.symm),
        seamLeft_eq_boundary c d a _ hnorm, boundary_eq]
      exact congrArg (inr c d a) (congrArg d.boundaryMap (by rw [hdir, a.apply_symm_apply]))


theorem radialMap_mem_interior {M : Type*} [TopologicalSpace M] [ChartedSpace csModel M] [T2Space M]
    (c : BallChart 3 (𝓡 3) M) {z : csSphere} {r : ℝ}
    (hr : r ∈ Set.Icc 1 2) (h1 : 1 < r) :
    (c.radialMap z r hr : M) ∈ (c.interior : Set M) := by
  change (c.radialMap z r hr : M) ∉ c.chart '' Metric.closedBall 0 1
  rintro ⟨y, hy, heq⟩
  rw [BallChart.radialMap_val] at heq
  have hr0 : 0 ≤ r := le_trans zero_le_one hr.1
  have hsource : r • (z : csModel) ∈ c.chart.source := by
    apply c.closedBall_subset_source
    rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z hr0]
    exact hr.2
  have hyz : y = r • (z : csModel) :=
    c.chart.toPartialEquiv.injOn (c.closedBall_one_subset_source hy) hsource heq
  have hnorm : ‖y‖ = r := by rw [hyz, BallChart.norm_radial z hr0]
  have hy1 : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
  linarith

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem one_le_norm_of_seamMap_mem_leftTarget
    {f : OpenPartialHomeomorph M csModel} {x : Seam}
    (hx : seamMap c d a x ∈ leftTarget c d a f) :
    1 ≤ ‖(x : csModel)‖ := by
  by_contra h
  have hlt : ‖(x : csModel)‖ < 1 := not_le.mp h
  have hr : (2 - ‖(x : csModel)‖) ∈ Set.Icc 1 2 :=
    ⟨by linarith [x.2.2], by linarith [x.2.1]⟩
  have htarget : seamMap c d a x ∈ rightTarget c d a
      (chartAt csModel (d.radialMap (a (seamDir x)) (2 - ‖(x : csModel)‖) hr : N)) := by
    rw [seamMap_of_lt_one c d a x h, seamRight_eq_of_lt_one c d a x hlt]
    refine ⟨_, ⟨mem_chart_source csModel _,
      radialMap_mem_interior d hr (by linarith [x.2.2])⟩, ?_⟩
    exact congrArg (inr c d a) (Subtype.ext rfl)
  exact Set.disjoint_left.mp (disjoint_leftTarget_rightTarget c d a f _) hx htarget

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem norm_lt_one_of_seamMap_mem_rightTarget
    {g : OpenPartialHomeomorph N csModel} {x : Seam}
    (hx : seamMap c d a x ∈ rightTarget c d a g) :
    ‖(x : csModel)‖ < 1 := by
  by_contra h
  have h1 : 1 ≤ ‖(x : csModel)‖ := not_lt.mp h
  rcases lt_or_eq_of_le h1 with hgt | heq
  · have hr : ‖(x : csModel)‖ ∈ Set.Icc 1 2 := ⟨h1, by linarith [x.2.2]⟩
    have htarget : seamMap c d a x ∈ leftTarget c d a
        (chartAt csModel (c.radialMap (seamDir x) ‖(x : csModel)‖ hr : M)) := by
      rw [seamMap_of_one_le c d a x h1, seamLeft_eq_of_one_le c d a x h1]
      refine ⟨_, ⟨mem_chart_source csModel _, radialMap_mem_interior c hr hgt⟩, ?_⟩
      exact congrArg (inl c d a) (Subtype.ext rfl)
    exact Set.disjoint_left.mp (disjoint_leftTarget_rightTarget c d a _ g) htarget hx
  · obtain ⟨q, hq, hqx⟩ := (mem_rightTarget c d a g _).mp hx
    have hbound : seamMap c d a x = inl c d a (c.boundaryMap (seamDir x)) := by
      rw [seamMap_of_one_le c d a x h1, seamLeft_eq_boundary c d a x heq.symm]
    rw [hbound] at hqx
    obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a _ q).mp hqx.symm
    refine (hq.2) ?_
    rw [← hz']
    exact ⟨(a z : csModel), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_coe_sphere]
      norm_num⟩

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem leftChart_symm_seamMap {f : OpenPartialHomeomorph M csModel} {x : Seam}
    (hx : seamMap c d a x ∈ leftTarget c d a f) :
    (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).symm (seamMap c d a x)
      = f (c.chart (x : csModel)) := by
  obtain ⟨p, hp, hpx⟩ := (mem_leftTarget c d a f _).mp hx
  have h1 : 1 ≤ ‖(x : csModel)‖ := one_le_norm_of_seamMap_mem_leftTarget c d a hx
  have hval : (p : M) = c.chart (x : csModel) := by
    have hp' : p = c.radialMap (seamDir x) ‖(x : csModel)‖ ⟨h1, by linarith [x.2.2]⟩ := by
      rw [seamMap_of_one_le c d a x h1, seamLeft_eq_of_one_le c d a x h1] at hpx
      exact (inl_injective c d a hpx).trans (Subtype.ext rfl)
    rw [hp']
    exact radialMap_seamDir_coe c x h1
  rw [← hpx, leftChart_symm_apply_inl c d a (by norm_num : 0 < (3 : ℕ)) f hp]
  exact congrArg f hval

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem rightChart_symm_seamMap {g : OpenPartialHomeomorph N csModel} {x : Seam}
    (hx : seamMap c d a x ∈ rightTarget c d a g) :
    (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm (seamMap c d a x)
      = g (d.chart (reflectMap a (x : csModel))) := by
  obtain ⟨q, hq, hqx⟩ := (mem_rightTarget c d a g _).mp hx
  have hlt : ‖(x : csModel)‖ < 1 := norm_lt_one_of_seamMap_mem_rightTarget c d a hx
  have hval : (q : N) = d.chart (reflectMap a (x : csModel)) := by
    have hq' : q = d.radialMap (a (seamDir x)) (2 - ‖(x : csModel)‖)
        ⟨by linarith [x.2.2], by linarith [x.2.1]⟩ := by
      rw [seamMap_of_lt_one c d a x (not_le.mpr hlt), seamRight_eq_of_lt_one c d a x hlt] at hqx
      exact (inr_injective c d a hqx).trans (Subtype.ext rfl)
    rw [hq']
    exact radialMap_a_seamDir_coe d a x hlt
  rw [← hqx, rightChart_symm_apply_inr c d a (by norm_num : 0 < (3 : ℕ)) g hq]
  exact congrArg g hval


omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamChartX_target : (seamChartX c d a).target = SeamShell := by
  rw [seamChartX, OpenPartialHomeomorph.trans_target, seamShellChart_target,
    OpenPartialHomeomorph.symm_target, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Set.preimage_univ, Set.inter_univ]

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamChartX_symm_apply_of_mem {x : csModel} (hx : x ∈ SeamShell) :
    (seamChartX c d a).symm x = seamMap c d a ⟨x, hx⟩ := by
  have h1 : seamMap c d a ⟨x, hx⟩ ∈ (seamChartX c d a).source := by
    rw [seamChartX_source]
    exact Set.mem_range_self _
  have h2 := OpenPartialHomeomorph.left_inv (seamChartX c d a) h1
  rwa [seamChartX_apply_seamMap c d a ⟨x, hx⟩] at h2

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem chart_mem_of_seamMap_mem_leftTarget {f : OpenPartialHomeomorph M csModel} {x : Seam}
    (hx : seamMap c d a x ∈ leftTarget c d a f) : c.chart (x : csModel) ∈ f.source := by
  obtain ⟨p, hp, hpx⟩ := (mem_leftTarget c d a f _).mp hx
  have h1 : 1 ≤ ‖(x : csModel)‖ := one_le_norm_of_seamMap_mem_leftTarget c d a hx
  have hpeq : p = c.radialMap (seamDir x) ‖(x : csModel)‖ ⟨h1, by linarith [x.2.2]⟩ := by
    rw [seamMap_of_one_le c d a x h1, seamLeft_eq_of_one_le c d a x h1] at hpx
    exact (inl_injective c d a hpx).trans (Subtype.ext rfl)
  rw [hpeq] at hp
  simpa only [radialMap_seamDir_coe c x h1] using hp.1

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem chart_mem_of_seamMap_mem_rightTarget {g : OpenPartialHomeomorph N csModel} {x : Seam}
    (hx : seamMap c d a x ∈ rightTarget c d a g) :
    d.chart (reflectMap a (x : csModel)) ∈ g.source := by
  obtain ⟨q, hq, hqx⟩ := (mem_rightTarget c d a g _).mp hx
  have hlt : ‖(x : csModel)‖ < 1 := norm_lt_one_of_seamMap_mem_rightTarget c d a hx
  have hqeq : q = d.radialMap (a (seamDir x)) (2 - ‖(x : csModel)‖)
      ⟨by linarith [x.2.2], by linarith [x.2.1]⟩ := by
    rw [seamMap_of_lt_one c d a x (not_le.mpr hlt), seamRight_eq_of_lt_one c d a x hlt] at hqx
    exact (inr_injective c d a hqx).trans (Subtype.ext rfl)
  rw [hqeq] at hq
  simpa only [radialMap_a_seamDir_coe d a x hlt] using hq.1

omit [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem contDiffOn_leftChart_trans_leftChart' (f g : OpenPartialHomeomorph M csModel)
    (hf : f ∈ atlas csModel M) (hg : g ∈ atlas csModel M) :
    ContDiffOn ℝ ∞ ((leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).trans
        (leftChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm)
      ((leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).trans
        (leftChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm).source :=
  contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_leftChart_trans_leftChart c d a (by norm_num : 0 < (3 : ℕ)) f g hf hg)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem contDiffOn_rightChart_trans_rightChart' (g h : OpenPartialHomeomorph N csModel)
    (hg : g ∈ atlas csModel N) (hh : h ∈ atlas csModel N) :
    ContDiffOn ℝ ∞ ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans
        (rightChart c d a (by norm_num : 0 < (3 : ℕ)) h).symm)
      ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans
        (rightChart c d a (by norm_num : 0 < (3 : ℕ)) h).symm).source :=
  contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_rightChart_trans_rightChart c d a (by norm_num : 0 < (3 : ℕ)) g h hg hh)

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem contDiffOn_leftChart_trans_rightChart' (f : OpenPartialHomeomorph M csModel)
    (g : OpenPartialHomeomorph N csModel) :
    ContDiffOn ℝ ∞ ((leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).trans
        (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm)
      ((leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).trans
        (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm).source := by
  rw [leftChart_trans_rightChart_source_eq_empty c d a (by norm_num : 0 < (3 : ℕ)) f g]
  exact contDiffOn_empty

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem contDiffOn_rightChart_trans_leftChart' (g : OpenPartialHomeomorph N csModel)
    (f : OpenPartialHomeomorph M csModel) :
    ContDiffOn ℝ ∞ ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans
        (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).symm)
      ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans
        (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).symm).source := by
  rw [rightChart_trans_leftChart_source_eq_empty c d a (by norm_num : 0 < (3 : ℕ)) g f]
  exact contDiffOn_empty

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem contDiffOn_seamChart_trans_seamChart :
    ContDiffOn ℝ ∞ ((seamChartX c d a).symm.trans (seamChartX c d a))
      ((seamChartX c d a).symm.trans (seamChartX c d a)).source := by
  refine contDiffOn_id.congr ?_
  intro x hx
  rw [OpenPartialHomeomorph.trans_source] at hx
  exact OpenPartialHomeomorph.right_inv _ hx.1


omit [IsManifold (𝓡 3) ∞ N] in
theorem contDiffOn_seamChart_trans_leftChart (f : OpenPartialHomeomorph M csModel)
    (hf : f ∈ atlas csModel M) :
    ContDiffOn ℝ ∞ ((seamChartX c d a).symm.trans
        (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).symm)
      ((seamChartX c d a).symm.trans
        (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).symm).source := by
  have hmodel : ContDiffOn ℝ ∞ (fun x : csModel => f (c.chart x))
      (SeamShell ∩ (fun x : csModel => c.chart x) ⁻¹' f.source) := by
    have h1 : ContMDiffOn 𝓘(ℝ, csModel) (𝓡 3) ∞ (fun x : csModel => c.chart x)
        (SeamShell ∩ (fun x : csModel => c.chart x) ⁻¹' f.source) :=
      c.chart.contMDiffOn_toFun.mono (fun x hx => mem_chart_source_of_norm_le_two c (by
        have := hx.1.2
        linarith))
    have h2 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source :=
      contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hf)
    exact contMDiffOn_iff_contDiffOn.mp (h2.comp h1 (fun x hx => hx.2))
  refine (hmodel.mono ?_).congr ?_
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      seamChartX_target] at hx
    refine ⟨hx.1, ?_⟩
    have hx2 : seamMap c d a ⟨x, hx.1⟩ ∈ leftTarget c d a f := by
      have h3 := hx.2
      rw [OpenPartialHomeomorph.symm_source, leftChart_target] at h3
      simp only [Set.mem_preimage] at h3
      rwa [seamChartX_symm_apply_of_mem c d a hx.1] at h3
    exact chart_mem_of_seamMap_mem_leftTarget c d a hx2
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      seamChartX_target, OpenPartialHomeomorph.symm_source, leftChart_target] at hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    have hx2 : seamMap c d a ⟨x, hx.1⟩ ∈ leftTarget c d a f := by
      rw [seamChartX_symm_apply_of_mem c d a hx.1] at hx
      exact hx.2
    rw [OpenPartialHomeomorph.trans_apply, seamChartX_symm_apply_of_mem c d a hx.1,
      leftChart_symm_seamMap c d a hx2]


omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem symm_mem_chart_target_of_leftChart_mem_range {f : OpenPartialHomeomorph M csModel}
    {x : csModel} (hx : x ∈ (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).source)
    (h : leftChart c d a (by norm_num : 0 < (3 : ℕ)) f x ∈ Set.range (seamMap c d a)) :
    f.symm x ∈ c.chart.target := by
  have hs : x ∈ f.target := leftChartSource_subset_target c f hx
  have hu : f.symm x ∈ f.source ∩ (c.interior : Set M) :=
    symm_mem_of_mem_leftChartSource c f x hx
  obtain ⟨z, hz⟩ := h
  set p : c.Punctured := c.interiorToPunctured ⟨f.symm x, hu.2⟩ with hp
  have hpv : (p : M) = f.symm x := rfl
  have h1 : leftChart c d a (by norm_num : 0 < (3 : ℕ)) f x = inl c d a p := by
    rw [leftChart_apply]
    exact congrArg (inl c d a) (Subtype.ext
      ((leftCoord_val_of_mem c (by norm_num : 0 < (3 : ℕ)) f x hx).trans hpv.symm))
  have h2 : seamMap c d a z = inl c d a p := hz ▸ h1
  have hmem : seamMap c d a z ∈ leftTarget c d a f := ⟨p, hu, h2.symm⟩
  have h3 : f (c.chart (z : csModel)) = x := by
    have h4 : (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).symm (seamMap c d a z) = x := by
      rw [h2, ← h1]
      exact (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).left_inv hx
    rw [leftChart_symm_seamMap c d a hmem] at h4
    exact h4
  have harg : c.chart (z : csModel) = f.symm x := by
    have ha : c.chart (z : csModel) ∈ f.source := chart_mem_of_seamMap_mem_leftTarget c d a hmem
    have hb : f.symm x ∈ f.source := hu.1
    rw [← f.left_inv ha, ← f.left_inv hb, h3, f.right_inv hs]
  rw [← harg]
  exact c.chart.toPartialEquiv.map_source (mem_chart_source_of_norm_le_two c (by
    have := z.2.2
    linarith))

omit [IsManifold (𝓡 3) ∞ N] in
theorem contDiffOn_leftChart_trans_seamChart (f : OpenPartialHomeomorph M csModel)
    (hf : f ∈ atlas csModel M) :
    ContDiffOn ℝ ∞ ((leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).trans (seamChartX c d a))
      ((leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).trans (seamChartX c d a)).source := by
  have hcm_mem : ((c.chart.symm).toOpenPartialHomeomorph) ∈
      IsManifold.maximalAtlas (𝓡 3) ∞ M :=
    DifferentialGeometry.PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas
      (I := 𝓡 3) (c.chart.symm)
  have htrans : f.symm.trans ((c.chart.symm).toOpenPartialHomeomorph) ∈
      contDiffGroupoid ∞ (𝓡 3) :=
    StructureGroupoid.compatible_of_mem_maximalAtlas (G := contDiffGroupoid ∞ (𝓡 3))
      (IsManifold.subset_maximalAtlas hf) hcm_mem
  have hmodel : ContDiffOn ℝ ∞
      (fun x : csModel => (f.symm.trans ((c.chart.symm).toOpenPartialHomeomorph)) x)
      (f.symm.trans ((c.chart.symm).toOpenPartialHomeomorph)).source :=
    contMDiffOn_iff_contDiffOn.mp (contMDiffOn_of_mem_contDiffGroupoid htrans)
  refine (hmodel.mono ?_).congr ?_
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [seamChartX_source] at hx2
    rw [OpenPartialHomeomorph.trans_source]
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨leftChartSource_subset_target c f hx1,
      symm_mem_chart_target_of_leftChart_mem_range c d a hx1 hx2⟩
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨hx1, hx2⟩ := hx
    set p : c.Punctured := c.interiorToPunctured
      ⟨f.symm x, (symm_mem_of_mem_leftChartSource c f x hx1).2⟩ with hp
    have hpv : (p : M) = f.symm x := rfl
    have hpreg : p ∈ leftRegion c f :=
      ⟨(symm_mem_of_mem_leftChartSource c f x hx1).1,
        (symm_mem_of_mem_leftChartSource c f x hx1).2⟩
    have h1 : leftChart c d a (by norm_num : 0 < (3 : ℕ)) f x = inl c d a p := by
      rw [leftChart_apply]
      exact congrArg (inl c d a) (Subtype.ext
        ((leftCoord_val_of_mem c (by norm_num : 0 < (3 : ℕ)) f x hx1).trans hpv.symm))
    rw [seamChartX_source] at hx2
    obtain ⟨z, hz⟩ := hx2
    have h2 : seamMap c d a z = inl c d a p := hz ▸ h1
    have hmem : seamMap c d a z ∈ leftTarget c d a f := ⟨p, hpreg, h2.symm⟩
    have hsz : seamChartX c d a (inl c d a p) = (z : csModel) := by
      rw [← h2, seamChartX_apply_seamMap c d a z]
    have hzchart : c.chart (z : csModel) = f.symm x := by
      have h4 : (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).symm (seamMap c d a z) = x := by
        rw [h2, ← h1]
        exact (leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).left_inv hx1
      rw [leftChart_symm_seamMap c d a hmem] at h4
      have ha : c.chart (z : csModel) ∈ f.source := chart_mem_of_seamMap_mem_leftTarget c d a hmem
      have hb : f.symm x ∈ f.source := (symm_mem_of_mem_leftChartSource c f x hx1).1
      rw [← f.left_inv ha, ← f.left_inv hb, h4,
        f.right_inv (leftChartSource_subset_target c f hx1)]
    change ((leftChart c d a (by norm_num : 0 < (3 : ℕ)) f).trans (seamChartX c d a)) x
      = (f.symm.trans ((c.chart.symm).toOpenPartialHomeomorph)) x
    rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply, h1, hsz]
    change (z : csModel) = c.chart.toPartialEquiv.symm (f.symm x)
    rw [← hzchart]
    exact (c.chart.toPartialEquiv.left_inv (mem_chart_source_of_norm_le_two c (by
      have := z.2.2
      linarith))).symm


omit [IsManifold (𝓡 3) ∞ M] in
theorem contDiffOn_seamChart_trans_rightChart (g : OpenPartialHomeomorph N csModel)
    (hg : g ∈ atlas csModel N)
    (hrefl : ContDiffOn ℝ ∞ (reflectMap a) {x : csModel | x ≠ 0}) :
    ContDiffOn ℝ ∞ ((seamChartX c d a).symm.trans
        (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm)
      ((seamChartX c d a).symm.trans
        (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm).source := by
  have hrefl' : ContMDiffOn 𝓘(ℝ, csModel) 𝓘(ℝ, csModel) ∞ (fun x : csModel => reflectMap a x)
      ({x : csModel | x ≠ 0} ∩ (fun x : csModel => reflectMap a x) ⁻¹' d.chart.source) :=
    (contMDiffOn_iff_contDiffOn.mpr hrefl).mono Set.inter_subset_left
  have h2 : ContMDiffOn 𝓘(ℝ, csModel) (𝓡 3) ∞ (fun y : csModel => d.chart y) d.chart.source :=
    d.chart.contMDiffOn_toFun
  have h3 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g g.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hg)
  have h23 : ContMDiffOn 𝓘(ℝ, csModel) (𝓡 3) ∞ (fun x : csModel => d.chart (reflectMap a x))
      (({x : csModel | x ≠ 0} ∩ (fun x : csModel => reflectMap a x) ⁻¹' d.chart.source) ∩
        (fun x : csModel => d.chart (reflectMap a x)) ⁻¹' g.source) :=
    (h2.comp hrefl' (fun x hx => hx.2)).mono Set.inter_subset_left
  have hmodel : ContDiffOn ℝ ∞ (fun x : csModel => g (d.chart (reflectMap a x)))
      (({x : csModel | x ≠ 0} ∩ (fun x : csModel => reflectMap a x) ⁻¹' d.chart.source) ∩
        (fun x : csModel => d.chart (reflectMap a x)) ⁻¹' g.source) :=
    contMDiffOn_iff_contDiffOn.mp (h3.comp h23 (fun x hx => hx.2))
  refine (hmodel.mono ?_).congr ?_
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      seamChartX_target] at hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [SeamShell] at hx1
    have hx2' : seamMap c d a ⟨x, hx1⟩ ∈ rightTarget c d a g := by
      rw [seamChartX_symm_apply_of_mem c d a hx1] at hx2
      rw [OpenPartialHomeomorph.symm_source, rightChart_target] at hx2
      exact hx2
    have hg1 : d.chart (reflectMap a (⟨x, hx1⟩ : Seam)) ∈ g.source :=
      chart_mem_of_seamMap_mem_rightTarget c d a hx2'
    have hsrc : reflectMap a x ∈ d.chart.source := by
      apply mem_chart_source_of_norm_le_two
      rw [norm_reflectMap (by linarith [hx1.2])]
      linarith [hx1.1]
    refine ⟨⟨?_, hsrc⟩, hg1⟩
    intro h0
    rw [h0] at hx1
    norm_num at hx1
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      seamChartX_target] at hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx2' : seamMap c d a ⟨x, hx1⟩ ∈ rightTarget c d a g := by
      rw [seamChartX_symm_apply_of_mem c d a hx1] at hx2
      rw [OpenPartialHomeomorph.symm_source, rightChart_target] at hx2
      exact hx2
    change ((seamChartX c d a).symm.trans
        (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).symm) x
      = g (d.chart (reflectMap a x))
    rw [OpenPartialHomeomorph.trans_apply,
      seamChartX_symm_apply_of_mem c d a hx1, rightChart_symm_seamMap c d a hx2']



omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] in
theorem mem_inter_of_rightChart_trans_mem {g : OpenPartialHomeomorph N csModel} {x : csModel}
    (hx : x ∈ ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans (seamChartX c d a)).source) :
    x ∈ (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).source ∧
      (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g) x ∈ Set.range (seamMap c d a) := by
  rw [OpenPartialHomeomorph.trans_source] at hx
  simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
  refine ⟨hx.1, ?_⟩
  rw [seamChartX_source] at hx
  exact hx.2

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem exists_seamMap_rightChart {g : OpenPartialHomeomorph N csModel} {x : csModel}
    (hx1 : x ∈ (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).source)
    (hx2 : (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g) x ∈ Set.range (seamMap c d a)) :
    ∃ z : Seam, (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g) x = seamMap c d a z ∧
      ‖(z : csModel)‖ < 1 ∧ g.symm x = d.chart (reflectMap a (z : csModel)) ∧
      d.chart.toPartialEquiv.symm (g.symm x) = reflectMap a (z : csModel) := by
  obtain ⟨z, hz⟩ := hx2
  have hreg : g.symm x ∈ g.source ∩ (d.interior : Set N) :=
    symm_mem_of_mem_rightChartSource d g x hx1
  have hq : g.symm x ∉ d.chart '' Metric.ball (0 : csModel) 1 :=
    fun hm => hreg.2 (Set.image_mono Metric.ball_subset_closedBall hm)
  let q : d.Punctured := ⟨g.symm x, hq⟩
  have hqx : (rightChart c d a (by norm_num : 0 < (3 : ℕ)) g) x = inr c d a q := by
    rw [rightChart_apply]
    exact congrArg (inr c d a)
      (Subtype.ext (rightCoord_val_of_mem d (by norm_num : 0 < (3 : ℕ)) g x hx1))
  have hmem : seamMap c d a z ∈ rightTarget c d a g := ⟨q, hreg, (hqx ▸ hz).symm⟩
  have hlt : ‖(z : csModel)‖ < 1 := norm_lt_one_of_seamMap_mem_rightTarget c d a hmem
  have hzsrc : reflectMap a (z : csModel) ∈ d.chart.source := by
    apply mem_chart_source_of_norm_le_two
    rw [norm_reflectMap (by linarith [z.2.2])]
    linarith [z.2.1]
  have hq' : d.chart (reflectMap a (z : csModel)) ∉ d.chart '' Metric.ball (0 : csModel) 1 :=
    chart_mem_punctured d hzsrc (by rw [norm_reflectMap (by linarith [z.2.2])]; linarith [z.2.2])
  let q' : d.Punctured := ⟨d.chart (reflectMap a (z : csModel)), hq'⟩
  have hz1 : seamMap c d a z = inr c d a q' := by
    rw [seamMap_of_lt_one c d a z (not_le.mpr hlt), seamRight_eq_of_lt_one c d a z hlt]
    refine congrArg (inr c d a) (Subtype.ext ?_)
    change (d.radialMap (a (seamDir z)) (2 - ‖(z : csModel)‖) _ : N) =
      d.chart (reflectMap a (z : csModel))
    exact radialMap_a_seamDir_coe d a z hlt
  have hqq : q = q' := inr_injective c d a (hqx.symm.trans (hz.symm.trans hz1))
  have hqqv : g.symm x = d.chart (reflectMap a (z : csModel)) := congrArg Subtype.val hqq
  refine ⟨z, hz.symm, hlt, hqqv, ?_⟩
  rw [hqqv]
  exact d.chart.toPartialEquiv.left_inv hzsrc

omit [IsManifold (𝓡 3) ∞ M] in
theorem contDiffOn_rightChart_trans_seamChart (g : OpenPartialHomeomorph N csModel)
    (hg : g ∈ atlas csModel N)
    (hreflInv : ContDiffOn ℝ ∞ (reflectMapInv a) {x : csModel | x ≠ 0}) :
    ContDiffOn ℝ ∞ ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans (seamChartX c d a))
      ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans (seamChartX c d a)).source := by
  have hcm_mem : ((d.chart.symm).toOpenPartialHomeomorph) ∈
      IsManifold.maximalAtlas (𝓡 3) ∞ N :=
    DifferentialGeometry.PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas
      (I := 𝓡 3) (d.chart.symm)
  have htrans : g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph) ∈
      contDiffGroupoid ∞ (𝓡 3) :=
    StructureGroupoid.compatible_of_mem_maximalAtlas (G := contDiffGroupoid ∞ (𝓡 3))
      (IsManifold.subset_maximalAtlas hg) hcm_mem
  have hbase : ContDiffOn ℝ ∞
      (fun x : csModel => (g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)) x)
      (g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)).source :=
    contMDiffOn_iff_contDiffOn.mp (contMDiffOn_of_mem_contDiffGroupoid htrans)
  have hmodel : ContDiffOn ℝ ∞
      (fun x : csModel => reflectMapInv a
        ((g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)) x))
      ((g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)).source ∩
        (fun x : csModel => (g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)) x) ⁻¹'
          {y : csModel | y ≠ 0}) := by
    have hri : ContMDiffOn 𝓘(ℝ, csModel) 𝓘(ℝ, csModel) ∞ (fun y : csModel => reflectMapInv a y)
        {y : csModel | y ≠ 0} := contMDiffOn_iff_contDiffOn.mpr hreflInv
    have hm0 : ContMDiffOn 𝓘(ℝ, csModel) 𝓘(ℝ, csModel) ∞
        (fun x : csModel => (g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)) x)
        ((g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)).source ∩
          (fun x : csModel => (g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)) x) ⁻¹'
            {y : csModel | y ≠ 0}) :=
      (contMDiffOn_iff_contDiffOn.mpr hbase).mono Set.inter_subset_left
    exact contMDiffOn_iff_contDiffOn.mp (hri.comp hm0 (fun x hx => hx.2))
  refine (hmodel.mono ?_).congr ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inter_of_rightChart_trans_mem c d a hx
    obtain ⟨z, hz, hlt, hqv, hz3⟩ := exists_seamMap_rightChart c d a hx1 hx2
    have hzsrc : reflectMap a (z : csModel) ∈ d.chart.source := by
      apply mem_chart_source_of_norm_le_two
      rw [norm_reflectMap (by linarith [z.2.2])]
      linarith [z.2.1]
    refine ⟨⟨rightChartSource_subset_target d g hx1, ?_⟩, ?_⟩
    · change g.symm x ∈ d.chart.target
      rw [hqv]
      exact d.chart.toPartialEquiv.map_source hzsrc
    · change (g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)) x ≠ 0
      change d.chart.toPartialEquiv.symm (g.symm x) ≠ 0
      rw [hz3]
      intro h0
      have hnorm := norm_reflectMap (a := a) (x := (z : csModel)) (by linarith [z.2.2])
      rw [h0, norm_zero] at hnorm
      linarith [hlt]
  · intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inter_of_rightChart_trans_mem c d a hx
    obtain ⟨z, hz, hlt, hqv, hz3⟩ := exists_seamMap_rightChart c d a hx1 hx2
    change ((rightChart c d a (by norm_num : 0 < (3 : ℕ)) g).trans (seamChartX c d a)) x
      = reflectMapInv a ((g.symm.trans ((d.chart.symm).toOpenPartialHomeomorph)) x)
    rw [OpenPartialHomeomorph.trans_apply, hz, seamChartX_apply_seamMap c d a z]
    change (z : csModel) = reflectMapInv a (d.chart.toPartialEquiv.symm (g.symm x))
    rw [hz3]
    exact (reflectMapInv_reflectMap a z).symm


/-- The chart family of the connected-sum atlas, as a bundled function. -/
def csChartFamily : CSIndex (M := M) (N := N) →
    OpenPartialHomeomorph (ConnectedSumQuotient c d a) csModel :=
  fun k => csChart c d a k

def csAtlas : Set (OpenPartialHomeomorph (ConnectedSumQuotient c d a) csModel) :=
  Set.range (csChartFamily c d a)

@[reducible] noncomputable def csChartedSpace :
    ChartedSpace csModel (ConnectedSumQuotient c d a) where
  atlas := csAtlas c d a
  chartAt x := csChartFamily c d a (Classical.choose (csChart_covers c d a x))
  mem_chart_source x := Classical.choose_spec (csChart_covers c d a x)
  chart_mem_atlas x := ⟨Classical.choose (csChart_covers c d a x), rfl⟩

theorem csIsManifold (hrefl : ContDiffOn ℝ ∞ (reflectMap a) {x : csModel | x ≠ 0})
    (hreflInv : ContDiffOn ℝ ∞ (reflectMapInv a) {x : csModel | x ≠ 0}) :
    let _ := csChartedSpace c d a
    IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d a) := by
  let _ := csChartedSpace c d a
  apply isManifold_of_contDiffOn (𝓡 3) ∞
  intro e e' he he'
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := he'
  rcases i with f | (g | u) <;> rcases j with f' | (g' | u') <;>
    simp only [csChartFamily, csChart,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
      Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  · exact contDiffOn_leftChart_trans_leftChart' c d a f.1 f'.1 f.2 f'.2
  · exact contDiffOn_leftChart_trans_rightChart' c d a f.1 g'.1
  · exact contDiffOn_leftChart_trans_seamChart c d a f.1 f.2
  · exact contDiffOn_rightChart_trans_leftChart' c d a g.1 f'.1
  · exact contDiffOn_rightChart_trans_rightChart' c d a g.1 g'.1 g.2 g'.2
  · exact contDiffOn_rightChart_trans_seamChart c d a g.1 g.2 hreflInv
  · exact contDiffOn_seamChart_trans_leftChart c d a f'.1 f'.2
  · exact contDiffOn_seamChart_trans_rightChart c d a g'.1 g'.2 hrefl
  · exact contDiffOn_seamChart_trans_seamChart c d a

theorem exists_chartedSpace_isManifold_of_diffeomorph
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    ∃ C : ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph),
      letI := C; IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph) :=
  ⟨csChartedSpace c d aD.toHomeomorph,
    csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)⟩

end ConnectedSumQuotient

end DifferentialGeometry.Topology
