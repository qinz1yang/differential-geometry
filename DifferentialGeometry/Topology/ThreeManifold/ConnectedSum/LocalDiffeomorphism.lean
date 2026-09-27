import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SmoothStructure
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace DifferentialGeometry.Topology
namespace ConnectedSumQuotient

abbrev hn3 : 0 < (3 : ℕ) := by norm_num

abbrev K := Metric.sphere (0 : csModel) 1 × collarInterval

def rad (p : K) : csModel := (1 + (p.2 : ℝ)) • (p.1 : csModel)

theorem norm_rad (p : K) : ‖rad p‖ = 1 + (p.2 : ℝ) := by
  rw [rad, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [p.2.2.1]), norm_coe_sphere,
    mul_one]

theorem rad_mem_SeamShell (p : K) : rad p ∈ SeamShell := by
  rw [SeamShell, Set.mem_ofPred_eq, norm_rad]
  constructor <;> linarith [p.2.2.1, p.2.2.2]

theorem contMDiff_rad : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ rad := by
  have h1 : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : K => (1 : ℝ) + (p.2 : ℝ)) :=
    contMDiff_const.add (contMDiff_subtype_val.comp (ContMDiff.snd (f := id) contMDiff_id))
  have h2 : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, csModel) ∞
      (fun p : K => (p.1 : csModel)) :=
    contMDiff_coe_sphere.comp (ContMDiff.fst (f := id) contMDiff_id)
  exact h1.smul h2

theorem rad_ne_zero (p : K) : rad p ≠ 0 := by
  have hmem := rad_mem_SeamShell p
  intro h
  rw [h] at hmem
  norm_num [SeamShell] at hmem

theorem seamDir_rad (p : K) :
    seamDir (⟨rad p, rad_mem_SeamShell p⟩ : Seam) = p.1 := by
  apply Subtype.ext
  rw [coe_seamDir_eq, norm_rad]
  change (1 + (p.2 : ℝ))⁻¹ • rad p = (p.1 : csModel)
  rw [rad, smul_smul, inv_mul_cancel₀ (by linarith [p.2.2.1] : (1 + (p.2 : ℝ)) ≠ 0), one_smul]

theorem unitVecFun_rad (p : K) : unitVecFun (rad p) = p.1 := by
  rw [unitVecFun_of_ne (rad_ne_zero p)]
  apply Subtype.ext
  rw [unitVec_val, norm_rad]
  change (1 + (p.2 : ℝ))⁻¹ • rad p = (p.1 : csModel)
  rw [rad, smul_smul, inv_mul_cancel₀ (by linarith [p.2.2.1] : (1 + (p.2 : ℝ)) ≠ 0), one_smul]

section Collar


variable {M : Type*} [TopologicalSpace M] [ChartedSpace csModel M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace csModel N] [IsManifold (𝓡 3) ∞ N]
  [T2Space N]
  (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
  (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace csModel M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace csModel N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N]

variable (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
variable (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
variable [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
variable [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)]

omit [T2Space M] in
theorem contMDiffOn_chart_of_mem (f : OpenPartialHomeomorph M csModel)
    (hf : f ∈ atlas csModel M) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source :=
  contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hf)

omit [T2Space M] in
theorem contMDiffOn_chart_symm_of_mem (f : OpenPartialHomeomorph M csModel)
    (hf : f ∈ atlas csModel M) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hf)

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem contMDiffOn_leftChart (f : OpenPartialHomeomorph M csModel)
    (hmem : (leftChart c d aD.toHomeomorph hn3 f).symm ∈
      atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (leftChart c d aD.toHomeomorph hn3 f)
      (leftChart c d aD.toHomeomorph hn3 f).source :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hmem)

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem contMDiffOn_leftChart_symm (f : OpenPartialHomeomorph M csModel)
    (hmem : (leftChart c d aD.toHomeomorph hn3 f).symm ∈
      atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (leftChart c d aD.toHomeomorph hn3 f).symm
      (leftChart c d aD.toHomeomorph hn3 f).target :=
  contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hmem)

omit [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem interiorLeft_isLocalDiffeomorph
    (hL : ∀ (f : OpenPartialHomeomorph M csModel), f ∈ atlas csModel M →
      (leftChart c d aD.toHomeomorph hn3 f).symm ∈
        atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (interiorLeft c d aD) := by
  classical
  intro x
  set f := chartAt csModel (x : M) with hfdef
  have hfmem : f ∈ atlas csModel M := chart_mem_atlas csModel (x : M)
  have hxsrc : (x : M) ∈ f.source := mem_chart_source csModel (x : M)
  set L := leftChart c d aD.toHomeomorph hn3 f with hLdef
  have hLmem : L.symm ∈ atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph) := hL f hfmem
  have hLsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L L.source :=
    contMDiffOn_leftChart c d aD f hLmem
  have hLsymmsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L.symm L.target :=
    contMDiffOn_leftChart_symm c d aD f hLmem
  have hfsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source :=
    contMDiffOn_chart_of_mem f hfmem
  have hfsymmsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target :=
    contMDiffOn_chart_symm_of_mem f hfmem
  have hsrcmem : ∀ q : ConnectedSumQuotient c d aD.toHomeomorph, q ∈ L.target →
      L.symm q ∈ leftChartSource c f := by
    intro q hq
    have hqs : q ∈ L.symm.source := by
      rw [OpenPartialHomeomorph.symm_source]
      exact hq
    have hlt := L.symm.map_source hqs
    rw [OpenPartialHomeomorph.symm_target] at hlt
    exact hlt
  let src : Set c.interior := {u | (u : M) ∈ f.source}
  let w : ConnectedSumQuotient c d aD.toHomeomorph → c.interior := fun q =>
    if h : q ∈ L.target then
      ⟨f.symm (L.symm q), ((mem_leftChartSource c f (L.symm q)).mp (hsrcmem q h)).2⟩
    else x
  have hLsrc_of : ∀ u : c.interior, (u : M) ∈ f.source → f u.1 ∈ L.source := by
    intro u hu
    change f (u : M) ∈ leftChartSource c f
    exact Set.mem_image_of_mem f ⟨hu, u.2⟩
  have hftgt_of : ∀ q : ConnectedSumQuotient c d aD.toHomeomorph, q ∈ L.target →
      L.symm q ∈ f.target := by
    intro q hq
    exact ((mem_leftChartSource c f (L.symm q)).mp (hsrcmem q hq)).1
  have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun u : c.interior => L (f (u : M))) src := by
    have h1 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun y : M => L (f y))
        (f.source ∩ (c.interior : Set M)) :=
      hLsmooth.comp (hfsmooth.mono inter_subset_left)
        (fun y hy => hLsrc_of ⟨y, hy.2⟩ hy.1)
    have h2 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val : c.interior → M) src :=
      (contMDiff_subtype_val (U := c.interior)).contMDiffOn.mono (subset_univ _)
    exact h1.comp h2 (fun u hu => ⟨hu, u.2⟩)
  have hgood : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun q : ConnectedSumQuotient c d aD.toHomeomorph => f.symm (L.symm q)) L.target :=
    hfsymmsmooth.comp hLsymmsmooth (fun q hq => hftgt_of q hq)
  have hregood : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun q : ConnectedSumQuotient c d aD.toHomeomorph => f.symm (L.symm q)) L.target := hgood
  have hcomp_inv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ w) L.target :=
    hregood.congr (fun q hq => by
      simp only [Function.comp_apply, w, dif_pos hq, Subtype.coe_mk])
  have hinv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ w L.target := by
    intro q hq
    exact (ContMDiffWithinAt.subtypeVal_comp_iff (U := c.interior) w L.target q).mp
      (hcomp_inv q hq)
  refine ⟨{ toFun := fun u : c.interior => L (f (u : M))
            invFun := w
            source := src
            target := L.target
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := ?_
            open_target := L.open_target
            contMDiffOn_toFun := hcomp
            contMDiffOn_invFun := hinv }, hxsrc, ?_⟩
  · intro u hu
    exact L.map_source (hLsrc_of u hu)
  · intro q hq
    simp only [w, dif_pos hq]
    exact f.map_target (hftgt_of q hq)
  · intro u hu
    have hLu : f (u : M) ∈ L.source := hLsrc_of u hu
    apply Subtype.ext
    simp only [w, dif_pos (L.map_source hLu), Subtype.coe_mk]
    rw [L.left_inv hLu, f.left_inv hu]
  · intro q hq
    simp only [w, dif_pos hq]
    rw [f.right_inv (hftgt_of q hq), L.right_inv hq]
  · exact f.open_source.preimage continuous_subtype_val
  · intro u hu
    have hmem : f (u : M) ∈ leftChartSource c f := hLsrc_of u hu
    change interiorLeft c d aD u = L (f (u : M))
    rw [interiorLeft, Function.comp_apply, leftChart_apply]
    refine congrArg (inl c d aD.toHomeomorph) (Subtype.ext ?_)
    rw [BallChart.interiorToPunctured_val, leftCoord_val_of_mem c hn3 f (f (u : M)) hmem,
      f.left_inv hu]

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] in
theorem contMDiffOn_rightChart (g : OpenPartialHomeomorph N csModel)
    (hmem : (rightChart c d aD.toHomeomorph hn3 g).symm ∈
      atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (rightChart c d aD.toHomeomorph hn3 g)
      (rightChart c d aD.toHomeomorph hn3 g).source :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hmem)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] in
theorem contMDiffOn_rightChart_symm (g : OpenPartialHomeomorph N csModel)
    (hmem : (rightChart c d aD.toHomeomorph hn3 g).symm ∈
      atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (rightChart c d aD.toHomeomorph hn3 g).symm
      (rightChart c d aD.toHomeomorph hn3 g).target :=
  contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hmem)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem interiorRight_isLocalDiffeomorph
    (hL : ∀ (g : OpenPartialHomeomorph N csModel), g ∈ atlas csModel N →
      (rightChart c d aD.toHomeomorph hn3 g).symm ∈
        atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (interiorRight c d aD) := by
  classical
  intro x
  set g := chartAt csModel (x : N) with hgdef
  have hgmem : g ∈ atlas csModel N := chart_mem_atlas csModel (x : N)
  have hxsrc : (x : N) ∈ g.source := mem_chart_source csModel (x : N)
  set L := rightChart c d aD.toHomeomorph hn3 g with hLdef
  have hLmem : L.symm ∈ atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph) := hL g hgmem
  have hLsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L L.source :=
    contMDiffOn_rightChart c d aD g hLmem
  have hLsymmsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L.symm L.target :=
    contMDiffOn_rightChart_symm c d aD g hLmem
  have hgsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g g.source :=
    contMDiffOn_chart_of_mem g hgmem
  have hgsymmsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g.symm g.target :=
    contMDiffOn_chart_symm_of_mem g hgmem
  have hsrcmem : ∀ q : ConnectedSumQuotient c d aD.toHomeomorph, q ∈ L.target →
      L.symm q ∈ rightChartSource d g := by
    intro q hq
    have hqs : q ∈ L.symm.source := by
      rw [OpenPartialHomeomorph.symm_source]
      exact hq
    have hlt := L.symm.map_source hqs
    rw [OpenPartialHomeomorph.symm_target] at hlt
    exact hlt
  let src : Set d.interior := {u | (u : N) ∈ g.source}
  let w : ConnectedSumQuotient c d aD.toHomeomorph → d.interior := fun q =>
    if h : q ∈ L.target then
      ⟨g.symm (L.symm q), ((mem_rightChartSource d g (L.symm q)).mp (hsrcmem q h)).2⟩
    else x
  have hLsrc_of : ∀ u : d.interior, (u : N) ∈ g.source → g u.1 ∈ L.source := by
    intro u hu
    change g (u : N) ∈ rightChartSource d g
    exact Set.mem_image_of_mem g ⟨hu, u.2⟩
  have hgtgt_of : ∀ q : ConnectedSumQuotient c d aD.toHomeomorph, q ∈ L.target →
      L.symm q ∈ g.target := by
    intro q hq
    exact ((mem_rightChartSource d g (L.symm q)).mp (hsrcmem q hq)).1
  have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun u : d.interior => L (g (u : N))) src := by
    have h1 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun y : N => L (g y))
        (g.source ∩ (d.interior : Set N)) :=
      hLsmooth.comp (hgsmooth.mono inter_subset_left)
        (fun y hy => hLsrc_of ⟨y, hy.2⟩ hy.1)
    have h2 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val : d.interior → N) src :=
      (contMDiff_subtype_val (U := d.interior)).contMDiffOn.mono (subset_univ _)
    exact h1.comp h2 (fun u hu => ⟨hu, u.2⟩)
  have hgood : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun q : ConnectedSumQuotient c d aD.toHomeomorph => g.symm (L.symm q)) L.target :=
    hgsymmsmooth.comp hLsymmsmooth (fun q hq => hgtgt_of q hq)
  have hcomp_inv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ w) L.target :=
    hgood.congr (fun q hq => by
      simp only [Function.comp_apply, w, dif_pos hq, Subtype.coe_mk])
  have hinv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ w L.target := by
    intro q hq
    exact (ContMDiffWithinAt.subtypeVal_comp_iff (U := d.interior) w L.target q).mp
      (hcomp_inv q hq)
  refine ⟨{ toFun := fun u : d.interior => L (g (u : N))
            invFun := w
            source := src
            target := L.target
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := ?_
            open_target := L.open_target
            contMDiffOn_toFun := hcomp
            contMDiffOn_invFun := hinv }, hxsrc, ?_⟩
  · intro u hu
    exact L.map_source (hLsrc_of u hu)
  · intro q hq
    simp only [w, dif_pos hq]
    exact g.map_target (hgtgt_of q hq)
  · intro u hu
    have hLu : g (u : N) ∈ L.source := hLsrc_of u hu
    apply Subtype.ext
    simp only [w, dif_pos (L.map_source hLu), Subtype.coe_mk]
    rw [L.left_inv hLu, g.left_inv hu]
  · intro q hq
    simp only [w, dif_pos hq]
    rw [g.right_inv (hgtgt_of q hq), L.right_inv hq]
  · exact g.open_source.preimage continuous_subtype_val
  · intro u hu
    have hmem : g (u : N) ∈ rightChartSource d g := hLsrc_of u hu
    change interiorRight c d aD u = L (g (u : N))
    rw [interiorRight, Function.comp_apply, rightChart_apply]
    refine congrArg (inr c d aD.toHomeomorph) (Subtype.ext ?_)
    rw [BallChart.interiorToPunctured_val, rightCoord_val_of_mem d hn3 g (g (u : N)) hmem,
      g.left_inv hu]

noncomputable def chartLin (v : Metric.sphere (0 : csModel) 1) :
    (ℝ ∙ (v : csModel))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr

theorem chartAt_sphere_eq (v x : Metric.sphere (0 : csModel) 1) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) v) x =
      chartLin (-v) (stereoToFun (-(v : csModel)) (x : csModel)) := by
  have : Fact (Module.finrank ℝ csModel = 2 + 1) := ⟨by simp⟩
  simp only [chartAt, chartLin]
  rfl

theorem extChartAt_sphere_apply (v x : Metric.sphere (0 : csModel) 1) :
    (extChartAt (𝓡 2) v) x =
      chartLin (-v) (stereoToFun (-(v : csModel)) (x : csModel)) := by
  rw [extChartAt_coe]
  simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq]
  exact chartAt_sphere_eq v x

theorem unitVecFun_contMDiffWithinAt (y₀ : csModel) (hy₀ : y₀ ∈ SeamShell) :
    ContMDiffWithinAt (𝓡 3) (𝓡 2) ∞ unitVecFun SeamShell y₀ := by
  classical
  have : Fact (Module.finrank ℝ csModel = 2 + 1) := ⟨by simp⟩
  have hy₀ne : y₀ ≠ 0 := by
    intro h
    rw [h] at hy₀
    norm_num [SeamShell] at hy₀
  have hcont : ContinuousWithinAt unitVecFun SeamShell y₀ :=
    (continuousOn_unitVecFun.mono (fun y hy => by
      intro h
      rw [h] at hy
      norm_num [SeamShell] at hy)).continuousWithinAt hy₀
  rw [contMDiffWithinAt_iff_of_mem_source (I' := (𝓡 2)) (x := y₀) (y := unitVecFun y₀)
    (mem_chart_source (EuclideanSpace ℝ (Fin 3)) y₀)
    (mem_chart_source (EuclideanSpace ℝ (Fin 2)) (unitVecFun y₀))]
  refine ⟨hcont, ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, Set.preimage_id,
    modelWithCornersSelf_coe, Set.inter_univ, Set.range_id, id_eq]
  set v : Metric.sphere (0 : csModel) 1 := unitVecFun y₀ with hv
  let F : csModel → EuclideanSpace ℝ (Fin 2) :=
    fun y => chartLin (-v) (stereoToFun (-(v : csModel)) ((‖y‖)⁻¹ • y))
  have hveq : (v : csModel) = (‖y₀‖)⁻¹ • y₀ := by
    rw [hv, unitVecFun_of_ne hy₀ne, unitVec_val]
  have hinner : innerSL ℝ (-(v : csModel)) ((‖y₀‖)⁻¹ • y₀) ≠ (1 : ℝ) := by
    have h2' : innerSL ℝ (-(v : csModel)) ((‖y₀‖)⁻¹ • y₀) = -1 := by
      rw [innerSL_apply_apply, ← hveq, inner_neg_left, inner_self_eq_norm_sq_to_K,
        norm_coe_sphere v]
      norm_num
    rw [h2']
    norm_num
  have h1 : ContDiffWithinAt ℝ ∞ (fun y : csModel => (‖y‖)⁻¹) SeamShell y₀ :=
    ((contDiffAt_norm ℝ hy₀ne).contDiffWithinAt).inv (norm_ne_zero_iff.mpr hy₀ne)
  have h2 : ContDiffWithinAt ℝ ∞ (fun y : csModel => (‖y‖)⁻¹ • y) SeamShell y₀ :=
    h1.smul contDiffWithinAt_id
  have hcont_s : ContinuousWithinAt (fun y : csModel => (‖y‖)⁻¹ • y) SeamShell y₀ :=
    (ContinuousWithinAt.inv₀ continuous_norm.continuousWithinAt
      (norm_ne_zero_iff.mpr hy₀ne)).smul continuousWithinAt_id
  have hcont_inner : ContinuousWithinAt
      (fun y : csModel => innerSL ℝ (-(v : csModel)) ((‖y‖)⁻¹ • y)) SeamShell y₀ := by
    have hc : ContinuousAt (fun u : csModel => innerSL ℝ (-(v : csModel)) u)
        ((‖y₀‖)⁻¹ • y₀) :=
      ((innerSL ℝ (-(v : csModel))).continuous.continuousAt)
    exact ContinuousAt.comp_continuousWithinAt
      (g := fun u : csModel => innerSL ℝ (-(v : csModel)) u)
      (f := fun y : csModel => (‖y‖)⁻¹ • y) hc hcont_s
  have hev : ∀ᶠ y in 𝓝[SeamShell] y₀,
      innerSL ℝ (-(v : csModel)) ((‖y‖)⁻¹ • y) ≠ 1 :=
    hcont_inner.eventually_ne hinner
  let s' : Set csModel :=
    SeamShell ∩ {y : csModel | innerSL ℝ (-(v : csModel)) ((‖y‖)⁻¹ • y) ≠ 1}
  have hs'mem : s' ∈ 𝓝[SeamShell] y₀ := Filter.inter_mem self_mem_nhdsWithin hev
  have hself : SeamShell ∈ 𝓝[s'] y₀ :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => hy.1)
  have h2' : ContDiffWithinAt ℝ ∞ (fun y : csModel => (‖y‖)⁻¹ • y) s' y₀ :=
    h2.mono_of_mem_nhdsWithin hself
  have hstereo : ContDiffWithinAt ℝ ∞ (fun u : csModel => stereoToFun (-(v : csModel)) u)
      {u : csModel | innerSL ℝ (-(v : csModel)) u ≠ 1} ((‖y₀‖)⁻¹ • y₀) :=
    (contDiffOn_stereoToFun (v := -(v : csModel)) (n := ∞)).contDiffWithinAt hinner
  have hcomp : ContDiffWithinAt ℝ ∞
      (fun y : csModel => stereoToFun (-(v : csModel)) ((‖y‖)⁻¹ • y)) s' y₀ :=
    ContDiffWithinAt.comp (f := fun y : csModel => (‖y‖)⁻¹ • y) (x := y₀) hstereo h2'
      (fun y hy => hy.2)
  have hchart : ContDiffWithinAt ℝ ∞ F s' y₀ := by
    have hlin : ContDiffWithinAt ℝ ∞
        (fun u : (ℝ ∙ (-(v : csModel)))ᗮ => chartLin (-v) u) Set.univ
        (stereoToFun (-(v : csModel)) ((‖y₀‖)⁻¹ • y₀)) :=
      (chartLin (-v)).contDiff.contDiffWithinAt
    exact ContDiffWithinAt.comp (f := fun y : csModel => stereoToFun (-(v : csModel))
      ((‖y‖)⁻¹ • y)) (x := y₀) hlin hcomp (fun y _ => Set.mem_univ _)
  have hF : ContDiffWithinAt ℝ ∞ F SeamShell y₀ := hchart.mono_of_mem_nhdsWithin hs'mem
  have hFeq : ∀ y ∈ SeamShell, (extChartAt (𝓡 2) v) (unitVecFun y) = F y := by
    intro y hy
    have hyne : y ≠ 0 := by
      intro h
      rw [h] at hy
      norm_num [SeamShell] at hy
    rw [extChartAt_sphere_apply, unitVecFun_of_ne hyne, unitVec_val]
  refine hF.congr_of_eventuallyEq ?_ ?_
  · exact eventually_nhdsWithin_iff.mpr (Eventually.of_forall (fun y hy => hFeq y hy))
  · exact hFeq y₀ hy₀

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem radialMap_congr {c : BallChart 3 (𝓡 3) M} {z₁ z₂ : Metric.sphere (0 : csModel) 1}
    {r₁ r₂ : ℝ} (hz : z₁ = z₂) (hr : r₁ = r₂)
    (h₁ : r₁ ∈ Set.Icc 1 2) (h₂ : r₂ ∈ Set.Icc 1 2) :
    c.radialMap z₁ r₁ h₁ = c.radialMap z₂ r₂ h₂ := by
  subst hz
  subst hr
  rfl

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem collarMap_eq_seamChartX (p : K) :
    collarMap c d aD p =
      (seamChartX c d aD.toHomeomorph).symm (rad p) := by
  rw [seamChartX_symm_apply c d aD.toHomeomorph (⟨rad p, rad_mem_SeamShell p⟩ : Seam)]
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · have hn1 : (1 : ℝ) ≤ 1 + (p.2 : ℝ) := by linarith
    have hlt32 : (1 + (p.2 : ℝ)) < 3 / 2 := by linarith [p.2.2.2]
    rw [collarMap_of_nonneg c d aD p ht,
      seamMap_of_one_le c d aD.toHomeomorph ⟨rad p, rad_mem_SeamShell p⟩ (by
        rw [norm_rad]; exact hn1),
      seamLeft_eq_of_one_le c d aD.toHomeomorph ⟨rad p, rad_mem_SeamShell p⟩ (by
        rw [norm_rad]; exact hn1)]
    refine congrArg (inl c d aD.toHomeomorph) ?_
    refine radialMap_congr ?_ ?_ _ _
    · exact (seamDir_rad p).symm
    · exact (norm_rad p).symm
  · have hlt1 : (1 + (p.2 : ℝ)) < 1 := by linarith
    have hgt12 : (1 / 2 : ℝ) < 1 + (p.2 : ℝ) := by linarith [p.2.2.1]
    rw [collarMap_of_neg c d aD p (lt_of_not_ge ht),
      seamMap_of_lt_one c d aD.toHomeomorph ⟨rad p, rad_mem_SeamShell p⟩
        (by rw [norm_rad]; exact not_le.mpr hlt1),
      seamRight_eq_of_lt_one c d aD.toHomeomorph ⟨rad p, rad_mem_SeamShell p⟩
        (by rw [norm_rad]; exact hlt1)]
    refine congrArg (inr c d aD.toHomeomorph) ?_
    refine radialMap_congr ?_ ?_ _ _
    · rw [Diffeomorph.coe_toHomeomorph, seamDir_rad]
    · rw [norm_rad]
      ring

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem collarMap_mem_range (p : K) :
    collarMap c d aD p ∈ Set.range (seamMap c d aD.toHomeomorph) :=
  ⟨⟨rad p, rad_mem_SeamShell p⟩, by
    rw [collarMap_eq_seamChartX c d aD p]
    exact (seamChartX_symm_apply c d aD.toHomeomorph ⟨rad p, rad_mem_SeamShell p⟩).symm⟩

variable (hseam : seamChartX c d aD.toHomeomorph ∈
  atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph))

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem contMDiffOn_seamChartX (hseam : seamChartX c d aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (seamChartX c d aD.toHomeomorph)
      (seamChartX c d aD.toHomeomorph).source :=
  contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hseam)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem contMDiffOn_seamChartX_symm (hseam : seamChartX c d aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (seamChartX c d aD.toHomeomorph).symm
      (seamChartX c d aD.toHomeomorph).target :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := ∞) hseam)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem seamChartX_mem_SeamShell {q : ConnectedSumQuotient c d aD.toHomeomorph}
    (hq : q ∈ Set.range (seamMap c d aD.toHomeomorph)) :
    seamChartX c d aD.toHomeomorph q ∈ SeamShell := by
  have hsrc : q ∈ (seamChartX c d aD.toHomeomorph).source := by
    rwa [seamChartX_source]
  have h := (seamChartX c d aD.toHomeomorph).map_source hsrc
  rwa [seamChartX_target] at h

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem contMDiffOn_collarMap (hseam : seamChartX c d aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (collarMap c d aD) Set.univ := by
  have h1 : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun p : K => (seamChartX c d aD.toHomeomorph).symm (rad p)) Set.univ := by
    refine (contMDiffOn_seamChartX_symm c d aD hseam).comp contMDiff_rad.contMDiffOn ?_
    intro p _
    rw [seamChartX_target]
    exact rad_mem_SeamShell p
  exact h1.congr (fun p _ => collarMap_eq_seamChartX c d aD p)

noncomputable def collarParam (q : ConnectedSumQuotient c d aD.toHomeomorph) : collarInterval := by
  classical
  exact
    if h : q ∈ Set.range (seamMap c d aD.toHomeomorph) then
      ⟨‖seamChartX c d aD.toHomeomorph q‖ - 1, by
        have hw := seamChartX_mem_SeamShell c d aD h
        change ‖seamChartX c d aD.toHomeomorph q‖ - 1 ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2)
        exact ⟨by linarith [hw.1], by linarith [hw.2]⟩⟩
    else
      ⟨0, by
        change (0 : ℝ) ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2)
        norm_num⟩

noncomputable def collarInv (q : ConnectedSumQuotient c d aD.toHomeomorph) : K := by
  classical
  exact
    if h : q ∈ Set.range (seamMap c d aD.toHomeomorph) then
      (unitVecFun (seamChartX c d aD.toHomeomorph q), collarParam c d aD q)
    else (spherePoint (n := 3) (by norm_num),
      ⟨0, by
        change (0 : ℝ) ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2)
        norm_num⟩)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem seamChartX_ne_zero {q : ConnectedSumQuotient c d aD.toHomeomorph}
    (hq : q ∈ Set.range (seamMap c d aD.toHomeomorph)) :
    seamChartX c d aD.toHomeomorph q ≠ 0 := by
  have hw := seamChartX_mem_SeamShell c d aD hq
  intro h
  rw [h] at hw
  norm_num [SeamShell] at hw

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem collarInv_collarMap (p : K) : collarInv c d aD (collarMap c d aD p) = p := by
  have hmem := collarMap_mem_range c d aD p
  have hchart : seamChartX c d aD.toHomeomorph (collarMap c d aD p) = rad p := by
    rw [collarMap_eq_seamChartX c d aD p]
    exact (seamChartX c d aD.toHomeomorph).right_inv (by
      rw [seamChartX_target]; exact rad_mem_SeamShell p)
  simp only [collarInv, dif_pos hmem]
  refine Prod.ext ?_ ?_
  · exact (congrArg unitVecFun hchart).trans (unitVecFun_rad p)
  · apply Subtype.ext
    simp only [collarParam, dif_pos hmem, hchart, norm_rad, Subtype.coe_mk]
    ring

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem collarMap_collarInv (q : ConnectedSumQuotient c d aD.toHomeomorph)
    (hq : q ∈ Set.range (seamMap c d aD.toHomeomorph)) :
    collarMap c d aD (collarInv c d aD q) = q := by
  have hwne := seamChartX_ne_zero c d aD hq
  have hrad : rad (unitVecFun (seamChartX c d aD.toHomeomorph q), collarParam c d aD q)
      = seamChartX c d aD.toHomeomorph q := by
    rw [rad]
    simp only [collarParam, dif_pos hq, Subtype.coe_mk]
    rw [unitVecFun_of_ne hwne]
    have h1 : (1 : ℝ) + (‖seamChartX c d aD.toHomeomorph q‖ - 1) =
        ‖seamChartX c d aD.toHomeomorph q‖ := by ring
    rw [h1, smul_unitVec]
  simp only [collarInv, dif_pos hq]
  rw [collarMap_eq_seamChartX c d aD, hrad]
  exact (seamChartX c d aD.toHomeomorph).left_inv (by rw [seamChartX_source]; exact hq)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem contMDiffOn_collarInv (hseam : seamChartX c d aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (collarInv c d aD)
      (Set.range (seamMap c d aD.toHomeomorph)) := by
  classical
  intro q₀ hq₀
  have hwne := seamChartX_ne_zero c d aD hq₀
  have hw := seamChartX_mem_SeamShell c d aD hq₀
  have hchart : ContMDiffWithinAt (𝓡 3) (𝓡 3) ∞ (seamChartX c d aD.toHomeomorph)
      (Set.range (seamMap c d aD.toHomeomorph)) q₀ := by
    rw [← seamChartX_source]
    exact (contMDiffOn_seamChartX c d aD hseam) q₀ (by rw [seamChartX_source]; exact hq₀)
  have hfirst : ContMDiffWithinAt (𝓡 3) (𝓡 2) ∞
      (fun q => unitVecFun (seamChartX c d aD.toHomeomorph q))
      (Set.range (seamMap c d aD.toHomeomorph)) q₀ :=
    ContMDiffWithinAt.comp (x := q₀) (unitVecFun_contMDiffWithinAt _ hw) hchart
      (fun q hq => by
        have hsrc : q ∈ (seamChartX c d aD.toHomeomorph).source := by
          rwa [seamChartX_source]
        have h := (seamChartX c d aD.toHomeomorph).map_source hsrc
        rwa [seamChartX_target] at h)
  have hnorm0 : ContMDiffWithinAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun q => ‖seamChartX c d aD.toHomeomorph q‖)
      (Set.range (seamMap c d aD.toHomeomorph)) q₀ := by
    have hamb : ContMDiffWithinAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun u : csModel => ‖u‖) Set.univ
        (seamChartX c d aD.toHomeomorph q₀) :=
      contMDiffWithinAt_iff_contDiffWithinAt.mpr ((contDiffAt_norm ℝ hwne).contDiffWithinAt)
    exact ContMDiffWithinAt.comp (x := q₀) hamb hchart (fun q _ => Set.mem_univ _)
  have hsub : ContMDiffWithinAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun q => ‖seamChartX c d aD.toHomeomorph q‖ - 1)
      (Set.range (seamMap c d aD.toHomeomorph)) q₀ :=
    hnorm0.sub contMDiffWithinAt_const
  have hparam : ContMDiffWithinAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (collarParam c d aD)
      (Set.range (seamMap c d aD.toHomeomorph)) q₀ := by
    refine (ContMDiffWithinAt.subtypeVal_comp_iff (U := collarInterval)
      (f := collarParam c d aD) (Set.range (seamMap c d aD.toHomeomorph)) q₀).mp ?_
    refine hsub.congr (fun q hq => ?_) ?_
    · simp only [Function.comp_apply, collarParam, dif_pos hq, Subtype.coe_mk]
    · simp only [Function.comp_apply, collarParam, dif_pos hq₀, Subtype.coe_mk]
  have hpair : ContMDiffWithinAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => (unitVecFun (seamChartX c d aD.toHomeomorph q), collarParam c d aD q))
      (Set.range (seamMap c d aD.toHomeomorph)) q₀ :=
    hfirst.prodMk hparam
  exact hpair.congr (fun q hq => by simp only [collarInv, dif_pos hq]) (by
    simp only [collarInv, dif_pos hq₀])

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem collarMap_isLocalDiffeomorph (hseam : seamChartX c d aD.toHomeomorph ∈
    atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph)) :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (collarMap c d aD) := by
  classical
  refine fun x => ⟨{ toFun := collarMap c d aD
                     invFun := collarInv c d aD
                     source := Set.univ
                     target := Set.range (seamMap c d aD.toHomeomorph)
                     map_source' := ?_
                     map_target' := ?_
                     left_inv' := ?_
                     right_inv' := ?_
                     open_source := isOpen_univ
                     open_target := ?_
                     contMDiffOn_toFun := contMDiffOn_collarMap c d aD hseam
                     contMDiffOn_invFun := contMDiffOn_collarInv c d aD hseam },
    Set.mem_univ x, fun y _ => rfl⟩
  · intro p _
    exact collarMap_mem_range c d aD p
  · intro q _
    exact Set.mem_univ _
  · intro p _
    exact collarInv_collarMap c d aD p
  · intro q hq
    exact collarMap_collarInv c d aD q hq
  · rw [← seamChartX_source]
    exact (seamChartX c d aD.toHomeomorph).open_source



end Collar

end ConnectedSumQuotient
end DifferentialGeometry.Topology
