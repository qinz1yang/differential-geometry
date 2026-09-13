import DifferentialGeometry.Topology.PiecewiseLinear.StdChart
import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPiecewiseAffineOn.inter_of_isOpen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {u O : Set E} (hf : IsPiecewiseAffineOn f u) (hO : IsOpen O) :
    IsPiecewiseAffineOn f (u ∩ O) :=
  fun x hx => (hf x hx.1).inter_of_mem_nhds (hO.mem_nhds hx.2)

omit [FiniteDimensional ℝ E] in
theorem openStar_eq_closedStar_inter (K : Geometry.SimplicialComplex ℝ E) {p : E}
    (hp : {p} ∈ K.faces) : openStar K p = closedStar K p ∩ (avoidingUnion K p)ᶜ := by
  classical
  refine Subset.antisymm (fun x hx => ⟨openStar_subset_closedStar K hp hx, hx.2⟩) ?_
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨closedStar_subset_space K p hx₁, hx₂⟩

section Chart

variable (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
  {n : ℕ}

open Classical in
noncomputable def starHomeo
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    (Fin (n + 2) → ℝ) → E :=
  Classical.choose (exists_starHomeo K hp hsph)

open Classical in
theorem starHomeo_spec (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    IsPLHomeomorphOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2))) (closedStar K p) ∧
      starHomeo K hp hsph '' openSimplex (stdVertices n) = openStar K p ∧
      starHomeo K hp hsph (stdCenter n) = p :=
  Classical.choose_spec (exists_starHomeo K hp hsph)

theorem openSimplex_stdVertices_subset_stdSimplex :
    openSimplex (stdVertices n) ⊆ stdSimplex ℝ (Fin (n + 2)) := by
  rw [← convexHull_stdVertices]
  exact openSimplex_subset_convexHull _

omit [FiniteDimensional ℝ E] [Finite K.faces] in
theorem apex_mem_space' (hp : {p} ∈ K.faces) : p ∈ K.space :=
  K.convexHull_subset_space hp (subset_convexHull ℝ _ (by simp))

open Classical in
noncomputable def vertexChart
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin (n + 1))) where
  toFun x := stdProj n (Function.invFunOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2))) x.1)
  invFun y :=
    if h : starHomeo K hp hsph (stdLift n y) ∈ K.space then ⟨_, h⟩ else ⟨p, apex_mem_space' K hp⟩
  source := Subtype.val ⁻¹' openStar K p
  target := stdTarget n
  map_source' := by
    intro x hx
    have hx' : x.1 ∈ starHomeo K hp hsph '' openSimplex (stdVertices n) := by
      rw [(starHomeo_spec K hp hsph).2.1]
      exact hx
    obtain ⟨w, hw, hxw⟩ := hx'
    have hw' : w ∈ stdSimplex ℝ (Fin (n + 2)) := openSimplex_stdVertices_subset_stdSimplex hw
    have hinv := (starHomeo_spec K hp hsph).1.bijOn.invOn_invFunOn.1 hw'
    change stdProj n (Function.invFunOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2))) x.1) ∈
      stdTarget n
    rw [← hxw, hinv]
    exact stdProj_mem_stdTarget n hw
  map_target' := by
    intro y hy
    have hmem : starHomeo K hp hsph (stdLift n y) ∈ openStar K p := by
      rw [← (starHomeo_spec K hp hsph).2.1]
      exact mem_image_of_mem _ (stdLift_mem_openSimplex n hy)
    have hK : starHomeo K hp hsph (stdLift n y) ∈ K.space := openStar_subset_space K p hmem
    change (if h : starHomeo K hp hsph (stdLift n y) ∈ K.space then (⟨_, h⟩ : K.space)
      else ⟨p, apex_mem_space' K hp⟩) ∈ Subtype.val ⁻¹' openStar K p
    rw [dif_pos hK]
    exact hmem
  left_inv' := by
    intro x hx
    have hx' : x.1 ∈ starHomeo K hp hsph '' openSimplex (stdVertices n) := by
      rw [(starHomeo_spec K hp hsph).2.1]
      exact hx
    obtain ⟨w, hw, hxw⟩ := hx'
    have hw' : w ∈ stdSimplex ℝ (Fin (n + 2)) := openSimplex_stdVertices_subset_stdSimplex hw
    have hinv := (starHomeo_spec K hp hsph).1.bijOn.invOn_invFunOn.1 hw'
    have e1 : stdLift n (stdProj n
        (Function.invFunOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2))) x.1)) = w := by
      rw [← hxw, hinv, stdLift_stdProj_of_mem n hw]
    change (if h : starHomeo K hp hsph (stdLift n (stdProj n
        (Function.invFunOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2))) x.1))) ∈ K.space
      then (⟨_, h⟩ : K.space) else ⟨p, apex_mem_space' K hp⟩) = x
    rw [e1, dif_pos (by rw [hxw]; exact x.2)]
    exact Subtype.ext hxw
  right_inv' := by
    intro y hy
    have hmem : starHomeo K hp hsph (stdLift n y) ∈ openStar K p := by
      rw [← (starHomeo_spec K hp hsph).2.1]
      exact mem_image_of_mem _ (stdLift_mem_openSimplex n hy)
    have hK : starHomeo K hp hsph (stdLift n y) ∈ K.space := openStar_subset_space K p hmem
    have hinv := (starHomeo_spec K hp hsph).1.bijOn.invOn_invFunOn.1
      (openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n hy))
    change stdProj n (Function.invFunOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2)))
      (if h : starHomeo K hp hsph (stdLift n y) ∈ K.space then (⟨_, h⟩ : K.space)
        else ⟨p, apex_mem_space' K hp⟩).1) = y
    rw [dif_pos hK, hinv, stdProj_stdLift]
  open_source := isOpen_preimage_openStar K p
  open_target := isOpen_stdTarget n
  continuousOn_toFun := by
    have hcont : ContinuousOn
        (Function.invFunOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2))) ∘
          (Subtype.val : K.space → E))
        ((Subtype.val : K.space → E) ⁻¹' openStar K p) :=
      (starHomeo_spec K hp hsph).1.symm.isPiecewiseAffineOn.continuousOn.comp
        (continuous_subtype_val (p := fun x => x ∈ K.space)).continuousOn
        fun x hx => openStar_subset_closedStar K hp hx
    exact (continuous_stdProj n).comp_continuousOn hcont
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hcont : ContinuousOn (starHomeo K hp hsph ∘ stdLift n) (stdTarget n) :=
      (starHomeo_spec K hp hsph).1.isPiecewiseAffineOn.continuousOn.comp
        (continuous_stdLift n).continuousOn fun y hy =>
          openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n hy)
    refine hcont.congr fun y hy => ?_
    have hmem : starHomeo K hp hsph (stdLift n y) ∈ openStar K p := by
      rw [← (starHomeo_spec K hp hsph).2.1]
      exact mem_image_of_mem _ (stdLift_mem_openSimplex n hy)
    change (if h : starHomeo K hp hsph (stdLift n y) ∈ K.space then (⟨_, h⟩ : K.space)
      else ⟨p, apex_mem_space' K hp⟩).1 = starHomeo K hp hsph (stdLift n y)
    rw [dif_pos (openStar_subset_space K p hmem)]

open Classical in
theorem vertexChart_apply (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space)
    (x : K.space) :
    vertexChart K hp hsph x =
      stdProj n (Function.invFunOn (starHomeo K hp hsph) (stdSimplex ℝ (Fin (n + 2))) x.1) := rfl

open Classical in
theorem vertexChart_source (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    (vertexChart K hp hsph).source = Subtype.val ⁻¹' openStar K p := rfl

open Classical in
theorem vertexChart_target (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    (vertexChart K hp hsph).target = stdTarget n := rfl

open Classical in
theorem vertexChart_symm_val (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space)
    {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ stdTarget n) :
    ((vertexChart K hp hsph).symm y : E) = starHomeo K hp hsph (stdLift n y) := by
  have hmem : starHomeo K hp hsph (stdLift n y) ∈ openStar K p := by
    rw [← (starHomeo_spec K hp hsph).2.1]
    exact mem_image_of_mem _ (stdLift_mem_openSimplex n hy)
  change (if h : starHomeo K hp hsph (stdLift n y) ∈ K.space then (⟨_, h⟩ : K.space)
    else ⟨p, apex_mem_space' K hp⟩).1 = starHomeo K hp hsph (stdLift n y)
  rw [dif_pos (openStar_subset_space K p hmem)]

open Classical in
theorem vertexChart_symm_val_mem
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space)
    {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ stdTarget n) :
    ((vertexChart K hp hsph).symm y : E) ∈ openStar K p := by
  rw [vertexChart_symm_val K hp hsph hy, ← (starHomeo_spec K hp hsph).2.1]
  exact mem_image_of_mem _ (stdLift_mem_openSimplex n hy)

open Classical in
theorem isPiecewiseAffineOn_vertexChart
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    IsPiecewiseAffineOn (fun q => if h : q ∈ K.space then vertexChart K hp hsph ⟨q, h⟩ else 0)
      (Subtype.val '' (vertexChart K hp hsph).source) := by
  rw [vertexChart_source, Subtype.image_preimage_coe,
    inter_eq_right.mpr (openStar_subset_space K p), openStar_eq_closedStar_inter K hp]
  have h1 : IsPiecewiseAffineOn (stdProj n).toAffineMap (univ : Set (Fin (n + 2) → ℝ)) :=
    isPiecewiseAffineOn_of_affine _ isOpen_univ
  have h2 := h1.comp (starHomeo_spec K hp hsph).1.symm.isPiecewiseAffineOn
  rw [preimage_univ, inter_univ] at h2
  refine (h2.inter_of_isOpen (isClosed_avoidingUnion K p).isOpen_compl).congr fun q hq => ?_
  have hqK : q ∈ K.space := closedStar_subset_space K p hq.1
  simp only [dif_pos hqK, vertexChart_apply, Function.comp_apply, LinearMap.coe_toAffineMap]

open Classical in
theorem isPiecewiseAffineOn_vertexChart_symm
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    IsPiecewiseAffineOn (fun y => ((vertexChart K hp hsph).symm y : E))
      (vertexChart K hp hsph).target := by
  rw [vertexChart_target]
  have h1 : IsPiecewiseAffineOn (stdLift n) (stdTarget n) :=
    isPiecewiseAffineOn_of_affine _ (isOpen_stdTarget n)
  have h2 := (starHomeo_spec K hp hsph).1.isPiecewiseAffineOn.comp h1
  have hsub : stdTarget n ⊆ stdLift n ⁻¹' stdSimplex ℝ (Fin (n + 2)) := fun y hy =>
    openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n hy)
  rw [inter_eq_left.mpr hsub] at h2
  exact h2.congr fun y hy => vertexChart_symm_val K hp hsph hy

end Chart

section Transition

variable (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p p' : E} (hp : {p} ∈ K.faces)
  (hp' : {p'} ∈ K.faces) {n : ℕ}

open Classical in
theorem vertexChart_trans_mem_plGroupoid
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space)
    (hsph' : IsPLSphere n (SimplicialComplex.geometricLink K {p'}).space) :
    (vertexChart K hp hsph).symm ≫ₕ vertexChart K hp' hsph' ∈ plGroupoid (n + 1) := by
  refine mem_plGroupoid_of_isPiecewiseAffineOn ?_
  set U := ((vertexChart K hp hsph).symm ≫ₕ vertexChart K hp' hsph').source with hU
  have hUopen : IsOpen U := ((vertexChart K hp hsph).symm ≫ₕ vertexChart K hp' hsph').open_source
  have hUsub : ∀ y ∈ U, y ∈ stdTarget n ∧
      starHomeo K hp hsph (stdLift n y) ∈ openStar K p' := by
    intro y hy
    rw [hU, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      vertexChart_target] at hy
    refine ⟨hy.1, ?_⟩
    have h2 := hy.2
    rw [mem_preimage, vertexChart_source, mem_preimage, vertexChart_symm_val K hp hsph hy.1] at h2
    exact h2
  have h1 : IsPiecewiseAffineOn (stdLift n) U := isPiecewiseAffineOn_of_affine _ hUopen
  have h2 := (starHomeo_spec K hp hsph).1.isPiecewiseAffineOn.comp h1
  have hsub₁ : U ⊆ stdLift n ⁻¹' stdSimplex ℝ (Fin (n + 2)) := fun y hy =>
    openSimplex_stdVertices_subset_stdSimplex (stdLift_mem_openSimplex n (hUsub y hy).1)
  rw [inter_eq_left.mpr hsub₁] at h2
  have h3 := (starHomeo_spec K hp' hsph').1.symm.isPiecewiseAffineOn.comp h2
  have hsub₂ : U ⊆ (starHomeo K hp hsph ∘ stdLift n) ⁻¹' closedStar K p' := fun y hy =>
    openStar_subset_closedStar K hp' (hUsub y hy).2
  rw [inter_eq_left.mpr hsub₂] at h3
  have h4 : IsPiecewiseAffineOn (stdProj n).toAffineMap (univ : Set (Fin (n + 2) → ℝ)) :=
    isPiecewiseAffineOn_of_affine _ isOpen_univ
  have h5 := h4.comp h3
  rw [preimage_univ, inter_univ] at h5
  refine h5.congr fun y hy => ?_
  rw [OpenPartialHomeomorph.trans_apply, vertexChart_apply, vertexChart_symm_val K hp hsph
    (hUsub y hy).1]
  rfl

end Transition

section ChartedSpace

variable (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}

omit [FiniteDimensional ℝ E] [Finite K.faces] in
open Classical in
theorem IsCombinatorialManifold.isPLSphere_link {K : Geometry.SimplicialComplex ℝ E}
    (hK : IsCombinatorialManifold (n + 1) K) {v : E} (hv : {v} ∈ K.faces) :
    IsPLSphere n (SimplicialComplex.geometricLink K {v}).space := hK v hv

noncomputable def vertexOf (x : K.space) : E := (exists_vertex_mem_openStar K x.2).choose

omit [FiniteDimensional ℝ E] [Finite K.faces] in
theorem vertexOf_mem (x : K.space) : {vertexOf K x} ∈ K.faces :=
  (exists_vertex_mem_openStar K x.2).choose_spec.1

omit [FiniteDimensional ℝ E] [Finite K.faces] in
theorem mem_openStar_vertexOf (x : K.space) : x.1 ∈ openStar K (vertexOf K x) :=
  (exists_vertex_mem_openStar K x.2).choose_spec.2

open Classical in
noncomputable def vertexChartAt (hK : IsCombinatorialManifold (n + 1) K)
    (v : {v : E // {v} ∈ K.faces}) : OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin (n + 1))) :=
  vertexChart K v.2 (hK.isPLSphere_link v.2)

open Classical in
@[instance_reducible] noncomputable def combinatorialChartedSpace
    (hK : IsCombinatorialManifold (n + 1) K) :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) K.space where
  atlas := Set.range (vertexChartAt K hK)
  chartAt x := vertexChartAt K hK ⟨vertexOf K x, vertexOf_mem K x⟩
  mem_chart_source x := by
    rw [vertexChartAt, vertexChart_source]
    exact mem_openStar_vertexOf K x
  chart_mem_atlas x := Set.mem_range_self _

open Classical in
theorem mem_combinatorialChartedSpace_atlas (hK : IsCombinatorialManifold (n + 1) K)
    {e : OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin (n + 1)))}
    (he : e ∈ (combinatorialChartedSpace K hK).atlas) :
    ∃ (p : E) (hp : {p} ∈ K.faces), e = vertexChart K hp (hK.isPLSphere_link hp) := by
  obtain ⟨v, hv⟩ := he
  exact ⟨v.1, v.2, by rw [← hv]; rfl⟩

open Classical in
theorem combinatorialChartedSpace_hasGroupoid (hK : IsCombinatorialManifold (n + 1) K) :
    letI := combinatorialChartedSpace K hK
    HasGroupoid K.space (plGroupoid (n + 1)) := by
  let _ := combinatorialChartedSpace K hK
  constructor
  intro e e' he he'
  obtain ⟨p, hp, rfl⟩ := mem_combinatorialChartedSpace_atlas K hK he
  obtain ⟨p', hp', rfl⟩ := mem_combinatorialChartedSpace_atlas K hK he'
  exact vertexChart_trans_mem_plGroupoid K hp hp' (hK.isPLSphere_link hp) (hK.isPLSphere_link hp')

end ChartedSpace

theorem combinatorialManifoldPLStructure_succ (n : ℕ) :
    CombinatorialManifoldPLStructure (n + 1) := by
  intro N K hfin hK
  refine ⟨combinatorialChartedSpace K hK, combinatorialChartedSpace_hasGroupoid K hK, ?_⟩
  intro e he
  obtain ⟨p, hp, rfl⟩ := mem_combinatorialChartedSpace_atlas K hK he
  exact ⟨isPiecewiseAffineOn_vertexChart K hp (hK.isPLSphere_link hp),
    isPiecewiseAffineOn_vertexChart_symm K hp (hK.isPLSphere_link hp)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
