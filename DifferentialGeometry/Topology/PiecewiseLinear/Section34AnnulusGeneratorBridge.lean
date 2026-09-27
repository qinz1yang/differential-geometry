import DifferentialGeometry.Topology.Homeomorph.JordanAnnulus
import DifferentialGeometry.Topology.PiecewiseLinear.CellTraceFirstHomology
import DifferentialGeometry.Topology.PiecewiseLinear.NestedJordanCurves
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialTrace

open Set Metric Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_closedBall_homeomorph {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D J : Set M}
    (hD : IsPLCellOn 2 D J) :
    ∃ e : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ D,
      ∀ x, (e x : M) ∈ J ↔ (x : EuclideanSpace ℝ (Fin 2)) ∈ sphere 0 1 := by
  obtain ⟨φ, hφ⟩ := hD.exists_homeomorph
  let τ := DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
  refine ⟨τ.symm.trans φ, fun x => ?_⟩
  rw [Homeomorph.trans_apply, hφ]
  have ht := DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (τ.symm x)
  change (τ (τ.symm x) : EuclideanSpace ℝ (Fin 2)) ∈ sphere 0 1 ↔ _ at ht
  rw [τ.apply_symm_apply] at ht
  exact ⟨fun h => ht.mpr h.2, fun h => ⟨(τ.symm x).property, ht.mp h⟩⟩

theorem IsAnnulusOn.exists_circle_embedding_first {M : Type*} [TopologicalSpace M]
    {A A₀ A₁ : Set M} (hA : IsAnnulusOn A A₀ A₁) :
    ∃ f : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → M,
      Continuous f ∧ Function.Injective f ∧ range f = A₀ := by
  obtain ⟨φ, h₀, -⟩ := hA
  let f : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → M := fun θ => φ (θ, 0)
  refine ⟨f, continuous_subtype_val.comp
    (φ.continuous.comp (continuous_id.prodMk continuous_const)), ?_, ?_⟩
  · intro x y hxy
    exact congrArg Prod.fst (φ.injective (Subtype.ext hxy))
  · rw [h₀]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ (x, 0), ⟨(x, 0), rfl, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      have hzero : p.2 = 0 := Subtype.ext hp
      exact ⟨p.1, congrArg (fun q => (φ q : M)) (Prod.ext rfl hzero.symm)⟩

theorem IsPLCellOn.exists_annulus_embedding_to_inner_circle {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D J K : Set M} (hD : IsPLCellOn 2 D J)
    {f : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → M}
    (hf : Continuous f) (hinj : Function.Injective f) (hrange : range f = K)
    (hKD : K ⊆ D) (hKJ : Disjoint K J) :
    ∃ F : unitInterval × DifferentialGeometry.Topology.loopCircle → M,
      Continuous F ∧ Function.Injective F ∧ range F ⊆ D ∧
      range (fun θ => F (0, θ)) = K ∧ range (fun θ => F (1, θ)) = J := by
  obtain ⟨e, he⟩ := hD.exists_closedBall_homeomorph
  let g : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → D :=
    fun θ => ⟨f θ, hKD (hrange ▸ mem_range_self θ)⟩
  let k : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → Schoenflies.Plane :=
    fun θ => e.symm (g θ)
  have hkc : Continuous k :=
    continuous_subtype_val.comp (e.symm.continuous.comp (hf.subtype_mk _))
  have hki : Function.Injective k := by
    intro x y hxy
    exact hinj (congrArg Subtype.val (e.symm.injective (Subtype.ext hxy)))
  have hK : Schoenflies.IsJordanCurve (range k) :=
    DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_circle
      (hkc.isClosedEmbedding hki).isEmbedding
  have hkball : range k ⊆ ball (0 : Schoenflies.Plane) 1 := by
    rintro _ ⟨θ, rfl⟩
    have hle := mem_closedBall_zero_iff.mp (e.symm (g θ)).property
    refine mem_ball_zero_iff.mpr (lt_of_le_of_ne hle ?_)
    intro hnorm
    have hj := (he (e.symm (g θ))).mpr (mem_sphere_zero_iff_norm.mpr hnorm)
    rw [e.apply_symm_apply] at hj
    exact disjoint_left.mp hKJ (hrange ▸ mem_range_self θ) hj
  have hs : Schoenflies.IsJordanCurve (sphere (0 : Schoenflies.Plane) 1) := by
    simpa only [Subtype.range_coe] using
      DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_range_of_isEmbedding_circle
        (Topology.IsEmbedding.subtypeVal :
          Topology.IsEmbedding (Subtype.val : sphere (0 : Schoenflies.Plane) 1 → _))
  have hfr := frontier_closedBall (0 : Schoenflies.Plane) one_ne_zero
  have hi : (interior (closedBall (0 : Schoenflies.Plane) 1)).Nonempty := by
    rw [interior_closedBall (0 : Schoenflies.Plane) one_ne_zero]
    exact nonempty_ball.mpr one_pos
  have hinside : Schoenflies.inside (sphere (0 : Schoenflies.Plane) 1) = ball 0 1 := by
    simpa only [hfr, interior_closedBall (0 : Schoenflies.Plane) one_ne_zero] using
      (DifferentialGeometry.Topology.PlanarJordan.interior_eq_inside_frontier_of_isCompact
        (isCompact_closedBall (0 : Schoenflies.Plane) 1) (hfr.symm ▸ hs) hi).symm
  have hclosure : closure (Schoenflies.inside (sphere (0 : Schoenflies.Plane) 1)) =
      closedBall 0 1 := by
    simpa only [hfr] using
      DifferentialGeometry.Topology.PlanarJordan.closure_inside_frontier_eq_of_isCompact
        (isCompact_closedBall (0 : Schoenflies.Plane) 1) (hfr.symm ▸ hs) hi
  obtain ⟨P, hP0, hP1⟩ := Homeomorph.exists_homeomorph_jordan_annulus hK hs
    (hinside ▸ closure_inside_subset_ball hK hkball)
  let p : unitInterval × DifferentialGeometry.Topology.loopCircle →
      closedBall (0 : Schoenflies.Plane) 1 := fun x => ⟨P x, hclosure ▸ (P x).property.1⟩
  have hp : Continuous p := (continuous_subtype_val.comp P.continuous).subtype_mk _
  let F : unitInterval × DifferentialGeometry.Topology.loopCircle → M := fun x => e (p x)
  refine ⟨F, continuous_subtype_val.comp (e.continuous.comp hp), ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply P.injective
    apply Subtype.ext
    exact congrArg (fun z : closedBall (0 : Schoenflies.Plane) 1 => z.val)
      (e.injective (Subtype.ext hxy))
  · rintro _ ⟨x, rfl⟩
    exact (e (p x)).property
  · ext y
    constructor
    · rintro ⟨θ, rfl⟩
      obtain ⟨z, hz⟩ := hP0.subset (mem_range_self θ)
      have heq : p (0, θ) = e.symm (g z) := Subtype.ext hz.symm
      change (e (p (0, θ)) : M) ∈ K
      rw [heq, e.apply_symm_apply]
      exact hrange ▸ mem_range_self z
    · intro hy
      obtain ⟨z, rfl⟩ := hrange.symm ▸ hy
      obtain ⟨θ, hθ⟩ := hP0.symm.subset (mem_range_self z)
      refine ⟨θ, ?_⟩
      have heq : p (0, θ) = e.symm (g z) := Subtype.ext hθ
      change (e (p (0, θ)) : M) = f z
      rw [heq, e.apply_symm_apply]
  · ext y
    constructor
    · rintro ⟨θ, rfl⟩
      exact (he (p (1, θ))).mpr (hP1.subset (mem_range_self θ))
    · intro hy
      let z : D := ⟨y, hD.boundary_subset hy⟩
      have hz : (e.symm z : Schoenflies.Plane) ∈ sphere 0 1 :=
        (he (e.symm z)).mp (by simpa using hy)
      obtain ⟨θ, hθ⟩ := hP1.symm.subset hz
      refine ⟨θ, ?_⟩
      have heq : p (1, θ) = e.symm z := Subtype.ext hθ
      change (e (p (1, θ)) : M) = y
      rw [heq, e.apply_symm_apply]

theorem IsPLCellOn.annular_homotopy_subset_of_boundary_avoidance {M L : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [TopologicalSpace L] {S B A A₀ A₁ D J : Set M} (hS : IsPLCellOn 3 S B)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B) (hDB : D ⊆ B) (hJA : J ⊆ A)
    (hDA₁ : Disjoint D A₁) {F : unitInterval × L → M}
    (hF : Continuous F) (hinj : Function.Injective F) (hFD : range F ⊆ D)
    (hzero : range (fun θ => F (0, θ)) = A₀)
    (hone : range (fun θ => F (1, θ)) = J) : range F ⊆ A := by
  rintro _ ⟨⟨t, θ⟩, rfl⟩
  by_cases ht : t = 0
  · subst t
    exact hA.first_subset (hzero ▸ mem_range_self θ)
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 fun h => ht (Subtype.ext h.symm)
  let γ : ℝ → M := fun s => F (projIcc 0 1 zero_le_one s, θ)
  have hγ : Continuous γ :=
    hF.comp (continuous_projIcc.prodMk continuous_const)
  have hγone : γ 1 = F (1, θ) := by simp [γ]
  have hγt : γ t = F (t, θ) := by simp [γ]
  have hRD : γ '' Icc (t : ℝ) 1 ⊆ D := image_subset_iff.mpr fun s _ =>
    hFD (mem_range_self (projIcc 0 1 zero_le_one s, θ))
  have hdis : Disjoint (γ '' Icc (t : ℝ) 1) (A₀ ∪ A₁) := by
    refine disjoint_left.mpr ?_
    rintro x ⟨s, hs, rfl⟩ (hx | hx)
    · obtain ⟨η, hη⟩ := hzero.symm ▸ hx
      have heq := congrArg (fun p : unitInterval × L => (p.1 : ℝ)) (hinj hη)
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨t.property.1.trans hs.1, hs.2⟩
      change 0 = (projIcc 0 1 zero_le_one s : ℝ) at heq
      rw [projIcc_of_mem zero_le_one hs01] at heq
      change 0 = s at heq
      linarith [hs.1]
    · exact disjoint_left.mp hDA₁ (hRD ⟨s, hs, rfl⟩) hx
  have hsub := hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hA hAB
    (hRD.trans hDB) (isPreconnected_Icc.image γ hγ.continuousOn)
    ⟨γ 1, ⟨1, ⟨t.property.2, le_rfl⟩, rfl⟩,
      hγone ▸ hJA (hone ▸ mem_range_self θ)⟩ hdis
  exact hγt ▸ hsub ⟨t, ⟨le_rfl, t.property.2⟩, rfl⟩

theorem IsPLCellOn.carriesFundamentalGroupOnto_boundary_of_annulus_end {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ D J T : Set M} (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B) (hDB : D ⊆ B)
    (hJA : J ⊆ A) (h₀D : A₀ ⊆ D) (h₀J : Disjoint A₀ J) (hD₁ : Disjoint D A₁)
    (hAT : A ⊆ T) (hcarry : CarriesFundamentalGroupOnto A₀ T) :
    CarriesFundamentalGroupOnto J T := by
  obtain ⟨f, hf, hfi, hfr⟩ := hA.exists_circle_embedding_first
  obtain ⟨F, hF, hFi, hFD, hF0, hF1⟩ :=
    hD.exists_annulus_embedding_to_inner_circle hf hfi hfr h₀D h₀J
  have hFA := hS.annular_homotopy_subset_of_boundary_avoidance hA hAB hDB hJA hD₁
    hF hFi hFD hF0 hF1
  let g (p : DifferentialGeometry.Topology.loopCircle × ℝ) : M :=
    F (projIcc 0 1 zero_le_one (1 - p.2), p.1)
  have hg : Continuous g := hF.comp
    ((continuous_projIcc.comp (continuous_const.sub continuous_snd)).prodMk continuous_fst)
  have hg0 : (fun θ => g (θ, 0)) '' univ = J := by
    simpa [g] using hF1
  have hg1 : (fun θ => g (θ, 1)) '' univ = A₀ := by
    simpa [g] using hF0
  rw [← hg0]
  apply carriesFundamentalGroupOnto_image_zero_of_image_one isCompact_univ hg.continuousOn
    (fun p _ => hAT (hFA (mem_range_self _)))
  · intro x _ y _ hxy
    have heq := hFi hxy
    exact congrArg Prod.snd heq
  · rwa [hg1]

end DifferentialGeometry.Topology.PiecewiseLinear
