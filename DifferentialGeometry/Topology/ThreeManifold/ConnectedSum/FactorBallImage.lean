import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)

private theorem image_chart_subset_transport_left
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (he : ∀ x ∈ closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) :
    (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) =
      {x : c.Punctured | x.val ∈ e.chart '' S} := by
  ext x
  constructor
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨_, htransport⟩ := he w (hS hw)
    rw [htransport] at hweq
    exact ⟨w, hw, congrArg Subtype.val ((inl_injective c.toBallChart d.toBallChart
      a.1.toHomeomorph) hweq)⟩
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨hw', htransport⟩ := he w (hS hw)
    exact ⟨w, hw, htransport.trans (congrArg
      (inl c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext hweq))⟩

private theorem image_chart_subset_transport_right
    (e : OrientedBallChart N.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (he : ∀ x ∈ closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ d.chart '' ball (0 : E3) 1,
        e'.chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) :
    (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) =
      {x : d.Punctured | x.val ∈ e.chart '' S} := by
  ext x
  constructor
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨_, htransport⟩ := he w (hS hw)
    rw [htransport] at hweq
    exact ⟨w, hw, congrArg Subtype.val ((inr_injective c.toBallChart d.toBallChart
      a.1.toHomeomorph) hweq)⟩
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨hw', htransport⟩ := he w (hS hw)
    exact ⟨w, hw, htransport.trans (congrArg
      (inr c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext hweq))⟩

private theorem inr_preimage_left_chart_subset_empty
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' closedBall (0 : E3) 1)
    (he : ∀ x ∈ closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) :
    (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y
  rintro ⟨w, hw, hweq⟩
  obtain ⟨_, htransport⟩ := he w (hS hw)
  rw [htransport] at hweq
  obtain ⟨z, hz, _⟩ :=
    (inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph _ _).mp hweq
  exact hdisj w (hS hw)
    ⟨z, sphere_subset_closedBall z.property, congrArg Subtype.val hz⟩

private theorem inl_preimage_right_chart_subset_empty
    (e : OrientedBallChart N.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ closedBall (0 : E3) 2,
      e.chart x ∉ d.chart '' closedBall (0 : E3) 1)
    (he : ∀ x ∈ closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ d.chart '' ball (0 : E3) 1,
        e'.chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) :
    (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y
  rintro ⟨w, hw, hweq⟩
  obtain ⟨_, htransport⟩ := he w (hS hw)
  rw [htransport] at hweq
  obtain ⟨z, _, hz⟩ :=
    (inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph _ _).mp hweq.symm
  exact hdisj w (hS hw)
    ⟨a.1 z, sphere_subset_closedBall (a.1 z).property, congrArg Subtype.val hz⟩

theorem preimage_inl_chart_image_ball
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (he : ∀ x ∈ closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩) :
    (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
        (e'.chart '' ball (0 : E3) 1) =
      {x : c.Punctured | x.val ∈ e.chart '' ball (0 : E3) 1} :=
  image_chart_subset_transport_left c d a e e' he _
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))

theorem preimage_inr_chart_image_ball_of_eq_inl
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' closedBall (0 : E3) 1)
    (he : ∀ x ∈ closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩) :
    (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
        (e'.chart '' ball (0 : E3) 1) = ∅ :=
  inr_preimage_left_chart_subset_empty c d a e e' hdisj he _
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))

theorem exists_orientedBallChart_inl_preimage
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' closedBall (0 : E3) 1) :
    ∃ e' : OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ x ∈ closedBall (0 : E3) 2,
        ∃ hx : e.chart x ∉ c.chart '' ball (0 : E3) 1,
          e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩) ∧
      (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (e'.chart '' ball (0 : E3) 1) =
        {x : c.Punctured | x.val ∈ e.chart '' ball (0 : E3) 1} ∧
      (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (e'.chart '' ball (0 : E3) 1) = ∅ := by
  obtain ⟨e', he'⟩ := exists_orientedBallChart_inl c d a e hdisj
  exact ⟨e', he', preimage_inl_chart_image_ball c d a e e' he',
    preimage_inr_chart_image_ball_of_eq_inl c d a e e' hdisj he'⟩

theorem exists_orientedBallChart_family_inl_preimage {ι : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (hdisj : ∀ i x, x ∈ closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' closedBall (0 : E3) 1) :
    ∃ e' : ι → OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∉ c.chart '' ball (0 : E3) 1,
          (e' i).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(e i).chart x, hx⟩) ∧
      (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (⋃ i, (e' i).chart '' ball (0 : E3) 1) =
        {x : c.Punctured | x.val ∈ ⋃ i, (e i).chart '' ball (0 : E3) 1} ∧
      (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (⋃ i, (e' i).chart '' ball (0 : E3) 1) = ∅ := by
  choose e' he' hleft hright using
    fun i => exists_orientedBallChart_inl_preimage c d a (e i) (hdisj i)
  refine ⟨e', he', ?_, ?_⟩
  · ext x
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq]
    exact exists_congr fun i => Set.ext_iff.mp (hleft i) x
  · rw [preimage_iUnion]
    simp only [hright, iUnion_empty]

theorem exists_orientedBallChart_sum_family_preimage {ι κ : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (f : κ → OrientedBallChart N.toClosedOrientedManifold)
    (hec : ∀ i x, x ∈ closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' closedBall (0 : E3) 1)
    (hfd : ∀ i x, x ∈ closedBall (0 : E3) 2 →
      (f i).chart x ∉ d.chart '' closedBall (0 : E3) 1)
    (he : Pairwise fun i j => Disjoint ((e i).chart '' closedBall (0 : E3) 2)
      ((e j).chart '' closedBall (0 : E3) 2))
    (hf : Pairwise fun i j => Disjoint ((f i).chart '' closedBall (0 : E3) 2)
      ((f j).chart '' closedBall (0 : E3) 2)) :
    ∃ b : ι ⊕ κ → OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∉ c.chart '' ball (0 : E3) 1,
          (b (Sum.inl i)).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(e i).chart x, hx⟩) ∧
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (f i).chart x ∉ d.chart '' ball (0 : E3) 1,
          (b (Sum.inr i)).chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(f i).chart x, hx⟩) ∧
      (Pairwise fun i j => Disjoint ((b i).chart '' closedBall (0 : E3) 2)
        ((b j).chart '' closedBall (0 : E3) 2)) ∧
      (∀ (S : Set E3), S ⊆ closedBall (0 : E3) 2 →
        (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : c.Punctured | x.val ∈ ⋃ i, (e i).chart '' S}) ∧
      (∀ (S : Set E3), S ⊆ closedBall (0 : E3) 2 →
        (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : d.Punctured | x.val ∈ ⋃ i, (f i).chart '' S}) := by
  classical
  choose e' he' using fun i => exists_orientedBallChart_inl c d a (e i) (hec i)
  choose f' hf' using fun i => exists_orientedBallChart_inr c d a (f i) (hfd i)
  let b := Sum.elim e' f'
  have hLL (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) (i : ι) :=
    image_chart_subset_transport_left c d a (e i) (e' i) (he' i) S hS
  have hRR (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) (i : κ) :=
    image_chart_subset_transport_right c d a (f i) (f' i) (hf' i) S hS
  have hRL (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) (i : ι) :=
    inr_preimage_left_chart_subset_empty c d a (e i) (e' i) (hec i) (he' i) S hS
  have hLR (S : Set E3) (hS : S ⊆ closedBall (0 : E3) 2) (i : κ) :=
    inl_preimage_right_chart_subset_empty c d a (f i) (f' i) (hfd i) (hf' i) S hS
  refine ⟨b, he', hf', ?_, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases i with i | i <;> rcases j with j | j
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := he' i x hx
      have hzj : inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(e i).chart x, hx'⟩ ∈
          (e' j).chart '' closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hLL _ subset_rfl j) ⟨(e i).chart x, hx'⟩
      exact Set.disjoint_left.mp (he (fun h => hij (congrArg Sum.inl h)))
        ⟨x, hx, rfl⟩ (hmem.mp hzj)
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := he' i x hx
      have hzj : inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(e i).chart x, hx'⟩ ∈
          (f' j).chart '' closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hLR _ subset_rfl j) ⟨(e i).chart x, hx'⟩
      exact hmem.mp hzj
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := hf' i x hx
      have hzj : inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(f i).chart x, hx'⟩ ∈
          (e' j).chart '' closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hRL _ subset_rfl j) ⟨(f i).chart x, hx'⟩
      exact hmem.mp hzj
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := hf' i x hx
      have hzj : inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(f i).chart x, hx'⟩ ∈
          (f' j).chart '' closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hRR _ subset_rfl j) ⟨(f i).chart x, hx'⟩
      exact Set.disjoint_left.mp (hf (fun h => hij (congrArg Sum.inr h)))
        ⟨x, hx, rfl⟩ (hmem.mp hzj)
  · intro S hS
    ext x
    simp only [mem_preimage, mem_iUnion, Sum.exists, mem_ofPred_eq]
    constructor
    · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
      · exact ⟨i, (Set.ext_iff.mp (hLL S hS i) x).mp hi⟩
      · exact ((Set.ext_iff.mp (hLR S hS j) x).mp hj).elim
    · rintro ⟨i, hi⟩
      exact Or.inl ⟨i, (Set.ext_iff.mp (hLL S hS i) x).mpr hi⟩
  · intro S hS
    ext x
    simp only [mem_preimage, mem_iUnion, Sum.exists, mem_ofPred_eq]
    constructor
    · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
      · exact ((Set.ext_iff.mp (hRL S hS i) x).mp hi).elim
      · exact ⟨j, (Set.ext_iff.mp (hRR S hS j) x).mp hj⟩
    · rintro ⟨j, hj⟩
      exact Or.inr ⟨j, (Set.ext_iff.mp (hRR S hS j) x).mpr hj⟩

end DifferentialGeometry.Topology.ConnectedSumQuotient
