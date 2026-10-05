import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem IsHPolytope.prod {P : Set E} {Q : Set F} (hP : IsHPolytope P) (hQ : IsHPolytope Q) :
    IsHPolytope (P ×ˢ Q) := by
  obtain ⟨hPc, ι, hι, l, c, rfl⟩ := hP
  obtain ⟨hQc, κ, hκ, m, d, rfl⟩ := hQ
  let _ := hι
  let _ := hκ
  refine ⟨hPc.prod hQc, ι ⊕ κ, inferInstance,
    Sum.elim (fun i => (l i).comp (LinearMap.fst ℝ E F))
      (fun j => (m j).comp (LinearMap.snd ℝ E F)), Sum.elim c d, ?_⟩
  ext x
  simp only [mem_prod, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]

theorem IsPolyhedron.prod {P : Set E} {Q : Set F} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ×ˢ Q) := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hQ
  let _ := hι
  let _ := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ×ˢ D p.2,
    fun p => (hC p.1).prod (hD p.2), ?_⟩
  ext x
  simp only [mem_prod, mem_iUnion, Prod.exists]
  exact ⟨fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => ⟨i, j, hi, hj⟩,
    fun ⟨i, j, hi, hj⟩ => ⟨⟨i, hi⟩, ⟨j, hj⟩⟩⟩

theorem IsPiecewiseAffineWithinAt.prodMap {f : E → F} {g : G → H}
    {P : Set E} {Q : Set G} {x : E} {y : G}
    (hf : IsPiecewiseAffineWithinAt f P x) (hg : IsPiecewiseAffineWithinAt g Q y) :
    IsPiecewiseAffineWithinAt (Prod.map f g) (P ×ˢ Q) (x, y) := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, B, hD, hDy⟩ := hg
  let _ := hι
  let _ := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ×ˢ D p.2,
    fun p => (A p.1).prodMap (B p.2), fun p => ?_, ?_⟩
  · exact ⟨(hC p.1).1.prod (hD p.2).1, prod_mono (hC p.1).2.1 (hD p.2).2.1,
      fun z hz => Prod.ext ((hC p.1).2.2 hz.1) ((hD p.2).2.2 hz.2)⟩
  · obtain ⟨U, hU, hxU, hUC⟩ := mem_nhdsWithin.mp hCx
    obtain ⟨V, hV, hyV, hVD⟩ := mem_nhdsWithin.mp hDy
    refine mem_nhdsWithin.mpr ⟨U ×ˢ V, hU.prod hV, ⟨hxU, hyV⟩, ?_⟩
    rintro z ⟨hzUV, hzPQ⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUC ⟨hzUV.1, hzPQ.1⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hVD ⟨hzUV.2, hzPQ.2⟩)
    exact mem_iUnion.mpr ⟨⟨i, j⟩, hi, hj⟩

theorem IsPiecewiseAffineOn.prodMap {f : E → F} {g : G → H}
    {P : Set E} {Q : Set G} (hf : IsPiecewiseAffineOn f P) (hg : IsPiecewiseAffineOn g Q) :
    IsPiecewiseAffineOn (Prod.map f g) (P ×ˢ Q) :=
  fun _ hx => (hf _ hx.1).prodMap (hg _ hx.2)

theorem IsPLHomeomorphOn.prodMap {f : E → F} {g : G → H}
    {P : Set E} {Q : Set F} {R : Set G} {S : Set H}
    (hf : IsPLHomeomorphOn f P Q) (hg : IsPLHomeomorphOn g R S) :
    IsPLHomeomorphOn (Prod.map f g) (P ×ˢ R) (Q ×ˢ S) := by
  have hbij := hf.bijOn.prodMap hg.bijOn
  refine ⟨hbij, hf.isPiecewiseAffineOn.prodMap hg.isPiecewiseAffineOn, ?_⟩
  have hinv := hf.isPiecewiseAffineOn_invFunOn.prodMap hg.isPiecewiseAffineOn_invFunOn
  apply hinv.congr
  intro x hx
  have hm := hf.bijOn.surjOn.mapsTo_invFunOn.prodMap hg.bijOn.surjOn.mapsTo_invFunOn
  have hu := hf.bijOn.invOn_invFunOn.2.prodMap hg.bijOn.invOn_invFunOn.2
  exact hbij.injOn (hbij.surjOn.mapsTo_invFunOn hx) (hm hx)
    ((hbij.invOn_invFunOn.2 hx).trans (hu hx).symm)

end DifferentialGeometry.Topology.PiecewiseLinear
