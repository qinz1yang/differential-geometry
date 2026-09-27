import DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryMeridianClass
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.CircleHomotopy
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy

open Set DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_nullhomotopic_graph
    {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (f : C(A × B, X)) (x : A) (e : loopCircle ≃ₜ B)
    (hs : Function.Surjective (fun a : FundamentalGroup A x =>
      FundamentalGroup.map f (x, e 0)
        ((fundamentalGroupProdEquiv x (e 0)).symm (a, 1)))) :
    ∃ g : C(B, A), (f.comp (g.prodMk (ContinuousMap.id B))).Nullhomotopic := by
  let q := circleGeneratorPath.map e.continuous
  let b : FundamentalGroup B (e 0) := Path.Homotopic.Quotient.mk q
  let φ := fundamentalGroupProdEquiv x (e 0)
  let T := φ.symm (1, b)
  obtain ⟨a, ha⟩ := hs ((FundamentalGroup.map f (x, e 0) T)⁻¹)
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  have hprod : Path.Homotopic.Quotient.mk (p.prod q) =
      φ.symm (Path.Homotopic.Quotient.mk p, 1) * T := by
    apply φ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    change (fundamentalGroupProdEquiv x (e 0))
      (Path.Homotopic.prod (Path.Homotopic.Quotient.mk p) b) = _
    rw [fundamentalGroupProdEquiv_apply, Path.Homotopic.projLeft_prod,
      Path.Homotopic.projRight_prod]
    refine Prod.ext ?_ ?_
    · change FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) * 1
      exact (mul_one _).symm
    · change b = (1 : FundamentalGroup B (e 0)) * b
      exact (one_mul b).symm
  have hnull : (pathToCircle ((p.prod q).map f.continuous)).Nullhomotopic := by
    apply (pathToCircle_nullhomotopic_iff _).mpr
    apply Path.Homotopic.Quotient.eq.mp
    change FundamentalGroup.map f (x, e 0)
      (Path.Homotopic.Quotient.mk (p.prod q)) = 1
    change FundamentalGroup.map f (x, e 0)
      (φ.symm (Path.Homotopic.Quotient.mk p, 1)) = _ at ha
    rw [hprod, map_mul, ha, inv_mul_cancel]
  let g := (pathToCircle p).comp (e.symm : C(B, loopCircle))
  let G := g.prodMk (ContinuousMap.id B)
  have heq : pathToCircle ((p.prod q).map f.continuous) =
      (f.comp G).comp (e : C(loopCircle, B)) := by
    ext θ
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    rw [pathToCircle_coe]
    change f (p t, e (circleGeneratorPath t)) =
      f (pathToCircle p (e.symm (e ((t : ℝ) : loopCircle))), e ((t : ℝ) : loopCircle))
    rw [e.symm_apply_apply, pathToCircle_coe]
    rfl
  rw [heq] at hnull
  refine ⟨g, ?_⟩
  have h := hnull.comp_left (e.symm : C(B, loopCircle))
  convert h using 1
  ext z
  exact congrArg (f.comp G) (e.apply_symm_apply z).symm


theorem exists_PL_meridian_graph_of_surjective_longitudes
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace X]
    {J : Set E} {Q : Set F} (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    (f : C(J × Q, X)) (x : J) (y : Q)
    (hs : Function.Surjective (fun a : FundamentalGroup J x =>
      FundamentalGroup.map f (x, y) ((fundamentalGroupProdEquiv x y).symm (a, 1)))) :
    ∃ (g : F → E) (G : C(Q, J × Q)), IsPiecewiseAffineOn g Q ∧ MapsTo g Q J ∧
      (∀ q, ((G q).1 : E) = g q ∧ (G q).2 = q) ∧
      IsPLHomeomorphOn (fun q => (g q, q)) Q ((fun q => (g q, q)) '' Q) ∧
      IsPLSphere 1 ((fun q => (g q, q)) '' Q) ∧
      (∀ q ∈ Q, ((fun q => (g q, q)) '' Q) ∩ (J ×ˢ {q}) = {(g q, q)}) ∧
      ¬ G.Nullhomotopic ∧ (f.comp G).Nullhomotopic := by
  classical
  obtain ⟨K, hKfin, rfl⟩ := hQ.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, rfl⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨e₀⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hQ
  let e := (Homeomorph.addLeft (e₀.symm y)).trans e₀
  have he : e 0 = y := by simp [e]
  obtain ⟨a, ha⟩ := exists_nullhomotopic_graph f x e (by rw [he]; exact hs)
  let a' : F → E := fun q => if h : q ∈ K.space then (a ⟨q, h⟩ : E) else 0
  have ha' (q : K.space) : a' q = (a q : E) := dif_pos q.2
  have hcont : ContinuousOn a' K.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp a.continuous).congr fun q => (ha' q).symm
  have hmap : MapsTo a' K.space L.space := by
    intro q hq
    rw [ha' ⟨q, hq⟩]
    exact (a ⟨q, hq⟩).2
  obtain ⟨g, hg, hgmap, -, hhom⟩ :=
    exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic K L hcont hmap zero_lt_one
  let ag : C(K.space, L.space) :=
    ⟨fun q => ⟨g q, hgmap q.2⟩, hg.continuousOn.domRestrict.subtype_mk _⟩
  have hahom : a.Homotopic ag := by
    convert hhom using 1
    exact ContinuousMap.ext fun q => Subtype.ext (ha' q).symm
  let G := ag.prodMk (ContinuousMap.id K.space)
  have hinj : InjOn (fun q => (g q, q)) K.space :=
    fun _ _ _ _ heq => congrArg Prod.snd heq
  have hgraph : IsPLHomeomorphOn (fun q => (g q, q)) K.space
      ((fun q => (g q, q)) '' K.space) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hQ.isPolyhedron
      (hg.prod_mk hQ.isPolyhedron.isPLHomeomorphOn_id.isPiecewiseAffineOn)
      hinj.bijOn_image
  refine ⟨g, G, hg, hgmap, fun _ => ⟨rfl, rfl⟩, hgraph,
    hQ.of_isPLHomeomorphOn hgraph, ?_, ?_⟩
  · intro q hq
    ext z
    constructor
    · rintro ⟨⟨r, -, rfl⟩, -, hrq⟩
      have hr : r = q := hrq
      subst r
      rfl
    · rintro rfl
      exact ⟨⟨q, hq, rfl⟩, hgmap hq, rfl⟩
  · constructor
    · intro hh
      have hid : (ContinuousMap.id K.space).Nullhomotopic := hh.comp_right ContinuousMap.snd
      let _ := (contractible_iff_id_nullhomotopic K.space).mpr hid
      exact hQ.not_simplyConnectedSpace_one inferInstance
    · obtain ⟨z, hz⟩ := ha
      refine ⟨z, ?_⟩
      exact ((ContinuousMap.Homotopic.refl f).comp
        (hahom.prodMk (ContinuousMap.Homotopic.refl _))).symm.trans hz


theorem IsPLHomeomorphInto.exists_PL_meridian_of_marked_boundary_product
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C J Q : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (J ×ˢ Q) (frontier C)) (x : J) (y : Q)
    {S : Set M} (hS : IsTopologicalSolidTorus S) (hCS : u '' C ⊆ S)
    (hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {(y : EuclideanSpace ℝ (Fin 3))})) S) :
    ∃ (r : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (B : C(Q, frontier C)) (H : C(Q, u '' C)),
      IsPLHomeomorphOn r Q (r '' Q) ∧ IsPLSphere 1 (r '' Q) ∧ r '' Q ⊆ frontier C ∧
      (∀ q, (B q : EuclideanSpace ℝ (Fin 3)) = r q) ∧
      (∀ q, (H q : M) = u (r q)) ∧ ¬ B.Nullhomotopic ∧ H.Nullhomotopic ∧
      ∀ q ∈ Q, ∃ p ∈ J, (r '' Q) ∩ (f '' (J ×ˢ {q})) = {f (p, q)} := by
  obtain ⟨F, hF, l, -, -, -, -, hlgen, -, -⟩ :=
    hu.exists_meridian_class_of_marked_boundary_product hC hCP hJ hQ hf x y hS hCS hgen
  have hs : Function.Surjective (fun a : FundamentalGroup J x =>
      FundamentalGroup.map F (x, y) ((fundamentalGroupProdEquiv x y).symm (a, 1))) := by
    intro a
    obtain ⟨n, hn⟩ := hlgen a
    refine ⟨l ^ n, ?_⟩
    have hp : (l ^ n, (1 : FundamentalGroup Q y)) = (l, (1 : FundamentalGroup Q y)) ^ n := by
      refine Prod.ext rfl ?_
      change (1 : FundamentalGroup Q y) = 1 ^ n
      exact (one_zpow n).symm
    change FundamentalGroup.map F (x, y)
      ((fundamentalGroupProdEquiv x y).symm (l ^ n, 1)) = a
    rw [hp, map_zpow, map_zpow]
    exact hn
  obtain ⟨g, G, -, hgmap, hG, hgraph, hgraphS, -, hnon, hnull⟩ :=
    exists_PL_meridian_graph_of_surjective_longitudes hJ hQ F x y hs
  let r := f ∘ (fun q => (g q, q))
  have hsub : (fun q => (g q, q)) '' Q ⊆ J ×ˢ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hgmap hq, hq⟩
  have hr : IsPLHomeomorphOn r Q (r '' Q) := by
    have h := hgraph.trans (hf.restrict hgraphS.isPolyhedron hsub)
    rwa [← image_comp] at h
  have hrsub : r '' Q ⊆ frontier C := by
    rintro _ ⟨q, hq, rfl⟩
    exact hf.bijOn.mapsTo ⟨hgmap hq, hq⟩
  let B : C(Q, frontier C) :=
    ⟨fun q => ⟨r q, hrsub ⟨q, q.2, rfl⟩⟩,
      hr.isPiecewiseAffineOn.continuousOn.domRestrict.subtype_mk _⟩
  let v := Function.invFunOn f (J ×ˢ Q)
  have hv (z : frontier C) : v z ∈ J ×ˢ Q := hf.symm.bijOn.mapsTo z.2
  have hvc : Continuous (fun z : frontier C => v z) :=
    hf.symm.isPiecewiseAffineOn.continuousOn.domRestrict
  let V : C(frontier C, J × Q) :=
    ⟨fun z => (⟨(v z).1, (hv z).1⟩, ⟨(v z).2, (hv z).2⟩),
      ((continuous_fst.comp hvc).subtype_mk _).prodMk
        ((continuous_snd.comp hvc).subtype_mk _)⟩
  have hVB : V.comp B = G := by
    apply ContinuousMap.ext
    intro q
    apply Prod.ext <;> apply Subtype.ext
    · have hi := hf.bijOn.invOn_invFunOn.1
        (show (g q, (q : EuclideanSpace ℝ (Fin 3))) ∈ J ×ˢ Q from ⟨hgmap q.2, q.2⟩)
      change (v (r q)).1 = ((G q).1 : EuclideanSpace ℝ (Fin 3))
      exact (congrArg Prod.fst hi).trans (hG q).1.symm
    · have hi := hf.bijOn.invOn_invFunOn.1
        (show (g q, (q : EuclideanSpace ℝ (Fin 3))) ∈ J ×ˢ Q from ⟨hgmap q.2, q.2⟩)
      change (v (r q)).2 = ((G q).2 : EuclideanSpace ℝ (Fin 3))
      exact (congrArg Prod.snd hi).trans (congrArg Subtype.val (hG q).2).symm
  refine ⟨r, B, F.comp G, hr, hQ.of_isPLHomeomorphOn hr, hrsub, fun _ => rfl,
    ?_, ?_, hnull, ?_⟩
  · intro q
    rw [ContinuousMap.comp_apply, hF]
    change u (f (((G q).1 : EuclideanSpace ℝ (Fin 3)), (G q).2)) = u (f (g q, q))
    rw [(hG q).1, (hG q).2]
  · intro hh
    apply hnon
    rw [← hVB]
    exact hh.comp_right V
  · intro q hq
    refine ⟨g q, hgmap hq, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, ⟨⟨p, s⟩, ⟨hp, hs⟩, heq⟩⟩
      have hs' : s = q := hs
      subst s
      have hpair := hf.bijOn.injOn ⟨hp, hq⟩ ⟨hgmap ht, ht⟩ heq
      have htq : t = q := (congrArg Prod.snd hpair).symm
      subst t
      rfl
    · rintro rfl
      exact ⟨⟨q, hq, rfl⟩, ⟨(g q, q), ⟨hgmap hq, rfl⟩, rfl⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
