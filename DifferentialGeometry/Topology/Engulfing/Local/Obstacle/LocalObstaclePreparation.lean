import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.ExpansionSubcomplexNeighborhood
import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstacleApproximation

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_local_obstacle_preparation
    {M : Type*} [PseudoMetricSpace M] {n d p : ℕ}
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hT : T.faces.Finite)
    (hTp : ∀ s ∈ T.faces, s.card ≤ p + 1) (hpd : p ≤ d)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : C(K.space, M)) (c : EuclideanSpace ℝ (Fin n)) {r R ε : ℝ}
    (hrR : r < R) (hR : closedBall c R ⊆ e.target) (hε : 0 < ε)
    {A U : Set E} (hA : IsCompact A) (hAK : A ⊆ K.space)
    (hU : IsOpen U) (hAU : A ⊆ U)
    (hgsource : ∀ x : K.space, x.val ∈ U → g x ∈ e.source)
    (hgrange : ∀ x : K.space, x.val ∈ U → e (g x) ∈ closedBall c r)
    (hPL : ∀ s ∈ L.faces, ∃ F : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → x.val ∈ U → e (g x) = F x.val)
    (hinj : InjOn (fun x : K.space => e (g x)) (Subtype.val ⁻¹' (L.space ∩ U))) :
    ∃ (P J D : SimplicialComplex ℝ E) (_hP : P.faces.Finite) (hspace : P.space = K.space),
      let κ : P.space ≃ₜ K.space := Homeomorph.setCongr hspace
      simplicialRefines P K ∧ (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      J.faces.Finite ∧ J.faces ⊆ P.faces ∧ J.space = L.space ∧ simplicialRefines J L ∧
      D.faces.Finite ∧ D.faces ⊆ P.faces ∧ D.space ⊆ U ∧ A ⊆ D.space ∧
      (Subtype.val ⁻¹' A : Set P.space) ⊆ interior (Subtype.val ⁻¹' D.space) ∧
      (∀ S C, FiniteSimplexExpansionIn K S C → FiniteSimplexExpansionIn P S C) ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ R - r ∧
      ∃ fext : C(P.space, EuclideanSpace ℝ (Fin n)),
      (∀ x : P.space, x.val ∈ D.space → fext x = e (g (κ x))) ∧
      ∃ a : RelativeGeneralPositionApproximation P (D ⊓ J) T fext d p η,
      ∃ G : C(P.space, M), ∃ B : Set P.space,
      IsClosed B ∧ (Subtype.val ⁻¹' A : Set P.space) ⊆ interior B ∧
      B ⊆ interior (Subtype.val ⁻¹' D.space) ∧
      (∀ x : P.space, x.val ∉ U → G x = g (κ x)) ∧
      (∀ x : P.space, x.val ∈ L.space → G x = g (κ x)) ∧
      (∀ x, dist (G x) (g (κ x)) < ε) ∧
      (∀ x : P.space, x.val ∈ D.space → G x ∈ e.source) ∧
      (∀ x ∈ B, e (G x) = a.approximation x) := by
  obtain ⟨P, J, D, hP, hspace, href, hdim, hJ, hJP, hJs, hJref,
    hD, hDP, hDU, hAD, hAint, hexp⟩ :=
    exists_subcomplex_neighborhood_preserving_expansions K L hK hLK hA hAK hU hAU hd
  let κ : P.space ≃ₜ K.space := Homeomorph.setCongr hspace
  let gP : C(P.space, M) := g.comp ⟨κ, κ.continuous⟩
  have hclosedA : IsClosed (Subtype.val ⁻¹' A : Set P.space) :=
    hA.isClosed.preimage continuous_subtype_val
  obtain ⟨V, hV, hAV, hVlocal⟩ :=
    normal_exists_closure_subset hclosedA isOpen_interior hAint
  have hgDsource (x : D.space) : gP (subcomplexInclusion P D hDP x) ∈ e.source :=
    hgsource _ (hDU x.property)
  have hgDrange (x : D.space) :
      e (gP (subcomplexInclusion P D hDP x)) ∈ closedBall c r :=
    hgrange _ (hDU x.property)
  have hPLD : ∀ s ∈ (D ⊓ J).faces, ∃ F : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : D.space, x.val ∈ convexHull ℝ (s : Set E) →
        e (gP (subcomplexInclusion P D hDP x)) = F x.val := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hJref s hs.2
    obtain ⟨F, hF⟩ := hPL t ht
    exact ⟨F, fun x hx => hF _ (hst hx) (hDU x.property)⟩
  have hinjD : InjOn (fun x : D.space => e (gP (subcomplexInclusion P D hDP x)))
      (Subtype.val ⁻¹' J.space) := by
    intro x hx y hy he
    have hxL : x.val ∈ L.space := hJs.subset hx
    have hyL : y.val ∈ L.space := hJs.subset hy
    have hxy := hinj (x₁ := κ (subcomplexInclusion P D hDP x))
      (x₂ := κ (subcomplexInclusion P D hDP y))
      ⟨hxL, hDU x.property⟩ ⟨hyL, hDU y.property⟩ he
    exact Subtype.ext (congrArg (fun z : K.space => z.val) hxy)
  obtain ⟨η, hη, hηR, fext, hfext, a, G, hout, hfix, hnear, hsource, hcore⟩ :=
    exists_local_obstacle_approximation_on_subcomplex P hP D J hDP hJP hdim T hT hTp hpd
      e gP c hrR hR hε hgDsource hgDrange hPLD hinjD
      isClosed_closure isOpen_interior hVlocal subset_rfl
  refine ⟨P, J, D, hP, hspace, href, hdim, hJ, hJP, hJs, hJref,
    hD, hDP, hDU, hAD, hAint, hexp, η, hη, hηR, fext, ?_, a, G, closure V,
    isClosed_closure, ?_, hVlocal, ?_, ?_, hnear, ?_, hcore⟩
  · intro x hx
    exact hfext ⟨x.val, hx⟩
  · exact hAV.trans ((hV.subset_interior_iff).mpr subset_closure)
  · intro x hxU
    apply hout x
    intro hxV
    exact hxU (hDU (show x ∈ (Subtype.val ⁻¹' D.space : Set P.space) from
      interior_subset hxV))
  · intro x hxL
    exact hfix x (hJs.symm.subset hxL)
  · intro x hx
    exact hsource ⟨x.val, hx⟩

end

end DifferentialGeometry.Topology.Engulfing
