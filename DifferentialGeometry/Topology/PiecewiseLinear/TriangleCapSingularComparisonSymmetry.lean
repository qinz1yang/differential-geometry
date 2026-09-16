import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCapSingularComparison

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_triangle_cap_with_singular_comparison_of_cap_below
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} {Q Q' D J C : Set E}
    {u v : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) Q)
    (hv : IsPLHomeomorphOn v (stdSimplex ℝ (Fin 3)) D)
    (huJ : u '' stdSimplexBoundary 2 = J) (hvJ : v '' stdSimplexBoundary 2 = J)
    (hQD : IsPLSphere 2 (Q ∪ D)) (hunion : Q ∪ Q' = K.space)
    (hQ' : IsClosed Q') (hinter : Q ∩ Q' ⊆ D) (hQDinter : Q ∩ D ⊆ J)
    (hDlevel : D ⊆ {x | ℓ x = ℓ p}) (hDC : D ⊆ C) (hC : IsCompact C)
    (hsep : ∀ q ∈ K.vertices \ {p}, Disjoint C {x | ℓ x = ℓ q})
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hfix : EqOn H id Cᶜ)
    (hfixV : EqOn H id (K.vertices \ {p})) (hheight : ∀ x, ℓ (H x) = ℓ x)
    (e : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] E)
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)))
    (hcard : T.card = 3) (he : Function.Injective e)
    (htriangle : H '' D = e '' convexHull ℝ (T : Set _))
    (hhalf : (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ x ≤ ℓ q) ∨
      (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ q ≤ ℓ x))
    (hboundary : ∀ q ∈ J \ {p},
      ∀ᶠ x in 𝓝 q, x ∈ J ↔ x ∈ Q ∧ ℓ x = ℓ q) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = H '' (Q ∪ D) ∧ IsPLSphere 2 R.space ∧
      ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 →
        InjOn f (R.vertices ∪ ((T.image e : Finset E) : Set E)) →
        (∀ x ∈ H '' D \ {H p}, f x < f (H p)) →
        heightSingularPoints R.space f \ {H p} ⊆
            heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R.space f ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ Q) ∧
          (levelPolygons R.space f (f q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard := by
  have hℓNeg : -ℓ ≠ 0 := neg_ne_zero.mpr hℓ
  have hinjNeg : InjOn (-ℓ) K.vertices := by
    intro x hx y hy hxy
    exact hinj hx hy (neg_injective hxy)
  have hDlevelNeg : D ⊆ {x | (-ℓ) x = (-ℓ) p} := by
    intro x hx
    simpa only [Set.mem_ofPred_eq, neg_apply, neg_inj] using hDlevel hx
  have hsepNeg : ∀ q ∈ K.vertices \ {p}, Disjoint C {x | (-ℓ) x = (-ℓ) q} := by
    intro q hq
    simpa only [neg_apply, neg_inj] using hsep q hq
  have hheightNeg : ∀ x, (-ℓ) (H x) = (-ℓ) x := by
    intro x
    simp only [neg_apply, hheight]
  have hhalfNeg :
      (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → (-ℓ) x ≤ (-ℓ) q) ∨
      (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → (-ℓ) q ≤ (-ℓ) x) := by
    rcases hhalf with hhalf | hhalf
    · right
      intro q hq
      filter_upwards [hhalf q hq] with x hx
      intro hxQ
      simpa only [neg_apply, neg_le_neg_iff] using hx hxQ
    · left
      intro q hq
      filter_upwards [hhalf q hq] with x hx
      intro hxQ
      simpa only [neg_apply, neg_le_neg_iff] using hx hxQ
  have hboundaryNeg : ∀ q ∈ J \ {p},
      ∀ᶠ x in 𝓝 q, x ∈ J ↔ x ∈ Q ∧ (-ℓ) x = (-ℓ) q := by
    intro q hq
    simpa only [neg_apply, neg_inj] using hboundary q hq
  obtain ⟨R, hRfin, hRspace, hR, hcompare⟩ :=
    exists_triangle_cap_with_singular_comparison hdimE K hK (-ℓ) hℓNeg hinjNeg
      hu hv huJ hvJ hQD hunion hQ' hinter hQDinter hDlevelNeg hDC hC hsepNeg
      H hH hfix hfixV hheightNeg e T hT hcard he htriangle hhalfNeg hboundaryNeg
  have ht : Filter.Tendsto (fun f : E →L[ℝ] ℝ => -f) (𝓝 ℓ) (𝓝 (-ℓ)) :=
    continuous_neg.continuousAt
  have hcompare' := ht.eventually hcompare
  refine ⟨R, hRfin, hRspace, hR, ?_⟩
  filter_upwards [hcompare'] with f hf
  intro hfne hfinj hbelow
  have hfneNeg : -f ≠ 0 := neg_ne_zero.mpr hfne
  have hfinjNeg : InjOn (-f) (R.vertices ∪ ((T.image e : Finset E) : Set E)) := by
    intro x hx y hy hxy
    exact hfinj hx hy (neg_injective hxy)
  have haboveNeg : ∀ x ∈ H '' D \ {H p}, (-f) (H p) < (-f) x := by
    intro x hx
    simpa only [neg_apply, neg_lt_neg_iff] using hbelow x hx
  obtain ⟨hsubset, hpoints⟩ := hf hfneNeg hfinjNeg haboveNeg
  have hnegf : (fun x => (-f) x) = fun x => -f x := by
    funext x
    exact neg_apply f x
  have hnegℓ : (fun x => (-ℓ) x) = fun x => -ℓ x := by
    funext x
    exact neg_apply ℓ x
  have hsubset' : heightSingularPoints R.space f \ {H p} ⊆
      heightSingularPoints K.space ℓ \ {p} := by
    simpa only [hnegf, hnegℓ, heightSingularPoints_neg] using hsubset
  refine ⟨hsubset', ?_⟩
  intro q hq
  have hpoint := hpoints q hq
  simpa only [hnegf, hnegℓ, heightSingularPoints_neg, neg_apply, levelPolygons_neg]
    using hpoint

end DifferentialGeometry.Topology.PiecewiseLinear
