import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanProblem
import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanQuotient

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M] [T2Space M]
    {n p : ℕ}

omit [T2Space M] in
theorem adaptedPiecewiseLinearChart_of_affine_sections
    (K : SimplicialComplex ℝ E) (Q LQ : SimplicialComplex ℝ F)
    (f : C(K.space, M)) (g : C(Q.space, M)) (q : K.space → Q.space)
    (hfactor : ∀ x, g (q x) = f x) (hfixed : InjOn g (Subtype.val ⁻¹' LQ.space))
    (A : Set (Finset E))
    (hsections : ∀ t ∈ LQ.faces, ∃ s ∈ A, ∃ B : F →ᵃ[ℝ] E,
      ∀ y : Q.space, y.1 ∈ convexHull ℝ (t : Set F) →
        ∃ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ q x = y ∧ x.1 = B y.1)
    (b : BufferedChart M n)
    (haff : ∀ s ∈ A, ∃ C : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → f x ∈ b.core →
        b.chart (f x) = C x.1)
    (X : Set M) (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hT : T.faces.Finite) (hTdim : ∀ s ∈ T.faces, s.card ≤ p + 1)
    (hX : b.chart '' (X ∩ b.core) ⊆ T.space) :
    ∃ b' : AdaptedPiecewiseLinearChart Q LQ g X n p, b'.toBufferedChart = b := by
  refine ⟨{
    toBufferedChart := b
    fixed_affine := ?_
    fixed_injective := ?_
    obstacle := T
    obstacle_finite := hT
    obstacle_dimension := hTdim
    obstacle_contains := hX }, rfl⟩
  · intro t ht
    obtain ⟨s, hs, B, hB⟩ := hsections t ht
    obtain ⟨C, hC⟩ := haff s hs
    refine ⟨C.comp B, fun y hy hycore => ?_⟩
    obtain ⟨x, hx, hqx, hxy⟩ := hB y hy
    have hfg : f x = g y := (hfactor x).symm.trans (congrArg g hqx)
    change b.chart (g y) = C (B y.1)
    rw [← hxy, ← hfg]
    exact hC x hx (hfg.symm ▸ hycore)
  · intro x hx y hy hxy
    apply hfixed hx.1 hy.1
    have hxsource : g x ∈ b.chart.source := hx.2.1
    have hysource : g y ∈ b.chart.source := hy.2.1
    exact (b.chart.left_inv hxsource).symm.trans
      ((congrArg b.chart.symm hxy).trans (b.chart.left_inv hysource))

theorem hasAdaptedPiecewiseLinearCharts.descend_union
    {K L : SimplicialComplex ℝ E} {f : C(K.space, M)} {X : Set M}
    (h : hasAdaptedPiecewiseLinearCharts K L f X n p) (hK : K.faces.Finite)
    (D : SimplicialComplex ℝ E) (hD : D.faces.Finite)
    (Q LQ : SimplicialComplex ℝ F) (g : C(Q.space, M)) (q : K.space → Q.space)
    (hfactor : ∀ x, g (q x) = f x) (hfixed : InjOn g (Subtype.val ⁻¹' LQ.space))
    (hsections : ∀ t ∈ LQ.faces, ∃ s ∈ L.faces ∪ D.faces, ∃ B : F →ᵃ[ℝ] E,
      ∀ y : Q.space, y.1 ∈ convexHull ℝ (t : Set F) →
        ∃ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ q x = y ∧ x.1 = B y.1)
    (b : BufferedChart M n)
    (hnew : f '' (Subtype.val ⁻¹' D.space) ⊆ b.core)
    (haff : ∀ s ∈ L.faces ∪ D.faces, ∃ C : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → f x ∈ b.core →
        b.chart (f x) = C x.1)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hT : T.faces.Finite) (hTdim : ∀ s ∈ T.faces, s.card ≤ p + 1)
    (hX : b.chart '' (X ∩ b.core) ⊆ T.space) :
    hasAdaptedPiecewiseLinearCharts Q LQ g X n p := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (isCompact_space_of_finite_faces K hK)
  have hcompact : IsCompact (f '' (Subtype.val ⁻¹' D.space)) :=
    (((isCompact_space_of_finite_faces D hD).isClosed.preimage
      continuous_subtype_val).isCompact).image f.continuous
  intro y
  by_cases hy : y ∈ f '' (Subtype.val ⁻¹' D.space)
  · obtain ⟨b', hb'⟩ := adaptedPiecewiseLinearChart_of_affine_sections K Q LQ f g q hfactor hfixed
      (L.faces ∪ D.faces) hsections b haff X T hT hTdim hX
    exact ⟨b', hb'.symm ▸ hnew hy⟩
  · obtain ⟨c, hyc⟩ := h y
    obtain ⟨c', -, hyc', hcore⟩ := c.exists_recenter hyc hcompact.isClosed.isOpen_compl hy
    have havoid : Disjoint (f '' (Subtype.val ⁻¹' D.space)) c'.toBufferedChart.core :=
      disjoint_left.mpr (fun z hz hzc => (hcore hzc).2 hz)
    have haff' : ∀ s ∈ L.faces ∪ D.faces,
        ∃ C : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
          ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) →
            f x ∈ c'.toBufferedChart.core → c'.chart (f x) = C x.1 := by
      intro s hs
      rcases hs with hsL | hsD
      · exact c'.fixed_affine s hsL
      · refine ⟨0, fun x hx hxcore => ?_⟩
        exact (disjoint_left.mp havoid
          ⟨x, D.convexHull_subset_space hsD hx, rfl⟩ hxcore).elim
    obtain ⟨b', hb'⟩ := adaptedPiecewiseLinearChart_of_affine_sections K Q LQ f g q hfactor hfixed
      (L.faces ∪ D.faces) hsections c'.toBufferedChart haff' X c'.obstacle
        c'.obstacle_finite c'.obstacle_dimension c'.obstacle_contains
    exact ⟨b', hb'.symm ▸ hyc'⟩

section Problem

variable [DecidableEq E] [DecidableEq F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {M₁ : Type*} [MetricSpace M₁]

omit [DecidableEq E] [DecidableEq F] in
theorem exists_newman_quotient_problem
    (K L D R P : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hDK : D.faces ⊆ K.faces)
    (hRK : R.faces ⊆ K.faces) (hPK : P.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ D.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ D.faces, InjOn f (convexHull ℝ (s : Set E)))
    (F₀ : C(K.space, M₁))
    (hF : ∀ x y : K.space, x.1 ∈ D.space → y.1 ∈ D.space →
      (F₀ x = F₀ y ↔ f x.1 = f y.1))
    (hfixed : InjOn F₀ (Subtype.val ⁻¹' L.space))
    (hsat : ∀ x : K.space, x.1 ∈ D.space → ∀ y : K.space,
      y.1 ∈ L.space → F₀ y = F₀ x → y.1 ∈ D.space)
    {k : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ p + 2)
    (hRd : ∀ s ∈ R.faces, s.card ≤ p + 1) (hPd : ∀ s ∈ P.faces, s.card ≤ k)
    (hkp : k ≤ p + 1) {V X : Set M₁}
    (hcovered : ∀ x : K.space, x.1 ∈ R.space → F₀ x ∈ V)
    (hXclosed : IsClosed X) (hV : IsOpen V) (hXV : X ⊆ V)
    (hcodim : p + 3 ≤ n) (hconn : NewmanConnectivity M₁ V p)
    (hdata : hasAdaptedPiecewiseLinearCharts K L F₀ X n p)
    (b : BufferedChart M₁ n)
    (hnew : F₀ '' (Subtype.val ⁻¹' D.space) ⊆ b.core)
    (haff : ∀ s ∈ L.faces ∪ D.faces, ∃ C : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → F₀ x ∈ b.core →
        b.chart (F₀ x) = C x.1)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hT : T.faces.Finite) (hTdim : ∀ s ∈ T.faces, s.card ≤ p + 1)
    (hX : b.chart '' (X ∩ b.core) ⊆ T.space) :
    ∃ m : ℕ, ∃ N : NewmanProblem (EuclideanSpace ℝ (Fin m)) M₁ n p k,
      ∃ q : C(K.space, N.source.space),
        (∀ x, N.map (q x) = F₀ x) ∧ N.obstacle = X ∧ N.openSet = V ∧
        (Subtype.val ⁻¹' N.fixed.space = q '' (Subtype.val ⁻¹' (L.space ∪ D.space))) ∧
        (Subtype.val ⁻¹' N.target.space = q '' (Subtype.val ⁻¹' (R.space ∪ P.space))) := by
  classical
  obtain ⟨m, Q, LQ, DQ, q, G, hQ, hQdim, hLQ, hDQ, hDQdim, -, hfactor, -, hLspace,
    hDspace, hGinj, hdecomp, hsections⟩ :=
    exists_newman_quotient_data K L D R P hK hLK hDK hRK hPK f hf hinj F₀ hF
      hfixed hsat (d := p + 1) hd hRd hPd hkp hcovered
  have hbranches : ∀ t ∈ LQ.faces, ∃ s ∈ L.faces ∪ D.faces,
      ∃ B : EuclideanSpace ℝ (Fin m) →ᵃ[ℝ] E,
        ∀ y : Q.space, y.1 ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin m))) →
          ∃ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ q x = y ∧ x.1 = B y.1 := by
    intro t ht
    obtain ⟨s, hs, B, hB⟩ := hsections t ht
    rw [subcomplexPair_faces] at hs
    refine ⟨s, hs, B, fun y hy => ?_⟩
    obtain ⟨x, hxy, hx, hqx⟩ := hB y.1 hy
    exact ⟨x, hx, Subtype.ext hqx, hxy⟩
  have hGdata : hasAdaptedPiecewiseLinearCharts Q LQ G X n p := hdata.descend_union hK D (hK.subset hDK)
    Q LQ G q hfactor hGinj hbranches b hnew haff T hT hTdim hX
  let N : NewmanProblem (EuclideanSpace ℝ (Fin m)) M₁ n p k :=
    { source := Q
      fixed := LQ
      target := DQ
      source_finite := hQ
      fixed_subcomplex := hLQ
      target_subcomplex := hDQ
      source_dimension := hQdim
      target_dimension := hDQdim
      map := G
      fixed_injective := hGinj
      obstacle := X
      openSet := V
      obstacle_closed := hXclosed
      open_openSet := hV
      obstacle_subset := hXV
      localData := hGdata
      codimension := hcodim
      connectivity := hconn
      decomposition := hdecomp }
  exact ⟨m, N, q, hfactor, rfl, rfl, hLspace, hDspace⟩

end Problem

end DifferentialGeometry.Topology.Engulfing
