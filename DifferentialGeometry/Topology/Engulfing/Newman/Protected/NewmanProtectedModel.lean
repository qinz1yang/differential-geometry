import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanLocalSaturation
import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanQuotientData

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] {n p q : ℕ}

omit [DecidableEq E] in
theorem exists_newman_problem_of_protected_model
    (K L C H : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hCK : C.faces ⊆ K.faces) (hHK : H.faces ⊆ K.faces)
    (a : E → EuclideanSpace ℝ (Fin n))
    (ha : ∀ s ∈ C.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn a A (convexHull ℝ (s : Set E)))
    (hainj : ∀ s ∈ C.faces, InjOn a (convexHull ℝ (s : Set E)))
    (F : C(K.space, M)) (hfixed : InjOn F (Subtype.val ⁻¹' L.space))
    (hd : ∀ s ∈ K.faces, s.card ≤ p + 2)
    (hHd : ∀ s ∈ H.faces, s.card ≤ p + 1)
    {X V : Set M} (hX : IsClosed X) (hV : IsOpen V) (hXV : X ⊆ V)
    (hcovered : F '' (Subtype.val ⁻¹' H.space) ⊆ V)
    (hcodim : p + 3 ≤ n) (hconn : NewmanConnectivity M V p)
    (hdata : hasAdaptedPiecewiseLinearCharts K L F X n p)
    (b : BufferedChart M n)
    (hcoords : ∀ x : K.space, x.1 ∈ C.space →
      F x ∈ b.chart.source ∧ b.chart (F x) = a x.1)
    (hLaff : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → F x ∈ b.core →
        b.chart (F x) = A x.1)
    (B T O : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hB : B.faces.Finite) (hT : T.faces.Finite) (hO : O.faces.Finite)
    (hTB : T.space ⊆ B.space) (hBcore : b.chart.symm '' B.space ⊆ b.core)
    (hLcovers : ∀ x : K.space, x.1 ∈ L.space → F x ∈ b.chart.source →
      b.chart (F x) ∈ B.space → x.1 ∈ C.space)
    (hTd : ∀ t ∈ T.faces, t.card ≤ q) (hqp : q ≤ p + 1)
    (hOd : ∀ t ∈ O.faces, t.card ≤ p + 1)
    (hXO : b.chart '' (X ∩ b.core) ⊆ O.space) :
    ∃ m : ℕ, ∃ N : NewmanProblem (EuclideanSpace ℝ (Fin m)) M n p q,
      ∃ π : C(K.space, N.source.space),
        (∀ x, N.map (π x) = F x) ∧ N.obstacle = X ∧ N.openSet = V ∧
        (Subtype.val ⁻¹' N.fixed.space = π '' (Subtype.val ⁻¹'
          (L.space ∪ localProtectedSet a C.space H.space B.space T.space))) ∧
        (Subtype.val ⁻¹' N.target.space = π '' (Subtype.val ⁻¹'
          (localCoveredSet a C.space H.space B.space ∪ (C.space ∩ a ⁻¹' T.space)))) ∧
        IsCompact (Subtype.val ⁻¹'
          (localCoveredSet a C.space H.space B.space ∪ (C.space ∩ a ⁻¹' T.space)) : Set K.space) := by
  classical
  obtain ⟨G, L', D, R, P, hG, hspace, -, hGdim, hL'G, hL'space, hL'ref,
    hDG, hRG, hPG, hDspace, hRspace, hPspace, -, hRdim, hPdim, hDaff, hDinj,
    -, -, -, -, -⟩ :=
    exists_global_local_saturation K L C H hK hLK hCK hHK a ha hainj B T hB hT
      (d := p + 1) hd hHd hTd hqp
  let e : G.space ≃ₜ K.space := Homeomorph.setCongr hspace
  let F' : C(G.space, M) := F.comp ⟨e, e.continuous⟩
  have hF' (x : G.space) : F' x = F (e x) := rfl
  have hcoord' (x : G.space) (hx : x.1 ∈ C.space) :
      F' x ∈ b.chart.source ∧ b.chart (F' x) = a x.1 := hcoords (e x) hx
  have hC_range : C.space ⊆ range (Subtype.val : G.space → E) := by
    intro x hx
    exact ⟨⟨x, hspace.symm ▸ subcomplex_space_subset K C hCK hx⟩, rfl⟩
  have hDset : D.space = localProtectedSet a C.space H.space B.space T.space := hDspace
  have hRset : R.space = localCoveredSet a C.space H.space B.space := hRspace
  have hDpre : (Subtype.val ⁻¹' D.space : Set G.space) =
      localProtectedSet (a ∘ Subtype.val) (Subtype.val ⁻¹' C.space)
        (Subtype.val ⁻¹' H.space) B.space T.space := by
    rw [hDset, localProtectedSet_preimage Subtype.val a hC_range]
  have hRpre : (Subtype.val ⁻¹' R.space : Set G.space) =
      localCoveredSet (a ∘ Subtype.val) (Subtype.val ⁻¹' C.space)
        (Subtype.val ⁻¹' H.space) B.space := by
    rw [hRset, localCoveredSet_preimage Subtype.val a hC_range]
  have hsat : ∀ x : G.space, x.1 ∈ D.space → ∀ y : G.space,
      y.1 ∈ L'.space → F' y = F' x → y.1 ∈ D.space := by
    intro x hx y hy hxy
    have hx' : x ∈ localProtectedSet (a ∘ Subtype.val) (Subtype.val ⁻¹' C.space)
        (Subtype.val ⁻¹' H.space) B.space T.space := hDpre ▸ hx
    have hy' := localProtectedSet_saturated_on F' (a ∘ Subtype.val) b.chart
      hcoord' hTB (L := Subtype.val ⁻¹' L'.space)
      (fun y hy hs hb => hLcovers (e y) (hL'space ▸ hy) hs hb) x hx' y hy hxy
    change y ∈ localProtectedSet (a ∘ Subtype.val) (Subtype.val ⁻¹' C.space)
      (Subtype.val ⁻¹' H.space) B.space T.space at hy'
    rwa [← hDpre] at hy'
  have hnew : F' '' (Subtype.val ⁻¹' D.space) ⊆ b.chart.symm '' B.space := by
    rw [hDpre]
    exact localProtectedSet_image_subset F' (a ∘ Subtype.val) b.chart hcoord' hTB
  have hRcovered : F' '' (Subtype.val ⁻¹' R.space) ⊆ F' '' (Subtype.val ⁻¹' H.space) := by
    rw [hRpre]
    exact localCoveredSet_image_subset F' (a ∘ Subtype.val) b.chart hcoord'
  have hDf (x : G.space) (hx : x.1 ∈ D.space) : x.1 ∈ C.space := by
    rw [hDset] at hx
    exact hx.1
  have hfiber (x y : G.space) (hx : x.1 ∈ D.space) (hy : y.1 ∈ D.space) :
      F' x = F' y ↔ a x.1 = a y.1 := by
    have hx' := hcoord' x (hDf x hx)
    have hy' := hcoord' y (hDf y hy)
    constructor
    · intro heq
      exact hx'.2.symm.trans ((congrArg b.chart heq).trans hy'.2)
    · intro heq
      apply b.chart.injOn hx'.1 hy'.1
      exact hx'.2.trans (heq.trans hy'.2.symm)
  have hfixed' : InjOn F' (Subtype.val ⁻¹' L'.space) := by
    intro x hx y hy hxy
    apply e.injective
    exact hfixed (hL'space ▸ hx) (hL'space ▸ hy) hxy
  have hdata' : hasAdaptedPiecewiseLinearCharts G L' F' X n p :=
    hdata.refine G L' hspace hL'ref hL'space.subset F' (fun _ => rfl)
  have haff : ∀ s ∈ L'.faces ∪ D.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : G.space, x.1 ∈ convexHull ℝ (s : Set E) → F' x ∈ b.core →
        b.chart (F' x) = A x.1 := by
    intro s hs
    rcases hs with hs | hs
    · obtain ⟨t, ht, hst⟩ := hL'ref s hs
      obtain ⟨A, hA⟩ := hLaff t ht
      exact ⟨A, fun x hx hxcore => hA (e x) (hst hx) hxcore⟩
    · obtain ⟨A, hA⟩ := hDaff s hs
      refine ⟨A, fun x hx _ => ?_⟩
      exact (hcoord' x (hDf x (D.convexHull_subset_space hs hx))).2.trans (hA hx)
  obtain ⟨m, N, π₀, hfactor, hNX, hNV, hNL, hNT⟩ :=
    exists_newman_quotient_problem G L' D R P hG hL'G hDG hRG hPG a hDaff hDinj F'
      hfiber hfixed' hsat hGdim hRdim hPdim hqp
      (fun x hx => hcovered (by
        obtain ⟨y, hy, heq⟩ := hRcovered (mem_image_of_mem F' hx)
        exact ⟨e y, hy, heq⟩)) hX hV hXV hcodim hconn hdata' b
      (hnew.trans hBcore) haff
      O hO hOd hXO
  let π : C(K.space, N.source.space) := π₀.comp ⟨e.symm, e.symm.continuous⟩
  refine ⟨m, N, π, ?_, hNX, hNV, ?_, ?_, ?_⟩
  · intro x
    exact (hfactor (e.symm x)).trans (congrArg F (e.apply_symm_apply x))
  · rw [hNL, hL'space, hDset]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, hx, congrArg π₀ (e.symm_apply_apply x)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.symm x, hx, rfl⟩
  · rw [hNT, hRset, hPspace]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, hx, congrArg π₀ (e.symm_apply_apply x)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.symm x, hx, rfl⟩
  · let : CompactSpace K.space := isCompact_iff_compactSpace.mp
      (isCompact_space_of_finite_faces K hK)
    rw [← hRset, ← hPspace]
    exact (((isCompact_space_of_finite_faces R (hG.subset hRG)).union
      (isCompact_space_of_finite_faces P (hG.subset hPG))).isClosed.preimage
        continuous_subtype_val).isCompact

end DifferentialGeometry.Topology.Engulfing
