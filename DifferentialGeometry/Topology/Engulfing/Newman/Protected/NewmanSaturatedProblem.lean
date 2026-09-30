import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanLocalSaturation
import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanQuotientData

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] {n p q : ℕ}

omit [DecidableEq E] in
theorem exists_newman_problem_of_local_saturation
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
    (hcore : ∀ x : K.space, F x ∈ b.core →
      x ∈ interior (Subtype.val ⁻¹' C.space))
    (B T O : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hB : B.faces.Finite) (hT : T.faces.Finite) (hO : O.faces.Finite)
    (hTB : T.space ⊆ B.space) (hBcore : b.chart.symm '' B.space ⊆ b.core)
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
  obtain ⟨G, L', D, R, P, hG, hspace, href, hGdim, hL'G, hL'space, hL'ref,
    hDG, hRG, hPG, hDspace, hRspace, hPspace, -, hRdim, hPdim, hDaff, hDinj,
    J, hJG, hJspace, hJaff, -⟩ :=
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
  have hcovers (x : G.space) (hx : F' x ∈ b.chart.source)
      (hb : b.chart (F' x) ∈ B.space) : x.1 ∈ C.space := by
    have hbc : F' x ∈ b.core := hBcore ⟨b.chart (F' x), hb, b.chart.left_inv hx⟩
    have hmem : e x ∈ Subtype.val ⁻¹' C.space := interior_subset (hcore (e x) hbc)
    exact hmem
  obtain ⟨hsat, hnew, hRcovered, -⟩ := chart_saturation_properties
    (Subtype.val : G.space → E) a F' b.chart hC_range hDset hRset hPspace
      hcoord' hcovers hTB
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
  have hcore' (x : G.space) (hx : F' x ∈ b.core) :
      x ∈ interior (Subtype.val ⁻¹' J.space) := by
    rw [hJspace]
    have h := hcore (e x) hx
    change x ∈ e ⁻¹' interior (Subtype.val ⁻¹' C.space) at h
    rw [e.preimage_interior] at h
    exact h
  have haff := exists_chart_affine_on_source_faces G J hJG a hJaff F' b.chart b.core
    hcore' (fun x hx => by
      have hxJ : x ∈ Subtype.val ⁻¹' J.space := interior_subset (hcore' x hx)
      exact (hcoord' x (hJspace ▸ hxJ)).2)
  obtain ⟨m, N, π₀, hfactor, hNX, hNV, hNL, hNT⟩ :=
    exists_newman_quotient_problem G L' D R P hG hL'G hDG hRG hPG a hDaff hDinj F'
      hfiber hfixed' (fun x hx y _ hxy => hsat x hx y hxy) hGdim hRdim hPdim hqp
      (fun x hx => hcovered (by
        obtain ⟨y, hy, heq⟩ := hRcovered (mem_image_of_mem F' hx)
        exact ⟨e y, hy, heq⟩)) hX hV hXV hcodim hconn hdata' b
      (hnew.trans hBcore) (fun s hs => haff s (hs.elim (fun h => hL'G h) (fun h => hDG h)))
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
