import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanProtectedModel
import DifferentialGeometry.Topology.Engulfing.Newman.Step.NewmanPartialChartStep

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] {n p q : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq E] in
theorem exists_simplex_step_of_protected_model
    (hlower : relativeNewmanAt M n p q)
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
    (hXO : b.chart '' (X ∩ b.core) ⊆ O.space)
    {A B₀ U S : Set K.space} (hA : IsCompact A) (hB₀ : IsClosed B₀) (hU : IsOpen U)
    (hB₀U : B₀ ⊆ U) (hUA : U ⊆ interior A)
    (hHlocal : (Subtype.val ⁻¹' H.space : Set K.space) ∩ U ⊆ Subtype.val ⁻¹' C.space)
    (hUcoords : ∀ x ∈ U, F x ∈ b.chart.source ∧ b.chart (F x) ∈ B.space)
    (c : EuclideanSpace ℝ (Fin n)) {r r' ε : ℝ} (hrr' : r < r')
    (hr' : closedBall c r' ⊆ b.chart.target)
    (hsource : ∀ x ∈ A, F x ∈ b.chart.source)
    (hrange : ∀ x ∈ A, b.chart (F x) ∈ closedBall c r)
    (s : SimplexSplit ι) (v : ι → EuclideanSpace ℝ (Fin n))
    (hv : AffineIndependent ℝ v)
    (hσ : convexHull ℝ (range v) ⊆ b.chart.target)
    (hTσ : T.space ⊆ convexHull ℝ (range v))
    (hσimage : convexHull ℝ (range v) ⊆ a '' C.space)
    (hTcolumns : s.columnSaturation v hv T.space = T.space)
    (hFS : F '' S ⊆ b.chart.symm '' convexHull ℝ (range v))
    (hbuffer : F ⁻¹' (b.chart.symm '' convexHull ℝ (range v)) ⊆ B₀)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    (hWbounded : Bornology.IsBounded W) (hWa : closure W ⊆ b.chart.target)
    (hmoving : convexHull ℝ (range v) \ s.lowerRoof v ⊆ W)
    (hattach : b.chart.symm ⁻¹' (X ∪ F '' (Subtype.val ⁻¹' H.space)) ∩
      convexHull ℝ (range v) ⊆ s.lowerRoof v ∪ T.space)
    (hroof : b.chart.symm '' s.lowerRoof v ⊆ F '' (Subtype.val ⁻¹' H.space))
    (hε : 0 < ε) :
    ∃ (G : C(K.space, M)) (h : M ≃ₜ M),
      EqOn G F (Subtype.val ⁻¹' L.space) ∧ EqOn G F B₀ ∧
      (∀ x, dist (G x) (F x) < ε) ∧
      X ∪ G '' ((Subtype.val ⁻¹' H.space) ∪ S) ⊆ h '' V ∧
      IsCompact (closure {x | h x ≠ x}) ∧
      EqOn G F (Subtype.val ⁻¹' localProtectedSet a C.space H.space B.space T.space) := by
  classical
  let D : Set K.space := Subtype.val ⁻¹' localProtectedSet a C.space H.space B.space T.space
  let R : Set K.space := Subtype.val ⁻¹'
    (localCoveredSet a C.space H.space B.space ∪ (C.space ∩ a ⁻¹' T.space))
  have hC_range : C.space ⊆ range (Subtype.val : K.space → E) := by
    intro x hx
    exact ⟨⟨x, subcomplex_space_subset K C hCK hx⟩, rfl⟩
  have hcoord' : ∀ x ∈ (Subtype.val ⁻¹' C.space : Set K.space),
      F x ∈ b.chart.source ∧ b.chart (F x) = (a ∘ Subtype.val) x := hcoords
  have hRset : R = localCoveredSet (a ∘ Subtype.val)
      (Subtype.val ⁻¹' C.space) (Subtype.val ⁻¹' H.space) B.space ∪
        ((Subtype.val ⁻¹' C.space) ∩ (a ∘ Subtype.val) ⁻¹' T.space) := by
    rw [localCoveredSet_preimage Subtype.val a hC_range]
    rfl
  have hDset : D = localProtectedSet (a ∘ Subtype.val)
      (Subtype.val ⁻¹' C.space) (Subtype.val ⁻¹' H.space) B.space T.space :=
    (localProtectedSet_preimage Subtype.val a hC_range).symm
  have hlocal : R ∩ U ⊆ D := by
    rw [hRset, hDset]
    exact local_target_inter_subset_protected_of_local_cover F (a ∘ Subtype.val) b.chart
      hcoord' hHlocal hUcoords
  obtain ⟨m, N, π, hfactor, hNX, hNV, hNfixed, hNtarget, hRcompact⟩ :=
    exists_newman_problem_of_protected_model K L C H hK hLK hCK hHK a ha hainj
      F hfixed hd hHd hX hV hXV hcovered hcodim hconn hdata b hcoords hLaff
      B T O hB hT hO hTB hBcore hLcovers hTd hqp hOd hXO
  have hπfixed : ∀ x ∈ ((Subtype.val ⁻¹' L.space) ∪ D) ∪ (R ∩ U),
      (π x).1 ∈ N.fixed.space := by
    intro x hx
    have hx' : x ∈ Subtype.val ⁻¹'
        (L.space ∪ localProtectedSet a C.space H.space B.space T.space) :=
      hx.elim (fun h => h) (fun h => Or.inr (hlocal h))
    have hmem := mem_image_of_mem π hx'
    rw [← hNfixed] at hmem
    exact hmem
  have hπtarget : ∀ x ∈ R, (π x).1 ∈ N.target.space := by
    intro x hx
    have hmem := mem_image_of_mem π hx
    rw [← hNtarget] at hmem
    exact hmem
  have hconclusion : ∀ δ : ℝ, 0 < δ →
      newmanConclusion N.source N.fixed N.target N.map X V δ := by
    intro δ hδ
    have h := hlower (EuclideanSpace ℝ (Fin m)) N δ hδ
    change newmanConclusion N.source N.fixed N.target N.map N.obstacle N.openSet δ at h
    rwa [hNX, hNV] at h
  have hTimage : T.space ⊆ (a ∘ Subtype.val) '' (Subtype.val ⁻¹' C.space : Set K.space) := by
    intro t ht
    obtain ⟨x, hx, hxt⟩ := hσimage (hTσ ht)
    exact ⟨⟨x, subcomplex_space_subset K C hCK hx⟩, hx, hxt⟩
  have hattach' : b.chart.symm ⁻¹' (X ∪ F '' R) ∩ convexHull ℝ (range v) ⊆
      s.lowerRoof v ∪ T.space := by
    rw [hRset]
    exact localTargetSet_attachment F (a ∘ Subtype.val) b.chart hcoord'
      hTimage hTσ hσ hattach
  have hroofcolumns : b.chart.symm '' (s.lowerRoof v ∪ T.space) ⊆ F '' (R ∩ U) := by
    rw [hRset]
    exact localTargetSet_roof_columns F (a ∘ Subtype.val) b.chart hcoord'
      hTimage hTσ (s.lowerRoof_subset_simplex v) hroof (hbuffer.trans hB₀U)
  have hroof' : b.chart.symm '' s.lowerRoof v ⊆ X ∪ F '' (R ∩ U) :=
    (image_mono subset_union_left).trans (hroofcolumns.trans subset_union_right)
  have hcolumns' : b.chart.symm '' s.columnSaturation v hv T.space ⊆ X ∪ F '' (R ∩ U) := by
    rw [hTcolumns]
    exact (image_mono subset_union_right).trans (hroofcolumns.trans subset_union_right)
  have havoid : Disjoint (F '' (R \ U)) (b.chart.symm '' convexHull ℝ (range v)) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    exact hx.2 (hB₀U (hbuffer hy))
  obtain ⟨G, h, hfix, -, hnear, hcover, hcompact, hBfix⟩ :=
    exists_simplex_step_of_lower_quotient_partial_chart N.source N.fixed N.target N.map
      π F hfactor hRcompact hX hV hπfixed hπtarget b.chart hA hB₀ hU hB₀U hUA
      c hrr' hr' hsource hrange s v hv b.chart
      (fun x hx => hbuffer (hFS (mem_image_of_mem F hx))) hFS havoid
      (isCompact_space_of_finite_faces T hT) hW hWbounded hWa hσ hmoving
      hattach' hroof' hcolumns' hconclusion hε
  refine ⟨G, h, hfix.mono subset_union_left, hBfix, hnear, ?_, hcompact,
    hfix.mono subset_union_right⟩
  apply subset_trans _ hcover
  apply union_subset_union_right
  apply image_mono
  apply union_subset_union_left
  intro x hx
  exact Or.inl (Or.inl hx)

end DifferentialGeometry.Topology.Engulfing
