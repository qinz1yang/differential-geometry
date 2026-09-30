import DifferentialGeometry.Topology.Engulfing.Newman.Step.NewmanLocalStep
import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanQuotientData

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E F M : Type*} [DecidableEq E] [DecidableEq F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MetricSpace M]
    {n p k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq E] [DecidableEq F] in
theorem exists_simplex_step_of_relativeNewman
    (hlower : relativeNewmanAt M n p k)
    (K L D R P : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hDK : D.faces ⊆ K.faces)
    (hRK : R.faces ⊆ K.faces) (hPK : P.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ D.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ D.faces, InjOn f (convexHull ℝ (s : Set E)))
    (F₀ : C(K.space, M))
    (hF : ∀ x y : K.space, x.1 ∈ D.space → y.1 ∈ D.space →
      (F₀ x = F₀ y ↔ f x.1 = f y.1))
    (hfixed : InjOn F₀ (Subtype.val ⁻¹' L.space))
    (hsat : ∀ x : K.space, x.1 ∈ D.space → ∀ y : K.space,
      y.1 ∈ L.space → F₀ y = F₀ x → y.1 ∈ D.space)
    (hd : ∀ s ∈ K.faces, s.card ≤ p + 2)
    (hRd : ∀ s ∈ R.faces, s.card ≤ p + 1) (hPd : ∀ s ∈ P.faces, s.card ≤ k)
    (hkp : k ≤ p + 1) {V X : Set M}
    (hcovered : ∀ x : K.space, x.1 ∈ R.space → F₀ x ∈ V)
    (hXclosed : IsClosed X) (hV : IsOpen V) (hXV : X ⊆ V)
    (hcodim : p + 3 ≤ n) (hconn : NewmanConnectivity M V p)
    (hdata : hasAdaptedPiecewiseLinearCharts K L F₀ X n p)
    (b : BufferedChart M n)
    (hnew : F₀ '' (Subtype.val ⁻¹' D.space) ⊆ b.core)
    (haff : ∀ s ∈ L.faces ∪ D.faces, ∃ C : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → F₀ x ∈ b.core →
        b.chart (F₀ x) = C x.1)
    (T₀ : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hT₀ : T₀.faces.Finite) (hT₀dim : ∀ s ∈ T₀.faces, s.card ≤ p + 1)
    (hXchart : b.chart '' (X ∩ b.core) ⊆ T₀.space)
    {A B U S : Set K.space} (hA : IsCompact A) (hB : IsClosed B) (hU : IsOpen U)
    (hBU : B ⊆ U) (hUA : U ⊆ interior A)
    (hlocal : (Subtype.val ⁻¹' (R.space ∪ P.space)) ∩ U ⊆ Subtype.val ⁻¹' D.space)
    (c : EuclideanSpace ℝ (Fin n)) {r r' ε : ℝ} (hrr' : r < r')
    (hr' : closedBall c r' ⊆ b.chart.target)
    (hsource : ∀ x ∈ A, F₀ x ∈ b.chart.source)
    (hrange : ∀ x ∈ A, b.chart (F₀ x) ∈ closedBall c r)
    (s : SimplexSplit ι) (v : ι → EuclideanSpace ℝ (Fin n))
    (hv : AffineIndependent ℝ v) {j : EuclideanSpace ℝ (Fin n) → M}
    (hj : IsOpenEmbedding j) (hSB : S ⊆ B)
    (hFS : F₀ '' S ⊆ j '' convexHull ℝ (range v))
    (havoid : Disjoint (F₀ '' ((Subtype.val ⁻¹' (R.space ∪ P.space)) \ U))
      (j '' convexHull ℝ (range v)))
    {T W : Set (EuclideanSpace ℝ (Fin n))} (hT : IsCompact T) (hW : IsOpen W)
    (hWbounded : Bornology.IsBounded W)
    (hmoving : convexHull ℝ (range v) \ s.lowerRoof v ⊆ W)
    (hattach : j ⁻¹' (X ∪ F₀ '' (Subtype.val ⁻¹' (R.space ∪ P.space))) ∩
      convexHull ℝ (range v) ⊆ s.lowerRoof v ∪ T)
    (hroof : j '' s.lowerRoof v ⊆
      X ∪ F₀ '' ((Subtype.val ⁻¹' (R.space ∪ P.space)) ∩ U))
    (hcolumns : j '' s.columnSaturation v hv T ⊆
      X ∪ F₀ '' ((Subtype.val ⁻¹' (R.space ∪ P.space)) ∩ U)) (hε : 0 < ε) :
    ∃ (G : C(K.space, M)) (H : M ≃ₜ M),
      EqOn G F₀ (Subtype.val ⁻¹' L.space) ∧ EqOn G F₀ S ∧
      (∀ x, dist (G x) (F₀ x) < ε) ∧
      X ∪ G '' ((Subtype.val ⁻¹' (R.space ∪ P.space)) ∪ S) ⊆ H '' V ∧
      IsCompact (closure {x | H x ≠ x}) ∧ EqOn G F₀ B := by
  classical
  obtain ⟨m, N, q, hfactor, hNX, hNV, hNfixed, hNtarget⟩ :=
    exists_newman_quotient_problem K L D R P hK hLK hDK hRK hPK f hf hinj F₀ hF
      hfixed hsat hd hRd hPd hkp hcovered hXclosed hV hXV hcodim hconn hdata
      b hnew haff T₀ hT₀ hT₀dim hXchart
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (isCompact_space_of_finite_faces K hK)
  have htargetCompact : IsCompact (Subtype.val ⁻¹' (R.space ∪ P.space) : Set K.space) :=
    (((isCompact_space_of_finite_faces R (hK.subset hRK)).union
      (isCompact_space_of_finite_faces P (hK.subset hPK))).isClosed.preimage
        continuous_subtype_val).isCompact
  have hqfixed : ∀ x ∈ (Subtype.val ⁻¹' L.space) ∪
      ((Subtype.val ⁻¹' (R.space ∪ P.space)) ∩ U), (q x).1 ∈ N.fixed.space := by
    intro x hx
    have hx' : x.1 ∈ L.space ∪ D.space := hx.elim Or.inl (fun hx => Or.inr (hlocal hx))
    have hmem : q x ∈ q '' (Subtype.val ⁻¹' (L.space ∪ D.space)) :=
      mem_image_of_mem q hx'
    rw [← hNfixed] at hmem
    exact hmem
  have hqtarget : ∀ x ∈ (Subtype.val ⁻¹' (R.space ∪ P.space)),
      (q x).1 ∈ N.target.space := by
    intro x hx
    have hmem := mem_image_of_mem q hx
    rw [← hNtarget] at hmem
    exact hmem
  have hconclusion : ∀ δ : ℝ, 0 < δ →
      newmanConclusion N.source N.fixed N.target N.map X V δ := by
    intro δ hδ
    have h := hlower (EuclideanSpace ℝ (Fin m)) N δ hδ
    change newmanConclusion N.source N.fixed N.target N.map N.obstacle N.openSet δ at h
    rwa [hNX, hNV] at h
  exact exists_simplex_step_of_lower_quotient N.source N.fixed N.target N.map q F₀
    hfactor htargetCompact hXclosed hV hqfixed hqtarget b.chart hA hB hU hBU hUA
    c hrr' hr' hsource hrange s v hv hj hSB hFS havoid hT hW hWbounded hmoving
    hattach hroof hcolumns hconclusion hε

end DifferentialGeometry.Topology.Engulfing
