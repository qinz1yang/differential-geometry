import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanSaturatedStep
import DifferentialGeometry.Topology.Engulfing.Local.Buffers.RestorationBuffers

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] {n p q : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq E] in
theorem exists_simplex_step_of_buffered_local_model
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
    (hcore : ∀ x : K.space, F x ∈ b.core →
      x ∈ interior (Subtype.val ⁻¹' C.space))
    (T O : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hT : T.faces.Finite) (hO : O.faces.Finite)
    (hTd : ∀ t ∈ T.faces, t.card ≤ q) (hqp : q ≤ p + 1)
    (hOd : ∀ t ∈ O.faces, t.card ≤ p + 1)
    (hXO : b.chart '' (X ∩ b.core) ⊆ O.space)
    (s : SimplexSplit ι) (v : ι → EuclideanSpace ℝ (Fin n))
    (hv : AffineIndependent ℝ v) {r₀ ε : ℝ} (hr₀ : r₀ < b.innerRadius)
    (hσball : convexHull ℝ (range v) ⊆ closedBall b.center r₀)
    (hTσ : T.space ⊆ convexHull ℝ (range v))
    (hσimage : convexHull ℝ (range v) ⊆ a '' C.space)
    (hTcolumns : s.columnSaturation v hv T.space = T.space)
    {S : Set K.space} (hFS : F '' S ⊆ b.chart.symm '' convexHull ℝ (range v))
    (hattach : b.chart.symm ⁻¹' (X ∪ F '' (Subtype.val ⁻¹' H.space)) ∩
      convexHull ℝ (range v) ⊆ s.lowerRoof v ∪ T.space)
    (hroof : b.chart.symm '' s.lowerRoof v ⊆ F '' (Subtype.val ⁻¹' H.space))
    (hε : 0 < ε) :
    ∃ (G : C(K.space, M)) (h : M ≃ₜ M),
      EqOn G F (Subtype.val ⁻¹' L.space) ∧
      EqOn G F (F ⁻¹' (b.chart.symm '' closedBall b.center r₀)) ∧
      (∀ x, dist (G x) (F x) < ε) ∧
      X ∪ G '' ((Subtype.val ⁻¹' H.space) ∪ S) ⊆ h '' V ∧
      IsCompact (closure {x | h x ≠ x}) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (isCompact_space_of_finite_faces K hK)
  let rU := (r₀ + b.innerRadius) / 2
  let rA := (rU + b.innerRadius) / 2
  have hr₀U : r₀ < rU := by dsimp [rU]; linarith
  have hrU : rU < b.innerRadius := by dsimp [rU]; linarith
  have hUA : rU < rA := by dsimp [rA]; linarith
  have hrA : rA < b.innerRadius := by dsimp [rA]; linarith
  have hAR : rA < b.outerRadius := hrA.trans b.radii_lt
  obtain ⟨B, hB, hBinside, hBoutside⟩ := exists_finite_complex_between_balls b.center hrU
  have hBcore : b.chart.symm '' B.space ⊆ b.core := by
    rintro _ ⟨y, hy, rfl⟩
    have hyball := hBoutside hy
    have hytarget : y ∈ b.chart.target := b.outer_subset
      (closedBall_subset_closedBall b.radii_lt.le (ball_subset_closedBall hyball))
    exact ⟨b.chart.map_target hytarget, by
      change b.chart (b.chart.symm y) ∈ ball b.center b.innerRadius
      rwa [b.chart.right_inv hytarget]⟩
  have hTB : T.space ⊆ B.space := hTσ.trans
    (hσball.trans ((closedBall_subset_closedBall hr₀U.le).trans hBinside))
  obtain ⟨A, B₀, U, hA, hB₀, hU, hB₀U, hUA', hsource, hrange, hB₀eq, hUeq, hbuffer⟩ :=
    exists_restoration_buffers_of_chart_balls F b.chart b.center hr₀U hUA hAR b.outer_subset
  have hUcoords : ∀ x ∈ U, F x ∈ b.chart.source ∧ b.chart (F x) ∈ B.space := by
    intro x hx
    rw [hUeq] at hx
    exact ⟨hx.1, hBinside (ball_subset_closedBall hx.2)⟩
  have hσtarget : convexHull ℝ (range v) ⊆ b.chart.target := hσball.trans
    ((closedBall_subset_closedBall (hr₀.trans b.radii_lt).le).trans b.outer_subset)
  obtain ⟨G, h, hfix, hBfix, hnear, hcover, hcompact⟩ :=
    exists_simplex_step_of_local_saturation hlower K L C H hK hLK hCK hHK a ha hainj
      F hfixed hd hHd hX hV hXV hcovered hcodim hconn hdata b hcoords hcore
      B T O hB hT hO hTB hBcore hTd hqp hOd hXO hA hB₀ hU hB₀U hUA' hUcoords
      b.center hAR b.outer_subset hsource hrange s v hv hσtarget hTσ hσimage hTcolumns hFS
      (hbuffer _ (image_mono hσball)).1 isOpen_ball isBounded_ball
      ((closure_ball_subset_closedBall).trans
        ((closedBall_subset_closedBall b.radii_lt.le).trans b.outer_subset))
      (sdiff_subset.trans (hσball.trans (closedBall_subset_ball hr₀))) hattach hroof hε
  rw [hB₀eq] at hBfix
  exact ⟨G, h, hfix, hBfix, hnear, hcover, hcompact⟩

end DifferentialGeometry.Topology.Engulfing
