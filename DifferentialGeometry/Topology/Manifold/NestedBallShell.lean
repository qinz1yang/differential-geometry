import DifferentialGeometry.Topology.Manifold.EmbeddedBallShell

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem transport_parametrization
    {G H P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace P] [ChartedSpace H P]
    {I : ModelWithCorners ℝ G H}
    (e : PartialEquiv P E) (hes : e.source = univ)
    (he : ContMDiff I 𝓘(ℝ, E) ∞ e) (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hsub : e.target ⊆ φ.source) :
    ∃ d : PartialEquiv P E, d.source = univ ∧ d.target = φ '' e.target ∧
      ContMDiff I 𝓘(ℝ, E) ∞ d ∧ ContMDiffOn 𝓘(ℝ, E) I ∞ d.symm d.target := by
  let d := e.trans φ.toPartialEquiv
  have hds : d.source = univ := by
    ext p
    constructor
    · exact fun _ ↦ mem_univ _
    · intro _
      have hp : p ∈ e.source := hes ▸ mem_univ p
      exact ⟨hp, hsub (e.map_source hp)⟩
  have hdt : d.target = φ '' e.target := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨φ.symm x, hy, φ.right_inv hx⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨φ.map_source (hsub hy), ?_⟩
      change φ.symm.toPartialEquiv (φ.toPartialEquiv y) ∈ e.target
      have hid : φ.symm.toPartialEquiv (φ.toPartialEquiv y) = y := φ.left_inv (hsub hy)
      exact hid.symm ▸ hy
  refine ⟨d, hds, hdt, ?_, ?_⟩
  · apply contMDiffOn_univ.mp
    exact φ.contMDiffOn_toFun.comp he.contMDiffOn
      (fun p _ ↦ hsub (e.map_source (hes ▸ mem_univ p)))
  · exact hei.comp (φ.contMDiffOn_invFun.mono (fun _ hx ↦ hx.1)) (fun _ hx ↦ hx.2)

theorem exists_smooth_nestedBallShell_parametrization
    {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (outer inner : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r R : ℝ} (hr : 0 < r)
    (houter : closedBall (0 : E) R ⊆ outer.source)
    (hinner : closedBall (0 : E) r ⊆ inner.source)
    (hnested : inner '' closedBall 0 r ⊆ outer '' ball 0 R)
    (v : sphere (0 : E) 1) :
    ∃ e : PartialEquiv (sphere (0 : E) 1 × unitInterval) E,
      e.source = univ ∧ e.target = outer '' closedBall 0 R \ inner '' ball 0 r ∧
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ e ∧
      ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod (𝓡∂ 1)) ∞ e.symm e.target := by
  let ψ := inner.trans outer.symm
  have himem (x : E) (hx : x ∈ closedBall 0 r) : inner x ∈ outer.target := by
    obtain ⟨y, hy, heq⟩ := hnested ⟨x, hx, rfl⟩
    exact heq ▸ outer.map_source (houter (ball_subset_closedBall hy))
  have hψs : closedBall (0 : E) r ⊆ ψ.source := fun x hx ↦ ⟨hinner hx, himem x hx⟩
  have hψsub : ψ '' closedBall 0 r ⊆ ball 0 R := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, heq⟩ := hnested ⟨x, hx, rfl⟩
    change outer.symm.toPartialEquiv (inner.toPartialEquiv x) ∈ ball 0 R
    have hi : outer.symm.toPartialEquiv (inner.toPartialEquiv x) = z := by
      rw [← heq]
      exact outer.left_inv (houter (ball_subset_closedBall hz))
    exact hi.symm ▸ hz
  have hcancel (x : E) (hx : x ∈ closedBall 0 r) :
      outer.toPartialEquiv (ψ.toPartialEquiv x) = inner.toPartialEquiv x :=
    outer.right_inv (himem x hx)
  obtain ⟨e, hes, het, he, hei⟩ :=
    exists_smooth_embeddedBallShell_parametrization (n := n) ψ hr hψs hψsub v
  have hesub : e.target ⊆ outer.source := by
    rw [het]
    exact fun _ hx ↦ houter hx.1
  obtain ⟨d, hds, hdt, hd, hdi⟩ := transport_parametrization e hes he hei outer hesub
  refine ⟨d, hds, ?_, hd, hdi⟩
  rw [hdt, het]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨z, hz, heq⟩
    apply hxn
    refine ⟨z, hz, ?_⟩
    apply outer.toPartialEquiv.injOn
      (ball_subset_closedBall (hψsub ⟨z, ball_subset_closedBall hz, rfl⟩) |> houter)
      (houter hx)
    exact (hcancel z (ball_subset_closedBall hz)).trans heq
  · rintro ⟨⟨x, hx, hxy⟩, hyn⟩
    refine ⟨x, ⟨hx, ?_⟩, hxy⟩
    rintro ⟨z, hz, hzx⟩
    apply hyn
    refine ⟨z, hz, ?_⟩
    exact (hcancel z (ball_subset_closedBall hz)).symm.trans
      ((congrArg outer.toPartialEquiv hzx).trans hxy)

end Poincare.Topology.Manifold
