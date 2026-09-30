import DifferentialGeometry.Topology.Engulfing.Obstacle.Approximation.ObstacleGeneralPosition
import DifferentialGeometry.Topology.Engulfing.Local.Charts.LocalOptimalApproximation
import Mathlib.Topology.TietzeExtension

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem exists_extension_from_finite_subcomplex {n : ℕ}
    (K D : SimplicialComplex ℝ E) (hD : D.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : C(D.space, EuclideanSpace ℝ (Fin n))) :
    ∃ g : C(K.space, EuclideanSpace ℝ (Fin n)),
      ∀ x : D.space, g (subcomplexInclusion K D hDK x) = f x := by
  let : CompactSpace D.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces D hD)
  let : TietzeExtension (EuclideanSpace ℝ (Fin n)) :=
    TietzeExtension.of_homeo (PiLp.homeomorph 2 (fun _ : Fin n => ℝ))
  have hi : Function.Injective (subcomplexInclusion K D hDK) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : K.space => z.val) h)
  obtain ⟨g, hg⟩ := f.exists_extension'
    ((subcomplexInclusion K D hDK).continuous.isClosedEmbedding hi)
  exact ⟨g, fun x => congrFun hg x⟩

theorem exists_local_obstacle_approximation_on_subcomplex
    {M : Type*} [PseudoMetricSpace M] {n d p : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (D L : SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hT : T.faces.Finite)
    (hTp : ∀ s ∈ T.faces, s.card ≤ p + 1) (hpd : p ≤ d)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : C(K.space, M)) (c : EuclideanSpace ℝ (Fin n)) {r R ε : ℝ}
    (hrR : r < R) (hR : closedBall c R ⊆ e.target) (hε : 0 < ε)
    (hgsource : ∀ x : D.space, g (subcomplexInclusion K D hDK x) ∈ e.source)
    (hgrange : ∀ x : D.space, e (g (subcomplexInclusion K D hDK x)) ∈ closedBall c r)
    (hPL : ∀ s ∈ (D ⊓ L).faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : D.space, x.val ∈ convexHull ℝ (s : Set E) →
        e (g (subcomplexInclusion K D hDK x)) = A x.val)
    (hinj : InjOn (fun x : D.space => e (g (subcomplexInclusion K D hDK x)))
      (Subtype.val ⁻¹' L.space))
    {B U : Set K.space} (hB : IsClosed B) (hU : IsOpen U) (hBU : B ⊆ U)
    (hUD : U ⊆ interior (Subtype.val ⁻¹' D.space)) :
    ∃ η : ℝ, 0 < η ∧ η ≤ R - r ∧
      ∃ f : C(K.space, EuclideanSpace ℝ (Fin n)),
      (∀ x : D.space, f (subcomplexInclusion K D hDK x) =
        e (g (subcomplexInclusion K D hDK x))) ∧
      ∃ a : RelativeGeneralPositionApproximation K (D ⊓ L) T f d p η,
      ∃ G : C(K.space, M),
      (∀ x ∉ U, G x = g x) ∧ (∀ x : K.space, x.val ∈ L.space → G x = g x) ∧
      (∀ x, dist (G x) (g x) < ε) ∧
      (∀ x : D.space, G (subcomplexInclusion K D hDK x) ∈ e.source) ∧
      (∀ x ∈ B, e (G x) = a.approximation x) := by
  let A : Set K.space := Subtype.val ⁻¹' D.space
  have hD : D.faces.Finite := hK.subset hDK
  have hA : IsClosed A := (isCompact_space_of_finite_faces D hD).isClosed.preimage continuous_subtype_val
  have hIspace := subcomplex_inf_space K D L hDK hLK
  let gD : C(D.space, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => e (g (subcomplexInclusion K D hDK x)), e.continuousOn.comp_continuous
      (g.continuous.comp (subcomplexInclusion K D hDK).continuous) hgsource⟩
  obtain ⟨f, hf⟩ := exists_extension_from_finite_subcomplex K D hD hDK gD
  have hfD (x : K.space) (hx : x.val ∈ D.space) : f x = e (g x) := hf ⟨x.val, hx⟩
  have hfPL : ∀ s ∈ (D ⊓ L).faces, ∃ a : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → f x = a x.val := by
    intro s hs
    obtain ⟨a, ha⟩ := hPL s hs
    refine ⟨a, fun x hx => ?_⟩
    have hxD := D.convexHull_subset_space hs.1 hx
    exact (hfD x hxD).trans (ha ⟨x.val, hxD⟩ hx)
  have hfinj : InjOn f (Subtype.val ⁻¹' (D ⊓ L).space) := by
    intro x hx y hy he
    rw [hIspace] at hx hy
    have hfx := hfD x hx.1
    have hfy := hfD y hy.1
    rw [hfx, hfy] at he
    exact Subtype.ext (congrArg (fun z : D.space => z.val)
      (hinj (x₁ := ⟨x.val, hx.1⟩) (x₂ := ⟨y.val, hy.1⟩) hx.2 hy.2 he))
  obtain ⟨η, hη, hηR, hblend⟩ := exists_chart_blend_tolerance (X := K.space) e c hrR hR hε
  obtain ⟨a⟩ := exists_relativeGeneralPositionApproximation K (D ⊓ L) hK
    (fun _ hs => hDK hs.1) T hT hd hTp hpd f hfPL hfinj hη
  let fA : C(A, EuclideanSpace ℝ (Fin n)) :=
    a.approximation.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hnear (x : A) : ‖fA x - e (g x)‖ < η := by
    change ‖a.approximation x.val - e (g x.val)‖ < η
    rw [← hfD x.val x.property]
    exact a.near x.val
  have hgsourceA (x : A) : g x ∈ e.source := hgsource ⟨x.val.val, x.property⟩
  have hgrangeA (x : A) : e (g x) ∈ closedBall c r := hgrange ⟨x.val.val, x.property⟩
  obtain ⟨G, hcore, hout, hfix, hnearG, hsourceG⟩ :=
    hblend hA hB hU hBU hUD g fA hgsourceA hgrangeA hnear
  refine ⟨η, hη, hηR, f, hf, a, G, hout, ?_, hnearG,
    (fun x => hsourceG ⟨subcomplexInclusion K D hDK x, x.property⟩), ?_⟩
  · intro x hxL
    by_cases hxD : x.val ∈ D.space
    · apply hfix ⟨x, hxD⟩
      exact (a.relative x (hIspace.symm.subset ⟨hxD, hxL⟩)).trans (hfD x hxD)
    · exact hout x (fun hxU => hxD
        (show x ∈ Subtype.val ⁻¹' D.space from interior_subset (hUD hxU)))
  · intro x hxB
    have hxD : x.val ∈ D.space :=
      show x ∈ Subtype.val ⁻¹' D.space from interior_subset (hUD (hBU hxB))
    let xA : A := ⟨x, hxD⟩
    have hball : fA xA ∈ closedBall c R := by
      apply mem_closedBall.mpr
      have hgdist := mem_closedBall.mp (hgrangeA xA)
      have hfdist : dist (fA xA) (e (g xA)) < η := by simpa only [dist_eq_norm] using hnear xA
      have ht := dist_triangle (fA xA) (e (g xA)) c
      linarith
    have he := congrArg e (hcore xA hxB)
    rw [e.right_inv (hR hball)] at he
    exact he

end

end DifferentialGeometry.Topology.Engulfing
