import DifferentialGeometry.Topology.PiecewiseLinear.Section34EmptyReturningBigon
import DifferentialGeometry.Topology.PiecewiseLinear.Section34NullMeridianReturningArc
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RotatedMeridianSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_empty_bigon_of_nullhomotopic_circle
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} {S J : Set F} {d : (Fin 3 → ℝ) → E}
    (hf : IsCylindricalDiagram f P S) (hd : IsPLHomeomorphOn d (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J)
    (hJside : J ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1))
    (hJS : J ⊆ S)
    (hnull : (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic)
    {a b s : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hs : s ∈ Ioo a b)
    (hfinite : (J ∩ f '' (P ×ˢ {s})).Finite)
    (hgerms : ∀ x ∈ P, f (x, s) ∈ J →
      (x, s) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | y.2 < s}) ∧
        (x, s) ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | s < y.2}))
    (hne : (J ∩ f '' (P ×ˢ {s})).Nonempty) :
    ∃ (D : Set F) (q : (Fin 3 → ℝ) → F) (x y : F),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ f '' ((d '' stdSimplexBoundary 2) ×ˢ Icc 0 1) ∧
      IsPLBall 1 (D ∩ J) ∧
      IsPLBall 1 (D ∩ f '' ((d '' stdSimplexBoundary 2) ×ˢ ({s} : Set ℝ))) ∧
      x ≠ y ∧ D ∩ (J ∩ f '' ((d '' stdSimplexBoundary 2) ×ˢ ({s} : Set ℝ))) = {x, y} ∧
      q '' stdSimplexBoundary 2 =
        (D ∩ J) ∪ (D ∩ f '' ((d '' stdSimplexBoundary 2) ×ˢ ({s} : Set ℝ))) := by
  have hP : IsPLBall 2 P := ⟨d, hd⟩
  let Z := d '' stdSimplexBoundary 2
  have hZP : Z ⊆ P := (image_mono fun _ hx => hx.1).trans hd.image_eq.subset
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
  obtain ⟨g, hg, hge, hcarriers, hrot⟩ :=
    hf.exists_seam_rotation hP.isPolyhedron hends hs01
  have hgends : ∀ x ∈ P, g (x, 0) = g (x, 1) := fun x hx =>
    (hge x hx).1.trans (hge x hx).2.symm
  have hJg : J ⊆ g '' (Z ×ˢ Icc (0 : ℝ) 1) := by
    rw [hcarriers Z hZP]
    exact hJside
  obtain ⟨η, γ, hη0, hη1, hγ, hγside, hγends, hγJ, -⟩ :=
    hf.exists_returning_source_arc_of_nullhomotopic_circle hd hends hJ hJside hJS hnull
      ha hb hs hrot hfinite hgerms hne
  have hseam : ∀ c ∈ Ioo (0 : ℝ) 1,
      ∀ y ∈ J ∩ g '' (Z ×ˢ ({1} : Set ℝ)),
        y ∈ closure (J ∩ g '' (Z ×ˢ Ioo c 1)) ∧
        y ∈ closure (J \ g '' (Z ×ˢ Icc c 1)) := by
    intro c hc
    obtain ⟨hin, hout⟩ :=
      hf.seam_subset_closure_sides_of_rotation hg hs01 hrot ha hb hgerms hc
    exact hg.seam_sides_of_subset_lateral hZP hJg hc.1
      (fun y hy => ⟨hin hy, hout hy⟩)
  obtain ⟨D, q, x, y, hq, hDside, hDJ, hDL, hxy, htrace, hqbd⟩ :=
    hg.exists_empty_returning_bigon hd hgends hJ hJg hseam hγ ⟨hη0, hη1⟩
      hγside (image_subset_iff.mp hγJ) hγends
  have hslice : g '' (Z ×ˢ ({1} : Set ℝ)) = f '' (Z ×ˢ ({s} : Set ℝ)) := by
    ext z
    constructor
    · rintro ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩
      have ht1 : t = 1 := ht
      subst t
      exact ⟨(p, s), ⟨hp, rfl⟩, (hge p (hZP hp)).2.symm⟩
    · rintro ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩
      have hts : t = s := ht
      subst t
      exact ⟨(p, 1), ⟨hp, rfl⟩, (hge p (hZP hp)).2⟩
  change D ⊆ g '' (Z ×ˢ Icc (0 : ℝ) 1) at hDside
  rw [hcarriers Z hZP] at hDside
  change IsPLBall 1 (D ∩ g '' (Z ×ˢ ({1} : Set ℝ))) at hDL
  change D ∩ (J ∩ g '' (Z ×ˢ ({1} : Set ℝ))) = {x, y} at htrace
  change q '' stdSimplexBoundary 2 = (D ∩ J) ∪ (D ∩ g '' (Z ×ˢ ({1} : Set ℝ))) at hqbd
  rw [hslice] at hDL htrace hqbd
  exact ⟨D, q, x, y, hq, hDside, hDJ, hDL, hxy, htrace, hqbd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
