import DifferentialGeometry.Topology.Planar.PolygonGraphCharts
import DifferentialGeometry.Topology.Diffeomorph.LevelTransport

open scoped ContDiff Manifold Topology

namespace Schoenflies

theorem PrePolygon.exists_compactly_supported_isotopy_near_one_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax (1 / 4) (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0) := by
  dsimp only
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign⟩ :=
    P.exists_regular_interpolation_near_one_edge_free_triangle M hfrontier T k hfree
  obtain ⟨K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_compactly_supported_proportional_vector_field
      hF.fst hF.snd ((hU₀.union hU₁).union hV) hJ hJW
      (fun t ht p hp _ => hregH t ht p (hJW hp)) (by
        intro t ht p hp hz hpJ
        rcases hexterior t ht p hp hz hpJ with ⟨_, _, N, hN, hpN, hNU, he⟩ |
          ⟨_, _, N, hN, hpN, hNU, he⟩
        · exact ⟨_, div_pos hfc₀ hfb, N, hN, hpN,
            fun q hq => Or.inl (Or.inl (hNU hq).1), he⟩
        · exact ⟨_, div_pos hfc₁ hfa, N, hN, hpN,
            fun q hq => Or.inl (Or.inr (hNU hq).1), he⟩)
  refine ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero, ?_⟩
  let Φ : ℝ → (Plane ≃ₘ[ℝ] Plane) := fun t => Diffeomorph.timeDependentFlow X hX hsX 0 t
  have hzero (t : ℝ) (p : Plane) (hp : p ∉ U₀ ∪ U₁ ∪ V) : X (t, p) = 0 :=
    hXzero t p (fun h => hp (hKW h))
  have ht (z : ℝ × Plane) (hz : z ∈ Ω) :
      deriv (fun t => (1 - t) * (F z.2).1 + t * (F z.2).2) z.1 +
        fderiv ℝ (fun y => (1 - z.1) * (F y).1 + z.1 * (F y).2) z.2 (X z) =
          κ z * (((1 - z.1) * (F z.2).1 + z.1 * (F z.2).2) - 0) := by
    simpa only [sub_zero] using htransport z hz
  refine ⟨Φ, fun _ _ _ => rfl,
    (Diffeomorph.contDiff_timeDependentFlow X hX hsX).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    (Diffeomorph.contDiff_timeDependentFlow_symm X hX hsX).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    Diffeomorph.timeDependentFlow_refl X hX hsX 0, ?_, ?_, ?_, ?_⟩
  · intro t
    constructor
    · exact fun p hp => Diffeomorph.timeDependentFlow_apply_eq_self_of_forall_eq_zero X hX hsX
        (fun u => hXzero u p hp) 0 t
    · intro p hp
      change (Diffeomorph.timeDependentFlow X hX hsX 0 t).symm p = p
      rw [Diffeomorph.timeDependentFlow_symm]
      exact Diffeomorph.timeDependentFlow_apply_eq_self_of_forall_eq_zero X hX hsX
        (fun u => hXzero u p hp) t 0
  · intro t
    exact ⟨Diffeomorph.timeDependentFlow_mem_iff_of_eq_zero X hX hsX hzero 0 t,
      Diffeomorph.timeDependentFlow_symm_mem_iff_of_eq_zero X hX hsX hzero 0 t⟩
  · intro t htI p hp
    have h := Diffeomorph.timeDependentFlow_level_and_sublevels_iff_of_proportional_transport
      X hX hsX hzero (a := 0) (b := t) (r := 0) htI.1 hΩ
      (fun z hz => hΩcover ⟨⟨hz.1.1, hz.1.2.trans htI.2⟩, hz.2⟩)
      (hH.differentiable (by simp)).differentiableOn hκ.continuousOn ht hp
    simpa only [Φ, sub_zero, one_mul, zero_mul, add_zero] using h
  · intro t htI p hp
    have h := Diffeomorph.timeDependentFlow_symm_level_and_sublevels_iff_of_proportional_transport
      X hX hsX hzero (a := 0) (b := t) (r := 0) htI.1 hΩ
      (fun z hz => hΩcover ⟨⟨hz.1.1, hz.1.2.trans htI.2⟩, hz.2⟩)
      (hH.differentiable (by simp)).differentiableOn hκ.continuousOn ht hp
    simpa only [Φ, sub_zero, one_mul, zero_mul, add_zero] using h

end Schoenflies
