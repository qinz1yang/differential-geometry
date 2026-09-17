import DifferentialGeometry.Topology.SphereSeparation.OneSaddleIncidence
import DifferentialGeometry.Topology.SphereSeparation.HeightCapChart
import DifferentialGeometry.Topology.Embedding.GraphChartNeighborhood
import DifferentialGeometry.Topology.Embedding.LinearEquiv
import DifferentialGeometry.Topology.PlanarJordan.SaddleCapSides
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk

open Set Metric Manifold
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.PlanarJordan
open Schoenflies

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_open_saddle_side_of_transport_and_graph_box
    {M : Type*} (e : M → Schoenflies.Plane × ℝ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (A : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ)) (hA : ∀ z, (A z).2 = z.2)
    (Φ : ℝ → Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    {s τ σ c k R b r : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1)
    (hk : 0 ≤ k) (hkone : k < 1) (hr : 0 < r)
    (hbound : saddleBandLevelCurve s τ σ '' Icc (-k) k ⊆ ball (0 : ℝ × ℝ) R)
    (hbox : ∀ z ∈ closedBall (0 : ℝ × ℝ) R,
      (B z, c + s + τ) ∈ range e ↔
        c + s + τ = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    (hselected : B '' (saddleBandLevelCurve s τ σ '' Icc (-k) k) ⊆
      (fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' sphere 0 r)
    (hopp : Disjoint (B '' (saddleBandLevelCurve s τ (-σ) '' Icc (-k) k))
      ((fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' closedBall 0 r))
    (hcontact : ((fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' closedBall 0 r) ∩
        ((fun x => (e x).1) '' {x | (e x).2 = c + s + τ}) =
      (fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' sphere 0 r) :
    (∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
      (B z ∈ interior
          ((fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' closedBall 0 r) ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
      (B z ∈ ((fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' closedBall 0 r) ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2)) ∧
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧
      saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V ∧
      V ⊆ Ioo (-k) k ×ˢ Ioo (-R) R ∧
      (∀ z ∈ V, B z ∈ interior
          ((fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' closedBall 0 r) ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
      (∀ z ∈ V, B z ∈
          ((fun y => Φ (c + s + τ) ((Φ b).symm (A (y, b)).1)) '' closedBall 0 r) ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) := by
  let G := (A.toHomeomorph.restrictFiber hA b).trans
    ((Φ b).symm.toHomeomorph.trans (Φ (c + s + τ)).toHomeomorph)
  let C := G '' sphere 0 r
  have hC : IsSeparating C := jordan_curve_theorem (isJordanCurve_image_sphere G 0 hr)
  have hdisk : G '' closedBall 0 r = closure (inside C) :=
    image_closedBall_eq_closure_inside_image_sphere G 0 hr
  have hinterior : interior (G '' closedBall 0 r) = inside C := by
    rw [← G.image_interior, interior_closedBall _ hr.ne']
    exact image_ball_eq_inside_image_sphere G 0 hr
  have hknorm : ‖saddleBandLevelCurve s τ σ k‖ < R := by
    exact mem_ball_zero_iff.mp (hbound ⟨k, ⟨by linarith, le_rfl⟩, rfl⟩)
  have hkR : k < R := by
    have h := (norm_fst_le (saddleBandLevelCurve s τ σ k)).trans_lt hknorm
    simpa only [saddleBandLevelCurve, Real.norm_eq_abs, abs_of_nonneg hk] using h
  have hrectangle : Icc (-k) k ×ˢ Icc (-R) R ⊆ closedBall (0 : ℝ × ℝ) R := by
    intro z hz
    rw [mem_closedBall_zero_iff, norm_prod_le_iff]
    exact ⟨(show ‖z.1‖ ≤ k by simpa only [Real.norm_eq_abs] using abs_le.mpr hz.1).trans hkR.le,
      by simpa only [Real.norm_eq_abs] using abs_le.mpr hz.2⟩
  have hR (u : ℝ) (hu : u ∈ Ioo (-k) k) : |(saddleBandLevelCurve s τ σ u).2| < R := by
    exact (norm_snd_le _).trans_lt
      (mem_ball_zero_iff.mp (hbound ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩))
  have hcurve (u : ℝ) (hu : u ∈ Ioo (-k) k) : B (saddleBandLevelCurve s τ σ u) ∈ C :=
    hselected ⟨_, ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩, rfl⟩
  have hout (u : ℝ) (hu : u ∈ Ioo (-k) k) :
      B (saddleBandLevelCurve s τ (-σ) u) ∉ closure (inside C) := by
    rw [← hdisk]
    exact disjoint_left.mp hopp ⟨_, ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩, rfl⟩
  have hlevel (z : ℝ × ℝ) (hz : z ∈ Icc (-k) k ×ˢ Icc (-R) R) (hzC : B z ∈ C) :
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = c + s + τ := by
    have hzlevel := (hcontact.symm.subset hzC).2
    obtain ⟨x, hx, hBx⟩ := hzlevel
    have he : (B z, c + s + τ) ∈ range e := ⟨x, Prod.ext hBx hx⟩
    exact ((hbox z (hrectangle hz)).mp he).symm
  refine ⟨?_, ?_⟩
  · intro z hz
    change (B z ∈ interior (G '' closedBall 0 r) ↔ _) ∧
      (B z ∈ G '' closedBall 0 r ↔ _)
    rw [hinterior, hdisk]
    exact mem_inside_and_closure_inside_iff_of_saddleBandLevelCurve
      hC B hs hτ hσ hkone hR hcurve hout hlevel hz
  obtain ⟨V, hV, hKV, hVU, hVin, hVcl⟩ :=
    exists_open_side_neighborhood_of_saddleBandLevelCurve hC B hs hτ hσ hkone
      hR hcurve hout hlevel
  refine ⟨V, hV, hKV, hVU, ?_, ?_⟩
  · intro z hz
    change B z ∈ interior (G '' closedBall 0 r) ↔ _
    rw [hinterior]
    exact hVin z hz
  · intro z hz
    change B z ∈ G '' closedBall 0 r ↔ _
    rw [hdisk]
    exact hVcl z hz


theorem exists_height_level_isotopy_saddle_cap_normal_form_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ p : SphereTwo, IsLocalMax (fun x => e x 2) p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      ¬ IsMaxOn (fun x => e x 2) univ p ∧
      ∃ δ k R : ℝ, 0 < δ ∧ c + s + δ ≤ e p 2 ∧ 0 < k ∧ k < 1 ∧
        0 < R ∧ k < R ∧ closedBall (0 : ℝ × ℝ) R ⊆ U ∧
        (∀ z ∈ closedBall (0 : ℝ × ℝ) R, ∀ t ∈ closedBall (c + s) δ,
          (B z, t) ∈ range (EuclideanSpace.equivProdLast 2 ∘ e) ↔
            t = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
        ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ τ ∈ Ioo (0 : ℝ) δ,
          let a := c + s + τ
          let Kp := saddleBandLevelCurve s τ σ '' Icc (-k) k
          let Kq := saddleBandLevelCurve s τ (-σ) '' Icc (-k) k
          let K := Kp ∪ Kq
          IsCompact Kp ∧ IsCompact Kq ∧ IsCompact K ∧ K ⊆ U ∧
          (∀ z ∈ K, (1 - z.1 ^ 2) * z.2 ≠ 0) ∧
          (∀ z ∈ K, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = a) ∧
          a < e p 2 ∧
          (∀ x, e x 2 ∈ Ico a (e p 2) → ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
          ∃ r : ℝ, 0 < r ∧ a < e p 2 - r ^ 2 / 2 ∧
            ∃ A : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
              (∀ z, (A z).2 = z.2) ∧
              (∃ R τ : ℝ, r < R ∧ 0 < τ ∧ r ^ 2 / 2 < τ ∧
                ((closedBall 0 R ×ˢ closedBall (e p 2) τ) ∩
                    range (fun x => A.symm (EuclideanSpace.equivProdLast 2 (e x)))) =
                  (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 R) ∧
              (EuclideanSpace.equivProdLast 2 ∘ e) ''
                  connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
                (fun y => A (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
              ∃ Φ : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
                ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => Φ z.1 z.2) ∧
                ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (Φ z.1).symm z.2) ∧
                Φ a = Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞ ∧
                (∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
                  Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) ''
                    {x | e x 2 = a}) =
                    (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) ∧
                (∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
                  ((fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
                      (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ∩
                      ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) =
                    (fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
                      (A (y, e p 2 - r ^ 2 / 2)).1)) '' sphere 0 r) ∧
                (∃ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S ∧ ∀ t : ℝ,
                  EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ) ∧
                (∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧
                  ∀ t ∈ Icc (a - δ₀) (a + δ₀), ∀ z ∈ cthickening ε K,
                    Φ t (B z) = B (saddleBandCurve z (t - a))) ∧
                (∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, r < R ∧
                  ∀ t ∈ Icc (e p 2 - r ^ 2 / 2 - δ) (e p 2 - r ^ 2 / 2 + δ),
                    ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
                      Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm (A (x, e p 2 - r ^ 2 / 2)).1) =
                        (A (quadraticLevelScaling (e p 2 - r ^ 2 / 2) (e p 2) x t, t)).1) ∧
                B '' Kp ⊆ (fun y => Φ a ((Φ (e p 2 - r ^ 2 / 2)).symm
                  (A (y, e p 2 - r ^ 2 / 2)).1)) '' sphere 0 r ∧
                Disjoint (B '' Kq) ((fun y => Φ a ((Φ (e p 2 - r ^ 2 / 2)).symm
                  (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ∧
                ∃ V : Set (ℝ × ℝ), IsOpen V ∧
                  saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V ∧ V ⊆ U ∧
                  (∀ z ∈ V, B z ∈ interior ((fun y => Φ a ((Φ (e p 2 - r ^ 2 / 2)).symm
                      (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ↔
                    a < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
                  (∀ z ∈ V, B z ∈ ((fun y => Φ a ((Φ (e p 2 - r ^ 2 / 2)).symm
                      (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ↔
                    a ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
                  Icc (-k) k ×ˢ Icc (-R) R ⊆ U ∧
                    (∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
                      (B z ∈ interior ((fun y => Φ a ((Φ (e p 2 - r ^ 2 / 2)).symm
                          (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ↔
                        a < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
                      (B z ∈ ((fun y => Φ a ((Φ (e p 2 - r ^ 2 / 2)).symm
                          (A (y, e p 2 - r ^ 2 / 2)).1)) '' closedBall 0 r) ↔
                        a ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2)) ∧
                  ∃ D : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ]
                      (EuclideanSpace ℝ (Fin 2) × ℝ),
                    (∀ z, (D z).2 = z.2) ∧
                    (∀ t ≤ e p 2 - r ^ 2 / 2, ∀ x,
                      D (quadraticLevelScaling (e p 2 - r ^ 2 / 2) (e p 2) x t, t) =
                        (Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
                          (A (x, e p 2 - r ^ 2 / 2)).1), t)) ∧
                    (∃ ρ > r, ∀ t, e p 2 - r ^ 2 / 2 ≤ t →
                      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, D (x, t) = A (x, t)) ∧
                    (D '' {z | a ≤ z.2 ∧ z.2 ≤ e p 2 - ‖z.1‖ ^ 2 / 2}) ∩
                        range (EuclideanSpace.equivProdLast 2 ∘ e) =
                      D '' {z | a ≤ z.2 ∧ z.2 = e p 2 - ‖z.1‖ ^ 2 / 2} := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  have heL := he.continuousLinearEquiv_comp L
  obtain ⟨Rbox, hRbox, tbox, htbox, hRboxU, hqbox, hbox⟩ :=
    heL.isEmbedding.isInducing.exists_prod_closedBall_mem_range_iff_of_smooth_parametrization
      B hU hβ
      (fun z _ => ((ContinuousLinearMap.fst ℝ Schoenflies.Plane ℝ).contDiff.contMDiff.comp
        heL.contMDiff).contMDiffAt)
      (by simp [Module.finrank_prod]) hgraph hzero
  obtain ⟨p, hpmax, hpnd, hpnglob, δ₀, k, hδ₀, hδ₀bound, hk, hkone, σ, hσ, hdata⟩ :=
    exists_saddleBandLevelCurve_incidence_of_one_saddle he hnd hinj hone hconn
      B (hU.inter isOpen_ball) ⟨hzero, mem_ball_self hRbox⟩
      (hβ.mono inter_subset_left) hs (fun z hz => hgraph z hz.1) hβcrit hβindex
  let δ := min δ₀ tbox
  have hδ : 0 < δ := lt_min hδ₀ htbox
  have hδbound : c + s + δ ≤ e p 2 := by
    have hd := min_le_left δ₀ tbox
    dsimp [δ]
    linarith
  have hkR : k < Rbox := by
    have hhδ : δ / 2 ∈ Ioo (0 : ℝ) δ₀ :=
      ⟨half_pos hδ, (half_lt_self hδ).trans_le (min_le_left δ₀ tbox)⟩
    obtain ⟨_, _, _, hKhalf, _⟩ := hdata (δ / 2) hhδ
    have hb := mem_ball_zero_iff.mp
      (hKhalf (Or.inl ⟨k, ⟨by linarith, le_rfl⟩, rfl⟩)).2
    have hh := (norm_fst_le (saddleBandLevelCurve s (δ / 2) σ k)).trans_lt hb
    simpa only [saddleBandLevelCurve, Real.norm_eq_abs, abs_of_pos hk] using hh
  refine ⟨p, hpmax, hpnd, hpnglob, δ, k, Rbox, hδ, hδbound, hk, hkone,
    hRbox, hkR, hRboxU, ?_, σ, hσ, ?_⟩
  · intro z hz t ht
    exact hbox z hz t (by
      simpa using (closedBall_subset_closedBall (min_le_right δ₀ tbox)) ht)
  intro τ hτ
  dsimp only
  let a := c + s + τ
  have hτ₀ : τ ∈ Ioo (0 : ℝ) δ₀ := ⟨hτ.1, hτ.2.trans_le (min_le_left δ₀ tbox)⟩
  obtain ⟨hKp, hKq, hK, hKU, hKreg, hKlevel, hap, hreg, hinc⟩ := hdata τ hτ₀
  have hKU₀ := hKU.trans inter_subset_left
  have hKbox := hKU.trans inter_subset_right
  obtain ⟨r, hr, hab, A, hA, hnormalbox, hcap, Φ, hΦ, hΦinv, hΦa, hlevels,
    hcontact, hsupport, hsaddlegerm, hmaxgerm, hchart⟩ :=
    exists_height_cap_diffeomorph_and_level_isotopy he hpnd hpmax B hU hβ hgraph
      hK hKU₀ hKreg hKlevel hap hreg
  have hboth := hinc r hr hab A hA hcap Φ hΦ hΦa hlevels (hcontact a ⟨le_rfl, hab.le⟩)
  have haBox : a ∈ closedBall (c + s) tbox := by
    rw [mem_closedBall, Real.dist_eq]
    have heq : a - (c + s) = τ := by dsimp [a]; ring
    rw [heq, abs_of_pos hτ.1]
    exact hτ.2.le.trans (min_le_right δ₀ tbox)
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨hfull, V, hV, hcurveV, hVrect, hVint, hVdisk⟩ :=
    exists_open_saddle_side_of_transport_and_graph_box (L ∘ e) B A hA Φ
      hs.le hτ.1 hσsq hk.le hkone hr
      (fun z hz => hKbox (Or.inl hz))
      (fun z hz => hbox z hz a (by simpa using haBox))
      hboth.1 hboth.2 (hcontact a ⟨le_rfl, hab.le⟩)
  have hrectangleU : Icc (-k) k ×ˢ Icc (-Rbox) Rbox ⊆ U := by
    intro z hz
    apply hRboxU
    change z ∈ closedBall (0 : ℝ × ℝ) Rbox
    rw [mem_closedBall_zero_iff, norm_prod_le_iff]
    exact ⟨(show ‖z.1‖ ≤ k by simpa only [Real.norm_eq_abs] using
      (abs_le.mpr hz.1)).trans hkR.le,
      by simpa only [Real.norm_eq_abs] using (abs_le.mpr hz.2)⟩
  have hVU : V ⊆ U := by
    intro z hz
    have hzrect := hVrect hz
    apply hRboxU
    change z ∈ closedBall (0 : ℝ × ℝ) Rbox
    rw [mem_closedBall_zero_iff, norm_prod_le_iff]
    exact ⟨(show ‖z.1‖ ≤ k by simpa only [Real.norm_eq_abs] using
      (abs_lt.mpr hzrect.1).le).trans hkR.le,
      by simpa only [Real.norm_eq_abs] using (abs_lt.mpr hzrect.2).le⟩
  obtain ⟨D, hD, hDmodel, hDupper, hDregion, hDgraph⟩ := hchart
  refine ⟨hKp, hKq, hK, hKU₀, hKreg, hKlevel, hap, hreg,
    r, hr, hab, A, hA, hnormalbox, hcap, Φ, hΦ, hΦinv, hΦa, hlevels,
    hcontact, hsupport, hsaddlegerm, hmaxgerm, hboth.1, hboth.2,
    V, hV, hcurveV, hVU, hVint, hVdisk, hrectangleU, hfull, D, hD, hDmodel, hDupper, ?_⟩
  rw [hDregion]
  exact hDgraph

end DifferentialGeometry.Topology.SphereSeparation
