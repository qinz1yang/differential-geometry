import DifferentialGeometry.Topology.Morse.GraphReplacement
import DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph
import DifferentialGeometry.Analysis.Calculus.Interpolation.ParabolicCompression
import DifferentialGeometry.Topology.PlanarJordan.ParabolicLens
import DifferentialGeometry.Topology.SphereSeparation.SaddleCutoffCollar
import DifferentialGeometry.Topology.SphereSeparation.SaddleCutoffRegion
import DifferentialGeometry.Topology.SphereSeparation.HeightCapGraphNeighborhood
import DifferentialGeometry.Topology.Diffeomorph.QuadraticCapProjection
import DifferentialGeometry.Topology.SphereSeparation.OneSaddleClosingArcFamily
import DifferentialGeometry.Topology.SphereSeparation.HeightCapChart
import DifferentialGeometry.Topology.Diffeomorph.FiberwiseReparametrization
import DifferentialGeometry.Topology.PlanarJordan.SaddleCutoffIsotopy
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleGraphNeighborhood
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleCutoffGraph
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleCutoffProjection
import DifferentialGeometry.Topology.Embedding.Cylinder
import DifferentialGeometry.Topology.Embedding.GraphChartNeighborhood
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Compactness.BoundaryCollar

open Set Metric Manifold
open Schoenflies (Plane IsCutPair)
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE (saddleBandCurve saddleBandCurve_zero quadraticLevelScaling)

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_regular_lower_graph_of_parabolic_lens
    (F : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    (hψ : StrictMono ψ) {a A B ℓ : ℝ} (ha : a < A) (hB : 0 < B)
    {g : Schoenflies.Plane → ℝ} {O : Set Schoenflies.Plane} (hg : ContDiffOn ℝ ∞ g O)
    (hFO : F '' {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2} ⊆ O)
    (hcompact : IsCompact (F '' {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2}))
    (hpos : ∀ p ∈ interior {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2},
      ψ (ℓ + a) < g (F p))
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hFV : frontier {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2} ⊆ V)
    (hboundary : ∀ p ∈ V, g (F p) = ψ (ℓ + p.1)) :
    ∃ k : Schoenflies.Plane → ℝ, ContDiff ℝ ∞ k ∧ (∀ y, fderiv ℝ k y ≠ 0) ∧
      (∀ y ∈ F '' {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2},
        ψ (ℓ + a) ≤ k y ∧ k y ≤ g y) ∧
      ∃ C : Set Schoenflies.Plane, IsCompact C ∧
        C ⊆ interior (F '' {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2}) ∧
        EqOn k g ((F '' {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2}) \ C) ∧
        ∃ U : Set Schoenflies.Plane, IsOpen U ∧
          frontier (F '' {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2}) ⊆ U ∧ EqOn k g U := by
  let X : Set (ℝ × ℝ) := {p | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2}
  have hX : IsCompact X := by
    have hh := hcompact.image F.symm.continuous
    have he : F.symm '' (F '' X) = X := by
      ext p
      constructor
      · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩; simpa only [F.symm_apply_apply] using hq
      · intro hp; exact ⟨F p, mem_image_of_mem F hp, F.symm_apply_apply p⟩
    exact he ▸ hh
  have hK : IsCompact (X \ V) := hX.diff hV
  have hKin : X \ V ⊆ interior X := by
    intro p hp
    by_contra hn
    exact hp.2 (hFV ⟨subset_closure hp.1, hn⟩)
  let f : (ℝ × ℝ) → ℝ := fun p => ψ.symm (g (F p)) - ℓ
  have hf : ContinuousOn f (X \ V) :=
    (ψ.symm.continuous.comp_continuousOn (hg.continuousOn.comp F.continuous.continuousOn
      (fun p hp => hFO (mem_image_of_mem F hp.1)))).sub continuousOn_const
  have hfp : ∀ p ∈ X \ V, a < f p := by
    intro p hp
    have hh : ℓ + a < ψ.symm (g (F p)) := hψ.lt_iff_lt.mp (by
      rw [ψ.apply_symm_apply]
      exact hpos p (hKin hp))
    dsimp [f]
    linarith
  have hfeq {p : ℝ × ℝ} (hp : p ∈ V) : f p = p.1 := by
    dsimp [f]
    rw [hboundary p hp, ψ.symm_apply_apply, add_sub_cancel_left]
  obtain ⟨H, hH, hHd, hHle, hHa, hHf, L, hL, hLin, hHfix⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_parabolic_compression_below_on_isCompact ha hB hK
      (by intro p hp; exact (PlanarJordan.interior_parabolic_lens ha hB).subset (hKin hp)) hf hfp
  have hLinterior : L ⊆ interior X := by
    simpa only [X, PlanarJordan.interior_parabolic_lens ha hB] using hLin
  have hHfX {p : ℝ × ℝ} (hp : p ∈ X) : H p ≤ f p := by
    by_cases hpV : p ∈ V
    · rw [hfeq hpV]; exact hHle p
    · exact (hHf p ⟨hp, hpV⟩).le
  let k : Schoenflies.Plane → ℝ := fun y => ψ (ℓ + H (F.symm y))
  have hk : ContDiff ℝ ∞ k := ψ.contDiff.comp (contDiff_const.add (hH.comp F.symm.contDiff))
  have hkeq {p : ℝ × ℝ} (hp : p ∈ V \ L) : k (F p) = g (F p) := by
    dsimp [k]
    rw [F.symm_apply_apply, hHfix hp.2, hboundary p hp.1]
  have hC : IsCompact (F '' ((X \ V) ∪ L)) := (hK.union hL).image F.continuous
  have hCin : F '' ((X \ V) ∪ L) ⊆ interior (F '' X) := by
    have he : F '' interior X = interior (F '' X) := F.toHomeomorph.image_interior X
    rw [← he]
    exact image_mono (union_subset hKin hLinterior)
  refine ⟨k, hk, ?_, ?_, F '' ((X \ V) ∪ L), hC, hCin, ?_,
    F '' (V \ L), F.toHomeomorph.isOpenMap _ (hV.sdiff hL.isClosed), ?_, ?_⟩
  · intro y hy
    let p := F.symm y
    have hidentity : (fun q => ψ.symm (k (F q)) - ℓ) = H := by
      funext q
      simp only [k, F.symm_apply_apply, ψ.symm_apply_apply, add_sub_cancel_left]
    have hzero : HasFDerivAt k (0 : Schoenflies.Plane →L[ℝ] ℝ) (F p) := by
      simpa only [p, F.apply_symm_apply, hy] using (hk.differentiable (by simp) y).hasFDerivAt
    have hc := ((ψ.symm.contDiff.differentiable (by simp) (k (F p))).hasFDerivAt.comp p
      (hzero.comp p (F.contDiff.differentiable (by simp) p).hasFDerivAt)).sub_const ℓ
    have hz : fderiv ℝ H p = 0 := by
      simpa only [Function.comp_def, hidentity, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] using hc.fderiv
    have hh := hHd p
    rw [hz, zero_apply] at hh
    exact (lt_irrefl 0) hh
  · rintro y ⟨p, hp, rfl⟩
    change ψ (ℓ + a) ≤ ψ (ℓ + H (F.symm (F p))) ∧ _
    rw [F.symm_apply_apply]
    refine ⟨hψ.monotone (add_le_add le_rfl (hHa p hp.1)), ?_⟩
    have hh := hψ.monotone (add_le_add (le_refl ℓ) (hHfX hp))
    simpa only [k, F.symm_apply_apply, f, add_sub_cancel, ψ.apply_symm_apply] using hh
  · rintro y ⟨⟨p, hp, rfl⟩, hn⟩
    apply hkeq
    exact ⟨by by_contra hpV; exact hn (mem_image_of_mem F (Or.inl ⟨hp, hpV⟩)),
      fun hpL => hn (mem_image_of_mem F (Or.inr hpL))⟩
  · have he : F '' frontier X = frontier (F '' X) := F.toHomeomorph.image_frontier X
    change frontier (F '' X) ⊆ _
    rw [← he]
    apply image_mono
    intro p hp
    exact ⟨hFV hp, fun hpL => disjoint_left.mp disjoint_interior_frontier (hLinterior hpL) hp⟩
  · rintro y ⟨p, hp, rfl⟩
    exact hkeq hp

private theorem exists_isOpen_graph_upper_saddle_cap {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (D T A Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ))
    (ψ : ℝ ≃ₘ[ℝ] ℝ)
    (G : ℝ → Plane ≃ₘ[ℝ] Plane)
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)}
    {c s h t₀ δ d ε σ r b m : ℝ}
    (hs : 0 < s) (hh1 : h < 1) (ht₀ : 0 < t₀)
    (ht₀d : t₀ < d) (hdδ : d < δ) (hε : 0 < ε)
    (hσ : σ ^ 2 = 1) (ht₀b : c + s + t₀ ≤ b)
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m ((G (c + s + t₀)).symm y) (ψ t), ψ t))
    (hQcap : Q '' ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}) =
      {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})
    (Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (η : unitInterval → SphereTwo)
    (hslices : ∀ t ∈ Icc (-δ) δ, ∀ u, e (Φ (t - δ / 2) (η u)) 2 = c + s + t)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    {θ : ℝ × ℝ → ℝ}
    (hθ1 : ∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1)
    {V : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1))
    (hrawU : ∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U) :
    let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
    let γ := fun q : ℝ × unitInterval => (L (e (Φ (q.1 - δ / 2) (η q.2)))).1
    (∀ t ∈ Icc (-d) d, ∀ u, T (γ (t, u), c + s + t) = (γ (t₀, u), c + s + t)) →
    G (c + s + t₀) '' Metric.sphere 0 r =
      B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ∪ range (fun u => γ (t₀, u)) →
    ((G (c + s + t₀) '' Metric.closedBall 0 r) ×ˢ Icc (c + s + t₀) b) ∩
      range (T ∘ L ∘ e) =
        (G (c + s + t₀) '' Metric.sphere 0 r) ×ˢ Icc (c + s + t₀) b →
    heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∩ range (L ∘ e) =
      D '' {q | c + s + t₀ ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} →
    ∀ j ∈ Ioo (t₀ / 2) t₀, ∃ W : Set (Plane × ℝ), IsOpen W ∧
      Q '' (((G (c + s + t₀) '' Metric.sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
        ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})) ⊆ W ∧
      W ∩ range (Q ∘ T ∘ L ∘ e) = W ∩ {q : Plane × ℝ | q.2 = m - ‖q.1‖ ^ 2 / 2} := by
  intro L γ hTarc hcircleRef hwhole hinter
  let Ucap : ℝ → Set (Plane × ℝ) := fun j =>
    ((G (c + s + t₀) '' Metric.sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
      ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})
  have hupperRange (j : ℝ) (hj : j ∈ Ioo (t₀ / 2) t₀) : Ucap j ⊆ range (T ∘ L ∘ e) := by
    have hsubraw : Icc j t₀ ⊆ Icc (-ε) d := by
      intro t ht
      exact ⟨by linarith [hj.1, ht.1], ht.2.trans ht₀d.le⟩
    have hsubδ : Icc j t₀ ⊆ Icc (-δ) δ := by
      intro t ht
      exact ⟨by linarith [hj.1, ht.1], ht.2.trans (ht₀d.trans hdδ).le⟩
    have hsubd : Icc j t₀ ⊆ Icc (-d) d := by
      intro t ht
      exact ⟨by linarith [hj.1, ht.1], ht.2.trans ht₀d.le⟩
    have hfullWall :
        (G (c + s + t₀) '' Metric.sphere 0 r) ×ˢ
          Icc (c + s + j) (c + s + t₀) ⊆ range (T ∘ L ∘ e) := by
      rw [range_comp]
      apply reference_cylinder_subset_image_of_saddle_band B T hs.le hh1
        (by linarith [hj.1] : 0 < j) hσ _ _ _ _ hcircleRef
      · intro t ht z hzwidth hzlevel
        refine ⟨β z, ?_⟩
        change L (e (β z)) = _
        rw [hgraph z (hrawU t (hsubraw ht) z hzwidth hzlevel), hzlevel]
        congr 1
        ring
      · intro t ht z hzwidth hzlevel
        have h := hTmodel (t, z) (hKV ⟨hsubraw ht, hzwidth, hzlevel⟩)
        change T (B z, c + s + t) =
          (B (saddleBandCurve z (θ (t, z.1) * (t₀ - t))), c + s + t) at h
        rw [hθ1 t z.1 (Or.inl (hj.1.le.trans ht.1)), one_mul] at h
        exact h
      · intro t ht u
        exact ⟨Φ (t - δ / 2) (η u), Prod.ext rfl (hslices t (hsubδ ht) u)⟩
      · intro t ht u
        exact hTarc t (hsubd ht) u
    intro q hq
    rcases hq with ⟨hqC, hqt⟩ | ⟨z, hz, rfl⟩
    · by_cases ht : q.2 ≤ c + s + t₀
      · exact hfullWall ⟨hqC, hqt.1, ht⟩
      · exact (hwhole.symm.subset ⟨hqC, (not_le.mp ht).le, hqt.2⟩).2
    · have hDz : D z ∈ range (L ∘ e) :=
        (hinter.symm.subset ⟨z, ⟨ht₀b.trans hz.1, hz.2⟩, rfl⟩).2
      obtain ⟨x, hx⟩ := hDz
      exact ⟨x, congrArg T hx⟩
  have himage (j : ℝ) (hj : c + s + j ≤ b) :
      Q '' Ucap j = {q : Plane × ℝ | ψ (c + s + j) ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} :=
    Diffeomorph.image_reference_cylinder_union_cap Q (G (c + s + t₀)).toEquiv ψ.toEquiv
      hbm hr hrsq hj hψ hψb hQfull hQcap
  have heQT : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, Plane × ℝ) ∞ (Q ∘ T ∘ L ∘ e) :=
    ((he.continuousLinearEquiv_comp L).diffeomorph_comp T).diffeomorph_comp Q
  intro j hj
  let j' := (t₀ / 2 + j) / 2
  have hj' : j' ∈ Ioo (t₀ / 2) t₀ := by
    dsimp only [j']
    constructor <;> linarith [hj.1, hj.2]
  have hj'j : j' < j := by dsimp only [j']; linarith [hj.1]
  let q : Plane → ℝ := fun y => m - ‖y‖ ^ 2 / 2
  let O : Set Plane := {y | ψ (c + s + j') < q y}
  have hq : ContDiff ℝ ∞ q := contDiff_const.sub ((contDiff_norm_sq ℝ).div_const 2)
  have hO : IsOpen O := isOpen_lt continuous_const hq.continuous
  have hgraphO : (fun y => (y, q y)) '' O ⊆ range (Q ∘ T ∘ L ∘ e) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyimage := (himage j' (by linarith [hj'.2])).symm.subset
      (show (y, q y) ∈ {p : Plane × ℝ | ψ (c + s + j') ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2}
        from ⟨hy.le, rfl⟩)
    obtain ⟨z, hz, hQz⟩ := hyimage
    obtain ⟨x, hx⟩ := hupperRange j' hj' hz
    exact ⟨x, (congrArg Q hx).trans hQz⟩
  obtain ⟨W, hW, hgraphW, _, hWeq⟩ := heQT.exists_isOpen_inter_range_eq_graph
    hO hq.contDiffOn (by simp) hgraphO
  refine ⟨W, hW, ?_, hWeq⟩
  intro z hz
  have hzcap := (himage j (by linarith [hj.2])).subset hz
  apply hgraphW
  refine ⟨z.1, ?_, Prod.ext rfl hzcap.2.symm⟩
  change ψ (c + s + j') < m - ‖z.1‖ ^ 2 / 2
  rw [← hzcap.2]
  exact (hψ (by linarith)).trans_le hzcap.1


private theorem isCompact_reference_circle_compl_selected_arc
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    {s τ σ h k r : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1)
    (hh1 : h < 1) (hk : k ≤ h) (hr : 0 < r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcurveV : saddleBandLevelCurve s τ σ '' Ioo (-h) h ⊆ V)
    (hcurve : ∀ u ∈ Ioo (-h) h, B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    (hside : ∀ z ∈ V, B z ∈ G '' closedBall 0 r ↔
      s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) :
    IsCompact (G '' sphere 0 r \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-k) k)) := by
  let O : Set (ℝ × ℝ) := V ∩ {z | z.1 ∈ Ioo (-k) k ∧ 0 < σ * z.2}
  have hO : IsOpen O := hV.inter ((isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_snd)))
  have hEq : (G '' sphere 0 r) ∩ (B '' O) = B '' (saddleBandLevelCurve s τ σ '' Ioo (-k) k) := by
    apply Subset.antisymm
    · rintro _ ⟨hzC, z, hzO, rfl⟩
      have heq := PlanarJordan.cap_circle_height_eq_on_side_neighborhood B.toHomeomorph G.toHomeomorph hr hV hside hzO.1 hzC
      have hu : z.1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith only [hzO.2.1.1, hk, hh1],
        hzO.2.1.2.trans_le hk |>.trans hh1⟩
      have hden : 1 - z.1 ^ 2 ≠ 0 := by nlinarith only [hu.1, hu.2]
      have hzcurve := saddleBandCurve_eq_saddleBandLevelCurve (s := s) (t := 0)
        hσ hden hzO.2.2 (by simp)
      rw [saddleBandCurve_zero, heq, show s + τ - s + 0 = τ by ring] at hzcurve
      exact ⟨z, ⟨z.1, hzO.2.1, hzcurve.symm⟩, rfl⟩
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have huh : u ∈ Ioo (-h) h := ⟨by linarith only [hu.1, hk], hu.2.trans_le hk⟩
      have hu1 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith only [huh.1, hh1], huh.2.trans hh1⟩
      refine ⟨hcurve u huh, saddleBandLevelCurve s τ σ u, ⟨hcurveV ⟨u, huh, rfl⟩, hu, ?_⟩, rfl⟩
      change 0 < σ * (σ * Real.sqrt _)
      rw [← mul_assoc, ← pow_two, hσ, one_mul]
      exact Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num)
        (add_pos_of_pos_of_nonneg hτ (mul_nonneg hs (sq_nonneg u))))
        (by nlinarith only [hu1.1, hu1.2]))
  rw [← hEq, sdiff_self_inter]
  exact ((isCompact_sphere 0 r).image G.continuous).diff (B.toHomeomorph.isOpenMap _ hO)


private theorem exists_exp_projection_eq_imp_mem_reference_wall
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    {s t₀ δ σ h R r v₀ a b : ℝ} (hs : 0 ≤ s) (ht₀ : 0 < t₀)
    (ht₀δ : t₀ < δ) (hσ : σ ^ 2 = 1) (hh : 0 < h) (hh1 : h < 1)
    (hr : 0 < r) (hv₀ : 0 ≤ v₀) (hv₀t : v₀ ^ 2 < 2 * t₀)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-R) R)
    (hclear : ∀ a < t₀, ∃ ρ > 0, cthickening ρ
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-R) R ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
          (G '' closedBall 0 r)ᶜ)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, |p.1.1| ≤ 5 * h / 8)
    (hbottom : ∀ p ∈ K, -v₀ ≤ σ * p.1.2)
    (henergy : ∀ p ∈ K, (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 ≤ s + t₀)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcurveV : saddleBandLevelCurve s t₀ σ '' Ioo (-h) h ⊆ V)
    (hside : ∀ z ∈ V, B z ∈ G '' closedBall 0 r ↔
      s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) :
    ∃ ρ > 0, ∀ μ ∈ Ioo (0 : ℝ) ρ, ∀ p ∈ K,
      ∀ q ∈ (G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc a b,
        Real.exp (-μ * p.2) • G.symm (B p.1) = Real.exp (-μ * q.2) • G.symm q.1 →
        (B.symm q.1, q.2) ∈ (fun w : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ w.1, w.2)) ''
          {w | |w.1| ≤ 7 * h / 8 ∧ h / 2 ≤ |w.1| ∧ w.2 ∈ Icc a b} := by
  let Oraw : Set (ℝ × ℝ) := V ∩ {z | |z.1| < 7 * h / 8 ∧ 0 < σ * z.2}
  let O : Set Schoenflies.Plane := B '' Oraw
  have hOraw : IsOpen Oraw := hV.inter
    ((isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.mul continuous_snd)))
  have hO : IsOpen O := B.toHomeomorph.isOpenMap _ hOraw
  let Kphys : Set (Schoenflies.Plane × ℝ) := (fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' K
  have hKphys : IsCompact Kphys := hK.image ((B.continuous.comp continuous_fst).prodMk continuous_snd)
  have hcontact : (B '' (Prod.fst '' K)) ∩ (G '' sphere 0 r) ⊆
      B '' (saddleBandLevelCurve s t₀ σ '' Icc (-(5 * h / 8)) (5 * h / 8)) :=
    saddle_lower_band_inter_cap_circle_subset B G hs ht₀ ht₀δ hσ hh1
      (by linarith) hv₀ hv₀t hupper hclear
      (by rintro z ⟨p, hp, rfl⟩; exact hwidth p hp)
      (by rintro z ⟨p, hp, rfl⟩; exact hbottom p hp)
      (by rintro z ⟨p, hp, rfl⟩; exact henergy p hp)
  have hKO : (Prod.fst '' Kphys) ∩ (G '' sphere 0 r) ⊆ O := by
    rintro y ⟨⟨_, ⟨p, hp, rfl⟩, rfl⟩, hyC⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, heq⟩ := hcontact ⟨⟨p.1, mem_image_of_mem _ hp, rfl⟩, hyC⟩
    have hui : u ∈ Ioo (-h) h := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have huunit : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hui.1], hui.2.trans hh1⟩
    refine ⟨saddleBandLevelCurve s t₀ σ u, ⟨hcurveV ⟨u, hui, rfl⟩, ?_⟩, heq⟩
    refine ⟨?_, ?_⟩
    · change |u| < 7 * h / 8
      exact (abs_le.mpr hu).trans_lt (by linarith)
    · change 0 < σ * (σ * Real.sqrt _)
      rw [← mul_assoc, ← pow_two, hσ, one_mul]
      exact Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num)
        (add_pos_of_pos_of_nonneg ht₀ (mul_nonneg hs (sq_nonneg u))))
        (by nlinarith [huunit.1, huunit.2]))
  obtain ⟨ρ, hρ, hlocal⟩ := DifferentialGeometry.Analysis.exists_exp_smul_eq_imp_mem_of_isCompact
    G.symm.continuous G.symm.injective hKphys ((isCompact_sphere 0 r).image G.continuous)
    (isCompact_Icc (a := a) (b := b)) hO hKO
  refine ⟨ρ, hρ, ?_⟩
  intro μ hμ p hp q hq heq
  have hqO := hlocal μ hμ (B p.1, p.2) (mem_image_of_mem _ hp) q ⟨hq.1.1, hq.2⟩ heq
  obtain ⟨z, hz, hzq⟩ := hqO
  have hzC : B z ∈ G '' sphere 0 r := hzq ▸ hq.1.1
  have hlevel := PlanarJordan.cap_circle_height_eq_on_side_neighborhood B.toHomeomorph G.toHomeomorph hr hV hside hz.1 hzC
  have huunit : z.1 ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp (hz.2.1.trans (by linarith))
  have hden : 1 - z.1 ^ 2 ≠ 0 := by nlinarith [huunit.1, huunit.2]
  have hzcurve := saddleBandCurve_eq_saddleBandLevelCurve (s := s) (t := 0) hσ hden hz.2.2 (by simp)
  rw [saddleBandCurve_zero, hlevel] at hzcurve
  have ht : s + t₀ - s + 0 = t₀ := by ring
  rw [ht] at hzcurve
  have hwidthlo : h / 2 ≤ |z.1| := by
    by_contra hn
    have hsmall : |z.1| < 5 * h / 8 := (lt_of_not_ge hn).trans (by linarith)
    apply hq.1.2
    exact ⟨z, ⟨z.1, abs_lt.mp hsmall, hzcurve.symm⟩, hzq⟩
  refine ⟨(z.1, q.2), ⟨hz.2.1.le, hwidthlo, hq.2⟩, ?_⟩
  change (saddleBandLevelCurve s t₀ σ z.1, q.2) = (B.symm q.1, q.2)
  refine Prod.ext ?_ rfl
  rw [← hzcurve, ← hzq, B.symm_apply_apply]

private theorem exists_injOn_exp_projection_union_reference_cylinder
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    {s t₀ δ σ h R r v₀ a b δproj : ℝ} (hs : 0 ≤ s) (ht₀ : 0 < t₀)
    (ht₀δ : t₀ < δ) (hσ : σ ^ 2 = 1) (hh : 0 < h) (hh1 : h < 1)
    (hr : 0 < r) (hv₀ : 0 ≤ v₀) (hv₀t : v₀ ^ 2 < 2 * t₀)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-R) R)
    (hclear : ∀ a < t₀, ∃ ρ > 0, cthickening ρ
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-R) R ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
          (G '' closedBall 0 r)ᶜ)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, |p.1.1| ≤ 5 * h / 8)
    (hbottom : ∀ p ∈ K, -v₀ ≤ σ * p.1.2)
    (henergy : ∀ p ∈ K, (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 ≤ s + t₀)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcurveV : saddleBandLevelCurve s t₀ σ '' Ioo (-h) h ⊆ V)
    (hside : ∀ z ∈ V, B z ∈ G '' closedBall 0 r ↔
      s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    (hδproj : 0 < δproj)
    (hproj : ∀ μ ∈ Ioo (0 : ℝ) δproj,
      InjOn (fun p : (ℝ × ℝ) × ℝ => Real.exp (-μ * p.2) • G.symm (B p.1))
        (K ∪ (fun w : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ w.1, w.2)) ''
          {w | |w.1| ≤ 7 * h / 8 ∧ h / 2 ≤ |w.1| ∧ w.2 ∈ Icc a b})) :
    ∃ δ > 0, δ ≤ δproj ∧ ∀ μ ∈ Ioo (0 : ℝ) δ,
      InjOn (fun q : Schoenflies.Plane × ℝ => Real.exp (-μ * q.2) • G.symm q.1)
        (((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' K) ∪
          ((G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc a b)) := by
  obtain ⟨ρ, hρ, hlocal⟩ := exists_exp_projection_eq_imp_mem_reference_wall B G
    hs ht₀ ht₀δ hσ hh hh1 hr hv₀ hv₀t hupper hclear hK hwidth hbottom henergy hV hcurveV hside
  refine ⟨min δproj ρ, lt_min hδproj hρ, min_le_left _ _, ?_⟩
  intro μ hμ
  have hμproj : μ ∈ Ioo (0 : ℝ) δproj := ⟨hμ.1, hμ.2.trans_le (min_le_left _ _)⟩
  have hμlocal : μ ∈ Ioo (0 : ℝ) ρ := ⟨hμ.1, hμ.2.trans_le (min_le_right _ _)⟩
  have hcross (p : (ℝ × ℝ) × ℝ) (hp : p ∈ K) (q : Schoenflies.Plane × ℝ)
      (hq : q ∈ (G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc a b)
      (heq : Real.exp (-μ * p.2) • G.symm (B p.1) = Real.exp (-μ * q.2) • G.symm q.1) :
      (B p.1, p.2) = q := by
    have htail := hlocal μ hμlocal p hp q hq heq
    have hmodel : p = (B.symm q.1, q.2) := by
      apply hproj μ hμproj (Or.inl hp) (Or.inr htail)
      simpa only [B.apply_symm_apply] using heq
    apply Prod.ext
    · have hy := congrArg (fun p : (ℝ × ℝ) × ℝ => B p.1) hmodel
      simpa only [B.apply_symm_apply] using hy
    · exact congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) hmodel
  intro q hq w hw heq
  rcases hq with ⟨p, hp, rfl⟩ | hq
  · rcases hw with ⟨p', hp', rfl⟩ | hw
    · have he := hproj μ hμproj (Or.inl hp) (Or.inl hp') heq
      exact congrArg (fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) he
    · exact hcross p hp w hw heq
  · rcases hw with ⟨p, hp, rfl⟩ | hw
    · exact (hcross p hp q hq heq.symm).symm
    · exact DifferentialGeometry.Analysis.injOn_exp_smul_sphere_prod G.toHomeomorph hr.ne'
        hμ.1.ne' ⟨hq.1.1, mem_univ _⟩ ⟨hw.1.1, mem_univ _⟩ heq

open DifferentialGeometry.Topology.PlanarJordan in
private theorem exists_reference_cap_side
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    {s t δ σ h R r : ℝ} (hs : 0 ≤ s) (ht : 0 < t)
    (htδ : t < δ) (hσ : σ ^ 2 = 1) (hh : h < 1) (hr : 0 < r)
    {Γ S : Set Schoenflies.Plane}
    (hcircle : G '' sphere 0 r =
      B '' (saddleBandLevelCurve s t σ '' Icc (-h) h) ∪ Γ)
    (hΓ : Γ ∩ B '' (Icc (-h) h ×ˢ Icc (-R) R) ⊆
      {B (saddleBandLevelCurve s t σ (-h)), B (saddleBandLevelCurve s t σ h)})
    (hcontact : (G '' closedBall 0 r) ∩ S = G '' sphere 0 r)
    (hopposite : B '' (saddleBandLevelCurve s t (-σ) '' Icc (-h) h) ⊆ S)
    (hrectangle : saddleBandLevelCurve s t (-σ) '' Icc (-h) h ⊆
      Icc (-h) h ×ˢ Icc (-R) R)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-R) R) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧
      saddleBandLevelCurve s t σ '' Ioo (-h) h ⊆ V ∧
      V ⊆ Ioo (-h) h ×ˢ Ioo (-R) R ∧
      ∀ z ∈ V, B z ∈ G '' closedBall 0 r ↔
        s + t ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by
  let C := G '' sphere 0 r
  have hC : Schoenflies.IsSeparating C :=
    Schoenflies.jordan_curve_theorem (isJordanCurve_image_sphere G.toHomeomorph 0 hr)
  have hdisk : G '' closedBall 0 r = closure (Schoenflies.inside C) :=
    image_closedBall_eq_closure_inside_image_sphere G.toHomeomorph 0 hr
  have hbound (u : ℝ) (hu : u ∈ Ioo (-h) h) :
      |(saddleBandLevelCurve s t σ u).2| < R := by
    have hui : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans hh⟩
    have hden : 0 < 1 - u ^ 2 := by nlinarith [hui.1, hui.2]
    have hlo := saddleBandLevelCurve_height hs ht hσ hui (0 : ℝ)
    have hhi := saddleBandLevelCurve_height hs (ht.trans htδ) hσ hui (0 : ℝ)
    simp only [zero_add, saddleBandLevelCurve] at hlo hhi
    have hsq : (saddleBandLevelCurve s t σ u).2 ^ 2 <
        (saddleBandLevelCurve s δ σ u).2 ^ 2 := by
      by_contra hn
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hden.le
      dsimp only [saddleBandLevelCurve] at hm
      nlinarith
    have hv := (hupper u ⟨hu.1.le, hu.2.le⟩).2
    have hR : 0 ≤ R := by linarith [hv.1, hv.2]
    have hsqR : (saddleBandLevelCurve s δ σ u).2 ^ 2 ≤ R ^ 2 := by nlinarith [hv.1, hv.2]
    apply abs_lt.mpr
    constructor <;> nlinarith
  have hselected (u : ℝ) (hu : u ∈ Ioo (-h) h) :
      B (saddleBandLevelCurve s t σ u) ∈ C :=
    hcircle.symm.subset (Or.inl ⟨_, ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩, rfl⟩)
  have hout (u : ℝ) (hu : u ∈ Ioo (-h) h) :
      B (saddleBandLevelCurve s t (-σ) u) ∉ closure (Schoenflies.inside C) := by
    rw [← hdisk]
    apply not_mem_image_closedBall_of_lt_saddleBandLevelCurve B.toHomeomorph G.toHomeomorph
      hs ht hσ hh hcircle hΓ hcontact hopposite hrectangle
      (hrectangle ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩)
    have hui : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans hh⟩
    have hpos : 0 < σ * (σ * Real.sqrt (2 * (t + s * u ^ 2) / (1 - u ^ 2))) := by
      rw [← mul_assoc, ← pow_two, hσ, one_mul]
      exact Real.sqrt_pos.mpr (div_pos
        (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg ht (mul_nonneg hs (sq_nonneg u))))
        (by nlinarith [hui.1, hui.2]))
    change σ * (-σ * Real.sqrt (2 * (t + s * u ^ 2) / (1 - u ^ 2))) <
      σ * (σ * Real.sqrt (2 * (t + s * u ^ 2) / (1 - u ^ 2)))
    rw [neg_mul, mul_neg]
    linarith
  have hlevel (z : ℝ × ℝ) (hz : z ∈ Icc (-h) h ×ˢ Icc (-R) R) (hzC : B z ∈ C) :
      (0 : ℝ) + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = 0 + s + t := by
    have hsel : B z ∈ B '' (saddleBandLevelCurve s t σ '' Icc (-h) h) := by
      rcases hcircle.subset hzC with hsel | hother
      · exact hsel
      · rcases hΓ ⟨hother, mem_image_of_mem B hz⟩ with heq | heq
        · exact ⟨_, ⟨-h, ⟨le_rfl, hz.1.1.trans hz.1.2⟩, rfl⟩, heq.symm⟩
        · exact ⟨_, ⟨h, ⟨hz.1.1.trans hz.1.2, le_rfl⟩, rfl⟩,
            (mem_singleton_iff.mp heq).symm⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, heq⟩ := hsel
    have hzEq := B.injective heq
    rw [← hzEq]
    exact saddleBandLevelCurve_height hs ht hσ
      ⟨by linarith [hu.1], hu.2.trans_lt hh⟩ 0
  obtain ⟨V, hV, hcurve, hVsub, _, hVside⟩ :=
    exists_open_side_neighborhood_of_saddleBandLevelCurve hC B hs ht hσ hh
      hbound hselected hout hlevel
  refine ⟨V, hV, hcurve, hVsub, ?_⟩
  intro z hz
  rw [hdisk]
  simpa only [zero_add] using hVside z hz

private theorem exists_isOpen_inter_range_eq_circle_strip
    {e : SphereTwo → Plane × ℝ} (he : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, Plane × ℝ) ∞ e)
    (G : Plane ≃ₘ[ℝ] Plane) {r : ℝ} (hr : 0 < r)
    {A : Set Plane} (hA : IsClosed A) {J : Set ℝ} (hJ : IsOpen J)
    (hwall : (G '' sphere 0 r \ A) ×ˢ J ⊆ range e) :
    ∃ W : Set (Plane × ℝ), IsOpen W ∧
      W ∩ range e = (G '' sphere 0 r \ A) ×ˢ J := by
  obtain ⟨γ, hγ, hγrange⟩ := exists_isSmoothEmbedding_addCircle_range_eq_sphere
    (E := Plane) (by simp) 0 hr
  let q : AddCircle (1 : ℝ) → Plane := G ∘ γ
  have hq : IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ q := hγ.diffeomorph_comp G
  have hqrange : range q = G '' sphere 0 r := by
    change range (G ∘ γ) = _
    rw [range_comp, hγrange]
  let O : TopologicalSpace.Opens (AddCircle (1 : ℝ)) := ⟨q ⁻¹' Aᶜ, hA.isOpen_compl.preimage hq.contMDiff.continuous⟩
  let I : TopologicalSpace.Opens ℝ := ⟨J, hJ⟩
  let w : O × I → Plane × ℝ := fun p => (q p.1.val, p.2.val)
  have hw : IsSmoothEmbedding (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Plane × ℝ) ∞ w := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (hq.comp (IsSmoothEmbedding.of_opens O) (by simp)).prodMap
      (IsSmoothEmbedding.of_opens I)
  have hwset : range w = (G '' sphere 0 r \ A) ×ˢ J := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨hqrange.subset (mem_range_self p.1.val), p.1.property⟩, p.2.property⟩
    · rintro ⟨⟨hz, hzA⟩, hzt⟩
      obtain ⟨x, hx⟩ := hqrange.symm.subset hz
      exact ⟨(⟨x, by change q x ∉ A; rwa [hx]⟩, ⟨z.2, hzt⟩), Prod.ext hx rfl⟩
  have hwrange : range w ⊆ range e := hwset ▸ hwall
  let f := he.lift w hwrange
  have hf : IsSmoothEmbedding (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ f :=
    he.isSmoothEmbedding_lift hw (by simp) hwrange
  have hfo : IsOpen (range f) :=
    Manifold.isOpen_range_of_isSmoothEmbedding (by simp [Module.finrank_prod]) hf
  obtain ⟨W, hW, hpre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp hfo
  refine ⟨W, hW, ?_⟩
  rw [← hwset]
  ext z
  constructor
  · rintro ⟨hzW, x, rfl⟩
    have hx : x ∈ range f := by rw [← hpre]; exact hzW
    obtain ⟨p, rfl⟩ := hx
    exact ⟨p, (he.comp_lift hwrange p).symm⟩
  · rintro ⟨p, rfl⟩
    have hpW : e (f p) ∈ W := by change f p ∈ e ⁻¹' W; rw [hpre]; exact mem_range_self p
    rw [he.comp_lift hwrange] at hpW
    exact ⟨hpW, f p, he.comp_lift hwrange p⟩

private theorem exists_isOpen_boundary_collar_disjoint_cap_interior
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane) (G : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {s t₀ δ ε d h ρ ell r σ : ℝ} (hs : 0 < s) (ht₀ : 0 < t₀)
    (ht₀δ : t₀ < δ) (ht₀d : t₀ < d) (hε : 0 < ε) (hεh : ε < s * h ^ 2 / 16)
    (hh : 0 < h) (hh1 : h < 1) (hσ : σ ^ 2 = 1)
    {θ : ℝ × ℝ → ℝ} (hθ01 : ∀ q, θ q ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    (hθ1 : ∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1)
    {Γ S : Set Schoenflies.Plane}
    (hcircle : G '' sphere 0 r =
      B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ∪ Γ)
    (hΓ : Γ ∩ B '' (Icc (-h) h ×ˢ Icc (-ρ) ρ) ⊆
      {B (saddleBandLevelCurve s t₀ σ (-h)), B (saddleBandLevelCurve s t₀ σ h)})
    (hcontact : (G '' closedBall 0 r) ∩ S = G '' sphere 0 r)
    (hopposite : B '' (saddleBandLevelCurve s t₀ (-σ) '' Icc (-h) h) ⊆ S)
    (hrectangle : saddleBandLevelCurve s t₀ (-σ) '' Icc (-h) h ⊆
      Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    {S₃ Z W : Set (Schoenflies.Plane × ℝ)} (hZ : IsOpen Z) (hW : IsOpen W)
    (hWeq : W ∩ S₃ =
      (G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Icc (-(3 * h / 4)) (3 * h / 4))) ×ˢ
        Ioo (ell - ε) (ell + d))
    (hfilled : (fun q : ℝ × (ℝ × ℝ) =>
        (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), ell + q.1)) ''
      {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
        s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
        (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
          s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)} ⊆ Z)
    (hZeq : Z ∩ S₃ = Z ∩ {q |
      (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
        s + (q.2 - ell) + θ (q.2 - ell, (B.symm q.1).1) * (t₀ - (q.2 - ell))}) :
    ∃ N : Set (Schoenflies.Plane × ℝ), IsOpen N ∧
      frontier (G '' closedBall 0 r) ×ˢ Icc (ell - ε / 2) (ell + t₀) ⊆ N ∧
      N ∩ S₃ ⊆ {q | q.1 ∉ interior (G '' closedBall 0 r)} := by
  let Q : Set (ℝ × ℝ) := Ioo (-h) h ×ˢ Ioo (-ρ) ρ
  let N : Set (Schoenflies.Plane × ℝ) := W ∪ (Z ∩ (fun q => B.symm q.1) ⁻¹' Q)
  have hQ : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hN : IsOpen N := hW.union (hZ.inter (hQ.preimage (B.symm.continuous.comp continuous_fst)))
  have hstrict (u : ℝ) (hu : u ∈ Icc (-(3 * h / 4)) (3 * h / 4)) :
      saddleBandLevelCurve s t₀ σ u ∈ Q := by
    have hufull : u ∈ Icc (-h) h := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hui : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hden : 0 < 1 - u ^ 2 := by nlinarith [hui.1, hui.2]
    have hlow := saddleBandLevelCurve_height hs.le ht₀ hσ hui (0 : ℝ)
    have hhigh := saddleBandLevelCurve_height hs.le (ht₀.trans ht₀δ) hσ hui (0 : ℝ)
    simp only [zero_add, saddleBandLevelCurve] at hlow hhigh
    have hsq : (saddleBandLevelCurve s t₀ σ u).2 ^ 2 <
        (saddleBandLevelCurve s δ σ u).2 ^ 2 := by
      by_contra hnot
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hden.le
      change (1 - u ^ 2) * (saddleBandLevelCurve s δ σ u).2 ^ 2 ≤
        (1 - u ^ 2) * (saddleBandLevelCurve s t₀ σ u).2 ^ 2 at hm
      dsimp only [saddleBandLevelCurve] at hm
      nlinarith
    have hvupper := (hupper u hufull).2
    refine ⟨⟨by change -h < u; linarith [hu.1], by change u < h; linarith [hu.2]⟩, ?_⟩
    have hρ : 0 ≤ ρ := by linarith [hvupper.1, hvupper.2]
    have hhighsq : (saddleBandLevelCurve s δ σ u).2 ^ 2 ≤ ρ ^ 2 := by
      nlinarith [hvupper.1, hvupper.2]
    constructor <;> nlinarith
  have hwallZ (u : ℝ) (hu : u ∈ Icc (-h) h) (v : ℝ)
      (hv : v ∈ Icc (ell - ε / 2) (ell + t₀)) :
      (B (saddleBandLevelCurve s t₀ σ u), v) ∈ Z := by
    have ht : v - ell ∈ Icc (-ε) t₀ := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    obtain ⟨z, hz, hzimage⟩ := saddleBandLevelCurve_mem_image_cutoff_region
      hs hh1 ht₀ hεh hθ01 hθ0 ht (abs_le.mpr hu) hσ
    apply hfilled
    refine ⟨(v - ell, z), ⟨⟨ht.1, ht.2.trans ht₀d.le⟩, hz⟩, ?_⟩
    exact Prod.ext (congrArg B hzimage) (by simp)
  refine ⟨N, hN, ?_, ?_⟩
  · rintro ⟨y, v⟩ ⟨hy, hv⟩
    have hycircle : y ∈ G '' sphere 0 r := by
      simpa only [← G.image_frontier, frontier_closedBall'] using hy
    by_cases hyinner : y ∈ B '' (saddleBandLevelCurve s t₀ σ '' Icc (-(3 * h / 4)) (3 * h / 4))
    · obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hyinner
      right
      refine ⟨hwallZ u ⟨by linarith [hu.1], by linarith [hu.2]⟩ v hv, ?_⟩
      change B.symm (B (saddleBandLevelCurve s t₀ σ u)) ∈ Q
      rw [B.symm_apply_apply]
      exact hstrict u hu
    · left
      exact (hWeq.symm.subset ⟨⟨hycircle, hyinner⟩, ⟨by linarith [hv.1], by linarith [hv.2]⟩⟩).1
  · rintro q ⟨hq, hqS₃⟩
    rcases hq with hqW | ⟨hqZ, hqQ⟩
    · have hcircleq := (hWeq.subset ⟨hqW, hqS₃⟩).1.1
      have hfront : q.1 ∈ frontier (G '' closedBall 0 r) := by
        simpa only [← G.image_frontier, frontier_closedBall'] using hcircleq
      exact fun hi => disjoint_left.mp disjoint_interior_frontier hi hfront
    · let z := B.symm q.1
      have hzQ : z ∈ Q := hqQ
      have hmodel := (hZeq.subset ⟨hqZ, hqS₃⟩).2
      have henergy : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + t₀ := by
        change (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 =
          s + (q.2 - ell) + θ (q.2 - ell, z.1) * (t₀ - (q.2 - ell)) at hmodel
        rw [hmodel]
        by_cases ht : t₀ / 2 ≤ q.2 - ell
        · rw [hθ1 _ _ (Or.inl ht)]
          linarith
        · have hmul := mul_nonneg (sub_nonneg.mpr (hθ01 (q.2 - ell, z.1)).2)
            (show 0 ≤ t₀ - (q.2 - ell) by linarith)
          nlinarith
      have hzclosed : z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ :=
        ⟨⟨hzQ.1.1.le, hzQ.1.2.le⟩, ⟨hzQ.2.1.le, hzQ.2.2.le⟩⟩
      have hzside : σ * z.2 ≤ σ * (saddleBandLevelCurve s t₀ σ z.1).2 := by
        have hu : z.1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hzQ.1.1], by linarith [hzQ.1.2]⟩
        have hden : 0 < 1 - z.1 ^ 2 := by nlinarith [hu.1, hu.2]
        let v := (saddleBandLevelCurve s t₀ σ z.1).2
        have hheight : (1 - z.1 ^ 2) * (v ^ 2 + 2 * s) / 2 = s + t₀ := by
          simpa only [zero_add, saddleBandLevelCurve, v] using saddleBandLevelCurve_height hs.le ht₀ hσ hu 0
        have hsq : z.2 ^ 2 ≤ v ^ 2 := by
          by_contra hn
          have hm := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hden
          nlinarith
        have hv : 0 < σ * v := by
          change 0 < σ * (σ * Real.sqrt (2 * (t₀ + s * z.1 ^ 2) / (1 - z.1 ^ 2)))
          rw [← mul_assoc, ← pow_two, hσ, one_mul]
          exact Real.sqrt_pos.mpr (div_pos
            (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg ht₀ (mul_nonneg hs.le (sq_nonneg z.1)))) hden)
        have hsquare (w : ℝ) : (σ * w) ^ 2 = w ^ 2 := by rw [mul_pow, hσ, one_mul]
        have hsq' : (σ * z.2) ^ 2 ≤ (σ * v) ^ 2 := by simpa only [hsquare] using hsq
        change σ * z.2 ≤ σ * v
        nlinarith
      have hout := PlanarJordan.not_mem_interior_image_closedBall_of_le_saddleBandLevelCurve
        B G hs.le ht₀ hσ hh1 hcircle hΓ hcontact hopposite hrectangle hzclosed hzside
      change q.1 ∉ interior (G '' closedBall 0 r)
      simpa only [z, B.apply_symm_apply] using hout

private theorem exists_inverse_fiber_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (ℝ × E) ≃ₘ[ℝ] (ℝ × E))
    (hF : ∀ p, (F p).1 = p.1) {t₀ : ℝ}
    (hF₀ : ∀ x, F (t₀, x) = (t₀, x)) :
    ∃ P : ℝ → E ≃ₘ[ℝ] E,
      ContDiff ℝ ∞ (fun p : ℝ × E => P p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (P p.1).symm p.2) ∧
      (∀ t y, P t y = (F.symm (t, y)).2) ∧
      (∀ t y, (P t).symm y = (F (t, y)).2) ∧
      P t₀ = Diffeomorph.refl 𝓘(ℝ, E) E ∞ := by
  let F' : (ℝ × E) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E),
      (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)⟯ (ℝ × E) :=
    { toEquiv := F.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact F.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact F.symm.contMDiff }
  let C := Diffeomorph.prodComm 𝓘(ℝ, E) 𝓘(ℝ, ℝ) E ℝ ∞
  let G := (C.trans F'.symm).trans C.symm
  have hFi (p : ℝ × E) : (F.symm p).1 = p.1 :=
    (hF (F.symm p)).symm.trans (congrArg Prod.fst (F.apply_symm_apply p))
  have hG (p : E × ℝ) : (G p).2 = p.2 := hFi (p.2, p.1)
  let P : ℝ → E ≃ₘ[ℝ] E := G.restrictFiber hG
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ (fun p : ℝ × E => (F.symm p).2)
    exact F.symm.contDiff.snd
  · change ContDiff ℝ ∞ (fun p : ℝ × E => (F p).2)
    exact F.contDiff.snd
  · intro t y
    rfl
  · intro t y
    rfl
  · apply Diffeomorph.ext
    intro y
    change (F.symm (t₀, y)).2 = y
    have h := congrArg F.symm (hF₀ y)
    rw [F.symm_apply_apply] at h
    exact (congrArg Prod.snd h).symm

private theorem exists_height_preserving_diffeomorph_saddle_cutoff_model_and_cap_of_one_saddle
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
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
      let τ := δ / 2
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ η : unitInterval → SphereTwo, ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
      let γ := fun q : ℝ × unitInterval => (L (e (Φ (q.1 - τ) (η q.2)))).1
      ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)) ∧
          ∀ u, e (Φ (t - τ) (η u)) 2 = c + s + t) ∧
        (∀ t ∈ Ioc (0 : ℝ) δ,
          IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
            (B (saddleBandLevelCurve s t σ h))
            (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
            (range (fun u => γ (t, u)))) ∧
      ∃ r : ℝ, 0 < r ∧
      let m := e p 2
      let b := m - r ^ 2 / 2
      c + s + τ < b ∧
      ∃ A : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ z, (A z).2 = z.2) ∧
        (L ∘ e) '' connectedComponentIn {x | b ≤ e x 2} p =
          (fun y => A (y, m + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
      ∃ G : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => G z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (G z.1).symm z.2) ∧
        (∀ t ∈ Icc τ (b - (c + s)), C t = G (c + s + t) '' sphere 0 r) ∧
        (∀ t ∈ Icc (c + s + τ) b,
          (G t '' closedBall 0 r) ∩ ((fun x => (L (e x)).1) '' {x | e x 2 = t}) =
            G t '' sphere 0 r) ∧
      ∃ t₀ : ℝ, τ < t₀ ∧ t₀ < δ ∧ c + s + t₀ < b ∧
      ∃ d : ℝ, t₀ < d ∧ d < δ ∧
      ∃ ε > 0, ε < t₀ / 4 ∧ ε < s * h ^ 2 / 16 ∧
      ∃ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ ∧ (∀ q, θ q ∈ Icc (0 : ℝ) 1) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
      ∃ κ : ContDiffBump (0 : ℝ), κ.rIn = h / 4 ∧ κ.rOut = h / 2 ∧
        (∀ t u, θ (t, u) =
          1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u) ∧
      ∃ ν > 0, Ioo (t₀ - ν) (t₀ + ν) ⊆ Ioo τ (min δ (b - (c + s))) ∧
      ∃ H : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
        H (c + s + t₀) = G (c + s + t₀) ∧
        (∀ t, c + s + t₀ - ν < t → H t '' closedBall 0 r = G t '' closedBall 0 r) ∧
      ∃ D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ z, (D z).2 = z.2) ∧
        (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b m x t, t) = (H t x, t)) ∧
        (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : Plane) ρ, D (x, t) = A (x, t)) ∧
        D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 ≤ m - ‖z.1‖ ^ 2 / 2} =
          heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∧
        heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∩ range (L ∘ e) =
          D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2} ∧
      ∃ T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
        (∀ z, T z = (G (c + s + t₀) ((H z.2).symm z.1), z.2)) ∧
        (∀ z, (T z).2 = z.2) ∧
        (∀ y, T (y, c + s + t₀) = (y, c + s + t₀)) ∧
        (∀ t ∈ Icc (-d) d, ∀ u,
          T (γ (t, u), c + s + t) = (γ (t₀, u), c + s + t)) ∧
        ((G (c + s + t₀) '' closedBall 0 r) ×ˢ Icc (c + s + t₀) b) ∩
            range (T ∘ L ∘ e) =
          (G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + t₀) b ∧
      ∃ V : Set (ℝ × (ℝ × ℝ)), IsOpen V ∧
        {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
          (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V ∧
        (∀ q ∈ V, θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
          (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
            0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (t₀ - q.1)) /
              q.2.2 ^ 2)) ∧
        (∀ q ∈ V, T (B q.2, c + s + q.1) =
          (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1)) ∧
        (∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U) ∧
      let K : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
        (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}
      ∃ Z : Set (Plane × ℝ), IsOpen Z ∧
        Z ⊆ T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' V) ∧
        Z ∩ range (T ∘ L ∘ e) =
          Z ∩ {q | (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
            s + (q.2 - (c + s)) +
              θ (q.2 - (c + s), (B.symm q.1).1) * (t₀ - (q.2 - (c + s)))} ∧
        ∃ ρ > 0, cthickening ρ
          (T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' K)) ⊆ Z ∧
        cthickening ρ (T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) ''
          {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
            s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
              (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
                s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)})) ⊆ Z ∧
      ∃ R > 0, Icc (-h) h ×ˢ Icc (-R) R ⊆ U ∧
        (∀ t ∈ Icc (-δ) δ, ∀ σ' : ℝ, σ' ^ 2 = 1 → ∀ u ∈ Icc (-h) h,
          saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-R) R) ∧
        (∀ a < t₀, ∃ ρ > 0, cthickening ρ
          (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-R) R ∧
            (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
          (G (c + s + t₀) '' closedBall 0 r)ᶜ) ∧
      ∃ O : Set (ℝ × ℝ), IsOpen O ∧ ∃ g : (ℝ × ℝ) → ℝ,
        ContDiffOn ℝ ∞ g O ∧ (∀ z ∈ O, g z ∈ Ioo (-ε) (t₀ / 2)) ∧
        ∃ W : Set (Plane × ℝ), IsOpen W ∧ W ⊆ Z ∧
          W ⊆ {q | B.symm q.1 ∈ O ∧ q.2 - (c + s) ∈ Ioo (-ε) (t₀ / 2)} ∧
          T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) ''
            {q | q.1 ∈ Ioo (-ε) (t₀ / 2) ∧ |q.2.1| < h / 2 ∧
              (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}) ⊆ W ∧
          W ∩ range (T ∘ L ∘ e) = W ∩ {q | q.2 = c + s + g (B.symm q.1)} ∧
          (∀ t ∈ Icc (-δ) δ, ∀ u,
            B.symm (γ (t, u)) ∈ Icc (-h) h ×ˢ Icc (-R) R →
              B.symm (γ (t, u)) = saddleBandLevelCurve s t σ (-h) ∨
                B.symm (γ (t, u)) = saddleBandLevelCurve s t σ h) := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
      r, hr, hab, A, hA, hnormal, hcap, Ψ, hΨ, hΨi, hΨa,
      G, hGformula, hG, hGi, hCcap, hcontact, hcapgerm,
      γ₀, η, hγ₀, hη, hηeq, hγ₀0, hγ₀1, hγrange, hηrange,
      Φ, hΦ, hΦi, hΦ0, T, hT, hδT, hTsh, ρ, hρ, N, hN, hηN, hheight, hNcircle,
      hsourcefamily, hplanefamily, hslices, hendpoints, hcoverage, hambient,
      hcompact, V, hV, hVe, htraceV, hcontactRect, hmodelRect, hrectangle, hrectangleLevel⟩ :=
    exists_closing_arc_family_and_height_cap_inter_rectangle_of_one_saddle he hnd hinj hone hconn
      B hU hzero hβ hs hgraph hβcrit hβindex
  obtain ⟨ε, hε, hεhalf, hendpoint⟩ := hendpoints
  let W : Set unitInterval := {u | (u : ℝ) < ε ∨ 1 - ε < (u : ℝ)}
  have hW : IsOpen W := (isOpen_lt continuous_subtype_val continuous_const).union
    (isOpen_lt continuous_const continuous_subtype_val)
  have hW0 : (0 : unitInterval) ∈ W := Or.inl (by simpa using hε)
  have hW1 : (1 : unitInterval) ∈ W := Or.inr (by change 1 - ε < 1; linarith)
  have hσsq : σ ^ 2 = 1 := by
    rcases hσ with hσ | hσ
    · rw [hσ]; norm_num
    · rw [mem_singleton_iff.mp hσ]; norm_num
  obtain ⟨R₀, τcap, hrR₀, hτcap, hrτcap, hnormal⟩ := hnormal
  obtain ⟨δcap, hδcap, R, hrR, hmodel⟩ := hcapgerm
  have hnormal' :
      (closedBall 0 R₀ ×ˢ closedBall (e p 2) τcap) ∩
        range (A.symm ∘ (EuclideanSpace.equivProdLast 2 ∘ e)) =
        (fun y => (y, e p 2 - ‖y‖ ^ 2 / 2)) '' closedBall 0 R₀ := by
    simpa only [Function.comp_def, neg_div, one_div_mul_eq_div, neg_mul,
      sub_eq_add_neg] using hnormal
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let γ : ℝ × unitInterval → Plane := fun q => (L (e (Φ (q.1 - δ / 2) (η q.2)))).1
  have hclear (t₀ : ℝ)
      (ht₀ : t₀ ∈ Ioo (δ / 2) (min δ (e p 2 - r ^ 2 / 2 - (c + s))))
      (a : ℝ) (ha : a < t₀) :
      ∃ ε > 0, cthickening ε
        (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
        (G (c + s + t₀) '' closedBall 0 r)ᶜ := by
    have ht₀pos : 0 < t₀ := (half_pos hδ).trans ht₀.1
    have ht₀δ : t₀ ≤ δ := (ht₀.2.trans_le (min_le_left _ _)).le
    have ht₀I : t₀ ∈ Icc (-δ) δ := ⟨by linarith, ht₀δ⟩
    have ht₀cap : t₀ ∈ Icc (δ / 2) (e p 2 - r ^ 2 / 2 - (c + s)) :=
      ⟨ht₀.1.le, (ht₀.2.trans_le (min_le_right _ _)).le⟩
    have hcircle : G (c + s + t₀) '' sphere 0 r =
        B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ∪
          range (fun u => γ (t₀, u)) :=
      (hCcap t₀ ht₀cap).symm.trans (hcoverage t₀ ⟨ht₀pos, ht₀δ⟩).union_eq.symm
    have hclosing : range (fun u => γ (t₀, u)) ∩
        B '' (Icc (-h) h ×ˢ Icc (-ρ) ρ) ⊆
        {B (saddleBandLevelCurve s t₀ σ (-h)), B (saddleBandLevelCurve s t₀ σ h)} := by
      rintro y ⟨⟨u, rfl⟩, z, hz, heq⟩
      change B z = γ (t₀, u) at heq
      have hmem : B.symm (γ (t₀, u)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ := by
        rw [← heq, B.symm_apply_apply]
        exact hz
      rcases hcontactRect t₀ ht₀I u hmem with hleft | hright
      · exact Or.inl (by simpa only [B.apply_symm_apply] using congrArg B hleft)
      · exact Or.inr (mem_singleton_iff.mpr
          (by simpa only [B.apply_symm_apply] using congrArg B hright))
    have hopposite : B '' (saddleBandLevelCurve s t₀ (-σ) '' Icc (-h) h) ⊆
        (fun x => (L (e x)).1) '' {x | e x 2 = c + s + t₀} := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have hnegσ : (-σ) ^ 2 = 1 := by simpa only [neg_sq] using hσsq
      have hzu := hrectangle (hmodelRect t₀ ht₀I (-σ) hnegσ u hu)
      have huone : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hpoint := hgraph _ hzu
      rw [saddleBandLevelCurve_height hs.le ht₀pos hnegσ huone c] at hpoint
      exact ⟨β (saddleBandLevelCurve s t₀ (-σ) u), congrArg Prod.snd hpoint,
        congrArg Prod.fst hpoint⟩
    exact PlanarJordan.exists_cthickening_saddle_band_sublevel_disjoint_image_closedBall
      B.toHomeomorph (G (c + s + t₀)).toHomeomorph hs.le ht₀pos hσsq hh1 hcircle
      hclosing (hcontact (c + s + t₀) ⟨by linarith [ht₀cap.1], by linarith [ht₀cap.2]⟩)
      hopposite (by
        rintro _ ⟨u, hu, rfl⟩
        exact hmodelRect t₀ ht₀I (-σ) (by simpa only [neg_sq] using hσsq) u hu) ha
  have hgap : δ / 2 < min δ (e p 2 - r ^ 2 / 2 - (c + s)) :=
    lt_min (half_lt_self hδ) (by linarith)
  obtain ⟨t₀, hτt₀, ht₀⟩ := exists_between hgap
  have ht₀pos : 0 < t₀ := (half_pos hδ).trans hτt₀
  have ht₀δ : t₀ < δ := ht₀.trans_le (min_le_left _ _)
  have ht₀b : c + s + t₀ < e p 2 - r ^ 2 / 2 := by
    linarith [ht₀.trans_le (min_le_right _ _)]
  let d₀ := (t₀ + δ) / 2
  have ht₀d₀ : t₀ < d₀ := by dsimp [d₀]; linarith
  have hd₀δ : d₀ < δ := by dsimp [d₀]; linarith
  have hd₀pos : 0 < d₀ := ht₀pos.trans ht₀d₀
  have hJ : Icc (-d₀) d₀ ⊆ Ioo (-δ) δ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨εcut, hεcut, hεcutd, hεcutt, hεcuth, θ, hθ, hθ01, hθ0, hθ1, hθzero,
      κ, hκin, hκout, hθformula, Ξ, hΞ, hΞi, hΞ0, hΞheight, hΞbase, hΞarc,
      ⟨Vcut, hVcut, hKcut, hΞcut, hVregular⟩, S, hS, hΞS⟩ :=
    PlanarJordan.exists_ambient_isotopy_closing_arc_eqOn_saddle_cutoff_region
      hplanefamily.contMDiffOn B hs hσsq hh hh1 (hδT.trans hTsh)
      (neg_neg_of_pos hd₀pos) ⟨ht₀pos, ht₀d₀⟩ hJ
      (fun t ht => (hslices t ht).1) hW hW0 hW1
      (v := fun u => (B.symm (γ₀ u)).1)
      (fun u hu => ⟨(hendpoint u hu).1, fun t ht => ((hendpoint u hu).2.2 t ht).2⟩)
      (fun t ht => ⟨(hslices t ht).2.2.1, (hslices t ht).2.2.2.1⟩)
      hcontactRect (fun t ht u hu => hmodelRect t ht 1 (by norm_num) u hu)
  have hrawU (t : ℝ) (ht : t ∈ Icc (-εcut) d₀) (z : ℝ × ℝ)
      (hz : |z.1| ≤ h) (hgraphz : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t) : z ∈ U := by
    apply hrectangle
    exact mem_rectangle_of_saddle_band_height_le (abs_lt.mp (hz.trans_lt hh1))
      (by rw [hgraphz]; linarith [ht.2])
      (hmodelRect d₀ ⟨by linarith, hd₀δ.le⟩ 1 (by norm_num) z.1 (abs_le.mp hz))
  obtain ⟨P, hP, hPi, hPformula, hPiformula, hP₀⟩ :=
    exists_inverse_fiber_family (Ξ 1) (hΞheight 1) (hΞbase 1)
  have hParc (t : ℝ) (ht : t ∈ Icc (-d₀) d₀) (u : unitInterval) :
      (P t).symm (γ (t, u)) = γ (t₀, u) := by
    rw [hPiformula]
    have hcur := congrArg Prod.snd (hΞarc 1 ⟨by norm_num, le_rfl⟩ t ht u)
    simpa only [sub_self, zero_mul, one_mul, zero_add] using hcur
  let ε₀ := min (t₀ / 4) ((d₀ - t₀) / 2)
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (half_pos (sub_pos.mpr ht₀d₀))
  have hε₀t : ε₀ ≤ t₀ / 4 := min_le_left _ _
  have hε₀d : ε₀ ≤ (d₀ - t₀) / 2 := min_le_right _ _
  have hPC (t : ℝ) (ht : t ∈ Icc (t₀ - ε₀) (t₀ + ε₀)) :
      P t '' ((fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t₀ ≤ e x 2} p ∩ {x | e x 2 = c + s + t₀})) =
      (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t}) := by
    have htpos : 0 < t := by linarith [ht.1]
    have htJ : t ∈ Icc (-d₀) d₀ := by constructor <;> linarith [ht.1, ht.2]
    have htδ : t ≤ δ := htJ.2.trans hd₀δ.le
    apply PlanarJordan.image_circle_eq_of_closing_arc_and_saddle_band_time_change
      (P t).toEquiv B hs.le ht₀pos.le htpos hσsq hh1
      (hcoverage t ⟨htpos, htδ⟩) (hcoverage t₀ ⟨ht₀pos, ht₀δ.le⟩)
      (θ := fun u => θ (t, u))
      (fun u _ => hθ1 t u (Or.inl (by linarith [ht.1])))
      (hParc t htJ)
    intro z hz hgraphz
    change (P t).symm (B z) = _
    rw [hPiformula]
    have hzV : (t, z) ∈ Vcut := by
      apply hKcut
      refine ⟨⟨by linarith, htJ.2⟩, hz, hgraphz.ge, ?_⟩
      simp only [hgraphz, hθ1 t z.1 (Or.inl (by linarith [ht.1])), sub_self, zero_mul,
        add_zero, le_refl]
    have hmodel := congrArg Prod.snd (hΞcut 1 ⟨by norm_num, le_rfl⟩ (t, z) hzV)
    simpa only [one_mul] using hmodel
  let djoin := min ε₀ (min ((t₀ - δ / 2) / 2)
    ((min δ (e p 2 - r ^ 2 / 2 - (c + s)) - t₀) / 2))
  have hdjoin : 0 < djoin := lt_min hε₀
    (lt_min (half_pos (sub_pos.mpr hτt₀)) (half_pos (sub_pos.mpr ht₀)))
  have hdjoinε : djoin ≤ ε₀ := min_le_left _ _
  have hdjoinl : djoin ≤ (t₀ - δ / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdjoinr : djoin ≤ (min δ (e p 2 - r ^ 2 / 2 - (c + s)) - t₀) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let Q (t : ℝ) := P (t - (c + s))
  have hQ : ContDiff ℝ ∞ (fun z : ℝ × Plane => Q z.1 z.2) :=
    hP.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  have hQi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (Q z.1).symm z.2) :=
    hPi.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  have hQ₀ : Q (c + s + t₀) = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ := by
    simpa only [Q, add_sub_cancel_left] using hP₀
  have hcircle (t : ℝ) (ht : t ∈ Ioo (c + s + t₀ - djoin) (c + s + t₀ + djoin)) :
      Q t '' (G (c + s + t₀) '' sphere 0 r) = G t '' sphere 0 r := by
    have htime : t - (c + s) ∈ Icc (t₀ - ε₀) (t₀ + ε₀) := by
      constructor <;> linarith [ht.1, ht.2]
    have href : t₀ ∈ Icc (δ / 2) (e p 2 - r ^ 2 / 2 - (c + s)) :=
      ⟨hτt₀.le, by linarith⟩
    have htarget : t - (c + s) ∈ Icc (δ / 2) (e p 2 - r ^ 2 / 2 - (c + s)) := by
      constructor <;> linarith [ht.1, ht.2,
        min_le_right δ (e p 2 - r ^ 2 / 2 - (c + s))]
    have hh := hPC (t - (c + s)) htime
    dsimp only at hCcap
    rw [hCcap t₀ href, hCcap (t - (c + s)) htarget,
      show c + s + (t - (c + s)) = t by ring] at hh
    exact hh
  obtain ⟨εjoin, hεjoin, hεjoinle, _, F, hF, hFi, hFQ, _, hFdisk,
      D₀, hD₀, _, _, _, _, H, hH, hHi, hH₀, hHlo, hHhi,
      D, hD, _, hDlo, hDhi, hregion, hinter, hDlower⟩ :=
    exists_diffeomorph_heightCapRegion_lower_family_of_image_sphere_eq
      (L ∘ e) G Q hG hGi hQ hQi A hA
      (by linarith : c + s + δ / 2 ≤ c + s + t₀ - djoin)
      (by linarith [min_le_right δ (e p 2 - r ^ 2 / 2 - (c + s))] :
        c + s + t₀ + djoin < e p 2 - r ^ 2 / 2)
      hdjoin rfl hr hrR hrR₀.le hrτcap.le hδcap hmodel hnormal' hcontact hQ₀ hcircle
  have hεsub : Ioo (t₀ - εjoin) (t₀ + εjoin) ⊆
      Ioo (δ / 2) (min δ (e p 2 - r ^ 2 / 2 - (c + s))) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hHdisk (t : ℝ) (ht : c + s + t₀ - εjoin < t) :
      H t '' closedBall 0 r = G t '' closedBall 0 r := by
    rw [hHhi t ht, hFdisk]
  have hHsphere (t : ℝ) (ht : c + s + t₀ - εjoin < t) :
      H t '' sphere 0 r = G t '' sphere 0 r := by
    have hfrontH := (H t).toHomeomorph.image_frontier (closedBall (0 : Plane) r)
    have hfrontG := (G t).toHomeomorph.image_frontier (closedBall (0 : Plane) r)
    change H t '' frontier (closedBall (0 : Plane) r) = frontier (H t '' closedBall 0 r) at hfrontH
    change G t '' frontier (closedBall (0 : Plane) r) = frontier (G t '' closedBall 0 r) at hfrontG
    rw [frontier_closedBall (0 : Plane) hr.ne'] at hfrontH hfrontG
    exact hfrontH.trans ((congrArg frontier (hHdisk t ht)).trans hfrontG.symm)
  obtain ⟨T, hT, hTi, hTheight, hTbase, hTtrack, hTsets, hTwhole⟩ :=
    Diffeomorph.exists_diffeomorph_straightening_family H hH hHi (c + s + t₀)
  rw [hH₀] at hT hTi hTtrack hTsets hTwhole
  have hwhole :
      ((G (c + s + t₀) '' closedBall 0 r) ×ˢ Icc (c + s + t₀) (e p 2 - r ^ 2 / 2)) ∩
          range (T ∘ L ∘ e) =
        (G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + t₀) (e p 2 - r ^ 2 / 2) := by
    apply hTwhole (L ∘ e) (closedBall 0 r) (sphere 0 r)
    intro t ht
    have htime : c + s + t₀ - εjoin < t := by linarith [ht.1]
    rw [hHdisk t htime, hHsphere t htime]
    exact hcontact t ⟨by linarith [ht.1], ht.2⟩
  let d := min d₀ (t₀ + εjoin / 2)
  have ht₀d : t₀ < d := lt_min ht₀d₀ (by linarith)
  have hdd₀ : d ≤ d₀ := min_le_left _ _
  have hdδ : d < δ := hdd₀.trans_lt hd₀δ
  have hdjoin : d < t₀ + εjoin := (min_le_right _ _).trans_lt (by linarith)
  have hdsub : Icc (-d) d ⊆ Icc (-d₀) d₀ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hTlower (t : ℝ) (ht : t < t₀ + εjoin) (y : Plane) :
      T (y, c + s + t) = ((Ξ 1 (t, y)).2, c + s + t) := by
    have htrack := hTtrack (c + s + t) ((G (c + s + t₀)).symm ((P t).symm y))
    rw [hHlo (c + s + t) (by linarith)] at htrack
    change T (P (c + s + t - (c + s))
      (G (c + s + t₀) ((G (c + s + t₀)).symm ((P t).symm y))), c + s + t) =
      (G (c + s + t₀) ((G (c + s + t₀)).symm ((P t).symm y)), c + s + t) at htrack
    simp only [add_sub_cancel_left, (G (c + s + t₀)).apply_symm_apply,
      (P t).apply_symm_apply] at htrack
    rwa [hPiformula] at htrack
  have hTarc (t : ℝ) (ht : t ∈ Icc (-d) d) (u : unitInterval) :
      T (γ (t, u), c + s + t) = (γ (t₀, u), c + s + t) := by
    rw [hTlower t (ht.2.trans_lt hdjoin), ← hPiformula, hParc t (hdsub ht)]
  let V := Vcut ∩ {q : ℝ × (ℝ × ℝ) | q.1 < t₀ + εjoin}
  have hV : IsOpen V := hVcut.inter (isOpen_lt continuous_fst continuous_const)
  let Kfilled : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧
    s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
        s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)}
  have hKfilledV : Kfilled ⊆ V := by
    intro q hq
    exact ⟨hKcut ⟨⟨hq.1.1, hq.1.2.trans hdd₀⟩, hq.2⟩, hq.1.2.trans_lt hdjoin⟩
  have hrawFilled : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ Kfilled := by
    intro q hq
    refine ⟨hq.1, hq.2.1, hq.2.2.ge, ?_⟩
    rw [hq.2.2]
    by_cases ht : q.1 ≤ t₀
    · exact le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr (hθ01 _).2) (sub_nonneg.mpr ht))
    · rw [hθ1 q.1 q.2.1 (Or.inl (by linarith))]
      simp
  have hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V :=
    hrawFilled.trans hKfilledV
  have hVreg (q : ℝ × (ℝ × ℝ)) (hq : q ∈ V) :
      θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
        (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
          0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (t₀ - q.1)) /
            q.2.2 ^ 2) := by
    simpa only [one_mul] using hVregular 1 ⟨by norm_num, le_rfl⟩ q hq.1
  have hTmodel (q : ℝ × (ℝ × ℝ)) (hq : q ∈ V) :
      T (B q.2, c + s + q.1) =
        (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1) := by
    rw [hTlower q.1 hq.2, hΞcut 1 ⟨by norm_num, le_rfl⟩ q hq.1, one_mul]
  let K : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧
    (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}
  have hKU : Prod.snd '' K ⊆ U := by
    rintro z ⟨q, hq, rfl⟩
    exact hrawU q.1 ⟨hq.1.1, hq.1.2.trans hdd₀⟩ q.2 hq.2.1 hq.2.2
  have hfilledRect (q : ℝ × (ℝ × ℝ)) (hq : q ∈ Kfilled) :
      q.2 ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ := by
    have henergy : (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤ s + d := by
      have hfirst := mul_nonneg (hθ01 (q.1, q.2.1)).1 (sub_nonneg.mpr hq.1.2)
      have hsecond := mul_nonneg (sub_nonneg.mpr (hθ01 (q.1, q.2.1)).2)
        (sub_nonneg.mpr ht₀d.le)
      nlinarith only [hfirst, hsecond, hq.2.2.2]
    exact mem_rectangle_of_saddle_band_height_le (abs_lt.mp (hq.2.1.trans_lt hh1))
      henergy (hmodelRect d ⟨by linarith, hdδ.le⟩ 1 (by norm_num) q.2.1
        (abs_le.mp hq.2.1))
  have henergyContinuous : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2) := by fun_prop
  have hupperContinuous : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)) := by fun_prop
  have hfilledClosed : IsClosed Kfilled :=
    (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_le (continuous_snd.fst.abs) continuous_const).inter
        ((isClosed_le (continuous_const.add continuous_fst) henergyContinuous).inter
          (isClosed_le henergyContinuous hupperContinuous)))
  have hfilledCompact : IsCompact Kfilled := by
    apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
      hfilledClosed (show Kfilled ⊆ Icc (-εcut) d ×ˢ (Icc (-h) h ×ˢ Icc (-ρ) ρ) from ?_)
    exact fun q hq => ⟨hq.1, hfilledRect q hq⟩
  let Vphys : Set (Plane × ℝ) := {p | (p.2 - (c + s), B.symm p.1) ∈ V}
  have hVphys : IsOpen Vphys := hV.preimage
    ((continuous_snd.sub continuous_const).prodMk (B.symm.continuous.comp continuous_fst))
  have hVphysEq : Vphys =
      (fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' V := by
    ext y
    constructor
    · intro hy
      refine ⟨(y.2 - (c + s), B.symm y.1), hy, ?_⟩
      simp only [B.apply_symm_apply]
      congr 1
      ring
    · rintro ⟨q, hq, rfl⟩
      simpa only [Vphys, mem_ofPred_eq, add_sub_cancel_left, B.symm_apply_apply] using hq
  let Wbox : Set (Plane × ℝ) := {p |
    (B.symm p.1).1 ∈ Ioo (-(2 * h)) (2 * h) ∧
      (B.symm p.1).2 ∈ Ioo (-(2 * ρ)) (2 * ρ) ∧
        p.2 - (c + s) ∈ Ioo (-(2 * δ)) (2 * δ)}
  have hWbox : IsOpen Wbox :=
    (isOpen_Ioo.preimage (B.symm.continuous.comp continuous_fst).fst).inter
      ((isOpen_Ioo.preimage (B.symm.continuous.comp continuous_fst).snd).inter
        (isOpen_Ioo.preimage (continuous_snd.sub continuous_const)))
  have hWboxGraph : Wbox ∩ range (L ∘ e) = Wbox ∩ {p |
      (1 - (B.symm p.1).1 ^ 2) * ((B.symm p.1).2 ^ 2 + 2 * s) / 2 =
        s + (p.2 - (c + s))} := by
    ext y
    have heq (hy : y ∈ Wbox) : y ∈ range (L ∘ e) ↔
        (1 - (B.symm y.1).1 ^ 2) * ((B.symm y.1).2 ^ 2 + 2 * s) / 2 =
          s + (y.2 - (c + s)) := by
      have hx := hrectangleLevel (B.symm y.1)
        ⟨⟨hy.1.1.le, hy.1.2.le⟩, ⟨hy.2.1.1.le, hy.2.1.2.le⟩⟩
        (y.2 - (c + s)) ⟨hy.2.2.1.le, hy.2.2.2.le⟩
      rwa [B.apply_symm_apply, show c + s + (y.2 - (c + s)) = y.2 by ring] at hx
    exact and_congr_right heq
  have hfilledPhysV :
      (fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' Kfilled ⊆ Vphys := by
    rw [hVphysEq]
    exact image_mono hKfilledV
  have hfilledPhysW :
      (fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' Kfilled ⊆ Wbox := by
    rintro _ ⟨q, hq, rfl⟩
    have hrect := hfilledRect q hq
    change (B.symm (B q.2)).1 ∈ Ioo (-(2 * h)) (2 * h) ∧
      (B.symm (B q.2)).2 ∈ Ioo (-(2 * ρ)) (2 * ρ) ∧
        c + s + q.1 - (c + s) ∈ Ioo (-(2 * δ)) (2 * δ)
    rw [B.symm_apply_apply, add_sub_cancel_left]
    exact ⟨⟨by linarith [hrect.1.1], by linarith [hrect.1.2]⟩,
      ⟨by linarith [hrect.2.1], by linarith [hrect.2.2]⟩,
      ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩⟩
  have hTmodelPhys (y : Plane × ℝ) (hy : y ∈ Vphys) :
      T y = (B (saddleBandCurve (B.symm y.1)
        (θ (y.2 - (c + s), (B.symm y.1).1) * (t₀ - (y.2 - (c + s))))), y.2) := by
    have hx := hTmodel (y.2 - (c + s), B.symm y.1) hy
    simpa only [B.apply_symm_apply,
      show c + s + (y.2 - (c + s)) = y.2 by ring] using hx
  obtain ⟨Z, _, hZ, hZTphys, _, hZeq, ρclear, hρclear, hρfilledZ⟩ :=
    DifferentialGeometry.Topology.Morse.exists_cthickening_inter_range_comp_eq_saddle_band_time_change
      B.toEquiv T.toHomeomorph hVphys hWbox hWboxGraph hTmodelPhys
      (ψ := fun q => θ q * (t₀ - q.1))
      (fun y hy => by
        rcases hVreg (y.2 - (c + s), B.symm y.1) hy with hz | hr
        · exact Or.inl hz
        · exact Or.inr ⟨hr.1, hr.2.1, hr.2.2.le⟩)
      (hfilledCompact.image (by fun_prop)) hfilledPhysV hfilledPhysW
  have hZT : Z ⊆ T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' V) := by
    rwa [hVphysEq] at hZTphys
  have hρZ : cthickening ρclear
      (T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' K)) ⊆ Z :=
    (cthickening_subset_of_subset _ (image_mono (image_mono hrawFilled))).trans hρfilledZ
  obtain ⟨O, hO, g, hg, hgt, Wgraph, hWgraph, hWZ, hWO, hgraphcover, hgrapheq⟩ :=
    exists_isOpen_inter_eq_graph_of_saddle_band_cutoff B.toHomeomorph κ.contDiff
      ht₀pos (show -εcut < t₀ / 2 by linarith) hθformula hZ hZeq
  have hactive : T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) ''
      {q | q.1 ∈ Ioo (-εcut) (t₀ / 2) ∧ |q.2.1| < h / 2 ∧
        (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}) ⊆ Wgraph := by
    rintro y ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hqK : q ∈ K :=
      ⟨⟨hq.1.1.le, by linarith [hq.1.2]⟩, by linarith [hq.2.1], hq.2.2⟩
    have hqZ : T (B q.2, c + s + q.1) ∈ Z :=
      hρZ (self_subset_cthickening _ ⟨_, ⟨q, hqK, rfl⟩, rfl⟩)
    have hsourceq : L (e (β q.2)) = (B q.2, c + s + q.1) := by
      rw [hgraph q.2 (hKU ⟨q, hqK, rfl⟩), hq.2.2]
      congr 1
      ring
    apply hgraphcover
    refine ⟨⟨hqZ, β q.2, congrArg T hsourceq⟩, ?_, ?_⟩
    · change 0 < κ (B.symm (T (B q.2, c + s + q.1)).1).1
      rw [hTmodel q (hKV hqK), B.symm_apply_apply]
      change 0 < κ q.2.1
      apply κ.pos_of_mem_ball
      simpa only [mem_ball, Real.dist_eq, sub_zero, hκout] using hq.2.1
    · rw [hTheight]
      simpa only [add_sub_cancel_left] using hq.1
  exact ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
    η, hη, Φ, hΦ, hΦi, hΦ0, hplanefamily,
    (fun t ht => ⟨(hslices t ht).1, (hslices t ht).2.1⟩), hcoverage,
    r, hr, hab, A, hA, hcap, G, hG, hGi, hCcap, hcontact,
    t₀, hτt₀, ht₀δ, ht₀b, d, ht₀d, hdδ, εcut, hεcut, hεcutt, hεcuth,
    θ, hθ, hθ01, hθ0, hθ1, hθzero, κ, hκin, hκout, hθformula, εjoin, hεjoin, hεsub,
    H, hH, hHi, hH₀, hHdisk, D, hD, hDlo, hDhi, hregion, hinter,
    T, hT, hTheight, hTbase, hTarc, hwhole, V, hV, hKV, hVreg, hTmodel,
    (fun t ht => hrawU t ⟨ht.1, ht.2.trans hdd₀⟩), Z, hZ, hZT, hZeq,
    ρclear, hρclear, hρZ, hρfilledZ, ρ, hρ, hrectangle, hmodelRect, hclear t₀ ⟨hτt₀, ht₀⟩,
    O, hO, g, hg, hgt, Wgraph, hWgraph, hWZ, hWO, hactive, hgrapheq, hcontactRect⟩

private theorem isCompact_paraboloid_above (a m : ℝ) :
    IsCompact {z : Plane × ℝ | a ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2} := by
  have hc : Continuous (fun y : Plane => m - ‖y‖ ^ 2 / 2) :=
    continuous_const.sub ((continuous_norm.pow 2).div_const 2)
  have hclosed : IsClosed {z : Plane × ℝ | a ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2} :=
    (isClosed_le continuous_const continuous_snd).inter
      (isClosed_eq continuous_snd (hc.comp continuous_fst))
  apply IsCompact.of_isClosed_subset
    ((isCompact_closedBall (0 : Plane) (Real.sqrt (2 * (m - a)))).prod
      (isCompact_Icc (a := a) (b := m))) hclosed
  intro z hz
  exact ⟨mem_closedBall_zero_iff.mpr
    (Real.le_sqrt_of_sq_le (by linarith only [hz.1, hz.2])), hz.1,
    by linarith only [hz.2, sq_nonneg ‖z.1‖]⟩

private theorem exists_isOpen_graph_of_source_neck_and_cap
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) {ℓ a m : ℝ}
    {X : Set ((ℝ × ℝ) × ℝ)} {N U S Z : Set (Plane × ℝ)}
    (hcompact : IsCompact (((fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' X) ∪ N))
    (hactual : (fun q : Plane × ℝ => (q.1, ℓ + q.2)) ''
      (((fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' X) ∪ N) ⊆ S)
    (hcap : Q '' U = {q : Plane × ℝ | a ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})
    (hproj : InjOn (fun q : Plane × ℝ => (Q q).1)
      (((fun q : Plane × ℝ => (q.1, ℓ + q.2)) ''
        (((fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' X) ∪ N)) ∪ U))
    (hsource : ∃ O : Set Plane, IsOpen O ∧ ∃ g : Plane → ℝ, ContDiffOn ℝ ∞ g O ∧
      ∃ W : Set (Plane × ℝ), IsOpen W ∧
        Q '' ((fun q : (ℝ × ℝ) × ℝ => (B q.1, ℓ + q.2)) '' X) ⊆ W ∧
          W ⊆ Q '' Z ∧ W ⊆ {q | q.1 ∈ O} ∧
          W ∩ Q '' S = W ∩ {q | q.2 = g q.1})
    (hneck : ∃ W : Set (Plane × ℝ), IsOpen W ∧
      Q '' ((fun q : Plane × ℝ => (q.1, ℓ + q.2)) '' N) ⊆ W ∧
      W ∩ Q '' S = W ∩ {q | q.2 = m - ‖q.1‖ ^ 2 / 2})
    (hupper : ∃ W : Set (Plane × ℝ), IsOpen W ∧ Q '' U ⊆ W ∧
      W ∩ Q '' S = W ∩ {q | q.2 = m - ‖q.1‖ ^ 2 / 2}) :
    IsCompact (((fun q : Plane × ℝ => (q.1, ℓ + q.2)) ''
      (((fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' X) ∪ N)) ∪ U) ∧
    ∃ O : Set Plane, IsOpen O ∧ ∃ g : Plane → ℝ, ContDiffOn ℝ ∞ g O ∧
      ∃ W : Set (Plane × ℝ), IsOpen W ∧
        Q '' (((fun q : Plane × ℝ => (q.1, ℓ + q.2)) ''
          (((fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' X) ∪ N)) ∪ U) ⊆ W ∩ Q '' S ∧
        W ⊆ {q | q.1 ∈ O} ∧ W ∩ Q '' S = W ∩ {q | q.2 = g q.1} := by
  obtain ⟨Osrc, hOsrc, gsrc, hgsrc, Wsrc, hWsrc, hsourceX, _, hWsrcO, hsourceEq⟩ := hsource
  obtain ⟨Wneck, hWneck, hneckW, hneckEq⟩ := hneck
  obtain ⟨Wcap, hWcap, hcapW, hcapEq⟩ := hupper
  let A := (fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' X
  have hsourceW : Q '' ((fun q : Plane × ℝ => (q.1, ℓ + q.2)) '' A) ⊆ Wsrc := by
    rintro _ ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    exact hsourceX ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  let K := ((fun q : Plane × ℝ => (q.1, ℓ + q.2)) '' (A ∪ N)) ∪ U
  have hKcompact : IsCompact (Q '' K) := by
    rw [show K = _ ∪ U from rfl, image_union]
    exact ((hcompact.image (continuous_fst.prodMk
      (continuous_const.add continuous_snd))).image Q.continuous).union
        (hcap.symm ▸ isCompact_paraboloid_above a m)
  have hKrange : Q '' K ⊆ Q '' S := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact mem_image_of_mem Q (hactual hz)
    · exact (hcapEq.symm.subset ⟨hcapW (mem_image_of_mem Q hz),
        (hcap.subset (mem_image_of_mem Q hz)).2⟩).2
  have hKinj : InjOn (Prod.fst : Plane × ℝ → Plane) (Q '' K) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ heq
    exact congrArg Q (hproj hz hw heq)
  have hqpar : ContDiff ℝ ∞ (fun y : Plane => m - ‖y‖ ^ 2 / 2) :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).div_const 2)
  have hlocal (z : Plane × ℝ) (hz : z ∈ Q '' K) :
      ∃ O : Set Plane, IsOpen O ∧ ∃ g : Plane → ℝ, ContDiffOn ℝ ∞ g O ∧
        ∃ W : Set (Plane × ℝ), IsOpen W ∧ z ∈ W ∧ W ⊆ O ×ˢ univ ∧
          W ∩ Q '' S = W ∩ {q | q.2 = g q.1} := by
    obtain ⟨w, hw, rfl⟩ := hz
    rcases hw with ⟨w, hw, rfl⟩ | hw
    · rcases hw with hw | hw
      · exact ⟨Osrc, hOsrc, gsrc, hgsrc, Wsrc, hWsrc,
          hsourceW ⟨_, ⟨w, hw, rfl⟩, rfl⟩, fun p hp => ⟨hWsrcO hp, mem_univ _⟩, hsourceEq⟩
      · exact ⟨univ, isOpen_univ, _, hqpar.contDiffOn, Wneck, hWneck,
          hneckW ⟨_, ⟨w, hw, rfl⟩, rfl⟩, fun p _ => ⟨mem_univ _, mem_univ _⟩, hneckEq⟩
    · exact ⟨univ, isOpen_univ, _, hqpar.contDiffOn, Wcap, hWcap,
        hcapW (mem_image_of_mem Q hw), fun p _ => ⟨mem_univ _, mem_univ _⟩, hcapEq⟩
  obtain ⟨O, hO, g, hg, W, hW, hKW, hWO, hWeq⟩ :=
    exists_isOpen_contDiffOn_graph_of_isCompact hKcompact hKrange hKinj hlocal
  exact ⟨Q.toHomeomorph.isCompact_image.mp hKcompact,
    O, hO, g, hg, W, hW, fun z hz => ⟨hKW hz, hKrange hz⟩,
    fun z hz => (hWO hz).1, hWeq⟩

private theorem disjoint_cylinder_and_quadratic_cap_interior
    (D T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (G : Plane ≃ₘ[ℝ] Plane)
    {a τ b m r : ℝ} {S R : Set (Plane × ℝ)}
    (hτb : τ ≤ b) (hr : 0 < r)
    (hregion : D '' {z : Plane × ℝ | τ ≤ z.2 ∧ z.2 ≤ m - ‖z.1‖ ^ 2 / 2} = R)
    (hinter : R ∩ S = D '' {z : Plane × ℝ | τ ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2})
    (hwhole : ((G '' closedBall 0 r) ×ˢ Icc τ b) ∩ T '' S =
      (G '' sphere 0 r) ×ˢ Icc τ b)
    (hlower : Disjoint (T '' S) (interior (G '' closedBall 0 r) ×ˢ Icc a τ)) :
    Disjoint (T '' S) (interior (G '' closedBall 0 r) ×ˢ Icc a b) ∧
      Disjoint (T '' S)
        ((D.trans T) '' {z : Plane × ℝ | b ≤ z.2 ∧ z.2 < m - ‖z.1‖ ^ 2 / 2}) := by
  constructor
  · apply disjoint_left.mpr
    rintro q hqS ⟨hqD, hqt⟩
    by_cases ht : q.2 ≤ τ
    · exact disjoint_left.mp hlower hqS ⟨hqD, hqt.1, ht⟩
    · have hqC : q.1 ∈ G '' sphere 0 r :=
        (hwhole.subset ⟨⟨interior_subset hqD, (lt_of_not_ge ht).le, hqt.2⟩, hqS⟩).1
      have hfront : q.1 ∈ frontier (G '' closedBall 0 r) := by
        change q.1 ∈ frontier (G.toHomeomorph '' closedBall 0 r)
        rw [← G.toHomeomorph.image_frontier, frontier_closedBall (0 : Plane) hr.ne']
        exact hqC
      exact disjoint_left.mp disjoint_interior_frontier hqD hfront
  · apply disjoint_left.mpr
    rintro _ hqS ⟨z, hz, rfl⟩
    obtain ⟨y, hy, heq⟩ := hqS
    have hyz : y = D z := T.injective heq
    rw [hyz] at hy
    have hzR : D z ∈ R := hregion.subset ⟨z, ⟨hτb.trans hz.1, hz.2.le⟩, rfl⟩
    obtain ⟨w, hw, heq⟩ := hinter.subset ⟨hzR, hy⟩
    have hwz := D.injective heq
    subst w
    exact hz.2.ne hw.2

private theorem disjoint_vertical_trace_of_source_neck_cap
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (G : Plane ≃ₘ[ℝ] Plane)
    (Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    {ℓ ε j τ b m r α μ : ℝ} {X : Set ((ℝ × ℝ) × ℝ)}
    {N : Set Plane} {U S : Set (Plane × ℝ)}
    (hjτ : j ≤ τ) (hτb : ℓ + τ ≤ b)
    (htime : ∀ p ∈ X, p.2 ≤ j) (hN : N ⊆ G '' sphere 0 r)
    (hQlow : ∀ t ≤ ℓ + τ, ∀ y, Q (y, t) =
      ((α * Real.exp (-μ * t)) • G.symm y, ψ t))
    (hQcylinder : Q '' ((G '' sphere 0 r) ×ˢ Iic b) ⊆
      {q : Plane × ℝ | q.2 = m - ‖q.1‖ ^ 2 / 2})
    (hQU : Q '' U ⊆ {q : Plane × ℝ | q.2 = m - ‖q.1‖ ^ 2 / 2})
    (hsource : ∀ p ∈ X, ∀ t ∈ Ico (-ε / 2) p.2,
      (G (Real.exp (μ * (t - p.2)) • G.symm (B p.1)), ℓ + t) ∉ S)
    (hcap : ∀ q : Plane × ℝ, (Q q).2 = m - ‖(Q q).1‖ ^ 2 / 2 →
      ∀ t ∈ Ico (ℓ - ε / 2) q.2, Q.symm ((Q q).1, ψ t) ∉ S) :
    ∀ q ∈ ((fun p : Plane × ℝ => (p.1, ℓ + p.2)) ''
      (((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' X) ∪ (N ×ˢ Icc (-ε / 2) j))) ∪ U,
      ∀ t ∈ Ico (ℓ - ε / 2) q.2, Q.symm ((Q q).1, ψ t) ∉ S := by
  intro q hq t ht
  rcases hq with ⟨v, hv, rfl⟩ | hq
  · rcases hv with ⟨w, hw, rfl⟩ | ⟨hvN, hvt⟩
    · rw [Diffeomorph.symm_apply_fst_height_of_exponential_formula G Q ψ hQlow
        (s := ℓ + w.2) (by linarith only [htime w hw, hjτ])
        (t := t) (by dsimp only at ht; linarith only [ht.2, htime w hw, hjτ]) (B w.1)]
      have hrawt : t - ℓ ∈ Ico (-ε / 2) w.2 := by
        constructor <;> dsimp only at ht <;> linarith only [ht.1, ht.2]
      have hnot := hsource w hw (t - ℓ) hrawt
      rw [show t - ℓ - w.2 = t - (ℓ + w.2) by ring,
        show ℓ + (t - ℓ) = t by ring] at hnot
      exact hnot
    · apply hcap _ _ t ht
      exact hQcylinder ⟨(v.1, ℓ + v.2), ⟨hN hvN,
        by change ℓ + v.2 ≤ b; linarith only [hvt.2, hjτ, hτb]⟩, rfl⟩
  · exact hcap q (hQU (mem_image_of_mem Q hq)) t ht

private theorem exists_isOpen_graph_reference_neck
    {e : SphereTwo → Plane × ℝ} (he : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, Plane × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (G : Plane ≃ₘ[ℝ] Plane)
    (Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (ψ : ℝ ≃ ℝ)
    {s h ε τ σ ℓ d j b m r : ℝ}
    (hs : 0 ≤ s) (hh : 0 < h) (hh1 : h < 1) (hε : 0 < ε) (hτ : 0 < τ)
    (hτd : τ ≤ d) (hj : j < τ) (hbaseb : ℓ + τ ≤ b)
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    (hwall : (G '' sphere 0 r \ B ''
      (saddleBandLevelCurve s τ σ '' Ioo (-(h / 2)) (h / 2))) ×ˢ
        Icc (ℓ - ε) (ℓ + d) ⊆ range e) :
    ∃ W : Set (Plane × ℝ), IsOpen W ∧
      Q '' ((fun q : Plane × ℝ => (q.1, ℓ + q.2)) ''
        ((G '' sphere 0 r \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ
          Icc (-ε / 2) j)) ⊆ W ∧
      W ∩ Q '' range e = W ∩ {q | q.2 = m - ‖q.1‖ ^ 2 / 2} := by
  let Ainner : Set Plane := B '' (saddleBandLevelCurve s τ σ '' Icc (-(h / 2)) (h / 2))
  have hAinner : IsClosed Ainner := by
    apply IsCompact.isClosed
    apply IsCompact.image _ B.continuous
    apply isCompact_Icc.image_of_continuousOn
    apply (contDiffOn_saddleBandLevelCurve hs hτ σ).continuousOn.mono
    intro u hu
    exact ⟨by linarith only [hu.1, hh1], by linarith only [hu.2, hh1]⟩
  have hneckRange : (G '' sphere 0 r \ Ainner) ×ˢ Ioo (ℓ - ε) (ℓ + τ) ⊆ range e := by
    rintro ⟨y, t⟩ ⟨⟨hy, hyA⟩, ht⟩
    apply hwall
    refine ⟨⟨hy, ?_⟩, ht.1.le, ?_⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, heq⟩
      exact hyA ⟨_, ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩, heq⟩
    · linarith only [ht.2, hτd]
  obtain ⟨W, hW, hneckW, hneckEq⟩ :=
    exists_isOpen_inter_range_eq_paraboloid_of_cylinder he (by simp) Q G.toEquiv ψ
      (a := ℓ - ε) (d := ℓ + τ) (b := b) (m := m)
      hbaseb hbm hr hrsq hψ hψb hQfull hAinner hneckRange
  refine ⟨W, hW, ?_, by simpa only [range_comp] using hneckEq⟩
  rintro _ ⟨_, ⟨w, ⟨⟨hwC, hwA⟩, hwt⟩, rfl⟩, rfl⟩
  apply hneckW
  refine ⟨(w.1, ℓ + w.2), ⟨⟨hwC, ?_⟩, ?_, ?_⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, heq⟩
    exact hwA ⟨_, ⟨u, ⟨by linarith only [hu.1, hh],
      by linarith only [hu.2, hh]⟩, rfl⟩, heq⟩
  · dsimp only
    linarith only [hwt.1, hε]
  · dsimp only
    linarith only [hwt.2, hj]

private theorem exists_isOpen_graph_cutoff_source_neck_cap {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (D T A Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ))
    (ψ : ℝ ≃ₘ[ℝ] ℝ)
    (G : ℝ → Plane ≃ₘ[ℝ] Plane)
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)}
    {c s h t₀ δ d ε σ r b m : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1) (ht₀ : 0 < t₀)
    (ht₀d : t₀ < d) (hdδ : d < δ) (hε : 0 < ε)
    (hσ : σ ^ 2 = 1) (ht₀b : c + s + t₀ ≤ b)
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m ((G (c + s + t₀)).symm y) (ψ t), ψ t))
    (hQcap : Q '' ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}) =
      {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})
    (Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (η : unitInterval → SphereTwo)
    (hslices : ∀ t ∈ Icc (-δ) δ, ∀ u, e (Φ (t - δ / 2) (η u)) 2 = c + s + t)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    {θ : ℝ × ℝ → ℝ}
    (hθ1 : ∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1)
    {V : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1))
    (hrawU : ∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U) :
    let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
    let γ := fun q : ℝ × unitInterval => (L (e (Φ (q.1 - δ / 2) (η q.2)))).1
    (∀ t ∈ Icc (-d) d, ∀ u, T (γ (t, u), c + s + t) = (γ (t₀, u), c + s + t)) →
    G (c + s + t₀) '' Metric.sphere 0 r =
      B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ∪ range (fun u => γ (t₀, u)) →
    ((G (c + s + t₀) '' Metric.closedBall 0 r) ×ˢ Icc (c + s + t₀) b) ∩
      range (T ∘ L ∘ e) =
        (G (c + s + t₀) '' Metric.sphere 0 r) ×ˢ Icc (c + s + t₀) b →
    heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∩ range (L ∘ e) =
      D '' {q | c + s + t₀ ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} →
    ∀ j ∈ Ioo (t₀ / 2) t₀,
      ∀ (X : Set ((ℝ × ℝ) × ℝ)) (Z : Set (Plane × ℝ)),
      let C := G (c + s + t₀) '' sphere 0 r \ B ''
        (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))
      let S := ((fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' X) ∪ C ×ˢ Icc (-ε / 2) j
      let Ucap := ((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
        ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})
      let K := ((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪ Ucap
      IsCompact S → ((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S ⊆ range (T ∘ L ∘ e)) →
      (∃ O : Set Plane, IsOpen O ∧ ∃ g : Plane → ℝ, ContDiffOn ℝ ∞ g O ∧
        ∃ W : Set (Plane × ℝ), IsOpen W ∧
          Q '' ((fun q : (ℝ × ℝ) × ℝ => (B q.1, c + s + q.2)) '' X) ⊆ W ∧
          W ⊆ Q '' Z ∧ W ⊆ {q | q.1 ∈ O} ∧
          W ∩ Q '' range (T ∘ L ∘ e) = W ∩ {q | q.2 = g q.1}) →
      ((G (c + s + t₀) '' sphere 0 r \ B ''
        (saddleBandLevelCurve s t₀ σ '' Ioo (-(h / 2)) (h / 2))) ×ˢ
        Icc (c + s - ε) (c + s + d) ⊆ range (T ∘ L ∘ e)) →
      InjOn (fun q : Plane × ℝ => (Q q).1) K →
      IsCompact K ∧ ∃ O : Set Plane, IsOpen O ∧ ∃ g : Plane → ℝ, ContDiffOn ℝ ∞ g O ∧
        ∃ W : Set (Plane × ℝ), IsOpen W ∧
          Q '' K ⊆ W ∩ Q '' range (T ∘ L ∘ e) ∧ W ⊆ {q | q.1 ∈ O} ∧
          W ∩ Q '' range (T ∘ L ∘ e) = W ∩ {q | q.2 = g q.1} := by
  intro L γ hTarc hcircleRef hwhole hinter j hj X Z C S Ucap K hcompact hactual hsource hwall hproj
  have heT := (he.continuousLinearEquiv_comp L).diffeomorph_comp T
  have hjb : c + s + j ≤ b := by linarith only [hj.2, ht₀b]
  have hcap : Q '' Ucap = {q : Plane × ℝ | ψ (c + s + j) ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} :=
    Diffeomorph.image_reference_cylinder_union_cap Q (G (c + s + t₀)).toEquiv ψ.toEquiv
      hbm hr hrsq hjb hψ hψb hQfull hQcap
  apply exists_isOpen_graph_of_source_neck_and_cap B Q hcompact hactual hcap hproj hsource
    (exists_isOpen_graph_reference_neck heT B (G (c + s + t₀)) Q ψ.toEquiv
      hs.le hh hh1 hε ht₀ ht₀d.le hj.2 ht₀b hbm hr hrsq hψ hψb hQfull hwall)
  simpa only [range_comp] using
    exists_isOpen_graph_upper_saddle_cap he B D T A Q ψ G
      hs hh1 ht₀ ht₀d hdδ hε hσ ht₀b hbm hr hrsq hψ hψb hQfull hQcap
      Φ η hslices hgraph hθ1 hKV hTmodel hrawU hTarc hcircleRef hwhole hinter j hj

private theorem saddle_cutoff_wedge_mem_and_not_mem
    {F : Type*} (B : (ℝ × ℝ) ≃ F) {s h τ ε d ℓ : ℝ} {θ : ℝ × ℝ → ℝ}
    (hs : 0 < s) (hh : h < 1) (hτ : 0 < τ) (hτd : τ ≤ d)
    (hε : ε < s * h ^ 2 / 16) (hθ01 : ∀ q, θ q ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ t u, t ≤ τ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    {Z S : Set (F × ℝ)}
    (hfilled : (fun q : ℝ × (ℝ × ℝ) =>
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (τ - q.1))), ℓ + q.1)) ''
      {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
        s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
          (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
            s + q.1 + (1 - θ (q.1, q.2.1)) * (τ - q.1)} ⊆ Z)
    (hZeq : Z ∩ S = Z ∩ {q | (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
      s + (q.2 - ℓ) + θ (q.2 - ℓ, (B.symm q.1).1) * (τ - (q.2 - ℓ))}) :
    ∀ t ∈ Icc (-ε) τ, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      s + t + θ (t, z.1) * (τ - t) ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + τ →
      (B z, ℓ + t) ∈ Z ∧
        (s + t + θ (t, z.1) * (τ - t) < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
          (B z, ℓ + t) ∉ S) := by
  intro t ht z hz hlower hupper
  have hzin := (Set.ext_iff.mp
    (image_saddle_band_cutoff_region hs hh hτ hε hθ01 hθ0 ht) z).mpr
      ⟨hz, hlower, hupper⟩
  obtain ⟨w, hw, hforward⟩ := hzin
  have hmem : (B z, ℓ + t) ∈ Z := by
    apply hfilled
    exact ⟨(t, w), ⟨⟨ht.1, ht.2.trans hτd⟩, hw⟩, Prod.ext (congrArg B hforward) rfl⟩
  refine ⟨hmem, ?_⟩
  intro hstrict hS
  have heq := (hZeq.subset ⟨hmem, hS⟩).2
  change (1 - (B.symm (B z)).1 ^ 2) * ((B.symm (B z)).2 ^ 2 + 2 * s) / 2 =
    s + (ℓ + t - ℓ) + θ (ℓ + t - ℓ, (B.symm (B z)).1) * (τ - (ℓ + t - ℓ)) at heq
  simp only [B.symm_apply_apply, add_sub_cancel_left] at heq
  exact (ne_of_gt hstrict) heq

private theorem reference_cylinder_subset_range_of_cutoff_graph
    {M ι : Type*} (e : M → Plane × ℝ) (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    (T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ))
    (β : (ℝ × ℝ) → M) (γ : ℝ × ι → M) {U : Set (ℝ × ℝ)}
    {c s h τ ε d δ σ : ℝ} {θ : ℝ × ℝ → ℝ} {C : Set Plane}
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hh1 : h < 1) (hτ : 0 ≤ τ)
    (hεh : ε < s * h ^ 2 / 16) (hεδ : ε ≤ δ) (hεd : ε ≤ d) (hdδ : d ≤ δ)
    (hσ : σ ^ 2 = 1)
    (hθ : ∀ t u, h / 2 ≤ |u| → θ (t, u) = 1)
    (hgraph : ∀ z ∈ U, e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hrawU : ∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U)
    {V : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (τ - q.1))), c + s + q.1))
    (hheight : ∀ t ∈ Icc (-δ) δ, ∀ u, (e (γ (t, u))).2 = c + s + t)
    (hTarc : ∀ t ∈ Icc (-d) d, ∀ u,
      T ((e (γ (t, u))).1, c + s + t) = ((e (γ (τ, u))).1, c + s + t))
    (hcircle : C = B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ∪
      range (fun u => (e (γ (τ, u))).1)) :
    (C \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-(h / 2)) (h / 2))) ×ˢ
      Icc (c + s - ε) (c + s + d) ⊆ range (T ∘ e) := by
  rw [range_comp]
  apply reference_cylinder_subset_image_of_saddle_cutoff B T hs hh hh1 hτ hεh hσ hθ
    (γ := fun q : ℝ × ι => (e (γ q)).1) _ _ _ _ hcircle
  · intro t ht z hzwidth hzlevel
    refine ⟨β z, ?_⟩
    rw [hgraph z (hrawU t ht z hzwidth hzlevel), hzlevel]
    congr 1
    ring
  · intro t ht z hzwidth hzlevel
    exact hTmodel (t, z) (hKV ⟨ht, hzwidth, hzlevel⟩)
  · intro t ht u
    exact ⟨γ (t, u), Prod.ext rfl (hheight t ⟨(neg_le_neg hεδ).trans ht.1, ht.2.trans hdδ⟩ u)⟩
  · intro t ht u
    exact hTarc t ⟨(neg_le_neg hεd).trans ht.1, ht.2⟩ u

private theorem exists_isOpen_inter_range_eq_reference_outer_strip
    {e : SphereTwo → Plane × ℝ} (he : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, Plane × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (G : Plane ≃ₘ[ℝ] Plane)
    {s h τ σ r a b : ℝ} (hs : 0 ≤ s) (hh : 0 < h) (hh1 : h < 1) (hτ : 0 < τ)
    (hr : 0 < r)
    (hwall : (G '' sphere 0 r \ B ''
      (saddleBandLevelCurve s τ σ '' Ioo (-(h / 2)) (h / 2))) ×ˢ Icc a b ⊆ range e) :
    ∃ W : Set (Plane × ℝ), IsOpen W ∧
      W ∩ range e = (G '' sphere 0 r \ B ''
        (saddleBandLevelCurve s τ σ '' Icc (-(3 * h / 4)) (3 * h / 4))) ×ˢ Ioo a b := by
  have houterWall :
      (G '' sphere 0 r \ B ''
        (saddleBandLevelCurve s τ σ '' Icc (-(3 * h / 4)) (3 * h / 4))) ×ˢ Ioo a b ⊆ range e := by
    rintro ⟨y, t⟩ ⟨⟨hy, hyA⟩, ht⟩
    apply hwall
    refine ⟨⟨hy, ?_⟩, ⟨ht.1.le, ht.2.le⟩⟩
    rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact hyA ⟨_, ⟨u, ⟨by linarith only [hu.1, hh], by linarith only [hu.2, hh]⟩, rfl⟩, rfl⟩
  have hinner : IsClosed
      (B '' (saddleBandLevelCurve s τ σ '' Icc (-(3 * h / 4)) (3 * h / 4))) := by
    apply IsCompact.isClosed
    apply IsCompact.image _ B.continuous
    apply isCompact_Icc.image_of_continuousOn
    apply (contDiffOn_saddleBandLevelCurve hs hτ σ).continuousOn.mono
    intro u hu
    exact ⟨by linarith only [hu.1, hh, hh1], by linarith only [hu.2, hh, hh1]⟩
  obtain ⟨W, hW, hWeq⟩ := exists_isOpen_inter_range_eq_circle_strip he G hr hinner isOpen_Ioo houterWall
  exact ⟨W, hW, hWeq⟩

private theorem disjoint_cap_interior_below_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    {p : SphereTwo} (hpmax : IsLocalMax (fun x => e x 2) p)
    (hpnotmax : ¬ IsMaxOn (fun x => e x 2) univ p)
    (T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (G : Plane ≃ₘ[ℝ] Plane)
    {r a b d : ℝ} (hbd : b ≤ d) (hbp : b < e p 2)
    (hTheight : ∀ q, (T q).2 = q.2)
    (hwhole : ((G '' closedBall 0 r) ×ˢ Icc b d) ∩
      range (T ∘ (EuclideanSpace.equivProdLast 2) ∘ e) =
        (G '' sphere 0 r) ×ˢ Icc b d)
    {N : Set (Plane × ℝ)} (hN : IsOpen N)
    (hboundary : frontier (G '' closedBall 0 r) ×ˢ Icc a b ⊆ N)
    (hcollar : N ∩ range (T ∘ (EuclideanSpace.equivProdLast 2) ∘ e) ⊆
      (interior (G '' closedBall 0 r))ᶜ ×ˢ univ) :
    Disjoint (range (T ∘ (EuclideanSpace.equivProdLast 2) ∘ e))
      (interior (G '' closedBall 0 r) ×ˢ Icc a b) := by
  let L : EuclideanThree ≃L[ℝ] (Plane × ℝ) := EuclideanSpace.equivProdLast 2
  have heT : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, Plane × ℝ) ∞ (T ∘ L ∘ e) :=
    (he.continuousLinearEquiv_comp L).diffeomorph_comp T
  have htop : Disjoint (range (T ∘ L ∘ e)) (interior (G '' closedBall 0 r) ×ˢ {b}) := by
    apply disjoint_left.mpr
    rintro q hq ⟨hqint, hqt⟩
    have hc := hwhole.subset ⟨⟨interior_subset hqint,
      by rw [mem_singleton_iff.mp hqt]; exact ⟨le_rfl, hbd⟩⟩, hq⟩
    have hfront : q.1 ∈ frontier (G '' closedBall 0 r) := by
      change q.1 ∈ frontier (G.toHomeomorph '' closedBall 0 r)
      rw [← G.toHomeomorph.image_frontier, frontier_closedBall']
      exact hc.1
    exact disjoint_left.mp disjoint_interior_frontier hqint hfront
  have hheight : (fun x => ((T ∘ L ∘ e) x).2) = (fun x => e x 2) := by
    funext x
    exact hTheight (L (e x))
  apply heT.contMDiff.continuous.disjoint_range_interior_prod_Icc_of_boundary_collar
    (isCompact_range heT.contMDiff.continuous).isClosed
    ((isCompact_closedBall 0 r).image G.continuous) htop
    (fun x _ hx => ?_) hN hboundary hcollar
  have hxheight : e x 2 ∈ Ico a b := by rwa [congrFun hheight x] at hx
  have hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  rw [hheight]
  exact not_isLocalMax_of_lt_of_one_saddle hsmooth hnd hinj hone hpmax hpnotmax
    (hxheight.2.trans hbp)

private theorem closing_arc_inter_saddle_rectangle_subset_endpoints
    {ι : Type*} (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (γ : ι → Plane)
    {s t σ h ρ : ℝ}
    (hcontact : ∀ u, B.symm (γ u) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
      B.symm (γ u) = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (γ u) = saddleBandLevelCurve s t σ h) :
    range γ ∩ B '' (Icc (-h) h ×ˢ Icc (-ρ) ρ) ⊆
      {B (saddleBandLevelCurve s t σ (-h)), B (saddleBandLevelCurve s t σ h)} := by
  rintro y ⟨⟨u, rfl⟩, z, hz, heq⟩
  have hmem : B.symm (γ u) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ := by
    rw [← heq, B.symm_apply_apply]
    exact hz
  rcases hcontact u hmem with hleft | hright
  · exact Or.inl (by simpa only [B.apply_symm_apply] using congrArg B hleft)
  · exact Or.inr (mem_singleton_iff.mpr
      (by simpa only [B.apply_symm_apply] using congrArg B hright))

private theorem saddleBandLevelCurve_subset_height_projection_of_graph
    {M : Type*} (e : M → Plane × ℝ) (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} {c s t σ h : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) (hh : h < 1) (hσ : σ ^ 2 = 1)
    (hgraph : ∀ z ∈ U, e (β z) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hU : ∀ u ∈ Icc (-h) h, saddleBandLevelCurve s t σ u ∈ U) :
    B '' (saddleBandLevelCurve s t σ '' Icc (-h) h) ⊆
      (fun x => (e x).1) '' {x | (e x).2 = c + s + t} := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have huone : u ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith only [hu.1, hh], by linarith only [hu.2, hh]⟩
  have hpoint := hgraph _ (hU u hu)
  rw [saddleBandLevelCurve_height hs ht hσ huone c] at hpoint
  exact ⟨β (saddleBandLevelCurve s t σ u), congrArg Prod.snd hpoint,
    congrArg Prod.fst hpoint⟩

private abbrev saddleCutoffHalfBand (s h v₀ σ εcut j : ℝ) : Set (ℝ × ℝ) :=
  ({z : ℝ × ℝ | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
  -εcut / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
  (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j})

private noncomputable abbrev saddleCutoffModelMap (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    (T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (c s : ℝ) : (ℝ × ℝ) → (ℝ × ℝ) × ℝ :=
  (fun z : ℝ × ℝ =>
  (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
    (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))

private noncomputable abbrev saddleCutoffSource (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    (T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (G : ℝ → Plane ≃ₘ[ℝ] Plane)
    (c s t₀ r h v₀ σ εcut j : ℝ) : Set (Plane × ℝ) :=
  (((fun q : (ℝ × ℝ) × ℝ => (B q.1, q.2)) '' ((saddleCutoffModelMap B T c s) '' (saddleCutoffHalfBand s h v₀ σ εcut j))) ∪
  (G (c + s + t₀) '' sphere 0 r \ B ''
    (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc (-εcut / 2) j)

private noncomputable abbrev saddleCutoffUpperCap (D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ))
    (T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (G : ℝ → Plane ≃ₘ[ℝ] Plane)
    (c s t₀ r j b m : ℝ) : Set (Plane × ℝ) :=
  ((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b ∪
  (D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})

private noncomputable abbrev saddleCutoffSurfacePatch (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane)
    (D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ))
    (G : ℝ → Plane ≃ₘ[ℝ] Plane) (c s t₀ r h v₀ σ εcut j b m : ℝ) : Set (Plane × ℝ) :=
  ((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' (saddleCutoffSource B T G c s t₀ r h v₀ σ εcut j) ∪ (saddleCutoffUpperCap D T G c s t₀ r j b m))

private theorem lt_graph_on_interior_saddle_cutoff_region
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) (D T Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ))
    (G : ℝ → Plane ≃ₘ[ℝ] Plane) (ψ : ℝ ≃ ℝ)
    {c s t₀ r h v₀ σ εcut j b m : ℝ}
    (haj : -εcut / 2 < j) (hab : c + s + (-εcut / 2) < b)
    (hD : ∀ q, (D q).2 = q.2) (hT : ∀ q, (T q).2 = q.2)
    (hQ : ∀ q, (Q q).2 = ψ q.2) (hψ : StrictMono ψ)
    (g : Plane → ℝ)
    (hgraph : ∀ q ∈ saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j b m,
      g (Q q).1 = (Q q).2)
    (hlower : ∀ q ∈ saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j b m,
      c + s + (-εcut / 2) ≤ q.2)
    (hfrontier : frontier ((fun q : Plane × ℝ => (Q q).1) ''
        saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j b m) =
      (fun z : ℝ × ℝ => (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1) ''
        {z ∈ saddleCutoffHalfBand s h v₀ σ εcut j | σ * z.2 = -v₀ ∨
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
      (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
        (G (c + s + t₀) '' sphere 0 r \ B ''
          (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))) :
    ∀ x ∈ interior ((fun q : Plane × ℝ => (Q q).1) ''
      saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j b m),
      ψ (c + s + (-εcut / 2)) < g x := by
  let K := saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j b m
  let Y := (fun q : Plane × ℝ => (Q q).1) '' K
  have hbottom : ∀ q ∈ K, q.2 = c + s + (-εcut / 2) → (Q q).1 ∈ frontier Y := by
    intro q hq htime
    rw [hfrontier]
    rcases hq with ⟨w, hw, rfl⟩ | hq | ⟨w, hw, rfl⟩
    · rcases hw with ⟨_, ⟨z, hz, rfl⟩, rfl⟩ | hw
      · have ht : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2 := by
          change c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s) = _ at htime
          linarith only [htime]
        refine Or.inl ⟨z, ⟨hz, Or.inr ht⟩, ?_⟩
        apply congrArg (fun q : Plane × ℝ => (Q q).1)
        apply Prod.ext
        · exact (B.apply_symm_apply _).symm
        · rw [hT]
          change c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 =
            c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
          ring
      · have ht : w.2 = -εcut / 2 := by
          change c + s + w.2 = _ at htime
          linarith only [htime]
        exact Or.inr ⟨w.1, hw.1, by simp only [ht]⟩
    · have ht := hq.2.1
      linarith only [ht, htime, haj]
    · change (T (D w)).2 = c + s + (-εcut / 2) at htime
      rw [hT, hD] at htime
      linarith only [hw.1, htime, hab]
  intro x hx
  obtain ⟨q, hq, rfl⟩ := interior_subset hx
  rw [hgraph q hq, hQ]
  apply hψ
  apply lt_of_le_of_ne (hlower q hq)
  intro he
  exact disjoint_left.mp disjoint_interior_frontier hx (hbottom q hq he.symm)


section CutoffGraphBoundary

variable {e : ↑SphereTwo → EuclideanThree}
  (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2)) {β : ℝ × ℝ → ↑SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {c s : ℝ}
  (hs : 0 < s)
  (hgraph : ∀ z ∈ U, (EuclideanSpace.equivProdLast 2) (e (β z)) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
  (pmax : ↑SphereTwo) (σ h : ℝ) (hh : 0 < h) (hh1 : h < 1) (δ : ℝ) (hδ : 0 < δ) (r : ℝ) (hr : 0 < r)
  (G : ℝ → Plane ≃ₘ[ℝ] Plane) (t₀ : ℝ) (ht₀δ : t₀ < δ) (d : ℝ) (ht₀d : t₀ < d) (εcut : ℝ) (hεcut : εcut > 0)
  (hεcuth : εcut < s * h ^ 2 / 16) (θ : ℝ × ℝ → ℝ) (hθ01 : ∀ (q : ℝ × ℝ), θ q ∈ Icc 0 1)
  (hθ1 : ∀ (t u : ℝ), t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) (κ : ContDiffBump (0 : ℝ)) (hκout : κ.rOut = h / 2)
  (D : (Plane × ℝ) ≃ₘ[ℝ] Plane × ℝ) (hD : ∀ (z : Plane × ℝ), (D z).2 = z.2) (T : (Plane × ℝ) ≃ₘ[ℝ] Plane × ℝ)
  (hTheight : ∀ (z : Plane × ℝ), (T z).2 = z.2) (V : Set (ℝ × ℝ × ℝ))
  (hKV : {q | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
  (hVreg :
    ∀ q ∈ V,
      θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
        1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧ 0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (t₀ - q.1)) / q.2.2 ^ 2)
  (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) = (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1))
  (ρ : ℝ)
  (hmodelRect :
    ∀ t ∈ Icc (-δ) δ,
      ∀ (σ' : ℝ), σ' ^ 2 = 1 → ∀ u ∈ Icc (-h) h, saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
  (hclear :
    ∀ a < t₀,
      ∃ ρ_1 > 0,
        cthickening ρ_1 (⇑B '' {z | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
          (⇑(G (c + s + t₀)) '' closedBall 0 r)ᶜ)
  (ht₀pos : 0 < t₀) (hσsq : σ ^ 2 = 1)
  (hreferenceWall :
    (⇑(G (c + s + t₀)) '' sphere 0 r \ ⇑B '' saddleBandLevelCurve s t₀ σ '' Ioo (-(h / 2)) (h / 2)) ×ˢ
        Icc (c + s - εcut) (c + s + d) ⊆
      range (⇑T ∘ ⇑(EuclideanSpace.equivProdLast 2) ∘ e))
  (Vside : Set (ℝ × ℝ)) (hVside : IsOpen Vside) (hcurveVside : saddleBandLevelCurve s t₀ σ '' Ioo (-h) h ⊆ Vside)
  (hside : ∀ z ∈ Vside, B z ∈ ⇑(G (c + s + t₀)) '' closedBall 0 r ↔ s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
  (hcurveRef : ∀ u ∈ Ioo (-h) h, B (saddleBandLevelCurve s t₀ σ u) ∈ ⇑(G (c + s + t₀)) '' sphere 0 r)
  (v₀ : ℝ) (hv₀ : v₀ > 0) (hv₀t : v₀ ^ 2 / 2 < t₀ / 4)

variable (j : ℝ) (hj : j ∈ Ioo (t₀ / 2) t₀)

variable (hzeroR : (0, 0) ∈ interior (saddleCutoffHalfBand s h v₀ σ εcut j)) (hRU : (saddleCutoffHalfBand s h v₀ σ εcut j) ⊆ U)
      (hpoints : ∀ p ∈ (saddleCutoffModelMap B T c s) '' (saddleCutoffHalfBand s h v₀ σ εcut j), p.1.1 ∈ Ioo (-h) h ∧ -v₀ ≤ σ * p.1.2 ∧
        p.2 ∈ Icc (-εcut / 2) j ∧
        (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
          κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - t₀ / 4) / (t₀ / 4))) * (t₀ - p.2)) = 0)
      (hsidepos : ∀ z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j), |z.1| = 5 * h / 8 → 0 < σ * z.2)
      (hJenergy : ∀ z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j), (1 - ((saddleCutoffModelMap B T c s) z).1.1 ^ 2) * (((saddleCutoffModelMap B T c s) z).1.2 ^ 2 + 2 * s) / 2 ≤ s + t₀)
      (hbm : (e pmax 2 - r ^ 2 / 2) < (e pmax 2)) (hbaseb : c + s + t₀ < (e pmax 2 - r ^ 2 / 2)) (hrsq : r ^ 2 = 2 * ((e pmax 2) - (e pmax 2 - r ^ 2 / 2))) (Q : (Plane × ℝ) ≃ₘ[ℝ] Plane × ℝ)
      (ψ : ℝ ≃ₘ[ℝ] ℝ) (hψd : ∀ (t : ℝ), 0 < deriv (⇑ψ) t) (hQheight : ∀ (p : Plane × ℝ), (Q p).2 = ψ p.2)
      (hQcap : ⇑Q '' ⇑(D.trans T) '' {p | (e pmax 2 - r ^ 2 / 2) ≤ p.2 ∧ p.2 = (e pmax 2) - ‖p.1‖ ^ 2 / 2} = {p | (e pmax 2 - r ^ 2 / 2) ≤ p.2 ∧ p.2 = (e pmax 2) - ‖p.1‖ ^ 2 / 2})
      (hQwhole : ∀ t ≤ (e pmax 2 - r ^ 2 / 2), ∀ (y : Plane), Q (y, t) = (quadraticLevelScaling (e pmax 2 - r ^ 2 / 2) (e pmax 2) ((G (c + s + t₀)).symm y) (ψ t), ψ t))
      (hψmono : StrictMono ⇑ψ) (hψb : ψ (e pmax 2 - r ^ 2 / 2) = (e pmax 2 - r ^ 2 / 2)) (hStime : ∀ q ∈ (saddleCutoffSource B T G c s t₀ r h v₀ σ εcut j), q.2 ∈ Icc (-εcut / 2) j)
      (hQprojS : InjOn (fun q => (Q (q.1, c + s + q.2)).1) (saddleCutoffSource B T G c s t₀ r h v₀ σ εcut j))

variable (hQprojWhole : InjOn (fun q => (Q q).1) (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2))) (hKcompact : IsCompact (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2))) (OQ : Set Plane) (hOQ : IsOpen OQ)
        (gQ : Plane → ℝ) (hgQ : ContDiffOn ℝ ∞ gQ OQ) (WQ : Set (Plane × ℝ)) (hWQ : IsOpen WQ)
        (hKWQ : ⇑Q '' (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)) ⊆ WQ ∩ ⇑Q '' range (⇑T ∘ ⇑(EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e)) (hWQO : WQ ⊆ {q | q.1 ∈ OQ})
        (hWQeq : WQ ∩ ⇑Q '' range (⇑T ∘ ⇑(EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) = WQ ∩ {q | q.2 = gQ q.1})

variable (hclosed : IsClosed (Q '' range (T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e)))
  (hwholeTrace : ∀ q ∈ (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)),
    ∀ t ∈ Ico (c + s - εcut / 2) q.2,
      Q.symm ((Q q).1, ψ t) ∉ range (T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e))

include e B β U hU c s hs hgraph pmax σ h
  hh hh1 δ hδ r hr G t₀ ht₀δ d ht₀d εcut
  hεcut hεcuth θ hθ01 hθ1 κ hκout D hD T hTheight V
  hKV hVreg hTmodel ρ hmodelRect hclear ht₀pos hσsq hreferenceWall Vside hVside hcurveVside
  hside hcurveRef v₀ hv₀ hv₀t j hj hzeroR hRU hpoints hsidepos
  hJenergy hbm hbaseb hrsq Q ψ hψd hQheight hQcap hQwhole hψmono hψb
  hStime hQprojS hQprojWhole hKcompact OQ hOQ gQ hgQ WQ hWQ hKWQ hWQO
  hWQeq hclosed hwholeTrace in
private theorem exists_saddle_cutoff_graph_boundary_collars
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
            (∃ OQ : Set Plane, IsOpen OQ ∧ ∃ gQ : Plane → ℝ, ContDiffOn ℝ ∞ gQ OQ ∧
              ∃ WQ : Set (Plane × ℝ), IsOpen WQ ∧
                Q '' (((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' (saddleCutoffSource B T G c s t₀ r h v₀ σ εcut j)) ∪
                  (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) (e pmax 2 - r ^ 2 / 2)) ∪
                    ((D.trans T) '' {q : Plane × ℝ | (e pmax 2 - r ^ 2 / 2) ≤ q.2 ∧ q.2 = (e pmax 2) - ‖q.1‖ ^ 2 / 2}))) ⊆
                      WQ ∩ Q '' range (T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) ∧
                WQ ⊆ {q | q.1 ∈ OQ} ∧
                WQ ∩ Q '' range (T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) = WQ ∩ {q | q.2 = gQ q.1} ∧
                let P := fun z : ℝ × ℝ =>
                  (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
                (∀ x ∈ P '' {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
                    (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
                      (G (c + s + t₀) '' sphere 0 r \ B ''
                        (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))),
                    gQ x = ψ (c + s + (-εcut / 2)) ∧ fderiv ℝ gQ x ≠ 0) ∧
                let Y := (fun q : Plane × ℝ => (Q q).1) '' (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2))
                ∃ k : Plane → ℝ, ContDiff ℝ ∞ k ∧ (∀ y, fderiv ℝ k y ≠ 0) ∧
                  (∀ y ∈ Y, ψ (c + s + (-εcut / 2)) ≤ k y ∧ k y ≤ gQ y) ∧
                  ∃ Acut : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
                    (∀ q, (Acut q).1 = q.1) ∧ (∀ y ∈ Y, Acut (y, gQ y) = (y, k y)) ∧
                    (∀ q ∈ Q '' range (T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e),
                      q ∉ WQ ∩ {q | q.1 ∈ interior Y} →
                      (Acut : (Plane × ℝ) → Plane × ℝ) =ᶠ[𝓝 q] id) ∧
                    (∀ x, IsCriticalPointAt (𝓡 2) (fun y => (Acut (Q (T ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) (e y))))).2) x →
                      x ≠ β (0, 0) ∧
                        (fun y => (Acut (Q (T ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) (e y))))).2) =ᶠ[𝓝 x] (fun y => ψ (e y 2)))) ∧
                let P := fun z : ℝ × ℝ =>
                  (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
                let Cboundary := P '' {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | σ * z.2 = -v₀ ∨
                    (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
                  (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
                    (G (c + s + t₀) '' sphere 0 r \ B ''
                      (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))
                IsCompact (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)) ∧ Schoenflies.IsJordanCurve Cboundary ∧
                  (fun q : Plane × ℝ => (Q q).1) '' (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)) = closure (Schoenflies.inside Cboundary) ∧
                  frontier ((fun q : Plane × ℝ => (Q q).1) '' (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2))) = Cboundary ∧
                  let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * (-εcut / 2)) / (v₀ ^ 2 + 2 * s))
                  Schoenflies.IsCutPair Cboundary (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀)))
                    (P '' {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | σ * z.2 = -v₀})
                    (P '' {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
                      (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
                        (G (c + s + t₀) '' sphere 0 r \ B ''
                          (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))) := by
  have hregionFacts := projection_saddle_cutoff_region_eq_closure_inside ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) B (G (c + s + t₀)) T Q
      ψ.toEquiv θ κ hU hs hh hh1 hεcut hεcuth ht₀pos ht₀δ ht₀d hj hσsq hr hv₀ hv₀t hκout
      hgraph hTheight hθ01 hθ1 hcurveRef
      (fun u hu => hmodelRect δ ⟨neg_le_self hδ.le, le_rfl⟩ σ hσsq u hu) hclear hKV hVreg hTmodel
      hbaseb hbm hrsq hψmono hψb
      hQwhole hQcap hOQ hgQ hWQ hWQO hWQeq hKcompact hRU hsidepos
      (fun p hp => ⟨(hpoints p hp).2.1, (hpoints p hp).2.2.2⟩) hQprojS
      (fun q hq => (hKWQ hq).1)
  have hbottomReg := fderiv_ne_zero_on_saddle_cutoff_bottom_boundary ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) B T Q ψ hU hs hh.le hεcut
        (ht₀pos.le.trans ht₀d.le) (by linarith only [hεcut, hj.1, ht₀pos])
        hgraph hTheight hQheight hψd hreferenceWall hOQ hgQ hWQ hWQO hWQeq
        (saddleCutoffUpperCap D T G c s t₀ r j (e pmax 2 - r ^ 2 / 2) (e pmax 2)) hRU (fun q hq => (hKWQ hq).1)
  obtain ⟨χ, hχsource, hχtarget, hχformula, hχheight, hχimage⟩ :=
    exists_partialDiffeomorph_saddle_cutoff_negative_edge ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) B (G (c + s + t₀)) T Q
        hψmono hU hs.le hh hh1 hεcut.le ht₀pos ht₀δ ht₀d hj hσsq hv₀ hv₀t
        hgraph hTheight (fun q => (hθ01 q).2)
        (fun u hu => hmodelRect δ ⟨neg_le_self hδ.le, le_rfl⟩ σ hσsq u hu)
        hclear hKV hVreg hTmodel hbaseb hψb
        hQheight hQcap hOQ hgQ hWQ hWQO hWQeq hKcompact hRU (fun q hq => (hKWQ hq).1)
        hQprojWhole hsidepos (fun p hp => (hpoints p hp).2.1)
  have hsplit : {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | σ * z.2 = -v₀ ∨
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} =
      {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | σ * z.2 = -v₀} ∪
        {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} := by
    ext z
    simp only [mem_ofPred_eq, mem_union]
    exact and_or_left
  have hboundarySplit (P : (ℝ × ℝ) → Plane) :
      P '' {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | σ * z.2 = -v₀ ∨
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
        (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
          (G (c + s + t₀) '' sphere 0 r \ B ''
            (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) =
      P '' {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | σ * z.2 = -v₀} ∪
        (P '' {z ∈ (saddleCutoffHalfBand s h v₀ σ εcut j) | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
          (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
            (G (c + s + t₀) '' sphere 0 r \ B ''
              (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))) := by
    rw [hsplit, image_union, union_assoc]
  have hregionBottom := hregionFacts
  simp only [hboundarySplit] at hregionBottom
  have hc (z : ℝ × ℝ) :
      c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s) =
        c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by ring
  have hcs (x : ℝ) : c + s + (x - s) = c + x := by ring
  have hSmodel :
      ((fun z : ℝ × ℝ =>
        ((T (B z, c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1,
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) '' (saddleCutoffHalfBand s h v₀ σ εcut j)) ∪
        (G (c + s + t₀) '' sphere 0 r \ B ''
          (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc (-εcut / 2) j =
        (saddleCutoffSource B T G c s t₀ r h v₀ σ εcut j) := by
    simp only [saddleCutoffSource, image_image, saddleCutoffModelMap,
      B.apply_symm_apply, hc]
  have hKheight : ∀ p ∈ (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)), c + s + (-εcut / 2) ≤ p.2 := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩ | hp | ⟨q, hq, rfl⟩
    · dsimp only
      linarith only [(hStime q hq).1]
    · have ht : c + s + j ≤ p.2 := hp.2.1
      linarith only [ht, hεcut, hj.1, ht₀pos]
    · change c + s + (-εcut / 2) ≤ (T (D q)).2
      rw [hTheight, hD]
      linarith only [hq.1, hbaseb, ht₀pos, hεcut]
  have hbottomCollar := exists_partialDiffeomorph_saddle_cutoff_boundary
    B (G (c + s + t₀)) T Q θ ψ hTheight hQheight
    (s := s) (a := -εcut / 2) (j := j) (ℓ := c + s) (k := 5 * h / 8)
    hs (by linarith only [hεcut]) ht₀pos ht₀δ hσsq
    (by positivity) (by linarith only [hh]) (by linarith only [hh]) hh1
    (by linarith only [hεcut]) (by linarith only [hεcut, ht₀pos, ht₀d])
    (by nlinarith only [hεcuth, mul_pos hs (sq_pos_of_pos hh)]) hr hv₀
    (by linarith only [hv₀t, hj.1, ht₀pos]) (by nlinarith only [hv₀t, ht₀pos])
    (fun t u hu => hθ1 t u (Or.inr hu))
    (by rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact hcurveRef u ⟨by linarith only [hu.1, hh], by linarith only [hu.2, hh]⟩)
    (fun u hu => hmodelRect δ ⟨neg_le_self hδ.le, le_rfl⟩ σ hσsq u hu)
    hclear hVside (fun ξ hξ => hcurveVside ⟨ξ * (5 * h / 8), by
      rcases hξ with rfl | hξ
      · constructor <;> simp only [neg_one_mul] <;> linarith only [hh]
      · have he : ξ = 1 := hξ; subst ξ
        constructor <;> simp only [one_mul] <;> linarith only [hh], rfl⟩)
    hside hKV hTmodel hKcompact hOQ hgQ (fun p hp => (hKWQ hp).1) hWQO
    (fun p hp => (hWQeq.subset (hKWQ (mem_image_of_mem Q hp))).2) hKheight
    hsidepos
    (fun z hz => hTmodel ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z) (hKV ⟨⟨by linarith only [hz.2.2.1, hεcut],
      hz.2.2.2.trans (hj.2.trans ht₀d).le⟩, hz.1.trans (by linarith only [hh]), by ring⟩))
    (fun z hz => by simpa only [hc, hcs] using (hpoints ((saddleCutoffModelMap B T c s) z) ⟨z, hz, rfl⟩).2.1)
    (fun z hz => by simpa only [hc, hcs] using hJenergy z hz)
    (hSmodel ▸ hQprojS)
    (by simpa only [hc, hcs] using hregionBottom.2.1)
    (by simpa only [hc, hcs] using hregionBottom.2.2.2)
    (by simpa only [hc, hcs] using hbottomReg) χ hχsource
    (by simpa only [hc, hcs] using hχformula) hχheight hχimage
  rcases hbottomCollar with ⟨γ, hγ, hγd, hγinj, hγimage, hγleft, hγright,
    E, hEsource, hEtarget, hEbase, hEheight, hEimage, hEχ,
    η, hηsource, hηboundary, hηimage, hηheight, hηχ, hηE⟩
  have ha : -εcut / 2 < v₀ ^ 2 / 2 := by nlinarith only [hεcut, sq_nonneg v₀]
  have hB : 0 < s + v₀ ^ 2 / 2 := by nlinarith only [hs, sq_nonneg v₀]
  have hu : Real.sqrt ((v₀ ^ 2 / 2 - (-εcut / 2)) / (s + v₀ ^ 2 / 2)) =
      Real.sqrt ((v₀ ^ 2 - 2 * (-εcut / 2)) / (v₀ ^ 2 + 2 * s)) := by
    congr 1
    apply (div_eq_div_iff hB.ne' (by nlinarith only [hB] : v₀ ^ 2 + 2 * s ≠ 0)).mpr
    ring
  have hfr := PlanarJordan.frontier_parabolic_lens ha hB
  rw [hu] at hfr
  obtain ⟨F, _, hFregion, V, hV, hFV, hVs, hFη⟩ :=
    PlanarJordan.exists_diffeomorph_eqOn_neighborhood_of_parabolic_lens ha hB η
      hregionFacts.1 (by rw [hfr]; exact hηsource)
      (by rw [← hregionFacts.2.1]; exact hηimage)
  have hstrict : ∀ p ∈ interior {p : ℝ × ℝ | -εcut / 2 ≤ p.1 ∧
      p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2},
      ψ (c + s + (-εcut / 2)) < gQ (F p) := by
    have hstrict := lt_graph_on_interior_saddle_cutoff_region B D T Q G ψ.toEquiv
      (by linarith only [hεcut, hj.1, ht₀pos]) (by linarith only [hbaseb, hεcut, ht₀pos])
      hD hTheight hQheight hψmono gQ
      (fun q hq => (hWQeq.subset (hKWQ (mem_image_of_mem Q hq))).2.symm)
      hKheight hregionFacts.2.2.1
    intro p hp
    apply hstrict
    have hh := F.toHomeomorph.image_interior
      {p : ℝ × ℝ | -εcut / 2 ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2}
    change F '' interior _ = interior (F '' _) at hh
    rw [hFregion, ← hregionFacts.2.1] at hh
    exact hh.subset (mem_image_of_mem F hp)
  have hheight : ∀ p ∈ V, gQ (F p) = ψ (c + s + p.1) := by
    intro p hp
    rw [hFη hp]
    exact hηheight p (hVs hp)
  have hFY : F '' {p : ℝ × ℝ | -εcut / 2 ≤ p.1 ∧
      p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2} =
      (fun q : Plane × ℝ => (Q q).1) '' (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)) :=
    hFregion.trans hregionFacts.2.1.symm
  have hminorant := exists_regular_lower_graph_of_parabolic_lens F ψ hψmono ha hB hgQ
    (by rw [hFY]; rintro _ ⟨q, hq, rfl⟩; exact hWQO (hKWQ (mem_image_of_mem Q hq)).1)
    (by rw [hFY]; exact hKcompact.image (continuous_fst.comp Q.continuous))
    hstrict hV hFV hheight
  rw [hFY] at hminorant
  rcases hminorant with ⟨k, hk, hkd, hbound, C, hC, hCY, hmatch, _, _, _, _⟩
  have hgraphQ : ∀ q ∈ (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)), (Q q).2 = gQ (Q q).1 := by
    intro q hq
    exact (hWQeq.subset (hKWQ (mem_image_of_mem Q hq))).2
  let R := saddleCutoffHalfBand s h v₀ σ εcut j
  let f : (ℝ × ℝ) → ℝ := fun z => c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2
  have hf : ContDiff ℝ ∞ f := by dsimp [f]; fun_prop
  have hqK (z : ℝ × ℝ) (hz : z ∈ R) :
      T (B z, f z) ∈ saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j
        (e pmax 2 - r ^ 2 / 2) (e pmax 2) := by
    apply Or.inl
    refine ⟨(B (saddleCutoffModelMap B T c s z).1, (saddleCutoffModelMap B T c s z).2),
      Or.inl ⟨saddleCutoffModelMap B T c s z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
    dsimp only [saddleCutoffModelMap]
    rw [B.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rfl
    · rw [hTheight]
      dsimp [f]
      ring
  obtain ⟨χ₀, hχ₀source, hχ₀, _⟩ :=
    exists_partialDiffeomorph_projection_of_graph_neighborhood B (T.trans Q) hf hU hOQ hgQ
      hWQ hWQO (by
        intro z hz hw
        have heq : (T.trans Q) (B z, f z) = Q (T ((EuclideanSpace.equivProdLast 2) (e (β z)))) := by
          rw [hgraph z hz]; rfl
        apply (hWQeq.subset ⟨hw, ?_⟩).2
        exact ⟨T ((EuclideanSpace.equivProdLast 2) (e (β z))), ⟨β z, rfl⟩, heq.symm⟩)
  have hRχ₀ : R ⊆ χ₀.source := by
    intro z hz
    rw [hχ₀source]
    exact ⟨hRU hz, (hKWQ (mem_image_of_mem Q (hqK z hz))).1⟩
  have hPint : (χ₀ (0, 0)) ∈ interior ((fun q : Plane × ℝ => (Q q).1) ''
      saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j
        (e pmax 2 - r ^ 2 / 2) (e pmax 2)) := by
    apply interior_mono (s := χ₀ '' interior R) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨T (B z, f z), hqK z (interior_subset hz), by rw [hχ₀]; rfl⟩
    · have ho : IsOpen (χ₀ '' interior R) :=
        χ₀.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hRχ₀)
      rw [ho.interior_eq]
      exact mem_image_of_mem χ₀ hzeroR
  have hcenter : Q (T ((EuclideanSpace.equivProdLast 2) (e (β (0, 0))))) ∈
      WQ ∩ {q | q.1 ∈ interior ((fun q : Plane × ℝ => (Q q).1) ''
        saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j
          (e pmax 2 - r ^ 2 / 2) (e pmax 2))} := by
    rw [hgraph (0, 0) (hRU (interior_subset hzeroR))]
    refine ⟨(hKWQ (mem_image_of_mem Q (hqK (0, 0) (interior_subset hzeroR)))).1, ?_⟩
    rw [hχ₀] at hPint
    exact hPint
  have hclearQ : ∀ y ∈ (fun q : Plane × ℝ => (Q q).1) '' (saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ εcut j (e pmax 2 - r ^ 2 / 2) (e pmax 2)),
      ∀ t ∈ Ico (ψ (c + s + (-εcut / 2))) (gQ y),
        (y, t) ∉ Q '' range (T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) := by
    rintro _ ⟨q, hq, rfl⟩ t ht ⟨w, hw, heq⟩
    have htlo : c + s - εcut / 2 ≤ ψ.symm t := hψmono.le_iff_le.mp (by
      rw [ψ.apply_symm_apply]
      simpa only [sub_eq_add_neg, neg_div] using ht.1)
    have htup : ψ.symm t < q.2 := hψmono.lt_iff_lt.mp (by
      rw [ψ.apply_symm_apply, ← hQheight q, hgraphQ q hq]
      exact ht.2)
    have hn := hwholeTrace q hq (ψ.symm t) ⟨htlo, htup⟩
    rw [ψ.apply_symm_apply, ← heq, Q.symm_apply_apply] at hn
    exact hn hw
  obtain ⟨Acut, hAcutfst, hAcutgraph, hAcutfixed⟩ :=
    Diffeomorph.exists_diffeomorph_graph_replacement_below hclosed hWQ
      (hKcompact.image (continuous_fst.comp Q.continuous)) hOQ
      (by rintro _ ⟨q, hq, rfl⟩; exact hWQO (hKWQ (mem_image_of_mem Q hq)).1)
      hgQ hk (by
        rintro _ ⟨q, hq, rfl⟩
        simpa only [Function.comp_def, ← hgraphQ q hq, Prod.eta] using hKWQ (mem_image_of_mem Q hq))
      hbound hclearQ hC hCY hmatch
  have heQT : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, Plane × ℝ) ∞
      (Q ∘ T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e) :=
    ((he.continuousLinearEquiv_comp (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2)).diffeomorph_comp T).diffeomorph_comp Q
  refine ⟨⟨OQ, hOQ, gQ, hgQ, WQ, hWQ, hKWQ, hWQO, hWQeq,
    hbottomReg, k, hk, hkd, hbound, Acut, hAcutfst, hAcutgraph, hAcutfixed, ?_⟩,
    hKcompact, hregionFacts⟩
  intro x hx
  have hh := eventuallyEq_of_isCriticalPointAt_regular_graph_replacement heQT hWQ
    (fun y hy => (hWQeq.subset ⟨hy, ⟨_, ⟨y, rfl⟩, rfl⟩⟩).2) hk hkd Acut hAcutfst hAcutgraph
    (by simpa only [← range_comp] using hAcutfixed) hx
  refine ⟨fun heq => hh.1 (heq ▸ hcenter), ?_⟩
  filter_upwards [hh.2] with y hy
  have hy' := congrArg Prod.snd hy
  change (Acut (Q (T ((EuclideanSpace.equivProdLast 2) (e y))))).2 =
    (Q (T ((EuclideanSpace.equivProdLast 2) (e y)))).2 at hy'
  rw [hQheight, hTheight] at hy'
  exact hy'



end CutoffGraphBoundary


private theorem exists_cutoff_projection_graph_and_boundary_collars {e : ↑SphereTwo → EuclideanThree}
  (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2)) {β : ℝ × ℝ → ↑SphereTwo}
  {U : Set (ℝ × ℝ)} (hU : IsOpen U) {c s : ℝ} (hs : 0 < s)
  (hgraph : ∀ z ∈ U, (EuclideanSpace.equivProdLast 2) (e (β z)) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
  (p : ↑SphereTwo) (σ h : ℝ) (hh : 0 < h) (hh1 : h < 1) (δ : ℝ) (hδ : 0 < δ) (η : ↑unitInterval → ↑SphereTwo)
  (Φ : ℝ → ↑SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ ↑SphereTwo)
  (hslices :
    ∀ t ∈ Icc (-δ) δ,
      (IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ fun u =>
          (fun q => ((EuclideanSpace.equivProdLast 2) (e ((Φ (q.1 - δ / 2)) (η q.2)))).1) (t, u)) ∧
        ∀ (u : ↑unitInterval), (e ((Φ (t - δ / 2)) (η u))).ofLp 2 = c + s + t)
  (r : ℝ) (hr : 0 < r) (A : (Plane × ℝ) ≃ₘ[ℝ] Plane × ℝ) (G : ℝ → Plane ≃ₘ[ℝ] Plane) (t₀ : ℝ) (ht₀δ : t₀ < δ)
  (ht₀b : c + s + t₀ < (e p).ofLp 2 - r ^ 2 / 2) (d : ℝ) (ht₀d : t₀ < d) (hdδ : d < δ) (εcut : ℝ) (hεcut : εcut > 0)
  (hεcuth : εcut < s * h ^ 2 / 16) (θ : ℝ × ℝ → ℝ) (hθ01 : ∀ (q : ℝ × ℝ), θ q ∈ Icc 0 1)
  (hθ1 : ∀ (t u : ℝ), t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) (κ : ContDiffBump (0 : ℝ)) (hκout : κ.rOut = h / 2)
  (hθformula : ∀ (t u : ℝ), θ (t, u) = 1 - (1 - ((t - t₀ / 4) / (t₀ / 4)).smoothTransition) * κ u)
  (H : ℝ → Plane ≃ₘ[ℝ] Plane) (D : (Plane × ℝ) ≃ₘ[ℝ] Plane × ℝ) (hD : ∀ (z : Plane × ℝ), (D z).2 = z.2)
  (hDlo :
    ∀ t ≤ (e p).ofLp 2 - r ^ 2 / 2,
      ∀ (x : Plane), D (quadraticLevelScaling ((e p).ofLp 2 - r ^ 2 / 2) ((e p).ofLp 2) x t, t) = ((H t) x, t))
  (hregion :
    ⇑D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 ≤ (e p).ofLp 2 - ‖z.1‖ ^ 2 / 2} =
      heightCapRegion (fun t => ⇑(G t)) (⇑A) (c + s + t₀) ((e p).ofLp 2 - r ^ 2 / 2) ((e p).ofLp 2) r)
  (hinter :
    heightCapRegion (fun t => ⇑(G t)) (⇑A) (c + s + t₀) ((e p).ofLp 2 - r ^ 2 / 2) ((e p).ofLp 2) r ∩
        range (⇑(EuclideanSpace.equivProdLast 2) ∘ e) =
      ⇑D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 = (e p).ofLp 2 - ‖z.1‖ ^ 2 / 2})
  (T : (Plane × ℝ) ≃ₘ[ℝ] Plane × ℝ) (hT : ∀ (z : Plane × ℝ), T z = ((G (c + s + t₀)) ((H z.2).symm z.1), z.2))
  (hTheight : ∀ (z : Plane × ℝ), (T z).2 = z.2)
  (hTarc :
    ∀ t ∈ Icc (-d) d,
      ∀ (u : ↑unitInterval),
        T ((fun q => ((EuclideanSpace.equivProdLast 2) (e ((Φ (q.1 - δ / 2)) (η q.2)))).1) (t, u), c + s + t) =
          ((fun q => ((EuclideanSpace.equivProdLast 2) (e ((Φ (q.1 - δ / 2)) (η q.2)))).1) (t₀, u), c + s + t))
  (hwhole :
    (⇑(G (c + s + t₀)) '' closedBall 0 r) ×ˢ Icc (c + s + t₀) ((e p).ofLp 2 - r ^ 2 / 2) ∩
        range (⇑T ∘ ⇑(EuclideanSpace.equivProdLast 2) ∘ e) =
      (⇑(G (c + s + t₀)) '' sphere 0 r) ×ˢ Icc (c + s + t₀) ((e p).ofLp 2 - r ^ 2 / 2))
  (V : Set (ℝ × ℝ × ℝ))
  (hKV : {q | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
  (hVreg :
    ∀ q ∈ V,
      θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
        1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧ 0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (t₀ - q.1)) / q.2.2 ^ 2)
  (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) = (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1))
  (hrawU : ∀ t ∈ Icc (-εcut) d, ∀ (z : ℝ × ℝ), |z.1| ≤ h → (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U)
  (Z : Set (Plane × ℝ)) (hZ : IsOpen Z)
  (hZeq :
    Z ∩ range (⇑T ∘ ⇑(EuclideanSpace.equivProdLast 2) ∘ e) =
      Z ∩
        {q |
          (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
            s + (q.2 - (c + s)) + θ (q.2 - (c + s), (B.symm q.1).1) * (t₀ - (q.2 - (c + s)))})
  (ρclear : ℝ)
  (hρZ :
    cthickening ρclear
        (⇑T ''
          (fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) ''
            {q | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}) ⊆
      Z)
  (ρ : ℝ)
  (hmodelRect :
    ∀ t ∈ Icc (-δ) δ,
      ∀ (σ' : ℝ), σ' ^ 2 = 1 → ∀ u ∈ Icc (-h) h, saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
  (hclear :
    ∀ a < t₀,
      ∃ ρ_1 > 0,
        cthickening ρ_1 (⇑B '' {z | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
          (⇑(G (c + s + t₀)) '' closedBall 0 r)ᶜ)
  (ht₀pos : 0 < t₀) (hσsq : σ ^ 2 = 1)
    (hreferenceWall :
      (G (c + s + t₀) '' sphere 0 r \ B ''
        (saddleBandLevelCurve s t₀ σ '' Ioo (-(h / 2)) (h / 2))) ×ˢ
          Icc (c + s - εcut) (c + s + d) ⊆ range (T ∘ (EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e))
    (hcircleRef :
      ⇑(G (c + s + t₀)) '' sphere 0 r = ⇑B '' saddleBandLevelCurve s t₀ σ '' Icc (-h) h ∪ range fun u => (fun q : ℝ × unitInterval => ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) (e (Φ (q.1 - δ / 2) (η q.2)))).1) (t₀, u))
    (Vside : Set (ℝ × ℝ)) (hVside : IsOpen Vside) (hcurveVside : saddleBandLevelCurve s t₀ σ '' Ioo (-h) h ⊆ Vside)
    (hside : ∀ z ∈ Vside, B z ∈ ⇑(G (c + s + t₀)) '' closedBall 0 r ↔ s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    (hlowerClearance :
      Disjoint (range (⇑T ∘ ⇑(EuclideanSpace.equivProdLast 2) ∘ e))
        (interior (⇑(G (c + s + t₀)) '' closedBall 0 r) ×ˢ Icc (c + s - εcut / 2) (c + s + t₀)))
    (hwedge :
      ∀ t ∈ Icc (-εcut) t₀,
        ∀ (z : ℝ × ℝ),
          |z.1| ≤ h →
            s + t + θ (t, z.1) * (t₀ - t) ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
              (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + t₀ →
                (B z, c + s + t) ∈ Z ∧
                  (s + t + θ (t, z.1) * (t₀ - t) < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
                    (B z, c + s + t) ∉ range (⇑T ∘ ⇑(EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) ∘ e)))
    (hcurveRef : ∀ u ∈ Ioo (-h) h, B (saddleBandLevelCurve s t₀ σ u) ∈ ⇑(G (c + s + t₀)) '' sphere 0 r)
    (v₀ : ℝ) (hv₀ : v₀ > 0) (hv₀t : v₀ ^ 2 / 2 < t₀ / 4)
    (hwide :
      ∀ j ∈ Ioo (t₀ / 2) t₀,
        let R : Set (ℝ × ℝ) :=
          {z |
            |z.1| ≤ 5 * h / 8 ∧
              -v₀ ≤ σ * z.2 ∧
                -εcut / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j};
        let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
          (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1, (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s);
        let C : Set ((ℝ × ℝ) × ℝ) :=
          (fun q : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ q.1, q.2)) ''
            {q | |q.1| ≤ 7 * h / 8 ∧ h / 2 ≤ |q.1| ∧ q.2 ∈ Icc (-εcut / 2) j};
        IsCompact R ∧
          (0, 0) ∈ interior R ∧
            R ⊆ U ∧
              IsCompact (J '' R) ∧
                IsCompact C ∧
                  (∀ z ∈ R, (B (J z).1, c + s + (J z).2) = T ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) (e (β z)))) ∧
                    (∀ p ∈ J '' R,
                        p.1.1 ∈ Ioo (-h) h ∧
                          -v₀ ≤ σ * p.1.2 ∧
                            p.2 ∈ Icc (-εcut / 2) j ∧
                              (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
                                  κ p.1.1 * ((1 - ((p.2 - t₀ / 4) / (t₀ / 4)).smoothTransition) * (t₀ - p.2)) =
                                0) ∧
                      (∀ z ∈ R, |z.1| = 5 * h / 8 → 0 < σ * z.2) ∧
                        ∃ δ > 0,
                          ∀ μ ∈ Ioo 0 δ,
                            InjOn (fun z => Real.exp (-μ * (J z).2) • (G (c + s + t₀)).symm (T ((EuclideanSpace.equivProdLast (𝕜 := ℝ) 2) (e (β z)))).1) R ∧
                              InjOn (fun p => Real.exp (-μ * p.2) • (G (c + s + t₀)).symm (B p.1)) (J '' R ∪ C)) :
    let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
    let m := e p 2
    let b := m - r ^ 2 / 2
      ∀ j ∈ Ioo (t₀ / 2) t₀,
      let R : Set (ℝ × ℝ) := {z | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
        -εcut / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
      let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
        (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
      let C : Set ((ℝ × ℝ) × ℝ) :=
        (fun q : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ q.1, q.2)) ''
          {q | |q.1| ≤ 7 * h / 8 ∧ h / 2 ≤ |q.1| ∧ q.2 ∈ Icc (-εcut / 2) j}
      let S : Set (Plane × ℝ) :=
        ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪
          ((G (c + s + t₀) '' sphere 0 r \ B ''
            (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc (-εcut / 2) j)
      IsCompact R ∧ (0, 0) ∈ interior R ∧ R ⊆ U ∧
        IsCompact (J '' R) ∧ IsCompact C ∧ IsCompact S ∧
        (∀ z ∈ R, (B (J z).1, c + s + (J z).2) =
          T (L (e (β z)))) ∧
        (∀ p ∈ J '' R, p.1.1 ∈ Ioo (-h) h ∧ -v₀ ≤ σ * p.1.2 ∧ p.2 ∈ Icc (-εcut / 2) j ∧
          (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
            κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - t₀ / 4) / (t₀ / 4))) *
              (t₀ - p.2)) = 0) ∧
        (∀ z ∈ R, |z.1| = 5 * h / 8 → 0 < σ * z.2) ∧
        (∀ z ∈ R, (J z).1.1 = z.1) ∧
        (fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S ⊆ range (T ∘ L ∘ e) ∧
        ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
          InjOn (fun z => Real.exp (-μ * (J z).2) •
            (G (c + s + t₀)).symm ((T (L (e (β z)))).1)) R ∧
          InjOn (fun p : (ℝ × ℝ) × ℝ => Real.exp (-μ * p.2) •
            (G (c + s + t₀)).symm (B p.1)) ((J '' R) ∪ C) ∧
          InjOn (fun q : Plane × ℝ => Real.exp (-μ * q.2) •
            (G (c + s + t₀)).symm q.1) S ∧
          ∃ (Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ) (α : ℝ),
            0 < α ∧ (∀ t, 0 < deriv ψ t) ∧
            (∀ t, (c + s + t₀ + b) / 2 ≤ t → ψ t = t) ∧
            (∀ q, (Q q).2 = ψ q.2) ∧
            (∀ t ≤ c + s + t₀, ∀ y, Q (y, t) =
              ((α * Real.exp (-μ * t)) • (G (c + s + t₀)).symm y, ψ t)) ∧
            (∀ q, (c + s + t₀ + b) / 2 ≤ q.2 → Q q = (D.trans T).symm q) ∧
            Q '' ((G (c + s + t₀) '' sphere 0 r) ×ˢ Iic b) ⊆
              {q : Plane × ℝ | q.2 = m - ‖q.1‖ ^ 2 / 2} ∧
            Q '' ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}) =
              {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} ∧
            (∀ t ≤ b, ∀ y, Q (y, t) =
              (quadraticLevelScaling b m ((G (c + s + t₀)).symm y) (ψ t), ψ t)) ∧
            Q '' (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
              ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})) =
                {q : Plane × ℝ | ψ (c + s + j) ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} ∧
            InjOn (fun q : (ℝ × ℝ) × ℝ => (Q (B q.1, c + s + q.2)).1) ((J '' R) ∪ C) ∧
            InjOn (fun q : Plane × ℝ => (Q (q.1, c + s + q.2)).1) S ∧
            InjOn (fun q : Plane × ℝ => (Q q).1)
              (((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                  ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))) ∧
            (∀ q ∈ (((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                  ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))),
              ∀ t ∈ Ico (c + s - εcut / 2) q.2,
                Q.symm ((Q q).1, ψ t) ∉ range (T ∘ L ∘ e)) ∧
            (∃ OQ : Set Plane, IsOpen OQ ∧ ∃ gQ : Plane → ℝ, ContDiffOn ℝ ∞ gQ OQ ∧
              ∃ WQ : Set (Plane × ℝ), IsOpen WQ ∧
                Q '' (((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                  (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                    ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))) ⊆
                      WQ ∩ Q '' range (T ∘ L ∘ e) ∧
                WQ ⊆ {q | q.1 ∈ OQ} ∧
                WQ ∩ Q '' range (T ∘ L ∘ e) = WQ ∩ {q | q.2 = gQ q.1} ∧
                let K := ((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                  (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                    ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))
                let P := fun z : ℝ × ℝ =>
                  (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
                (∀ x ∈ P '' {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
                    (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
                      (G (c + s + t₀) '' sphere 0 r \ B ''
                        (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))),
                    gQ x = ψ (c + s + (-εcut / 2)) ∧ fderiv ℝ gQ x ≠ 0) ∧
                let Y := (fun q : Plane × ℝ => (Q q).1) '' K
                ∃ k : Plane → ℝ, ContDiff ℝ ∞ k ∧ (∀ y, fderiv ℝ k y ≠ 0) ∧
                  (∀ y ∈ Y, ψ (c + s + (-εcut / 2)) ≤ k y ∧ k y ≤ gQ y) ∧
                  ∃ Acut : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
                    (∀ q, (Acut q).1 = q.1) ∧ (∀ y ∈ Y, Acut (y, gQ y) = (y, k y)) ∧
                    (∀ q ∈ Q '' range (T ∘ L ∘ e),
                      q ∉ WQ ∩ {q | q.1 ∈ interior Y} →
                      (Acut : (Plane × ℝ) → Plane × ℝ) =ᶠ[𝓝 q] id) ∧
                    (∀ x, IsCriticalPointAt (𝓡 2) (fun y => (Acut (Q (T (L (e y))))).2) x →
                      x ≠ β (0, 0) ∧
                        (fun y => (Acut (Q (T (L (e y))))).2) =ᶠ[𝓝 x] (fun y => ψ (e y 2)))) ∧
                let K := ((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                  (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                    ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))
                let P := fun z : ℝ × ℝ =>
                  (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
                let Cboundary := P '' {z ∈ R | σ * z.2 = -v₀ ∨
                    (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
                  (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
                    (G (c + s + t₀) '' sphere 0 r \ B ''
                      (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))
                IsCompact K ∧ Schoenflies.IsJordanCurve Cboundary ∧
                  (fun q : Plane × ℝ => (Q q).1) '' K = closure (Schoenflies.inside Cboundary) ∧
                  frontier ((fun q : Plane × ℝ => (Q q).1) '' K) = Cboundary ∧
                  let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * (-εcut / 2)) / (v₀ ^ 2 + 2 * s))
                  Schoenflies.IsCutPair Cboundary (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀)))
                    (P '' {z ∈ R | σ * z.2 = -v₀})
                    (P '' {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -εcut / 2} ∪
                      (fun y => (Q (y, c + s + (-εcut / 2))).1) ''
                        (G (c + s + t₀) '' sphere 0 r \ B ''
                          (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))) := by
  intro L m b j hj Rwide J Cwall Sfull
  obtain ⟨hRwide, hzeroR, hRU, hJcompact, hCcompact, hJactual, hpoints, hsidepos,
    δproj, hδproj, hprojections⟩ := hwide j hj
  have hScircle := isCompact_reference_circle_compl_selected_arc B (G (c + s + t₀))
    hs.le ht₀pos hσsq hh1 (k := 5 * h / 8) (by linarith only [hh]) hr
    hVside hcurveVside hcurveRef hside
  have hScompact : IsCompact Sfull :=
    (hJcompact.image ((B.continuous.comp continuous_fst).prodMk continuous_snd)).union
      (hScircle.prod isCompact_Icc)
  have hcertificate := saddle_cutoff_half_band_coordinates_and_height B T hh.le hεcut.le
    (hj.2.trans ht₀d).le hj.2.le (fun q => (hθ01 q).2) hKV hVreg hTmodel
    (v₀ := v₀) (σ := σ)
  have hJcoord (z : ℝ × ℝ) (hz : z ∈ Rwide) : (J z).1.1 = z.1 := (hcertificate z hz).1
  have hJenergy (z : ℝ × ℝ) (hz : z ∈ Rwide) :
      (1 - (J z).1.1 ^ 2) * ((J z).1.2 ^ 2 + 2 * s) / 2 ≤ s + t₀ := (hcertificate z hz).2
  obtain ⟨δall, hδall, hδle, hwholeProjection⟩ := exists_injOn_exp_projection_union_reference_cylinder
    B (G (c + s + t₀)) hs.le ht₀pos ht₀δ hσsq hh hh1 hr hv₀.le (by nlinarith only [hv₀t])
    (fun u hu => hmodelRect δ ⟨neg_le_self hδ.le, le_rfl⟩ σ hσsq u hu) hclear hJcompact
    (by rintro _ ⟨z, hz, rfl⟩; rw [hJcoord z hz]; exact hz.1)
    (fun q hq => (hpoints q hq).2.1)
    (by rintro _ ⟨z, hz, rfl⟩; exact hJenergy z hz)
    hVside hcurveVside hside hδproj (fun μ hμ => (hprojections μ hμ).2)
  have hSactual : (fun q : Plane × ℝ => (q.1, c + s + q.2)) '' Sfull ⊆
      range (T ∘ L ∘ e) := by
    rintro _ ⟨q, hq, rfl⟩
    rcases hq with ⟨_, ⟨z, hz, rfl⟩, rfl⟩ | ⟨⟨hqC, hqA⟩, hqt⟩
    · exact ⟨β z, (hJactual z hz).symm⟩
    · apply hreferenceWall
      refine ⟨⟨hqC, ?_⟩, ⟨by linarith only [hqt.1, hεcut], by linarith only [hqt.2, hj.2, ht₀d]⟩⟩
      rintro ⟨_, ⟨u, hu, rfl⟩, heq⟩
      exact hqA ⟨_, ⟨u, ⟨by linarith only [hu.1, hh, hh1], by linarith only [hu.2, hh, hh1]⟩, rfl⟩, heq⟩
  have hJZ : (fun q : (ℝ × ℝ) × ℝ => (B q.1, c + s + q.2)) '' (J '' Rwide) ⊆ Z := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    change (B (J z).1, c + s + (J z).2) ∈ Z
    rw [hJactual z hz, hgraph z (hRU hz)]
    apply hρZ
    apply self_subset_cthickening
    refine ⟨_, ⟨((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z), ?_, ?_⟩, rfl⟩
    · exact ⟨⟨by linarith only [hz.2.2.1, hεcut], hz.2.2.2.trans (hj.2.trans ht₀d).le⟩,
        hz.1.trans (by linarith only [hh]), by ring⟩
    · refine Prod.ext rfl ?_
      dsimp only
      ring
  obtain ⟨δgraph, hδgraph, hgraphs⟩ := exists_isOpen_graph_image_saddle_cutoff_of_isCompact
    B (G (c + s + t₀)) κ.contDiff (fun u => κ.nonneg) hs.le ht₀pos hσsq hh1 hr
    (v₀ := 2 * v₀) (by positivity) (by nlinarith only [hv₀t]) hcurveRef hVside hcurveVside
    (fun z hz hq => (hside z hz).mpr hq) hJcompact
    (fun q hq => (hpoints q hq).1)
    (fun q hq => by linarith only [(hpoints q hq).2.1, hv₀])
    (fun q hq => (hpoints q hq).2.2.2) hθformula hZ hZeq hJZ
    (fun q hq => (hpoints q hq).2.2.1.2.trans_lt hj.2)
  obtain ⟨δtrace, hδtrace, htrace⟩ := exists_disjoint_exp_smul_saddle_cutoff_trace
    B (G (c + s + t₀)) κ.contDiff (fun u => κ.nonneg) hs.le ht₀pos hσsq hh1 hr
    (v₀ := 2 * v₀) (a := -εcut / 2) (b := j) (ℓ := c + s)
    (by positivity) (by nlinarith only [hv₀t]) hcurveRef hVside hcurveVside
    (fun z hz hq => (hside z hz).mpr hq) hJcompact
    (fun q hq => (hpoints q hq).1)
    (fun q hq => by linarith only [(hpoints q hq).2.1, hv₀])
    (fun q hq => (hpoints q hq).2.2.2)
    (fun q hq => (hpoints q hq).2.2.1)
    (by rintro _ ⟨z, hz, rfl⟩; exact hJenergy z hz)
    hθformula (S := range (T ∘ L ∘ e)) (hlowerClearance.mono_right (by
      rintro q ⟨hy, ht⟩
      refine ⟨hy, ?_, ?_⟩
      · linarith only [ht.1]
      · linarith only [ht.2, hj.2]))
    (fun t ht z hz hlt hle => (hwedge t
      ⟨by linarith only [ht.1, hεcut], ht.2.trans hj.2.le⟩ z hz hlt.le hle).2 hlt)
  refine ⟨hRwide, hzeroR, hRU, hJcompact, hCcompact, hScompact, hJactual, hpoints, hsidepos, hJcoord, hSactual,
    min (min δall δgraph) δtrace, lt_min (lt_min hδall hδgraph) hδtrace, fun μ hμ => ?_⟩
  have hμold : μ ∈ Ioo (0 : ℝ) (min δall δgraph) := ⟨hμ.1, hμ.2.trans_le (min_le_left _ _)⟩
  have hμall : μ ∈ Ioo (0 : ℝ) δall := ⟨hμ.1, hμold.2.trans_le (min_le_left _ _)⟩
  have hμgraph : μ ∈ Ioo (0 : ℝ) δgraph := ⟨hμ.1, hμold.2.trans_le (min_le_right _ _)⟩
  have hμtrace : μ ∈ Ioo (0 : ℝ) δtrace := ⟨hμ.1, hμ.2.trans_le (min_le_right _ _)⟩
  have hμproj : μ ∈ Ioo (0 : ℝ) δproj := ⟨hμ.1, hμall.2.trans_le hδle⟩
  have hbm : b < m := by dsimp [b]; nlinarith only [sq_pos_of_pos hr]
  have hbaseb : c + s + t₀ < b := ht₀b
  have hrsq : r ^ 2 = 2 * (m - b) := by dsimp [b]; ring
  obtain ⟨Q, ψ, α, hα, hψd, hψhi, hQheight, hQlow, hQhi, hQcylinder, hQcap, hQwhole⟩ :=
    Diffeomorph.exists_exp_projection_quadratic_cylinder D T (G (c + s + t₀)) H
      (a := c + s + t₀) (d := (c + s + t₀ + b) / 2) (b := b) (m := m) (r := r)
      (by linarith only [hbaseb]) (by linarith only [hbaseb]) hbm hμ.1
      hrsq hD hDlo hT
  have hψmono : StrictMono ψ := strictMono_of_deriv_pos hψd
  have hψb : ψ b = b := hψhi b (by linarith only [hbaseb])
  have hQcapall := Diffeomorph.image_reference_cylinder_union_cap
    Q (G (c + s + t₀)).toEquiv ψ.toEquiv hbm hr.le hrsq
    (j := c + s + j) (by linarith only [hj.2, hbaseb])
    hψmono hψb hQwhole hQcap
  have hStime (q : Plane × ℝ) (hq : q ∈ Sfull) : q.2 ∈ Icc (-εcut / 2) j := by
    rcases hq with ⟨p, hp, rfl⟩ | hq
    · exact (hpoints p hp).2.2.1
    · exact hq.2
  have hQprojS : InjOn (fun q : Plane × ℝ => (Q (q.1, c + s + q.2)).1) Sfull :=
    Diffeomorph.injOn_fst_of_exponential_formula (G (c + s + t₀)) Q ψ id hα.ne' hQlow
      (fun q hq => (hStime q hq).2.trans hj.2.le) (hwholeProjection μ hμall)
  let Ucap : Set (Plane × ℝ) :=
    ((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
      ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})
  let K : Set (Plane × ℝ) :=
    ((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' Sfull) ∪ Ucap
  have hQprojWhole : InjOn (fun q : Plane × ℝ => (Q q).1) K := by
    apply Diffeomorph.injOn_projection_union_quadratic_cap_of_disjoint_interior Q Q.injective
      (G (c + s + t₀)) hbm hr.le hrsq
      (a := c + s - εcut / 2) (j := c + s + j) (by linarith only [hj.2, hbaseb])
      hψmono.monotone
      hψb hQwhole ?_ ?_ ?_ hQcapall.subset
    · rintro _ ⟨q, hq, rfl⟩
      exact ⟨by dsimp only; linarith only [(hStime q hq).1],
        by dsimp only; linarith only [(hStime q hq).2]⟩
    · exact hlowerClearance.mono hSactual
        (prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by linarith only [hj.2])))
    · rintro _ ⟨q, hq, rfl⟩ _ ⟨w, hw, rfl⟩ heq
      exact congrArg (fun q : Plane × ℝ => (q.1, c + s + q.2)) (hQprojS hq hw heq)
  have hclearBoth := disjoint_cylinder_and_quadratic_cap_interior D T (G (c + s + t₀))
    hbaseb.le hr hregion hinter (by simpa only [range_comp] using hwhole)
    (by simpa only [range_comp] using hlowerClearance)
  have hlowerWhole : Disjoint (range (T ∘ L ∘ e))
      (interior (G (c + s + t₀) '' closedBall 0 r) ×ˢ Icc (c + s - εcut / 2) b) := by
    simpa only [range_comp] using hclearBoth.1
  have hupperClear : Disjoint (range (T ∘ L ∘ e))
      ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 < m - ‖q.1‖ ^ 2 / 2}) := by
    simpa only [range_comp] using hclearBoth.2
  have hcapTrace := Diffeomorph.disjoint_vertical_trace_of_quadratic_cap
    (D.trans T) Q (G (c + s + t₀)) ψ hbm hr hrsq
    hψmono hψb hQheight hQwhole
    (fun z hz => hQhi z (by linarith only [hz, hbaseb])) hlowerWhole hupperClear
  have hwholeTrace : ∀ q ∈ K, ∀ t ∈ Ico (c + s - εcut / 2) q.2,
      Q.symm ((Q q).1, ψ t) ∉ range (T ∘ L ∘ e) :=
    disjoint_vertical_trace_of_source_neck_cap B (G (c + s + t₀)) Q ψ hj.2.le hbaseb.le
      (fun w hw => (hpoints w hw).2.2.1.2) sdiff_subset hQlow hQcylinder
      (fun q hq => (hQcapall.subset hq).2) (htrace μ hμtrace) hcapTrace
  refine ⟨(hprojections μ hμproj).1, (hprojections μ hμproj).2, hwholeProjection μ hμall,
    Q, ψ, α, hα, hψd, hψhi, hQheight, hQlow, hQhi, hQcylinder, hQcap, hQwhole, hQcapall, ?_, hQprojS, hQprojWhole, hwholeTrace, ?_⟩
  · apply Diffeomorph.injOn_fst_of_exponential_formula
      (G (c + s + t₀)) Q ψ B hα.ne' hQlow ?_ (hprojections μ hμproj).2
    intro q hq
    rcases hq with hq | ⟨w, hw, rfl⟩
    · exact (hpoints q hq).2.2.1.2.trans hj.2.le
    · exact hw.2.2.2.trans hj.2.le
  · have hwholeGraph : IsCompact K ∧ ∃ OQ : Set Plane, IsOpen OQ ∧ ∃ gQ : Plane → ℝ,
        ContDiffOn ℝ ∞ gQ OQ ∧ ∃ WQ : Set (Plane × ℝ), IsOpen WQ ∧
          Q '' K ⊆ WQ ∩ Q '' range (T ∘ L ∘ e) ∧ WQ ⊆ {q | q.1 ∈ OQ} ∧
          WQ ∩ Q '' range (T ∘ L ∘ e) = WQ ∩ {q | q.2 = gQ q.1} := by
      exact exists_isOpen_graph_cutoff_source_neck_cap he B D T A Q ψ G
        hs hh hh1 ht₀pos ht₀d hdδ hεcut hσsq hbaseb.le hbm hr.le hrsq hψmono hψb
        hQwhole hQcap Φ η (fun t ht u => (hslices t ht).2 u)
        hgraph hθ1 hKV hTmodel hrawU hTarc hcircleRef hwhole hinter j hj
        (J '' Rwide) Z hScompact hSactual (hgraphs μ hμgraph Q ψ α hα hQlow)
        hreferenceWall hQprojWhole
    rcases hwholeGraph with ⟨hKcompact, OQ, hOQ, gQ, hgQ, WQ, hWQ, hKWQ, hWQO, hWQeq⟩
    exact @exists_saddle_cutoff_graph_boundary_collars e B β U hU c s hs hgraph p σ h
      hh hh1 δ hδ r hr G t₀ ht₀δ d ht₀d εcut
      hεcut hεcuth θ hθ01 hθ1 κ hκout D hD T hTheight V
      hKV hVreg hTmodel ρ hmodelRect hclear ht₀pos hσsq hreferenceWall Vside hVside hcurveVside
      hside hcurveRef v₀ hv₀ hv₀t j hj hzeroR hRU hpoints hsidepos
      hJenergy hbm hbaseb hrsq Q ψ hψd hQheight hQcap hQwhole hψmono hψb
      hStime hQprojS hQprojWhole hKcompact OQ hOQ gQ hgQ WQ hWQ hKWQ hWQO
      hWQeq
      (by
        have hc := (isCompact_range
          (Q.continuous.comp (T.continuous.comp (L.continuous.comp he.contMDiff.continuous)))).isClosed
        simpa only [← range_comp, Function.comp_def] using hc)
      hwholeTrace he


theorem exists_height_preserving_diffeomorph_saddle_cutoff_graph_and_cap_of_one_saddle
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
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
      let τ := δ / 2
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ η : unitInterval → SphereTwo, ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
      let γ := fun q : ℝ × unitInterval => (L (e (Φ (q.1 - τ) (η q.2)))).1
      ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)) ∧
          ∀ u, e (Φ (t - τ) (η u)) 2 = c + s + t) ∧
        (∀ t ∈ Ioc (0 : ℝ) δ,
          IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
            (B (saddleBandLevelCurve s t σ h))
            (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
            (range (fun u => γ (t, u)))) ∧
      ∃ r : ℝ, 0 < r ∧
      let m := e p 2
      let b := m - r ^ 2 / 2
      c + s + τ < b ∧
      ∃ A : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ z, (A z).2 = z.2) ∧
        (L ∘ e) '' connectedComponentIn {x | b ≤ e x 2} p =
          (fun y => A (y, m + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
      ∃ G : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => G z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (G z.1).symm z.2) ∧
        (∀ t ∈ Icc τ (b - (c + s)), C t = G (c + s + t) '' sphere 0 r) ∧
        (∀ t ∈ Icc (c + s + τ) b,
          (G t '' closedBall 0 r) ∩ ((fun x => (L (e x)).1) '' {x | e x 2 = t}) =
            G t '' sphere 0 r) ∧
      ∃ t₀ : ℝ, τ < t₀ ∧ t₀ < δ ∧ c + s + t₀ < b ∧
      ∃ d : ℝ, t₀ < d ∧ d < δ ∧
      ∃ ε > 0, ε < t₀ / 4 ∧ ε < s * h ^ 2 / 16 ∧
      ∃ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ ∧ (∀ q, θ q ∈ Icc (0 : ℝ) 1) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
      ∃ κ : ContDiffBump (0 : ℝ), κ.rIn = h / 4 ∧ κ.rOut = h / 2 ∧
        (∀ t u, θ (t, u) =
          1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u) ∧
      ∃ ν > 0, Ioo (t₀ - ν) (t₀ + ν) ⊆ Ioo τ (min δ (b - (c + s))) ∧
      ∃ H : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
        H (c + s + t₀) = G (c + s + t₀) ∧
        (∀ t, c + s + t₀ - ν < t → H t '' closedBall 0 r = G t '' closedBall 0 r) ∧
      ∃ D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ z, (D z).2 = z.2) ∧
        (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b m x t, t) = (H t x, t)) ∧
        (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : Plane) ρ, D (x, t) = A (x, t)) ∧
        D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 ≤ m - ‖z.1‖ ^ 2 / 2} =
          heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∧
        heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∩ range (L ∘ e) =
          D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2} ∧
      ∃ T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
        (∀ z, T z = (G (c + s + t₀) ((H z.2).symm z.1), z.2)) ∧
        (∀ z, (T z).2 = z.2) ∧
        (∀ y, T (y, c + s + t₀) = (y, c + s + t₀)) ∧
        (∀ t ∈ Icc (-d) d, ∀ u,
          T (γ (t, u), c + s + t) = (γ (t₀, u), c + s + t)) ∧
        ((G (c + s + t₀) '' closedBall 0 r) ×ˢ Icc (c + s + t₀) b) ∩
            range (T ∘ L ∘ e) =
          (G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + t₀) b ∧
      ∃ V : Set (ℝ × (ℝ × ℝ)), IsOpen V ∧
        {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
          (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V ∧
        (∀ q ∈ V, θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
          (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
            0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (t₀ - q.1)) /
              q.2.2 ^ 2)) ∧
        (∀ q ∈ V, T (B q.2, c + s + q.1) =
          (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1)) ∧
        (∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U) ∧
      let K : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
        (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}
      ∃ Z : Set (Plane × ℝ), IsOpen Z ∧
        Z ⊆ T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' V) ∧
        Z ∩ range (T ∘ L ∘ e) =
          Z ∩ {q | (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
            s + (q.2 - (c + s)) +
              θ (q.2 - (c + s), (B.symm q.1).1) * (t₀ - (q.2 - (c + s)))} ∧
        ∃ ρ > 0, cthickening ρ
          (T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' K)) ⊆ Z ∧
        cthickening ρ (T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) ''
          {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
            s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
              (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
                s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)})) ⊆ Z ∧
      ∃ R > 0, Icc (-h) h ×ˢ Icc (-R) R ⊆ U ∧
        (∀ t ∈ Icc (-δ) δ, ∀ σ' : ℝ, σ' ^ 2 = 1 → ∀ u ∈ Icc (-h) h,
          saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-R) R) ∧
        (∀ a < t₀, ∃ ρ > 0, cthickening ρ
          (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-R) R ∧
            (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
          (G (c + s + t₀) '' closedBall 0 r)ᶜ) ∧
      ∃ O : Set (ℝ × ℝ), IsOpen O ∧ ∃ g : (ℝ × ℝ) → ℝ,
        ContDiffOn ℝ ∞ g O ∧ (∀ z ∈ O, g z ∈ Ioo (-ε) (t₀ / 2)) ∧
        ∃ W : Set (Plane × ℝ), IsOpen W ∧ W ⊆ Z ∧
          W ⊆ {q | B.symm q.1 ∈ O ∧ q.2 - (c + s) ∈ Ioo (-ε) (t₀ / 2)} ∧
          T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) ''
            {q | q.1 ∈ Ioo (-ε) (t₀ / 2) ∧ |q.2.1| < h / 2 ∧
              (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}) ⊆ W ∧
          W ∩ range (T ∘ L ∘ e) = W ∩ {q | q.2 = c + s + g (B.symm q.1)} ∧
      ∃ N : Set (Plane × ℝ), IsOpen N ∧
        frontier (G (c + s + t₀) '' closedBall 0 r) ×ˢ
          Icc (c + s - ε / 2) (c + s + t₀) ⊆ N ∧
        N ∩ range (T ∘ L ∘ e) ⊆
          (interior (G (c + s + t₀) '' closedBall 0 r))ᶜ ×ˢ univ ∧
        Disjoint (range (T ∘ L ∘ e))
          (interior (G (c + s + t₀) '' closedBall 0 r) ×ˢ
            Icc (c + s - ε / 2) (c + s + t₀)) ∧
        (∀ t ∈ Icc (-ε) t₀, ∀ z : ℝ × ℝ, |z.1| ≤ h →
          s + t + θ (t, z.1) * (t₀ - t) ≤
            (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + t₀ →
          (B z, c + s + t) ∈ Z ∧
            (s + t + θ (t, z.1) * (t₀ - t) <
              (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
              (B z, c + s + t) ∉ range (T ∘ L ∘ e))) ∧
      ∃ Vside : Set (ℝ × ℝ), IsOpen Vside ∧
        saddleBandLevelCurve s t₀ σ '' Ioo (-h) h ⊆ Vside ∧
        Vside ⊆ Ioo (-h) h ×ˢ Ioo (-R) R ∧
        (∀ z ∈ Vside, B z ∈ G (c + s + t₀) '' closedBall 0 r ↔
          s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) ∧
    ∃ v₀ > 0, v₀ ^ 2 / 2 < t₀ / 4 ∧
      ∀ j ∈ Ioo (t₀ / 2) t₀,
      let R : Set (ℝ × ℝ) := saddleCutoffHalfBand s h v₀ σ ε j
      let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := saddleCutoffModelMap B T c s
      let C : Set ((ℝ × ℝ) × ℝ) :=
        (fun q : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ q.1, q.2)) ''
          {q | |q.1| ≤ 7 * h / 8 ∧ h / 2 ≤ |q.1| ∧ q.2 ∈ Icc (-ε / 2) j}
      let S : Set (Plane × ℝ) := saddleCutoffSource B T G c s t₀ r h v₀ σ ε j
      IsCompact R ∧ (0, 0) ∈ interior R ∧ R ⊆ U ∧
        IsCompact (J '' R) ∧ IsCompact C ∧ IsCompact S ∧
        (∀ z ∈ R, (B (J z).1, c + s + (J z).2) =
          T (L (e (β z)))) ∧
        (∀ p ∈ J '' R, p.1.1 ∈ Ioo (-h) h ∧ -v₀ ≤ σ * p.1.2 ∧ p.2 ∈ Icc (-ε / 2) j ∧
          (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
            κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - t₀ / 4) / (t₀ / 4))) *
              (t₀ - p.2)) = 0) ∧
        (∀ z ∈ R, |z.1| = 5 * h / 8 → 0 < σ * z.2) ∧
        (∀ z ∈ R, (J z).1.1 = z.1) ∧
        (fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S ⊆ range (T ∘ L ∘ e) ∧
        ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
          InjOn (fun z => Real.exp (-μ * (J z).2) •
            (G (c + s + t₀)).symm ((T (L (e (β z)))).1)) R ∧
          InjOn (fun p : (ℝ × ℝ) × ℝ => Real.exp (-μ * p.2) •
            (G (c + s + t₀)).symm (B p.1)) ((J '' R) ∪ C) ∧
          InjOn (fun q : Plane × ℝ => Real.exp (-μ * q.2) •
            (G (c + s + t₀)).symm q.1) S ∧
          ∃ (Q : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ) (α : ℝ),
            0 < α ∧ (∀ t, 0 < deriv ψ t) ∧
            (∀ t, (c + s + t₀ + b) / 2 ≤ t → ψ t = t) ∧
            (∀ q, (Q q).2 = ψ q.2) ∧
            (∀ t ≤ c + s + t₀, ∀ y, Q (y, t) =
              ((α * Real.exp (-μ * t)) • (G (c + s + t₀)).symm y, ψ t)) ∧
            (∀ q, (c + s + t₀ + b) / 2 ≤ q.2 → Q q = (D.trans T).symm q) ∧
            Q '' ((G (c + s + t₀) '' sphere 0 r) ×ˢ Iic b) ⊆
              {q : Plane × ℝ | q.2 = m - ‖q.1‖ ^ 2 / 2} ∧
            Q '' ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}) =
              {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} ∧
            (∀ t ≤ b, ∀ y, Q (y, t) =
              (quadraticLevelScaling b m ((G (c + s + t₀)).symm y) (ψ t), ψ t)) ∧
            Q '' (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
              ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2})) =
                {q : Plane × ℝ | ψ (c + s + j) ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2} ∧
            InjOn (fun q : (ℝ × ℝ) × ℝ => (Q (B q.1, c + s + q.2)).1) ((J '' R) ∪ C) ∧
            InjOn (fun q : Plane × ℝ => (Q (q.1, c + s + q.2)).1) S ∧
            InjOn (fun q : Plane × ℝ => (Q q).1)
              (((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                  ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))) ∧
            (∀ q ∈ (((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                  ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))),
              ∀ t ∈ Ico (c + s - ε / 2) q.2,
                Q.symm ((Q q).1, ψ t) ∉ range (T ∘ L ∘ e)) ∧
            (∃ OQ : Set Plane, IsOpen OQ ∧ ∃ gQ : Plane → ℝ, ContDiffOn ℝ ∞ gQ OQ ∧
              ∃ WQ : Set (Plane × ℝ), IsOpen WQ ∧
                Q '' (((fun q : Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪
                  (((G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + j) b) ∪
                    ((D.trans T) '' {q : Plane × ℝ | b ≤ q.2 ∧ q.2 = m - ‖q.1‖ ^ 2 / 2}))) ⊆
                      WQ ∩ Q '' range (T ∘ L ∘ e) ∧
                WQ ⊆ {q | q.1 ∈ OQ} ∧
                WQ ∩ Q '' range (T ∘ L ∘ e) = WQ ∩ {q | q.2 = gQ q.1} ∧
                let K := saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ ε j b m
                let P := fun z : ℝ × ℝ =>
                  (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
                (∀ x ∈ P '' {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} ∪
                    (fun y => (Q (y, c + s + (-ε / 2))).1) ''
                      (G (c + s + t₀) '' sphere 0 r \ B ''
                        (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))),
                    gQ x = ψ (c + s + (-ε / 2)) ∧ fderiv ℝ gQ x ≠ 0) ∧
                let Y := (fun q : Plane × ℝ => (Q q).1) '' K
                ∃ k : Plane → ℝ, ContDiff ℝ ∞ k ∧ (∀ y, fderiv ℝ k y ≠ 0) ∧
                  (∀ y ∈ Y, ψ (c + s + (-ε / 2)) ≤ k y ∧ k y ≤ gQ y) ∧
                  ∃ Acut : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
                    (∀ q, (Acut q).1 = q.1) ∧ (∀ y ∈ Y, Acut (y, gQ y) = (y, k y)) ∧
                    (∀ q ∈ Q '' range (T ∘ L ∘ e),
                      q ∉ WQ ∩ {q | q.1 ∈ interior Y} →
                      (Acut : (Plane × ℝ) → Plane × ℝ) =ᶠ[𝓝 q] id) ∧
                    (∀ x, IsCriticalPointAt (𝓡 2) (fun y => (Acut (Q (T (L (e y))))).2) x →
                      x ≠ β (0, 0) ∧
                        (fun y => (Acut (Q (T (L (e y))))).2) =ᶠ[𝓝 x] (fun y => ψ (e y 2)))) ∧
                let K := saddleCutoffSurfacePatch B D T G c s t₀ r h v₀ σ ε j b m
                let P := fun z : ℝ × ℝ =>
                  (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
                let Cboundary := P '' {z ∈ R | σ * z.2 = -v₀ ∨
                    (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} ∪
                  (fun y => (Q (y, c + s + (-ε / 2))).1) ''
                    (G (c + s + t₀) '' sphere 0 r \ B ''
                      (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))
                IsCompact K ∧ Schoenflies.IsJordanCurve Cboundary ∧
                  (fun q : Plane × ℝ => (Q q).1) '' K = closure (Schoenflies.inside Cboundary) ∧
                  frontier ((fun q : Plane × ℝ => (Q q).1) '' K) = Cboundary ∧
                  let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * (-ε / 2)) / (v₀ ^ 2 + 2 * s))
                  Schoenflies.IsCutPair Cboundary (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀)))
                    (P '' {z ∈ R | σ * z.2 = -v₀})
                    (P '' {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} ∪
                      (fun y => (Q (y, c + s + (-ε / 2))).1) ''
                        (G (c + s + t₀) '' sphere 0 r \ B ''
                          (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8)))) := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
      η, hη, Φ, hΦ, hΦi, hΦ0, hγ, hslices, hcoverage,
      r, hr, hab, A, hA, hcap, G, hG, hGi, hCcap, hcontact,
      t₀, hτt₀, ht₀δ, ht₀b, d, ht₀d, hdδ, εcut, hεcut, hεcutt, hεcuth,
      θ, hθ, hθ01, hθ0, hθ1, hθzero, κ, hκin, hκout, hθformula, ν, hν, hνsub,
      H, hH, hHi, hH₀, hHdisk, D, hD, hDlo, hDhi, hregion, hinter,
      T, hT, hTheight, hTbase, hTarc, hwhole, V, hV, hKV, hVreg, hTmodel,
      hrawU, Z, hZ, hZT, hZeq, ρclear, hρclear, hρZ, hρfilledZ,
      ρ, hρ, hrectangle, hmodelRect, hclear, O, hO, g, hg, hgt,
      Wgraph, hWgraph, hWZ, hWO, hactive, hgrapheq, hcontactRect⟩ :=
    exists_height_preserving_diffeomorph_saddle_cutoff_model_and_cap_of_one_saddle he hnd hinj hone hconn
      B hU hzero hβ hs hgraph hβcrit hβindex
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let γ := fun q : ℝ × unitInterval => (L (e (Φ (q.1 - δ / 2) (η q.2)))).1
  have ht₀pos : 0 < t₀ := (half_pos hδ).trans hτt₀
  have hσsq : σ ^ 2 = 1 := by
    rcases hσ with hσ | hσ
    · rw [hσ]; norm_num
    · rw [mem_singleton_iff.mp hσ]; norm_num
  let Kfilled : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Icc (-εcut) d ∧ |q.2.1| ≤ h ∧
    s + q.1 ≤ (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 ≤
        s + q.1 + (1 - θ (q.1, q.2.1)) * (t₀ - q.1)}
  have hKfilledV : Kfilled ⊆ V := by
    intro q hq
    have hqZ := hρfilledZ (self_subset_cthickening _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩)
    obtain ⟨_, ⟨q', hq'V, rfl⟩, hTeq⟩ := hZT hqZ
    have hphys := T.injective hTeq
    have hspace := B.injective (congrArg Prod.fst hphys)
    have htime := congrArg Prod.snd hphys
    have hqeq : q' = q := Prod.ext (add_left_cancel htime) hspace
    rwa [hqeq] at hq'V
  have hcutRef := hcoverage t₀ ⟨ht₀pos, ht₀δ.le⟩
  have hcircleCapRef := hCcap t₀ ⟨hτt₀.le, by linarith only [ht₀b]⟩
  have heT : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, Plane × ℝ) ∞ (T ∘ L ∘ e) :=
    (he.continuousLinearEquiv_comp L).diffeomorph_comp T
  have hcircleRef : G (c + s + t₀) '' sphere 0 r =
      B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ∪ range (fun u => γ (t₀, u)) :=
    hcircleCapRef.symm.trans hcutRef.union_eq.symm
  have hreferenceWall := reference_cylinder_subset_range_of_cutoff_graph (L ∘ e) B T β
    (fun q : ℝ × unitInterval => Φ (q.1 - δ / 2) (η q.2)) hs.le hh.le hh1 ht₀pos.le hεcuth
    (by linarith only [hεcutt, ht₀d, hdδ, ht₀pos])
    (by linarith only [hεcutt, ht₀d, ht₀pos]) hdδ.le hσsq
    (fun t u hu => hθ1 t u (Or.inr hu)) hgraph hrawU hKV hTmodel
    (fun t ht u => (hslices t ht).2 u) hTarc hcircleRef
  obtain ⟨Wouter, hWouter, hWouterEq⟩ := exists_isOpen_inter_range_eq_reference_outer_strip
    heT B (G (c + s + t₀)) hs.le hh hh1 ht₀pos hr hreferenceWall
  have hclosingRef := closing_arc_inter_saddle_rectangle_subset_endpoints B (fun u => γ (t₀, u))
    (fun u => hcontactRect t₀ ⟨(neg_nonpos.mpr hδ.le).trans ht₀pos.le, ht₀δ.le⟩ u)
  have hoppositeRef := saddleBandLevelCurve_subset_height_projection_of_graph (L ∘ e) B
    hs.le ht₀pos hh1 (by simpa only [neg_sq] using hσsq : (-σ) ^ 2 = 1) hgraph
    (fun u hu => hrectangle (hmodelRect t₀
      ⟨(neg_nonpos.mpr hδ.le).trans ht₀pos.le, ht₀δ.le⟩ (-σ)
      (by simpa only [neg_sq] using hσsq) u hu))
  obtain ⟨Vside, hVside, hcurveVside, hVsideRect, hside⟩ :=
    exists_reference_cap_side B (G (c + s + t₀)) hs.le ht₀pos ht₀δ hσsq hh1 hr
      hcircleRef hclosingRef (hcontact (c + s + t₀) ⟨add_le_add le_rfl hτt₀.le, ht₀b.le⟩)
      hoppositeRef (by
        rintro _ ⟨u, hu, rfl⟩
        exact hmodelRect t₀ ⟨(neg_nonpos.mpr hδ.le).trans ht₀pos.le, ht₀δ.le⟩ (-σ)
          (by simpa only [neg_sq] using hσsq) u hu)
      (fun u hu => hmodelRect δ ⟨neg_le_self hδ.le, le_rfl⟩ σ hσsq u hu)
  have hfilledModelZ : (fun q : ℝ × (ℝ × ℝ) =>
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1)) '' Kfilled ⊆ Z := by
    rintro _ ⟨q, hq, rfl⟩
    change (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1) ∈ Z
    rw [← hTmodel q (hKfilledV hq)]
    exact hρfilledZ (self_subset_cthickening _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩)
  obtain ⟨Ncollar, hNcollar, hboundaryCollar, hcollar⟩ :=
    exists_isOpen_boundary_collar_disjoint_cap_interior B.toHomeomorph
      (G (c + s + t₀)).toHomeomorph hs ht₀pos ht₀δ ht₀d hεcut hεcuth hh hh1 hσsq
      hθ01 hθ0 hθ1 hcircleRef hclosingRef
      (hcontact (c + s + t₀) ⟨add_le_add le_rfl hτt₀.le, ht₀b.le⟩) hoppositeRef
      (by
        rintro _ ⟨u, hu, rfl⟩
        exact hmodelRect t₀ ⟨(neg_nonpos.mpr hδ.le).trans ht₀pos.le, ht₀δ.le⟩ (-σ)
          (by simpa only [neg_sq] using hσsq) u hu)
      (fun u hu => hmodelRect δ ⟨neg_le_self hδ.le, le_rfl⟩ σ hσsq u hu)
      hZ hWouter hWouterEq hfilledModelZ hZeq
  have hcollarProd : Ncollar ∩ range (T ∘ L ∘ e) ⊆
      (interior (G (c + s + t₀) '' closedBall 0 r))ᶜ ×ˢ univ :=
    fun q hq => ⟨hcollar hq, mem_univ _⟩
  have hlowerClearance := disjoint_cap_interior_below_of_one_saddle he hnd hinj hone
    hpmax hpnotmax T (G (c + s + t₀)) (r := r) (a := c + s - εcut / 2)
    (b := c + s + t₀) (d := e p 2 - r ^ 2 / 2) ht₀b.le
    (by have hsq := sq_nonneg r; linarith only [ht₀b, hsq])
    hTheight hwhole hNcollar hboundaryCollar hcollarProd
  have hwedge : ∀ t ∈ Icc (-εcut) t₀, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      s + t + θ (t, z.1) * (t₀ - t) ≤
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + t₀ →
      (B z, c + s + t) ∈ Z ∧
        (s + t + θ (t, z.1) * (t₀ - t) <
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
          (B z, c + s + t) ∉ range (T ∘ L ∘ e)) :=
    saddle_cutoff_wedge_mem_and_not_mem B.toEquiv hs hh1 ht₀pos ht₀d.le hεcuth hθ01 hθ0
      hfilledModelZ hZeq
  have hcurveRef (u : ℝ) (hu : u ∈ Ioo (-h) h) :
      B (saddleBandLevelCurve s t₀ σ u) ∈ G (c + s + t₀) '' sphere 0 r :=
    hcircleCapRef.subset (hcutRef.fst_subset ⟨_, ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩, rfl⟩)
  obtain ⟨v₀, hv₀, hv₀t, hwide⟩ := exists_injOn_exp_smul_saddle_band_cutoff_on_half_band
    B (G (c + s + t₀)) T hs hh hh1 hεcut hεcuth ht₀pos ht₀d hσsq hr
    κ hκout hθ0 hθformula hKV hVreg hTmodel hrawU hTheight
    hcurveRef hVside hcurveVside (fun z hz hq => (hside z hz).mpr hq)
    (fun z => L (e (β z))) hgraph
  refine ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
    η, hη, Φ, hΦ, hΦi, hΦ0, hγ, hslices, hcoverage,
    r, hr, hab, A, hA, hcap, G, hG, hGi, hCcap, hcontact,
    t₀, hτt₀, ht₀δ, ht₀b, d, ht₀d, hdδ, εcut, hεcut, hεcutt, hεcuth,
    θ, hθ, hθ01, hθ0, hθ1, hθzero, κ, hκin, hκout, hθformula, ν, hν, hνsub,
    H, hH, hHi, hH₀, hHdisk, D, hD, hDlo, hDhi, hregion, hinter,
    T, hT, hTheight, hTbase, hTarc, hwhole, V, hV, hKV, hVreg, hTmodel,
    hrawU, Z, hZ, hZT, hZeq, ρclear, hρclear, hρZ, hρfilledZ,
    ρ, hρ, hrectangle, hmodelRect, hclear, O, hO, g, hg, hgt,
    Wgraph, hWgraph, hWZ, hWO, hactive, hgrapheq,
    Ncollar, hNcollar, hboundaryCollar, hcollarProd, hlowerClearance, hwedge,
    Vside, hVside, hcurveVside, hVsideRect, hside, v₀, hv₀, hv₀t, ?_⟩
  exact @exists_cutoff_projection_graph_and_boundary_collars e he B β U hU c s hs hgraph p σ
    h hh hh1 δ hδ η Φ hslices r hr A G
    t₀ ht₀δ ht₀b d ht₀d hdδ εcut hεcut hεcuth θ hθ01 hθ1
    κ hκout hθformula H D hD hDlo hregion hinter T hT hTheight
    hTarc hwhole V hKV hVreg hTmodel hrawU Z hZ hZeq ρclear hρZ
    ρ hmodelRect hclear ht₀pos hσsq hreferenceWall hcircleRef Vside hVside hcurveVside hside hlowerClearance hwedge
    hcurveRef v₀ hv₀ hv₀t hwide


theorem exists_height_preserving_diffeomorph_saddle_cutoff_and_cap_of_one_saddle
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
      ∃ σ ∈ ({-1, 1} : Set ℝ), ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
      let τ := δ / 2
      let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
      let C := fun t => (fun x => (L (e x)).1) ''
        (connectedComponentIn {x | c + s + t ≤ e x 2} p ∩ {x | e x 2 = c + s + t})
      ∃ η : unitInterval → SphereTwo, ContMDiff (𝓡∂ 1) (𝓡 2) ∞ η ∧
      ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => Φ q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × SphereTwo => (Φ q.1).symm q.2) ∧
        Φ 0 = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
      let γ := fun q : ℝ × unitInterval => (L (e (Φ (q.1 - τ) (η q.2)))).1
      ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ ∧
        (∀ t ∈ Icc (-δ) δ,
          IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)) ∧
          ∀ u, e (Φ (t - τ) (η u)) 2 = c + s + t) ∧
        (∀ t ∈ Ioc (0 : ℝ) δ,
          IsCutPair (C t) (B (saddleBandLevelCurve s t σ (-h)))
            (B (saddleBandLevelCurve s t σ h))
            (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h))
            (range (fun u => γ (t, u)))) ∧
      ∃ r : ℝ, 0 < r ∧
      let m := e p 2
      let b := m - r ^ 2 / 2
      c + s + τ < b ∧
      ∃ A : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ z, (A z).2 = z.2) ∧
        (L ∘ e) '' connectedComponentIn {x | b ≤ e x 2} p =
          (fun y => A (y, m + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
      ∃ G : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => G z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (G z.1).symm z.2) ∧
        (∀ t ∈ Icc τ (b - (c + s)), C t = G (c + s + t) '' sphere 0 r) ∧
        (∀ t ∈ Icc (c + s + τ) b,
          (G t '' closedBall 0 r) ∩ ((fun x => (L (e x)).1) '' {x | e x 2 = t}) =
            G t '' sphere 0 r) ∧
      ∃ t₀ : ℝ, τ < t₀ ∧ t₀ < δ ∧ c + s + t₀ < b ∧
      ∃ d : ℝ, t₀ < d ∧ d < δ ∧
      ∃ ε > 0, ε < t₀ / 4 ∧ ε < s * h ^ 2 / 16 ∧
      ∃ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ ∧ (∀ q, θ q ∈ Icc (0 : ℝ) 1) ∧
        (∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0) ∧
        (∀ t u, t₀ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1) ∧
        (∀ t u, t < t₀ / 4 → |u| < h / 4 → (t, u) ∉ tsupport θ) ∧
      ∃ ν > 0, Ioo (t₀ - ν) (t₀ + ν) ⊆ Ioo τ (min δ (b - (c + s))) ∧
      ∃ H : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × Plane => (H z.1).symm z.2) ∧
        H (c + s + t₀) = G (c + s + t₀) ∧
        (∀ t, c + s + t₀ - ν < t → H t '' closedBall 0 r = G t '' closedBall 0 r) ∧
      ∃ D : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ), (∀ z, (D z).2 = z.2) ∧
        (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b m x t, t) = (H t x, t)) ∧
        (∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ ball (0 : Plane) ρ, D (x, t) = A (x, t)) ∧
        D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 ≤ m - ‖z.1‖ ^ 2 / 2} =
          heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∧
        heightCapRegion (fun t => G t) A (c + s + t₀) b m r ∩ range (L ∘ e) =
          D '' {z | c + s + t₀ ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2} ∧
      ∃ T : (Plane × ℝ) ≃ₘ[ℝ] (Plane × ℝ),
        (∀ z, T z = (G (c + s + t₀) ((H z.2).symm z.1), z.2)) ∧
        (∀ z, (T z).2 = z.2) ∧
        (∀ y, T (y, c + s + t₀) = (y, c + s + t₀)) ∧
        (∀ t ∈ Icc (-d) d, ∀ u,
          T (γ (t, u), c + s + t) = (γ (t₀, u), c + s + t)) ∧
        ((G (c + s + t₀) '' closedBall 0 r) ×ˢ Icc (c + s + t₀) b) ∩
            range (T ∘ L ∘ e) =
          (G (c + s + t₀) '' sphere 0 r) ×ˢ Icc (c + s + t₀) b ∧
      ∃ V : Set (ℝ × (ℝ × ℝ)), IsOpen V ∧
        {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
          (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V ∧
        (∀ q ∈ V, θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
          (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
            0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (t₀ - q.1)) /
              q.2.2 ^ 2)) ∧
        (∀ q ∈ V, T (B q.2, c + s + q.1) =
          (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1)) ∧
        (∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U) ∧
      let K : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
        (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1}
      ∃ Z : Set (Plane × ℝ), IsOpen Z ∧
        Z ⊆ T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' V) ∧
        Z ∩ range (T ∘ L ∘ e) =
          Z ∩ {q | (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
            s + (q.2 - (c + s)) +
              θ (q.2 - (c + s), (B.symm q.1).1) * (t₀ - (q.2 - (c + s)))} ∧
        ∃ ρ > 0, cthickening ρ
          (T '' ((fun q : ℝ × (ℝ × ℝ) => (B q.2, c + s + q.1)) '' K)) ⊆ Z := by
  obtain ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
      η, hη, Φ, hΦ, hΦi, hΦ0, hγ, hslices, hcoverage,
      r, hr, hab, A, hA, hcap, G, hG, hGi, hCcap, hcontact,
      t₀, hτt₀, ht₀δ, ht₀b, d, ht₀d, hdδ, ε, hε, hεt, hεh,
      θ, hθ, hθ01, hθ0, hθ1, hθzero, _, _, _, _, ν, hν, hνsub,
      H, hH, hHi, hH₀, hHdisk, D, hD, hDlo, hDhi, hregion, hinter,
      T, hT, hTheight, hTbase, hTarc, hwhole, V, hV, hKV, hVreg, hTmodel,
      hrawU, Z, hZ, hZT, hZeq, ρ, hρ, hρZ, _, _⟩ :=
    exists_height_preserving_diffeomorph_saddle_cutoff_graph_and_cap_of_one_saddle
      he hnd hinj hone hconn B hU hzero hβ hs hgraph hβcrit hβindex
  exact ⟨p, hpmax, hpnd, hpnotmax, σ, hσ, h, hh, hh1, δ, hδ,
    η, hη, Φ, hΦ, hΦi, hΦ0, hγ, hslices, hcoverage,
    r, hr, hab, A, hA, hcap, G, hG, hGi, hCcap, hcontact,
    t₀, hτt₀, ht₀δ, ht₀b, d, ht₀d, hdδ, ε, hε, hεt, hεh,
    θ, hθ, hθ01, hθ0, hθ1, hθzero, ν, hν, hνsub,
    H, hH, hHi, hH₀, hHdisk, D, hD, hDlo, hDhi, hregion, hinter,
    T, hT, hTheight, hTbase, hTarc, hwhole, V, hV, hKV, hVreg, hTmodel,
    hrawU, Z, hZ, hZT, hZeq, ρ, hρ, hρZ⟩

end DifferentialGeometry.Topology.SphereSeparation
