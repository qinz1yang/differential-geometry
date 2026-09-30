import DifferentialGeometry.Topology.Engulfing.Local.Charts.LocalReplacement
import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexNeighborhood

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry
open scoped _root_.Topology ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem subcomplex_space_subset (K D : SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces) :
    D.space ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact K.convexHull_subset_space (hDK hs) hxs

def subcomplexInclusion (K D : SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces) :
    C(D.space, K.space) :=
  ⟨fun x => ⟨x.1, subcomplex_space_subset K D hDK x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

omit [FiniteDimensional ℝ E] in
theorem subcomplex_inf_space (K D L : SimplicialComplex ℝ E)
    (hDK : D.faces ⊆ K.faces) (hLK : L.faces ⊆ K.faces) :
    (D ⊓ L).space = D.space ∩ L.space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact ⟨D.convexHull_subset_space hs.1 hxs, L.convexHull_subset_space hs.2 hxs⟩
  · rintro x ⟨hxD, hxL⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hxD
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxL
    have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using K.inter_subset_convexHull (hDK hs) (hLK ht) ⟨hxs, hxt⟩
    have hne : (s ∩ t).Nonempty := by exact_mod_cast convexHull_nonempty_iff.mp ⟨x, hxst⟩
    exact (D ⊓ L).convexHull_subset_space
      ⟨D.down_closed hs Finset.inter_subset_left hne,
        L.down_closed ht Finset.inter_subset_right hne⟩ hxst

section ChartMetric

variable {X M F : Type*} [TopologicalSpace X] [NormalSpace X] [PseudoMetricSpace M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_chart_blend_tolerance (e : OpenPartialHomeomorph M F) (c : F)
    {r R ε : ℝ} (hrR : r < R) (hR : closedBall c R ⊆ e.target) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ R - r ∧
      ∀ {A B U : Set X}, IsClosed A → IsClosed B → IsOpen U → B ⊆ U → U ⊆ interior A →
      ∀ (g : C(X, M)) (f : C(A, F)),
      (∀ x : A, g x ∈ e.source) →
      (∀ x : A, e (g x) ∈ closedBall c r) →
      (∀ x : A, ‖f x - e (g x)‖ < η) →
      ∃ G : C(X, M),
        (∀ x : A, x.1 ∈ B → G x = e.symm (f x)) ∧
        (∀ x ∉ U, G x = g x) ∧
        (∀ x : A, f x = e (g x) → G x = g x) ∧
        (∀ x, dist (G x) (g x) < ε) ∧
        (∀ x : A, G x ∈ e.source) := by
  have huc : UniformContinuousOn e.symm (closedBall c R) :=
    (isCompact_closedBall c R).uniformContinuousOn_of_continuous (e.continuousOn_symm.mono hR)
  obtain ⟨δ, hδ, heδ⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let η := min δ (R - r)
  have hη : 0 < η := lt_min hδ (sub_pos.mpr hrR)
  refine ⟨η, hη, min_le_right _ _, ?_⟩
  intro A B U hA hB hU hBU hUA g f hgsource hgrange hnear
  have hfrange (x : A) : f x ∈ closedBall c R := by
    apply mem_closedBall.mpr
    have hgdist := mem_closedBall.mp (hgrange x)
    have hfdist : dist (f x) (e (g x)) < η := by simpa only [dist_eq_norm] using hnear x
    have ht := dist_triangle (f x) (e (g x)) c
    have hηR : η ≤ R - r := min_le_right _ _
    linarith
  obtain ⟨G, hGcore, hGout, hGfix, hGcoord⟩ := exists_local_chart_blend e hA hB hU hBU hUA
    g f hgsource (convex_closedBall c R) hR
    (fun x => closedBall_subset_closedBall hrR.le (hgrange x)) hfrange
  refine ⟨G, hGcore, hGout, hGfix, ?_, fun x => (hGcoord x).1⟩
  intro x
  by_cases hxA : x ∈ A
  · have hcoord := hGcoord ⟨x, hxA⟩
    have hdist : dist (e (G x)) (e (g x)) < η := by
      rw [dist_eq_norm]
      exact hcoord.2.trans_lt (hnear ⟨x, hxA⟩)
    have hGball : e (G x) ∈ closedBall c R := by
      apply mem_closedBall.mpr
      have hgdist := mem_closedBall.mp (hgrange ⟨x, hxA⟩)
      have ht := dist_triangle (e (G x)) (e (g x)) c
      have hηR : η ≤ R - r := min_le_right _ _
      linarith
    have hgb := closedBall_subset_closedBall hrR.le (hgrange ⟨x, hxA⟩)
    have h := heδ _ hGball _ hgb (hdist.trans_le (min_le_left _ _))
    rwa [e.left_inv hcoord.1, e.left_inv (hgsource ⟨x, hxA⟩)] at h
  · rw [hGout x (fun hxU => hxA (interior_subset (hUA hxU))), dist_self]
    exact hε

end ChartMetric

theorem optimal_intersection_of_eqOn_corrected_faces {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (f : K.space → EuclideanSpace ℝ (Fin n))
    (hgp : ∀ r : Finset E, (r : Set E) ⊆ K.vertices → r.card ≤ n + 1 →
      AffineIndependent ℝ (fun a : r => w a))
    (s t : K.faces) (hs : s.1.card ≤ n + 1) (ht : t.1.card ≤ n + 1)
    (hfs : EqOn f (correctedInterpolant K hK w H) (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E)))
    (hft : EqOn f (correctedInterpolant K hK w H) (Subtype.val ⁻¹' convexHull ℝ (t.1 : Set E))) :
    let S := f '' (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E))
    let T := f '' (Subtype.val ⁻¹' convexHull ℝ (t.1 : Set E))
    S ∩ T = H '' convexHull ℝ (w '' ((s.1 : Set E) ∩ (t.1 : Set E))) ∨
      ∃ P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        S ∩ T ⊆ H '' (P : Set (EuclideanSpace ℝ (Fin n))) ∧
          Module.finrank ℝ P.direction + n + 2 ≤ s.1.card + t.1.card := by
  dsimp only
  rw [image_congr hfs, image_congr hft]
  exact correctedInterpolant_optimal_intersection K hK w H hgp s t hs ht

def refinedSubcomplexInclusion (K D P : SimplicialComplex ℝ E)
    (hDK : D.faces ⊆ K.faces) (hspace : P.space = D.space) : C(P.space, K.space) :=
  (subcomplexInclusion K D hDK).comp
    ⟨Homeomorph.setCongr hspace, (Homeomorph.setCongr hspace).continuous⟩

theorem exists_local_optimal_approximation_on_subcomplex
    {M : Type*} [PseudoMetricSpace M] {n d : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (D L : SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ D.faces, s.card ≤ d + 1)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : C(K.space, M)) (c : EuclideanSpace ℝ (Fin n)) {r R ε : ℝ}
    (hrR : r < R) (hR : closedBall c R ⊆ e.target) (hε : 0 < ε)
    (hgsource : ∀ x : D.space, g (subcomplexInclusion K D hDK x) ∈ e.source)
    (hgrange : ∀ x : D.space, e (g (subcomplexInclusion K D hDK x)) ∈ closedBall c r)
    (hPL : ∀ s ∈ (D ⊓ L).faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : D.space, x.1 ∈ convexHull ℝ (s : Set E) →
        e (g (subcomplexInclusion K D hDK x)) = A x.1)
    (hinj : InjOn (fun x : D.space => e (g (subcomplexInclusion K D hDK x)))
      (Subtype.val ⁻¹' L.space))
    {B U : Set K.space} (hB : IsClosed B) (hU : IsOpen U) (hBU : B ⊆ U)
    (hUD : U ⊆ interior (Subtype.val ⁻¹' D.space)) :
    ∃ (G : C(K.space, M)) (P : SimplicialComplex ℝ E) (hP : P.faces.Finite)
      (hspace : P.space = D.space)
      (w : E → EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)),
      simplicialRefines P D ∧ (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      (∀ s : Finset E, (s : Set E) ⊆ P.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x ∉ U, G x = g x) ∧ (∀ x : K.space, x.1 ∈ L.space → G x = g x) ∧
      (∀ x, dist (G x) (g x) < ε) ∧
      (∀ x : D.space, G (subcomplexInclusion K D hDK x) ∈ e.source) ∧
      (∀ x : P.space, refinedSubcomplexInclusion K D P hDK hspace x ∈ B →
        e (G (refinedSubcomplexInclusion K D P hDK hspace x)) = correctedInterpolant P hP w H x) ∧
      ∃ Q : SimplicialComplex ℝ E, Q.faces.Finite ∧ Q.space = P.space ∧
        simplicialRefines Q P ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧
        ∀ s ∈ Q.faces,
          (∀ x : P.space, x.1 ∈ convexHull ℝ (s : Set E) →
            refinedSubcomplexInclusion K D P hDK hspace x ∈ B) →
          ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
            ∀ x : P.space, x.1 ∈ convexHull ℝ (s : Set E) →
              e (G (refinedSubcomplexInclusion K D P hDK hspace x)) = A x.1 := by
  classical
  let A : Set K.space := Subtype.val ⁻¹' D.space
  have hD : D.faces.Finite := hK.subset hDK
  have hA : IsClosed A := (isCompact_space_of_finite_faces D hD).isClosed.preimage continuous_subtype_val
  have hIspace := subcomplex_inf_space K D L hDK hLK
  let gD : C(D.space, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => e (g (subcomplexInclusion K D hDK x)), e.continuousOn.comp_continuous
      (g.continuous.comp (subcomplexInclusion K D hDK).continuous) hgsource⟩
  obtain ⟨η, hη, hηR, hηblend⟩ := exists_chart_blend_tolerance (X := K.space) e c hrR hR hε
  have hgDinj : InjOn gD (Subtype.val ⁻¹' (D ⊓ L).space) := by
    intro x hx y hy hxy
    rw [hIspace] at hx hy
    exact hinj hx.2 hy.2 hxy
  obtain ⟨P, hP, hspace, w, H, href, hdim, hgp, hrel, hnear, Q, hQ, hQspace, hQref, hQdim, hQaff⟩ :=
    exists_relative_piecewise_affine_approximation D hD (D ⊓ L) (fun _ h => h.1) hd
      gD hPL hgDinj hη
  let fD : C(D.space, EuclideanSpace ℝ (Fin n)) := (correctedInterpolant P hP w H).comp
    ⟨Homeomorph.setCongr hspace.symm, (Homeomorph.setCongr hspace.symm).continuous⟩
  let toD : C(A, D.space) := ⟨fun x => ⟨x.1.1, x.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let fA := fD.comp toD
  have hnearA (x : A) : ‖fA x - e (g x)‖ < η := hnear
    (Homeomorph.setCongr hspace.symm (toD x))
  have hgsourceA (x : A) : g x ∈ e.source := hgsource (toD x)
  have hgrangeA (x : A) : e (g x) ∈ closedBall c r := hgrange (toD x)
  obtain ⟨G, hGcore, hGout, hGfix, hGnear, hGsource⟩ := hηblend hA hB hU hBU hUD g fA
    hgsourceA hgrangeA hnearA
  have hcore (x : P.space) (hx : refinedSubcomplexInclusion K D P hDK hspace x ∈ B) :
      e (G (refinedSubcomplexInclusion K D P hDK hspace x)) = correctedInterpolant P hP w H x := by
    let y : A := ⟨refinedSubcomplexInclusion K D P hDK hspace x, by
      change x.1 ∈ D.space
      exact hspace ▸ x.2⟩
    have hy := hGcore y hx
    have hfball : fA y ∈ closedBall c R := by
      apply mem_closedBall.mpr
      have hgdist := mem_closedBall.mp (hgrangeA y)
      have hfdist : dist (fA y) (e (g y)) < η := by simpa only [dist_eq_norm] using hnearA y
      have ht := dist_triangle (fA y) (e (g y)) c
      linarith
    have h := congrArg e hy
    rw [e.right_inv (hR hfball)] at h
    exact h
  refine ⟨G, P, hP, hspace, w, H, href, hdim, hgp, hGout, ?_, hGnear,
    (fun x => hGsource ⟨subcomplexInclusion K D hDK x, x.2⟩), hcore,
    Q, hQ, hQspace, hQref, hQdim, ?_⟩
  · intro x hxL
    by_cases hxA : x ∈ A
    · apply hGfix ⟨x, hxA⟩
      have hxI : x.1 ∈ (D ⊓ L).space := hIspace.symm ▸ ⟨hxA, hxL⟩
      exact hrel (Homeomorph.setCongr hspace.symm (toD ⟨x, hxA⟩)) hxI
    · exact hGout x (fun hxU => hxA (interior_subset (hUD hxU)))
  · intro s hs hcoreface
    obtain ⟨T, hT⟩ := hQaff s hs
    exact ⟨T, fun x hx => (hcore x (hcoreface x hx)).trans (hT x hx)⟩

theorem exists_local_optimal_approximation
    {M : Type*} [PseudoMetricSpace M] {n d : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : C(K.space, M)) (c : EuclideanSpace ℝ (Fin n)) {r R ε : ℝ}
    (hrR : r < R) (hR : closedBall c R ⊆ e.target) (hε : 0 < ε)
    {A U : Set E} (hA : IsCompact A) (hAK : A ⊆ K.space) (hU : IsOpen U) (hAU : A ⊆ U)
    (hgsource : ∀ x : K.space, x.1 ∈ U → g x ∈ e.source)
    (hgrange : ∀ x : K.space, x.1 ∈ U → e (g x) ∈ closedBall c r)
    (hPL : ∀ s ∈ L.faces, ∃ T : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → x.1 ∈ U → e (g x) = T x.1)
    (hinj : InjOn (fun x : K.space => e (g x)) (Subtype.val ⁻¹' (L.space ∩ U))) :
    ∃ (G : C(K.space, M)) (P : SimplicialComplex ℝ E) (hP : P.faces.Finite)
      (κ : C(P.space, K.space)) (B : Set K.space)
      (w : E → EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)),
      simplicialRefines P K ∧ (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      A ⊆ P.space ∧ P.space ⊆ U ∧ (∀ x : P.space, (κ x).1 = x.1) ∧
      IsClosed B ∧ (Subtype.val ⁻¹' A : Set K.space) ⊆ interior B ∧
      (∀ s : Finset E, (s : Set E) ⊆ P.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x : K.space, x.1 ∉ U → G x = g x) ∧
      (∀ x : K.space, x.1 ∈ L.space → G x = g x) ∧
      (∀ x, dist (G x) (g x) < ε) ∧
      (∀ x : P.space, G (κ x) ∈ e.source) ∧
      (∀ x : P.space, κ x ∈ B → e (G (κ x)) = correctedInterpolant P hP w H x) ∧
      ∃ Q : SimplicialComplex ℝ E, Q.faces.Finite ∧ Q.space = P.space ∧
        simplicialRefines Q P ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧
        ∀ s ∈ Q.faces, (∀ x : P.space, x.1 ∈ convexHull ℝ (s : Set E) → κ x ∈ B) →
          ∃ T : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
            ∀ x : P.space, x.1 ∈ convexHull ℝ (s : Set E) → e (G (κ x)) = T x.1 := by
  classical
  obtain ⟨K₀, J, D, hK₀, hK₀space, hK₀ref, hK₀dim, -, hJK₀, hJspace, hJref,
    -, hDK₀, hDU, hAD, hAint⟩ :=
    exists_subcomplex_neighborhood_preserving K L hK hLK hA hAK hU hAU hd
  let k : K₀.space ≃ₜ K.space := Homeomorph.setCongr hK₀space
  let g₀ : C(K₀.space, M) := g.comp ⟨k, k.continuous⟩
  let U₀ : Set K₀.space := interior (Subtype.val ⁻¹' D.space)
  have hclosedA : IsClosed (Subtype.val ⁻¹' A : Set K₀.space) :=
    hA.isClosed.preimage continuous_subtype_val
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hclosedA isOpen_interior hAint
  have hgDsource (x : D.space) : g₀ (subcomplexInclusion K₀ D hDK₀ x) ∈ e.source :=
    hgsource _ (hDU x.2)
  have hgDrange (x : D.space) : e (g₀ (subcomplexInclusion K₀ D hDK₀ x)) ∈ closedBall c r :=
    hgrange _ (hDU x.2)
  have hPLD : ∀ s ∈ (D ⊓ J).faces, ∃ T : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : D.space, x.1 ∈ convexHull ℝ (s : Set E) →
        e (g₀ (subcomplexInclusion K₀ D hDK₀ x)) = T x.1 := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hJref s hs.2
    obtain ⟨T, hT⟩ := hPL t ht
    exact ⟨T, fun x hx => hT _ (hst hx) (hDU x.2)⟩
  have hinjD : InjOn (fun x : D.space => e (g₀ (subcomplexInclusion K₀ D hDK₀ x)))
      (Subtype.val ⁻¹' J.space) := by
    intro x hx y hy hxy
    have hxL : x.1 ∈ L.space := hJspace ▸ hx
    have hyL : y.1 ∈ L.space := hJspace ▸ hy
    have heq := hinj (x₁ := k (subcomplexInclusion K₀ D hDK₀ x))
      (x₂ := k (subcomplexInclusion K₀ D hDK₀ y)) ⟨hxL, hDU x.2⟩ ⟨hyL, hDU y.2⟩ hxy
    apply Subtype.ext
    exact congrArg (fun z : K.space => z.1) heq
  obtain ⟨G₀, P, hP, hspace, w, H, hPD, hPdim, hgp, hGout, hGfix, hGnear,
    hGsource, hGcore, Q, hQ, hQspace, hQref, hQdim, hQaff⟩ :=
    exists_local_optimal_approximation_on_subcomplex K₀ hK₀ D J hDK₀ hJK₀
      (fun s hs => hK₀dim s (hDK₀ hs)) e g₀ c hrR hR hε hgDsource hgDrange hPLD hinjD
      isClosed_closure isOpen_interior hVU subset_rfl
  let κ₀ := refinedSubcomplexInclusion K₀ D P hDK₀ hspace
  let κ : C(P.space, K.space) := (⟨k, k.continuous⟩ : C(K₀.space, K.space)).comp κ₀
  let G : C(K.space, M) := G₀.comp ⟨k.symm, k.symm.continuous⟩
  let B : Set K.space := k.symm ⁻¹' closure V
  have hB : IsClosed B := isClosed_closure.preimage k.symm.continuous
  have hBint : (Subtype.val ⁻¹' A : Set K.space) ⊆ interior B := by
    have hvB : k.symm ⁻¹' V ⊆ B := preimage_mono subset_closure
    have hint := (hV.preimage k.symm.continuous).subset_interior_iff.mpr hvB
    intro x hx
    exact hint (hAV hx)
  have hcore (x : P.space) (hx : κ x ∈ B) : e (G (κ x)) = correctedInterpolant P hP w H x := by
    change e (G₀ (k.symm (k (κ₀ x)))) = _
    rw [k.symm_apply_apply]
    apply hGcore x
    change k.symm (k (κ₀ x)) ∈ closure V at hx
    rwa [k.symm_apply_apply] at hx
  have hDref : simplicialRefines D K₀ := fun s hs => ⟨s, hDK₀ hs, subset_rfl⟩
  refine ⟨G, P, hP, κ, B, w, H, hPD.trans (hDref.trans hK₀ref), hPdim,
    (fun x hx => hspace.symm ▸ hAD hx), (fun x hx => hDU (hspace ▸ hx)),
    (fun _ => rfl), hB, hBint, hgp, ?_, ?_, ?_, ?_, hcore,
    Q, hQ, hQspace, hQref, hQdim, ?_⟩
  · intro x hxU
    have hout : k.symm x ∉ U₀ := by
      intro hx
      have hxD : (k.symm x).1 ∈ D.space :=
        (interior_subset (s := (Subtype.val ⁻¹' D.space : Set K₀.space))) hx
      exact hxU (hDU hxD)
    exact hGout (k.symm x) hout
  · intro x hxL
    have hxJ : (k.symm x).1 ∈ J.space := hJspace.symm ▸ hxL
    exact hGfix (k.symm x) hxJ
  · intro x
    exact hGnear (k.symm x)
  · intro x
    change G₀ (k.symm (k (κ₀ x))) ∈ e.source
    rw [k.symm_apply_apply]
    exact hGsource (Homeomorph.setCongr hspace x)
  · intro s hs hface
    obtain ⟨T, hT⟩ := hQaff s hs (fun x hx => by
      have h := hface x hx
      change k.symm (k (κ₀ x)) ∈ closure V at h
      rwa [k.symm_apply_apply] at h)
    refine ⟨T, fun x hx => ?_⟩
    change e (G₀ (k.symm (k (κ₀ x)))) = T x.1
    rw [k.symm_apply_apply]
    exact hT x hx

end DifferentialGeometry.Topology.Engulfing
