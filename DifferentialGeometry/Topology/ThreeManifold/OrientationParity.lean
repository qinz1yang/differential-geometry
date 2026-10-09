import DifferentialGeometry.Topology.ThreeManifold.OrientedChartNeighborhood
import DifferentialGeometry.Topology.LocalDegree.ChartParity
import DifferentialGeometry.Topology.LocalDegree.Determinant
import DifferentialGeometry.External.CanonicalTopology.LinearAlgebra.Orientation
/-!
# Orientation parity of topological embeddings into an oriented smooth 3-manifold

Route A' of the R05 orientation bridge, steps A1 and A2. Two charts that are both positive for a
tangent orientation at the same point (`OrientedChartSimplex`) have transition parity `0` there
(`OrientedChartSimplex.chartOrientationParity_eq_zero`), by comparing both with the preferred
chart through the determinant formula for the local degree.

For a continuous injective `F : ℝ³ → M` on an open set `U`, `orientedParity o hU hF hFi x` is the
local-degree parity of `S.chart ∘ F` at `x`, where `S` is a positive chart at `F x`. By A1 any
positive chart gives the same value (`orientedParity_eq_of_chart`). The parity is locally
constant, constant on preconnected subsets, depends only on the germ of `F`, is additive under
precomposition with an embedding of open subsets of `ℝ³` (with the affine case expressed by the
sign of the determinant), and for a differentiable `F` with invertible derivative it vanishes
exactly when the derivative carries the standard orientation to `o`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

open DifferentialGeometry.LocalDegree DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem embeddingOrientationParity_eq_of_differentiableAt {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hf : ContinuousOn f U) (hfi : InjOn f U) (x : U) (hd : DifferentiableAt ℝ f x)
    (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    embeddingOrientationParity hU hf hfi x =
      if 0 < LinearMap.det (fderiv ℝ f x).toLinearMap then 0 else 1 := by
  have hfd : fderiv ℝ (fun w => f w - f x) x = fderiv ℝ f x := fderiv_sub_const _
  unfold embeddingOrientationParity
  rw [euclideanLocalDegree_eq_sign_det_fderiv _ (hd.sub_const _) (by rwa [hfd]), hfd]
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · simp [sign_neg hneg, not_lt.mpr hneg.le]
  · simp [sign_pos hpos, hpos]

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M}

omit [IsManifold ThreeModel ∞ M] in
private theorem writtenInExtChartAt_chart (y : M) (c : OpenPartialHomeomorph M ThreeSpace) :
    writtenInExtChartAt ThreeModel ThreeModel y c = c ∘ (chartAt ThreeSpace y).symm := by
  funext z
  simp [writtenInExtChartAt]

omit [IsManifold ThreeModel ∞ M] in
private theorem chartOrientationParity_chartAt {y : M} (c : OpenPartialHomeomorph M ThreeSpace)
    (hc : y ∈ c.source) (hd : MDifferentiableAt ThreeModel ThreeModel c y)
    (hdet : LinearMap.det (mfderiv ThreeModel ThreeModel c y).toLinearMap ≠ 0) :
    chartOrientationParity (d := 2) (chartAt ThreeSpace y) c y
        (mem_chart_source ThreeSpace y) hc =
      if 0 < LinearMap.det (mfderiv ThreeModel ThreeModel c y).toLinearMap then 0 else 1 := by
  have hw := writtenInExtChartAt_chart y c
  have hdiff : DifferentiableAt ℝ (c ∘ (chartAt ThreeSpace y).symm) (chartAt ThreeSpace y y) := by
    have h := hd.differentiableWithinAt_writtenInExtChartAt
    rw [hw] at h
    simpa [differentiableWithinAt_univ] using h
  have hfd : fderiv ℝ (c ∘ (chartAt ThreeSpace y).symm) (chartAt ThreeSpace y y) =
      mfderiv ThreeModel ThreeModel c y := by
    rw [hd.mfderiv_abuse, hw]
    simp
  have hdet' : LinearMap.det
      (fderiv ℝ (c ∘ (chartAt ThreeSpace y).symm) (chartAt ThreeSpace y y)).toLinearMap ≠ 0 := by
    rw [hfd]
    exact hdet
  unfold chartOrientationParity
  exact (embeddingOrientationParity_eq_of_differentiableAt (d := 2) _ _ _ _ hdiff hdet').trans
    (congrArg (fun L : ThreeSpace →L[ℝ] ThreeSpace =>
      if 0 < LinearMap.det (L : ThreeSpace →ₗ[ℝ] ThreeSpace) then (0 : ZMod 2) else 1) hfd)

private theorem det_pos_iff_of_positive {y : M} (S : OrientedChartSimplex o y) :
    0 < LinearMap.det (mfderiv ThreeModel ThreeModel S.chart y).toLinearMap ↔
      standardThreeOrientation = o.orientation y := by
  let L : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv ThreeModel ThreeModel S.chart y).toLinearMap S.derivative_bijective
  let ori : Orientation ℝ ThreeSpace (Fin 3) := o.orientation y
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace := by simp
  have h := Orientation.map_eq_iff_det_pos ori L hcard
  have hpos : Orientation.map (Fin 3) L ori = standardThreeOrientation := S.positive
  have hL : (L : ThreeSpace →ₗ[ℝ] ThreeSpace) =
      (mfderiv ThreeModel ThreeModel S.chart y).toLinearMap := LinearMap.ext fun _ => rfl
  exact (iff_of_eq (congrArg (fun A : ThreeSpace →ₗ[ℝ] ThreeSpace => 0 < LinearMap.det A)
    hL)).symm.trans (h.symm.trans (Eq.congr_left hpos))

private theorem det_ne_zero_of_bijective {f : ThreeSpace →ₗ[ℝ] ThreeSpace}
    (hf : Function.Bijective f) : LinearMap.det f ≠ 0 := by
  have h := (LinearEquiv.ofBijective f hf).det.ne_zero
  rwa [LinearEquiv.coe_det,
    show ((LinearEquiv.ofBijective f hf : ThreeSpace →ₗ[ℝ] ThreeSpace)) = f from
      LinearMap.ext fun _ => rfl] at h

theorem OrientedChartSimplex.chartOrientationParity_eq_zero {y : M}
    (S T : OrientedChartSimplex o y) :
    chartOrientationParity (d := 2) S.chart T.chart y S.center_mem T.center_mem = 0 := by
  have hφ := mem_chart_source ThreeSpace y
  have hST := (det_pos_iff_of_positive S).trans (det_pos_iff_of_positive T).symm
  rw [← chartOrientationParity_add S.chart (chartAt ThreeSpace y) T.chart y S.center_mem hφ
    T.center_mem, chartOrientationParity_symm S.chart _ y S.center_mem hφ,
    chartOrientationParity_chartAt S.chart S.center_mem S.differentiableAt
      (det_ne_zero_of_bijective S.derivative_bijective),
    chartOrientationParity_chartAt T.chart T.center_mem T.differentiableAt
      (det_ne_zero_of_bijective T.derivative_bijective)]
  by_cases h : 0 < LinearMap.det (mfderiv ThreeModel ThreeModel S.chart y).toLinearMap
  · simp only [h, hST.mp h, ↓reduceIte, add_zero]
  · simp only [h, mt hST.mpr h, ↓reduceIte]
    decide

private theorem nonempty_orientedChartSimplex (o : TangentOrientationSection M) (p : M) :
    Nonempty (OrientedChartSimplex o p) := by
  obtain ⟨e, U, -, hp, h⟩ := exists_open_orientedChartSimplex o p
  obtain ⟨T, -⟩ := h p hp
  exact ⟨T⟩

def chartCompParity (c : OpenPartialHomeomorph M ThreeSpace) {U : Set ThreeSpace}
    (hU : IsOpen U) {F : ThreeSpace → M} (hF : ContinuousOn F U) (hFi : InjOn F U)
    (x : U) (hx : F x ∈ c.source) : ZMod 2 :=
  embeddingOrientationParity (d := 2) (hF.isOpen_inter_preimage hU c.open_source)
    (c.continuousOn.comp (hF.mono inter_subset_left) fun _ hz => hz.2)
    (c.injOn.comp (hFi.mono inter_subset_left) fun _ hz => hz.2) ⟨x, x.2, hx⟩

def orientedParity (o : TangentOrientationSection M) {U : Set ThreeSpace} (hU : IsOpen U)
    {F : ThreeSpace → M} (hF : ContinuousOn F U) (hFi : InjOn F U) (x : U) : ZMod 2 :=
  chartCompParity (Classical.choice (nonempty_orientedChartSimplex o (F x))).chart hU hF hFi x
    (Classical.choice (nonempty_orientedChartSimplex o (F x))).center_mem

section Parity

variable {U : Set ThreeSpace} (hU : IsOpen U) {F : ThreeSpace → M}
  (hF : ContinuousOn F U) (hFi : InjOn F U)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem chartCompParity_eq_add (c c' : OpenPartialHomeomorph M ThreeSpace) (x : U)
    (hx : F x ∈ c.source) (hx' : F x ∈ c'.source) :
    chartCompParity c' hU hF hFi x hx' =
      chartCompParity c hU hF hFi x hx + chartOrientationParity (d := 2) c c' (F x) hx hx' := by
  have hW : IsOpen (U ∩ F ⁻¹' (c.source ∩ c'.source)) :=
    hF.isOpen_inter_preimage hU (c.open_source.inter c'.open_source)
  have hxW : (x : ThreeSpace) ∈ U ∩ F ⁻¹' (c.source ∩ c'.source) := ⟨x.2, hx, hx'⟩
  have hfc : ContinuousOn (c ∘ F) (U ∩ F ⁻¹' (c.source ∩ c'.source)) :=
    c.continuousOn.comp (hF.mono fun _ hz => hz.1) fun _ hz => hz.2.1
  have hfi : InjOn (c ∘ F) (U ∩ F ⁻¹' (c.source ∩ c'.source)) :=
    c.injOn.comp (hFi.mono fun _ hz => hz.1) fun _ hz => hz.2.1
  have hm : MapsTo (c ∘ F) (U ∩ F ⁻¹' (c.source ∩ c'.source)) (c.symm ≫ₕ c').source := by
    intro z hz
    refine ⟨c.map_source hz.2.1, ?_⟩
    change c.symm (c (F z)) ∈ c'.source
    rw [c.left_inv hz.2.1]
    exact hz.2.2
  have hcomp := embeddingOrientationParity_comp (d := 2) hW (c.symm ≫ₕ c').open_source hfc hfi
    (c.symm ≫ₕ c').continuousOn (c.symm ≫ₕ c').injOn hm ⟨x, hxW⟩
  have heq : ((c.symm ≫ₕ c') ∘ (c ∘ F)) =ᶠ[𝓝 (x : ThreeSpace)] (c' ∘ F) := by
    filter_upwards [hW.mem_nhds hxW] with z hz
    change c' (c.symm (c (F z))) = c' (F z)
    rw [c.left_inv hz.2.1]
  have h1 : embeddingOrientationParity (d := 2) hW hfc hfi ⟨x, hxW⟩ =
      chartCompParity c hU hF hFi x hx :=
    embeddingOrientationParity_congr (d := 2) hW _ hfc hfi _ _ hxW _ EventuallyEq.rfl
  have h2 : embeddingOrientationParity (d := 2) hW ((c.symm ≫ₕ c').continuousOn.comp hfc hm)
      ((c.symm ≫ₕ c').injOn.comp hfi hm) ⟨x, hxW⟩ = chartCompParity c' hU hF hFi x hx' :=
    embeddingOrientationParity_congr (d := 2) hW _ _ _ _ _ hxW _ heq
  rw [← h1, ← h2]
  exact hcomp

theorem orientedParity_eq_of_chart (x : U) (S : OrientedChartSimplex o (F x)) :
    orientedParity o hU hF hFi x = chartCompParity S.chart hU hF hFi x S.center_mem := by
  unfold orientedParity
  rw [chartCompParity_eq_add hU hF hFi _ S.chart x _ S.center_mem,
    OrientedChartSimplex.chartOrientationParity_eq_zero, add_zero]

private theorem orientedParity_eq_of_chart_of_eq {z : M} (S : OrientedChartSimplex o z) (x : U)
    (hz : F x = z) :
    orientedParity o hU hF hFi x =
      chartCompParity S.chart hU hF hFi x (by rw [hz]; exact S.center_mem) := by
  subst hz
  exact orientedParity_eq_of_chart hU hF hFi x S

theorem isLocallyConstant_orientedParity :
    IsLocallyConstant (orientedParity o hU hF hFi) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x₀
  obtain ⟨e, V, hV, hx₀V, hT⟩ := exists_open_orientedChartSimplex o (F x₀)
  have hVe : V ⊆ e.source := fun z hz => by
    obtain ⟨T, rfl⟩ := hT z hz
    exact T.center_mem
  have hW : IsOpen (U ∩ F ⁻¹' V) := hF.isOpen_inter_preimage hU hV
  have hx₀W : (x₀ : ThreeSpace) ∈ U ∩ F ⁻¹' V := ⟨x₀.2, hx₀V⟩
  have hQW := connectedComponentIn_subset (U ∩ F ⁻¹' V) (x₀ : ThreeSpace)
  have hx₀Q := mem_connectedComponentIn hx₀W
  have hQe : connectedComponentIn (U ∩ F ⁻¹' V) (x₀ : ThreeSpace) ⊆ U ∩ F ⁻¹' e.source :=
    fun z hz => ⟨(hQW hz).1, hVe (hQW hz).2⟩
  have key : ∀ (x : U)
      (hx : (x : ThreeSpace) ∈ connectedComponentIn (U ∩ F ⁻¹' V) (x₀ : ThreeSpace)),
      orientedParity o hU hF hFi x = chartCompParity e hU hF hFi x (hVe (hQW hx).2) := by
    intro x hx
    obtain ⟨T, hTe⟩ := hT (F x) (hQW hx).2
    subst hTe
    exact orientedParity_eq_of_chart hU hF hFi x T
  refine ⟨Subtype.val ⁻¹' connectedComponentIn (U ∩ F ⁻¹' V) (x₀ : ThreeSpace),
    hW.connectedComponentIn.preimage continuous_subtype_val, hx₀Q, fun x hx => ?_⟩
  rw [key x hx, key x₀ hx₀Q]
  exact embeddingOrientationParity_eq_of_isPreconnected (d := 2) _ _ _
    isPreconnected_connectedComponentIn hQe hx hx₀Q

theorem orientedParity_eq_of_isPreconnected {A : Set ThreeSpace} (hA : IsPreconnected A)
    (hAU : A ⊆ U) {x y : ThreeSpace} (hx : x ∈ A) (hy : y ∈ A) :
    orientedParity o hU hF hFi ⟨x, hAU hx⟩ = orientedParity o hU hF hFi ⟨y, hAU hy⟩ := by
  have hA' : IsPreconnected ((Subtype.val : U → ThreeSpace) ⁻¹' A) := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.mpr hAU]
    exact hA
  exact (isLocallyConstant_orientedParity hU hF hFi).apply_eq_of_isPreconnected hA' hx hy

theorem orientedParity_congr {V : Set ThreeSpace} (hV : IsOpen V) {G : ThreeSpace → M}
    (hG : ContinuousOn G V) (hGi : InjOn G V) {x : ThreeSpace} (hxU : x ∈ U) (hxV : x ∈ V)
    (hFG : F =ᶠ[𝓝 x] G) :
    orientedParity o hU hF hFi ⟨x, hxU⟩ = orientedParity o hV hG hGi ⟨x, hxV⟩ := by
  obtain ⟨S⟩ := nonempty_orientedChartSimplex o (F x)
  rw [orientedParity_eq_of_chart hU hF hFi ⟨x, hxU⟩ S,
    orientedParity_eq_of_chart_of_eq hV hG hGi S ⟨x, hxV⟩ hFG.self_of_nhds.symm]
  exact embeddingOrientationParity_congr (d := 2) _ _ _ _ _ _ _ _ (hFG.fun_comp S.chart)

theorem orientedParity_comp {V : Set ThreeSpace} (hV : IsOpen V) {g : ThreeSpace → ThreeSpace}
    (hg : ContinuousOn g V) (hgi : InjOn g V) (hm : MapsTo g V U) (x : V) :
    orientedParity o hV (hF.comp hg hm) (hFi.comp hgi hm) x =
      embeddingOrientationParity (d := 2) hV hg hgi x +
        orientedParity o hU hF hFi ⟨g x, hm x.2⟩ := by
  obtain ⟨S⟩ := nonempty_orientedChartSimplex o (F (g x))
  rw [orientedParity_eq_of_chart hV (hF.comp hg hm) (hFi.comp hgi hm) x S,
    orientedParity_eq_of_chart hU hF hFi ⟨g x, hm x.2⟩ S]
  have hW : IsOpen (V ∩ (F ∘ g) ⁻¹' S.chart.source) :=
    (hF.comp hg hm).isOpen_inter_preimage hV S.chart.open_source
  have hxW : (x : ThreeSpace) ∈ V ∩ (F ∘ g) ⁻¹' S.chart.source := ⟨x.2, S.center_mem⟩
  have hmW : MapsTo g (V ∩ (F ∘ g) ⁻¹' S.chart.source) (U ∩ F ⁻¹' S.chart.source) :=
    fun _ hz => ⟨hm hz.1, hz.2⟩
  have hcomp := embeddingOrientationParity_comp (d := 2) hW
    (hF.isOpen_inter_preimage hU S.chart.open_source) (hg.mono inter_subset_left)
    (hgi.mono inter_subset_left)
    (S.chart.continuousOn.comp (hF.mono inter_subset_left) fun _ hz => hz.2)
    (S.chart.injOn.comp (hFi.mono inter_subset_left) fun _ hz => hz.2) hmW ⟨x, hxW⟩
  have h1 : embeddingOrientationParity (d := 2) hW (hg.mono inter_subset_left)
      (hgi.mono inter_subset_left) ⟨x, hxW⟩ = embeddingOrientationParity (d := 2) hV hg hgi x :=
    embeddingOrientationParity_congr (d := 2) _ _ _ _ _ _ _ _ EventuallyEq.rfl
  rw [h1] at hcomp
  exact hcomp

private theorem hasFDerivAt_affineEquiv (A : ThreeSpace ≃ᵃ[ℝ] ThreeSpace) (x : ThreeSpace) :
    HasFDerivAt (A : ThreeSpace → ThreeSpace)
      (LinearMap.toContinuousLinearMap (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace)) x := by
  have h : (A : ThreeSpace → ThreeSpace) = fun z => A.linear z + A 0 := by
    funext z
    simpa using A.map_vadd 0 z
  rw [h]
  exact (LinearMap.toContinuousLinearMap
    (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace)).hasFDerivAt.add_const (A 0)

omit [IsManifold ThreeModel ∞ M] in
private theorem embeddingOrientationParity_affineEquiv (A : ThreeSpace ≃ᵃ[ℝ] ThreeSpace)
    {V : Set ThreeSpace} (hV : IsOpen V) (x : V) :
    embeddingOrientationParity (d := 2) hV
        (A.continuous_of_finiteDimensional.continuousOn) (A.injective.injOn) x =
      if 0 < LinearMap.det (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) then 0 else 1 := by
  have hA := hasFDerivAt_affineEquiv A x
  rw [embeddingOrientationParity_eq_of_differentiableAt (d := 2) hV _ _ x hA.differentiableAt
    (by
      rw [hA.fderiv, LinearMap.coe_toContinuousLinearMap, ← LinearEquiv.coe_det]
      exact (LinearEquiv.det A.linear).ne_zero), hA.fderiv]
  rfl

theorem orientedParity_comp_affineEquiv (A : ThreeSpace ≃ᵃ[ℝ] ThreeSpace) {V : Set ThreeSpace}
    (hV : IsOpen V) (hG : ContinuousOn (F ∘ A) V) (hGi : InjOn (F ∘ A) V) (hm : MapsTo A V U)
    (x : V) :
    orientedParity o hV hG hGi x = orientedParity o hU hF hFi ⟨A x, hm x.2⟩ +
      if 0 < LinearMap.det (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) then 0 else 1 := by
  rw [add_comm, ← embeddingOrientationParity_affineEquiv A hV x]
  exact orientedParity_comp hU hF hFi hV A.continuous_of_finiteDimensional.continuousOn
    A.injective.injOn hm x

private theorem ite_zero_one_eq_zero_iff (p : Prop) [Decidable p] :
    (if p then 0 else 1 : ZMod 2) = 0 ↔ p := by
  by_cases h : p
  · simp [h]
  · simp only [h, ↓reduceIte, iff_false]
    decide

theorem orientedParity_eq_zero_iff_of_mdifferentiableAt (x : U)
    (hd : MDifferentiableAt ThreeModel ThreeModel F x)
    (hb : Function.Bijective (mfderiv ThreeModel ThreeModel F x)) :
    orientedParity o hU hF hFi x = 0 ↔
      Orientation.map (Fin 3) (LinearEquiv.ofBijective
          (mfderiv ThreeModel ThreeModel F x).toLinearMap hb) standardThreeOrientation =
        o.orientation (F x) := by
  obtain ⟨S⟩ := nonempty_orientedChartSimplex o (F x)
  rw [orientedParity_eq_of_chart hU hF hFi x S]
  have hcd : MDifferentiableAt ThreeModel ThreeModel (S.chart ∘ F) x :=
    S.differentiableAt.comp (x : ThreeSpace) hd
  have hdiff : DifferentiableAt ℝ (S.chart ∘ F) x :=
    mdifferentiableAt_iff_differentiableAt.mp hcd
  have hfd : fderiv ℝ (S.chart ∘ F) x = (mfderiv ThreeModel ThreeModel S.chart (F x)).comp
      (mfderiv ThreeModel ThreeModel F x) := by
    rw [← mfderiv_comp (x : ThreeSpace) S.differentiableAt hd, mfderiv_eq_fderiv]
    rfl
  let DF := LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel F x).toLinearMap hb
  let DS := LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel S.chart (F x)).toLinearMap
    S.derivative_bijective
  let L : ThreeSpace ≃ₗ[ℝ] ThreeSpace := DF.trans DS
  have hL : (L : ThreeSpace →ₗ[ℝ] ThreeSpace) = (fderiv ℝ (S.chart ∘ F) x).toLinearMap := by
    rw [hfd]
    rfl
  have hdet : LinearMap.det (fderiv ℝ (S.chart ∘ F) x).toLinearMap ≠ 0 := by
    rw [← hL, ← LinearEquiv.coe_det]
    exact (LinearEquiv.det L).ne_zero
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace := by simp
  have h1 := Orientation.map_eq_iff_det_pos standardThreeOrientation L hcard
  have h2 : Orientation.map (Fin 3) L standardThreeOrientation =
      Orientation.map (Fin 3) DS (Orientation.map (Fin 3) DF standardThreeOrientation) :=
    DifferentialGeometry.orientation_map_trans DF DS _
  have h3 : Orientation.map (Fin 3) DS (o.orientation (F x)) = standardThreeOrientation :=
    S.positive
  have he := embeddingOrientationParity_eq_of_differentiableAt (d := 2)
    (hF.isOpen_inter_preimage hU S.chart.open_source)
    (S.chart.continuousOn.comp (hF.mono inter_subset_left) fun _ hz => hz.2)
    (S.chart.injOn.comp (hFi.mono inter_subset_left) fun _ hz => hz.2)
    ⟨x, x.2, S.center_mem⟩ hdiff hdet
  have key : 0 < LinearMap.det (fderiv ℝ (S.chart ∘ F) x).toLinearMap ↔
      Orientation.map (Fin 3) DF standardThreeOrientation = o.orientation (F x) := by
    rw [← hL, ← h1, h2]
    exact (Eq.congr_right h3.symm).trans (Orientation.map (Fin 3) DS).injective.eq_iff
  exact (Eq.congr_left he).trans ((ite_zero_one_eq_zero_iff _).trans key)

end Parity

end DifferentialGeometry.Topology
