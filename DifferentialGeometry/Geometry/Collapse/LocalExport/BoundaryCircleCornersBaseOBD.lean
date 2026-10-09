import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimSmoothOBD
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRankTwoEFE

/-!
# The corner model of the circle base, on the base manifold (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G11b (hlift, `JunctionRimFacts74.local_faces`, the
part that does not depend on the slim pieces): `geom.circleCorners` (G6c: at every point of `C₁`
off its relative interior in `B₀`, one or two labelled ambient face functions with independent
differentials through `f₁`) is transported to the circle base manifold `↥circleBaseOpen` of the
produced stages:

* `frontier_circle_cbase_OBD`: a frontier point of `C₁` in the circle base lies in `C₁` and its
  image is NOT in the relative interior of `f₀(R_c)` in `B₀` (`ι_circle` is a topological
  embedding with range `B₀`);
* `circle_corners_base_OBD`: at such a point there are an open `U ∋ c` and labelled smooth face
  functions `φ_f = Φ_f ∘ ι_circle` on `U` (`ContMDiffOn`) with `φ_f c = 0`, zero set in `C₁` the
  base points whose WHOLE `f₀`-fibre lies in the labelled face, surjective base differential
  (chain rule through `proj`: the fibre differential of G6c factors through `d(proj)`) and
  `C₁ ∩ U = {φ_f ≤ 0 ∀ f}`. The labels are `CircleFaceLabel74 dec.slim` of the boundary exports; the
  translation to the residual-face labels of the actual slim pieces is the remaining step of
  `local_faces`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}


section CircleCorners

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc)

include C in
/-- `ι_circle` has range exactly the circle base. -/
theorem range_ιcircle_OBD : range P.ιcircle = dec.bases.base 0 :=
  Subset.antisymm P.circle_range (C.base_zero_subset_range_OBD P)

include C in
/-- **A frontier point of `C₁` is a corner candidate**: it lies in `C₁` and its image is not in the
relative interior of `f₀(R_c)` in `B₀`. -/
theorem frontier_circle_cbase_OBD
    (hS : IsCompact (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen))
    {c' : P.cut.circleBaseOpen}
    (hc : c' ∈ frontier (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen)) :
    c'.1 ∈ P.cut.C₁ ∧ P.ιcircle c'.1 ∈ C.toChain.stageMap 0 '' dec.slim.remainder ∧
      P.ιcircle c'.1 ∉ relInterior_BIF (dec.bases.base 0)
        (C.toChain.stageMap 0 '' dec.slim.remainder) := by
  have hcS : c' ∈ (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen) :=
    hS.isClosed.frontier_subset hc
  have hmem : P.ιcircle c'.1 ∈ C.toChain.stageMap 0 '' dec.slim.remainder := by
    rw [← P.cut_C₁]
    exact ⟨c'.1, hcS, rfl⟩
  refine ⟨hcS, hmem, fun hri => ?_⟩
  -- the relative interior pulls back to an open set of the circle base inside `C₁`
  obtain ⟨y', hy', hy'v⟩ := hri
  have hrange : ∀ b : P.circle.Base, P.ιcircle b ∈ dec.bases.base 0 := fun b =>
    P.circle_range ⟨b, rfl⟩
  let e : P.circle.Base → dec.bases.base 0 := fun b => ⟨P.ιcircle b, hrange b⟩
  have he : Continuous e := P.circle_ident.emb.continuous.subtype_mk _
  have hopen : IsOpen (e ⁻¹' interior (Subtype.val ⁻¹' (C.toChain.stageMap 0 ''
      dec.slim.remainder) : Set (dec.bases.base 0))) := isOpen_interior.preimage he
  have hcmem : c'.1 ∈ e ⁻¹' interior (Subtype.val ⁻¹' (C.toChain.stageMap 0 ''
      dec.slim.remainder) : Set (dec.bases.base 0)) := by
    have : e c'.1 = y' := Subtype.ext hy'v.symm
    rw [mem_preimage, this]
    exact hy'
  have hsub : e ⁻¹' interior (Subtype.val ⁻¹' (C.toChain.stageMap 0 ''
      dec.slim.remainder) : Set (dec.bases.base 0)) ⊆ P.cut.C₁ := by
    intro b hb
    have h1 : e b ∈ (Subtype.val ⁻¹' (C.toChain.stageMap 0 '' dec.slim.remainder) :
        Set (dec.bases.base 0)) := interior_subset hb
    have h2 : P.ιcircle b ∈ P.ιcircle '' P.cut.C₁ := by
      rw [P.cut_C₁]
      exact h1
    obtain ⟨b', hb', hbb⟩ := h2
    rw [← P.circle_ident.emb.injective hbb]
    exact hb'
  have hnhds : (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen) ∈ 𝓝 c' := by
    refine Filter.mem_of_superset ((hopen.preimage continuous_subtype_val).mem_nhds hcmem) ?_
    intro b hb
    exact hsub hb
  exact hc.2 (mem_interior_iff_mem_nhds.2 hnhds)

include C in
/-- **The base differential of the corner functions is onto**: the fibre differential of G6c at a
point of the fibre factors through `d(proj)`, so the base differential is onto. -/
theorem circle_corners_surj_OBD {ι : Type*} (L : Finset ι)
    (φ : ι → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ)
    {O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))} (hO : IsOpen O)
    (hιc : ContMDiff (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιcircle)
    {c' : P.cut.circleBaseOpen} (hyO : P.ιcircle c'.1 ∈ O)
    (hφ : ∀ f ∈ L, ContDiffOn ℝ ∞ (φ f) O)
    (hsurj : ∀ p ∈ dec.bases.fibre 0 (P.ιcircle c'.1),
      Surjective fun v : TangentSpace W.model p =>
        fun f : L => mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p v) :
    Surjective fun w : TangentSpace (𝓡 2) c' =>
      fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun b : P.cut.circleBaseOpen => φ f (P.ιcircle b.1)) c' w := by
  have hy : P.ιcircle c'.1 ∈ dec.bases.base 0 := P.circle_range ⟨c'.1, rfl⟩
  obtain ⟨p, hp, hpf⟩ : ∃ p ∈ dec.bases.source 0, C.toChain.stageMap 0 p = P.ιcircle c'.1 := by
    rw [← dec.bases.image_eq 0] at hy
    exact hy
  have hpar : p ∈ P.circle.parent := by
    rw [← SetLike.mem_coe, P.circle_ident.parent_eq]
    exact hp
  have hproj : P.circle.proj ⟨p, hpar⟩ = c'.1 := by
    refine P.circle_ident.emb.injective ?_
    rw [P.circle_ident.proj_eq ⟨p, hpar⟩]
    exact hpf
  let z₀ : P.circle.restrictParent P.cut.circleBaseOpen :=
    ⟨p, P.circle.mem_restrictParent_of hpar (by rw [hproj]; exact c'.2)⟩
  let Pj := P.stageGeometry.circle.restrictProj P.cut.circleBaseOpen
  have hPx : Pj z₀ = c' := Subtype.ext hproj
  have hPj : ContMDiff W.model (𝓡 2) ∞ Pj := P.stageGeometry.circle.restrictProj_smooth _
  have hιV : ContMDiff (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ (fun b : P.cut.circleBaseOpen => P.ιcircle b.1) :=
    hιc.comp (contMDiff_subtype_val (I := 𝓡 2) (U := P.cut.circleBaseOpen))
  intro t
  obtain ⟨v, hv⟩ := hsurj p ⟨hp, hpf⟩ t
  refine ⟨mfderiv W.model (𝓡 2) Pj z₀ v, ?_⟩
  funext f
  have hfq : ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => φ f (C.toChain.stageMap 0 q)) p := by
    have h1 : ContDiffAt ℝ ∞ (φ f) (C.toChain.stageMap 0 p) := by
      rw [hpf]
      exact (hφ f f.2).contDiffAt (hO.mem_nhds hyO)
    exact h1.contMDiffAt.comp p ((C.contMDiff_stageMap_OBD 0) p)
  have hlhs : mvfderiv W.model ((fun b : P.cut.circleBaseOpen => φ f (P.ιcircle b.1)) ∘ Pj) z₀ =
      mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p :=
    mvfderiv_comp_subtype_val_EFE P.cut.circleSource
      (f := fun q => φ f (C.toChain.stageMap 0 q))
      (g := (fun b : P.cut.circleBaseOpen => φ f (P.ιcircle b.1)) ∘ Pj)
      (fun z => congrArg (φ f)
        (P.circle_ident.proj_eq (P.stageGeometry.circle.restrictIncl _ z))) z₀
      (hfq.mdifferentiableAt (by simp))
  have hGd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
      (fun b : P.cut.circleBaseOpen => φ f (P.ιcircle b.1)) c' := by
    have h1 : ContDiffAt ℝ ∞ (φ f) (P.ιcircle c'.1) := (hφ f f.2).contDiffAt (hO.mem_nhds hyO)
    exact (h1.contMDiffAt.comp c' (hιV c')).mdifferentiableAt (by simp)
  have hchain := mvfderiv_comp_apply_of_eq (x := z₀) hGd (hPj.mdifferentiableAt (by simp)) hPx v
  have hvf : mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p v = t f := congrFun hv f
  have h2 : mvfderiv (𝓡 2) (fun b : P.cut.circleBaseOpen => φ f (P.ιcircle b.1)) c'
      (mfderiv W.model (𝓡 2) Pj z₀ v) = t f :=
    hchain.symm.trans ((congrArg (fun L => L v) hlhs).trans hvf)
  exact h2

include C in
/-- **`local_faces` at the base level, in the labels of the boundary exports**: at a frontier point
`c'` of `C₁` in the circle base, the corner model of G6c transported by `ι_circle`. -/
theorem circle_corners_base_OBD (geom : BoundaryGeometricExports74b C.toChain dec)
    (hS : IsCompact (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen))
    (hιc : ContMDiff (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιcircle)
    {c' : P.cut.circleBaseOpen}
    (hc : c' ∈ frontier (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen)) :
    ∃ U : TopologicalSpace.Opens P.cut.circleBaseOpen, c' ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel74 dec.slim))
        (φ : CircleFaceLabel74 dec.slim → P.cut.circleBaseOpen → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c' = 0 ∧
          {b | b ∈ U ∧ b.1 ∈ P.cut.C₁ ∧ φ f b = 0} =
            {b | b ∈ U ∧ b.1 ∈ P.cut.C₁ ∧
              {z | C.toChain.stageMap 0 z = P.ιcircle b.1} ⊆ circleFaceSet74 dec.slim f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c' =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c' w) ∧
        (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen) ∩ U =
          {b | b ∈ U ∧ ∀ f ∈ L, φ f b ≤ 0} := by
  obtain ⟨hcC, hmem, hnri⟩ := C.frontier_circle_cbase_OBD P hS hc
  obtain ⟨O, L, φ, hO, hyO, hc1, hc2, hface, hsurj, hsign⟩ := geom.circleCorners _ hmem hnri
  have hιV : ContMDiff (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ (fun b : P.cut.circleBaseOpen => P.ιcircle b.1) :=
    hιc.comp (contMDiff_subtype_val (I := 𝓡 2) (U := P.cut.circleBaseOpen))
  let U : TopologicalSpace.Opens P.cut.circleBaseOpen :=
    ⟨(fun b : P.cut.circleBaseOpen => P.ιcircle b.1) ⁻¹' O, hO.preimage hιV.continuous⟩
  -- membership in `C₁` is membership of the image in `f₀(R_c)`
  have hZ : ∀ b : P.cut.circleBaseOpen, P.ιcircle b.1 ∈ C.toChain.stageMap 0 ''
      dec.slim.remainder ↔ b.1 ∈ P.cut.C₁ := by
    intro b
    rw [← P.cut_C₁]
    exact ⟨fun h => by
      obtain ⟨b', hb', hbb⟩ := h
      rw [← P.circle_ident.emb.injective hbb]
      exact hb', fun h => ⟨b.1, h, rfl⟩⟩
  have hfib : ∀ b : P.cut.circleBaseOpen, {z | C.toChain.stageMap 0 z = P.ιcircle b.1} =
      dec.bases.fibre 0 (P.ιcircle b.1) := by
    intro b
    ext z
    constructor
    · intro hz
      refine ⟨?_, hz⟩
      rw [dec.bases.circle_source_eq, mem_preimage, hz]
      exact P.circle_range ⟨b.1, rfl⟩
    · intro hz
      exact hz.2
  refine ⟨U, hyO, L, fun f b => φ f (P.ιcircle b.1), hc1, hc2, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨hsm, hφ0, hzero⟩ := hface f hf
    refine ⟨(hsm.contMDiffOn).comp hιV.contMDiffOn (fun b hb => hb), hφ0, ?_⟩
    ext b
    have hb := Set.ext_iff.1 hzero (P.ιcircle b.1)
    simp only [Set.mem_ofPred_eq] at hb ⊢
    rw [hfib b]
    constructor
    · rintro ⟨hbU, hbC, h0⟩
      exact ⟨hbU, hbC, ((hb.1 ⟨hbU, (hZ b).2 hbC, h0⟩).2.2)⟩
    · rintro ⟨hbU, hbC, h0⟩
      exact ⟨hbU, hbC, ((hb.2 ⟨hbU, (hZ b).2 hbC, h0⟩).2.2)⟩
  · exact C.circle_corners_surj_OBD P L φ hO hιc hyO
      (fun f hf => (hface f hf).1) hsurj
  · ext b
    have hb := Set.ext_iff.1 hsign (P.ιcircle b.1)
    have hbase : P.ιcircle b.1 ∈ dec.bases.base 0 := P.circle_range ⟨b.1, rfl⟩
    constructor
    · rintro ⟨hbC, hbU⟩
      have := hb.1 ⟨(hZ b).2 hbC, hbU⟩
      exact ⟨hbU, this.2⟩
    · rintro ⟨hbU, hfs⟩
      have := hb.2 ⟨⟨hbU, hbase⟩, hfs⟩
      exact ⟨(hZ b).1 this.1, hbU⟩

end BoundaryGaf02ChainE

end CircleCorners

end DifferentialGeometry.Geometry.Collapse
