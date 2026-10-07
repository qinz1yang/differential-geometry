import DifferentialGeometry.Geometry.Exponential.Cartan.NormGeneralHGI
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Exponential
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Curvature
import DifferentialGeometry.Geometry.Exponential.Cartan.Norm
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import DifferentialGeometry.Geometry.Metric.Polarization
import DifferentialGeometry.Geometry.Metric.Completeness

noncomputable section

open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

private theorem hyperboloid_riemannOp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (x : Hyperboloid E)
    (X Y Z : TangentSpace 𝓘(ℝ, E) x) :
    Curvature.riemannOp (Connection.LeviCivita Hyperboloid.riemannianMetric) x X Y Z =
      (-1 : ℝ) • (Hyperboloid.riemannianMetric.inner x Y Z • X -
        Hyperboloid.riemannianMetric.inner x X Z • Y) := by
  let g := Hyperboloid.riemannianMetric (E := E)
  let A := Curvature.riemannOp (Connection.LeviCivita g) x X Y Z
  let B := (-1 : ℝ) • (g.inner x Y Z • X - g.inner x X Z • Y)
  have hp (W : TangentSpace 𝓘(ℝ, E) x) : g.inner x W A = g.inner x W B := by
    rw [← CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp]
    rw [Hyperboloid.metricRm04StandardAt_riemannianMetric]
    simp only [B, map_smul, map_sub, smul_eq_mul]
    rw [g.symm x W X, g.symm x W Y]
    ring
  by_contra hne
  have hd : A - B ≠ 0 := sub_ne_zero.mpr hne
  have hh : g.inner x (A - B) (A - B) = 0 := by
    rw [map_sub, hp, sub_self]
  exact (ne_of_gt (g.pos x (A - B) hd)) hh

private theorem hyperboloid_inner_origin {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a b : E) :
    Hyperboloid.riemannianMetric.inner (Hyperboloid.origin : Hyperboloid E)
      (show TangentSpace 𝓘(ℝ, E) (Hyperboloid.origin : Hyperboloid E) from a)
      (show TangentSpace 𝓘(ℝ, E) (Hyperboloid.origin : Hyperboloid E) from b) = inner ℝ a b := by
  rw [Hyperboloid.riemannianMetric_inner, Hyperboloid.mfderiv_spaceDiffeomorph]
  simp only [Hyperboloid.origin_space, inner_zero_left, zero_mul, zero_div, sub_zero]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def hyperbolicComparison (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    (E ≃ₗᵢ[ℝ] TangentSpace I p) → Hyperboloid E → M := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  intro i
  exact fun x => expMapIntrinsic (I := I) g hEnorm p
    (i (Hyperboloid.expMapIntrinsicOriginDiffeomorph.symm x))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolicComparison_apply (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    let hEnorm : IsMetricNorm (I := I) g :=
      fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p) (x : Hyperboloid E),
      hyperbolicComparison g hg p i x = expMapIntrinsic (I := I) g hEnorm p
        (i (Hyperboloid.expMapIntrinsicOriginDiffeomorph.symm x)) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  dsimp only
  intro i x
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem contMDiff_hyperbolicComparison (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p),
      ContMDiff 𝓘(ℝ, E) I ∞ (hyperbolicComparison g hg p i) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  intro i
  let Φ := Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)
  let j : E ≃L[ℝ] E :=
    (show E ≃ₗ[ℝ] E from i.toLinearEquiv).toContinuousLinearEquiv
  let expM : E → M := fun u => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from u)
  have hExp : ContMDiff 𝓘(ℝ, E) I ∞ expM := intrinsicFiber_smooth g hEnorm p
  have hj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun u : E => j u) := j.contDiff.contMDiff
  exact hExp.comp (hj.comp Φ.symm.contMDiff)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolicComparison_inner_of_radial_curvature (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    let hEnorm : IsMetricNorm (I := I) g :=
      fun q v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g q v
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p) (x : Hyperboloid E),
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        let q := intrinsicGeodesic g hEnorm p
          (i (Hyperboloid.expMapIntrinsicOriginDiffeomorph.symm x)) t
        ∀ (X Y Z : TangentSpace I q),
          Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
            (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) →
      ∀ (Y Z : TangentSpace 𝓘(ℝ, E) x),
      g.inner (hyperbolicComparison g hg p i x)
        (mfderiv 𝓘(ℝ, E) I (hyperbolicComparison g hg p i) x Y)
        (mfderiv 𝓘(ℝ, E) I (hyperbolicComparison g hg p i) x Z) =
          Hyperboloid.riemannianMetric.inner x Y Z := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  dsimp only
  intro i x hR
  let _ : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨(Hyperboloid.riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
  let hHNorm := isMetricNorm_of_riemannianBundle (Hyperboloid.riemannianMetric (E := E))
  let _ : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
    ⟨fun a b => (Hyperboloid.riemannianEDistOf_eq_edist a b).symm⟩
  let _ : IsContinuousRiemannianBundle E
      (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) := hHNorm.isContinuousRiemannianBundle
  let Φ := Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)
  let j : E ≃L[ℝ] E :=
    (show E ≃ₗ[ℝ] E from i.toLinearEquiv).toContinuousLinearEquiv
  let expM : E → M := fun u => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from u)
  let F : Hyperboloid E → M := expM ∘ (fun u : E => j u) ∘ Φ.symm
  have hExp : ContMDiff 𝓘(ℝ, E) I ∞ expM := intrinsicFiber_smooth g hEnorm p
  have hj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun u : E => j u) := j.contDiff.contMDiff
  change ∀ (Y Z : TangentSpace 𝓘(ℝ, E) x),
    g.inner (F x) (mfderiv 𝓘(ℝ, E) I F x Y) (mfderiv 𝓘(ℝ, E) I F x Z) =
      Hyperboloid.riemannianMetric.inner x Y Z
  intro Y Z
  apply inner_eq_of_diag Hyperboloid.riemannianMetric g x (F x) (mfderiv 𝓘(ℝ, E) I F x)
  intro V
  let u : E := Φ.symm x
  let w : E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ.symm x V
  have hbase : Φ u = x := Φ.apply_symm_apply x
  have hright : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ u w = V := by
    have hchain := mfderiv_comp_apply x
      (Φ.contMDiff.mdifferentiableAt (by simp) (x := u))
      (Φ.symm.contMDiff.mdifferentiableAt (by simp) (x := x)) V
    have heq : (Φ : E → Hyperboloid E) ∘ Φ.symm = id := funext Φ.apply_symm_apply
    rw [heq, mfderiv_id] at hchain
    exact hchain.symm
  have hmap : mfderiv 𝓘(ℝ, E) I F x V = mfderiv 𝓘(ℝ, E) I expM (j u) (j w) := by
    have hmid := mfderiv_comp_apply x
      (j.mdifferentiableAt (x := u))
      (Φ.symm.contMDiff.mdifferentiableAt (by simp) (x := x)) V
    rw [ContinuousLinearEquiv.mfderiv_eq] at hmid
    have hchain := mfderiv_comp_apply x
      (hExp.mdifferentiableAt (by simp) (x := j u))
      ((hj.comp Φ.symm.contMDiff).mdifferentiableAt (by simp) (x := x)) V
    rw [hmid] at hchain
    exact hchain
  have hi (a b : E) : g.inner p (j a) (j b) =
      Hyperboloid.riemannianMetric.inner (Hyperboloid.origin : Hyperboloid E) a b := by
    rw [hyperboloid_inner_origin]
    change g.inner p (i a) (i b) = inner ℝ a b
    rw [← hEnorm.inner_eq]
    exact i.inner_map_map a b
  have ht := expMapIntrinsic_mfderiv_inner_self_eq_of_radial_curvature
    (I := 𝓘(ℝ, E)) (I' := I) Hyperboloid.riemannianMetric hHNorm g hEnorm
    Hyperboloid.origin p u w j hi (-1)
    (fun t _ => hyperboloid_riemannOp _)
    hR
  have hmodel : (fun a : E => expMapIntrinsic (I := 𝓘(ℝ, E))
        Hyperboloid.riemannianMetric hHNorm Hyperboloid.origin
        (show TangentSpace 𝓘(ℝ, E) (Hyperboloid.origin : Hyperboloid E) from a)) = Φ := by
    funext a
    rfl
  rw [hmodel] at ht
  change g.inner (expM (j u))
    (mfderiv 𝓘(ℝ, E) I expM (j u) (j w))
    (mfderiv 𝓘(ℝ, E) I expM (j u) (j w)) =
      Hyperboloid.riemannianMetric.inner (Φ u)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ u w)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ u w) at ht
  have hsource : Hyperboloid.riemannianMetric.inner (Φ u)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ u w)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ u w) =
        Hyperboloid.riemannianMetric.inner x V V :=
    congrArg₂ (fun (z : Hyperboloid E) (a : E) => Hyperboloid.riemannianMetric.inner z
      (show TangentSpace 𝓘(ℝ, E) z from a) (show TangentSpace 𝓘(ℝ, E) z from a))
      hbase (show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ u w : E) = (V : E) from hright)
  exact (congrArg (fun W : TangentSpace I (F x) => g.inner (F x) W W) hmap).trans
    (ht.trans hsource)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolicComparison_inner (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hR : ∀ (q : M) (X Y Z : TangentSpace I q),
      Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
        (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p)
      (x : Hyperboloid E) (Y Z : TangentSpace 𝓘(ℝ, E) x),
      g.inner (hyperbolicComparison g hg p i x)
        (mfderiv 𝓘(ℝ, E) I (hyperbolicComparison g hg p i) x Y)
        (mfderiv 𝓘(ℝ, E) I (hyperbolicComparison g hg p i) x Z) =
          Hyperboloid.riemannianMetric.inner x Y Z := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  intro i x Y Z
  exact hyperbolicComparison_inner_of_radial_curvature g hg p i x
    (fun t _ => hR (intrinsicGeodesic g hEnorm p
      (i (Hyperboloid.expMapIntrinsicOriginDiffeomorph.symm x)) t)) Y Z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isLocalDiffeomorph_hyperbolicComparison (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hR : ∀ (q : M) (X Y Z : TangentSpace I q),
      Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
        (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) :
    letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p),
      IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ (hyperbolicComparison g hg p i) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  intro i
  let F := hyperbolicComparison g hg p i
  apply isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ.mpr
  apply (contMDiff_hyperbolicComparison g hg p i).contMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv
    isOpen_univ (by simp)
  intro x _
  have hi : Function.Injective (mfderiv 𝓘(ℝ, E) I F x) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h := hyperbolicComparison_inner g hg p hR i x v v
    rw [hv] at h
    have hz : Hyperboloid.riemannianMetric.inner x v v = 0 := by
      simpa only [map_zero, zero_apply] using h.symm
    by_contra hne
    exact (ne_of_gt (Hyperboloid.riemannianMetric.pos x v hne)) hz
  have hs := LinearMap.surjective_of_injective hi
  let D : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective (mfderiv 𝓘(ℝ, E) I F x)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  exact ⟨D, rfl⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential
