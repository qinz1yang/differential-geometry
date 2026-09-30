# Additional API translation checks on the accepted migration

The baseline is `777299070a5529e96345e0033979706fd00c7e62`, Lean 4.35.0-rc3 / mathlib c55e6e786f49471c72fbddbec5415808896aec1e. These are code-level equivalence/compatibility checks; they introduce no new mathematical source claim.

## Positive spherical space forms

At old accepted commit `3167083409cd58f39742a7872dab504a65d24b56`, `Surgery/Contract/Terminal.lean:281–295` defines `IsConstantPositiveSectionalCurvature` and `IsPositiveSpaceFormModel`. The full source was read through the retained read-only Git object mirror and saved at `historical/old_positive_space_form.lean.txt`. The old covering implementation at `Sphere/Quotient/SpaceFormCovering.lean:113–146` is retained separately.

Old hypothesis:

```lean
(h : IsPositiveSpaceFormModel M)
```

New hypothesis, the exact expansion of the two removed definitions (with `ThreeModel = 𝓡 3`):

```lean
(h : ∃ g : SmoothRiemannianMetric (𝓡 3) M.Carrier,
  ∃ κ : ℝ, 0 < κ ∧ ∀ x (v w : TangentSpace (𝓡 3) x),
    LinearIndependent ℝ ![v, w] →
      Riemannian.sectionalCurvature g x v w = κ)
```

The conclusion of `GC.Geometry.complete_spherical_metric_of_positive_space_form` is unchanged. In the new accepted source, `Curvature/Metric/ConstantSectional.lean:35–64` proves the equivalence with `constantPositiveSectionalCurvatureMetric`; the forward and reverse implications explicitly handle dependent tangent pairs. `Sphere/Quotient/SpaceFormCovering.lean:62–75` supplies `exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature`. The migrated proof applies this equivalence and that actual oriented diffeomorphism producer. No old PC umbrella or private replacement foundation is restored. Direct elaboration is silent in `evidence/antipodal_quotient.log`; combined-root and transitive-axiom acceptance passed in the archived 802-module receipt.

## Manifold derivative equality

`SphericalProductPiece.lean` has an unchanged atlas statement. In mathlib c55e6e78, `Geometry/Manifold/MFDeriv/Basic.lean:1097–1107`, `Filter.EventuallyEq.mfderiv_eq` spells out a tangent-space cast followed by the original derivative. The proof now first assigns this equality the underlying `ℝ →L[ℝ] ℝ` type, then rewrites the original metric identity. The accepted metric producer is unchanged. Direct elaboration is silent in `evidence/spherical_product_piece.log`.

## Build storage and audit matching

The first combined-root attempt stopped on filesystem error 28. Only regenerable Lake setup JSON was removed, first from the superseded task build and then from the stopped current build. Lake 4.35 source inspection (`Lake/Build/Actions.lean:54–56`, `Lake/Build/Module.lean:986–1005`) confirmed that this invocation metadata is rewritten when a module is actually compiled and is not a cached output artifact. The resumed diagnostic removes setup JSON only after Lake reports that module built or replayed; the compiler command and proof checks are unchanged. The failure log and cleanup receipt are retained.

The audit matcher now includes the owning module before resolving private logical names. The existing FourPoint and HyperbolicSideComparison modules both contain a private `cos_add_cos_nonneg_of_sum_le_pi`; their fully qualified kernel names remain different. The gate still requires exactly one checked declaration in its registered module. All five full-static negative fixtures continue to be rejected.

## Oriented components of a disjoint sum

The accepted upstream renamed `ClosedOrientedManifold.sumComponentInl_orientedDiffeomorph` and `sumComponentInr_orientedDiffeomorph` to `sumComponentInlOrientedDiffeomorph` and `sumComponentInrOrientedDiffeomorph`. Their actual definitions were read in `Topology/ThreeManifold/CutCapCappedPresentationRealization.lean:402–406` and `578–582`: they still package the same component diffeomorphisms with their orientation proofs. Only these names change in the GC `CutCapFreeFactor` and `RetainedDiscardedLabels` callers. All public caller statements are unchanged. Direct checks are silent in `evidence/cut_cap_free_factor.log` and `evidence/retained_discarded_labels.log`; root and joint acceptance passed in the archived 802-module receipt.

## Initial markings and canonical tolerance

The accepted upstream's `Surgery/Topology/TowerBookkeeping.lean:59–69` now names the stage-zero transport `InitialIdentification.ofStageZero`; its unchanged map-HEq theorem still expresses precisely that transport. The GC callers in `History/MarkedContinuation` and `Noncollapsing/FiniteGeometricHorizon` use the new constructor spelling. `CanonicalNeighborhood/CanonicalToleranceMonotone.lean:134–139` now names the buffered witness constructor `BufferedCanonical.canonicalWitnessMono`; the GC `RoundReservedWitness` caller uses that name. These changes preserve the public caller statements and use the actual accepted constructors. Direct checks of `MarkedContinuation` and `RoundReservedWitness` are silent in their named evidence logs. The finite-horizon consumer and the complete migrated root now build successfully; the archived 802-module joint audit passed.

The same erased history parameter also left an unused, explicitly quantified `P₀` in the private cutoff-record helper in `SmallScaleFromDegree`. Removing that phantom quantifier lets its existing actual-history arguments determine the call again. The public small-scale noncollapsing statement is unchanged. Direct elaboration is silent in `evidence/small_scale_from_degree.log`.

## Retained-core event constructor

`RetainedCoreTower.lean:29–51` no longer stores `old_contains_outside` as a field: the old set is the whole retained core. Its actual conversion to `MetricCutCapEvent` at lines 57–81 proves that clause directly by `fun _ hx _ => hx`. The time-translated event therefore omits the removed constructor field; conversion still supplies the same containment property, and the actual terminal/output maps and metric equality are retained. Public time-translation statements are unchanged. The obsolete unused surgery namespace opening was also removed from `StandardFactorGeometry`, as in the earlier spherical adapter.

## Completed migration gate

The joint gate passed all 802 registered modules and 8,187 generated/authored declarations, with exactly the 22 historical direct admissions. Upstream mathematical sources, Lake files and toolchain were unchanged. The root completes 27,662 jobs; its inherited style/deprecation and authorized admission messages are not described as silent. The current gate also pins the independent chapter manifest and module-placement record, alongside the existing source hashes and skeleton crosswalks.
