# Formalization Status — Geometric Refinement Theory (GRT)

Purpose
- Make explicit which claims in this repository are fully machine-checked by Lean, which are reduced to smaller lemmas, and which are currently axiomatized due to missing mathlib infrastructure. This is intended to guide contributors who want to remove axioms.

How to read this file
- "Proved" means the claim has a Lean proof in this repo.
- "Reduced" means the claim is proved modulo one or more axioms; the reduction is implemented.
- "Axiomatic" means the claim is introduced as an `axiom` in the code and depends on external literature or missing infrastructure.

Legend: (file : lemma/theorem) — status — dependencies / upgrade path

Core axioms (explicitly cited in README and code)
- (RefinementAxioms.lean : moser_equivalence) — Axiomatic
  - Reference: Moser, Trans. AMS 120 (1965).
  - Missing infra: smooth manifold + PDE/divergence solution machinery.
  - Upgrade path: formalize Moser in polynomial case first (moser_equivalence_poly), then extend via approximation and compactness.

- (RefinementAxioms.lean : moser_equivalence_poly) — Axiomatic / Target for formalization
  - Reference: Dacorogna–Moser.
  - Suggestion: implement polynomial-specialized constructive proof; polynomial maps allow algebraic handling.

- (RefinementAxioms.lean : moser_jacobian_averages_to_one) — Axiomatic
  - Role: technical change-of-variables result for Moser maps.
  - Suggestion: derive from moser_equivalence_poly once available.

- (RefinementAxioms.lean : du_faber_gunzburger_existence) — Axiomatic
  - Role: CVT existence/variational characterization.
  - Missing infra: calculus of variations / compactness & lower-semicontinuity.
  - Suggestion: 1D discretized CVT first; then OT-based proof.

- (RefinementAxioms.lean : laguerre_weight_uniqueness) — Axiomatic
  - Role: uniqueness of Laguerre weights in weighted Voronoi.
  - Missing infra: convex duality and power-diagram formalization.
  - Suggestion: prove for finite-site polynomial case.

- (RefinementAxioms.lean : centroid_minimizes_energy) — Reduced → Proveable
  - Role: standard variational lemma (finite-dimensional calculus).
  - Suggestion: formalize using standard analysis tools in mathlib.

- (RefinementAxioms.lean : shape_similarity_forces_constant_step) — Axiomatic
  - Role: additive combinatorics lemma used for step forcing.
  - Suggestion: consider specializing to the finite combinatorial case needed.

- (RefinementAxioms.lean : entropy_sl_invariant_isotropic) — Axiomatic
  - Role: thermodynamic invariance under SL action.
  - Suggestion: formalize for polynomial/finite approximations first.

- (RefinementAxioms.lean : weighted_coface_coface) — Likely Proveable
  - Role: DEC combinatorial identity.
  - Suggestion: formalize in CombinatorialDEC.lean; likely minimal upstream needed.

- (RefinementAxioms.lean : offDiagonal_sum_zero) — Likely Proveable
  - Role: Cartan/linear algebra identity.
  - Suggestion: formalize using Mathlib linear algebra.

- (RefinementAxioms.lean : diagonal_sum_identity) — Likely Proveable
  - Role: linear algebra identity.

- (RefinementAlgebra.lean : cyclic_tower_rigidity) — Axiomatic
  - Reference: Serre LNM 1500 (1992)
  - Missing infra: profinite group / p-adic towers
  - Suggestion: formalize the specific finite-grid rigidity statement you need rather than the full theorem.

Additional axioms in RefinementAlgebra
- (RefinementAlgebra.lean : mass_metric_volume_property) — Axiomatic
  - Role: equates mass-metric Voronoi cell volumes with Jacobian integrals.
  - Missing infra: Riemannian manifold volume form for conformal metric J^{1/n}.
  - Suggestion: prove in coordinates for C¹ densities; start 1D and then 2D.

- (RefinementAlgebra.lean : cvt_variational_uniqueness) — Axiomatic
  - Role: uniqueness of CVT from variational problem.
  - Missing infra: Brenier/OT machinery.
  - Suggestion: 1D Brenier first; then generalize.

- (RefinementAlgebra.lean : voronoi_equal_mass_implies_cvt) — Axiomatic
  - Role: shows Voronoi equal-mass cells are centroidal (CVTs).
  - Suggestion: derive from cvt_variational_uniqueness once available.

- (RefinementAlgebra.lean : bentCube_measure_preserved) — Axiomatic
  - Role: Moser pullback preserves measure of flat cell.
  - Suggestion: derive from polynomial Moser or explicit construction.

Practical contributor tasks (first milestones)
1. Prove moser_equivalence_poly for polynomial Jacobians on compact domains.
2. Prove bentCube_measure_preserved under polynomial Moser maps.
3. Formalize DEC combinatorial lemmas (weighted_coface_coface, offDiagonal_sum_zero, diagonal_sum_identity).
4. Implement mass metric path-integral in 1D and prove mass_metric_volume_property in 1D.
5. Formalize 1D Brenier monotone rearrangement and a 1D CVT uniqueness lemma.

Community engagement recommendations
- Open issues per axiom with clearly listed milestones (polynomial variant → 1D → general).
- Minimal Zulip posts showing the polynomial Moser example + request for pointers.
- Upstream small lemmas that are reusable (DEC combinatorics, finite-site Laguerre uniqueness) rather than monolithic theorems.

If you want me to:
- create this FORMALIZATION_STATUS.md in your repo as a PR, say "create status file",
- or open issues for the top N axioms, say "create issues" and list which ones (or let me pick top 4),
I will proceed.
