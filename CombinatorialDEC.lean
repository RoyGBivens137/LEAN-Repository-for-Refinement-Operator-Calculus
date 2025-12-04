/-
Copyright (c) 2025 Zachary Mullaghy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Mullaghy
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Combinatorial Discrete Exterior Calculus

This file develops the combinatorial layer of DEC on simplicial complexes,
establishing the algebraic foundation for geometric refinement theory.

## Main Definitions

- `LevelComplex k`: Finite simplicial complex at refinement level k
- `ComplexRefinement C C'`: Refinement from coarse to fine complex
- `coboundary`: Coboundary operator d: Cᵖ → Cᵖ⁺¹
- `chainCodifferential`: Codifferential δ: Cᵖ⁺¹ → Cᵖ
- `cochainRefine`: Pullback of cochains along refinement

## Main Results

- `coboundary_comp_self`: d² = 0
- `chainCodifferential_comp_self`: δ² = 0
- `coboundary_cochainRefine`: d commutes with refinement

## Axioms (2)

| Axiom | Description |
|-------|-------------|
| `boundary_boundary` | ∂² = 0 (chain complex) |
| `face_compat` | Parent commutes with boundary (simplicial map) |

## References

- Arnold, Falk, Winther. "Finite element exterior calculus." Acta Numerica (2006)
- Desbrun, Hirani, Leok, Marsden. "Discrete exterior calculus." arXiv (2005)
-/

namespace CombinatorialDEC

/-!
## Helper Functions
-/

/-- Sum a list of reals -/
def List.sumReal (l : List ℝ) : ℝ := l.foldr (· + ·) 0

/-- Flatten a list of lists -/
def List.flatten {α : Type _} : List (List α) → List α
  | [] => []
  | h :: t => h ++ List.flatten t

/-- sumReal distributes over append -/
lemma List.sumReal_append (l₁ l₂ : List ℝ) :
    List.sumReal (l₁ ++ l₂) = List.sumReal l₁ + List.sumReal l₂ := by
  induction l₁ with
  | nil => simp [List.sumReal]
  | cons h t ih =>
      simp only [List.cons_append]
      unfold List.sumReal
      simp only [List.foldr]
      unfold List.sumReal at ih
      rw [ih]
      ring

/-- Scalar multiplication distributes over sumReal -/
lemma List.mul_sumReal (c : ℝ) (l : List ℝ) :
    c * List.sumReal l = List.sumReal (l.map (c * ·)) := by
  induction l with
  | nil => simp [List.sumReal]
  | cons h t ih =>
      unfold List.sumReal
      simp only [List.foldr, List.map]
      unfold List.sumReal at ih
      rw [mul_add, ih]

/-- Nested sums equal sum over flattened list -/
lemma List.sumReal_map_sumReal_eq_sumReal_flatten
    {α β : Type _}
    (l : List α)
    (g : α → List β)
    (w : α → β → ℝ) :
    List.sumReal (l.map fun a => List.sumReal ((g a).map fun b => w a b)) =
    List.sumReal (List.flatten (l.map fun a => (g a).map fun b => w a b)) := by
  induction l with
  | nil => simp [List.sumReal, List.flatten]
  | cons a t ih =>
      simp only [List.map, List.flatten]
      unfold List.sumReal
      simp only [List.foldr]
      unfold List.sumReal at ih
      rw [ih]
      symm
      apply List.sumReal_append

/-!
## Simplicial Complex Structure
-/

/-- A finite simplicial complex at refinement level k.

**Minimal version**: Just vertices, simplices, and boundary.
We'll add axioms (∂² = 0, etc.) incrementally as needed.
-/
structure LevelComplex (k : ℕ) where
  /-- Vertices of the complex -/
  Vertex : Type _
  [fintype_vertex : Fintype Vertex]

  /-- p-simplices for each dimension p -/
  simplex : ℕ → Type _
  [fintype_simplex : ∀ p, Fintype (simplex p)]

  /-- Boundary map: (p+1)-simplex → list of (p-face, sign) pairs -/
  boundary : ∀ {p}, simplex (p+1) → List (simplex p × ℤ)

  /-- 0-simplices are exactly vertices -/
  vertex_eq_0simplex : simplex 0 ≃ Vertex

  /-- Boundary of boundary is zero: ∂² = 0

  **Strengthened version**: For ANY cochain β, the sum ε₁·ε₂·β(ρ) over ∂²σ is zero.
  This is the precise algebraic statement needed to prove d² = 0.
  -/
  boundary_boundary : ∀ {p} (σ : simplex (p + 2)) (β : simplex p → ℝ),
    List.sumReal (List.flatten ((boundary σ).map fun (τ, ε₁) =>
      (boundary τ).map fun (ρ, ε₂) => (ε₁ * ε₂ : ℝ) * β ρ)) = 0

  /-- Coface map: p-simplex → list of ((p+1)-coface, sign) pairs.

  This is the "dual" of the boundary map: it tells us which (p+1)-simplices
  have a given p-simplex as a face.

  **For the sl₂ structure**: The Koszul differential κ needs to sum over cofaces.
  -/
  coface : ∀ {p}, simplex p → List (simplex (p+1) × ℤ)

  /-- Coface of coface is zero: δ² = 0 (dual to ∂² = 0).

  This ensures κ² = 0 when the Koszul differential is defined using cofaces.
  -/
  coface_coface : ∀ {p} (τ : simplex p) (α : simplex (p + 2) → ℝ),
    List.sumReal (List.flatten ((coface τ).map fun (σ, ε₁) =>
      (coface σ).map fun (ρ, ε₂) => (ε₁ * ε₂ : ℝ) * α ρ)) = 0

  /-- Boundary and coface are adjoint: if τ ∈ ∂σ with sign ε,
      then σ ∈ δτ with the same sign ε.

  This is the fundamental duality between chains and cochains.
  -/
  boundary_coface_adjoint : ∀ {p} (σ : simplex (p + 1)) (τ : simplex p) (ε : ℤ),
    (τ, ε) ∈ boundary σ ↔ (σ, ε) ∈ coface τ

  /-- Vertices of a p-simplex: the list of 0-simplices that make up σ.

  A p-simplex has exactly (p+1) vertices.
  This is needed for geometric computations (barycenters, etc.) -/
  vertices : ∀ {p}, simplex p → List (simplex 0)

  /-- A p-simplex has exactly (p+1) vertices. -/
  vertices_length : ∀ {p} (σ : simplex p), (vertices σ).length = p + 1

  /-- Vertices are distinct (no repeated vertices in a simplex). -/
  vertices_nodup : ∀ {p} (σ : simplex p), (vertices σ).Nodup

attribute [instance] LevelComplex.fintype_vertex
attribute [instance] LevelComplex.fintype_simplex

namespace LevelComplex

variable {k : ℕ} (L : LevelComplex k)

/-!
## DEC Coboundary Operator
-/

/-- Discrete Exterior Calculus coboundary operator

For a p-cochain α and a (p+1)-simplex σ:
  (dα)(σ) = Σ_{(τ,ε) ∈ ∂σ} ε · α(τ)
-/
noncomputable def coboundary {p : ℕ} (α : L.simplex p → ℝ) : L.simplex (p+1) → ℝ :=
  fun σ =>
    List.sumReal ((L.boundary σ).map fun (τ, ε) => (ε : ℝ) * α τ)

/-- d ∘ d = 0 (follows from ∂² = 0) -/
theorem coboundary_comp_self {p : ℕ} (α : L.simplex p → ℝ) :
    coboundary L (coboundary L α) = 0 := by
  funext σ
  simp only [coboundary]
  -- Expand d(dα)(σ) = Σ_{(τ,ε₁) ∈ ∂σ} ε₁ · (dα)(τ)
  --                 = Σ_{(τ,ε₁) ∈ ∂σ} ε₁ · Σ_{(ρ,ε₂) ∈ ∂τ} ε₂ · α(ρ)
  -- Step 1: push ε₁ into inner sum using distributivity
  have step1 : ∀ (τ : L.simplex (p + 1)) (ε₁ : ℤ),
      (ε₁ : ℝ) * List.sumReal ((L.boundary τ).map fun (ρ, ε₂) => (ε₂ : ℝ) * α ρ) =
      List.sumReal ((L.boundary τ).map fun (ρ, ε₂) => (ε₁ * ε₂ : ℝ) * α ρ) := by
    intro τ ε₁
    rw [List.mul_sumReal]
    congr 1
    induction L.boundary τ with
    | nil => rfl
    | cons head tail ih =>
        obtain ⟨ρ, ε₂⟩ := head
        simp only [List.map]
        rw [ih]
        ring_nf
  simp_rw [step1]
  -- Step 2: flatten nested sums
  rw [List.sumReal_map_sumReal_eq_sumReal_flatten]
  -- Now exactly matches boundary_boundary axiom
  exact L.boundary_boundary σ α

/-- Counting measure L² norm on p-cochains -/
noncomputable def l2Norm {p : ℕ} (α : L.simplex p → ℝ) : ℝ :=
  Real.sqrt (Finset.univ.sum fun σ => (α σ)^2)

/-!
## Codifferential (Chain-Level κ)

The codifferential δ is the "dual" of the boundary operator.
For a (p+1)-cochain α and a p-simplex τ:
  (δα)(τ) = Σ_{(σ,ε) ∈ coface(τ)} ε · α(σ)

This is the algebraic part of the Koszul differential.
-/

/-- Chain-level codifferential: the algebraic part of κ.

For a (p+1)-cochain α and a p-simplex τ:
  (δα)(τ) = Σ_{(σ,ε) ∈ coface(τ)} ε · α(σ)

This sums over all (p+1)-simplices σ that have τ as a face. -/
noncomputable def chainCodifferential {p : ℕ} (α : L.simplex (p + 1) → ℝ) : L.simplex p → ℝ :=
  fun τ =>
    List.sumReal ((L.coface τ).map fun (σ, ε) => (ε : ℝ) * α σ)

/-- δ ∘ δ = 0 (follows from coface² = 0) -/
theorem chainCodifferential_comp_self {p : ℕ} (α : L.simplex (p + 2) → ℝ) :
    chainCodifferential L (chainCodifferential L α) = 0 := by
  funext τ
  simp only [chainCodifferential]
  -- Expand δ(δα)(τ) = Σ_{(σ,ε₁) ∈ δτ} ε₁ · (δα)(σ)
  --                 = Σ_{(σ,ε₁) ∈ δτ} ε₁ · Σ_{(ρ,ε₂) ∈ δσ} ε₂ · α(ρ)
  -- Step 1: push ε₁ into inner sum using distributivity
  have step1 : ∀ (σ : L.simplex (p + 1)) (ε₁ : ℤ),
      (ε₁ : ℝ) * List.sumReal ((L.coface σ).map fun (ρ, ε₂) => (ε₂ : ℝ) * α ρ) =
      List.sumReal ((L.coface σ).map fun (ρ, ε₂) => (ε₁ * ε₂ : ℝ) * α ρ) := by
    intro σ ε₁
    rw [List.mul_sumReal]
    congr 1
    induction L.coface σ with
    | nil => rfl
    | cons head tail ih =>
        obtain ⟨ρ, ε₂⟩ := head
        simp only [List.map]
        rw [ih]
        ring_nf
  simp_rw [step1]
  -- Step 2: flatten nested sums
  rw [List.sumReal_map_sumReal_eq_sumReal_flatten]
  -- Now exactly matches coface_coface axiom
  exact L.coface_coface τ α

/-!
## Combinatorial Laplacian

The combinatorial Laplacian Δ = dδ + δd is the anticommutator of d and δ.

**Important**: The combinatorial Laplacian is NOT a scalar operator on general
simplicial complexes. The off-diagonal terms do NOT cancel in general.

The true Cartan identity requires GEOMETRIC structure (the Euler vector,
vertex positions, metric). This is handled in RefinementAxioms.lean where
JacobianDEC provides the necessary geometric data.
-/

/-- Combinatorial Laplacian: the anticommutator of d and δ.

    Δ = dδ + δd : C^{p+1} → C^{p+1}

    **Note**: This is NOT a scalar operator in general. The Cartan identity
    dκ + κd = H requires geometric structure (see JacobianDEC). -/
noncomputable def combinatorialLaplacian {p : ℕ}
    (β : L.simplex (p + 1) → ℝ) : L.simplex (p + 1) → ℝ :=
  fun σ =>
    (coboundary L (chainCodifferential L β)) σ +
    (chainCodifferential L (coboundary L β)) σ

end LevelComplex

/-!
## Complex Refinement
-/

/-- Refinement from coarse complex C to fine complex C' -/
structure ComplexRefinement {k : ℕ} (C : LevelComplex k) (C' : LevelComplex (k + 1)) where
  /-- Parent map on vertices -/
  parentVertex : C'.Vertex → C.Vertex

  /-- Parent map on p-simplices -/
  parentSimplex : ∀ {p}, C'.simplex p → C.simplex p

  /-- Face compatibility: parent commutes with boundary

  This axiom ensures that refinement respects the simplicial structure:
  the parent of a face is a face of the parent.

  This is the **key axiom** making refinement a chain map.
  -/
  face_compat : ∀ {p} (σ' : C'.simplex (p + 1)),
    (C'.boundary σ').map (fun (τ', ε) => (parentSimplex τ', ε)) =
    C.boundary (parentSimplex σ')

namespace ComplexRefinement

variable {k : ℕ} {C : LevelComplex k} {C' : LevelComplex (k + 1)}
variable (R : ComplexRefinement C C')

/-!
## Cochain Refinement
-/

/-- Refine a coarse p-cochain to a fine p-cochain

**Combinatorial version**: Pure pullback along parent map, no normalization.
This makes refinement a cochain map: d ∘ refine = refine ∘ d.

L² isometry will be handled at the geometric/measure layer.
-/
def cochainRefine {p : ℕ} (α : C.simplex p → ℝ) : C'.simplex p → ℝ :=
  fun σ' => α (R.parentSimplex σ')

/-- Coboundary commutes with refinement: d ∘ refine = refine ∘ d -/
theorem coboundary_cochainRefine {p : ℕ} (α : C.simplex p → ℝ) :
    C'.coboundary (R.cochainRefine α) = R.cochainRefine (C.coboundary α) := by
  funext σ'
  simp only [LevelComplex.coboundary, cochainRefine, List.sumReal]
  -- d(refine α)(σ') = Σ_{(τ',ε) ∈ ∂σ'} ε · α(parent τ')
  -- By face_compat: map parent over ∂σ' gives ∂(parent σ')
  --               = Σ_{(τ,ε) ∈ ∂(parent σ')} ε · α(τ)
  --               = (dα)(parent σ')
  --               = (refine (dα))(σ')
  -- The key: rewrite using face_compat to swap boundaries
  congr 1
  rw [← R.face_compat σ']
  simp only [List.map_map]
  rfl

end ComplexRefinement

end CombinatorialDEC
