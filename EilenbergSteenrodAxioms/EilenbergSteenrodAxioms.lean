/-
Copyright (c) 2026 Wolfgang Schamltz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wolfgang Schmaltz
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import EilenbergSteenrodAxioms.TopologicalPair
public import EilenbergSteenrodAxioms.AlgebraicMayerVietoris

@[expose] public section

open CategoryTheory ContinuousMap TopPair DirectSum ShortComplex Limits AlgebraicMayerVietoris

namespace EilenbergSteenrodAxioms

universe u v

structure ESHomologyTheoryI where
  /- 
  For every integer (n : ℤ) we have a functor H n from
  - the Category of Topological Pairs, with objects (X,A) where A ⊆ X
  - to the Category of Abelian Groups. 
  -/
  H : ℤ → TopPair ⥤ Ab

  /- The Boundary Natural Transformation -/
  boundary : (n m : ℤ) → (H n ⟶ functor_ρ ⋙ H m)
  /- If m is not exactly n - 1 the boundary map is 0. -/
  boundary_shape : ∀ (n m : ℤ), m ≠ n - 1 → boundary n m = 0

  /- 1. Homotopy Axiom -/
  homotopy_invariant (n : ℤ) {P Q : TopPair} (f g : P ⟶ Q) : 
    HomotopicPairHom f g → (H n).map f = (H n).map g

  /- 2. Excision Axiom -/
  excision (n : ℤ) (X : Type u) [TopologicalSpace X] (A U: Set X) (h : closure U ⊆ interior A) :
    IsIso ((H n).map (excision_map X A U))

  /- 3. Dimension Axiom -/
  /- PUnit is the universe polymorphic verion of the one-point Type. -/
  /- PUnit has an implicit topology via instTopologicalSpacePunit. -/
  /- Update: PUnit should be replaced by the appropriate condition that 'IsTerminal'. -/
  /- Given a group G, Subsingleton G is the Prop that G is the trivial group. -/
  /- Although, with further investigation, IsZero might be appropriate. -/
  /- In the case of Abelian groups, this is not completely clear, but since we are in the category of Abelian groups, it seems standard. -/
  dimension {n : ℤ} (X : Type u) [TopologicalSpace X] [Unique X] : n ≠ 0 → IsZero ((H n).obj (X, ∅)ₜₚ)

  /- 4. Additivity Axiom -/
  additivity (n : ℤ) {I : Type u} [Fintype I] (X : I → Type u) [∀ (i : I), TopologicalSpace (X i)] : 
    (H n).obj ( ((Σi, X i), ∅)ₜₚ) ≅  ⨁ (fun i ↦ (H n).obj (X i, ∅)ₜₚ)

namespace ESHomologyTheoryI
variable (ES : ESHomologyTheoryI)
def hom_i (n : ℤ) (X : Type u) [TopologicalSpace X] (A B : Set X) : 
  (ES.H n).obj (A ∩ᵣ B, ∅)ₜₚ  ⟶ (ES.H n).obj (A, ∅)ₜₚ := (ES.H n).map (inclusion_i A B)
def hom_j (n : ℤ) (X : Type u) [TopologicalSpace X] (A B : Set X) : 
  (ES.H n).obj (A ∩ᵣ B, ∅)ₜₚ  ⟶ (ES.H n).obj (B, ∅)ₜₚ := (ES.H n).map (inclusion_j A B)
def hom_k (n : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : 
  (ES.H n).obj (A, ∅)ₜₚ ⟶ (ES.H n).obj (X, ∅)ₜₚ := (ES.H n).map (inclusion_k X A)
def hom_x (n : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : 
  (ES.H n).obj (X, ∅)ₜₚ ⟶ (ES.H n).obj (X, A)ₜₚ := (ES.H n).map (inclusion_X_to_XA X A)
def hom_cover (n : ℤ) (X : Type u) [TopologicalSpace X] (A B : Set X) : 
  (ES.H n).obj (B, A ∩ᵣ B)ₜₚ ⟶ (ES.H n).obj (X, A)ₜₚ := (ES.H n).map (excision_cover_map X A B)
def delta (n m : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : 
  (ES.H n).obj (X, A)ₜₚ ⟶ (ES.H m).obj (A, ∅)ₜₚ := 
  (ES.boundary n m).app (X, A)ₜₚ
end ESHomologyTheoryI

structure ESHomologyTheoryII extends ESHomologyTheoryI where
  /- Assert that compositions are zero. -/
  zero_kx (n : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : 
    (toESHomologyTheoryI.hom_k n X A) ≫ (toESHomologyTheoryI.hom_x n X A) = 0
  zero_xd (n m : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : 
    (toESHomologyTheoryI.hom_x n X A) ≫ (toESHomologyTheoryI.delta n m X A) = 0
  zero_dk (n m : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : 
    (toESHomologyTheoryI.delta n m X A) ≫ (toESHomologyTheoryI.hom_k m X A) = 0

namespace ESHomologyTheoryII
variable (ES : ESHomologyTheoryII)
/- H_n (A, ∅) →[hom_k] H_n (X, ∅) →[hom_x] H_n (X, A) -/
def S_kx (n : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : ShortComplex Ab :=
  ShortComplex.mk 
    (ES.hom_k n X A)
    (ES.hom_x n X A)
    (ES.zero_kx n X A)
/- H_n (X, ∅) →[hom_x] H_n (X, A) →[delta] H_(n-1) (A, ∅) -/
def S_xd (n m : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : ShortComplex Ab :=
  ShortComplex.mk 
    (ES.hom_x n X A)
    (ES.delta n m X A)
    (ES.zero_xd n m X A)
/- H_n (X, A) →[delta] H_(n-1) (A, ∅) →[hom_k] H_(n-1) (X, ∅) -/
def S_dk (n m : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) : ShortComplex Ab :=
  ShortComplex.mk 
    (ES.delta n m X A)
    (ES.hom_k m X A)
    (ES.zero_dk n m X A)
end ESHomologyTheoryII

structure EilenbergSteenrodHomologyTheory extends ESHomologyTheoryII where
  /- 5. Exactness Axiom -/
  exactness_kx (n : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) :
    (toESHomologyTheoryII.S_kx n X A).Exact
  exactness_xd (n m : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) (h : m = n - 1) :
    (toESHomologyTheoryII.S_xd n m X A).Exact
  exactness_dk (n m : ℤ) (X : Type u) [TopologicalSpace X] (A : Set X) (h : m = n - 1) :
    (toESHomologyTheoryII.S_dk n m X A).Exact

/- We take a moment to prepare the setup for proving Mayer-Vietoris. -/
lemma closure_compl_subset_interior {X : Type*} [TopologicalSpace X] {A B : Set X} (h_cover : interior A ∪ interior B = Set.univ) 
  : closure (Bᶜ) ⊆ interior A := by
  -- The closure of a complement is the complement of the interior
  rw [closure_compl]
  intro x hx
  have hx_univ : x ∈ interior A ∪ interior B := by
    rw [h_cover]
    exact Set.mem_univ x
  cases hx_univ with
  | inl hA => 
    exact hA
  | inr hB => 
    contradiction

instance hom_cover_isIso (ES : EilenbergSteenrodHomologyTheory) (n : ℤ) (X : Type u) [TopologicalSpace X] (A B : Set X) (h_cover : interior A ∪ interior B = Set.univ) : IsIso (ES.hom_cover n X A B) := by
  -- 1. Rewrite hom_cover using our factored topology maps
  have h_eq : ES.hom_cover n X A B = 
      (ES.H n).map (excise_equiv_cover X A B).hom ≫ (ES.H n).map (excision_map X A Bᶜ) := by
    rw [← (ES.H n).map_comp]
    congr 1
  rw [h_eq]
  -- 2. Supply the excision axiom instance to the local context
  have h_subset : closure (Bᶜ) ⊆ interior A := closure_compl_subset_interior h_cover
  haveI : IsIso ((ES.H n).map (excision_map X A Bᶜ)) := ES.excision n X A Bᶜ h_subset
  -- 3. The first map is an iso because functors preserve isomorphisms.
  -- The second map is an iso by the excision axiom.
  -- Lean's typeclass inference automatically knows the composition of isos is an iso!
  infer_instance

def MayerVietorisSetup
  (ES : EilenbergSteenrodHomologyTheory) 
  (n : ℤ) 
  (X : Type u) [TopologicalSpace X] 
  (A B : Set X)
  (h_cover : interior A ∪ interior B = Set.univ)
  : AlgMayerVietorisInput Ab := 
  let H := ES.H
  {
  /- Objects -/
  A := (H (n + 1)).obj (B, A ∩ᵣ B)ₜₚ
  B := (H n).obj (A ∩ᵣ B, ∅)ₜₚ
  C := (H n).obj (B, ∅)ₜₚ
  D := (H n).obj (B, A ∩ᵣ B)ₜₚ
  E := (H (n - 1)).obj (A ∩ᵣ B, ∅)ₜₚ
  F := (H (n - 1)).obj (B, ∅)ₜₚ
  A' := (H (n + 1)).obj (X, A)ₜₚ
  B' := (H n).obj (A, ∅)ₜₚ
  C' := (H n).obj (X, ∅)ₜₚ
  D' := (H n).obj (X, A)ₜₚ
  E' := (H (n - 1)).obj (A, ∅)ₜₚ
  F' := (H (n - 1)).obj (X, ∅)ₜₚ

  /- Horizontal Morphisms -/
  mor_AB := ES.delta (n + 1) n  B (A ∩ᵣ B)
  mor_BC := ES.hom_k n B (A ∩ᵣ B)
  mor_CD := ES.hom_x n B (A ∩ᵣ B)
  mor_DE := ES.delta n (n - 1) B (A ∩ᵣ B )
  mor_EF := ES.hom_k (n - 1) B (A ∩ᵣ B)

  mor_A'B' := ES.delta (n + 1) n X A 
  mor_B'C' := ES.hom_k n X A
  mor_C'D' := ES.hom_x n X A
  mor_D'E' := ES.delta n (n - 1) X A 
  mor_E'F' := ES.hom_k (n - 1) X A

  /- Vertical Morphisms -/
  mor_AA' := ES.hom_cover (n + 1) X A B
  mor_BB' := ES.hom_i n X A B
  mor_CC' := ES.hom_k n X B
  mor_DD' := ES.hom_cover n X A B
  mor_EE' := ES.hom_i (n - 1) X A B
  mor_FF' := ES.hom_k (n - 1) X B

  /- Excision Isomorphisms -/
  excision_iso_AA' := hom_cover_isIso ES (n + 1) X A B h_cover
  excision_iso_DD' := hom_cover_isIso ES n X A B h_cover

  /- Commutativity Conditions -/
  comm_AB := by 
    dsimp [ESHomologyTheoryI.hom_cover, ESHomologyTheoryI.delta, ESHomologyTheoryI.hom_i]
    have h_nat := (ES.boundary (n + 1) n).naturality (excision_cover_map X A B)
    exact h_nat.symm
  comm_BC := by 
    dsimp [ESHomologyTheoryI.hom_k, ESHomologyTheoryI.hom_i]
    rw [← (ES.H n).map_comp, ← (ES.H n).map_comp]
    congr 1
  comm_CD := by
    dsimp [ESHomologyTheoryI.hom_x, ESHomologyTheoryI.hom_k, ESHomologyTheoryI.hom_cover]
    rw [← (ES.H n).map_comp, ← (ES.H n).map_comp]
    congr 1
  comm_DE := by 
    dsimp [ESHomologyTheoryI.hom_cover, ESHomologyTheoryI.delta, ESHomologyTheoryI.hom_i]
    have h_nat := (ES.boundary n (n - 1)).naturality (excision_cover_map X A B)
    exact h_nat.symm
  comm_EF := by
    dsimp [ESHomologyTheoryI.hom_k, ESHomologyTheoryI.hom_i]
    rw [← (ES.H (n - 1)).map_comp, ← (ES.H (n - 1)).map_comp]
    rfl

  /- Zero Compositions -/
  zero_ABC := ES.zero_dk (n + 1) n B (A ∩ᵣ B)
  zero_BCD := ES.zero_kx n B (A ∩ᵣ B)
  zero_CDE := ES.zero_xd n (n - 1) B (A ∩ᵣ B)
  zero_DEF := ES.zero_dk n (n - 1) B (A ∩ᵣ B)
  zero_A'B'C' := ES.zero_dk (n + 1) n X A
  zero_B'C'D' := ES.zero_kx n X A
  zero_C'D'E' := ES.zero_xd n (n - 1) X A
  zero_D'E'F' := ES.zero_dk n (n - 1) X A

  /- Exactness -/
  exact_ABC := ES.exactness_dk (n + 1) n B (A ∩ᵣ B) (by omega)
  exact_BCD := ES.exactness_kx n B (A ∩ᵣ B)
  exact_CDE := ES.exactness_xd n (n - 1) B (A ∩ᵣ B) (by omega)
  exact_DEF := ES.exactness_dk n (n - 1) B (A ∩ᵣ B) (by omega)
  exact_A'B'C' := ES.exactness_dk (n + 1) n X A (by omega)
  exact_B'C'D' := ES.exactness_kx n X A
  exact_C'D'E' := ES.exactness_xd n (n - 1) X A (by omega)
  exact_D'E'F' := ES.exactness_dk n (n - 1) X A (by omega)
  }

/- Mayer-Vietoris Sequence for a Pair -/
noncomputable section
variable (ES : EilenbergSteenrodHomologyTheory) (n : ℤ) (X : Type u) [TopologicalSpace X] (A B : Set X) (h_cover : interior A ∪ interior B = Set.univ)
local notation "H" => ES.H

def α : (H n).obj (A ∩ᵣ B, ∅)ₜₚ ⟶ (H n).obj (A, ∅)ₜₚ ⊞ (H n).obj (B, ∅)ₜₚ :=
  biprod.lift (ES.hom_i n X A B) (-ES.hom_k n B (A ∩ᵣ B))
def β : (H n).obj (A, ∅)ₜₚ ⊞ (H n).obj (B, ∅)ₜₚ ⟶ (H n).obj (X, ∅)ₜₚ :=
  biprod.desc (ES.hom_k n X A) (ES.hom_k n X B)
def Δ : (H n).obj (X, ∅)ₜₚ ⟶ (H (n - 1)).obj (A ∩ᵣ B, ∅)ₜₚ:=
  haveI : IsIso (ES.hom_cover n X A B) := hom_cover_isIso ES n X A B h_cover
  (ES.hom_x n X A) ≫ inv (ES.hom_cover n X A B) ≫ (ES.delta n (n - 1) B (A ∩ᵣ B ))

lemma αβ_zero (h_cover : interior A ∪ interior B = Set.univ) : (α ES n X A B) ≫ (β ES n X A B) = 0 := by 
  exact AlgebraicMayerVietoris.αβ_zero (Z := MayerVietorisSetup ES n X A B h_cover)
lemma βΔ_zero : (β ES n X A B) ≫ (Δ ES n X A B h_cover) = 0 := by
  exact AlgebraicMayerVietoris.βΔ_zero (Z := MayerVietorisSetup ES n X A B h_cover)
lemma Δα_zero : (Δ ES n X A B h_cover) ≫ (α ES (n - 1) X A B) = 0 := by
  exact AlgebraicMayerVietoris.Δγ_zero (Z := MayerVietorisSetup ES n X A B h_cover)

def S_αβ := ShortComplex.mk 
  (α ES n X A B) 
  (β ES n X A B) 
  (by exact αβ_zero ES n X A B h_cover)
def S_βΔ := ShortComplex.mk 
  (β ES n X A B) 
  (Δ ES n X A B h_cover) 
  (by exact βΔ_zero ES n X A B h_cover) 
def S_Δα := ShortComplex.mk 
  (Δ ES n X A B h_cover) 
  (α ES (n - 1) X A B) 
  (by exact Δα_zero ES n X A B h_cover)

lemma αβ_exact : (S_αβ ES n X A B h_cover).Exact := by
  exact AlgebraicMayerVietoris.αβ_exact (Z := MayerVietorisSetup ES n X A B h_cover)
lemma βΔ_exact : (S_βΔ ES n X A B h_cover).Exact := by
  exact AlgebraicMayerVietoris.βΔ_exact (Z := MayerVietorisSetup ES n X A B h_cover)
lemma Δα_exact : (S_Δα ES n X A B h_cover).Exact := by
  exact AlgebraicMayerVietoris.Δγ_exact (Z := MayerVietorisSetup ES n X A B h_cover)

end
end EilenbergSteenrodAxioms
