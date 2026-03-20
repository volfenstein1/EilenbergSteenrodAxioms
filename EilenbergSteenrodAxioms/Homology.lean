/-
Copyright (c) 2026 Wolfgang Schamltz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wolfgang Schmaltz
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import EilenbergSteenrodAxioms.EilenbergSteenrodAxioms

@[expose] public section

open CategoryTheory TopCat ContinuousMap TopPair EilenbergSteenrodAxioms

namespace EilenbergSteenrodHomology

/- We define a functor from TopCat to TopPair as follows: -/
/-     - on objects: X ↦ (X, ∅)ₜₚ -/
/-     - on morphisms: (f : X ⟶ Y) ↦ (f : (X, ∅)ₜₚ ⟶ (Y, ∅)ₜₚ) -/
def TopCat_to_TopPair : TopCat ⥤ TopPair where
  obj X := TopPair.of X ∅
  map f := {
    toContFun := by 
      simp only [TopPair.of_carrier]
      exact f.hom
    map_subset_mem := by
      intro x hx
      rw [of_subset]
      contradiction
  }

lemma homotopy_lift_to_pair_homotopy {X Y : TopCat} {f g : X ⟶ Y} (h : Homotopic f.hom' g.hom') : 
  HomotopicPairHom (TopCat_to_TopPair.map f) (TopCat_to_TopPair.map g) := by
  /- `h` is a proposition (Nonempty Homotopy). Extract the actual Homotopy data `H`. -/
  rcases h with ⟨H⟩
  /- We use the Homotopy H to construct a TopPairHom and thus show that (Nonempty TopPairHomotopy). -/
  apply Nonempty.intro
  exact {
    toHomotopy := H
    prop' := by
      intro t x hx
      contradiction
  }

/-  Given an Eilenberg-Steenrod Homology Theory, considered as a Homology functor on Topological Pairs  -/
/-  (satisifying a number of axioms) -/
/- we obtain a Homology functor on the Category of Topological spaces via the functor TopCat ⥤ TopPair. -/
def Homology (ES : EilenbergSteenrodHomologyTheory) : 
    ℤ → TopCat ⥤ Ab := fun n => TopCat_to_TopPair ⋙ ES.H n

/- Given two topological spaces X and Y and a homotopy equivalence between them, -/
/- we use the Eilenberg-Steenrod Homotopy Invariant Axiom to obtain an isomorphism between the homology groups. -/
def homotopy_equiv_implies_isomorphic_homology (ES : EilenbergSteenrodHomologyTheory) (n : ℤ) {X Y : TopCat} (h : X ≃ₕ Y) : 
  (Homology ES n).obj X ≅ (Homology ES n).obj Y where
  hom := (Homology ES n).map (TopCat.ofHom h.toFun)
  inv := (Homology ES n).map (TopCat.ofHom h.invFun)
  hom_inv_id := by
    rw [← (Homology ES n).map_comp]
    rw [← (Homology ES n).map_id]
    apply ES.homotopy_invariant
    exact homotopy_lift_to_pair_homotopy h.left_inv
  inv_hom_id := by
    rw [← (Homology ES n).map_comp]
    rw [← (Homology ES n).map_id]
    apply ES.homotopy_invariant
    exact homotopy_lift_to_pair_homotopy h.right_inv


/- Mayer-Vietoris -/
/- We write the Mayer-Vietoris sequence for a topological space X and a cover A ∪ B = X. -/
/- ··· → H_(n+1) (X) ⟶ H_n (A ∩ᵣ B) ⟶ H_n (A)⊕ H_n (B) ⟶ H_n (X) ⟶ ···  -/
/- This amounts to nothing more than rewriting the appropriate results from the Mayer-Vietoris sequence for Topological Pairs.  -/
open ShortComplex Limits
noncomputable section

variable (ES : EilenbergSteenrodHomologyTheory) (n : ℤ) (X : Type*) [TopologicalSpace X] (A B : Set X) (h_cover : interior A ∪ interior B = Set.univ)
local notation "H" => Homology ES

def i : TopCat.of (A ∩ᵣB) ⟶ TopCat.of A where
  hom' := {
    toFun : (A ∩ᵣB) → A := fun x => ⟨x.val.val, x.property⟩
    continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
  }
def j : TopCat.of (A ∩ᵣB) ⟶ TopCat.of (B) where
  hom' := {
    toFun : A ∩ᵣ B → B := Subtype.val
    continuous_toFun := continuous_subtype_val
  }
def k : TopCat.of A ⟶ TopCat.of X where
  hom' := {
      toFun := fun x => x.val,
      continuous_toFun := by exact continuous_subtype_val
    }

def hom_i : (H n).obj (TopCat.of (A ∩ᵣB)) ⟶ (H n).obj (TopCat.of A) := (H n).map (i X A B)
def hom_j : (H n).obj (TopCat.of (A∩ᵣB)) ⟶ (H n).obj (TopCat.of B) := (H n).map (j X A B)
def hom_k : (H n).obj (TopCat.of A) ⟶ (H n).obj (TopCat.of X) := (H n).map (k X A)

def α : (H n).obj (TopCat.of (A∩ᵣB)) ⟶ (H n).obj (TopCat.of A) ⊞ (H n).obj (TopCat.of B) :=
  biprod.lift (hom_i ES n X A B) (-hom_j ES n X A B)
def β : (H n).obj (TopCat.of A) ⊞ (H n).obj (TopCat.of B) ⟶ (H n).obj (TopCat.of X) :=
  biprod.desc (hom_k ES n X A) (hom_k ES n X B)
def Δ : (H n).obj (TopCat.of X) ⟶ (H (n - 1)).obj (TopCat.of (A ∩ᵣ B)) := 
  EilenbergSteenrodAxioms.Δ ES n X A B h_cover
  /- haveI : IsIso (ES.hom_cover n X A B) := hom_cover_isIso ES n X A B h_cover -/
  /- (ES.hom_x n X A) ≫ inv (ES.hom_cover n X A B) ≫ (ES.delta n (n - 1) B (A ∩ᵣ B )) -/

lemma αβ_zero (h_cover : interior A ∪ interior B = Set.univ) : 
  (α ES n X A B) ≫  (β ES n X A B) = 0 := by
  exact EilenbergSteenrodAxioms.αβ_zero ES n X A B h_cover
lemma βΔ_zero : (β ES n X A B) ≫  (Δ ES n X A B h_cover) = 0 := by
  exact EilenbergSteenrodAxioms.βΔ_zero ES n X A B h_cover
lemma Δα_zero : (Δ ES n X A B h_cover) ≫  (α ES (n - 1) X A B)= 0 := by
  exact EilenbergSteenrodAxioms.Δα_zero ES n X A B h_cover

def S_αβ := ShortComplex.mk 
  (α ES n X A B) 
  (β ES n X A B) 
  (αβ_zero ES n X A B h_cover)
def S_βΔ := ShortComplex.mk 
  (β ES n X A B) 
  (Δ ES n X A B h_cover) 
  (βΔ_zero ES n X A B h_cover)
def S_Δα := ShortComplex.mk 
  (Δ ES n X A B h_cover) 
  (α ES (n - 1) X A B) 
  (Δα_zero ES n X A B h_cover)

lemma αβ_exact : (S_αβ ES n X A B h_cover).Exact := by 
  exact EilenbergSteenrodAxioms.αβ_exact ES n X A B h_cover
lemma βΔ_exact : (S_βΔ ES n X A B h_cover).Exact := by
  exact EilenbergSteenrodAxioms.βΔ_exact ES n X A B h_cover
lemma Δα_exact : (S_Δα ES n X A B h_cover).Exact := by
  exact EilenbergSteenrodAxioms.Δα_exact ES n X A B h_cover

end
end EilenbergSteenrodHomology
