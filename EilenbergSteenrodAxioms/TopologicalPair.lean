/-
Copyright (c) 2026 Wolfgang Schamltz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wolfgang Schmaltz
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

open Set CategoryTheory TopCat

/--
A structure representing a topological pair which consists of:
- X, a topological space, 
- A, a subset of X.
-/
structure TopPair where
  /- The carrier of a topologicaly pair, a type representing the whole space X. -/
  carrier : Type*
  /- The topological space structure on X, instance-implicit. -/
  [str : TopologicalSpace carrier]
  /- The subset A of X. -/
  subset : Set carrier

namespace TopPair

/- Register an instance for TopologicalSpace so that Lean infers it automatically for P.carrier. -/
instance (P : TopPair) : TopologicalSpace P.carrier := P.str
/- Note that subsets of a topological space automatically carry the induced subspace topology. -/
/- Hence the subspace topology is automatically inferred for P.subset. -/

/- Define a helper function for constructing a pair topological pair. -/
protected def of (X : Type*) [TopologicalSpace X] (A : Set X) : TopPair := { 
  carrier := X, 
  str := ‹TopologicalSpace X›, 
  subset := A }

/- We introduce a scoped notation `(X, Y)ₜₚ` for a topological pair. -/
scoped notation "(" X ", " A ")ₜₚ" => TopPair.of X A

/- Tell the simplifier that taking the carrier of a constructed topological pair should return the carrier. -/
@[simp]
theorem of_carrier {X : Type*} [TopologicalSpace X] (A : Set X) :
  (TopPair.of X A).carrier = X := rfl

/- Tell the simplifier that taking the subset of a constructed topological pair should return the subset. -/
@[simp]
theorem of_subset {X : Type*} [TopologicalSpace X] (A : Set X) :
  (TopPair.of X A).subset = A := rfl

/- Consider the following situation: (X : Type*), and (A B : Set X). -/
/- Then intersection 'A ∩ B' is necessarily of type Set X. -/
/- In the context of the Mayer-Vietoris sequence, we will want to consider topological pairs (B, A ∩ B). -/
/- This is most naturally done by considering A ∩ B as being of type Set B. -/
/- We define this in type theory as follows: -/
abbrev intersection_as_subset_of_right {X : Type*} (A : Set X) (B : Set X) : Set B := 
  Subtype.val ⁻¹' A
/- We introduce a scoped notation A ∩ᵣ B of type Set B. -/
scoped infixl:70 " ∩ᵣ " => intersection_as_subset_of_right 

/-
A morphism of topological pairs f : (X, A) → (Y, B) consists of:
- a continuous map f : X → Y which satisfies the property
- ∀ x ∈ A, f(x) ∈ B
-/
@[ext]
structure TopPairHom (P Q : TopPair) where
  /- The continuous function -/
  toContFun : C(P.carrier, Q.carrier)
  /- The condition that the subset is mapped into the target subset. -/
  map_subset_mem : ∀ x ∈ P.subset, toContFun x ∈ Q.subset

/-
Given (f : TopPairHom P Q) and (x : P.carrier) we normally would have to write:
    - (f.toFun x : Q.carrier)
We register an instance so that we may write:
    - (f x : Q.carrier)
-/
/- We will see later if this is really necessary, how often are we looking at points in a topological pair? -/
instance (P Q : TopPair) : CoeFun (TopPairHom P Q) (fun _ => P.carrier → Q.carrier) 
  where
  coe f := f.toContFun

/- The identity morphism for a pair (X, A). -/
def id' (P : TopPair) : TopPairHom P P where
  toContFun := ContinuousMap.id P.carrier
  map_subset_mem := by
    intro x hx
    rw [ContinuousMap.id_apply]
    exact hx

/- The composition of morphisms of pairs is again a morphism of a pair. -/
def comp' {P Q R : TopPair} (g : TopPairHom Q R) (f : TopPairHom P Q) : 
  TopPairHom P R 
  where
  toContFun := g.toContFun.comp f.toContFun
  map_subset_mem := by
    intro x hx
    apply g.map_subset_mem
    apply f.map_subset_mem
    exact hx

/-
A morphism f : (X, A) → (Y, B) yields a well-defined continuous map between the subsets A → B, 
where the subsets A and B are equipped with the induced (subspace) topology.
-/
def toSubsetMap {P Q : TopPair} (f : TopPairHom P Q) : C(↑P.subset, ↑Q.subset) :=
  { toFun := fun x => ↑⟨f.toContFun x.val, f.map_subset_mem x x.property⟩,
    continuous_toFun := by
      -- If a map f : A → Y is continuous and f(A) ⊆ B then f : A → B ⊆ Y is continuous.
      apply Continuous.subtype_mk
      -- If a map f : X → Y is continous and the subtype inclusion ι : A → X is the continuous, 
      -- then the composition (f ∘ ι) : A → Y is continuous
      exact f.toContFun.continuous.comp continuous_subtype_val }

/- A morphism f : (X, A) → (Y, B) yields a well-defined morphism (A, ∅) → (B, ∅) -/
def toSubsetHom {P Q : TopPair} (f : TopPairHom P Q) : TopPairHom (TopPair.of P.subset ∅) (TopPair.of Q.subset ∅)
  where
  toContFun := toSubsetMap f
  map_subset_mem := by
    intro x hx
    exact hx

/- Given two TopPairHoms f g, a homotopy between them is a homotopy H : [0, 1] × P.carrier → Q.carrier between f and g, considered as continuous functions (f g : C(P.carrier, Q.carrier))  -/
/- with the property that for all t ∈ [0, 1] the function H(t,·) maps P.subset into Q.subset. -/
def map_subset_mem_condition {P Q : TopPair} : C(P.carrier, Q.carrier) → Prop :=
  fun h => ∀ x ∈ P.subset, h x ∈ Q.subset

abbrev TopPairHomotopy {P Q : TopPair} (f g : TopPairHom P Q) :=
  ContinuousMap.HomotopyWith f.toContFun g.toContFun map_subset_mem_condition

def HomotopicPairHom {P Q : TopPair} (f g : TopPairHom P Q) : Prop := 
  ContinuousMap.HomotopicWith f.toContFun g.toContFun map_subset_mem_condition 

/- If H is a TopPairHomotopy between f and g then f and g are a HomotopicPairHom. -/
lemma TopPairHomotopy.toHomotopicPairHom {P Q : TopPair} {f g : TopPairHom P Q} (H : TopPairHomotopy f g) : 
    HomotopicPairHom f g := Nonempty.intro H

/- Define a helper function to construct a TopPairHomotopy from a standard Homotopy which satisfies map_subset_mem_condition. -/
def TopPairHomotopy.mk {P Q : TopPair} {f g : TopPairHom P Q}
  (H : ContinuousMap.Homotopy f.toContFun g.toContFun)
  (h_subset : ∀ t x, x ∈ P.subset → H (t, x) ∈ Q.subset) : 
  TopPairHomotopy f g where
  toHomotopy := H
  prop' t := by
    intro x hx
    exact h_subset t x hx

/- Together, TopPair and TopPairHom define a category instance. -/
instance : Category TopPair where
  Hom P Q := TopPairHom P Q
  id P := id' P
  comp f g := comp' g f
  /- aesop_cat automatically handles id_comp, comp_id, and assoc -/

@[ext]
lemma TopPair_hom_ext {P Q : TopPair} (f g : P ⟶ Q) (h : ∀ x, f.toContFun x = g.toContFun x) : f = g := by
  apply TopPairHom.ext
  ext x
  exact h x

/- The functor ρ is defined as follows: -/
/-     - on objects: (X, A)ₜₚ ↦ (A, ∅)ₜₚ  -/
/-     - on morphisms: (f : (X, A)ₜₚ ⟶ (Y, B)ₜₚ) ↦ (toSubsetHom f : (A, ∅)ₜₚ ⟶ (B, ∅)ₜₚ)  -/
def functor_ρ : TopPair ⥤ TopPair where
  obj P := TopPair.of P.subset ∅
  map f := toSubsetHom f
  /- aseop_cat automatically handles map_id, map_comp -/

/- We take a moment to define a few distinguished morphisms between topological pairs. -/
def inclusion_i {X : Type*} [TopologicalSpace X] (A B : Set X) :
    (TopPair.of (A ∩ᵣ B) ∅) ⟶ (TopPair.of A ∅) where
    toContFun := {
      toFun : A ∩ᵣ B → A := fun x => ⟨x.val.val, x.property⟩
      continuous_toFun := by 
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
    }
    map_subset_mem := by
      intro x hx
      rw [of_subset] at hx
      contradiction

def inclusion_j {X : Type*} [TopologicalSpace X] (A B : Set X) :
    (TopPair.of (A ∩ᵣ B) ∅) ⟶ (TopPair.of B ∅) where
    toContFun := {
      toFun : A ∩ᵣ B → B := Subtype.val
      continuous_toFun := continuous_subtype_val
    }
    map_subset_mem := by
      intro x hx
      rw [of_subset] at hx
      contradiction

def inclusion_k (X : Type*) [TopologicalSpace X] (A : Set X) : 
    (TopPair.of A ∅) ⟶ (TopPair.of X ∅) where
    toContFun := {
      toFun := fun x => x.val,
      continuous_toFun := by exact continuous_subtype_val
    }
    map_subset_mem := by
      intro x hx
      rw [of_subset] at hx
      contradiction

def inclusion_X_to_XA (X : Type*) [TopologicalSpace X] (A : Set X) : 
    (TopPair.of X ∅) ⟶ (TopPair.of X A) where
    toContFun := {
      toFun := fun x => x,
      continuous_toFun := by exact continuous_id
    }
    map_subset_mem := by
      intro x hx
      rw [of_subset] at hx
      contradiction

/- We define an excision pair, as well as natural maps associated to it. -/
/- Define a helper function for constructing a excision pair (X \ U, A \ U). -/
protected def excise (X : Type*) [TopologicalSpace X] (A : Set X) (U : Set X) : TopPair := {
  carrier := {x // x ∉ U},
  str := inferInstance,
  subset := Subtype.val ⁻¹' A
  }

/- Tell the simplifier that the carrier of TopPair.excise X A U should return X \ U. -/
@[simp]
lemma excise_carrier (X : Type*) [TopologicalSpace X] (A U : Set X) :
    (TopPair.excise X A U).carrier = {x // x ∉ U} := 
  rfl

/- Tell the simplifier that the subset of TopPair.excise X A U should return A \ U. -/
@[simp]
lemma excise_subset (X : Type*) [TopologicalSpace X] (A U : Set X) :
    (TopPair.excise X A U).subset = Subtype.val ⁻¹' A := 
  rfl

/- (X \ U, A \ U) → (X, A) -/
def excision_map (X : Type*) [TopologicalSpace X] (A U : Set X) :
    (TopPair.excise X A U) ⟶ (TopPair.of X A) where
    toContFun := {
      toFun := fun x => x.val,
      continuous_toFun := by exact continuous_subtype_val
    }
    map_subset_mem := by
      intro x hx
      exact hx

/- (B, A ∩ B) → (X, A) -/
def excision_cover_map (X : Type*) [TopologicalSpace X] (A B : Set X) :
    (TopPair.of B (A ∩ᵣ B)) ⟶ (TopPair.of X A) where
    toContFun := {
      toFun := fun x => x.val,
      continuous_toFun := by exact continuous_subtype_val
    }
    map_subset_mem := by
      intro x hx
      exact hx

/- The topological pairs (B, A ∩ᵣ B)ₜₚ and (X \ Bᶜ, A \ Bᶜ)ₜₚ are isomorphic in the Category TopPair. -/
def excise_equiv_cover (X : Type*) [TopologicalSpace X] (A B : Set X) :
    TopPair.of B (A ∩ᵣ B) ≅ TopPair.excise X A (Bᶜ) where
  hom := {
    toContFun := {
      toFun := fun x => ⟨x.val, fun h => h x.property⟩,
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
    }
    map_subset_mem := fun x hx => hx
  }
  inv := {
    toContFun := {
      toFun := fun x => ⟨x.val, Classical.byContradiction (fun h => x.property h)⟩,
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
    }
    map_subset_mem := fun x hx => hx
  }
  hom_inv_id := by ext; rfl 
  inv_hom_id := by ext; rfl

lemma cover_factors_through_excise (X : Type*) [TopologicalSpace X] (A B : Set X) :
    (excise_equiv_cover X A B).hom ≫ excision_map X A (Bᶜ) = excision_cover_map X A B := by
  ext
  rfl

end TopPair
